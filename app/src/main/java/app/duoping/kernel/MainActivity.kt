package app.duoping.kernel

import android.app.Activity
import android.content.Context
import android.content.Intent
import android.content.res.Configuration
import android.graphics.Typeface
import android.graphics.drawable.ClipDrawable
import android.graphics.drawable.GradientDrawable
import android.graphics.drawable.LayerDrawable
import android.graphics.drawable.StateListDrawable
import android.net.Uri
import android.os.Build
import android.provider.DocumentsContract
import android.os.Bundle
import android.os.PowerManager
import android.util.DisplayMetrics
import android.util.Log
import android.view.Gravity
import android.view.TextureView
import android.view.View
import android.view.WindowManager
import android.widget.Button
import android.widget.EditText
import android.widget.FrameLayout
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.SeekBar
import android.widget.TextView
import android.Manifest
import android.content.pm.PackageManager
import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Paint
import android.hardware.Camera
import android.view.SurfaceHolder
import android.view.SurfaceView
import android.view.MotionEvent
import android.widget.ImageView
import androidx.media3.common.MediaItem
import androidx.media3.common.Player
import androidx.media3.common.VideoSize
import androidx.media3.exoplayer.ExoPlayer
import androidx.media3.exoplayer.trackselection.DefaultTrackSelector
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.Job
import kotlinx.coroutines.delay
import kotlinx.coroutines.launch
import org.java_websocket.WebSocket
import org.java_websocket.client.WebSocketClient
import org.java_websocket.handshake.ClientHandshake
import org.java_websocket.handshake.ServerHandshake
import org.java_websocket.server.WebSocketServer
import org.json.JSONObject
import com.google.zxing.BarcodeFormat
import com.google.zxing.BinaryBitmap
import com.google.zxing.PlanarYUVLuminanceSource
import com.google.zxing.common.HybridBinarizer
import com.google.zxing.qrcode.QRCodeReader
import com.google.zxing.qrcode.QRCodeWriter
import java.io.File
import java.io.FileOutputStream
import java.net.HttpURLConnection
import java.net.InetSocketAddress
import java.net.NetworkInterface
import java.net.URL
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import java.util.concurrent.ConcurrentHashMap
import kotlin.math.abs

/** 多屏同显 — 同步内核原型。单 Activity，主机/从机双角色。协议见 protocol-v1.md。 */
class MainActivity : Activity() {

    companion object {
        const val PORT = 18765
        const val TAG = "DUOPING"
        const val REQ_PICK = 42
        const val REQ_PICK_XFER = 43 // v0.5.0：互传多选文件
        const val REQ_PICK_DIR = 44 // v0.5.0：互传接收文件夹（SAF）授权
        const val REQ_CAMERA = 45 // v0.6.0：扫码连接相机权限
    }

    private val scope = CoroutineScope(Dispatchers.Main + Job())
    private var logFile: File? = null

    // UI
    private lateinit var stage: FrameLayout
    private lateinit var overlay: FrameLayout
    private lateinit var controlsCol: LinearLayout
    private lateinit var statusTv: TextView
    private lateinit var debugTv: TextView
    private lateinit var bigNoTv: TextView
    private lateinit var textureView: TextureView
    private var role: String = "none" // host | client
    private var myNo: Int = -1

    // Player
    private var player: ExoPlayer? = null
    private var mediaReady = false
    private var started = false

    // Sync state
    @Volatile private var offsetMs: Long = 0
    @Volatile private var rttMs: Long = -1
    @Volatile private var lastErrMs: Long = 0
    @Volatile private var hardCorrections: Int = 0
    @Volatile private var rateState: String = "1.00"
    @Volatile private var lastTickHostClock: Long = 0
    @Volatile private var lastTickMediaPos: Long = 0
    private var wasBuffering = false
    @Volatile private var firstTickAfterStart = false

    // Host state
    private var server: KernelServer? = null
    private val clientReady = ConcurrentHashMap<Int, Boolean>()
    private val clientFailed = ConcurrentHashMap<Int, String>() // v0.3.2：本轮 PREPARE_FAIL 的从机 no -> reason
    private val clientConns = ConcurrentHashMap<Int, WebSocket>()
    // v0.6.5：编号复用——发号取 clientConns 当前未占用的最小正整数（断开时 onClose 清理即释放），不再设只增计数器
    private var tickJob: Job? = null

    // Client state
    private var wsClient: KernelClient? = null
    private var prepareRequested = false
    private val pendingPongs = ConcurrentHashMap<Long, (Long, Long, Long) -> Unit>()

    // ---- v0.2: device size table / tiling / ready hardening ----
    data class DevSize(val pxW: Int, val pxH: Int, val physW: Double, val physH: Double)
    data class Tile(val no: Int, val x: Double, val y: Double, val w: Double, val h: Double)
    private val deviceSizes = ConcurrentHashMap<Int, DevSize>()
    @Volatile private var mySize: DevSize? = null
    @Volatile private var currentMode: String? = null
    @Volatile private var myTile: Tile? = null
    @Volatile private var canvasRatio: Double = 0.0
    @Volatile private var videoAspect: Float = 0f
    @Volatile private var readySent = false
    private var prepareRound = 0
    private var devicesBox: LinearLayout? = null
    private var devicesHeaderTv: TextView? = null
    private val modePillBtns = mutableMapOf<String, Button>()

    // ---- v0.3: keep-on / fullscreen / host transport controls / periodic sync / stalls ----
    @Volatile private var sessionRate: Float = 1.0f
    @Volatile private var localPaused: Boolean = false
    @Volatile private var hostTickState: String = "playing"
    @Volatile private var stalls: Int = 0
    @Volatile private var sessionActive: Boolean = false
    @Volatile private var playbackEnded: Boolean = false
    private var wakeLock: PowerManager.WakeLock? = null
    @Volatile private var playingMode: Boolean = false
    private var overlayHideJob: Job? = null
    @Volatile private var videoPxW: Double = 0.0
    @Volatile private var videoPxH: Double = 0.0
    private var syncRound = 0
    private var playPauseBtn: Button? = null
    private var seekBar: SeekBar? = null
    private var timeTv: TextView? = null
    private var rateBtn: Button? = null
    @Volatile private var seekDragging: Boolean = false
    private val rateSteps = listOf(0.5f, 0.75f, 1.0f, 1.25f, 1.5f, 2.0f)

    // ---- v0.3.1: 校正换形（宽死区/seek 冷却）/ 控制条常驻 / 亮度同步 / 本地色温 ----
    @Volatile private var seekCooldownUntilMs: Long = 0
    private var hostBarBox: LinearLayout? = null
    private var tintView: View? = null
    private var clientBrightBar: SeekBar? = null

    // ---- v0.3.1 改动六：媒体自动分发（直链 / 主机 HTTP 分发 / 本地文件三态） ----
    private var mediaKind: String = "none" // host: none | local | link
    private var hostFileUri: Uri? = null
    private var hostLinkUrl: String? = null
    private var mediaToken: String = ""
    private var mediaServer: MediaFileServer? = null
    private var mediaServerUrl: String? = null
    private var mediaServerUri: Uri? = null
    @Volatile private var remoteMediaUrl: String? = null // client: 当前远程媒体 url
    private var sourceTv: TextView? = null // client: 来源标记行
    @Volatile private var connectedHostIp: String = ""

    // ---- v0.3.2：分发下载后播 / 远程备片 15 秒超时防呆 / PREPARE_FAIL ----
    @Volatile private var remotePrepareStartMs: Long = 0 // 远程流式 prepare 计时起点（0=未计时）；分发下载路径不计时
    @Volatile private var remotePrepareTimedOut: Boolean = false
    private var remoteTimeoutJob: Job? = null
    @Volatile private var distDownloadGen: Int = 0 // 下载代次：新一轮远程备片递增，过期下载结果作废
    @Volatile private var downloadingDist: Boolean = false

    // ---- v0.3.3：校正改速率微调（死区 30ms／微调区 30–2000ms／seek 仅灾难偏差） ----
    @Volatile private var appliedRate: Float = 1.0f // 从机当前实际下发到播放器的速率（会话速率×微调系数）；主机为参考不使用

    // ---- v0.5.0：局域网文件互传（一次性、多选、SHA-256 校验、.part 断点续传；仅主机⇄从机） ----
    private class XferItem(val name: String, var size: Long, var sha256: String, val uri: Uri?)
    // 发送方状态
    @Volatile private var xferSendTid: String? = null
    @Volatile private var xferSendToken: String = ""
    @Volatile private var xferSendTargetNo: Int = -1
    private val xferSendItems = mutableListOf<XferItem>()
    private val xferSendRows = mutableListOf<TextView>()
    @Volatile private var xferSendGen: Int = 0 // 选片算哈希代次：重选作废旧结果
    private var xferServer: XferFileServer? = null
    private var xferServerJob: Job? = null
    @Volatile private var xferTargetNo: Int = -1 // 界面选中的发送目标（主机：从机编号；从机固定 0=主机）
    // 接收方状态
    @Volatile private var xferRecvTid: String? = null
    @Volatile private var xferRecvFromNo: Int = -1
    @Volatile private var xferRecvFromIp: String = ""
    @Volatile private var xferRecvToken: String = ""
    private var xferRecvItems: List<XferItem> = emptyList()
    private val xferRecvRows = mutableListOf<TextView>()
    @Volatile private var xferRecvGen: Int = 0 // 接收代次：取消/断开递增，过期拉取结果作废
    @Volatile private var xferRecvTotalBytes: Long = 0
    @Volatile private var xferRecvDoneBytes: Long = 0
    @Volatile private var xferPendingAccept: Boolean = false // 等 SAF 选目录回来后补走接受流程
    // 互传 UI 引用
    private var xferTargetRow: LinearLayout? = null
    private var xferSendBox: LinearLayout? = null
    private var xferRecvBox: LinearLayout? = null
    private var xferRecvTotalTv: TextView? = null
    private var xferDestTv: TextView? = null
    private var xferBannerBox: LinearLayout? = null
    private var xferBannerTv: TextView? = null
    // 接收落盘：SAF 目录授权（持久化在 SharedPreferences）
    @Volatile private var xferDirUri: Uri? = null
    @Volatile private var xferDirAsked: Boolean = false

    // ---- v0.6.0：显示模式（全场 fit）/ 主机覆盖层分页 / 布局图示卡片 / 扫码连接 ----
    @Volatile private var layoutFit: String = "cover" // 全场显示模式 cover 铺满裁切 / contain 完整留边（主机选定随 LAYOUT 下发；从机从 LAYOUT 读入同一字段）
    private val hostPageBoxes = mutableMapOf<String, LinearLayout>()
    private val hostTabBtns = mutableMapOf<String, Button>()
    private var layoutCardsBox: LinearLayout? = null
    @Volatile private var layoutSelectedMode: String = "full"
    private val layoutCardViews = mutableMapOf<String, LinearLayout>()
    private var fitCoverBtn: Button? = null
    private var fitContainBtn: Button? = null
    private var fitContainVBtn: Button? = null // v0.6.1：完整·竖向胶囊（仅单台全屏提供）
    private var fitHintTv: TextView? = null // v0.6.1：显示模式说明行（随所选档刷新，cover 如实标注裁切）

    // ---- v0.6.1：播放期 UI 纪律（CHROME 生命周期 / 面板抑制 / 从机退出条）＋ EXIT_PLAYBACK 与活跃集 ----
    private var chromeHideJob: Job? = null
    @Volatile private var chromeWanted: Boolean = false // 播放中被 cmd/tap 唤醒的临时意愿（超时/toggle 清除）
    @Volatile private var chromeVisibleNow: Boolean = false // CHROME 实际显隐（仅切换时记日志）
    @Volatile private var chromeReasonHint: String? = null // 本次切换的原因提示（cmd/tap/timeout，apply 时消费）
    private var panelBtn: Button? = null // 工具条「面板」按钮：播放期进整页面板的唯一显式入口
    private var stopBtn: Button? = null // v0.6.3：工具条「退出播放」按钮（STOP 发起入口，仅主机；显隐随会话状态）
    private var stopPageBtn: Button? = null // v0.6.3：面板「播放」页「退出播放」按钮（与工具条同一处理函数）
    private var clientExitBox: LinearLayout? = null // 从机播放期极简退出条（舞台底部，只一颗「退出播放」）
    private var clientBarHideJob: Job? = null
    @Volatile private var clientBarVisibleNow: Boolean = false
    private val clientExited = java.util.concurrent.ConcurrentHashMap.newKeySet<Int>() // 主机侧：已退出播放的从机编号（设备行标记＋布局活跃集排除）
    private var qrScannerBox: FrameLayout? = null
    private var qrCamera: Camera? = null
    @Volatile private var qrScanning: Boolean = false
    @Volatile private var qrDecoding: Boolean = false
    private var lastQrTryMs: Long = 0
    private var clientIpInput: EditText? = null

    // ---- v0.3.1 改动七：死循环修复（程序 seek 标记 / RESYNC 纪律 / STALL 分开计数） ----
    @Volatile private var lastProgramSeekMs: Long = 0
    @Volatile private var lastResyncMs: Long = 0
    @Volatile private var stallsLoad: Int = 0
    @Volatile private var stallsSeek: Int = 0

    private fun fmtSpeed(f: Float): String = String.format(Locale.US, "%.2f", f)
    private fun fmtRate3(f: Float): String = String.format(Locale.US, "%.3f", f)
    private fun fmtRate(r: Float): String = if (r == r.toLong().toFloat()) r.toLong().toString() else r.toString()
    private fun fmtTime(ms: Long): String {
        val s = (ms / 1000).coerceAtLeast(0)
        return String.format(Locale.US, "%02d:%02d", s / 60, s % 60)
    }

    private fun fmt1(v: Double): String = String.format(Locale.US, "%.1f", v)
    private fun fmt2(v: Double): String = String.format(Locale.US, "%.2f", v)
    private fun fmt4(v: Double): String = String.format(Locale.US, "%.4f", v)

    /**
     * v0.6.4：稳定屏幕像素——面板真实尺寸（API 30+ 取 WindowManager.maximumWindowMetrics，
     * 低版本走 Display.getRealMetrics）。不随沉浸/系统栏显隐变化，与 resources.displayMetrics
     * 的窗口尺寸（沉浸切换中可瞬时出现 2263/2307 等中间值）严格区分。
     * 变换计算与尺寸上报共用此唯一几何来源，等比的前提是两处口径一致。
     */
    private fun stableScreenPx(): Pair<Int, Int> {
        return if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.R) {
            val b = windowManager.maximumWindowMetrics.bounds
            Pair(b.width(), b.height())
        } else {
            val dm = DisplayMetrics()
            @Suppress("DEPRECATION")
            windowManager.defaultDisplay.getRealMetrics(dm)
            Pair(dm.widthPixels, dm.heightPixels)
        }
    }

    /** 采集本机屏幕规模：像素 + 物理毫米（xdpi/ydpi 缺失时以 densityDpi 兜底）。v0.6.4：像素改取 stableScreenPx 的面板真实尺寸。 */
    private fun measureSize(): DevSize {
        val dm = resources.displayMetrics
        val xDpi = if (dm.xdpi > 0) dm.xdpi else dm.densityDpi.toFloat()
        val yDpi = if (dm.ydpi > 0) dm.ydpi else dm.densityDpi.toFloat()
        val (pxW, pxH) = stableScreenPx()
        val physW = pxW / xDpi * 25.4
        val physH = pxH / yDpi * 25.4
        return DevSize(pxW, pxH, physW, physH)
    }

    private fun logSize(no: Int, s: DevSize, xdpi: Float, ydpi: Float, fallback: Boolean) {
        klog("SIZE no=$no px=${s.pxW}x${s.pxH} xdpi=$xdpi ydpi=$ydpi phys_mm=${fmt1(s.physW)}x${fmt1(s.physH)} fallback=$fallback")
    }

    private fun logMySize(no: Int) {
        val s = mySize ?: return
        val dm = resources.displayMetrics
        logSize(no, s, dm.xdpi, dm.ydpi, dm.xdpi <= 0 || dm.ydpi <= 0)
    }

    private fun helloJson(type: String, s: DevSize): JSONObject {
        val dm = resources.displayMetrics
        return msg(type)
            .put("device_name", android.os.Build.MODEL ?: "android")
            .put("screen_w", s.pxW)
            .put("screen_h", s.pxH)
            .put("platform", "android")
            .put("px_w", s.pxW)
            .put("px_h", s.pxH)
            .put("phys_w_mm", s.physW)
            .put("phys_h_mm", s.physH)
            .put("xdpi", dm.xdpi.toDouble())
            .put("ydpi", dm.ydpi.toDouble())
    }

    /** 从 HELLO/HELLO_UPDATE 消息解析设备规模；物理尺寸缺失时以 160dpi 名义值兜底估算。 */
    private fun parseSize(o: JSONObject): DevSize {
        val pxW = if (o.has("px_w")) o.optInt("px_w") else o.optInt("screen_w")
        val pxH = if (o.has("px_h")) o.optInt("px_h") else o.optInt("screen_h")
        var physW = o.optDouble("phys_w_mm", 0.0)
        var physH = o.optDouble("phys_h_mm", 0.0)
        if (physW <= 0 && pxW > 0) physW = pxW * 25.4 / 160.0
        if (physH <= 0 && pxH > 0) physH = pxH * 25.4 / 160.0
        return DevSize(pxW, pxH, physW, physH)
    }

    private fun refreshDevicesTv() {
        val entries = deviceSizes.entries.sortedBy { it.key }
        runOnUiThread {
            val box = devicesBox ?: return@runOnUiThread
            devicesHeaderTv?.text = "设备表（编号 像素 物理mm）:"
            box.removeAllViews()
            entries.forEach { (no, s) -> box.addView(deviceRow(no, s)) }
        }
        refreshXferTargets() // v0.5.0：互传目标胶囊随设备表同步刷新（未建互传区时为空操作）
        rebuildLayoutCards() // v0.6.0：布局图示卡片随设备数变化重绘（未建主机页时为空操作）
        refreshFitPills() // v0.6.1：完整·竖向胶囊的单台可用性随活跃成员数刷新（未建主机页时为空操作）
    }

    /** v0.4.0：设备表卡片行——金色圆角徽章（编号）＋右侧像素/物理尺寸小字。数据与旧版文本行同源，仅排版拆分。 */
    private fun deviceRow(no: Int, s: DevSize): LinearLayout {
        val row = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            background = roundedDrawable(colPanel, 16)
            setPadding(dp(12), dp(10), dp(12), dp(10))
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT
            ).apply { topMargin = dp(8) }
        }
        val badge = TextView(this).apply {
            text = no.toString()
            textSize = 18f
            setTextColor(0xFF000000.toInt())
            setTypeface(null, Typeface.BOLD)
            gravity = Gravity.CENTER
            background = roundedDrawable(colGold, 10)
            layoutParams = LinearLayout.LayoutParams(dp(36), dp(36))
        }
        val info = TextView(this).apply {
            text = "${s.pxW}x${s.pxH}px ${fmt1(s.physW)}x${fmt1(s.physH)}mm"
            textSize = 14f
            setTextColor(colText)
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
                .apply { leftMargin = dp(12) }
        }
        row.addView(badge)
        row.addView(info)
        // v0.6.1（§14）：已退出播放的从机行尾金字标记（主机不自动暂停，仅状态呈现）
        if (no != 0 && clientExited.contains(no)) {
            row.addView(TextView(this).apply {
                text = "已退出播放"; textSize = 12f; setTextColor(colGold)
                layoutParams = LinearLayout.LayoutParams(
                    LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT
                ).apply { leftMargin = dp(10) }
            })
        }
        return row
    }

    // ---------- logging ----------
    private fun klog(msg: String) {
        Log.d(TAG, msg)
        try {
            val f = logFile ?: File(getExternalFilesDir(null), "duoping-kernel.log").also { logFile = it }
            val ts = SimpleDateFormat("MM-dd HH:mm:ss.SSS", Locale.US).format(Date())
            FileOutputStream(f, true).use { it.write("$ts $msg\n".toByteArray()) }
        } catch (e: Exception) {
            Log.d(TAG, "log write fail: ${e.message}")
        }
    }

    private fun setStatus(s: String) {
        runOnUiThread { statusTv.text = s }
    }

    // ---------- lifecycle ----------
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        buildStage()
        buildRolePickerUi()
        klog("app start")
        scope.launch { while (true) { updateDebugLine(); delay(500) } }
        scope.launch { while (true) { refreshHostProgress(); delay(500) } }
    }

    override fun onDestroy() {
        super.onDestroy()
        stopQrCamera() // v0.6.0：扫码相机兜底释放
        stopXferServer("destroy")
        stopMediaServer()
        releasePlayWakeLock("destroy")
        try { server?.stop(500) } catch (e: Exception) {}
        try { wsClient?.close() } catch (e: Exception) {}
        player?.release()
    }

    override fun onWindowFocusChanged(hasFocus: Boolean) {
        super.onWindowFocusChanged(hasFocus)
        if (hasFocus && playingMode) applyImmersive()
    }

    /** 屏幕形态变化（旋转、折叠屏展开/合上）：重新采集规模，从机重发 HELLO_UPDATE，主机更新设备表并按当前模式重算分片。 */
    override fun onConfigurationChanged(newConfig: Configuration) {
        super.onConfigurationChanged(newConfig)
        klog("config changed orientation=${newConfig.orientation} role=$role")
        scope.launch {
            delay(300) // 等 displayMetrics 稳定
            val s = measureSize()
            mySize = s
            when (role) {
                "client" -> {
                    logMySize(myNo)
                    if (wsClient?.isOpen == true) {
                        wsClient?.send(helloJson("HELLO_UPDATE", s).toString())
                        klog("client sent HELLO_UPDATE phys_mm=${fmt1(s.physW)}x${fmt1(s.physH)}")
                    }
                }
                "host" -> {
                    deviceSizes[0] = s
                    logMySize(0)
                    refreshDevicesTv()
                    currentMode?.let { doSendLayout(it) }
                }
            }
        }
    }

    // ---------- UI builders ----------
    private fun dp(v: Int): Int = (v * resources.displayMetrics.density).toInt()

    // ---------- v0.4.0 影院暗黑风：色板与样式助手（仅表现层；业务逻辑、文案与日志一律不动） ----------
    private val colBg = 0xFF0B0B10.toInt()       // 背景近黑
    private val colPanel = 0xFF16161F.toInt()    // 面板 / 卡片
    private val colGold = 0xFFFFC24B.toInt()     // 点缀琥珀金
    private val colGoldPressed = 0xFFE0A92E.toInt()
    private val colText = 0xFFF5F2EA.toInt()     // 主文字暖白
    private val colSub = 0xFF9A97A3.toInt()      // 次文字
    private val colDanger = 0xFFE5484D.toInt()   // 危险 / 错误（降饱和红）
    private val colStroke = 0xFF33333F.toInt()   // 描边
    private val colGlass = 0xCC12121A.toInt()    // 玻璃条半透明深色

    private fun roundedDrawable(fill: Int, radiusDp: Int, strokeColor: Int? = null): GradientDrawable =
        GradientDrawable().apply {
            setColor(fill)
            cornerRadius = dp(radiusDp).toFloat()
            if (strokeColor != null) setStroke(dp(1), strokeColor)
        }

    private fun pressableDrawable(normal: Int, pressed: Int, radiusDp: Int, strokeColor: Int? = null): StateListDrawable =
        StateListDrawable().apply {
            addState(intArrayOf(android.R.attr.state_pressed), roundedDrawable(pressed, radiusDp, strokeColor))
            addState(intArrayOf(), roundedDrawable(normal, radiusDp, strokeColor))
        }

    /** 金色实心主按钮（黑字加粗）。 */
    private fun stylePrimaryButton(b: Button, radiusDp: Int = 16) {
        b.background = pressableDrawable(colGold, colGoldPressed, radiusDp)
        b.setTextColor(0xFF000000.toInt())
        b.setTypeface(null, Typeface.BOLD)
        b.setPadding(dp(18), dp(10), dp(18), dp(10))
    }

    /** 暗色描边次按钮（面板底、暖白字）。 */
    private fun styleGhostButton(b: Button, radiusDp: Int = 16) {
        b.background = pressableDrawable(colPanel, 0xFF22222C.toInt(), radiusDp, colStroke)
        b.setTextColor(colText)
        b.setPadding(dp(18), dp(10), dp(18), dp(10))
    }

    /** 布局模式胶囊分段按钮：选中态金色实心黑字，未选暗色描边暖白字。 */
    private fun styleModePill(b: Button, selected: Boolean) {
        if (selected) {
            b.background = pressableDrawable(colGold, colGoldPressed, 24)
            b.setTextColor(0xFF000000.toInt())
            b.setTypeface(null, Typeface.BOLD)
        } else {
            b.background = pressableDrawable(colPanel, 0xFF22222C.toInt(), 24, colStroke)
            b.setTextColor(colText)
            b.setTypeface(null, Typeface.NORMAL)
        }
        b.textSize = 13f
        b.setPadding(dp(6), dp(8), dp(6), dp(8))
    }

    private fun selectModePill(key: String) {
        modePillBtns.forEach { (k, b) -> styleModePill(b, k == key) }
    }

    /** 暗色输入框：面板底圆角、金色描边、暖白字、次色提示、金色光标（API 29+）。 */
    private fun styleInput(et: EditText) {
        et.background = roundedDrawable(colPanel, 12, colGold)
        et.setTextColor(colText)
        et.setHintTextColor(colSub)
        et.textSize = 15f
        et.setPadding(dp(14), dp(12), dp(14), dp(12))
        if (Build.VERSION.SDK_INT >= 29) {
            et.textCursorDrawable = GradientDrawable().apply { setColor(colGold); setSize(dp(2), dp(20)) }
        }
    }

    /** 滑杆暗黑化：轨道灰、金色已播段、金色圆拇指。 */
    private fun styleSeekBar(bar: SeekBar) {
        fun trackLayer(): GradientDrawable = GradientDrawable().apply {
            setColor(0xFF3A3A46.toInt()); cornerRadius = dp(3).toFloat()
        }
        val progFill = GradientDrawable().apply { setColor(colGold); cornerRadius = dp(3).toFloat() }
        val ld = LayerDrawable(arrayOf(trackLayer(), trackLayer(), ClipDrawable(progFill, Gravity.LEFT, ClipDrawable.HORIZONTAL)))
        ld.setId(0, android.R.id.background)
        ld.setId(1, android.R.id.secondaryProgress)
        ld.setId(2, android.R.id.progress)
        for (i in 0..2) ld.setLayerInset(i, 0, dp(11), 0, dp(11))
        bar.progressDrawable = ld
        bar.thumb = GradientDrawable().apply {
            shape = GradientDrawable.OVAL
            setColor(colGold)
            setSize(dp(18), dp(18))
            setStroke(dp(2), colBg)
        }
        bar.setPadding(dp(12), dp(6), dp(12), dp(6))
    }

    /** 纵向占满宽度的堆叠布局参数（可带上间距）。 */
    private fun stackLp(topMarginDp: Int = 0): LinearLayout.LayoutParams =
        LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, LinearLayout.LayoutParams.WRAP_CONTENT)
            .apply { if (topMarginDp > 0) topMargin = dp(topMarginDp) }

    /**
     * v0.3 舞台结构：TextureView 铺满整块物理屏（变形修复的前提），
     * 其上依次是闪号大字、覆盖层（控制列 ScrollView + 底部调试行）。
     * 未进入播放时覆盖层常显；进入播放后点屏切换、4 秒无操作自动隐藏。
     */
    private fun buildStage() {
        // v0.4.0：状态栏 / 导航栏与舞台底统一近黑
        window.statusBarColor = colBg
        window.navigationBarColor = colBg
        stage = FrameLayout(this)
        stage.setBackgroundColor(colBg)
        // v0.6.4：舞台尺寸变化（沉浸进出/窗口重排）即重算变换。监听挂舞台根容器
        // （原挂 TextureView，v0.6.4 移至此；TextureView 为 match_parent 子视图，尺寸变化同源同频）。
        // 变换已改读 stableScreenPx 的稳定尺寸，重算必收敛同一结果，残余瞬时态在一个布局帧内自愈。
        stage.addOnLayoutChangeListener { _, l, t, r, b, ol, ot, orr, ob ->
            if (r - l != orr - ol || b - t != ob - ot) {
                if (myTile != null) applyTileTransform()
            }
        }
        textureView = TextureView(this)
        textureView.layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)
        textureView.setOnClickListener { onStageTap() }
        bigNoTv = TextView(this).apply {
            textSize = 120f; gravity = Gravity.CENTER; setTextColor(colGold)
            setTypeface(null, Typeface.BOLD)
            setBackgroundColor(0xCC000000.toInt()); visibility = View.GONE
            layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)
        }
        // v0.3.1 改动五：色温片层——在 TextureView 之上、闪号层与覆盖层之下，不可点击不拦截触摸
        val tint = View(this).apply {
            layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)
            isClickable = false
            isFocusable = false
            setBackgroundColor(0)
        }
        tintView = tint
        stage.addView(textureView); stage.addView(tint); stage.addView(bigNoTv)
        overlay = FrameLayout(this)
        overlay.layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)
        overlay.setBackgroundColor(0x66000000)
        overlay.setOnClickListener { onStageTap() }
        controlsCol = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL; setPadding(dp(20), dp(20), dp(20), dp(20)) }
        val sv = ScrollView(this)
        // v0.6.2：面板打开时点按未被控件覆盖的舞台区域关闭面板。ScrollView 全屏覆盖并吞掉触摸，
        // 点按到不了 textureView/overlay 的 OnClickListener（v0.6.1 关不掉面板的根因之一）；
        // 故在此只观察不拦截（return false，不影响滚动与子控件分发——点在控件上的触摸由控件先消费、到不了这里）：
        // 按下-抬起位移 <24px 且 <500ms 的真点按、且处于播放会话时，视为舞台点按走 closePanel。
        var svDownX = 0f; var svDownY = 0f; var svDownT = 0L
        sv.setOnTouchListener { _, ev ->
            when (ev.action) {
                MotionEvent.ACTION_DOWN -> { svDownX = ev.x; svDownY = ev.y; svDownT = System.currentTimeMillis() }
                MotionEvent.ACTION_UP -> {
                    val dx = ev.x - svDownX; val dy = ev.y - svDownY
                    if (dx * dx + dy * dy < 24f * 24f && System.currentTimeMillis() - svDownT < 500 &&
                        inPlaybackSession() && ::overlay.isInitialized && overlay.visibility == View.VISIBLE) {
                        closePanel("stage-tap")
                    }
                }
            }
            false
        }
        sv.addView(controlsCol)
        overlay.addView(sv)
        debugTv = TextView(this).apply {
            textSize = 11f; setTextColor(colSub); setBackgroundColor(0xAA0B0B10.toInt())
            setTypeface(Typeface.MONOSPACE); setPadding(dp(10), dp(4), dp(10), dp(4))
            layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.BOTTOM)
        }
        overlay.addView(debugTv)
        stage.addView(overlay)
        // v0.6.1：从机播放期极简退出条——挂舞台根容器（覆盖层之上、横幅之下），玻璃底、只有一颗「退出播放」，
        // 默认隐藏：播放期点屏唤醒、4 秒无交互自隐（规则同主机 CHROME）；主机侧永不显示（显隐判定带 role 检查）
        val exitBox = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER
            background = roundedDrawable(colGlass, 20)
            setPadding(dp(16), dp(10), dp(16), dp(10))
            layoutParams = FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.WRAP_CONTENT, FrameLayout.LayoutParams.WRAP_CONTENT,
                Gravity.BOTTOM or Gravity.CENTER_HORIZONTAL
            ).apply { bottomMargin = dp(16) }
            visibility = View.GONE
        }
        exitBox.addView(Button(this).apply {
            text = "退出播放"
            styleGhostButton(this)
            setOnClickListener { exitClientPlayback() }
        })
        exitBox.setOnTouchListener { _, ev ->
            if (ev.action == MotionEvent.ACTION_DOWN) armClientBarTimer()
            false
        }
        clientExitBox = exitBox
        stage.addView(exitBox)
        setContentView(stage)
    }

    private fun buildRolePickerUi() {
        controlsCol.removeAllViews()
        // v0.4.0：首屏大标题＋副标题（原文案拆分呈现，字词不变）
        val title = TextView(this).apply {
            text = "多屏同显"; textSize = 40f; setTextColor(colText)
            setTypeface(null, Typeface.BOLD); gravity = Gravity.CENTER
            layoutParams = stackLp().apply { topMargin = dp(30) }
        }
        val subtitle = TextView(this).apply {
            text = "同步内核原型"; textSize = 14f; setTextColor(colSub); gravity = Gravity.CENTER
            layoutParams = stackLp(6)
        }
        controlsCol.addView(title)
        controlsCol.addView(subtitle)
        controlsCol.addView(roleCard("主机 (HOST)", "创建房间 · 本机出声 · 等待从机加入") { startHost() })
        controlsCol.addView(roleCard("从机 (CLIENT)", "加入主机 · 静音跟随播放") { buildClientUi() })
        statusTv = TextView(this).apply {
            text = "请选择角色"; textSize = 15f; setTextColor(colSub); gravity = Gravity.CENTER
            layoutParams = stackLp(20)
        }
        controlsCol.addView(statusTv)
    }

    /** v0.4.0：首屏角色入口大卡片——面板底、左侧金条、标题＋一行说明小字、右侧金色箭头。点击行为与旧按钮一致。 */
    private fun roleCard(titleText: String, subText: String, onClick: () -> Unit): LinearLayout {
        val card = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            background = pressableDrawable(colPanel, 0xFF22222C.toInt(), 16, colStroke)
            setPadding(dp(18), dp(18), dp(18), dp(18))
            isClickable = true
            isFocusable = true
            setOnClickListener { onClick() }
            layoutParams = stackLp(16)
        }
        val bar = View(this).apply {
            background = roundedDrawable(colGold, 3)
            layoutParams = LinearLayout.LayoutParams(dp(5), LinearLayout.LayoutParams.MATCH_PARENT)
        }
        val texts = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
                .apply { leftMargin = dp(14) }
        }
        texts.addView(TextView(this).apply {
            text = titleText; textSize = 20f; setTextColor(colText); setTypeface(null, Typeface.BOLD)
        })
        texts.addView(TextView(this).apply {
            text = subText; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(4)
        })
        card.addView(bar)
        card.addView(texts)
        card.addView(TextView(this).apply { text = "›"; textSize = 26f; setTextColor(colGold) })
        return card
    }

    // ---------- v0.3: immersive / overlay ----------
    private fun applyImmersive() {
        window.decorView.systemUiVisibility = (View.SYSTEM_UI_FLAG_IMMERSIVE_STICKY
            or View.SYSTEM_UI_FLAG_HIDE_NAVIGATION or View.SYSTEM_UI_FLAG_FULLSCREEN
            or View.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION or View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN
            or View.SYSTEM_UI_FLAG_LAYOUT_STABLE)
    }

    private fun enterPlaybackUi() {
        playingMode = true
        runOnUiThread {
            applyImmersive()
            // v0.6.1：起播即收起整页面板（播放期面板抑制自起播生效，不再闪现 4 秒）；主机改亮 CHROME，从机退出条保持隐藏待点屏唤醒
            overlayHideJob?.cancel()
            if (::overlay.isInitialized) overlay.visibility = View.GONE
            if (role == "host") chromeShow("cmd") else hideClientBar()
            updateHostBarVisibility()
            hideBigNumber("playback") // v0.6.5：起播即藏大编号（暂停保持隐藏，播放期任何路径不许带回）
        }
    }

    private fun exitPlaybackUi(showReason: String = "standby") {
        playingMode = false
        overlayHideJob?.cancel()
        runOnUiThread {
            window.decorView.systemUiVisibility = 0
            if (::overlay.isInitialized) overlay.visibility = View.VISIBLE
            hideClientBar()
            updateHostBarVisibility()
        }
        showBigNumber(showReason) // v0.6.5：离开播放 UI 回到待机/大厅，大编号重现（统一出口，reason 区分触发源）
    }

    /** v0.6.5：大编号显隐统一出口——进入播放态隐藏、回到待机重现；只在实际切换时各记一行日志。 */
    private fun hideBigNumber(reason: String) {
        runOnUiThread {
            if (::bigNoTv.isInitialized && bigNoTv.visibility != View.GONE) {
                bigNoTv.visibility = View.GONE
                klog("UI number hide reason=$reason")
            }
        }
    }

    private fun showBigNumber(reason: String) {
        runOnUiThread {
            if (::bigNoTv.isInitialized && myNo >= 0) {
                bigNoTv.text = myNo.toString()
                if (bigNoTv.visibility != View.VISIBLE) {
                    bigNoTv.visibility = View.VISIBLE
                    klog("UI number show reason=$reason")
                }
            }
        }
    }

    private fun showOverlay(autoHide: Boolean, explicit: Boolean = false) {
        if (!::overlay.isInitialized) return
        // v0.6.1：播放会话中整页面板抑制——只有工具条「面板」按钮的显式打开（explicit=true）放行，其余入口一律抑制并记日志
        if (inPlaybackSession() && !explicit) {
            klog("UI panel suppressed during playback")
            return
        }
        overlay.visibility = View.VISIBLE
        updateHostBarVisibility()
        overlayHideJob?.cancel()
        if (autoHide && playingMode) {
            overlayHideJob = scope.launch {
                delay(4000)
                if (playingMode) {
                    overlay.visibility = View.GONE
                    // v0.3.1 改动二：覆盖层隐藏后控制条按自身规则决定显隐（播放中常驻）
                    updateHostBarVisibility()
                }
            }
        }
    }

    /** v0.6.1：本机处于播放会话中（已起播且未结束，含暂停）——面板抑制与浮条唤醒的统一判定口径，主机从机同规。 */
    private fun inPlaybackSession(): Boolean = started && !playbackEnded

    private fun onStageTap() {
        if (inPlaybackSession()) {
            // v0.6.1：播放期点屏——整页面板不许被点开（抑制并记日志），只唤醒/收起本机浮条（主机 CHROME／从机退出条）
            if (::overlay.isInitialized && overlay.visibility == View.VISIBLE) {
                // 面板是经工具条「面板」按钮显式打开的：点舞台背景收起面板回纯画面（关闭动作不算抑制），走 closePanel 统一出口
                closePanel("stage-tap")
                return
            }
            klog("UI panel suppressed during playback")
            if (role == "host") chromeTapToggle() else clientBarTapToggle()
            return
        }
        if (!playingMode) {
            if (::overlay.isInitialized) overlay.visibility = View.VISIBLE
            updateHostBarVisibility()
            return
        }
        if (overlay.visibility == View.VISIBLE) {
            closePanel("stage-tap")
        } else {
            showOverlay(autoHide = true)
        }
        updateHostBarVisibility()
    }

    // ---------- v0.6.1：从机播放期极简退出条（唤醒/自隐规则同主机 CHROME；点「退出播放」只退本机、连接保持） ----------
    private fun clientBarTapToggle() {
        if (clientBarVisibleNow) hideClientBar() else showClientBar()
    }

    private fun showClientBar() {
        runOnUiThread { clientExitBox?.visibility = View.VISIBLE; clientBarVisibleNow = true }
        armClientBarTimer()
    }

    private fun hideClientBar() {
        clientBarHideJob?.cancel()
        runOnUiThread { clientExitBox?.visibility = View.GONE; clientBarVisibleNow = false }
    }

    /** 退出条 4 秒自隐计时：条上触摸重置（arm 时先取消旧计时）。 */
    private fun armClientBarTimer() {
        clientBarHideJob?.cancel()
        clientBarHideJob = scope.launch {
            delay(4000)
            hideClientBar()
        }
    }

    /**
     * v0.6.1：从机「退出播放」——只退本机：释放本机播放器（渲染停止）、回从机面板/待机界面，WebSocket 连接保持不断；
     * 并通知主机 EXIT_PLAYBACK（§14 口径：主机只标记、不自动暂停）。全场会话不受影响。
     * 退出后主机新发 PREPARE/START 时，本机经 startRemoteMedia/schedulePlay 既有流程重新入场；
     * 本场仍在播时不做专门的「重新加入」按钮（已知限制）。
     */
    private fun exitClientPlayback() {
        if (role != "client") return
        hideClientBar()
        try { wsClient?.send(msg("EXIT_PLAYBACK").put("client_no", myNo).toString()) } catch (e: Exception) {}
        releasePlayWakeLock("client exit playback")
        remoteTimeoutJob?.cancel()
        distDownloadGen++ // 作废进行中的分发下载结果（同断开处理口径）
        downloadingDist = false
        player?.release()
        player = null
        remoteMediaUrl = null
        mediaReady = false
        prepareRequested = false
        started = false
        localPaused = false
        playbackEnded = false
        if (::textureView.isInitialized) {
            textureView.rotation = 0f
            textureView.scaleX = 1f
            textureView.scaleY = 1f
        }
        exitPlaybackUi("exit")
        klog("UI client exit playback")
        setStatus("已退出本机播放（连接保持），等待主机下一次起播")
    }

    // ---------- v0.3: keep screen on ----------
    private fun updateKeepScreenOn() {
        runOnUiThread {
            val flag = WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON
            val has = (window.attributes.flags and flag) != 0
            if (sessionActive && !has) {
                window.addFlags(flag)
                klog("KEEP_ON screen flag set sessionActive=true role=$role")
            } else if (!sessionActive && has) {
                window.clearFlags(flag)
                klog("KEEP_ON screen flag cleared sessionActive=false role=$role")
            }
        }
    }

    private fun acquirePlayWakeLock() {
        try {
            if (wakeLock?.isHeld == true) return
            val pm = getSystemService(Context.POWER_SERVICE) as PowerManager
            @Suppress("DEPRECATION")
            wakeLock = pm.newWakeLock(PowerManager.SCREEN_BRIGHT_WAKE_LOCK, "duoping:play")
            wakeLock?.acquire(4 * 60 * 60 * 1000L)
            klog("KEEP_ON wakelock acquired level=SCREEN_BRIGHT timeout_ms=14400000 role=$role")
        } catch (e: Exception) {
            klog("KEEP_ON wakelock acquire fail: ${e.message}")
        }
    }

    private fun releasePlayWakeLock(reason: String) {
        try {
            if (wakeLock?.isHeld == true) {
                wakeLock?.release()
                klog("KEEP_ON wakelock released reason=$reason role=$role")
            }
        } catch (e: Exception) {
            klog("KEEP_ON wakelock release fail: ${e.message}")
        } finally {
            wakeLock = null
        }
    }

    private fun pickButton(): Button = Button(this).apply {
        text = "选择视频文件"
        styleGhostButton(this)
        layoutParams = stackLp(12)
        setOnClickListener {
            val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
                addCategory(Intent.CATEGORY_OPENABLE); type = "video/*"
            }
            startActivityForResult(intent, REQ_PICK)
        }
    }

    // ---------- HOST ----------
    private fun startHost() {
        role = "host"; myNo = 0
        // 改动六：本场分发令牌（每次组会生成 16 位随机串），分发地址 /media/<令牌> 用
        val alpha = "abcdefghijklmnopqrstuvwxyz0123456789"
        val rnd = java.security.SecureRandom()
        mediaToken = (1..16).map { alpha[rnd.nextInt(alpha.length)] }.joinToString("")
        controlsCol.removeAllViews()
        val ip = localIp()
        controlsCol.addView(TextView(this).apply {
            text = "主机模式 · 本机 IP: $ip · 端口 $PORT · 本机编号 0"; textSize = 17f
            setTextColor(colText); setTypeface(null, Typeface.BOLD)
        })
        statusTv = TextView(this).apply {
            text = "服务端启动中…"; textSize = 15f; setTextColor(colText)
            layoutParams = stackLp(10)
        }
        // ---- v0.6.0：主机覆盖层分页（播放／布局／互传／更多）——只动视图组织：既有控件、回调、文案、日志一律保留，仅改挂载父容器 ----
        modePillBtns.clear() // 旧布局胶囊行退役（布局改走布局页图示卡片），清旧引用防跨会话残留
        hostPageBoxes.clear(); hostTabBtns.clear()
        val tabRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            layoutParams = stackLp(16)
        }
        val pagesBox = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            layoutParams = stackLp()
        }
        listOf("play" to "播放", "layout" to "布局", "xfer" to "互传", "more" to "更多").forEach { (key, label) ->
            val page = LinearLayout(this).apply {
                orientation = LinearLayout.VERTICAL
                visibility = if (key == "play") View.VISIBLE else View.GONE
                layoutParams = stackLp()
            }
            hostPageBoxes[key] = page
            pagesBox.addView(page)
            val tb = Button(this).apply {
                text = label
                styleModePill(this, key == "play")
                layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
                    .apply { leftMargin = dp(3); rightMargin = dp(3) }
                setOnClickListener { selectHostPage(key) }
            }
            hostTabBtns[key] = tb
            tabRow.addView(tb)
        }
        controlsCol.addView(tabRow)
        controlsCol.addView(pagesBox)
        val playPage = hostPageBoxes["play"]!!
        val layoutPage = hostPageBoxes["layout"]!!
        val xferPage = hostPageBoxes["xfer"]!!
        val morePage = hostPageBoxes["more"]!!
        // —— 播放页：选片／分发入口、起播、就绪状态列表概要（设备表）、状态行 ——
        playPage.addView(pickButton())
        // 改动六入口乙：直链输入——粘贴 http/https 直链成为本场媒体地址（入口甲为上方本地选片）
        val linkInput = EditText(this).apply { hint = "或粘贴 http/https 直链"; styleInput(this); layoutParams = stackLp(12) }
        playPage.addView(linkInput)
        playPage.addView(Button(this).apply {
            text = "用此链接"
            styleGhostButton(this)
            layoutParams = stackLp(10)
            setOnClickListener { hostUseLink(linkInput.text.toString().trim()) }
        })
        playPage.addView(Button(this).apply {
            text = "准备 (PREPARE → 等 READY 后自动起播)"
            stylePrimaryButton(this)
            layoutParams = stackLp(14)
            setOnClickListener { hostPrepare() }
        })
        playPage.addView(Button(this).apply {
            text = "重发准备 (对未 READY 从机重发 PREPARE)"
            styleGhostButton(this)
            layoutParams = stackLp(10)
            setOnClickListener { hostResendPrepare() }
        })
        // v0.6.3：「退出播放」——与工具条同名按钮、同一处理函数（STOP 结束当前视频，组会保留）；无播放会话时不出现（显隐由 applyChrome 随会话状态同步）
        stopPageBtn = Button(this).apply {
            text = "退出播放"
            styleGhostButton(this)
            layoutParams = stackLp(10)
            visibility = View.GONE
            setOnClickListener { hostStopPlayback() }
        }
        playPage.addView(stopPageBtn!!)
        // —— v0.6.0 扫码连接（主机出码）：内容为纯文本 duoping://<局域网IP>:18765/<会话令牌>，令牌沿用本场组会随机令牌；
        // 码下同时显示 IP 与令牌文本，扫不了时从机手输 IP 的兜底不变 ——
        val qrText = "duoping://$ip:$PORT/$mediaToken"
        val qrImg = ImageView(this).apply {
            layoutParams = LinearLayout.LayoutParams(dp(240), dp(240)).apply { gravity = Gravity.CENTER_HORIZONTAL }
        }
        val qrBox = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            gravity = Gravity.CENTER_HORIZONTAL
            visibility = View.GONE
            layoutParams = stackLp(10)
        }
        qrBox.addView(qrImg)
        qrBox.addView(TextView(this).apply {
            text = "从机点「扫码连接」扫此码入会 · IP：$ip · 令牌：$mediaToken"
            textSize = 13f; setTextColor(colSub); gravity = Gravity.CENTER
            layoutParams = stackLp(8)
        })
        playPage.addView(Button(this).apply {
            text = "显示连接二维码"
            styleGhostButton(this)
            layoutParams = stackLp(14)
            setOnClickListener {
                if (qrBox.visibility == View.VISIBLE) {
                    qrBox.visibility = View.GONE
                } else {
                    if (qrImg.drawable == null) makeQrBitmap(qrText, 720)?.let { b -> qrImg.setImageBitmap(b) }
                    qrBox.visibility = View.VISIBLE
                }
            }
        })
        playPage.addView(qrBox)
        devicesHeaderTv = TextView(this).apply {
            text = "设备表: （暂无）"; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(18)
        }
        playPage.addView(devicesHeaderTv)
        devicesBox = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        playPage.addView(devicesBox)
        playPage.addView(statusTv)
        // —— 布局页：显示模式二选一（全场 fit）＋布局图示卡片 ——
        layoutPage.addView(TextView(this).apply {
            text = "显示模式（全场，选定即下发）"; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(4)
        })
        val fitRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            layoutParams = stackLp(8)
        }
        fitCoverBtn = Button(this).apply {
            text = "铺满（裁切）"
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
                .apply { leftMargin = dp(3); rightMargin = dp(3) }
            setOnClickListener { setLayoutFit("cover") }
        }
        fitContainBtn = Button(this).apply {
            text = "完整·横向"
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
                .apply { leftMargin = dp(3); rightMargin = dp(3) }
            setOnClickListener { setLayoutFit("contain_h") }
        }
        // v0.6.1：第三档「完整·竖向」——仅单台全屏时提供（多台时胶囊不出现，由 refreshFitPills 按活跃成员数控制）
        fitContainVBtn = Button(this).apply {
            text = "完整·竖向"
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f)
                .apply { leftMargin = dp(3); rightMargin = dp(3) }
            setOnClickListener { setLayoutFit("contain_v") }
        }
        fitRow.addView(fitCoverBtn!!)
        fitRow.addView(fitContainBtn!!)
        fitRow.addView(fitContainVBtn!!)
        layoutPage.addView(fitRow)
        // v0.6.1：显示模式说明行——如实标注每档代价（cover 明示「铺满会裁切画面」，不拿完整话术描述铺满）
        fitHintTv = TextView(this).apply {
            textSize = 12f; setTextColor(colSub)
            layoutParams = stackLp(6)
        }
        layoutPage.addView(fitHintTv!!)
        refreshFitPills()
        layoutPage.addView(TextView(this).apply {
            text = "布局排布（按各机物理尺寸成比例绘制，点卡片即下发）"; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(14)
        })
        layoutCardsBox = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        layoutPage.addView(layoutCardsBox!!)
        rebuildLayoutCards()
        // —— 互传页 ——
        buildXferSection(xferPage) // v0.5.0：文件互传区（主机页；v0.6.0 起挂互传分页）
        // —— 更多页：全场亮度（自常显控制条移入，广播语义不变）、本机色温、调试说明、结束会话 ——
        morePage.addView(TextView(this).apply {
            text = "全场亮度（拖动结束应用本机并广播全场）"; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(4)
        })
        morePage.addView(makeBrightnessBar { level -> hostSetBrightness(level) })
        morePage.addView(TextView(this).apply {
            text = "本机色温（左冷右暖，仅本机不广播）"; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(16)
        })
        morePage.addView(makeTintBar())
        morePage.addView(TextView(this).apply {
            text = "调试读数常显于屏幕底部小字行（编号／对时／偏差／速率／卡顿）"; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(16)
        })
        morePage.addView(Button(this).apply {
            text = "结束会话（返回角色选择）"
            styleGhostButton(this)
            setTextColor(colDanger)
            layoutParams = stackLp(14)
            setOnClickListener { endHostSession() }
        })
        buildHostControlBar()
        val s0 = measureSize()
        mySize = s0
        deviceSizes[0] = s0
        logMySize(0)
        refreshDevicesTv()
        server = KernelServer(InetSocketAddress(PORT))
        server?.isReuseAddr = true
        server?.start()
        klog("host server starting on $PORT ip=$ip")
        sessionActive = true
        updateKeepScreenOn()
        setStatus("服务端已启动，等待从机连接。本机 IP: $ip")
    }

    // ---------- v0.3: host transport controls (PAUSE / RESUME / SEEK / RATE) ----------
    /**
     * v0.6.1：主机控制条（CHROME）生命周期——取代 v0.3.1 的「播放中常驻」口径（Owen 验收细化）：
     * 无播放会话（未备片/已结束/已断开，或已回角色选择）完全隐藏；播放中由命令（起播/继续/倍速，reason=cmd）
     * 或点屏（reason=tap）唤醒，4 秒无交互自隐（reason=timeout），已显示时点屏即收起（reason=tap）；
     * 暂停中钉住常显不自隐（reason=pause，保住 v0.3「暂停时找不到继续键」的教训，硬要求）；
     * 播放结束隐藏（reason=end）。
     * v0.6.2 解耦（真机根因修复）：显隐不再与面板开关绑定——v0.6.1 的「面板打开时随行」分支把条钉死：
     * 大厅未备片时条浮在页面上、播放中开面板后条永不自隐（计时又被面板打开状态拒挂），且面板关不掉形成死锁。
     * 现口径：播放中目标显隐只看 chromeWanted（最后交互时刻＋4 秒计时）；面板仅在「已备片未起播」时让条随行
     * （起播入口够得着）；未备片且不在播放会话时恒 GONE，周期刷新（refreshHostProgress 每 500ms 调本函数）
     * 只同步求值、永不置 chromeWanted，不得把条带出来。
     * 本函数为兜底刷新：只按当前状态求目标显隐，实际切换才写 CHROME 日志（周期刷新不刷屏）。
     */
    private fun updateHostBarVisibility() { applyChrome() }

    private fun applyChrome() {
        if (hostBarBox == null) return
        runOnUiThread {
            if (role != "host") { setChromeVisible(false, null); return@runOnUiThread }
            // v0.6.3：「退出播放」两处入口的显隐随播放会话状态走——有媒体在场（已备片/播放中/暂停中/已播完）才出现，无会话不出现
            val stopVis = if (mediaKind != "none" || started || playbackEnded) View.VISIBLE else View.GONE
            stopBtn?.visibility = stopVis
            stopPageBtn?.visibility = stopVis
            val inSession = inPlaybackSession()
            val overlayOpen = ::overlay.isInitialized && overlay.visibility == View.VISIBLE
            val target = when {
                playbackEnded -> false
                inSession && localPaused -> true // 暂停钉住
                inSession -> chromeWanted // v0.6.2：播放中只由唤醒意愿＋4 秒计时决定，面板开着也不钉住（解耦，见 v0.6.2 根因）
                overlayOpen && mediaKind != "none" -> true // 已备片未起播：随面板显示（起播入口在条上）；未备片恒不浮出（无会话 GONE）
                else -> false
            }
            val reason = if (target) {
                chromeReasonHint ?: if (inSession && localPaused) "pause" else "cmd"
            } else {
                when {
                    playbackEnded -> "end"
                    !inSession -> "nosession"
                    else -> chromeReasonHint ?: "timeout"
                }
            }
            setChromeVisible(target, reason)
        }
    }

    /** CHROME 实际显隐切换的唯一出口：与 chromeVisibleNow 一致时只同步 visibility、不记日志；切换时按 reason 记一行并消费原因提示。 */
    private fun setChromeVisible(target: Boolean, reason: String?) {
        val box = hostBarBox ?: return
        box.visibility = if (target) View.VISIBLE else View.GONE
        if (target != chromeVisibleNow) {
            chromeVisibleNow = target
            if (reason != null) klog(if (target) "CHROME show reason=$reason" else "CHROME hide reason=$reason")
            chromeReasonHint = null
        }
    }

    /** CHROME 唤醒（起播/继续/倍速/拖进度等命令与点屏）：置意愿、刷新显隐、播放中（未暂停、面板未开）重启 4 秒自隐计时。 */
    private fun chromeShow(reason: String) {
        chromeWanted = true
        chromeReasonHint = reason
        applyChrome()
        armChromeTimer()
    }

    /** 点屏 toggle：CHROME 已显示则立即收起（reason=tap），未显示则唤醒（reason=tap）。 */
    private fun chromeTapToggle() {
        if (chromeVisibleNow && chromeWanted) {
            chromeWanted = false
            chromeHideJob?.cancel()
            chromeReasonHint = "tap"
            applyChrome()
        } else {
            chromeShow("tap")
        }
    }

    /** CHROME 4 秒自隐计时：只由最后交互时刻驱动——续期事件仅限工具条真实触摸、播放命令、舞台点按、面板关闭回场；
     * 进度刷新/TICK/STAT/调试读数一律不得续期。暂停钉住、无会话时不计时。
     * v0.6.2：面板打开时照常挂计时（v0.6.1 在此以面板打开为由拒绝挂计时，是自隐失效的关键一环）。 */
    private fun armChromeTimer() {
        chromeHideJob?.cancel()
        if (role != "host" || !inPlaybackSession() || localPaused) return
        chromeHideJob = scope.launch {
            delay(4000)
            chromeWanted = false
            chromeReasonHint = "timeout"
            applyChrome()
        }
    }

    /** 会话终局撤条（结束会话/回角色选择）：取消计时与意愿，若条正显示记 hide reason=nosession。 */
    private fun chromeReset() {
        chromeHideJob?.cancel()
        chromeWanted = false
        runOnUiThread {
            if (chromeVisibleNow) klog("CHROME hide reason=nosession")
            chromeVisibleNow = false
            hostBarBox?.visibility = View.GONE
        }
    }

    /** 工具条「面板」按钮（v0.6.2 改开关 toggle）：面板关时打开（播放期进整页面板的唯一显式入口，
     * 用户明确动作、不受点屏抑制约束，记 UI panel open）；面板开时关闭回舞台（走 closePanel）。打开面板不停止播放。 */
    private fun openPanelFromChrome() {
        if (::overlay.isInitialized && overlay.visibility == View.VISIBLE) {
            closePanel("toggle")
            return
        }
        chromeWanted = true
        klog("UI panel open")
        showOverlay(autoHide = false, explicit = true)
        applyChrome()
    }

    /** 整页面板关闭的统一出口（按钮 toggle／点舞台未覆盖区两条路径共用）：
     * 收面板、记 UI panel close；随后回场——播放中以 reason=panel-close 重新点亮 CHROME 并重启 4 秒自隐计时，
     * 暂停中钉住规则不变（applyChrome 按 pause 点亮/保持），无会话时条保持 GONE。 */
    private fun closePanel(reason: String) {
        if (!::overlay.isInitialized) return
        overlayHideJob?.cancel()
        val wasOpen = overlay.visibility == View.VISIBLE
        overlay.visibility = View.GONE
        if (wasOpen) klog("UI panel close reason=$reason")
        if (role == "host") {
            if (inPlaybackSession() && !localPaused) chromeShow("panel-close") else applyChrome()
        }
    }

    /** 改动三：应用本机窗口亮度（level 0.05–1.0）。 */
    private fun applyBrightness(level: Float) {
        val lp = window.attributes
        lp.screenBrightness = level.coerceIn(0.05f, 1.0f)
        window.attributes = lp
    }

    /** 主机亮度：先应用本机，再广播 BRIGHTNESS 给全场。 */
    private fun hostSetBrightness(level: Float) {
        applyBrightness(level)
        server?.broadcast(msg("BRIGHTNESS").put("level", level.toDouble()).toString())
        klog("BRIGHTNESS level=${fmt2(level.toDouble())} sent")
        setStatus("全场亮度 ${fmt2(level.toDouble())}")
    }

    /** 亮度滑杆：progress 0–100 线性映射到 level 0.05–1.0（初始 1.0），拖动结束才生效。 */
    private fun makeBrightnessBar(onDone: (Float) -> Unit): SeekBar {
        val bar = SeekBar(this)
        styleSeekBar(bar)
        bar.max = 100
        bar.progress = 100
        bar.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(sb: SeekBar?, progress: Int, fromUser: Boolean) {}
            override fun onStartTrackingTouch(sb: SeekBar?) {}
            override fun onStopTrackingTouch(sb: SeekBar?) {
                val level = 0.05f + ((sb?.progress ?: 100) / 100f) * 0.95f
                onDone(level)
            }
        })
        return bar
    }

    /** 改动五：本机色温片——正值暖（255,140,0）、负值冷（0,120,255），不透明度 = |值|/100 × 0.18。 */
    private fun applyTint(v: Int) {
        val a = (abs(v) / 100.0 * 0.18 * 255).toInt().coerceIn(0, 255)
        val color = when {
            v > 0 -> android.graphics.Color.argb(a, 255, 140, 0)
            v < 0 -> android.graphics.Color.argb(a, 0, 120, 255)
            else -> 0
        }
        tintView?.setBackgroundColor(color)
    }

    /** 色温滑杆：整数 −100…+100（progress 0–200，初始 100 对应 0），只调本机、不广播、不持久化。 */
    private fun makeTintBar(): SeekBar {
        val bar = SeekBar(this)
        styleSeekBar(bar)
        bar.max = 200
        bar.progress = 100
        bar.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(sb: SeekBar?, progress: Int, fromUser: Boolean) {
                if (fromUser) applyTint(progress - 100)
            }
            override fun onStartTrackingTouch(sb: SeekBar?) {}
            override fun onStopTrackingTouch(sb: SeekBar?) {
                klog("TINT value=${(sb?.progress ?: 100) - 100}")
            }
        })
        return bar
    }

    private fun buildHostControlBar() {
        // v0.3.1 改动二：控制条从覆盖层内的 controlsCol 拆出，改为挂在 stage 上的独立容器
        // （z 序在覆盖层之上、半透明底），使它能独立于覆盖层常驻；未起播/播完时仍随覆盖层显隐。
        val box = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            // v0.4.0：悬浮玻璃条——半透明深色圆角面板，浮于舞台底部上方 16dp、左右各留 12dp
            background = roundedDrawable(colGlass, 20)
            setPadding(dp(16), dp(12), dp(16), dp(12))
            layoutParams = FrameLayout.LayoutParams(
                FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.BOTTOM
            ).apply { bottomMargin = dp(16); leftMargin = dp(12); rightMargin = dp(12) }
            visibility = View.GONE
        }
        // v0.6.1：条上任何触摸（点按钮、拖进度/倍速）都算交互，重置 4 秒自隐计时；返回 false 不拦截子控件事件
        box.setOnTouchListener { _, ev ->
            if (ev.action == MotionEvent.ACTION_DOWN) armChromeTimer()
            false
        }
        val bar = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
        }
        playPauseBtn = Button(this).apply {
            text = "起播"
            stylePrimaryButton(this, 24) // v0.4.0：金色圆角主按钮（字形文案沿用现状，由既有逻辑切换）
            minWidth = dp(96)
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.WRAP_CONTENT, dp(48)
            )
            setOnClickListener { onPlayPauseClicked() }
        }
        rateBtn = Button(this).apply {
            text = "倍速 ×${fmtRate(sessionRate)}"
            background = pressableDrawable(colPanel, 0xFF22222C.toInt(), 24, colStroke) // v0.4.0：暗色胶囊、金字
            setTextColor(colGold)
            setPadding(dp(14), dp(8), dp(14), dp(8))
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.WRAP_CONTENT, dp(48)
            ).apply { leftMargin = dp(10) }
            setOnClickListener { cycleRate() }
        }
        // v0.6.1：「面板」按钮——播放期打开整页面板的唯一显式入口（点屏不许开面板，Owen 口径）；样式同倍速胶囊的暗色描边
        panelBtn = Button(this).apply {
            text = "面板"
            background = pressableDrawable(colPanel, 0xFF22222C.toInt(), 24, colStroke)
            setTextColor(colText)
            setPadding(dp(14), dp(8), dp(14), dp(8))
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.WRAP_CONTENT, dp(48)
            ).apply { leftMargin = dp(10) }
            setOnClickListener { openPanelFromChrome() }
        }
        // v0.6.3：「退出播放」按钮——结束当前视频（STOP 全场广播）但不解散组会；样式同「面板」幽灵胶囊，显隐随会话状态（applyChrome 同步）
        stopBtn = Button(this).apply {
            text = "退出播放"
            background = pressableDrawable(colPanel, 0xFF22222C.toInt(), 24, colStroke)
            setTextColor(colText)
            setPadding(dp(14), dp(8), dp(14), dp(8))
            layoutParams = LinearLayout.LayoutParams(
                LinearLayout.LayoutParams.WRAP_CONTENT, dp(48)
            ).apply { leftMargin = dp(10) }
            setOnClickListener { hostStopPlayback() }
        }
        bar.addView(playPauseBtn); bar.addView(rateBtn); bar.addView(panelBtn!!); bar.addView(stopBtn!!)
        box.addView(bar)
        // v0.6.0：常显控制条瘦身——只留播放/暂停、倍速与下方进度条三件；主机亮度滑杆移入覆盖层「更多」页（广播语义不变）
        seekBar = SeekBar(this).apply {
            styleSeekBar(this)
            layoutParams = stackLp(4)
            max = 0
            setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
                override fun onProgressChanged(sb: SeekBar?, progress: Int, fromUser: Boolean) {
                    if (fromUser) {
                        val dur = (player?.duration ?: 0).coerceAtLeast(0)
                        timeTv?.text = "${fmtTime(progress.toLong())} / ${fmtTime(dur)}"
                    }
                }
                override fun onStartTrackingTouch(sb: SeekBar?) { seekDragging = true }
                override fun onStopTrackingTouch(sb: SeekBar?) {
                    seekDragging = false
                    hostSeek((sb?.progress ?: 0).toLong())
                }
            })
        }
        box.addView(seekBar)
        timeTv = TextView(this).apply { text = "00:00 / 00:00"; textSize = 13f; setTextColor(colText) }
        box.addView(timeTv)
        stage.addView(box)
        hostBarBox = box
        updateHostBarVisibility()
    }

    private fun refreshHostProgress() {
        updateHostBarVisibility() // 兜底同步控制条显隐（状态变化后最迟 500ms 内跟上）
        if (role != "host" || !started || seekDragging) return
        val p = player ?: return
        val dur = p.duration
        if (dur > 0) {
            seekBar?.max = dur.toInt()
            seekBar?.progress = p.currentPosition.coerceIn(0, dur).toInt()
            timeTv?.text = "${fmtTime(p.currentPosition)} / ${fmtTime(dur)}"
        }
    }

    private fun onPlayPauseClicked() {
        when {
            !started || playbackEnded -> {
                playPauseBtn?.text = "暂停"
                hostPrepare() // 未起播/已播完：走既有 PREPARE → READY → START 全流程
            }
            localPaused -> hostResume()
            else -> hostPause()
        }
    }

    private fun hostPause() {
        val p = player ?: return
        val pos = p.currentPosition
        p.pause()
        localPaused = true
        server?.broadcast(msg("PAUSE").put("media_pos_ms", pos).toString())
        klog("PAUSE sent media_pos_ms=$pos")
        playPauseBtn?.text = "继续"
        chromeHideJob?.cancel() // v0.6.1：暂停钉住 CHROME 常显，停自隐计时（applyChrome 按 pause 规则点亮/保持）
        applyChrome()
        releasePlayWakeLock("host pause")
        setStatus("已暂停于 ${fmtTime(pos)}")
    }

    private fun hostResume() {
        val p = player ?: return
        val startAt = System.currentTimeMillis() + 1200
        val pos = p.currentPosition
        val rate = sessionRate
        server?.broadcast(msg("RESUME").put("start_at_hostclock", startAt)
            .put("media_pos_ms", pos).put("rate", rate.toDouble()).toString())
        klog("RESUME sent start_at=$startAt media_pos_ms=$pos rate=$rate")
        scheduleResume(startAt, pos, isHostClock = true)
        playPauseBtn?.text = "暂停"
        setStatus("全场将于 1.2 秒后继续播放")
    }

    private fun hostSeek(pos: Long) {
        val p = player ?: return
        if (!started) { setStatus("尚未起播，不能拖动进度"); return }
        programSeek(p, pos)
        server?.broadcast(msg("SEEK").put("media_pos_ms", pos).toString())
        klog("SEEK sent media_pos_ms=$pos paused=$localPaused")
        chromeShow("cmd") // v0.6.1：命令唤醒 CHROME
        setStatus("全场跳转到 ${fmtTime(pos)}")
    }

    private fun cycleRate() {
        val idx = rateSteps.indexOf(sessionRate).let { if (it < 0) 2 else it }
        val next = rateSteps[(idx + 1) % rateSteps.size]
        sessionRate = next
        if (started && !localPaused) {
            player?.setPlaybackSpeed(next)
            rateState = fmtSpeed(next)
        }
        server?.broadcast(msg("RATE").put("rate", next.toDouble()).toString())
        klog("RATE sent rate=$next")
        rateBtn?.text = "倍速 ×${fmtRate(next)}"
        chromeShow("cmd") // v0.6.1：命令唤醒 CHROME
        setStatus("全场倍速 ×${fmtRate(next)}")
    }

    /** 定时恢复起播：主机到 startAt 本机起播；从机同刻 seek 到 pos 后以 sessionRate 起播。 */
    private fun scheduleResume(startAtHostClock: Long, mediaPos: Long, isHostClock: Boolean) {
        val localStart = if (isHostClock) startAtHostClock else startAtHostClock - offsetMs
        val delayMs = localStart - System.currentTimeMillis()
        klog("scheduleResume localStart=$localStart delay=$delayMs media_pos_ms=$mediaPos role=$role no=$myNo")
        scope.launch {
            if (delayMs > 0) delay(delayMs)
            val p = player ?: return@launch
            if (!isHostClock) programSeek(p, mediaPos) // 改动七：RESUME 的 seek 同样记程序 seek 时刻
            p.setPlaybackSpeed(sessionRate)
            appliedRate = sessionRate // v0.3.3 复位点：RESUME 起播实际速率回到会话速率
            rateState = fmtSpeed(sessionRate)
            p.play()
            started = true
            localPaused = false
            playbackEnded = false
            acquirePlayWakeLock()
            enterPlaybackUi()
            klog("RESUME play() executed pos=${p.currentPosition} rate=$sessionRate role=$role no=$myNo")
        }
    }

    // ---------- v0.3.1 改动六：媒体自动分发（直链入口 / 主机 HTTP 分发服务） ----------
    /** 入口乙：直链成为本场媒体地址；主机本机直接以直链建播放器，PREPARE 时 url 原样下发。 */
    private fun hostUseLink(url: String) {
        if (!url.startsWith("http://") && !url.startsWith("https://")) {
            setStatus("直链须以 http:// 或 https:// 开头")
            return
        }
        mediaKind = "link"
        hostLinkUrl = url
        stopMediaServer()
        klog("MEDIA host link selected authority=${Uri.parse(url).authority}")
        setupPlayer(Uri.parse(url))
        armRemotePrepareTimeout("link") // v0.3.2：主机本机直链备片同样适用 15 秒超时
        setStatus("已选直链为本场媒体，等 prepare 完成后点「准备」下发")
    }

    /** 本轮 PREPARE 的 url：直链用直链；本地文件且有从机连接时启动分发服务用分发地址；否则 local-file 占位。 */
    private fun currentPrepareUrl(): String = when (mediaKind) {
        "link" -> hostLinkUrl ?: "local-file"
        "local" -> if (clientConns.isNotEmpty()) ensureMediaServer() ?: "local-file" else "local-file"
        else -> "local-file"
    }

    private fun ensureMediaServer(): String? {
        val uri = hostFileUri ?: return null
        val alive = mediaServer
        if (alive != null && alive.isRunning() && mediaServerUri == uri) return mediaServerUrl
        stopMediaServer()
        val size = queryFileSize(uri)
        val degraded = !canOpenFd(uri)
        if (degraded) klog("MEDIASRV reason=no_fd uri=$uri")
        val srv = MediaFileServer(localIp(), uri, mediaToken, size, contentTypeFor(uri), degraded)
        srv.start()
        mediaServer = srv
        mediaServerUri = uri
        val url = "http://${localIp()}:18767/media/$mediaToken"
        mediaServerUrl = url
        return url
    }

    private fun stopMediaServer() {
        mediaServer?.stop()
        mediaServer = null
        mediaServerUrl = null
        mediaServerUri = null
    }

    private fun queryFileSize(uri: Uri): Long {
        try { contentResolver.openFileDescriptor(uri, "r")?.use { return it.statSize } } catch (e: Exception) {}
        try {
            contentResolver.query(uri, null, null, null, null)?.use { c ->
                val idx = c.getColumnIndex(android.provider.OpenableColumns.SIZE)
                if (idx >= 0 && c.moveToFirst() && !c.isNull(idx)) return c.getLong(idx)
            }
        } catch (e: Exception) {}
        return -1
    }

    private fun canOpenFd(uri: Uri): Boolean = try {
        val pfd = contentResolver.openFileDescriptor(uri, "r")
        pfd?.close()
        pfd != null
    } catch (e: Exception) { false }

    private fun displayNameOf(uri: Uri): String {
        try {
            contentResolver.query(uri, null, null, null, null)?.use { c ->
                val idx = c.getColumnIndex(android.provider.OpenableColumns.DISPLAY_NAME)
                if (idx >= 0 && c.moveToFirst()) return c.getString(idx) ?: ""
            }
        } catch (e: Exception) {}
        return uri.lastPathSegment ?: ""
    }

    /** Content-Type 按文件扩展名取（规格三值），未知扩展名一律 application/octet-stream。 */
    private fun contentTypeFor(uri: Uri): String {
        val name = displayNameOf(uri).lowercase()
        return when {
            name.endsWith(".mp4") || name.endsWith(".m4v") -> "video/mp4"
            name.endsWith(".mkv") -> "video/x-matroska"
            name.endsWith(".mp3") -> "audio/mpeg"
            else -> "application/octet-stream"
        }
    }

    /**
     * 主机局域网 HTTP 文件服务（JDK 标准库 ServerSocket 手写，无新增依赖）。
     * 只绑主机局域网 IP，只提供当前选定的一个文件，路径须等于 /media/<会话令牌>，否则 404。
     * 支持 Range（206 + Content-Range）；取不到文件描述符时降级为整流（Range 也回 200 整流）。
     * 每连接一线程，信号量限流（许可数 = 服务启动时的从机连接数，至少 1）；64KB 固定缓冲流式转发，不整文件载入内存。
     */
    inner class MediaFileServer(
        private val bindIp: String,
        val fileUri: Uri,
        private val token: String,
        private val fileSize: Long,
        private val contentType: String,
        private val degraded: Boolean
    ) {
        @Volatile private var running = false
        private var serverSocket: java.net.ServerSocket? = null
        private val seenClients = ConcurrentHashMap.newKeySet<String>()
        private val gate = java.util.concurrent.Semaphore(maxOf(1, clientConns.size))

        fun isRunning(): Boolean = running

        fun start() {
            try {
                val ss = java.net.ServerSocket()
                ss.reuseAddress = true
                ss.bind(java.net.InetSocketAddress(bindIp, 18767))
                serverSocket = ss
                running = true
                klog("MEDIASRV started port=18767 size=$fileSize degraded=$degraded bind=$bindIp")
                Thread {
                    while (running) {
                        try {
                            val conn = ss.accept()
                            Thread { serve(conn) }.apply { isDaemon = true }.start()
                        } catch (e: Exception) {
                            if (running) klog("MEDIASRV accept err: ${e.message}")
                        }
                    }
                }.apply { isDaemon = true }.start()
            } catch (e: Exception) {
                klog("MEDIASRV start fail: ${e.message}")
            }
        }

        fun stop() {
            if (!running && serverSocket == null) return
            running = false
            try { serverSocket?.close() } catch (e: Exception) {}
            serverSocket = null
            klog("MEDIASRV stopped port=18767")
        }

        private fun serve(conn: java.net.Socket) {
            try {
                gate.acquire()
                try { handle(conn) } finally { gate.release() }
            } catch (e: Exception) {
                klog("MEDIASRV conn err: ${e.message}")
            } finally {
                try { conn.close() } catch (e: Exception) {}
            }
        }

        private fun handle(conn: java.net.Socket) {
            val remote = conn.inetAddress?.hostAddress ?: "?"
            val reader = java.io.BufferedReader(java.io.InputStreamReader(conn.getInputStream(), Charsets.US_ASCII))
            val requestLine = reader.readLine() ?: return
            val parts = requestLine.split(" ")
            var rangeHeader: String? = null
            while (true) {
                val line = reader.readLine() ?: break
                if (line.isEmpty()) break
                val idx = line.indexOf(':')
                if (idx > 0 && line.substring(0, idx).trim().equals("Range", ignoreCase = true)) {
                    rangeHeader = line.substring(idx + 1).trim()
                }
            }
            val out = conn.getOutputStream()
            val path = (if (parts.size >= 2) parts[1] else "").substringBefore('?')
            if (parts.isEmpty() || parts[0] != "GET" || path != "/media/$token") {
                writeHead(out, 404, "Not Found", 0, null)
                return
            }
            if (seenClients.add(remote)) {
                klog("MEDIASRV first GET from=$remote range=${rangeHeader != null}")
            }
            var start = 0L
            var end = if (fileSize > 0) fileSize - 1 else -1L
            var partial = false
            if (rangeHeader != null && !degraded && fileSize > 0) {
                val spec = rangeHeader.removePrefix("bytes=").trim()
                val dash = spec.indexOf('-')
                if (dash >= 0) {
                    val a = spec.substring(0, dash).trim()
                    val b = spec.substring(dash + 1).trim()
                    try {
                        if (a.isEmpty() && b.isNotEmpty()) {
                            val suffix = b.toLong()
                            start = maxOf(0L, fileSize - suffix)
                            end = fileSize - 1
                        } else if (a.isNotEmpty()) {
                            start = a.toLong()
                            end = if (b.isEmpty()) fileSize - 1 else minOf(b.toLong(), fileSize - 1)
                        }
                        partial = start in 0..end
                    } catch (e: Exception) { partial = false }
                }
            }
            if (partial) {
                writeHead(out, 206, "Partial Content", end - start + 1, "bytes $start-$end/$fileSize")
                streamRange(out, start, end - start + 1)
            } else {
                writeHead(out, 200, "OK", fileSize, null)
                streamWhole(out)
            }
        }

        private fun writeHead(out: java.io.OutputStream, code: Int, text: String, length: Long, contentRange: String?) {
            val sb = StringBuilder()
            sb.append("HTTP/1.1 $code $text\r\n")
            sb.append("Content-Type: $contentType\r\n")
            if (length >= 0) sb.append("Content-Length: $length\r\n")
            sb.append("Accept-Ranges: bytes\r\n")
            if (contentRange != null) sb.append("Content-Range: $contentRange\r\n")
            sb.append("Connection: close\r\n\r\n")
            out.write(sb.toString().toByteArray(Charsets.US_ASCII))
            out.flush()
        }

        private fun streamWhole(out: java.io.OutputStream) {
            if (!degraded) {
                val pfd = contentResolver.openFileDescriptor(fileUri, "r")
                if (pfd != null) {
                    try { java.io.FileInputStream(pfd.fileDescriptor).use { copyN(it, out, Long.MAX_VALUE) } }
                    finally { try { pfd.close() } catch (e: Exception) {} }
                    return
                }
            }
            contentResolver.openInputStream(fileUri)?.use { copyN(it, out, Long.MAX_VALUE) }
        }

        private fun streamRange(out: java.io.OutputStream, start: Long, len: Long) {
            val pfd = contentResolver.openFileDescriptor(fileUri, "r")
            if (pfd == null) { streamWhole(out); return }
            try {
                val fis = java.io.FileInputStream(pfd.fileDescriptor)
                fis.channel.position(start)
                fis.use { copyN(it, out, len) }
            } finally { try { pfd.close() } catch (e: Exception) {} }
        }

        private fun copyN(input: java.io.InputStream, out: java.io.OutputStream, maxBytes: Long) {
            val buf = ByteArray(64 * 1024)
            var remain = maxBytes
            while (remain > 0) {
                val want = minOf(buf.size.toLong(), remain).toInt()
                val n = input.read(buf, 0, want)
                if (n < 0) break
                out.write(buf, 0, n)
                remain -= n
            }
            out.flush()
        }
    }

    private fun hostPrepare() {
        if (!mediaReady) { setStatus("请先选片并等本机 prepare 完成"); return }
        // v0.3：播完后重走全流程前，本机播放器若处于 ENDED 先回卷到 0（从机在 PREPARE 分支同样处理）
        if (player?.playbackState == Player.STATE_ENDED) {
            player?.let { programSeek(it, 0) }
            klog("hostPrepare: ended player rewound to 0 for replay")
        }
        prepareRound++
        val round = prepareRound
        clientReady.clear()
        clientFailed.clear() // v0.3.2：新一轮 PREPARE 作废上一轮的失败记录
        server?.broadcast(msg("PREPARE").put("url", currentPrepareUrl()).put("duration_ms", player?.duration ?: 0).toString())
        klog("host sent PREPARE round=$round, clients=${clientConns.size}")
        if (clientConns.isEmpty()) { hostStart() } else setStatus("已发 PREPARE，等待从机 READY…")
        if (clientConns.isNotEmpty()) {
            scope.launch {
                delay(10000)
                if (round != prepareRound) return@launch
                // v0.3.2：已回 PREPARE_FAIL 的从机视为已决，不再列入等待名单
                val missing = clientConns.keys.filter { clientReady[it] != true && !clientFailed.containsKey(it) }.sorted()
                if (missing.isNotEmpty()) {
                    setStatus("等待从机 READY：编号 ${missing.joinToString("、")}")
                    klog("READY_WAIT missing=$missing")
                }
            }
        }
    }

    private fun hostResendPrepare() {
        // v0.3.2：重发只针对既未 READY 也未 FAIL 的从机（已 FAIL 的本场不参与）
        val missing = clientConns.entries.filter { clientReady[it.key] != true && !clientFailed.containsKey(it.key) }
        if (missing.isEmpty()) { setStatus("没有未 READY 的从机"); return }
        val m = msg("PREPARE").put("url", currentPrepareUrl()).put("duration_ms", player?.duration ?: 0).toString()
        missing.forEach { it.value.send(m) }
        klog("host resent PREPARE to ${missing.map { it.key }.sorted()}")
        setStatus("已对未 READY 从机重发 PREPARE: ${missing.map { it.key }.sorted()}")
    }

    /**
     * v0.3.2 核对结论：现行（v0.3.1）收齐判定为「clientReady 覆盖全部连接且全为 true」——备片失败的从机永远凑不齐，
     * 全场会被一台坏链从机永久阻塞（host-log-v031.txt 中 READY_WAIT missing=[1, 2] 反复出现即此症）。
     * 改为：已 READY 数 + 已 FAIL 数（限当前连接）>= 连接总数即起播，FAIL 的从机不参与本场。
     */
    private fun hostMaybeStart() {
        if (clientConns.isEmpty()) return
        val ready = clientReady.values.count { it }
        val failed = clientFailed.keys.count { clientConns.containsKey(it) }
        if (ready + failed >= clientConns.size) hostStart()
    }

    private fun hostStart() {
        val startAt = System.currentTimeMillis() + 1500
        server?.broadcast(msg("START").put("start_at_hostclock", startAt).put("media_pos_ms", 0).toString())
        klog("host sent START start_at=$startAt")
        localPaused = false
        playbackEnded = false
        playPauseBtn?.text = "暂停"
        schedulePlay(startAt, isHostClock = true, mediaPos = 0)
        tickJob?.cancel()
        tickJob = scope.launch {
            while (true) {
                delay(5000)
                val p = player ?: break
                if (started) {
                    server?.broadcast(msg("TICK").put("host_clock", System.currentTimeMillis())
                        .put("media_pos_ms", p.currentPosition).put("rate", sessionRate.toDouble())
                        .put("state", if (localPaused) "paused" else "playing").toString())
                }
            }
        }
    }

    // ---------- layout engine (v0.2: per-number auto tiling, physical-mm weighted) ----------
    private fun hostLayoutMode(mode: String) {
        val n = activeNos().size // v0.6.1：模式守卫按活跃成员数（已退出播放者不计入）
        when (mode) {
            "third" -> {
                if (n != 3) setStatus("三等分仅适用于 3 台，已按横排拼下发")
                doSendLayout("hrow")
            }
            "grid" -> {
                if (n != 4) { setStatus("田字格仅适用于 4 台"); return }
                doSendLayout("grid")
            }
            else -> doSendLayout(mode)
        }
    }

    /** 按设备表（物理毫米）计算 tiles。返回 (canvas_ratio, tiles)；设备按编号升序。 */
    private fun computeTiles(mode: String, devs: List<Pair<Int, DevSize>>): Pair<Double, List<Tile>> {
        return when (mode) {
            "full" -> 0.0 to devs.map { (no, _) -> Tile(no, 0.0, 0.0, 1.0, 1.0) }
            "vcol" -> {
                val canvasH = devs.sumOf { it.second.physH }
                val canvasW = devs.maxOf { it.second.physW }
                var accY = 0.0
                val tiles = devs.map { (no, s) ->
                    val w = s.physW / canvasW
                    val h = s.physH / canvasH
                    val t = Tile(no, (1 - w) / 2, accY / canvasH, w, h)
                    accY += s.physH
                    t
                }
                (canvasW / canvasH) to tiles
            }
            "grid" -> {
                if (devs.size < 4) return computeTiles("hrow", devs) // 设备数变化时的防御降级
                // 仅 N=4：0,1 上行；2,3 下行。行内按行宽归一化 x/w，y/h 按全画布高。
                val rows = listOf(devs.subList(0, 2), devs.subList(2, 4))
                val rowH = rows.map { r -> r.maxOf { it.second.physH } }
                val rowW = rows.map { r -> r.sumOf { it.second.physW } }
                val canvasH = rowH.sum()
                val canvasW = maxOf(rowW[0], rowW[1])
                val tiles = mutableListOf<Tile>()
                var rowTop = 0.0
                rows.forEachIndexed { ri, row ->
                    var accX = 0.0
                    row.forEach { (no, s) ->
                        val x = accX / rowW[ri]
                        val w = s.physW / rowW[ri]
                        val h = s.physH / canvasH
                        val y = (rowTop + (rowH[ri] - s.physH) / 2) / canvasH
                        tiles.add(Tile(no, x, y, w, h))
                        accX += s.physW
                    }
                    rowTop += rowH[ri]
                }
                (canvasW / canvasH) to tiles
            }
            else -> { // hrow（含 third 的计算本体）
                val canvasW = devs.sumOf { it.second.physW }
                val canvasH = devs.maxOf { it.second.physH }
                var accX = 0.0
                val tiles = devs.map { (no, s) ->
                    val w = s.physW / canvasW
                    val h = s.physH / canvasH
                    val t = Tile(no, accX / canvasW, (1 - h) / 2, w, h)
                    accX += s.physW
                    t
                }
                (canvasW / canvasH) to tiles
            }
        }
    }

    /** v0.6.1：当前活跃成员编号（升序）——主机 0 恒在；从机须在设备表中且未退出播放。布局计算与自动重排的统一口径。 */
    private fun activeNos(): List<Int> =
        deviceSizes.keys.filter { it == 0 || !clientExited.contains(it) }.sorted()

    /**
     * v0.6.1：模式在给定活跃台数下的有效形态——田字格仅 4 台成立：3 台回退横排三等分、2 台回退横排
     * （三等分计算本体即 hrow，故回退统一落 hrow）；横排/竖排任意台数同族重算；全屏跟随恒成立（单台即全屏）。
     * 所选模式本身（currentMode）不被回退改写：成员数恢复后（如退出者重入凑回 4 台）自动回到田字格。
     */
    private fun resolveEffectiveMode(mode: String, activeCount: Int): String = when (mode) {
        "grid" -> if (activeCount == 4) "grid" else "hrow"
        "third" -> "hrow"
        else -> mode
    }

    /**
     * v0.6.1：成员变化自动重排——按活跃集重算切片并重发 LAYOUT（既有语义即时生效、播放不中断、不重新备片）；
     * fit 保持用户所选（仅 contain_v 单台回落规则为例外，在 doSendLayout 内统一把关）。
     */
    private fun relayout(reason: String) {
        val mode = currentMode ?: return
        val active = activeNos()
        doSendLayout(mode)
        klog("LAYOUT relayout reason=$reason active=[${active.joinToString(",")}] mode=${resolveEffectiveMode(mode, active.size)}")
    }

    private fun doSendLayout(mode: String) {
        enforceContainV() // v0.6.1：contain_v 仅单台全屏——活跃成员数不符时先回落 contain_h 再下发
        val active = activeNos()
        val devs = deviceSizes.entries.sortedBy { it.key }.filter { it.key in active }.map { it.key to it.value }
        if (devs.isEmpty()) { setStatus("设备表为空，无法下发布局"); return }
        currentMode = mode
        val effMode = resolveEffectiveMode(mode, devs.size)
        val (ratio, tiles) = computeTiles(effMode, devs)
        val arr = org.json.JSONArray()
        tiles.forEach { t ->
            arr.put(JSONObject().put("client_no", t.no).put("x", t.x).put("y", t.y).put("w", t.w).put("h", t.h))
        }
        val layoutMsg = msg("LAYOUT").put("canvas_ratio", ratio).put("tiles", arr).put("fit", layoutFit)
        server?.broadcast(layoutMsg.toString())
        klog("LAYOUT mode=$effMode fit=$layoutFit canvas_ratio=${fmt4(ratio)} tiles=" +
            tiles.joinToString("; ") { "no=${it.no} x=${fmt4(it.x)} y=${fmt4(it.y)} w=${fmt4(it.w)} h=${fmt4(it.h)}" })
        // 主机自身应用本机 tile
        canvasRatio = ratio
        myTile = tiles.firstOrNull { it.no == 0 } ?: Tile(0, 0.0, 0.0, 1.0, 1.0)
        applyTileTransform()
        setStatus("已下发布局 mode=$effMode（${devs.size} 台）")
    }

    // ---------- v0.6.0：主机覆盖层分页 ----------
    /** 分页签切换：只切四页容器显隐与页签选中态（样式沿用布局胶囊的 styleModePill），不触碰任何业务状态。 */
    private fun selectHostPage(key: String) {
        hostPageBoxes.forEach { (k, page) -> page.visibility = if (k == key) View.VISIBLE else View.GONE }
        hostTabBtns.forEach { (k, b) -> styleModePill(b, k == key) }
    }

    /** 主机「结束会话」：停掉服务端、 tick 循环、分发与互传服务后返回角色选择（播放器对象留待下次建会话时复用/重建）。 */
    private fun endHostSession() {
        val s = server
        server = null
        Thread { try { s?.stop(500) } catch (e: Exception) {} }.start()
        tickJob?.cancel(); tickJob = null
        stopXferServer("session_end")
        stopMediaServer()
        try { player?.pause() } catch (e: Exception) {}
        started = false; sessionActive = false; playbackEnded = false; localPaused = false
        clientConns.clear(); clientReady.clear(); clientFailed.clear(); clientExited.clear(); deviceSizes.clear()
        updateKeepScreenOn()
        chromeReset() // v0.6.1：结束会话即撤 CHROME（原直接隐藏条的一行改走生命周期出口）
        klog("host session ended by user")
        buildRolePickerUi()
    }

    // ---------- v0.6.3：主机「退出播放」（新消息 STOP，协议 §15 v1.8 增补） ----------
    /**
     * 主机「退出播放／退出此视频」：广播 STOP 结束当前视频的播放会话，本机同步执行同一清除（execStopPlayback）。
     * 组会不散——连接、编号、布局模式与 fit 选择全部保留，退出后重新选片即可再走 PREPARE→START。
     * 发起入口仅主机有两处（同一处理函数）：常显工具条「退出播放」按钮、面板「播放」页同名按钮；从机不设发起入口。
     */
    private fun hostStopPlayback() {
        if (role != "host") return
        server?.broadcast(msg("STOP").toString())
        klog("STOP sent")
        execStopPlayback()
    }

    /**
     * STOP 本机执行（主机点按钮本地执行、从机收到 STOP 时执行，同一函数）：
     * 停播放器并清除当前媒体与备片状态、进度归零、离开播放 UI；
     * 主机回大厅待选片（分发服务停掉回空闲、就绪表清零、起播键复位），从机回待机大数字屏、状态行「等待主机选片」。
     * 连接保持不断；本机已无媒体时只做状态复位（幂等，cleared=false）——含从机已本地退出播放后再收到 STOP 的情形。
     * 注意：从机执行 STOP 不回 EXIT_PLAYBACK（那是本机主动退出的通知语义），主机侧退出标记不因 STOP 增减。
     */
    private fun execStopPlayback() {
        val cleared = mediaKind != "none" || started || playbackEnded || mediaReady || remoteMediaUrl != null
        tickJob?.cancel(); tickJob = null
        remoteTimeoutJob?.cancel()
        distDownloadGen++ // 作废进行中的分发下载结果（同退出/断开处理口径）
        downloadingDist = false
        releasePlayWakeLock("stop")
        try { player?.stop() } catch (e: Exception) {}
        player?.release()
        player = null
        started = false; localPaused = false; playbackEnded = false
        mediaReady = false; prepareRequested = false
        if (role == "host") {
            mediaKind = "none"; hostFileUri = null; hostLinkUrl = null
            stopMediaServer() // 本场分发停掉，媒体服务回空闲
            clientReady.clear(); clientFailed.clear()
            playPauseBtn?.text = "起播"
            seekBar?.max = 0; seekBar?.progress = 0
            timeTv?.text = "00:00 / 00:00"
        } else {
            remoteMediaUrl = null
            sourceTv?.text = "来源：—"
        }
        if (::textureView.isInitialized) {
            textureView.rotation = 0f
            textureView.scaleX = 1f
            textureView.scaleY = 1f
        }
        hideClientBar()
        exitPlaybackUi("stop")
        klog("STOP exec cleared=$cleared")
        if (role == "host") {
            setStatus("已退出当前视频（组会保留），重新选片后点「准备」即可再播")
        } else {
            // v0.6.5：从机大编号重现已由 exitPlaybackUi("stop") 统一出口处理，此处不再重复直设
            setStatus("等待主机选片")
        }
    }

    // ---------- v0.6.0/v0.6.1：显示模式三档（铺满 cover / 完整·横向 contain_h / 完整·竖向 contain_v，全场设置） ----------
    /** 主机选定显示模式：存全场状态、刷新三档胶囊；已下发过布局时以同一 mode 重新下发（新 LAYOUT 携带 fit），未下发时仅本机按新 fit 重算。 */
    private fun setLayoutFit(fitIn: String) {
        val fit = if (fitIn == "contain") "contain_h" else fitIn // v0.6.0 旧值 contain 改名归 contain_h
        if (fit != "cover" && fit != "contain_h" && fit != "contain_v") return
        if (fit == "contain_v" && activeNos().size != 1) {
            // 完整·竖向仅单台全屏（胶囊在多台时本不出现，此为兜底守卫）
            setStatus("完整·竖向仅适用于单台全屏（当前活跃 ${activeNos().size} 台）")
            refreshFitPills()
            return
        }
        layoutFit = fit
        refreshFitPills()
        val m = currentMode
        if (m != null) doSendLayout(m) else applyTileTransform()
        setStatus(when (fit) {
            "cover" -> "显示模式：铺满（裁切）"
            "contain_h" -> "显示模式：完整·横向（留边）"
            else -> "显示模式：完整·竖向（旋转 90°）"
        })
    }

    private fun refreshFitPills() {
        fitCoverBtn?.let { styleModePill(it, layoutFit == "cover") }
        fitContainBtn?.let { styleModePill(it, layoutFit == "contain_h") }
        // v0.6.1：完整·竖向胶囊仅在单台全屏（活跃成员恰 1 台）时出现，多台布局不提供该档
        fitContainVBtn?.let {
            styleModePill(it, layoutFit == "contain_v")
            it.visibility = if (activeNos().size == 1) View.VISIBLE else View.GONE
        }
        fitHintTv?.text = when (layoutFit) {
            "cover" -> "铺满会裁切画面：满屏但丢内容，不算完整显示"
            "contain_h" -> "完整显示：整幅画面放下，空缺处留黑边"
            else -> "完整显示：整幅旋转 90° 放下（仅单台全屏）"
        }
    }

    /**
     * v0.6.1：contain_v 的成员数回落规则——所选为完整·竖向而活跃成员回到多台时，自动回落完整·横向并在状态行提示；
     * 在每次 LAYOUT 下发前统一把关（doSendLayout 入口调用），保证下发的 fit 永远合法。返回是否发生了回落。
     */
    private fun enforceContainV(): Boolean {
        if (layoutFit != "contain_v" || activeNos().size == 1) return false
        layoutFit = "contain_h"
        refreshFitPills()
        setStatus("成员数已回到多台，显示模式自动回落：完整·竖向 → 完整·横向")
        return true
    }

    // ---------- v0.6.0：布局图示选择器 ----------
    /** 当前设备数可选的模式集（沿用既有计算与守卫：third 本体为横排、grid 仅 4 台成立，n>4 时 grid 卡片在点击时由既有守卫回绝）。 */
    private fun layoutModesForCount(n: Int): List<Pair<String, String>> = when {
        n <= 1 -> listOf("full" to "全屏跟随", "hrow" to "横排拼", "vcol" to "竖排拼")
        n == 2 -> listOf("hrow" to "横排拼", "vcol" to "竖排拼（上下）", "full" to "全屏跟随")
        n == 3 -> listOf("hrow" to "横排拼", "vcol" to "竖排拼", "third" to "三等分")
        else -> listOf("hrow" to "横排拼", "vcol" to "竖排拼", "grid" to "田字格", "full" to "全屏跟随")
    }

    /**
     * 示意图数据：(画布宽 mm, 画布高 mm, tiles)。tiles 与下发同源（computeTiles），仅 third 例外——
     * third 的下发本体走既有 hrow 计算，示意图按其名义语义画等分三列，便于与横排拼区分。
     */
    private fun layoutDiagram(mode: String, devs: List<Pair<Int, DevSize>>): Triple<Double, Double, List<Tile>> {
        val eff = if (mode == "third") "hrow" else mode
        val canvasW: Double; val canvasH: Double
        when (eff) {
            "vcol" -> { canvasW = devs.maxOf { it.second.physW }; canvasH = devs.sumOf { it.second.physH } }
            "grid" -> if (devs.size >= 4) {
                val r0 = devs.subList(0, 2); val r1 = devs.subList(2, devs.size.coerceAtMost(4))
                canvasW = maxOf(r0.sumOf { it.second.physW }, r1.sumOf { it.second.physW })
                canvasH = r0.maxOf { it.second.physH } + r1.maxOf { it.second.physH }
            } else { canvasW = devs.sumOf { it.second.physW }; canvasH = devs.maxOf { it.second.physH } }
            "full" -> { canvasW = devs.maxOf { it.second.physW }; canvasH = devs.maxOf { it.second.physH } }
            else -> { canvasW = devs.sumOf { it.second.physW }; canvasH = devs.maxOf { it.second.physH } }
        }
        if (mode == "third" && devs.size == 3) {
            var accX = 0.0
            val eq = devs.map { (no, s) ->
                val w = 1.0 / 3.0
                val h = s.physH / canvasH
                val t = Tile(no, accX, (1 - h) / 2, w, h)
                accX += w
                t
            }
            return Triple(canvasW, canvasH, eq)
        }
        val (_, tiles) = computeTiles(eff, devs)
        return Triple(canvasW, canvasH, tiles)
    }

    /** 布局示意图：按真实物理毫米成比例画矩形（相邻矩形间留 2mm 等效间隙＝每侧内缩 1mm），矩形内金字标编号。全屏跟随画单矩形并排全部编号。 */
    private inner class LayoutDiagramView(
        private val canvasWmm: Double,
        private val canvasHmm: Double,
        private val tiles: List<Tile>,
        private val overlapAll: Boolean
    ) : View(this) {
        private val fillPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.FILL; color = 0xFF22222C.toInt() }
        private val strokePaint = Paint(Paint.ANTI_ALIAS_FLAG).apply { style = Paint.Style.STROKE; color = colStroke; strokeWidth = dp(1).toFloat() }
        private val numPaint = Paint(Paint.ANTI_ALIAS_FLAG).apply {
            color = colGold; textSize = dp(17).toFloat(); typeface = Typeface.DEFAULT_BOLD; textAlign = Paint.Align.CENTER
        }

        override fun onDraw(canvas: Canvas) {
            super.onDraw(canvas)
            if (canvasWmm <= 0 || canvasHmm <= 0 || tiles.isEmpty()) return
            val pad = dp(8).toFloat()
            val availW = width - pad * 2
            val availH = height - pad * 2
            if (availW <= 0 || availH <= 0) return
            val k = minOf(availW / canvasWmm, availH / canvasHmm).toFloat() // px 每 mm
            val cw = (canvasWmm * k).toFloat(); val ch = (canvasHmm * k).toFloat()
            val ox = (width - cw) / 2; val oy = (height - ch) / 2
            val inset = 1.0f * k // 每侧内缩 1mm → 相邻矩形间 2mm 等效间隙
            val r = dp(6).toFloat()
            fun drawTile(l: Float, t: Float, rr: Float, b: Float, label: String) {
                if (rr <= l || b <= t) return
                canvas.drawRoundRect(l, t, rr, b, r, r, fillPaint)
                canvas.drawRoundRect(l, t, rr, b, r, r, strokePaint)
                val fm = numPaint.fontMetrics
                canvas.drawText(label, (l + rr) / 2, (t + b) / 2 - (fm.ascent + fm.descent) / 2, numPaint)
            }
            if (overlapAll) {
                drawTile(ox + inset, oy + inset, ox + cw - inset, oy + ch - inset,
                    tiles.joinToString(" · ") { it.no.toString() })
                return
            }
            tiles.forEach { t ->
                drawTile(
                    ox + (t.x * cw).toFloat() + inset, oy + (t.y * ch).toFloat() + inset,
                    ox + ((t.x + t.w) * cw).toFloat() - inset, oy + ((t.y + t.h) * ch).toFloat() - inset,
                    t.no.toString()
                )
            }
        }
    }

    /** 按当前设备表重绘布局卡片（设备数变化时由 refreshDevicesTv 顺带调用；未建主机页时为空操作）。点卡即按既有 hostLayoutMode 下发。 */
    private fun rebuildLayoutCards() {
        val box = layoutCardsBox ?: return
        runOnUiThread {
            if (layoutCardsBox !== box) return@runOnUiThread
            box.removeAllViews()
            layoutCardViews.clear()
            val activeCards = activeNos()
            val devs = deviceSizes.entries.sortedBy { it.key }.filter { it.key in activeCards }.map { it.key to it.value }
            if (devs.isEmpty()) return@runOnUiThread
            layoutModesForCount(devs.size).forEach { (mode, label) ->
                val (cw, ch, tiles) = layoutDiagram(mode, devs)
                val card = LinearLayout(this).apply {
                    orientation = LinearLayout.VERTICAL
                    background = roundedDrawable(colPanel, 16, if (mode == layoutSelectedMode) colGold else colStroke)
                    setPadding(dp(10), dp(10), dp(10), dp(10))
                    layoutParams = stackLp(10)
                    isClickable = true; isFocusable = true
                    setOnClickListener {
                        layoutSelectedMode = mode
                        hostLayoutMode(mode)
                        refreshLayoutCardSelection()
                    }
                }
                val diagram = LayoutDiagramView(cw, ch, tiles, mode == "full")
                diagram.layoutParams = LinearLayout.LayoutParams(LinearLayout.LayoutParams.MATCH_PARENT, dp(110))
                card.addView(diagram)
                card.addView(TextView(this).apply {
                    text = label; textSize = 13f; setTextColor(colSub); gravity = Gravity.CENTER
                    layoutParams = stackLp(6)
                })
                layoutCardViews[mode] = card
                box.addView(card)
            }
        }
    }

    private fun refreshLayoutCardSelection() {
        layoutCardViews.forEach { (mode, card) ->
            card.background = roundedDrawable(colPanel, 16, if (mode == layoutSelectedMode) colGold else colStroke)
        }
    }

    // ---------- v0.6.0：扫码连接（主机出码 / 从机扫码） ----------
    /** ZXing 生成二维码位图（白底黑码，系统相机与自研扫码均可识别）。 */
    private fun makeQrBitmap(text: String, sizePx: Int): Bitmap? {
        return try {
            val matrix = QRCodeWriter().encode(text, BarcodeFormat.QR_CODE, sizePx, sizePx)
            val pixels = IntArray(sizePx * sizePx)
            for (y in 0 until sizePx) for (x in 0 until sizePx) {
                pixels[y * sizePx + x] = if (matrix.get(x, y)) 0xFF000000.toInt() else 0xFFFFFFFF.toInt()
            }
            Bitmap.createBitmap(sizePx, sizePx, Bitmap.Config.ARGB_8888).apply { setPixels(pixels, 0, sizePx, 0, 0, sizePx, sizePx) }
        } catch (e: Exception) { klog("QR encode fail: ${e.message}"); null }
    }

    /** 从机点「扫码连接」：先查相机权限（被拒走手输兜底），有权限才开扫码界面。 */
    private fun startQrScan() {
        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(arrayOf(Manifest.permission.CAMERA), REQ_CAMERA)
            setStatus("扫码需要相机权限（也可在上方手输 IP 连接）")
            return
        }
        openQrScanner()
    }

    override fun onRequestPermissionsResult(requestCode: Int, permissions: Array<out String>, grantResults: IntArray) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (requestCode == REQ_CAMERA) {
            if (grantResults.isNotEmpty() && grantResults[0] == PackageManager.PERMISSION_GRANTED) openQrScanner()
            else setStatus("相机权限被拒，请手输主机 IP 连接")
        }
    }

    /** 扫码界面：全屏 SurfaceView 预览（平台 Camera API）＋提示行＋取消按钮，挂 stage 顶层。 */
    private fun openQrScanner() {
        if (qrScannerBox != null) return
        val box = FrameLayout(this)
        box.setBackgroundColor(colBg)
        box.layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)
        val surface = SurfaceView(this)
        surface.layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.MATCH_PARENT)
        box.addView(surface)
        box.addView(TextView(this).apply {
            text = "将主机二维码对准画面，识别后自动连接"
            textSize = 15f; setTextColor(colText); gravity = Gravity.CENTER
            layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.TOP)
                .apply { topMargin = dp(48); leftMargin = dp(16); rightMargin = dp(16) }
        })
        box.addView(Button(this).apply {
            text = "取消扫码"
            styleGhostButton(this)
            layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.WRAP_CONTENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.BOTTOM or Gravity.CENTER_HORIZONTAL)
                .apply { bottomMargin = dp(40) }
            setOnClickListener { closeQrScanner(cancelled = true) }
        })
        stage.addView(box)
        qrScannerBox = box
        qrScanning = true
        surface.holder.addCallback(object : SurfaceHolder.Callback {
            override fun surfaceCreated(holder: SurfaceHolder) { startQrCamera(holder) }
            override fun surfaceChanged(holder: SurfaceHolder, format: Int, w: Int, h: Int) {}
            override fun surfaceDestroyed(holder: SurfaceHolder) { stopQrCamera() }
        })
        setStatus("扫码中…")
    }

    private fun startQrCamera(holder: SurfaceHolder) {
        try {
            val cam = Camera.open()
            qrCamera = cam
            val params = cam.parameters
            val size = params.supportedPreviewSizes.filter { it.width <= 1280 }.maxByOrNull { it.width * it.height } ?: params.previewSize
            params.setPreviewSize(size.width, size.height)
            if (params.supportedFocusModes.contains(Camera.Parameters.FOCUS_MODE_CONTINUOUS_PICTURE)) {
                params.focusMode = Camera.Parameters.FOCUS_MODE_CONTINUOUS_PICTURE
            }
            cam.parameters = params
            cam.setDisplayOrientation(90)
            cam.setPreviewDisplay(holder)
            cam.setPreviewCallback { data, _ -> onQrPreviewFrame(data, size.width, size.height) }
            cam.startPreview()
        } catch (e: Exception) {
            klog("JOIN qr camera fail: ${e.message}")
            setStatus("相机打开失败，请手输主机 IP 连接")
            closeQrScanner(cancelled = true)
        }
    }

    private fun stopQrCamera() {
        try { qrCamera?.setPreviewCallback(null); qrCamera?.stopPreview(); qrCamera?.release() } catch (e: Exception) {}
        qrCamera = null
    }

    private fun closeQrScanner(cancelled: Boolean) {
        qrScanning = false
        stopQrCamera()
        qrScannerBox?.let { (it.parent as? android.view.ViewGroup)?.removeView(it) }
        qrScannerBox = null
        if (cancelled) klog("JOIN qr cancel")
    }

    /** 预览帧节流喂 ZXing 解码（至多每 250ms 一帧、同一时刻只解一帧）：原始方向、正反各一次旋转方向共三种朝向尝试。 */
    private fun onQrPreviewFrame(data: ByteArray, w: Int, h: Int) {
        if (!qrScanning || qrDecoding) return
        val now = System.currentTimeMillis()
        if (now - lastQrTryMs < 250) return
        lastQrTryMs = now
        qrDecoding = true
        val copy = data.copyOf()
        Thread {
            try { tryDecodeQr(copy, w, h) } catch (e: Exception) {}
            qrDecoding = false
        }.start()
    }

    private fun tryDecodeQr(data: ByteArray, w: Int, h: Int) {
        val reader = QRCodeReader()
        fun attempt(bytes: ByteArray, dw: Int, dh: Int): String? = try {
            val src = PlanarYUVLuminanceSource(bytes, dw, dh, 0, 0, dw, dh, false)
            reader.decode(BinaryBitmap(HybridBinarizer(src))).text
        } catch (e: Exception) { null }
        var text = attempt(data, w, h)
        if (text == null) {
            // 顺时针 90°：新宽=h、新高=w，dst[y2*h + x2] = src[y*w + x]，(x2,y2)=(h-1-y, x)
            val rot = ByteArray(data.size)
            for (y in 0 until h) for (x in 0 until w) rot[x * h + (h - 1 - y)] = data[y * w + x]
            text = attempt(rot, h, w)
        }
        if (text == null) {
            // 逆时针 90°：(x2,y2)=(y, w-1-x)
            val rot = ByteArray(data.size)
            for (y in 0 until h) for (x in 0 until w) rot[(w - 1 - x) * h + y] = data[y * w + x]
            text = attempt(rot, h, w)
        }
        if (text != null && text.startsWith("duoping://")) onQrDecoded(text)
    }

    /** 扫码成功：解析 duoping://<ip>:<port>/<令牌>，回填 IP 输入框并直接发起连接（令牌随组会机制保留，本端连接暂不校验）。 */
    private fun onQrDecoded(text: String) {
        val body = text.removePrefix("duoping://")
        val hostPart = body.substringBefore('/')
        val ip = hostPart.substringBefore(':').trim()
        if (ip.isEmpty()) return
        runOnUiThread {
            if (!qrScanning) return@runOnUiThread
            klog("JOIN qr ok ip=$ip")
            closeQrScanner(cancelled = false)
            clientIpInput?.setText(ip)
            connectClient(ip)
        }
    }

    // ---------- CLIENT UI ----------
    private fun buildClientUi() {
        role = "client"
        controlsCol.removeAllViews()
        controlsCol.addView(TextView(this).apply {
            text = "从机模式"; textSize = 20f; setTextColor(colText); setTypeface(null, Typeface.BOLD)
        })
        val ipInput = EditText(this).apply {
            hint = "主机 IP，例如 192.168.1.10"; setText(lastHostIp())
            styleInput(this); layoutParams = stackLp(14)
        }
        controlsCol.addView(ipInput)
        clientIpInput = ipInput // v0.6.0：扫码成功后回填本框
        statusTv = TextView(this).apply {
            text = "未连接"; textSize = 15f; setTextColor(colText)
            layoutParams = stackLp(10)
        }
        controlsCol.addView(Button(this).apply {
            text = "连接主机"
            stylePrimaryButton(this)
            layoutParams = stackLp(12)
            setOnClickListener {
                val ip = ipInput.text.toString().trim()
                if (ip.isNotEmpty()) connectClient(ip)
            }
        })
        controlsCol.addView(Button(this).apply {
            text = "扫码连接"
            styleGhostButton(this)
            setTextColor(colGold)
            layoutParams = stackLp(10)
            setOnClickListener { startQrScan() }
        })
        controlsCol.addView(pickButton())
        controlsCol.addView(Button(this).apply {
            text = "闪号"
            styleGhostButton(this)
            setTextColor(colGold)
            layoutParams = stackLp(10)
            setOnClickListener { flashNumber() }
        })
        controlsCol.addView(Button(this).apply {
            text = "断开并返回角色选择"
            styleGhostButton(this)
            setTextColor(colDanger)
            layoutParams = stackLp(10)
            setOnClickListener { disconnectClient() }
        })
        // v0.6.0：从机覆盖层分区标题——连接区（上）／本机调节（中）／互传区（下）
        controlsCol.addView(TextView(this).apply {
            text = "本机调节"; textSize = 16f; setTextColor(colText); setTypeface(null, Typeface.BOLD)
            layoutParams = stackLp(24)
        })
        // 改动三：从机本机亮度滑杆（只调本机；收到主机 BRIGHTNESS 时以主机值为准覆盖）
        controlsCol.addView(TextView(this).apply {
            text = "本机亮度（主机广播会覆盖本机值）"; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(16)
        })
        val brightBar = makeBrightnessBar { level ->
            applyBrightness(level)
            klog("BRIGHTNESS level=${fmt2(level.toDouble())} local applied=true")
        }
        clientBrightBar = brightBar
        controlsCol.addView(brightBar)
        // 改动五：从机本机色温滑杆（只调本机、不广播）
        controlsCol.addView(TextView(this).apply {
            text = "本机色温（左冷右暖，仅本机不广播）"; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(12)
        })
        controlsCol.addView(makeTintBar())
        controlsCol.addView(statusTv)
        sourceTv = TextView(this).apply {
            text = "来源：—"; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(6)
        }
        controlsCol.addView(sourceTv)
        buildXferSection(controlsCol) // v0.5.0：文件互传区（从机页；v0.6.0 分区呈现，仍挂主列）
    }

    private fun disconnectClient() {
        try { wsClient?.close() } catch (e: Exception) {}
        wsClient = null
        // v0.5.0：断开即终止本机互传（发送服务关停、接收代次作废）
        stopXferServer("disconnect")
        xferSendTid = null
        xferRecvGen++
        xferRecvTid = null
        hideXferBanner()
        remoteMediaUrl = null
        distDownloadGen++ // v0.3.2：作废进行中的分发下载结果
        downloadingDist = false
        remoteTimeoutJob?.cancel()
        sessionActive = false
        updateKeepScreenOn()
        started = false
        localPaused = false
        releasePlayWakeLock("disconnect")
        exitPlaybackUi("disconnect")
        role = "none"
        klog("client disconnected by user")
        buildRolePickerUi()
    }

    private fun lastHostIp(): String = ""

    private fun connectClient(ip: String) {
        connectedHostIp = ip
        try { wsClient?.close() } catch (e: Exception) {}
        val c = KernelClient("ws://$ip:$PORT")
        wsClient = c
        c.connect()
        setStatus("连接中: $ip:$PORT")
        klog("client connecting to $ip:$PORT")
    }

    private fun flashNumber() {
        if (myNo < 0) return
        // v0.6.5：播放中不许任何路径把大编号带回画面（含本闪烁认领）；待机闪烁不受影响
        if (inPlaybackSession()) { klog("UI number flash suppressed during playback"); return }
        scope.launch {
            bigNoTv.text = myNo.toString()
            repeat(6) {
                bigNoTv.visibility = View.VISIBLE; delay(280)
                bigNoTv.visibility = View.GONE; delay(180)
            }
            bigNoTv.visibility = View.GONE
        }
    }

    // ---------- player ----------
    override fun onActivityResult(requestCode: Int, resultCode: Int, data: Intent?) {
        super.onActivityResult(requestCode, resultCode, data)
        // v0.5.0：互传多选文件回来——收集全部 Uri 并后台逐个算 size 与 SHA-256
        if (requestCode == REQ_PICK_XFER) {
            if (resultCode == RESULT_OK) {
                val uris = mutableListOf<Uri>()
                val clip = data?.clipData
                if (clip != null) {
                    for (i in 0 until clip.itemCount) clip.getItemAt(i)?.uri?.let { uris.add(it) }
                } else {
                    data?.data?.let { uris.add(it) }
                }
                if (uris.isNotEmpty()) onXferFilesPicked(uris)
                else setStatus("没有选到文件")
            }
            return
        }
        // v0.5.0：接收文件夹（SAF）授权回来——授权成功则持久化；无论选没选都置已问标记，等接受的补走接受流程
        if (requestCode == REQ_PICK_DIR) {
            val treeUri: Uri? = if (resultCode == RESULT_OK) data?.data else null
            if (treeUri != null) {
                try {
                    contentResolver.takePersistableUriPermission(treeUri,
                        Intent.FLAG_GRANT_READ_URI_PERMISSION or Intent.FLAG_GRANT_WRITE_URI_PERMISSION)
                } catch (e: Exception) { klog("XFER dest persist fail: ${e.message}") }
                xferDirUri = treeUri
                getSharedPreferences("duoping", Context.MODE_PRIVATE).edit()
                    .putString("xfer_dir_uri", treeUri.toString()).apply()
                klog("XFER dest dir selected name=${xferDirDisplayName()}")
            }
            xferDirAsked = true
            getSharedPreferences("duoping", Context.MODE_PRIVATE).edit()
                .putBoolean("xfer_dir_asked", true).apply()
            refreshXferDestLabel()
            if (xferPendingAccept) {
                xferPendingAccept = false
                doXferAccept()
            }
            return
        }
        if (requestCode == REQ_PICK && resultCode == RESULT_OK) {
            val uri: Uri = data?.data ?: return
            try { contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION) } catch (e: Exception) {}
            // 改动六入口甲：本地文件成为本场媒体；重新选片即关旧分发服务，下一次 PREPARE 前按新文件重启
            if (role == "host") {
                mediaKind = "local"
                hostFileUri = uri
                stopMediaServer()
            }
            setupPlayer(uri)
        }
    }

    private fun setupPlayer(uri: Uri) {
        remoteTimeoutJob?.cancel() // v0.3.2：新一轮备片作废旧的远程超时计时（流式路径在建播放器后重新 arm）
        player?.release()
        // 改动四：轨道选择器设解码分辨率上限 = 本机屏幕像素宽高（构建时刻的 DisplayMetrics）
        val dm = resources.displayMetrics
        val trackSelector = DefaultTrackSelector(this)
        trackSelector.setParameters(
            trackSelector.buildUponParameters().setMaxVideoSize(dm.widthPixels, dm.heightPixels)
        )
        val p = ExoPlayer.Builder(this).setTrackSelector(trackSelector).build()
        klog("TRACKCAP max=${dm.widthPixels}x${dm.heightPixels} screen=${dm.widthPixels}x${dm.heightPixels}")
        player = p
        p.setVideoTextureView(textureView)
        if (role == "client") p.volume = 0f
        p.addListener(object : Player.Listener {
            override fun onPlaybackStateChanged(state: Int) {
                if (state == Player.STATE_READY && !started) {
                    mediaReady = true
                    remoteTimeoutJob?.cancel() // v0.3.2：15 秒内到达 READY，备片超时计时作废
                    klog("player prepared (READY, paused at ${p.currentPosition}) role=$role")
                    setStatus("已选片并 prepare 完成，停在 0 位置")
                    if (role == "client" && prepareRequested) sendReadyOnce()
                }
                if (state == Player.STATE_BUFFERING && started) {
                    wasBuffering = true
                    // 改动七：卡顿分开计数（仅从机，STAT 上报）——距上次程序 seek <1500ms 记 seek 诱发，其余记加载卡顿
                    if (role == "client") {
                        val sinceSeek = System.currentTimeMillis() - lastProgramSeekMs
                        if (lastProgramSeekMs > 0 && sinceSeek < 1500) {
                            stallsSeek++; stalls++
                            klog("STALL pos=${p.currentPosition} kind=seek stalls_seek=$stallsSeek")
                        } else {
                            stallsLoad++; stalls++
                            klog("STALL pos=${p.currentPosition} kind=load stalls_load=$stallsLoad")
                        }
                    }
                }
                if (state == Player.STATE_READY && started && wasBuffering) {
                    wasBuffering = false
                    if (role == "client") resyncAfterBuffering()
                }
                if (state == Player.STATE_ENDED && started) {
                    started = false
                    playbackEnded = true
                    klog("playback ended role=$role no=$myNo")
                    releasePlayWakeLock("ended")
                    if (role == "host") playPauseBtn?.text = "重新起播"
                    exitPlaybackUi()
                    setStatus("播放结束")
                }
            }
            override fun onRenderedFirstFrame() {
                if (started) klog("first frame rendered at wallclock=${System.currentTimeMillis()}")
            }
            override fun onVideoSizeChanged(videoSize: VideoSize) {
                videoPxW = videoSize.width * videoSize.pixelWidthHeightRatio.toDouble()
                videoPxH = videoSize.height.toDouble()
                val a = if (videoSize.height > 0) (videoSize.width * videoSize.pixelWidthHeightRatio) / videoSize.height else 0f
                if (a > 0 && a != videoAspect) {
                    videoAspect = a
                    klog("video size ${videoSize.width}x${videoSize.height} aspect=$a")
                    if (myTile != null) applyTileTransform()
                }
            }
        })
        p.setMediaItem(MediaItem.fromUri(uri))
        p.prepare()
        p.pause()
        klog("player setup uri=$uri role=$role")
    }

    /** 改动七：程序 seek 统一入口——每次执行前记录时刻 lastProgramSeekMs，供 RESYNC 抑制与 STALL 分开计数区分 seek 诱发缓冲。 */
    private fun programSeek(p: Player, pos: Long) {
        lastProgramSeekMs = System.currentTimeMillis()
        p.seekTo(pos.coerceAtLeast(0))
    }

    /** 同一轮 PREPARE 只回一次 READY（标志位防重复）。 */
    private fun sendReadyOnce() {
        if (readySent) return
        readySent = true
        sendReady()
    }

    private fun sendReady() {
        val buffered = player?.let { it.bufferedPosition - it.currentPosition } ?: 0
        wsClient?.send(msg("READY").put("buffered_ms", buffered).toString())
        klog("client sent READY buffered_ms=$buffered")
        setStatus("已回 READY，等待 START")
    }

    /**
     * 改动六（v0.3.1）：从机远程媒体 prepare 入口。同 url 已备好立即回 READY；已播完回卷后回 READY。
     * v0.3.2：分发模式改走下载后播（startDistDownload），直链模式仍流式 prepare 并 arm 15 秒超时；
     * 新 url 重建播放器，READY 由播放器监听在 STATE_READY 时按 prepareRequested 自动回（与本地模式一致）。
     */
    private fun startRemoteMedia(url: String, fromPrepare: Boolean = false) {
        val uri = Uri.parse(url)
        val path = uri.path ?: ""
        val isDist = uri.host == connectedHostIp && path.startsWith("/media/")
        sourceTv?.text = if (isDist) "来源：主机分发" else "来源：直链"
        val pathLog = if (path.startsWith("/media/")) "/media/***" else path
        klog("MEDIA host=${uri.authority} path=$pathLog mode=${if (isDist) "dist" else "link"}")
        if (remoteMediaUrl == url && downloadingDist) {
            klog("MEDIA same url download in progress")
            return
        }
        val p = player
        if (p != null && remoteMediaUrl == url) {
            when {
                p.playbackState == Player.STATE_ENDED -> {
                    programSeek(p, 0)
                    playbackEnded = false
                    sendReadyOnce()
                    klog("MEDIA same url ended, rewound, READY resent")
                }
                mediaReady && p.playbackState == Player.STATE_READY -> sendReadyOnce()
                else -> {
                    klog("MEDIA same url still preparing")
                    // v0.3.2：用户重走 PREPARE 流程时对未完成的流式备片重新计时（已超时的不自动重试）
                    if (fromPrepare && !isDist) armRemotePrepareTimeout("link")
                    if (fromPrepare && isDist) armRemotePrepareTimeout("dist")
                }
            }
            return
        }
        distDownloadGen++
        remoteMediaUrl = url
        if (isDist) {
            startDistDownload(url)
        } else {
            setupPlayer(uri)
            armRemotePrepareTimeout("link")
        }
    }

    /**
     * v0.3.2 改动一：分发模式先把整文件下载到本机 dist 缓存，再以本地文件建播放器（同步行为与本地模式同构）。
     * 缓存键 = dist-<令牌前8位>-<Content-Length>.bin；命中且字节数一致则跳过下载。
     * 失败（连接错误／字节数不一致／连续 10 秒无新字节）回退 v0.3.1 的流式 prepare 并 arm 分发流式超时。
     */
    private fun startDistDownload(url: String) {
        val gen = distDownloadGen
        val token = Uri.parse(url).lastPathSegment ?: ""
        downloadingDist = true
        setStatus("分发下载中 0%")
        klog("DOWNLOAD start host=${Uri.parse(url).authority} token_prefix=${token.take(8)}")
        Thread {
            var conn: HttpURLConnection? = null
            try {
                // 先用普通 GET 拿到 Content-Length 组缓存键（命中时断开连接不读 body）
                conn = (URL(url).openConnection() as HttpURLConnection).apply {
                    connectTimeout = 10000
                    readTimeout = 10000
                }
                conn.connect()
                val total = conn.contentLengthLong
                val dir = distCacheDir()
                val target = File(dir, "dist-${token.take(8)}-$total.bin")
                // 存储纪律：新一次下载开始时删旧分发缓存，至多保留当前一份
                dir.listFiles()?.forEach { if (it != target) it.delete() }
                if (total > 0 && target.exists() && target.length() == total) {
                    conn.disconnect()
                    klog("DOWNLOAD cache hit file=${target.name} bytes=$total")
                    runOnUiThread {
                        if (gen != distDownloadGen) return@runOnUiThread
                        downloadingDist = false
                        setStatus("分发下载完成（命中缓存）")
                        setupPlayer(Uri.fromFile(target))
                    }
                    return@Thread
                }
                // 未命中：断开探测连接，另开一条连接顺序读整文件（readTimeout 10 秒即「连续 10 秒无新字节」判定）
                conn.disconnect()
                val t0 = System.currentTimeMillis()
                val c2 = (URL(url).openConnection() as HttpURLConnection).apply {
                    connectTimeout = 10000
                    readTimeout = 10000
                }
                c2.connect()
                val total2 = c2.contentLengthLong
                if (total2 != total) throw IllegalStateException("content-length changed $total -> $total2")
                var done = 0L
                var nextPctMark = 25
                c2.inputStream.use { input ->
                    FileOutputStream(target).use { out ->
                        val buf = ByteArray(64 * 1024)
                        while (true) {
                            val n = input.read(buf)
                            if (n < 0) break
                            out.write(buf, 0, n)
                            done += n
                            if (total > 0) {
                                val pct = (done * 100 / total).toInt()
                                setStatus("分发下载中 $pct%")
                                if (pct >= nextPctMark) {
                                    klog("DOWNLOAD progress pct=$pct bytes=$done/$total")
                                    nextPctMark += 25
                                }
                            }
                        }
                    }
                }
                c2.disconnect()
                if (total > 0 && done != total) {
                    target.delete()
                    throw IllegalStateException("size mismatch got=$done expected=$total")
                }
                val took = System.currentTimeMillis() - t0
                klog("DOWNLOAD complete bytes=$done took_ms=$took file=${target.name}")
                runOnUiThread {
                    if (gen != distDownloadGen) return@runOnUiThread
                    downloadingDist = false
                    setStatus("分发下载完成，备片中")
                    setupPlayer(Uri.fromFile(target))
                }
            } catch (e: Exception) {
                try { conn?.disconnect() } catch (_: Exception) {}
                klog("DOWNLOAD fail reason=${e.javaClass.simpleName}: ${e.message}")
                runOnUiThread {
                    if (gen != distDownloadGen) return@runOnUiThread
                    downloadingDist = false
                    setStatus("分发下载失败，回退流式播放")
                    setupPlayer(Uri.parse(url))
                    armRemotePrepareTimeout("dist")
                }
            }
        }.start()
    }

    private fun distCacheDir(): File {
        val base = getExternalFilesDir(null) ?: cacheDir
        return File(base, "dist").apply { mkdirs() }
    }

    /**
     * v0.3.2 改动二：远程流式备片 15 秒超时计时。起点为本次 arm 时刻（prepare 开始或重走 PREPARE 时）；
     * 播放器到达 STATE_READY 时由监听取消；超时只判定一次，不自动重试。
     * 适用：从机直链、从机分发流式回退、主机本机直链。分发下载路径不适用。
     */
    private fun armRemotePrepareTimeout(mode: String) {
        remoteTimeoutJob?.cancel()
        remotePrepareStartMs = System.currentTimeMillis()
        remotePrepareTimedOut = false
        remoteTimeoutJob = scope.launch {
            delay(15000)
            if (remotePrepareTimedOut) return@launch
            val p = player ?: return@launch
            if (!started && p.playbackState != Player.STATE_READY) {
                remotePrepareTimedOut = true
                onRemotePrepareTimeout(mode)
            }
        }
    }

    private fun onRemotePrepareTimeout(mode: String) {
        val waited = System.currentTimeMillis() - remotePrepareStartMs
        if (role == "host") {
            klog("PREPARE_TIMEOUT mode=link role=host waited_ms=$waited")
            setStatus("链接无法直接播放（可能不是直链）")
            return
        }
        klog("PREPARE_TIMEOUT mode=$mode waited_ms=$waited")
        if (mode == "link") {
            setStatus("链接无法直接播放（可能不是直链）")
            wsClient?.send(msg("PREPARE_FAIL").put("client_no", myNo).put("reason", "link_timeout").toString())
        } else {
            setStatus("分发拉取超时")
            wsClient?.send(msg("PREPARE_FAIL").put("client_no", myNo).put("reason", "dist_stream_timeout").toString())
        }
    }

    private fun schedulePlay(startAtHostClock: Long, isHostClock: Boolean, mediaPos: Long = 0) {
        val localStart = if (isHostClock) startAtHostClock else startAtHostClock - offsetMs
        val delayMs = localStart - System.currentTimeMillis()
        klog("schedulePlay startAtHost=$startAtHostClock localStart=$localStart delay=$delayMs media_pos_ms=$mediaPos role=$role no=$myNo")
        scope.launch {
            // 改动七：START 幂等——无论本机是否正在播放，先 seek 到 media_pos 并暂停待命，到点再起播
            // （旧版第二次 START 只重复 play()，本机留在旧时间线，首次 TICK 出现两万多毫秒假偏差）
            val p0 = player
            if (p0 != null) {
                programSeek(p0, mediaPos)
                p0.pause()
                if (!isHostClock) localPaused = true // 待命期让 onTick 走 paused-skip，不做校正
            }
            if (delayMs > 0) delay(delayMs)
            val before = System.currentTimeMillis()
            player?.setPlaybackSpeed(sessionRate)
            appliedRate = sessionRate // v0.3.3 复位点：START 起播实际速率回到会话速率
            rateState = fmtSpeed(sessionRate)
            player?.play()
            started = true
            localPaused = false
            playbackEnded = false
            acquirePlayWakeLock()
            enterPlaybackUi()
            val err = before - localStart
            klog("play() called, start error=${err}ms (actual-call minus target) role=$role no=$myNo")
            setStatus("已起播，起播调用误差 ${err}ms")
        }
    }

    // ---------- client sync ----------
    /** 改动四：首次对时后每 60 秒重跑一轮完整 5 采样对时，offset 原子替换，不触发额外 seek。 */
    private fun startClockSyncLoop() {
        scope.launch(Dispatchers.IO) {
            while (role == "client" && wsClient?.isOpen == true) {
                syncRound++
                doClockSyncRound(syncRound)
                delay(60000)
            }
        }
    }

    private suspend fun doClockSyncRound(round: Int) {
        var bestOffset = 0L; var bestRtt = Long.MAX_VALUE
        repeat(5) {
            val c1 = System.currentTimeMillis()
            val latch = java.util.concurrent.CountDownLatch(1)
            var got: Triple<Long, Long, Long>? = null
            pendingPongs[c1] = { h2, h3, _ -> got = Triple(c1, h2, h3); latch.countDown() }
            wsClient?.send(msg("PING").put("c1", c1).toString())
            latch.await(2, java.util.concurrent.TimeUnit.SECONDS)
            val c4 = System.currentTimeMillis()
            pendingPongs.remove(c1)
            val g = got
            if (g != null) {
                val rtt = (c4 - g.first) - (g.third - g.second)
                val off = ((g.second - g.first) + (g.third - c4)) / 2
                klog("sync sample rtt=$rtt offset=$off round=$round")
                if (rtt < bestRtt) { bestRtt = rtt; bestOffset = off }
            }
            delay(120)
        }
        if (bestRtt != Long.MAX_VALUE) {
            offsetMs = bestOffset; rttMs = bestRtt
            klog("CLOCK_SYNC offset=$offsetMs rtt=$rttMs round=$round")
            setStatus("对时完成 offset=${offsetMs}ms rtt=${rttMs}ms（第 $round 轮）")
        } else {
            klog("CLOCK_SYNC FAILED no pong round=$round")
            setStatus("对时失败：没有收到 PONG（第 $round 轮）")
        }
    }

    private fun onTick(hostClock: Long, mediaPos: Long, hostState: String, tickRate: Float) {
        // 本函数整体须在主线程执行：调用点 KernelClient.onMessage 已用 runOnUiThread 包裹（v0.2.1 线程归位）
        lastTickHostClock = hostClock; lastTickMediaPos = mediaPos
        hostTickState = hostState
        val p = player ?: return
        if (!started) return
        val actual = p.currentPosition
        // 预期进度按协议第 4 节：media_pos + 滞后时间 × rate（rate 为 TICK 携带的主机会话倍速）
        val expected = if (hostState == "paused" || localPaused) mediaPos
            else mediaPos + ((System.currentTimeMillis() + offsetMs - hostClock) * tickRate).toLong()
        val err = actual - expected
        lastErrMs = err
        // 改动七：缓冲期跳过校正——不做任何校正、首次对齐判定也不消耗（firstTickAfterStart 保持待定），只记一行后返回
        if (p.playbackState == Player.STATE_BUFFERING) {
            klog("TICK err=${err}ms action=buffering-skip actual=$actual expected=$expected rate=${fmtRate3(appliedRate)}")
            return
        }
        // 主机 state 为 paused 或本机暂停：跳过校正——实际速率恢复 sessionRate、不 seek，只更新读数
        if (hostState == "paused" || localPaused) {
            if (rateState != fmtSpeed(sessionRate)) {
                p.setPlaybackSpeed(sessionRate); appliedRate = sessionRate; rateState = fmtSpeed(sessionRate)
            }
            klog("TICK err=${err}ms action=paused-skip actual=$actual expected=$expected rate=${fmtRate3(appliedRate)}")
            return
        }
        // 经 TICK 采纳主机会话倍速（主机在起播前或从机入会前改过倍速时由此对齐）——会话速率变更即复位点，实际速率回到新会话速率
        if (tickRate > 0 && abs(tickRate - sessionRate) > 0.001f) {
            sessionRate = tickRate
            p.setPlaybackSpeed(sessionRate); appliedRate = sessionRate; rateState = fmtSpeed(sessionRate)
            klog("RATE sync from TICK rate=$tickRate")
        }
        // v0.3.3：校正再换形——速率微调为唯一常规校正，seek 只留灾难偏差（协议 v1.4 增补，supersede v1.2 校正段）。
        // 依据（真机判读）：每次校正 seek 后约 5 秒只能跑约 1.31 倍速、丢约 0.9 秒——seek 自付约 1 秒代价；
        // v0.3.1 的「>200ms 即 seek」注入的误差比修掉的还大、回路自激。微调不触发该代价，无自激之源。
        var action = "none"
        val nowMs = System.currentTimeMillis()
        val wasFirstTick = firstTickAfterStart
        if (firstTickAfterStart) firstTickAfterStart = false // v0.3.3：只作日志区分（first=1），不再驱动单独 seek 分支；FIRST_TICK_ALIGN 50ms 特例删除
        val absErr = abs(err)
        when {
            absErr <= 30 -> {
                // 死区：不校正；实际速率若偏离会话速率，先恢复为会话速率（rate-restore）
                if (abs(appliedRate - sessionRate) > 0.0001f) {
                    appliedRate = sessionRate
                    p.setPlaybackSpeed(sessionRate); rateState = fmtSpeed(sessionRate)
                    action = "rate-restore"
                    klog("RATE_ADJ err=${err}ms session=${fmtRate3(sessionRate)} applied=${fmtRate3(appliedRate)}")
                }
            }
            absErr <= 2000 -> {
                // 微调区：adj = clamp(-err/10000, -0.05, +0.05)，实际速率 = 会话速率 ×(1+adj)，不许 seek。
                // 符号：err<0（从机落后）→ -err>0 → adj>0 → 速率上调加速追赶；err>0（超前）→ adj<0 → 减速等待。
                val adj = (-err / 10000.0).coerceIn(-0.05, 0.05)
                val target = (sessionRate * (1.0 + adj)).toFloat()
                action = "rate-adj"
                // 与当前实际速率相差 <0.002 不重复下发，避免抖动
                if (abs(target - appliedRate) >= 0.002f) {
                    appliedRate = target
                    p.setPlaybackSpeed(target); rateState = fmtSpeed(target)
                    klog("RATE_ADJ err=${err}ms session=${fmtRate3(sessionRate)} applied=${fmtRate3(target)}")
                }
            }
            else -> {
                // 灾难偏差（>2000ms）：才许 seek，沿用 8 秒冷却（冷却只约束 seek）
                if (nowMs < seekCooldownUntilMs) {
                    action = "cooldown-skip"
                    klog("TICK cooldown-skip err=${err}ms remain_s=${(seekCooldownUntilMs - nowMs + 999) / 1000}")
                } else {
                    programSeek(p, expected)
                    hardCorrections++
                    action = "seek"
                    seekCooldownUntilMs = nowMs + 8000
                    klog("HARD_CORRECTION err=${err}ms seekTo=$expected count=$hardCorrections")
                }
            }
        }
        klog("TICK err=${err}ms action=$action actual=$actual expected=$expected rate=${fmtRate3(appliedRate)}" + if (wasFirstTick) " first=1" else "")
    }

    private fun resyncAfterBuffering() {
        if (lastTickHostClock == 0L) return
        val p = player ?: return
        val now = System.currentTimeMillis()
        // 改动七其一：seek 诱发抑制——距上次程序 seek <1500ms 的缓冲结束判定为 seek 诱发，不触发 RESYNC
        if (lastProgramSeekMs > 0 && now - lastProgramSeekMs < 1500) {
            klog("RESYNC skip=seek-induced since_seek_ms=${now - lastProgramSeekMs}")
            return
        }
        val hostNow = System.currentTimeMillis() + offsetMs
        val expected = lastTickMediaPos + (hostNow - lastTickHostClock)
        val from = p.currentPosition
        val err = from - expected
        // v0.3.3：偏差门改 micro-band——|err| ≤2000ms 不许 seek，交播中速率微调收敛（取代改动七的 300ms small-err 门）
        if (abs(err) <= 2000) {
            klog("RESYNC skip=micro-band err=${err}ms")
            return
        }
        // 改动七其三：RESYNC 冷却——两次 RESYNC 间隔 <5 秒不执行第二次
        if (lastResyncMs > 0 && now - lastResyncMs < 5000) {
            klog("RESYNC skip=cooldown err=${err}ms")
            return
        }
        lastResyncMs = now
        programSeek(p, expected)
        hardCorrections++
        wsClient?.send(msg("RESYNC").put("from_pos", from).put("to_pos", expected).toString())
        klog("RESYNC after buffering from=$from to=$expected err=${err}ms")
    }

    private fun startStatLoop() {
        scope.launch {
            while (true) {
                delay(10000)
                if (role == "client" && wsClient?.isOpen == true) {
                    val p = player
                    val stat = msg("STAT")
                        .put("media_pos_ms", p?.currentPosition ?: -1)
                        .put("err_ms", lastErrMs)
                        .put("buffered_ms", p?.let { it.bufferedPosition - it.currentPosition } ?: 0)
                        .put("corrections", hardCorrections)
                        .put("stalls", stalls)
                        .put("stalls_load", stallsLoad)
                        .put("stalls_seek", stallsSeek)
                    wsClient?.send(stat.toString())
                    klog("STAT sent $stat")
                }
            }
        }
    }

    // ---------- layout rendering (v0.2: cover-fit canvas + own tile) ----------
    /**
     * 渲染管线（v0.6.4 重构）：完整视频先按 canvas_ratio 铺进虚拟画布（cover 裁切 / contain 留边），
     * 再取本机 tile 对应的子区域显示。用 TextureView 的 scale/pivot 实现（锚点公式同 v0.2：
     * pivot = b * V / (1 - a)，使区域左缘恰落到屏幕左缘）。
     *
     * 等比锁死（不变形原则）：只求一个标量像素缩放 s——cover 取两轴商的 max、contain 取 min；
     * 两轴的分数仿射都由 s 反推（A = s * 视频像素 / 屏幕像素），平移把目标区域居中。
     * 于是日志的 scaleX 与 scaleY 恒为同一个 s，warn=aniso 结构性不可触发（判定保留作守卫）。
     * 几何来源：屏幕尺寸一律取 stableScreenPx() 的面板真实尺寸，不再读 TextureView 的瞬时
     * measured 值（沉浸落定前可为 2307 等中间值，正是 v0.3 起残留 1.9% 变形的来源）；
     * 舞台尺寸变化时经 stage 的 OnLayoutChange 重算，残余瞬时态在一个布局帧内自愈。
     */
    private fun applyTileTransform() {
        val tile = myTile ?: Tile(myNo, 0.0, 0.0, 1.0, 1.0)
        runOnUiThread {
            if (!::textureView.isInitialized) return@runOnUiThread
            val (vw, vh) = stableScreenPx()
            if (vw == 0 || vh == 0) { textureView.post { applyTileTransform() }; return@runOnUiThread }
            val cr = canvasRatio
            val va = videoAspect.toDouble()
            var rx: Double; var ry: Double; var rw: Double; var rh: Double // 日志 region：视频坐标中落在本屏的可见子矩形
            // v0.6.1：fit 三档——cover 铺满裁切；contain_h 完整·横向（v0.6.0 的 contain 改名归此档，旧值 "contain" 兼容读作 contain_h）；
            // contain_v 完整·竖向：本屏恰为整幅全屏（tile=[0,0,1,1]）且视频与屏幕朝向相反时，整幅先顺时针旋转 90° 再按 contain 放下。
            // 旋转的等价处理：旋转后视频宽高比取倒数（vaF=1/va）走同一套 contain 数学，旋转本体在下方赋值段以 View.rotation 复合；
            // 朝向已一致（如竖片竖屏）时不旋转，contain_v 退化为 contain_h 数学。非全屏 tile 收到 contain_v 同样退化为 contain_h（主机侧已把关，此为从机防御）。
            val ecr0 = if (cr > 0) cr else vw.toDouble() / vh.toDouble()
            val rotV = layoutFit == "contain_v" && va > 0 &&
                tile.x == 0.0 && tile.y == 0.0 && tile.w == 1.0 && tile.h == 1.0 &&
                (va > 1.0) != (ecr0 > 1.0)
            val hasVideo = videoPxW > 0 && videoPxH > 0 && va > 0
            var ax = 1.0; var bx = 0.0; var ay = 1.0; var by = 0.0
            var s = -1.0 // 单一标量像素缩放；视频尺寸未知时保持 -1（日志 scaleX/scaleY 同为 -1，与旧口径一致）
            if ((layoutFit == "contain_h" || layoutFit == "contain" || layoutFit == "contain_v") && va > 0) {
                // 完整（留边）：整幅视频等比放下。画布在视频中居中占据子矩形 V（画布坐标），
                // 本屏负责画布的 tile 份；tile 与 V 交集之外的屏幕区域不画视频、露舞台底色（#0B0B10），不拉伸。
                // canvasRatio==0（全屏跟随）时画布即本屏自身，取本屏宽高比为有效画布比（v0.6.4：本屏比取稳定尺寸）。
                val vaF = if (rotV) 1.0 / va else va
                val ecr = ecr0
                val vvx: Double; val vvy: Double; val vvw: Double; val vvh: Double
                if (vaF > ecr) { vvw = 1.0; vvh = ecr / vaF; vvx = 0.0; vvy = (1 - vvh) / 2 }
                else { vvh = 1.0; vvw = vaF / ecr; vvy = 0.0; vvx = (1 - vvw) / 2 }
                // 目标矩形（本屏分数坐标）：画布 V 份落入本屏 tile 份的仿射 a/b（视频分数坐标口径，同 v0.6.0）
                val dx = (vvx - tile.x) / tile.w; val dw = vvw / tile.w
                val dy = (vvy - tile.y) / tile.h; val dh = vvh / tile.h
                val ix0 = maxOf(tile.x, vvx); val iy0 = maxOf(tile.y, vvy)
                val ix1 = minOf(tile.x + tile.w, vvx + vvw); val iy1 = minOf(tile.y + tile.h, vvy + vvh)
                rx = if (ix1 > ix0) (ix0 - vvx) / vvw else 0.0
                rw = if (ix1 > ix0) (ix1 - ix0) / vvw else 0.0
                ry = if (iy1 > iy0) (iy0 - vvy) / vvh else 0.0
                rh = if (iy1 > iy0) (iy1 - iy0) / vvh else 0.0
                if (hasVideo && !rotV) {
                    // v0.6.4：contain 的两轴商 qx/qy（与旧日志 scaleX/scaleY 同定义），s 取 min（整幅必须放得下）；
                    // 较小商所在轴沿用原仿射，另一轴由 s 反推、并把整幅视频在目标矩形内居中。
                    // 几何自洽（qx==qy）时反推结果与旧式逐项相等，行为不回归。
                    val qx = dw * vw / videoPxW
                    val qy = dh * vh / videoPxH
                    s = minOf(qx, qy)
                    if (qx <= qy) {
                        ax = dw; bx = dx
                        ay = s * videoPxH / vh
                        by = (dy + dh / 2) - ay * 0.5
                    } else {
                        ay = dh; by = dy
                        ax = s * videoPxW / vw
                        bx = (dx + dw / 2) - ax * 0.5
                    }
                } else {
                    // rotV 时 ax/ay 暂存 contain 原仿射，供赋值段求旋转两轴商；无视频尺寸时亦走此路（赋值与旧式一致）
                    ax = dw; bx = dx; ay = dh; by = dy
                }
            } else {
                // 铺满（裁切）：视频先按画布比例裁出可见子矩形（视频坐标），本屏显示 tile 对应份
                var vx = 0.0; var vy = 0.0; var vwd = 1.0; var vht = 1.0
                if (cr > 0 && va > 0) {
                    if (va > cr) { vwd = cr / va; vx = (1 - vwd) / 2 } else { vht = va / cr; vy = (1 - vht) / 2 }
                }
                rx = vx + tile.x * vwd
                ry = vy + tile.y * vht
                rw = tile.w * vwd
                rh = tile.h * vht
                if (hasVideo) {
                    // v0.6.4：cover 的两轴商 qx = vw/(rw*视频宽)、qy = vh/(rh*视频高)（与旧日志定义一致），
                    // s 取 max（子矩形必须盖满本屏），两轴仿射由 s 反推、平移把子矩形居中。
                    // 几何自洽（qx==qy）时与旧式（a=1/rw、b=-rx/rw）逐项相等，行为不回归。
                    val qx = vw / (rw * videoPxW)
                    val qy = vh / (rh * videoPxH)
                    s = maxOf(qx, qy)
                    ax = s * videoPxW / vw
                    bx = 0.5 - ax * (rx + rw / 2)
                    ay = s * videoPxH / vh
                    by = 0.5 - ay * (ry + rh / 2)
                } else {
                    ax = 1.0 / rw; bx = -rx / rw
                    ay = 1.0 / rh; by = -ry / rh
                }
            }
            // 赋值段。非旋转档：rotation 恒 0，scale/pivot 由上面的单一 s 仿射给出。
            // contain_v 旋转档（v0.6.1 结构不变）：rotation=90、pivot=画面中心，
            // View.scaleX = ay*vh/vw、View.scaleY = ax*vw/vh；v0.6.4 起 ax/ay 先收敛到单一 s：
            // 两轴商 q1 = ax*vw/videoPxH（视频 x 轴落屏幕 y 向）、q2 = ay*vh/videoPxW（视频 y 轴落屏幕 x 向），
            // contain 取 s = min(q1, q2)，反推 ax' = s*videoPxH/vw、ay' = s*videoPxW/vh 代入上式，
            // 两向像素缩放同为 s（推导见 v0.6.4 构建报告）。取向规则：恒顺时针 90°（视频顶边落到屏幕右侧）。
            val scaleX: Double
            val scaleY: Double
            if (rotV) {
                textureView.rotation = 90f
                textureView.pivotX = vw / 2f
                textureView.pivotY = vh / 2f
                if (hasVideo) {
                    val q1 = ax * vw / videoPxH
                    val q2 = ay * vh / videoPxW
                    s = minOf(q1, q2)
                    val axr = s * videoPxH / vw
                    val ayr = s * videoPxW / vh
                    textureView.scaleX = (ayr * vh / vw).toFloat()
                    textureView.scaleY = (axr * vw / vh).toFloat()
                    scaleX = s; scaleY = s
                } else {
                    textureView.scaleX = (ay * vh / vw).toFloat()
                    textureView.scaleY = (ax * vw / vh).toFloat()
                    scaleX = -1.0; scaleY = -1.0
                }
            } else {
                textureView.rotation = 0f
                textureView.scaleX = ax.toFloat()
                textureView.scaleY = ay.toFloat()
                textureView.pivotX = if (ax != 1.0) (bx * vw / (1 - ax)).toFloat() else 0f
                textureView.pivotY = if (ay != 1.0) (by * vh / (1 - ay)).toFloat() else 0f
                scaleX = s; scaleY = s
            }
            // 守卫保留（v0.3 起）：两值相对差 >0.1% 记 warn=aniso。v0.6.4 起 scaleX 与 scaleY
            // 同源于单一 s（或同为 -1），差恒为 0，本判定结构性不可触发——留着防未来改动回潮。
            var warn = ""
            if (scaleX > 0 && scaleY > 0 && abs(scaleX - scaleY) / maxOf(scaleX, scaleY) > 0.001) warn = " warn=aniso"
            klog("TRANSFORM no=$myNo video=${videoPxW.toInt()}x${videoPxH.toInt()} canvas_ratio=${fmt4(cr)} tile=[${fmt4(tile.x)},${fmt4(tile.y)},${fmt4(tile.w)},${fmt4(tile.h)}] view=${vw}x${vh} region=[${fmt4(rx)},${fmt4(ry)},${fmt4(rw)},${fmt4(rh)}] scaleX=${fmt4(scaleX)} scaleY=${fmt4(scaleY)}$warn${if (rotV) " rot=90" else ""}")
        }
    }

    // ---------- debug ----------
    private fun updateDebugLine() {
        if (!::debugTv.isInitialized) return
        val txt = "role=$role no=$myNo offset=${offsetMs}ms rtt=${rttMs}ms err=${lastErrMs}ms hard=$hardCorrections rate=$rateState srate=${fmtSpeed(sessionRate)} stalls=$stalls state=$hostTickState"
        debugTv.text = txt
    }

    // ---------- helpers ----------
    private fun msg(t: String): JSONObject = JSONObject().put("t", t).put("seq", System.nanoTime())

    private fun localIp(): String {
        try {
            val ifs = NetworkInterface.getNetworkInterfaces()
            while (ifs.hasMoreElements()) {
                val ni = ifs.nextElement()
                val addrs = ni.inetAddresses
                while (addrs.hasMoreElements()) {
                    val a = addrs.nextElement()
                    if (!a.isLoopbackAddress && a.hostAddress?.contains('.') == true) return a.hostAddress ?: "?"
                }
            }
        } catch (e: Exception) {}
        return "?"
    }

    // ---------- v0.5.0：局域网文件互传 ----------
    // 拓扑（规格已定）：星形连接下只做主机⇄从机双向——主机可向任一已连接从机发，从机只能向主机发；
    // 从机之间不互传、不中转。传输沿用「接收方拉取」：发送方在 18768 起本轮文件服务，接收方逐个 GET。
    // 同一时刻只跑一轮互传（发送与接收各自至多一轮并行），新一轮须先取消旧轮。

    private fun randStr(n: Int): String {
        val alpha = "abcdefghijklmnopqrstuvwxyz0123456789"
        val rnd = java.security.SecureRandom()
        return (1..n).map { alpha[rnd.nextInt(alpha.length)] }.joinToString("")
    }

    private fun fmtBytes(n: Long): String = when {
        n < 1024 -> "$n B"
        n < 1024L * 1024 -> String.format(Locale.US, "%.1f KB", n / 1024.0)
        n < 1024L * 1024 * 1024 -> String.format(Locale.US, "%.1f MB", n / (1024.0 * 1024))
        else -> String.format(Locale.US, "%.2f GB", n / (1024.0 * 1024 * 1024))
    }

    private fun sha256OfFile(f: File): String =
        java.io.FileInputStream(f).use { input ->
            val md = java.security.MessageDigest.getInstance("SHA-256")
            val buf = ByteArray(64 * 1024)
            while (true) { val n = input.read(buf); if (n < 0) break; md.update(buf, 0, n) }
            md.digest().joinToString("") { String.format(Locale.US, "%02x", it.toInt() and 0xFF) }
        }

    /** 互传消息统一出口：从机一律经 wsClient 发往主机；主机按对端编号定向发（不广播）。 */
    private fun xferReply(peerNo: Int, json: JSONObject) {
        if (role == "client") wsClient?.send(json.toString())
        else clientConns[peerNo]?.send(json.toString())
    }

    /** 文件互传区（主机页与从机页共用，沿用 v0.4.0 样式常量）；接收横幅单独挂覆盖层顶部。 */
    private fun buildXferSection(parent: LinearLayout) {
        loadXferDest()
        parent.addView(TextView(this).apply {
            text = "文件互传（局域网 · 一次性）"; textSize = 16f; setTextColor(colText); setTypeface(null, Typeface.BOLD)
            layoutParams = stackLp(24)
        })
        xferTargetRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            gravity = Gravity.CENTER_VERTICAL
            layoutParams = stackLp(10)
        }
        parent.addView(xferTargetRow!!)
        val btnRow = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            layoutParams = stackLp(10)
        }
        btnRow.addView(Button(this).apply {
            text = "选择文件"
            styleGhostButton(this)
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f).apply { rightMargin = dp(4) }
            setOnClickListener {
                if (xferSendTid != null) { setStatus("当前有一轮互传未结束，先取消再选新文件"); return@setOnClickListener }
                val intent = Intent(Intent.ACTION_OPEN_DOCUMENT).apply {
                    addCategory(Intent.CATEGORY_OPENABLE); type = "*/*"
                    putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true)
                }
                startActivityForResult(intent, REQ_PICK_XFER)
            }
        })
        btnRow.addView(Button(this).apply {
            text = "发送"
            stylePrimaryButton(this)
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f).apply { leftMargin = dp(4); rightMargin = dp(4) }
            setOnClickListener { onXferSendClicked() }
        })
        btnRow.addView(Button(this).apply {
            text = "取消互传"
            styleGhostButton(this)
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f).apply { leftMargin = dp(4) }
            setOnClickListener { onXferCancelClicked() }
        })
        parent.addView(btnRow)
        xferSendBox = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        parent.addView(xferSendBox!!)
        xferRecvTotalTv = TextView(this).apply {
            text = ""; textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(10)
        }
        parent.addView(xferRecvTotalTv!!)
        xferRecvBox = LinearLayout(this).apply { orientation = LinearLayout.VERTICAL }
        parent.addView(xferRecvBox!!)
        xferDestTv = TextView(this).apply {
            textSize = 13f; setTextColor(colSub)
            layoutParams = stackLp(10)
        }
        parent.addView(xferDestTv!!)
        parent.addView(Button(this).apply {
            text = "选择接收文件夹"
            styleGhostButton(this)
            layoutParams = stackLp(8)
            setOnClickListener { launchXferTreePicker() }
        })
        // 接收横幅：v0.6.1 改挂舞台根容器最顶层（玻璃面板），默认隐藏，收到 XFER_OFFER 时亮起——与覆盖层开关无关，播放中也照常弹
        (xferBannerBox?.parent as? android.view.ViewGroup)?.removeView(xferBannerBox)
        val banner = LinearLayout(this).apply {
            orientation = LinearLayout.VERTICAL
            background = roundedDrawable(colGlass, 20)
            setPadding(dp(16), dp(12), dp(16), dp(12))
            layoutParams = FrameLayout.LayoutParams(FrameLayout.LayoutParams.MATCH_PARENT, FrameLayout.LayoutParams.WRAP_CONTENT, Gravity.TOP)
                .apply { topMargin = dp(12); leftMargin = dp(12); rightMargin = dp(12) }
            visibility = View.GONE
        }
        xferBannerTv = TextView(this).apply { textSize = 15f; setTextColor(colText) }
        banner.addView(xferBannerTv!!)
        val bannerBtns = LinearLayout(this).apply {
            orientation = LinearLayout.HORIZONTAL
            layoutParams = stackLp(10)
        }
        bannerBtns.addView(Button(this).apply {
            text = "接受"
            stylePrimaryButton(this)
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f).apply { rightMargin = dp(4) }
            setOnClickListener { onXferAcceptClicked() }
        })
        bannerBtns.addView(Button(this).apply {
            text = "拒绝"
            styleGhostButton(this)
            layoutParams = LinearLayout.LayoutParams(0, LinearLayout.LayoutParams.WRAP_CONTENT, 1f).apply { leftMargin = dp(4) }
            setOnClickListener { onXferRejectClicked() }
        })
        banner.addView(bannerBtns)
        xferBannerBox = banner
        stage.addView(banner) // v0.6.1：舞台根容器最后添加的子 View（z 序最高，压覆盖层与各浮条）
        refreshXferTargets()
        refreshXferDestLabel()
    }

    private fun hideXferBanner() {
        runOnUiThread { xferBannerBox?.visibility = View.GONE }
    }

    /** 互传目标行：主机列已连接从机编号胶囊（点选切换，样式同布局模式胶囊），从机固定显示主机。由设备表刷新顺带驱动。 */
    private fun refreshXferTargets() {
        val row = xferTargetRow ?: return
        runOnUiThread {
            if (xferTargetRow !== row) return@runOnUiThread
            row.removeAllViews()
            if (role == "client") {
                xferTargetNo = 0
                row.addView(TextView(this).apply { text = "发送目标：主机（编号 0）"; textSize = 14f; setTextColor(colText) })
            } else if (role == "host") {
                row.addView(TextView(this).apply { text = "发送目标："; textSize = 14f; setTextColor(colSub) })
                val nos = clientConns.keys.sorted()
                if (nos.isEmpty()) {
                    row.addView(TextView(this).apply {
                        text = "暂无从机连接"; textSize = 14f; setTextColor(colSub)
                        layoutParams = LinearLayout.LayoutParams(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT).apply { leftMargin = dp(8) }
                    })
                    xferTargetNo = -1
                } else {
                    if (xferTargetNo !in nos) xferTargetNo = nos.first()
                    nos.forEach { no ->
                        val b = Button(this).apply {
                            text = "$no 号"
                            styleModePill(this, no == xferTargetNo)
                            layoutParams = LinearLayout.LayoutParams(LinearLayout.LayoutParams.WRAP_CONTENT, LinearLayout.LayoutParams.WRAP_CONTENT)
                                .apply { leftMargin = dp(6) }
                            setOnClickListener { xferTargetNo = no; refreshXferTargets() }
                        }
                        row.addView(b)
                    }
                }
            }
        }
    }

    // ----- 发送方 -----
    /** 选片回来（主线程）：逐个建行，后台线程逐个算 size 与 SHA-256（经 ContentResolver 读流一遍过）。 */
    private fun onXferFilesPicked(uris: List<Uri>) {
        if (xferSendTid != null) { setStatus("当前有一轮互传未结束，先取消再选新文件"); return }
        val gen = ++xferSendGen
        xferSendItems.clear()
        xferSendRows.clear()
        xferSendBox?.removeAllViews()
        uris.forEach { uri ->
            try { contentResolver.takePersistableUriPermission(uri, Intent.FLAG_GRANT_READ_URI_PERMISSION) } catch (e: Exception) {}
            val item = XferItem(displayNameOf(uri).ifEmpty { "file" }, -1, "", uri)
            xferSendItems.add(item)
            val tv = TextView(this).apply {
                text = "${item.name} · 计算校验中…"; textSize = 13f; setTextColor(colText)
                setPadding(0, dp(2), 0, dp(2))
            }
            xferSendBox?.addView(tv)
            xferSendRows.add(tv)
        }
        setStatus("已选 ${uris.size} 个文件，计算校验中…")
        Thread {
            val itemsSnapshot = ArrayList(xferSendItems)
            itemsSnapshot.forEachIndexed { idx, item ->
                if (gen != xferSendGen) return@Thread
                val uri = item.uri ?: return@forEachIndexed
                try {
                    var size = 0L
                    val md = java.security.MessageDigest.getInstance("SHA-256")
                    val ok = contentResolver.openInputStream(uri)?.use { input ->
                        val buf = ByteArray(64 * 1024)
                        while (true) {
                            val n = input.read(buf)
                            if (n < 0) break
                            md.update(buf, 0, n)
                            size += n
                        }
                        true
                    } ?: false
                    if (ok) {
                        item.size = size
                        item.sha256 = md.digest().joinToString("") { String.format(Locale.US, "%02x", it.toInt() and 0xFF) }
                        updateSendRow(idx, "待发送")
                    } else {
                        updateSendRow(idx, "读取失败")
                    }
                } catch (e: Exception) {
                    klog("XFER hash fail name=${item.name} reason=${e.message}")
                    updateSendRow(idx, "读取失败")
                }
            }
            if (gen == xferSendGen) setStatus("文件已就绪，点「发送」")
        }.start()
    }

    private fun updateSendRow(idx: Int, status: String) {
        if (idx < 0 || idx >= xferSendItems.size) return
        val item = xferSendItems[idx]
        runOnUiThread {
            if (idx < xferSendRows.size) {
                val sizeTxt = if (item.size >= 0) fmtBytes(item.size) else "?"
                xferSendRows[idx].text = "${item.name} · $sizeTxt · $status"
            }
        }
    }

    private fun onXferSendClicked() {
        when (role) {
            "client" -> if (wsClient?.isOpen != true) { setStatus("请先连接主机再发送文件"); return }
            "host" -> if (xferTargetNo < 0 || !clientConns.containsKey(xferTargetNo)) { setStatus("暂无可发送的从机（先等从机连接）"); return }
            else -> { setStatus("请先选择角色"); return }
        }
        if (xferSendTid != null) { setStatus("当前有一轮互传未结束，请先取消"); return }
        if (xferSendItems.isEmpty()) { setStatus("请先选择文件"); return }
        if (xferSendItems.any { it.sha256.isEmpty() || it.size < 0 }) { setStatus("文件校验还在计算中（或读取失败），稍候再发送"); return }
        val tid = randStr(12)
        xferSendTid = tid
        xferSendToken = randStr(16)
        xferSendTargetNo = if (role == "client") 0 else xferTargetNo
        val arr = org.json.JSONArray()
        xferSendItems.forEach { arr.put(JSONObject().put("name", it.name).put("size", it.size).put("sha256", it.sha256)) }
        val offer = msg("XFER_OFFER").put("tid", tid).put("from_no", myNo).put("token", xferSendToken).put("files", arr)
        xferReply(xferSendTargetNo, offer)
        startXferServer() // v0.6.0 改法 A：发出 OFFER 的同时即启动本轮文件服务——接收方点接受后立即拉取，不再撞「服务未起」的时序竞态（真机实锤：接收方比服务早约 150ms 发起连接被拒、整轮判死）
        for (i in xferSendItems.indices) updateSendRow(i, "待确认")
        val total = xferSendItems.sumOf { it.size }
        klog("XFER offer sent tid=$tid to_no=$xferSendTargetNo files=${xferSendItems.size} total=$total")
        setStatus("已发送 ${xferSendItems.size} 个文件（${fmtBytes(total)}），等对方确认")
    }

    private fun onXferAccept(tid: String, fromNo: Int) {
        if (tid != xferSendTid || fromNo != xferSendTargetNo) return
        klog("XFER offer accepted tid=$tid")
        if (xferServer?.isRunning() != true) startXferServer() // v0.6.0：服务已随 OFFER 启动（改法 A），此处仅在未运行时兜底补启
        for (i in xferSendItems.indices) updateSendRow(i, "发送中（对方拉取中）")
        setStatus("对方已接受，文件服务已启动，等对方拉取")
    }

    private fun onXferReject(tid: String, fromNo: Int) {
        if (tid != xferSendTid || fromNo != xferSendTargetNo) return
        klog("XFER offer rejected tid=$tid")
        stopXferServer("reject") // v0.6.0：服务已随 OFFER 启动（改法 A），被拒须显式关停（v0.5.0 时服务未启、此步为空操作）
        for (i in xferSendItems.indices) updateSendRow(i, "被拒绝")
        xferSendTid = null
        setStatus("对方拒绝了本次发送")
    }

    private fun onXferFileDone(tid: String, idx: Int, ok: Boolean, fromNo: Int) {
        if (tid != xferSendTid || fromNo != xferSendTargetNo) return
        klog("XFER file ack tid=$tid idx=$idx ok=$ok")
        updateSendRow(idx, if (ok) "已完成" else "失败")
    }

    private fun onXferDone(tid: String, fromNo: Int) {
        if (tid != xferSendTid || fromNo != xferSendTargetNo) return
        stopXferServer("done")
        klog("XFER done received tid=$tid")
        xferSendTid = null
        setStatus("互传完成")
    }

    private fun onXferCancel(tid: String) {
        if (tid == xferSendTid) {
            stopXferServer("cancel")
            xferSendTid = null
            for (i in xferSendItems.indices) updateSendRow(i, "已取消")
            klog("XFER cancel received tid=$tid side=sender")
            setStatus("对方取消了本次互传")
        }
        if (tid == xferRecvTid) {
            xferRecvGen++
            xferRecvTid = null
            hideXferBanner()
            for (i in xferRecvItems.indices) updateRecvRow(i, "已取消")
            klog("XFER cancel received tid=$tid side=receiver")
            setStatus("对方取消了本次互传")
        }
    }

    private fun onXferCancelClicked() {
        val sTid = xferSendTid
        if (sTid != null) {
            xferReply(xferSendTargetNo, msg("XFER_CANCEL").put("tid", sTid))
            stopXferServer("cancel")
            xferSendTid = null
            for (i in xferSendItems.indices) updateSendRow(i, "已取消")
            klog("XFER cancel sent tid=$sTid side=sender")
            setStatus("已取消本次互传")
            return
        }
        val rTid = xferRecvTid
        if (rTid != null) {
            xferRecvGen++
            xferReply(xferRecvFromNo, msg("XFER_CANCEL").put("tid", rTid))
            xferRecvTid = null
            hideXferBanner()
            for (i in xferRecvItems.indices) updateRecvRow(i, "已取消")
            klog("XFER cancel sent tid=$rTid side=receiver")
            setStatus("已取消本次互传")
            return
        }
        setStatus("当前没有进行中的互传")
    }

    /** 发送方文件服务生命周期：v0.6.0 起随 OFFER 发出即启动（改法 A，修时序竞态）；DONE／CANCEL／拒绝／对端断开／10 分钟超时关停。 */
    private fun startXferServer() {
        val tid = xferSendTid ?: return
        stopXferServer("restart")
        val srv = XferFileServer(localIp(), tid, xferSendToken, ArrayList(xferSendItems))
        srv.start()
        xferServer = srv
        xferServerJob?.cancel()
        xferServerJob = scope.launch {
            delay(600000)
            if (xferSendTid == tid && xferServer?.isRunning() == true) {
                stopXferServer("timeout")
                xferSendTid = null
                for (i in xferSendItems.indices) updateSendRow(i, "已超时")
                klog("XFER round timeout tid=$tid")
                setStatus("互传超时（10 分钟），文件服务已关停")
            }
        }
    }

    private fun stopXferServer(reason: String) {
        xferServerJob?.cancel()
        xferServerJob = null
        xferServer?.stop(reason)
        xferServer = null
    }

    /**
     * 发送方本轮文件 HTTP 服务（手写 ServerSocket，沿用媒体分发服务的写法与纪律；无新增依赖）。
     * 绑本机局域网 IP 的 18768 端口（与媒体分发 18767 区分），路径须为 /xfer/<tid>/<idx> 且带 ?token=<本轮令牌>，不符一律 404。
     * 支持 Range 三形式（start-end／只有起点／只有尾部）回 206 + Content-Range，无 Range 回 200 + Content-Length；
     * 取不到文件描述符时降级整流（Range 也回 200 全量，接收方据此整文件重写）。每连接一线程，64KB 缓冲流式转发。
     */
    private inner class XferFileServer(
        private val bindIp: String,
        private val tid: String,
        private val token: String,
        private val items: List<XferItem>
    ) {
        @Volatile private var running = false
        private var serverSocket: java.net.ServerSocket? = null

        fun isRunning(): Boolean = running

        fun start() {
            try {
                val ss = java.net.ServerSocket()
                ss.reuseAddress = true
                ss.bind(java.net.InetSocketAddress(bindIp, 18768))
                serverSocket = ss
                running = true
                klog("XFER server started port=18768 tid=$tid files=${items.size} bind=$bindIp")
                Thread {
                    while (running) {
                        try {
                            val conn = ss.accept()
                            Thread { serve(conn) }.apply { isDaemon = true }.start()
                        } catch (e: Exception) {
                            if (running) klog("XFER server accept err: ${e.message}")
                        }
                    }
                }.apply { isDaemon = true }.start()
            } catch (e: Exception) {
                klog("XFER server start fail: ${e.message}")
            }
        }

        fun stop(reason: String) {
            if (!running && serverSocket == null) return
            running = false
            try { serverSocket?.close() } catch (e: Exception) {}
            serverSocket = null
            klog("XFER server stopped tid=$tid reason=$reason")
        }

        private fun serve(conn: java.net.Socket) {
            try { handle(conn) } catch (e: Exception) {
                klog("XFER server conn err: ${e.message}")
            } finally {
                try { conn.close() } catch (e: Exception) {}
            }
        }

        private fun handle(conn: java.net.Socket) {
            val reader = java.io.BufferedReader(java.io.InputStreamReader(conn.getInputStream(), Charsets.US_ASCII))
            val requestLine = reader.readLine() ?: return
            val parts = requestLine.split(" ")
            var rangeHeader: String? = null
            while (true) {
                val line = reader.readLine() ?: break
                if (line.isEmpty()) break
                val ci = line.indexOf(':')
                if (ci > 0 && line.substring(0, ci).trim().equals("Range", ignoreCase = true)) {
                    rangeHeader = line.substring(ci + 1).trim()
                }
            }
            val out = conn.getOutputStream()
            val target = if (parts.size >= 2) parts[1] else ""
            val path = target.substringBefore('?')
            val query = target.substringAfter('?', "")
            val qToken = query.split('&').firstOrNull { it.startsWith("token=") }?.substringAfter('=')
            val segs = path.split('/')
            val idx = segs.getOrNull(3)?.toIntOrNull()
            val item = if (idx != null && idx in items.indices) items[idx] else null
            if (parts.isEmpty() || parts[0] != "GET" || segs.getOrNull(1) != "xfer" || segs.getOrNull(2) != tid ||
                item == null || qToken != token || item.uri == null) {
                writeHead(out, 404, "Not Found", 0, null)
                return
            }
            val fileUri = item.uri
            val fileSize = item.size
            var start = 0L
            var end = if (fileSize > 0) fileSize - 1 else -1L
            var partial = false
            val degraded = !canOpenFd(fileUri)
            if (rangeHeader != null && !degraded && fileSize > 0) {
                val spec = rangeHeader.removePrefix("bytes=").trim()
                val dash = spec.indexOf('-')
                if (dash >= 0) {
                    val a = spec.substring(0, dash).trim()
                    val b = spec.substring(dash + 1).trim()
                    try {
                        if (a.isEmpty() && b.isNotEmpty()) {
                            val suffix = b.toLong()
                            start = maxOf(0L, fileSize - suffix)
                            end = fileSize - 1
                        } else if (a.isNotEmpty()) {
                            start = a.toLong()
                            end = if (b.isEmpty()) fileSize - 1 else minOf(b.toLong(), fileSize - 1)
                        }
                        partial = start in 0..end
                    } catch (e: Exception) { partial = false }
                }
            }
            if (partial) {
                writeHead(out, 206, "Partial Content", end - start + 1, "bytes $start-$end/$fileSize")
                streamRange(out, fileUri, start, end - start + 1)
            } else {
                writeHead(out, 200, "OK", fileSize, null)
                streamWhole(out, fileUri, degraded)
            }
        }

        private fun writeHead(out: java.io.OutputStream, code: Int, text: String, length: Long, contentRange: String?) {
            val sb = StringBuilder()
            sb.append("HTTP/1.1 $code $text\r\n")
            sb.append("Content-Type: application/octet-stream\r\n")
            if (length >= 0) sb.append("Content-Length: $length\r\n")
            sb.append("Accept-Ranges: bytes\r\n")
            if (contentRange != null) sb.append("Content-Range: $contentRange\r\n")
            sb.append("Connection: close\r\n\r\n")
            out.write(sb.toString().toByteArray(Charsets.US_ASCII))
            out.flush()
        }

        private fun streamWhole(out: java.io.OutputStream, fileUri: Uri, degraded: Boolean) {
            if (!degraded) {
                val pfd = contentResolver.openFileDescriptor(fileUri, "r")
                if (pfd != null) {
                    try { java.io.FileInputStream(pfd.fileDescriptor).use { copyN(it, out, Long.MAX_VALUE) } }
                    finally { try { pfd.close() } catch (e: Exception) {} }
                    return
                }
            }
            contentResolver.openInputStream(fileUri)?.use { copyN(it, out, Long.MAX_VALUE) }
        }

        private fun streamRange(out: java.io.OutputStream, fileUri: Uri, start: Long, len: Long) {
            val pfd = contentResolver.openFileDescriptor(fileUri, "r")
            if (pfd == null) { streamWhole(out, fileUri, true); return }
            try {
                val fis = java.io.FileInputStream(pfd.fileDescriptor)
                fis.channel.position(start)
                fis.use { copyN(it, out, len) }
            } finally { try { pfd.close() } catch (e: Exception) {} }
        }

        private fun copyN(input: java.io.InputStream, out: java.io.OutputStream, maxBytes: Long) {
            val buf = ByteArray(64 * 1024)
            var remain = maxBytes
            while (remain > 0) {
                val want = minOf(buf.size.toLong(), remain).toInt()
                val n = input.read(buf, 0, want)
                if (n < 0) break
                out.write(buf, 0, n)
                remain -= n
            }
            out.flush()
        }
    }

    // ----- 接收方 -----
    /** 收到发送提议：本机正忙（有未决横幅或正在接收）时自动回绝新提议；否则记下对端与清单、亮横幅等用户裁决（不自动处理）。 */
    private fun onXferOffer(fromNo: Int, fromIp: String, o: JSONObject) {
        val tid = o.optString("tid", "")
        if (tid.isEmpty()) return
        if (xferRecvTid != null) {
            xferReply(fromNo, msg("XFER_REJECT").put("tid", tid))
            klog("XFER offer auto-rejected busy tid=$tid from_no=$fromNo")
            return
        }
        val arr = o.optJSONArray("files") ?: return
        val items = mutableListOf<XferItem>()
        for (i in 0 until arr.length()) {
            val f = arr.getJSONObject(i)
            items.add(XferItem(f.optString("name", "file"), f.optLong("size", -1), f.optString("sha256", ""), null))
        }
        if (items.isEmpty()) return
        xferRecvTid = tid
        xferRecvFromNo = fromNo
        xferRecvFromIp = fromIp
        xferRecvToken = o.optString("token", "")
        xferRecvItems = items
        xferRecvTotalBytes = items.sumOf { maxOf(0L, it.size) }
        xferRecvDoneBytes = 0
        val total = xferRecvTotalBytes
        klog("XFER offer received tid=$tid from_no=$fromNo files=${items.size} total=$total")
        runOnUiThread {
            xferRecvBox?.removeAllViews()
            xferRecvRows.clear()
            items.forEach { item ->
                val tv = TextView(this).apply {
                    text = "${item.name} · ${fmtBytes(maxOf(0L, item.size))} · 待接收"; textSize = 13f; setTextColor(colText)
                    setPadding(0, dp(2), 0, dp(2))
                }
                xferRecvBox?.addView(tv)
                xferRecvRows.add(tv)
            }
            xferRecvTotalTv?.text = "总进度：${fmtBytes(0)} / ${fmtBytes(total)}（0%）"
            xferBannerTv?.text = "收到 $fromNo 号发来的 ${items.size} 个文件（共 ${fmtBytes(total)}）"
            xferBannerBox?.visibility = View.VISIBLE
            xferBannerBox?.bringToFront() // v0.6.1：确保横幅压在舞台最顶层（其后新建的浮层也不得遮挡）
        }
        // v0.6.1：横幅已挂舞台顶层，不再连带弹整页覆盖层（旧行为正是播放中收不到确认的病根之一）
        klog("XFER banner show stage=${if (playingMode) "playing" else "idle"} overlay=${if (::overlay.isInitialized && overlay.visibility == View.VISIBLE) "open" else "closed"}")
        setStatus("收到 $fromNo 号的文件发送请求，请确认接受或拒绝")
    }

    private fun onXferAcceptClicked() {
        if (xferRecvTid == null) return
        // 首次接收且从未问过落盘目录：先引导 SAF 选一次（选或跳过回来后都补走接受流程）
        if (xferDirUri == null && !xferDirAsked) {
            xferPendingAccept = true
            setStatus("先选一次接收文件夹（也可跳过，文件存本机应用目录）")
            launchXferTreePicker()
            return
        }
        doXferAccept()
    }

    private fun doXferAccept() {
        val tid = xferRecvTid ?: return
        hideXferBanner()
        xferReply(xferRecvFromNo, msg("XFER_ACCEPT").put("tid", tid))
        klog("XFER accept sent tid=$tid")
        setStatus("已接受，开始接收…")
        startXferReceiveLoop()
    }

    private fun onXferRejectClicked() {
        val tid = xferRecvTid ?: return
        xferReply(xferRecvFromNo, msg("XFER_REJECT").put("tid", tid))
        klog("XFER reject sent tid=$tid")
        hideXferBanner()
        xferRecvTid = null
        setStatus("已拒绝本次文件发送")
    }

    private fun updateRecvRow(idx: Int, status: String) {
        if (idx < 0 || idx >= xferRecvItems.size) return
        val item = xferRecvItems[idx]
        runOnUiThread {
            if (idx < xferRecvRows.size) {
                xferRecvRows[idx].text = "${item.name} · ${fmtBytes(maxOf(0L, item.size))} · $status"
            }
        }
    }

    private fun refreshXferTotal(currentFileGot: Long) {
        val total = xferRecvTotalBytes
        val done = xferRecvDoneBytes + currentFileGot
        val pct = if (total > 0) (done * 100 / total).toInt() else 0
        runOnUiThread { xferRecvTotalTv?.text = "总进度：${fmtBytes(done)} / ${fmtBytes(total)}（$pct%）" }
    }

    /** 接收主循环（后台线程）：文件串行拉取，一件完再下一件；每件回 XFER_FILE_DONE，全完回 XFER_DONE。 */
    private fun startXferReceiveLoop() {
        val tid = xferRecvTid ?: return
        val items = xferRecvItems
        val fromNo = xferRecvFromNo
        val peerIp = xferRecvFromIp
        val token = xferRecvToken
        val gen = ++xferRecvGen
        Thread {
            var okCount = 0
            for ((idx, item) in items.withIndex()) {
                if (gen != xferRecvGen) { klog("XFER receive aborted tid=$tid at idx=$idx"); break }
                val ok = pullXferFile(tid, idx, item, peerIp, token, gen)
                if (gen != xferRecvGen) break
                if (ok) okCount++
                xferRecvDoneBytes += maxOf(0L, item.size)
                refreshXferTotal(0)
                xferReply(fromNo, msg("XFER_FILE_DONE").put("tid", tid).put("idx", idx).put("ok", ok))
            }
            if (gen == xferRecvGen) {
                xferReply(fromNo, msg("XFER_DONE").put("tid", tid))
                klog("XFER done sent tid=$tid ok=$okCount/${items.size}")
                setStatus("接收完成：$okCount/${items.size} 个成功")
                if (xferRecvTid == tid) xferRecvTid = null
            }
        }.start()
    }

    /**
     * 单文件接收：先落 .part（按 sha 前 16 位命名，跨轮认领续传），字节齐后验 SHA-256，
     * 通过才搬入目标文件夹改正式名；验不过删 .part 整文件重拉一次，再不过标失败。纪律：校验不过绝不落正式名。
     */
    private fun pullXferFile(tid: String, idx: Int, item: XferItem, peerIp: String, token: String, gen: Int): Boolean {
        val t0 = System.currentTimeMillis()
        val part = File(xferWorkDir(), item.sha256.take(16) + ".part")
        var retried = false
        while (true) {
            try {
                downloadXferToPart(tid, idx, item, part, peerIp, token, gen)
            } catch (e: Exception) {
                if (gen != xferRecvGen) return false
                klog("XFER file fail tid=$tid idx=$idx reason=${e.javaClass.simpleName}: ${e.message}")
                updateRecvRow(idx, "中断待续（已收 ${fmtBytes(part.length())}）")
                refreshXferTotal(part.length().coerceAtMost(maxOf(0L, item.size)))
                return false
            }
            if (gen != xferRecvGen) return false
            if (part.length() != item.size) {
                klog("XFER file incomplete tid=$tid idx=$idx got=${part.length()} size=${item.size}")
                updateRecvRow(idx, "中断待续（已收 ${fmtBytes(part.length())}）")
                refreshXferTotal(part.length().coerceAtMost(maxOf(0L, item.size)))
                return false
            }
            val shaOk = try { sha256OfFile(part) } catch (e: Exception) { "" }.equals(item.sha256, ignoreCase = true)
            if (shaOk) {
                val savedAs = saveXferFinal(part, item.name)
                if (savedAs == null) {
                    klog("XFER file fail tid=$tid idx=$idx reason=save_failed")
                    updateRecvRow(idx, "落盘失败")
                    return false
                }
                part.delete()
                val took = System.currentTimeMillis() - t0
                klog("XFER file done tid=$tid idx=$idx ok=true sha_ok=true took_ms=$took saved_as=$savedAs")
                updateRecvRow(idx, "已完成（存为 $savedAs）")
                return true
            }
            part.delete()
            if (!retried) {
                retried = true
                klog("XFER file sha mismatch tid=$tid idx=$idx retry=1")
                updateRecvRow(idx, "校验不过，整文件重拉…")
                continue
            }
            klog("XFER file done tid=$tid idx=$idx ok=false sha_ok=false took_ms=${System.currentTimeMillis() - t0}")
            updateRecvRow(idx, "失败（校验不过）")
            return false
        }
    }

    /**
     * 把一个文件拉进 .part：已有 .part 且长度小于目标时以 Range 续拉（追加写）；
     * 长度已满直接返回待校验；服务端回 200 而非 206 时视为未理会 Range，整文件重写；
     * 网络错误/读超时抛异常，由调用方保留 .part 标中断待续。
     */
    private fun downloadXferToPart(tid: String, idx: Int, item: XferItem, part: File, peerIp: String, token: String, gen: Int) {
        var resumeFrom = if (part.exists()) part.length() else 0L
        if (resumeFrom > item.size) { part.delete(); resumeFrom = 0 }
        if (item.size == 0L) {
            if (!part.exists()) FileOutputStream(part).close()
            return
        }
        if (resumeFrom == item.size) return // 已下满，待校验
        klog("XFER file start tid=$tid idx=$idx name=${item.name} size=${item.size} resume_from=$resumeFrom")
        updateRecvRow(idx, "接收中…")
        val url = URL("http://$peerIp:18768/xfer/$tid/$idx?token=$token")
        // v0.6.0 改法 B：仅「连接建立」阶段（拿到响应码之前）遇连接类异常才退避重试——300ms 起翻倍、
        // 单次上限 1200ms、至多 5 次尝试，总窗口约 3 秒；其间状态行与清单行显示「等待对方服务…」。
        // 服务端已随 OFFER 提前启动（改法 A），此为吸收极端时序与网络抖动的兜底；重试用尽才抛给上层判该文件失败。
        // 已开始读流后的中断不在此处重试（保留 .part、标中断待续的既有语义不变）。
        var conn: HttpURLConnection? = null
        var code = -1
        var attempt = 0
        while (true) {
            attempt++
            try {
                val c = url.openConnection() as HttpURLConnection
                c.connectTimeout = 10000
                c.readTimeout = 10000
                if (resumeFrom > 0) c.setRequestProperty("Range", "bytes=$resumeFrom-")
                code = c.responseCode
                conn = c
                break
            } catch (e: java.io.IOException) {
                val connectClass = e is java.net.ConnectException || e is java.net.SocketTimeoutException || e is java.net.NoRouteToHostException
                if (!connectClass || attempt >= 5) throw e
                klog("XFER connect retry tid=$tid idx=$idx attempt=$attempt")
                updateRecvRow(idx, "等待对方服务…")
                setStatus("等待对方服务…")
                Thread.sleep(minOf(300L shl (attempt - 1), 1200L))
                if (gen != xferRecvGen) throw java.io.IOException("cancelled")
            }
        }
        val connection = conn!!
        var base = resumeFrom
        var append = true
        when (code) {
            206 -> {}
            200 -> if (resumeFrom > 0) { base = 0; append = false }
            else -> { connection.disconnect(); throw java.io.IOException("http $code") }
        }
        FileOutputStream(part, append).use { out ->
            connection.inputStream.use { input ->
                val buf = ByteArray(64 * 1024)
                var got = base
                var lastPct = -1
                while (true) {
                    if (gen != xferRecvGen) throw java.io.IOException("cancelled")
                    val n = input.read(buf)
                    if (n < 0) break
                    out.write(buf, 0, n)
                    got += n
                    val pct = if (item.size > 0) (got * 100 / item.size).toInt() else 100
                    if (pct != lastPct) {
                        lastPct = pct
                        updateRecvRow(idx, "接收中 $pct%")
                        refreshXferTotal(got)
                    }
                }
            }
        }
        connection.disconnect()
    }

    // ----- 接收落盘（SAF 授权目录优先，未授权兜底 App 外部目录 xfer） -----
    private fun xferWorkDir(): File {
        val base = getExternalFilesDir(null) ?: cacheDir
        return File(base, "xfer").apply { mkdirs() }
    }

    private fun sanitizeFileName(name: String): String {
        var s = name.replace('/', '_').replace('\\', '_').trim()
        if (s.isEmpty() || s == "." || s == "..") s = "file"
        return s
    }

    private fun dedupName(name: String, existing: Set<String>): String {
        if (!existing.contains(name)) return name
        val dot = name.lastIndexOf('.')
        val base = if (dot > 0) name.substring(0, dot) else name
        val ext = if (dot > 0) name.substring(dot) else ""
        var i = 1
        while (true) {
            val cand = "$base ($i)$ext"
            if (!existing.contains(cand)) return cand
            i++
        }
    }

    /** 成品落盘：先试 SAF 授权目录，失败（授权失效等）回退 App 外部目录 xfer。返回最终文件名，彻底失败回 null。 */
    private fun saveXferFinal(part: File, rawName: String): String? {
        val clean = sanitizeFileName(rawName)
        if (xferDirUri != null) {
            val saved = saveXferToSaf(part, clean)
            if (saved != null) return saved
            klog("XFER dest fallback app dir name=$clean")
        }
        return saveXferToAppDir(part, clean)
    }

    private fun saveXferToAppDir(part: File, clean: String): String? {
        return try {
            val dir = xferWorkDir()
            val existing = dir.list()?.toSet() ?: emptySet()
            val finalName = dedupName(clean, existing)
            part.copyTo(File(dir, finalName), overwrite = false)
            finalName
        } catch (e: Exception) {
            klog("XFER appdir save fail: ${e.message}")
            null
        }
    }

    private fun saveXferToSaf(part: File, clean: String): String? {
        val tree = xferDirUri ?: return null
        return try {
            val parentId = DocumentsContract.getTreeDocumentId(tree)
            val childrenUri = DocumentsContract.buildChildDocumentsUriUsingTree(tree, parentId)
            val existing = HashSet<String>()
            contentResolver.query(childrenUri, arrayOf(DocumentsContract.Document.COLUMN_DISPLAY_NAME), null, null, null)?.use { c ->
                val ci = c.getColumnIndex(DocumentsContract.Document.COLUMN_DISPLAY_NAME)
                while (c.moveToNext()) { if (ci >= 0) c.getString(ci)?.let { existing.add(it) } }
            }
            val finalName = dedupName(clean, existing)
            val parentUri = DocumentsContract.buildDocumentUriUsingTree(tree, parentId)
            val mime = java.net.URLConnection.guessContentTypeFromName(finalName) ?: "application/octet-stream"
            val doc = DocumentsContract.createDocument(contentResolver, parentUri, mime, finalName) ?: return null
            val out = contentResolver.openOutputStream(doc) ?: return null
            out.use { o -> java.io.FileInputStream(part).use { it.copyTo(o) } }
            finalName
        } catch (e: Exception) {
            klog("XFER saf save fail: ${e.message}")
            null
        }
    }

    private fun loadXferDest() {
        val prefs = getSharedPreferences("duoping", Context.MODE_PRIVATE)
        xferDirAsked = prefs.getBoolean("xfer_dir_asked", false)
        xferDirUri = null
        val s = prefs.getString("xfer_dir_uri", null)
        if (s != null) {
            val u = Uri.parse(s)
            val ok = try {
                contentResolver.persistedUriPermissions.any { it.uri == u && it.isWritePermission }
            } catch (e: Exception) { false }
            if (ok) xferDirUri = u
        }
    }

    private fun xferDirDisplayName(): String {
        val tree = xferDirUri ?: return ""
        val docId = try { DocumentsContract.getTreeDocumentId(tree) } catch (e: Exception) { "" }
        val tail = docId.substringAfterLast('/').substringAfterLast(':')
        return tail.ifEmpty { tree.lastPathSegment ?: "已选文件夹" }
    }

    private fun refreshXferDestLabel() {
        runOnUiThread {
            xferDestTv?.text = if (xferDirUri != null) "接收文件夹：${xferDirDisplayName()}"
                else "接收文件夹：未选（文件存本机应用目录 xfer）"
        }
    }

    private fun launchXferTreePicker() {
        val intent = Intent(Intent.ACTION_OPEN_DOCUMENT_TREE)
        startActivityForResult(intent, REQ_PICK_DIR)
    }

    // ---------- WebSocket server (host) ----------
    inner class KernelServer(addr: InetSocketAddress) : WebSocketServer(addr) {
        override fun onOpen(conn: WebSocket, handshake: ClientHandshake) {
            klog("server: conn open from ${conn.remoteSocketAddress}")
        }
        override fun onClose(conn: WebSocket, code: Int, reason: String, remote: Boolean) {
            val no = clientConns.entries.firstOrNull { it.value == conn }?.key
            if (no != null) { clientConns.remove(no); clientReady.remove(no); clientFailed.remove(no); clientExited.remove(no); deviceSizes.remove(no); refreshDevicesTv() }
            // v0.6.1：播放期成员掉线即按活跃集自动重排（画面补齐、播放不中断）
            if (no != null && inPlaybackSession() && currentMode != null) relayout("disconnect")
            klog("server: conn closed no=$no reason=$reason")
            // v0.5.0：互传对端断开——发送方关停服务作废本轮；接收方作废拉取
            if (no != null && xferSendTid != null && xferSendTargetNo == no) {
                stopXferServer("peer_disconnect")
                xferSendTid = null
                klog("XFER peer disconnected no=$no side=sender")
            }
            if (no != null && xferRecvTid != null && xferRecvFromNo == no) {
                xferRecvGen++
                xferRecvTid = null
                hideXferBanner()
                klog("XFER peer disconnected no=$no side=receiver")
            }
            setStatus("从机连接数: ${clientConns.size}")
        }
        override fun onMessage(conn: WebSocket, message: String) {
            try {
                val o = JSONObject(message)
                when (o.optString("t")) {
                    "HELLO" -> {
                        // v0.6.5：编号复用——取当前未占用的最小正整数（断开时 onClose 已清理释放）；
                        // 分配＋登记在锁内完成，保任一时刻已连接从机编号互不相同
                        val no = synchronized(clientConns) {
                            var cand = 1
                            while (clientConns.containsKey(cand)) cand++
                            clientConns[cand] = conn
                            cand
                        }
                        val s = parseSize(o)
                        deviceSizes[no] = s
                        logSize(no, s, o.optDouble("xdpi", 0.0).toFloat(), o.optDouble("ydpi", 0.0).toFloat(),
                            o.optDouble("xdpi", 0.0) <= 0 || o.optDouble("ydpi", 0.0) <= 0)
                        conn.send(msg("WELCOME").put("client_no", no).toString())
                        klog("server: HELLO from ${o.optString("device_name")} -> no=$no")
                        refreshDevicesTv()
                        setStatus("从机已连接: ${clientConns.keys.sorted()} 本机IP: ${localIp()}")
                        currentMode?.let { doSendLayout(it) }
                    }
                    "HELLO_UPDATE" -> {
                        val no = clientConns.entries.firstOrNull { it.value == conn }?.key
                        if (no != null) {
                            val s = parseSize(o)
                            deviceSizes[no] = s
                            logSize(no, s, o.optDouble("xdpi", 0.0).toFloat(), o.optDouble("ydpi", 0.0).toFloat(),
                                o.optDouble("xdpi", 0.0) <= 0 || o.optDouble("ydpi", 0.0) <= 0)
                            klog("server: HELLO_UPDATE no=$no phys_mm=${fmt1(s.physW)}x${fmt1(s.physH)}")
                            refreshDevicesTv()
                            currentMode?.let { doSendLayout(it) }
                        }
                    }
                    "PING" -> {
                        val h2 = System.currentTimeMillis()
                        val c1 = o.optLong("c1")
                        conn.send(msg("PONG").put("c1", c1).put("h2", h2).put("h3", System.currentTimeMillis()).toString())
                    }
                    "READY" -> {
                        val no = clientConns.entries.firstOrNull { it.value == conn }?.key ?: -1
                        // v0.6.1（§14）：已退出从机重新 READY 即清除退出标记——恢复设备行状态；
                        // 播放中重入先按恢复后的活跃集重排（LAYOUT 先于 START 到达，该机起播即有正确切片），未起播时仅重发一轮布局备齐切片
                        val wasExited = no >= 0 && clientExited.remove(no)
                        clientReady[no] = true
                        klog("server: READY from no=$no buffered=${o.optLong("buffered_ms")}")
                        setStatus("READY: ${clientReady.keys.sorted()} / 连接: ${clientConns.keys.sorted()}")
                        if (wasExited) {
                            refreshDevicesTv()
                            if (currentMode != null) {
                                if (inPlaybackSession()) relayout("rejoin") else doSendLayout(currentMode!!)
                            }
                        }
                        hostMaybeStart()
                    }
                    "EXIT_PLAYBACK" -> {
                        // v0.6.1（§14）：从机退出本机播放——主机只做三件事：设备行标记「已退出播放」、状态行提示、记日志；
                        // 主机不暂停、不做任何播放动作（暂停与否由主机用户手动决定，Owen 明确口径）。播放中再按活跃集自动重排。
                        val no = clientConns.entries.firstOrNull { it.value == conn }?.key ?: -1
                        if (no >= 0) {
                            clientExited.add(no)
                            klog("HOST note client=$no exit playback")
                            setStatus("$no 号机已退出播放")
                            refreshDevicesTv()
                            if (inPlaybackSession() && currentMode != null) relayout("exit")
                        }
                    }
                    "PREPARE_FAIL" -> {
                        // v0.3.2：从机远程备片超时回报——记录失败、提示主机，且不阻塞全场起播
                        val no = clientConns.entries.firstOrNull { it.value == conn }?.key ?: -1
                        val reason = o.optString("reason", "")
                        if (no >= 0) clientFailed[no] = reason
                        val reasonCn = when (reason) {
                            "link_timeout" -> "链接无法直接播放"
                            "dist_stream_timeout" -> "分发拉取超时"
                            else -> reason
                        }
                        klog("PREPARE_FAIL no=$no reason=$reason")
                        setStatus("从机 $no 备片失败：$reasonCn")
                        hostMaybeStart()
                    }
                    "STAT" -> klog("server: STAT $message")
                    "RESYNC" -> klog("server: RESYNC $message")
                    // v0.5.0：从机→主机方向的文件互传消息（主机可为发送方或接收方，凭 tid 与对端编号判读）
                    "XFER_OFFER" -> {
                        // 主机为接收方：发送方 IP 取连接对端地址
                        val no = clientConns.entries.firstOrNull { it.value == conn }?.key ?: -1
                        val ip = conn.remoteSocketAddress?.address?.hostAddress ?: ""
                        if (no >= 0) onXferOffer(no, ip, o)
                    }
                    "XFER_ACCEPT" -> onXferAccept(o.optString("tid", ""), clientConns.entries.firstOrNull { it.value == conn }?.key ?: -1)
                    "XFER_REJECT" -> onXferReject(o.optString("tid", ""), clientConns.entries.firstOrNull { it.value == conn }?.key ?: -1)
                    "XFER_CANCEL" -> onXferCancel(o.optString("tid", ""))
                    "XFER_FILE_DONE" -> onXferFileDone(o.optString("tid", ""), o.optInt("idx", -1), o.optBoolean("ok", false),
                        clientConns.entries.firstOrNull { it.value == conn }?.key ?: -1)
                    "XFER_DONE" -> onXferDone(o.optString("tid", ""), clientConns.entries.firstOrNull { it.value == conn }?.key ?: -1)
                }
            } catch (e: Exception) { klog("server msg err: ${e.message}") }
        }
        override fun onError(conn: WebSocket?, ex: Exception) { klog("server error: ${ex.message}") }
        override fun onStart() { klog("server started port=$PORT") }
    }

    // ---------- WebSocket client (slave) ----------
    inner class KernelClient(uriStr: String) : WebSocketClient(java.net.URI(uriStr)) {
        override fun onOpen(handshakedata: ServerHandshake) {
            klog("client: ws open")
            sessionActive = true
            updateKeepScreenOn()
            val s = measureSize()
            mySize = s
            send(helloJson("HELLO", s).toString())
            setStatus("已连接，等待编号…")
        }
        override fun onMessage(message: String) {
            try {
                val o = JSONObject(message)
                when (o.optString("t")) {
                    "WELCOME" -> {
                        myNo = o.optInt("client_no")
                        klog("client: WELCOME no=$myNo")
                        logMySize(myNo)
                        setStatus("已锁定编号 $myNo，开始对时…")
                        showBigNumber("standby") // v0.6.5：编号锁定即亮待机大编号（走统一出口）
                        startClockSyncLoop()
                        startStatLoop()
                    }
                    "PONG" -> {
                        val c1 = o.optLong("c1")
                        pendingPongs[c1]?.invoke(o.optLong("h2"), o.optLong("h3"), c1)
                    }
                    "PREPARE" -> {
                        prepareRequested = true
                        readySent = false
                        val url = o.optString("url", "local-file")
                        klog("client: PREPARE received, mediaReady=$mediaReady url=${if (url.startsWith("http")) "remote" else url}")
                        if (url.startsWith("http://") || url.startsWith("https://")) {
                            // 改动六：远程媒体（直链 / 主机分发）——直接以 url 建播放器并 prepare，不许再提示本地选片
                            // v0.3.2：分发走下载后播、直链走流式＋15 秒超时；fromPrepare 表示重走流程时重新计时
                            runOnUiThread { startRemoteMedia(url, fromPrepare = true) }
                        } else {
                            // local-file：与现行本地选片路径完全一致
                            runOnUiThread { sourceTv?.text = "来源：本地文件" }
                            // v0.2.1 线程归位：playbackState 读取与 sendReadyOnce 整体回主线程执行
                            runOnUiThread {
                                val p = player
                                when {
                                    p == null -> {}
                                    p.playbackState == Player.STATE_ENDED -> {
                                        // v0.3：播完后重走全流程——回卷到 0 后回 READY（START 的 play() 才能生效）
                                        programSeek(p, 0)
                                        playbackEnded = false
                                        sendReadyOnce()
                                        klog("PREPARE: ended player rewound to 0, READY resent")
                                    }
                                    mediaReady && p.playbackState == Player.STATE_READY -> {
                                        sendReadyOnce() // 已 prepare 完成：立即回 READY，不等状态事件
                                    }
                                    !mediaReady -> setStatus("收到 PREPARE，请先选片")
                                }
                            }
                        }
                    }
                    "START" -> {
                        val startAt = o.optLong("start_at_hostclock")
                        firstTickAfterStart = true // v0.3.3：仅标记起播后第一拍供日志区分（first=1），校正走统一微调规则
                        seekCooldownUntilMs = 0 // v0.3.1：新一轮起播不继承上一轮的 seek 冷却
                        klog("client: START start_at=$startAt offset=$offsetMs")
                        schedulePlay(startAt, isHostClock = false, mediaPos = o.optLong("media_pos_ms", 0))
                    }
                    "TICK" -> runOnUiThread {
                        onTick(o.optLong("host_clock"), o.optLong("media_pos_ms"),
                            o.optString("state", "playing"), o.optDouble("rate", 1.0).toFloat())
                    }
                    "PAUSE" -> runOnUiThread {
                        val pos = o.optLong("media_pos_ms")
                        val p = player
                        if (p != null && started) {
                            val before = p.currentPosition
                            if (abs(before - pos) > 80) programSeek(p, pos)
                            p.pause()
                            klog("PAUSE exec media_pos_ms=$pos own_pos_before=$before")
                        } else {
                            klog("PAUSE ignored (not started) media_pos_ms=$pos")
                        }
                        localPaused = true
                        releasePlayWakeLock("host pause")
                    }
                    "RESUME" -> {
                        // 不置 firstTickAfterStart：RESUME 的定时起播不触发首次 TICK 硬对齐
                        val startAt = o.optLong("start_at_hostclock")
                        val pos = o.optLong("media_pos_ms")
                        val rate = o.optDouble("rate", 1.0).toFloat()
                        sessionRate = rate
                        rateState = fmtSpeed(rate)
                        klog("RESUME received start_at=$startAt media_pos_ms=$pos rate=$rate")
                        scheduleResume(startAt, pos, isHostClock = false)
                    }
                    "STOP" -> runOnUiThread {
                        // v0.6.3：主机结束当前视频（协议 §15）——本机停播放器清媒体、回待机大数字屏、状态行「等待主机选片」；连接保持，不回 EXIT_PLAYBACK
                        execStopPlayback()
                    }
                    "SEEK" -> runOnUiThread {
                        val pos = o.optLong("media_pos_ms")
                        val p = player
                        if (p != null && started) {
                            programSeek(p, pos) // 播放中继续播、暂停中保持暂停，均不自行起播
                            klog("SEEK exec media_pos_ms=$pos paused=$localPaused")
                        } else {
                            klog("SEEK ignored (not started) media_pos_ms=$pos")
                        }
                    }
                    "RATE" -> runOnUiThread {
                        val rate = o.optDouble("rate", 1.0).toFloat()
                        sessionRate = rate
                        val p = player
                        if (p != null && started && !localPaused) {
                            p.setPlaybackSpeed(rate)
                            appliedRate = rate // v0.3.3 复位点：RATE 确定的会话速率即新实际速率
                            rateState = fmtSpeed(rate)
                        }
                        klog("RATE exec rate=$rate")
                    }
                    "BRIGHTNESS" -> runOnUiThread {
                        // 改动三：主机广播亮度——主线程应用本机窗口亮度，并同步本机滑杆位置（主机值为准）
                        val level = o.optDouble("level", 1.0).toFloat().coerceIn(0.05f, 1.0f)
                        applyBrightness(level)
                        clientBrightBar?.progress = ((level - 0.05f) / 0.95f * 100).toInt().coerceIn(0, 100)
                        klog("BRIGHTNESS level=${fmt2(level.toDouble())} applied=true")
                    }
                    "LAYOUT" -> {
                        canvasRatio = o.optDouble("canvas_ratio", 0.0)
                        layoutFit = o.optString("fit", "cover") // v0.6.0：全场显示模式随 LAYOUT 下发，缺省 cover 兼容旧端
                        val arr = o.optJSONArray("tiles")
                        var mine: Tile? = null
                        if (arr != null) {
                            for (i in 0 until arr.length()) {
                                val t = arr.getJSONObject(i)
                                if (t.optInt("client_no") == myNo) {
                                    mine = Tile(myNo, t.optDouble("x"), t.optDouble("y"), t.optDouble("w"), t.optDouble("h"))
                                }
                            }
                        }
                        myTile = mine ?: Tile(myNo, 0.0, 0.0, 1.0, 1.0)
                        klog("client: LAYOUT canvas_ratio=${fmt4(canvasRatio)} myTile=[${fmt4(myTile!!.x)},${fmt4(myTile!!.y)},${fmt4(myTile!!.w)},${fmt4(myTile!!.h)}] found=${mine != null}")
                        runOnUiThread { applyTileTransform() } // v0.2.1 防御性归位（applyTileTransform 内部原已自带 runOnUiThread）
                    }
                    // v0.5.0：主机→从机方向的文件互传消息（发送方为主机，编号 0）
                    "XFER_OFFER" -> onXferOffer(0, connectedHostIp, o)
                    "XFER_ACCEPT" -> onXferAccept(o.optString("tid", ""), 0)
                    "XFER_REJECT" -> onXferReject(o.optString("tid", ""), 0)
                    "XFER_CANCEL" -> onXferCancel(o.optString("tid", ""))
                    "XFER_FILE_DONE" -> onXferFileDone(o.optString("tid", ""), o.optInt("idx", -1), o.optBoolean("ok", false), 0)
                    "XFER_DONE" -> onXferDone(o.optString("tid", ""), 0)
                }
            } catch (e: Exception) { klog("client msg err: ${e.message}") }
        }
        override fun onClose(code: Int, reason: String, remote: Boolean) {
            klog("client: ws closed $reason")
            sessionActive = false
            updateKeepScreenOn()
            releasePlayWakeLock("ws closed")
            setStatus("连接已断开: $reason")
            hideClientBar() // v0.6.1：与主机断开，撤下从机退出条
            showBigNumber("disconnect") // v0.6.5：断线回到待机，大编号重现
            // v0.5.0：与主机断开——作废互传两向状态
            if (xferSendTid != null) { stopXferServer("peer_disconnect"); xferSendTid = null }
            if (xferRecvTid != null) { xferRecvGen++; xferRecvTid = null; hideXferBanner() }
        }
        override fun onError(ex: Exception) {
            klog("client: ws error ${ex.message}")
            setStatus("连接错误: ${ex.message}")
        }
    }
}
