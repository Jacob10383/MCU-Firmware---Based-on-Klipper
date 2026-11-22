#include "basecmd.h" // oid_alloc
#include "board/gpio.h" // struct gpio_adc
#include "board/misc.h" // alloc_maxsize
#include "command.h" // DECL_COMMAND
#include "sched.h" // DECL_TASK
#include "i2ccmds.h"
#include "trsync.h" // trsync_do_trigger
#include "internal.h" // GPIO
#include "board/irq.h" // irq_disable

DECL_CONSTANT("CARTOGRAPHER_SENSOR_FREQ_DIVISOR", 8);
DECL_CONSTANT("CARTOGRAPHER_ADC_SMOOTH_COUNT", 16);
DECL_CONSTANT("CARTOGRAPHER_EXP_VERSION", 3);

#define LDC_REG_DATA_MSB    0x00
#define LDC_REG_DATA_LSB    0x01
#define LDC_REG_RCOUNT_CH0  0x08
#define LDC_REG_SETTLE_CH0  0x10
#define LDC_REG_CLKDIV_CH0  0x14
#define LDC_REG_STATUS      0x18
#define LDC_REG_ERR_CONFIG  0x19
#define LDC_REG_CONFIG      0x1A
#define LDC_REG_MUX_CONFIG  0x1B
#define LDC_REG_DRIVE_CH0   0x1E

#define LDC_STATUS_UNREAD0  0x0008
#define LDC_CONFIG_ACTIVE   0x1601
#define LDC_CONFIG_SLEEP    0x3601

#define RING_SIZE           64
#define RING_MASK           (RING_SIZE - 1)
#define MAX_COMB            32
#define MAX_WIN             25
#define MIN_WIN             3

// Q24 biquad notch coefficients for f0=26.5 Hz, Q=1.5 at fs=606.9 Hz
#define NOTCH_SHIFT         24
#define NOTCH_B0            15387562LL
#define NOTCH_B1            (-29624101LL)
#define NOTCH_B2            15387562LL
#define NOTCH_A1            (-29624101LL)
#define NOTCH_A2            13997909LL

static uint32_t trigger_freq = 33784425, untrigger_freq = 33581718;
static uint8_t idm_trigger_reason, idm_trigger_invert;
static struct trsync *idm_ts;
static struct i2cdev_s *idm_i2c;

static uint8_t idm_status = 0;      // 1 = high-rate streaming active
static uint8_t trigger_method = 0;  // 0 = scan, 1 = touch
static uint8_t idm_home_flag = 0;   // 1 = homing active
static uint32_t trigger_threshold = 1000;

static struct gpio_adc temp_in;
static struct gpio_out led;
static struct gpio_out power;

static struct task_wake poll_wake;
static struct timer poll_timer;

// LDC1612 runtime parameters
static uint16_t cur_rcount = 0x088C;
static uint16_t cur_mux = 0x020C;
static uint32_t conv_us = 1647;
static uint32_t ldc_err_count = 0;
static uint8_t ldc_last_err = 0;

// Non-blocking ADC temperature accumulator
static uint32_t adc_accum = 0;
static uint8_t adc_count = 0;
static uint32_t cached_temp = 55927;

// Homing / trigger state & diagnostics
static uint8_t homing_triggered = 0;
static uint32_t trigger_clock = 0;
static int32_t last_peak_slope = 0;
static int32_t last_trig_slope = 0;
static uint32_t last_sample_count = 0;

// Touch detector configuration (runtime-tunable)
// mode 0: Comb+OLS slope + peak-drop (signed-safe)
// mode 1: Comb+OLS slope + lagged-baseline fractional drop + hold + backdate
// mode 2: Fast Notch(26.5Hz,Q=1.5)+OLS(win) against Comb+OLS3 lagged baseline
static uint8_t touch_mode = 2;
static uint8_t touch_comb = 23;     // 26.4 Hz + 52.8 Hz notch for baseline
static uint8_t touch_win = 7;       // OLS window (3 for mode1, 7 for mode2)
static uint8_t touch_hold = 2;      // consecutive samples below ratio
static uint16_t touch_frac_pct = 50;
static uint32_t touch_min_slope = 500;
static uint8_t touch_lag = 8;       // ~13 ms lag behind current for baseline
static uint8_t touch_backdate = 1;

// Touch detector ring state
static uint32_t data_anchor = 0;
static int32_t rel_ring[RING_SIZE];
static int32_t box_ring[RING_SIZE];
static uint32_t clk_ring[RING_SIZE];
static int32_t slope_ring[RING_SIZE];
static int64_t box_sum = 0;
static uint32_t ring_idx = 0;
static uint32_t sample_count = 0;
static int32_t touch_peak = 0;
static int32_t touch_baseline = 0;
static uint8_t baseline_init = 0;
static uint8_t hold_count = 0;

// Biquad notch state (Q24 scaled outputs/inputs kept as int64_t)
static int64_t notch_x1 = 0, notch_x2 = 0, notch_y1 = 0, notch_y2 = 0;
static uint8_t notch_init = 0;

static uint32_t
calc_conv_us(uint16_t rcount)
{
    uint64_t ticks = ((uint64_t)rcount * 16ULL + 4ULL) * 100ULL;
    uint32_t us = (uint32_t)(ticks / 2125ULL);
    return us < 100 ? 100 : us;
}

static uint16_t
readRegister(uint8_t reg)
{
    uint8_t data[2];
    int ret = i2c_dev_read(idm_i2c, 1, &reg, 2, data);
    i2c_shutdown_on_err(ret);
    return ((uint16_t)data[0] << 8) | data[1];
}

static void
writeRegister(uint8_t reg, uint16_t data)
{
    uint8_t buffer[3];
    buffer[0] = reg;
    buffer[1] = data >> 8;
    buffer[2] = data;
    i2c_dev_write(idm_i2c, 3, buffer);
}

static void
idm_sleep(uint32_t delay_us)
{
    uint32_t timeout = timer_read_time() + timer_from_us(delay_us);
    for (;;) {
        if (!timer_is_before(timer_read_time(), timeout))
            break;
    }
}

static void
configure_ldc(uint16_t rcount, uint16_t mux)
{
    writeRegister(LDC_REG_CONFIG, LDC_CONFIG_SLEEP);
    writeRegister(LDC_REG_MUX_CONFIG, mux);
    writeRegister(LDC_REG_DRIVE_CH0, 0xD000);
    writeRegister(LDC_REG_SETTLE_CH0, 0x0100);
    writeRegister(LDC_REG_CLKDIV_CH0, 0x1001);
    writeRegister(LDC_REG_RCOUNT_CH0, rcount);
    writeRegister(LDC_REG_ERR_CONFIG, 0x0001);
    writeRegister(LDC_REG_CONFIG, LDC_CONFIG_ACTIVE);
    cur_rcount = rcount;
    cur_mux = mux;
    conv_us = calc_conv_us(rcount);
}

static uint_fast8_t
poll_timer_handler(struct timer *timer)
{
    sched_wake_task(&poll_wake);
    return SF_DONE;
}

static void
schedule_poll_at(uint32_t waketime)
{
    irq_disable();
    sched_del_timer(&poll_timer);
    poll_timer.waketime = waketime;
    sched_add_timer(&poll_timer);
    irq_enable();
}

static void
wake_poll_now(void)
{
    irq_disable();
    sched_del_timer(&poll_timer);
    sched_wake_task(&poll_wake);
    irq_enable();
}

static void
reset_touch_state(void)
{
    data_anchor = 0;
    box_sum = 0;
    ring_idx = 0;
    sample_count = 0;
    touch_peak = 0;
    touch_baseline = 0;
    baseline_init = 0;
    hold_count = 0;
    notch_x1 = notch_x2 = notch_y1 = notch_y2 = 0;
    notch_init = 0;
    homing_triggered = 0;
    trigger_clock = 0;
    last_peak_slope = 0;
    last_trig_slope = 0;
    last_sample_count = 0;
}

static void
fire_trigger(uint32_t clk, int32_t peak, int32_t slope)
{
    irq_disable();
    if (idm_home_flag && idm_ts) {
        trsync_do_trigger(idm_ts, idm_trigger_reason);
        idm_home_flag = 0;
        homing_triggered = 1;
        trigger_clock = clk;
        last_peak_slope = peak;
        last_trig_slope = slope;
        last_sample_count = sample_count;
    }
    irq_enable();
}

static int32_t
compute_ols_ring(const int32_t *ring, uint32_t newest_idx, uint8_t w)
{
    uint32_t oldest_idx = (newest_idx + RING_SIZE + 1 - w) & RING_MASK;
    int64_t base = (int64_t)ring[oldest_idx];
    int64_t num = 0;
    for (uint8_t i = 0; i < w; i++) {
        int32_t weight = 2 * (int32_t)i - ((int32_t)w - 1);
        int64_t val = (int64_t)ring[(oldest_idx + i) & RING_MASK] - base;
        num += (int64_t)weight * val;
    }
    int64_t den = ((int64_t)w * ((int64_t)w * (int64_t)w - 1)) / 6;
    return (int32_t)(num / den);
}

static int32_t
apply_notch265(int32_t x)
{
    int64_t x0 = (int64_t)x;
    if (!notch_init) {
        notch_x1 = notch_x2 = notch_y1 = notch_y2 = x0;
        notch_init = 1;
        return x;
    }
    int64_t acc = NOTCH_B0 * x0 + NOTCH_B1 * notch_x1 + NOTCH_B2 * notch_x2
                - NOTCH_A1 * notch_y1 - NOTCH_A2 * notch_y2;
    int64_t y0 = acc >> NOTCH_SHIFT;
    notch_x2 = notch_x1;
    notch_x1 = x0;
    notch_y2 = notch_y1;
    notch_y1 = y0;
    return (int32_t)y0;
}

static void
touch_process_sample(uint32_t clk, uint32_t data)
{
    uint32_t idx = ring_idx & RING_MASK;
    if (sample_count == 0)
        data_anchor = data;
    int32_t rel = (int32_t)(data - data_anchor);
    rel_ring[idx] = rel;
    clk_ring[idx] = clk;
    ring_idx++;
    sample_count++;

    // Running O(1) comb/boxcar average (used for baseline in modes 1 & 2, slope in modes 0 & 1)
    uint8_t comb = touch_comb;
    box_sum += (int64_t)rel;
    if (sample_count > comb) {
        int32_t old_rel = rel_ring[(idx + RING_SIZE - comb) & RING_MASK];
        box_sum -= (int64_t)old_rel;
    }
    if (sample_count >= comb)
        box_ring[idx] = (int32_t)(box_sum / (int64_t)comb);
    else
        box_ring[idx] = 0;

    // Mode 2: Fast Notch(26.5Hz) on raw OLS(win) vs smooth Box(comb)+OLS3 lagged baseline
    if (touch_mode == 2) {
        uint8_t w = touch_win;
        int32_t fast_notched = 0;
        if (sample_count >= w) {
            int32_t fast_raw = compute_ols_ring(rel_ring, idx, w);
            fast_notched = apply_notch265(fast_raw);
        }

        uint32_t base_ready = (uint32_t)comb + 2; // Box(comb) + OLS(3)
        if (sample_count < base_ready) {
            slope_ring[idx] = 0;
            return;
        }
        int32_t box_slope = compute_ols_ring(box_ring, idx, 3);
        slope_ring[idx] = box_slope;

        uint8_t lag = touch_lag;
        if (sample_count < base_ready + (uint32_t)lag)
            return;

        int32_t lagged = slope_ring[(idx + RING_SIZE - lag) & RING_MASK];
        if (!baseline_init) {
            touch_baseline = lagged;
            baseline_init = 1;
        } else {
            touch_baseline = (touch_baseline * 3 + lagged) / 4;
        }

        int32_t min_s = touch_min_slope ? (int32_t)touch_min_slope : (int32_t)trigger_threshold;
        if (touch_baseline >= min_s
            && (int64_t)fast_notched * 100 < (int64_t)touch_baseline * (int64_t)touch_frac_pct) {
            hold_count++;
            if (hold_count >= touch_hold) {
                uint32_t tclk = clk;
                if (touch_backdate) {
                    // OLS(w) midpoint + hold delay (notch has ~0 HF phase lag)
                    uint32_t back = (uint32_t)(w / 2) + (uint32_t)(touch_hold - 1);
                    if (back < sample_count && back < RING_SIZE)
                        tclk = clk_ring[(idx + RING_SIZE - back) & RING_MASK];
                }
                fire_trigger(tclk, touch_baseline, fast_notched);
            }
        } else {
            hold_count = 0;
        }
        return;
    }

    // Modes 0 & 1: Comb+OLS slope
    uint8_t w = touch_win;
    uint32_t slope_ready = (uint32_t)comb + (uint32_t)w - 1;
    if (sample_count < slope_ready) {
        slope_ring[idx] = 0;
        return;
    }

    int32_t slope = compute_ols_ring(box_ring, idx, w);
    slope_ring[idx] = slope;

    if (touch_mode == 0) {
        if (touch_peak > 100 && (touch_peak - slope) > (int32_t)trigger_threshold) {
            uint32_t tclk = clk;
            if (touch_backdate) {
                uint32_t back = (comb / 2) + (w / 2);
                if (back < sample_count && back < RING_SIZE)
                    tclk = clk_ring[(idx + RING_SIZE - back) & RING_MASK];
            }
            fire_trigger(tclk, touch_peak, slope);
        } else if (slope > touch_peak) {
            touch_peak = slope;
        }
        return;
    }

    // Mode 1: Lagged-baseline fractional slope drop + hold + linear-ramp backdate
    uint8_t lag = touch_lag;
    if (sample_count < slope_ready + (uint32_t)lag)
        return;

    int32_t lagged = slope_ring[(idx + RING_SIZE - lag) & RING_MASK];
    if (!baseline_init) {
        touch_baseline = lagged;
        baseline_init = 1;
    } else {
        touch_baseline = (touch_baseline * 3 + lagged) / 4;
    }

    int32_t min_s = touch_min_slope ? (int32_t)touch_min_slope : (int32_t)trigger_threshold;
    if (touch_baseline >= min_s
        && (int64_t)slope * 100 < (int64_t)touch_baseline * (int64_t)touch_frac_pct) {
        hold_count++;
        if (hold_count >= touch_hold) {
            uint32_t tclk = clk;
            if (touch_backdate) {
                uint32_t ramp_delay = ((uint32_t)(100 - touch_frac_pct) * (uint32_t)comb + 50) / 100;
                uint32_t back = ramp_delay + (uint32_t)(w / 2) + (uint32_t)(touch_hold - 1);
                if (back < sample_count && back < RING_SIZE)
                    tclk = clk_ring[(idx + RING_SIZE - back) & RING_MASK];
            }
            fire_trigger(tclk, touch_baseline, slope);
        }
    } else {
        hold_count = 0;
    }
}

static void
sample_temp_nonblocking(void)
{
    if (gpio_adc_sample(temp_in) == 0) {
        adc_accum += gpio_adc_read(temp_in);
        adc_count++;
        if (adc_count >= 16) {
            cached_temp = adc_accum;
            adc_accum = 0;
            adc_count = 0;
        }
    }
}

void
idm_poll_task(void)
{
    if (!sched_check_wake(&poll_wake))
        return;

    uint8_t active = idm_status || idm_home_flag;
    uint16_t status = readRegister(LDC_REG_STATUS);

    if (!(status & LDC_STATUS_UNREAD0)) {
        uint32_t wait_us = active ? 120 : 100000;
        schedule_poll_at(timer_read_time() + timer_from_us(wait_us));
        return;
    }

    uint32_t sample_clock = timer_read_time();
    uint16_t msb = readRegister(LDC_REG_DATA_MSB);
    uint16_t lsb = readRegister(LDC_REG_DATA_LSB);
    uint8_t err = (msb >> 12) & 0x0F;
    uint32_t data = (((uint32_t)(msb & 0x0FFF)) << 16) | lsb;

    if (err || data == 0) {
        ldc_err_count++;
        ldc_last_err = err;
    } else {
        if (idm_home_flag) {
            if (trigger_method) {
                touch_process_sample(sample_clock, data);
            } else if (data > trigger_freq) {
                fire_trigger(sample_clock, (int32_t)data, (int32_t)trigger_freq);
                gpio_out_write(led, 1);
            } else if (data < untrigger_freq) {
                gpio_out_write(led, 0);
            }
        } else {
            if (data > trigger_freq)
                gpio_out_write(led, 1);
            else if (data < untrigger_freq)
                gpio_out_write(led, 0);
        }

        sample_temp_nonblocking();

        if (idm_status || !active) {
            sendf("cartographer_data clock=%u data=%u temp=%u",
                  sample_clock, data, cached_temp);
        }
    }

    active = idm_status || idm_home_flag;
    uint32_t now = timer_read_time();
    if (active) {
        uint32_t next_us = conv_us > 250 ? (conv_us - 200) : 100;
        uint32_t target = sample_clock + timer_from_us(next_us);
        uint32_t min_target = now + timer_from_us(50);
        if (timer_is_before(target, min_target))
            target = min_target;
        schedule_poll_at(target);
    } else {
        schedule_poll_at(now + timer_from_us(100000));
    }
}
DECL_TASK(idm_poll_task);

void
idm_init(void)
{
    power = gpio_out_setup(GPIO('B', 4), 0);
#if CONFIG_CANSERIAL
    gpio_out_setup(GPIO('A', 3), 1);
#endif
    idm_sleep(50000);
    gpio_pwm_setup(GPIO('B', 6), 8, 1 << 14);
    led = gpio_out_setup(GPIO('A', 15), 0);
    temp_in = gpio_adc_setup(GPIO('A', 4));

    uint32_t init_temp = 0;
    for (uint8_t j = 0; j < 16; ) {
        if (gpio_adc_sample(temp_in) == 0) {
            init_temp += gpio_adc_read(temp_in);
            j++;
        }
    }
    cached_temp = init_temp;

    idm_i2c = alloc_chunk(sizeof(*idm_i2c));
    idm_i2c->i2c_hw = i2c_setup(0, 400000, (0x2A & 0x7f));
    idm_i2c->flags |= 2;
    configure_ldc(cur_rcount, cur_mux);

    poll_timer.func = poll_timer_handler;
    schedule_poll_at(timer_read_time() + timer_from_us(5000));
}
DECL_INIT(idm_init);

void
turn_off_idm(void)
{
    irq_disable();
    sched_del_timer(&poll_timer);
    idm_status = 0;
    idm_home_flag = 0;
    irq_enable();
    gpio_out_write(led, 1);
}

void
command_idm_stream(uint32_t *args)
{
    irq_disable();
    idm_status = args[0] ? 1 : 0;
    irq_enable();
    if (idm_status)
        wake_poll_now();
}
DECL_COMMAND(command_idm_stream, "cartographer_stream en=%u");

void
command_idm_set_threshold(uint32_t *args)
{
    trigger_freq = args[0];
    untrigger_freq = args[1];
}
DECL_COMMAND(command_idm_set_threshold,
             "cartographer_set_threshold trigger=%u untrigger=%u");

void
command_idm_home(uint32_t *args)
{
    irq_disable();
    idm_ts = trsync_oid_lookup(args[0]);
    idm_trigger_reason = args[1];
    idm_trigger_invert = args[2];
    trigger_threshold = args[3];
    trigger_method = args[4];
    reset_touch_state();
    idm_home_flag = 1;
    irq_enable();
    wake_poll_now();
}
DECL_COMMAND(command_idm_home,
             "cartographer_home trsync_oid=%c trigger_reason=%c"
             " trigger_invert=%c threshold=%u trigger_method=%u");

void
command_idm_stop_home(uint32_t *args)
{
    irq_disable();
    idm_home_flag = 0;
    idm_ts = NULL;
    irq_enable();
}
DECL_COMMAND(command_idm_stop_home, "cartographer_stop_home");

void
command_idm_query_home(uint32_t *args)
{
    sendf("cartographer_home_state triggered=%c clock=%u peak=%i slope=%i"
          " samples=%u errors=%u",
          homing_triggered, trigger_clock, last_peak_slope, last_trig_slope,
          last_sample_count, ldc_err_count);
}
DECL_COMMAND(command_idm_query_home, "cartographer_query_home");

void
command_idm_touch_config(uint32_t *args)
{
    uint8_t mode = args[0];
    uint8_t comb = args[1];
    uint8_t win = args[2];
    uint8_t hold = args[3];
    uint16_t frac_pct = args[4];
    uint32_t min_slope = args[5];
    uint8_t lag = args[6];
    uint8_t backdate = args[7];

    if (comb < 1)
        comb = 1;
    if (comb > MAX_COMB)
        comb = MAX_COMB;
    if (win < MIN_WIN)
        win = MIN_WIN;
    if (win > MAX_WIN)
        win = MAX_WIN;
    if (hold < 1)
        hold = 1;
    if (hold > 10)
        hold = 10;
    if (frac_pct < 1)
        frac_pct = 1;
    if (frac_pct > 99)
        frac_pct = 99;
    if (lag < 1)
        lag = 1;
    if (lag > RING_SIZE - 2)
        lag = RING_SIZE - 2;

    irq_disable();
    touch_mode = mode;
    touch_comb = comb;
    touch_win = win;
    touch_hold = hold;
    touch_frac_pct = frac_pct;
    touch_min_slope = min_slope;
    touch_lag = lag;
    touch_backdate = backdate ? 1 : 0;
    irq_enable();
}
DECL_COMMAND(command_idm_touch_config,
             "cartographer_touch_config mode=%c comb=%c win=%c hold=%c"
             " frac_pct=%hu min_slope=%u lag=%c backdate=%c");

void
command_idm_set_ldc(uint32_t *args)
{
    uint16_t rcount = args[0];
    uint16_t mux = args[1];
    if (rcount < 0x0100)
        rcount = 0x0100;
    configure_ldc(rcount, mux);
}
DECL_COMMAND(command_idm_set_ldc, "cartographer_set_ldc rcount=%hu mux=%hu");

void
command_idm_query_ldc(uint32_t *args)
{
    sendf("cartographer_ldc_state rcount=%hu mux=%hu errors=%u"
          " last_err=%c conv_us=%u",
          cur_rcount, cur_mux, ldc_err_count, ldc_last_err, conv_us);
}
DECL_COMMAND(command_idm_query_ldc, "cartographer_query_ldc");

void
command_idm_base_read(uint32_t *args)
{
    uint8_t data_len = args[0];
    uint8_t offset = args[1];
    uint32_t f_count = 31600800;
    uint16_t adc_count = 55927;
    uint64_t data = ((uint64_t)adc_count) << 32 | f_count;
    sendf("cartographer_base_data bytes=%*s offset=%hu",
          data_len, &data, offset);
}
DECL_COMMAND(command_idm_base_read,
             "cartographer_base_read len=%c offset=%hu");
