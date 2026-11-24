function IsNonNegativeNumber(element) {
  if (typeof element == "number") {
    if (element != element) {
      return false;
    } else if (element == Infinity || element == -Infinity) {
      return false;
    } else {
      return element >= 0;
    }
  }
  return false;
}

function IsPositiveNumber(element) {
  if (typeof element == "number") {
    if (element != element) {
      return false;
    } else if (element == Infinity || element == -Infinity) {
      return false;
    } else {
      return element > 0;
    }
  }
  return false;
}

function FormatSecond(Seconds, ShowColons = true) {
  if (typeof Seconds != "number") {
    throw TypeError();
  }
  if (Seconds < 10) {
    return Seconds.toFixed(1);
  } else if (Seconds < 60) {
    return `${Math.floor(Seconds)}`;
  } else if (Seconds < 3600) {
    let seconds = Math.floor(Seconds % 60);
    if (ShowColons) {
      return `${Math.floor(Seconds / 60)}:${seconds < 10 ? "0" + seconds.toString() : seconds}`;
    } else {
      return `${Math.floor(Seconds / 60)} ${seconds < 10 ? "0" + seconds.toString() : seconds}`;
    }
  } else {
    let minutes = Math.floor((Seconds / 60) % 60);
    let seconds = Math.floor(Seconds % 60);
    if (ShowColons) {
      return `${Math.floor(Seconds / 3600)}:${minutes < 10 ? "0" + minutes.toString() : minutes}:${seconds < 10 ? "0" + seconds.toString() : seconds}`;
    } else {
      return `${Math.floor(Seconds / 3600)} ${minutes < 10 ? "0" + minutes.toString() : minutes} ${seconds < 10 ? "0" + seconds.toString() : seconds}`;
    }
  }
}

class BaseTimingLogic {
  static TYPE = "sudden death";
  static NAME = "Sudden death";
  static DESCRIPTION =
    "This player loses on time when the countdown reaches 0.";

  constructor(InitialTime, TimeoutMargin) {
    if (typeof InitialTime != "number" || typeof TimeoutMargin != "number") {
      throw TypeError();
    }
    this.RemainingTime = InitialTime;
    this.TimeoutMargin = TimeoutMargin;
    this.InitialTime = InitialTime;
    this.Running = false;
    this.History = [];
    this.PreviousStartRemainingTime = 0;
    this.PreviousElapsedTime = 0;
  }

  Elapse(TimeElapsed) {
    if (typeof TimeElapsed != "number") {
      throw TypeError();
    }
    if (this.Running) {
      this.RemainingTime -= TimeElapsed;
      this.PreviousElapsedTime += TimeElapsed;
      return true;
    } else {
      return false;
    }
  }

  AddTime(TimeToAdd) {
    if (typeof TimeToAdd != "number") {
      throw TypeError();
    }
    this.RemainingTime += TimeToAdd;
  }

  IsOutOfTime() {
    return this.RemainingTime < -this.TimeoutMargin;
  }

  IsInTimeoutMargin() {
    return this.RemainingTime >= -this.TimeoutMargin && this.RemainingTime < 0;
  }

  OnCountDownStart(OpponentTimingLogic) {
    this.PreviousStartRemainingTime = this.RemainingTime;
    this.PreviousElapsedTime = 0;
    this.Running = true;
  }

  OnCountDownStop() {
    if (this.RemainingTime < 0) {
      this.RemainingTime = 0;
    }
    this.History.push({
      starttime: this.PreviousStartRemainingTime,
      stoptime: this.PreviousStartRemainingTime - this.PreviousElapsedTime,
    });
    this.Running = false;
  }

  PreviousUsedTime() {
    if (this.History.length > 0) {
      return this.History.at(-1).starttime - this.History.at(-1).stoptime;
    } else {
      return 0;
    }
  }

  FormattedRemainingTime(ShowColons = true) {
    return FormatSecond(this.RemainingTime / 1000, ShowColons);
  }

  // Translate time control to engine readable time & increment
  TimeLeft() {
    return this.RemainingTime;
  }

  // Translate time control to engine readable time & increment
  TimeIncrement() {
    return 0;
  }
}

class InfiniteTimingLogic extends BaseTimingLogic {
  static TYPE = "infinite";
  static NAME = "Infinite (No clock)";
  static DESCRIPTION = "This player has infinite time.";

  constructor() {
    super(2147483647, 0);
  }

  Elapse(TimeElapsed) {
    if (this.Running) {
      this.PreviousElapsedTime += TimeElapsed;
      return true;
    } else {
      return false;
    }
  }

  AddTime(TimeToAdd) {
    return;
  }

  IsOutOfTime() {
    return false;
  }

  IsInTimeoutMargin() {
    return false;
  }

  FormattedRemainingTime() {
    return "∞";
  }

  TimeLeft() {
    return 2147483647;
  }

  TimeIncrement() {
    return 2147483647;
  }
}

class FischerTimingLogic extends BaseTimingLogic {
  static TYPE = "tournament";
  static NAME = "Tournament (Fischer)";
  static DESCRIPTION =
    "This player has limited time and may get a time increment after a move.";

  constructor(InitialTime, TimeGain, TimeGainCooldownTurnCount, TimeoutMargin) {
    if (
      typeof InitialTime != "number" ||
      typeof TimeGain != "number" ||
      typeof TimeGainCooldownTurnCount != "number" ||
      typeof TimeoutMargin != "number"
    ) {
      throw TypeError();
    }
    super(InitialTime, TimeoutMargin);
    this.TimeGain = TimeGain;
    this.TimeGainCooldownTurnCount = TimeGainCooldownTurnCount;
    this.CurrentTimeGainCooldownTurnCount = 0;
  }

  OnCountDownStart() {
    super.OnCountDownStart();
    if (
      this.CurrentTimeGainCooldownTurnCount >= this.TimeGainCooldownTurnCount
    ) {
      this.RemainingTime += this.TimeGain;
      this.PreviousStartRemainingTime = this.RemainingTime;
    } else {
      this.CurrentTimeGainCooldownTurnCount++;
    }
  }

  TimeIncrement() {
    return this.TimeGain;
  }
}

class FixedTimeTimingLogic extends BaseTimingLogic {
  static TYPE = "fixed time";
  static NAME = "Fixed time";
  static DESCRIPTION =
    "This player needs to make each move within a fixed time limit.";

  constructor(TimePerMove, TimeoutMargin) {
    if (typeof TimePerMove != "number" || typeof TimeoutMargin != "number") {
      throw TypeError();
    }
    super(TimePerMove, TimeoutMargin);
  }

  OnCountDownStart() {
    super.OnCountDownStart();
    this.RemainingTime = this.PreviousStartRemainingTime = this.InitialTime;
  }

  TimeIncrement() {
    return this.InitialTime;
  }
}

class HourglassTimingLogic extends BaseTimingLogic {
  static TYPE = "hourglass";
  static NAME = "Hourglass";
  static DESCRIPTION =
    "This player has limited time and opponent's used time will be added to own time.";

  constructor(InitialTime, TimeoutMargin) {
    if (typeof InitialTime != "number" || typeof TimeoutMargin != "number") {
      throw TypeError();
    }
    super(InitialTime, TimeoutMargin);
  }

  OnCountDownStart(OpponentTimingLogic) {
    super.OnCountDownStart();
    if (OpponentTimingLogic instanceof BaseTimingLogic) {
      this.RemainingTime += OpponentTimingLogic.PreviousUsedTime();
      this.PreviousStartRemainingTime = this.RemainingTime;
    } else if (typeof OpponentTimingLogic == "undefined") {
    } else {
      throw TypeError();
    }
  }
}

class ByoyomiTimingLogic extends BaseTimingLogic {
  static TYPE = "byoyomi";
  static NAME = "Byo-yomi";
  static DESCRIPTION =
    "This player will enter the countdown (byoyomi) period(s) after their initial time runs out. During countdown periods, if the player make a move before the countdown period time runs out, the time will be reset to full time of countdown periods, otherwise the remaining period count will be decreased by 1 and the time will be reset to full time of countdown periods. If there's no countdown periods left and the remaining time runs out, this player runs out of time.";

  constructor(
    InitialTime,
    ByoyomiPeriodCount,
    ByoyomiPeriodLength,
    TimeoutMargin,
  ) {
    if (
      typeof InitialTime != "number" ||
      typeof ByoyomiPeriodCount != "number" ||
      typeof ByoyomiPeriodLength != "number" ||
      typeof TimeoutMargin != "number"
    ) {
      throw TypeError();
    }
    super(InitialTime, TimeoutMargin);
    this.ByoyomiPeriodCount = ByoyomiPeriodCount;
    this.ByoyomiPeriodLength = ByoyomiPeriodLength;
    this.RemainingByoyomiPeriodCount = ByoyomiPeriodCount;
  }

  Elapse(TimeElapsed) {
    if (typeof TimeElapsed != "number") {
      throw TypeError();
    }
    if (super.Elapse(TimeElapsed)) {
      if (this.RemainingTime <= 0 && this.RemainingByoyomiPeriodCount > 0) {
        this.RemainingTime = this.ByoyomiPeriodLength;
        this.RemainingByoyomiPeriodCount--;
      }
      return true;
    } else {
      return false;
    }
  }

  OnCountDownStart() {
    super.OnCountDownStart();
    if (this.RemainingByoyomiPeriodCount < this.ByoyomiPeriodCount) {
      this.RemainingTime = this.PreviousStartRemainingTime =
        this.ByoyomiPeriodLength;
    }
  }

  FormattedRemainingTime(ShowColons = true) {
    return `${super.FormattedRemainingTime(ShowColons)} (×${this.RemainingByoyomiPeriodCount})`;
  }

  TimeLeft() {
    if (
      this.RemainingByoyomiPeriodCount == this.ByoyomiPeriodCount &&
      this.RemainingByoyomiPeriodCount > 0
    ) {
      return this.RemainingTime + this.ByoyomiPeriodLength;
    } else if (
      this.RemainingByoyomiPeriodCount < this.ByoyomiPeriodCount &&
      this.RemainingByoyomiPeriodCount > 0
    ) {
      return Math.floor(this.RemainingTime + this.ByoyomiPeriodLength / 2);
    } else {
      return this.RemainingTime;
    }
  }

  TimeIncrement() {
    if (
      this.RemainingByoyomiPeriodCount == this.ByoyomiPeriodCount &&
      this.RemainingByoyomiPeriodCount > 0
    ) {
      if (this.RemainingTime >= this.ByoyomiPeriodLength) {
        return 0;
      } else {
        return this.ByoyomiPeriodLength - this.RemainingTime;
      }
    } else {
      return this.ByoyomiPeriodLength;
    }
  }
}

class SimpleDelayTimingLogic extends BaseTimingLogic {
  static TYPE = "simple delay";
  static NAME = "Simple delay";
  static DESCRIPTION =
    "This player has limited time but the clock won't elapse if they make their move within the delay time at the start of each turn.";

  constructor(InitialTime, DelayTime, TimeoutMargin) {
    if (
      typeof InitialTime != "number" ||
      typeof DelayTime != "number" ||
      typeof TimeoutMargin != "number"
    ) {
      throw TypeError();
    }
    super(InitialTime, TimeoutMargin);
    this.RemainingDelayTime = DelayTime;
    this.DelayTime = DelayTime;
  }

  Elapse(TimeElapsed) {
    if (typeof TimeElapsed != "number") {
      throw TypeError();
    }
    if (this.Running) {
      if (this.RemainingDelayTime > 0) {
        this.RemainingDelayTime -= TimeElapsed;
        if (this.RemainingDelayTime < 0) {
          this.RemainingTime += this.RemainingDelayTime;
          this.RemainingDelayTime = 0;
        }
      } else {
        this.RemainingTime -= TimeElapsed;
      }
      this.PreviousElapsedTime += TimeElapsed;
      return true;
    } else {
      return false;
    }
  }

  OnCountDownStart() {
    super.OnCountDownStart();
    this.RemainingDelayTime = this.DelayTime;
  }

  FormattedRemainingTime(ShowColons = true) {
    return `${super.FormattedRemainingTime(ShowColons)} (${FormatSecond(this.RemainingDelayTime / 1000, ShowColons)})`;
  }

  TimeLeft() {
    return this.RemainingTime + this.RemainingDelayTime;
  }
}

class BronsteinTimingLogic extends BaseTimingLogic {
  static TYPE = "bronstein";
  static NAME = "Bronstein delay";
  static DESCRIPTION =
    "This player has limited time and may get a time increment after a move, but the clock won't exceed the time at the start of each turn, which prevents gaining extra time by making fast moves.";

  constructor(InitialTime, Increment, TimeoutMargin) {
    if (
      typeof InitialTime != "number" ||
      typeof Increment != "number" ||
      typeof TimeoutMargin != "number"
    ) {
      throw TypeError();
    }
    super(InitialTime, TimeoutMargin);
    this.Increment = Increment;
    this.StartedBefore = false;
  }

  OnCountDownStart() {
    this.RemainingTime = Math.min(
      this.StartedBefore ? this.PreviousStartRemainingTime : this.InitialTime,
      this.RemainingTime + this.Increment,
    );
    this.PreviousStartRemainingTime = this.RemainingTime;
    this.Running = true;
    this.StartedBefore = true;
  }
}

export class TimingSystem {
  constructor(TimingLogicList) {
    if (!Array.isArray(TimingLogicList)) {
      throw TypeError();
    }
    this.TimerInstance = null;
    this.TimerInterval = 100;
    this.TimingLogics = TimingLogicList.filter(
      (val) => val instanceof BaseTimingLogic,
    );
    this.CurrentRound = 0;
    this.PreviousRound = 0;
    this.TotalRoundsPerTurn = 0;
    this.OnOutOfTimeCallback = null;
    this.OnTimeElapsedCallback = null;
    this.OnRoundSwitchedCallback = null;
    this.Running = false;
    this.TotalRoundsPerTurn = this.TimingLogics.length;
  }

  destructor() {
    if (this.TimerInstance != null) {
      clearInterval(this.TimerInstance);
    }
  }

  SetTimerInterval(IntervalInMilliseconds) {
    if (typeof IntervalInMilliseconds != "number") {
      throw TypeError();
    }
    if (IntervalInMilliseconds < 1) {
      throw RangeError("Interval must be a positive integer.");
    }
    if (this.Running) {
      return;
    }
    this.TimerInterval = Math.ceil(IntervalInMilliseconds);
  }

  SetCurrentRound(MoverRound) {
    if (typeof MoverRound != "number") {
      throw TypeError();
    }
    if (MoverRound < 0 || MoverRound >= this.TimingLogics.length) {
      throw RangeError(
        "Interval must be a integer between 0 and " +
          `${this.TimingLogics.length}.`,
      );
    }
    if (this.Running) {
      return;
    }
    this.CurrentRound = Math.floor(MoverRound);
  }

  SetOnOutOfTimeCallback(Callback) {
    if (typeof Callback != "function") {
      throw TypeError(
        "Callback: function(ThisArg: TimingSystem, MoverRound: number)",
      );
    }
    this.OnOutOfTimeCallback = Callback;
  }

  SetOnTimeElapsedCallback(Callback) {
    if (typeof Callback != "function") {
      throw TypeError(
        "Callback: function(ThisArg: TimingSystem, MoverRound: number, RemainingTime: number, FormattedRemainingTime: string, IsInTimoutMargin: boolean)",
      );
    }
    this.OnTimeElapsedCallback = Callback;
  }

  SetOnRoundSwitchedCallback(Callback) {
    if (typeof Callback != "function") {
      throw TypeError(
        "Callback: function(ThisArg: TimingSystem, NewMoverRound: number, TimeLeft: number, TimeIncrement: number)",
      );
    }
    this.OnRoundSwitchedCallback = Callback;
  }

  StartTiming() {
    if (this.TimerInstance == null) {
      let previoustime = Date.now();
      let timinglogic = this.TimingLogics[this.CurrentRound];
      timinglogic.OnCountDownStart();
      if (this.OnRoundSwitchedCallback) {
        this.OnRoundSwitchedCallback(
          this,
          this.CurrentRound,
          timinglogic.TimeLeft(),
          timinglogic.TimeIncrement(),
        );
      }
      this.PreviousRound = this.CurrentRound;
      this.TimerInstance = setInterval(() => {
        timinglogic = this.TimingLogics[this.PreviousRound];
        timinglogic.Elapse(Date.now() - previoustime);
        if (timinglogic.IsOutOfTime()) {
          timinglogic.OnCountDownStop();
          this.StopTiming();
          if (this.OnOutOfTimeCallback) {
            this.OnOutOfTimeCallback(this, this.PreviousRound);
          }
        } else {
          if (this.OnTimeElapsedCallback) {
            this.OnTimeElapsedCallback(
              this,
              this.PreviousRound,
              timinglogic.RemainingTime,
              timinglogic.FormattedRemainingTime((Date.now() & 1023) < 512),
              timinglogic.IsInTimeoutMargin(),
            );
          }
        }
        previoustime = Date.now();
        this.PreviousRound = this.CurrentRound;
      }, this.TimerInterval);
      this.Running = true;
    }
  }

  StopTiming() {
    if (this.TimerInstance != null) {
      clearInterval(this.TimerInstance);
      this.TimerInstance = null;
      this.Running = false;
    }
  }

  NextRound() {
    if (this.Running) {
      let old_round = this.CurrentRound;
      let timinglogic = this.TimingLogics[old_round];
      this.CurrentRound = (this.CurrentRound + 1) % this.TotalRoundsPerTurn;
      timinglogic.OnCountDownStop();
      timinglogic = this.TimingLogics[this.CurrentRound];
      timinglogic.OnCountDownStart(this.TimingLogics[old_round]);
      if (this.OnRoundSwitchedCallback) {
        this.OnRoundSwitchedCallback(
          this,
          this.CurrentRound,
          timinglogic.TimeLeft(),
          timinglogic.TimeIncrement(),
        );
      }
    }
  }

  AddTime(MoverRound, TimeToAdd) {
    if (typeof MoverRound != "number" || typeof TimeToAdd != "number") {
      throw TypeError();
    }
    if (MoverRound < 0 || MoverRound >= this.TimingLogics.length) {
      throw RangeError(
        "Interval must be a integer between 0 and " +
          `${this.TimingLogics.length}.`,
      );
    }
    if (!this.Running) {
      return;
    }
    this.TimingLogics[MoverRound].AddTime(TimeToAdd);
    if (this.OnTimeElapsedCallback) {
      this.OnTimeElapsedCallback(
        this,
        MoverRound,
        this.TimingLogics[MoverRound].RemainingTime,
        this.TimingLogics[MoverRound].FormattedRemainingTime(
          (Date.now() & 1023) < 512,
        ),
        this.TimingLogics[MoverRound].IsInTimeoutMargin(),
      );
    }
  }
}

export const TIMER_TYPES = [
  BaseTimingLogic.TYPE,
  InfiniteTimingLogic.TYPE,
  FischerTimingLogic.TYPE,
  FixedTimeTimingLogic.TYPE,
  HourglassTimingLogic.TYPE,
  ByoyomiTimingLogic.TYPE,
  SimpleDelayTimingLogic.TYPE,
  BronsteinTimingLogic.TYPE,
];
export const TIMER_TYPE_FRIENDLY_NAMES = [
  BaseTimingLogic.NAME,
  InfiniteTimingLogic.NAME,
  FischerTimingLogic.NAME,
  FixedTimeTimingLogic.NAME,
  HourglassTimingLogic.NAME,
  ByoyomiTimingLogic.NAME,
  SimpleDelayTimingLogic.NAME,
  BronsteinTimingLogic.NAME,
];
export const TIMER_TYPE_DESCRIPTIONS = [
  BaseTimingLogic.DESCRIPTION,
  InfiniteTimingLogic.DESCRIPTION,
  FischerTimingLogic.DESCRIPTION,
  FixedTimeTimingLogic.DESCRIPTION,
  HourglassTimingLogic.DESCRIPTION,
  ByoyomiTimingLogic.DESCRIPTION,
  SimpleDelayTimingLogic.DESCRIPTION,
  BronsteinTimingLogic.DESCRIPTION,
];

export const DEFAULT_TIMING_SETTINGS = {
  type: BaseTimingLogic.TYPE,
  initial_time: 300000,
  increment: 0,
  byoyomi_periods: 3,
  byoyomi_period_length: 30000,
  delay_time: 5000,
  timeout_margin: 500,
};

export function GetTimerInformation(TimerType, AddClockSuffix = false) {
  let index = TIMER_TYPES.indexOf(TimerType);
  if (index < 0) {
    return ["???", "???", "Invalid timer type."];
  } else {
    return [
      TIMER_TYPES[index],
      `${TIMER_TYPE_FRIENDLY_NAMES[index]}${AddClockSuffix ? " clock" : ""}`,
      TIMER_TYPE_DESCRIPTIONS[index],
    ];
  }
}

/* TimingSettings:
 *  {
 *      type: "sudden death" | "infinite" | "tournament" | "fixed time" | "hourglass" | "byoyomi" | "bronstein" | "simple delay",
 *      initial_time: number,
 *      increment: number,
 *      byoyomi_periods: number,
 *      byoyomi_period_length: number,
 *      delay_time: number,
 *      timeout_margin: number,
 *  }
 */
export function CreateTimingLogic(TimingSettings) {
  if (typeof TimingSettings != "object") {
    throw TypeError();
  }
  let initial_time =
    TimingSettings.initial_time || DEFAULT_TIMING_SETTINGS.initial_time;
  let increment = TimingSettings.increment || DEFAULT_TIMING_SETTINGS.increment;
  let byoyomi_periods =
    TimingSettings.byoyomi_periods || DEFAULT_TIMING_SETTINGS.byoyomi_periods;
  let byoyomi_period_length =
    TimingSettings.byoyomi_period_length ||
    DEFAULT_TIMING_SETTINGS.byoyomi_period_length;
  let delay_time =
    TimingSettings.delay_time || DEFAULT_TIMING_SETTINGS.delay_time;
  let timeout_margin =
    TimingSettings.timeout_margin || DEFAULT_TIMING_SETTINGS.timeout_margin;
  if (!IsPositiveNumber(initial_time)) {
    initial_time = DEFAULT_TIMING_SETTINGS.initial_time;
  }
  if (!IsNonNegativeNumber(increment)) {
    increment = DEFAULT_TIMING_SETTINGS.increment;
  }
  if (!IsPositiveNumber(byoyomi_periods)) {
    byoyomi_periods = DEFAULT_TIMING_SETTINGS.byoyomi_periods;
  }
  if (!IsPositiveNumber(byoyomi_period_length)) {
    byoyomi_period_length = DEFAULT_TIMING_SETTINGS.byoyomi_period_length;
  }
  if (!IsPositiveNumber(delay_time)) {
    delay_time = DEFAULT_TIMING_SETTINGS.delay_time;
  }
  if (!IsNonNegativeNumber(timeout_margin)) {
    timeout_margin = DEFAULT_TIMING_SETTINGS.timeout_margin;
  }
  if (TimingSettings.type == BaseTimingLogic.TYPE) {
    return new BaseTimingLogic(initial_time, timeout_margin);
  } else if (TimingSettings.type == InfiniteTimingLogic.TYPE) {
    return new InfiniteTimingLogic();
  } else if (TimingSettings.type == FischerTimingLogic.TYPE) {
    return new FischerTimingLogic(initial_time, increment, 0, timeout_margin);
  } else if (TimingSettings.type == FixedTimeTimingLogic.TYPE) {
    return new FixedTimeTimingLogic(initial_time, timeout_margin);
  } else if (TimingSettings.type == HourglassTimingLogic.TYPE) {
    return new HourglassTimingLogic(initial_time, timeout_margin);
  } else if (TimingSettings.type == ByoyomiTimingLogic.TYPE) {
    return new ByoyomiTimingLogic(
      initial_time,
      byoyomi_periods,
      byoyomi_period_length,
      timeout_margin,
    );
  } else if (TimingSettings.type == SimpleDelayTimingLogic.TYPE) {
    return new SimpleDelayTimingLogic(initial_time, delay_time, timeout_margin);
  } else if (TimingSettings.type == BronsteinTimingLogic.TYPE) {
    return new BronsteinTimingLogic(initial_time, increment, timeout_margin);
  } else {
    throw Error(`Invalid timer type: ${TimingSettings.type}`);
  }
}
