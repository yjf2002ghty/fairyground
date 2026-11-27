import * as analysisutil from "./analysisUtil.js";

//this.OnNextMoveAnalysisStartedCallback: function (eval_string: string | null, symbol_to_set: string | null, comment_text_after: string | null, best_moves: string | null, next_position_moves: string | null) -> void
export class AutomaticAnalysisHandler {
  constructor(
    TimePerMoveMilliseconds,
    InitialMover,
    MovesToAnalyze,
    AnalyzeOnMover,
    OnNextMoveAnalysisStartedCallback,
    UCIMoveToSanMoveCallback,
    OnAnalysisFinishedCallback,
  ) {
    if (
      typeof TimePerMoveMilliseconds != "number" ||
      typeof InitialMover != "string" ||
      !(MovesToAnalyze instanceof Array) ||
      typeof AnalyzeOnMover != "string" ||
      typeof OnNextMoveAnalysisStartedCallback != "function" ||
      typeof UCIMoveToSanMoveCallback != "function" ||
      typeof OnAnalysisFinishedCallback != "function"
    ) {
      throw TypeError();
    }
    this.TimePerMoveMilliseconds = TimePerMoveMilliseconds;
    this.MovesToAnalyze = MovesToAnalyze.filter(
      (value) => typeof value == "string",
    );
    this.InitialMover = InitialMover;
    this.CurrentMoveIndex = 0;
    this.PreviousEvaluation = { number: 0, is_mate: false, pv: "" };
    this.CurrentEvaluation = { number: 0, is_mate: false, pv: "" };
    this.OnNextMoveAnalysisStartedCallback = OnNextMoveAnalysisStartedCallback;
    this.UCIMoveToSanMoveCallback = UCIMoveToSanMoveCallback;
    this.OnAnalysisFinishedCallback = OnAnalysisFinishedCallback;
    this.Timer = null;
    this.AnalyzeOnMover = AnalyzeOnMover;
    this.AnnotateBestMoves = false;
    this._OnSingleMoveAnalysisFinished =
      this.OnSingleMoveAnalysisFinished.bind(this);
    this.StartTimeDelay = 100;
    this.FirstMoverStatistics = {
      blunders: 0,
      mistakes: 0,
      inaccuracies: 0,
      best_moves: 0,
    };
    this.SecondMoverStatistics = {
      blunders: 0,
      mistakes: 0,
      inaccuracies: 0,
      best_moves: 0,
    };
  }

  StartAnalysis() {
    this.Timer = setTimeout(
      this._OnSingleMoveAnalysisFinished,
      this.TimePerMoveMilliseconds + this.StartTimeDelay,
    );
  }

  StopAnalysis() {
    if (this.Timer) {
      clearTimeout(this.Timer);
      this.Timer = null;
    }
  }

  OnEngineEvaluationMessage(
    EvaluationNumber,
    IsMate,
    PrincipalVariationUCIMoves,
  ) {
    if (
      typeof EvaluationNumber != "number" ||
      typeof IsMate != "boolean" ||
      typeof PrincipalVariationUCIMoves != "string"
    ) {
      throw TypeError();
    }
    this.CurrentEvaluation.number = EvaluationNumber;
    this.CurrentEvaluation.is_mate = IsMate;
    this.CurrentEvaluation.pv = PrincipalVariationUCIMoves;
  }

  OnSingleMoveAnalysisFinished() {
    function text_style(type) {
      if (type == 0) {
        // Blunder
        return "[%css color: var(--disastrous-move-color); font-weight: bold; font-style: normal; border-left: 5px solid var(--disastrous-move-color); padding-left: 3px;][%mcss color: var(--disastrous-move-color);]";
      } else if (type == 1) {
        // Mistake
        return "[%css color: var(--bad-move-color); font-weight: bold; font-style: normal; border-left: 5px solid var(--bad-move-color); padding-left: 3px;][%mcss color: var(--bad-move-color);]";
      } else if (type == 2) {
        // Inaccuracy
        return "[%css color: var(--dubious-move-color); font-weight: bold; font-style: normal; border-left: 5px solid var(--dubious-move-color); padding-left: 3px;][%mcss color: var(--dubious-move-color);]";
      } else if (type == 3) {
        // Interesting
        return "[%css color: var(--interesting-move-color); font-weight: bold; font-style: normal; border-left: 5px solid var(--interesting-move-color); padding-left: 3px;][%mcss color: var(--interesting-move-color);]";
      } else if (type == 4) {
        // Good
        return "[%css color: var(--good-move-color); font-weight: bold; font-style: normal; border-left: 5px solid var(--good-move-color); padding-left: 3px;][%mcss color: var(--good-move-color);]";
      } else if (type == 5) {
        // Brilliant
        return "[%css color: var(--brilliant-move-color); font-weight: bold; font-style: normal; border-left: 5px solid var(--brilliant-move-color); padding-left: 3px;][%mcss color: var(--brilliant-move-color);]";
      } else if (type == 6) {
        // Best move
        return "[%css color: var(--best-move-color); font-weight: bold; font-style: normal; border-left: 5px solid var(--best-move-color); padding-left: 3px;][%mcss color: var(--best-move-color);]";
      } else {
        return "";
      }
    }
    // is_first_mover refers to the player to move currently, not the player made the move previously
    const is_first_mover =
      ((this.InitialMover == "white" ? 0 : 1) + this.CurrentMoveIndex) % 2 == 0;
    const annotate_previous_move =
      (this.AnalyzeOnMover == "white" && !is_first_mover) ||
      (this.AnalyzeOnMover == "black" && is_first_mover) ||
      this.AnalyzeOnMover == "both";
    const better_side_is_first_mover = this.CurrentEvaluation.number > 0;
    const previous_moves =
      this.CurrentMoveIndex == 0
        ? ""
        : this.MovesToAnalyze.slice(0, this.CurrentMoveIndex - 1).join(" ");
    const pv_best_move = this.PreviousEvaluation.pv.trim().split(" ")[0];
    const current_move =
      this.CurrentMoveIndex == 0
        ? ""
        : this.MovesToAnalyze[this.CurrentMoveIndex - 1];
    if (this.CurrentMoveIndex <= this.MovesToAnalyze.length) {
      const next_position_moves =
        this.CurrentMoveIndex < this.MovesToAnalyze.length
          ? this.MovesToAnalyze.slice(0, this.CurrentMoveIndex + 1).join(" ")
          : null;
      if (this.CurrentMoveIndex == 0 || !annotate_previous_move) {
        this.OnNextMoveAnalysisStartedCallback(
          analysisutil.EvaluationToString(
            this.CurrentEvaluation.number,
            this.CurrentEvaluation.is_mate,
          ),
          null,
          null,
          null,
          next_position_moves,
        );
      } else if (current_move == pv_best_move) {
        this.OnNextMoveAnalysisStartedCallback(
          analysisutil.EvaluationToString(
            this.CurrentEvaluation.number,
            this.CurrentEvaluation.is_mate,
          ),
          null,
          this.AnnotateBestMoves
            ? `${text_style(6)}Best move. (Same with engine's best move)`
            : null,
          null,
          next_position_moves,
        );
        if (is_first_mover) {
          this.SecondMoverStatistics.best_moves++;
        } else {
          this.FirstMoverStatistics.best_moves++;
        }
      } else {
        const level_difference = analysisutil.GetEvaluationLevelDifference(
          this.PreviousEvaluation.number,
          this.PreviousEvaluation.is_mate,
          this.CurrentEvaluation.number,
          this.CurrentEvaluation.is_mate,
          !is_first_mover,
        );
        const previous_evaluation = analysisutil.EvaluationToString(
          this.PreviousEvaluation.number,
          this.PreviousEvaluation.is_mate,
        );
        if (level_difference <= -4) {
          this.OnNextMoveAnalysisStartedCallback(
            analysisutil.EvaluationToString(
              this.CurrentEvaluation.number,
              this.CurrentEvaluation.is_mate,
            ),
            "??",
            `${text_style(0)}Blunder. ${this.UCIMoveToSanMoveCallback(pv_best_move, previous_moves)} is the best move. (Evaluation: ${previous_evaluation})`,
            this.PreviousEvaluation.pv,
            next_position_moves,
          );
          if (is_first_mover) {
            this.SecondMoverStatistics.blunders++;
          } else {
            this.FirstMoverStatistics.blunders++;
          }
        } else if (level_difference <= -2) {
          this.OnNextMoveAnalysisStartedCallback(
            analysisutil.EvaluationToString(
              this.CurrentEvaluation.number,
              this.CurrentEvaluation.is_mate,
            ),
            "?",
            `${text_style(1)}Mistake. ${this.UCIMoveToSanMoveCallback(pv_best_move, previous_moves)} is the best move. (Evaluation: ${previous_evaluation})`,
            this.PreviousEvaluation.pv,
            next_position_moves,
          );
          if (is_first_mover) {
            this.SecondMoverStatistics.mistakes++;
          } else {
            this.FirstMoverStatistics.mistakes++;
          }
        } else if (level_difference <= -1) {
          this.OnNextMoveAnalysisStartedCallback(
            analysisutil.EvaluationToString(
              this.CurrentEvaluation.number,
              this.CurrentEvaluation.is_mate,
            ),
            "?!",
            `${text_style(2)}Inaccuracy. ${this.UCIMoveToSanMoveCallback(pv_best_move, previous_moves)} is the best move. (Evaluation: ${previous_evaluation})`,
            this.PreviousEvaluation.pv,
            next_position_moves,
          );
          if (is_first_mover) {
            this.SecondMoverStatistics.inaccuracies++;
          } else {
            this.FirstMoverStatistics.inaccuracies++;
          }
        } else if (
          !this.PreviousEvaluation.is_mate &&
          this.CurrentEvaluation.is_mate &&
          better_side_is_first_mover == is_first_mover
        ) {
          this.OnNextMoveAnalysisStartedCallback(
            analysisutil.EvaluationToString(
              this.CurrentEvaluation.number,
              this.CurrentEvaluation.is_mate,
            ),
            null,
            `Checkmate is now inevitable for ${better_side_is_first_mover ? "second" : "first"} mover.`,
            null,
            next_position_moves,
          );
        } else {
          this.OnNextMoveAnalysisStartedCallback(
            analysisutil.EvaluationToString(
              this.CurrentEvaluation.number,
              this.CurrentEvaluation.is_mate,
            ),
            null,
            null,
            null,
            next_position_moves,
          );
        }
      }
      if (next_position_moves) {
        this.PreviousEvaluation.number = this.CurrentEvaluation.number;
        this.PreviousEvaluation.is_mate = this.CurrentEvaluation.is_mate;
        this.PreviousEvaluation.pv = this.CurrentEvaluation.pv;
        this.Timer = setTimeout(
          this._OnSingleMoveAnalysisFinished,
          this.TimePerMoveMilliseconds + this.StartTimeDelay,
        );
      } else {
        let comment = "";
        if (this.AnalyzeOnMover == "white" || this.AnalyzeOnMover == "both") {
          comment += "Analysis Result on First Mover:\n";
          comment += `Best moves: ${this.FirstMoverStatistics.best_moves}\n`;
          comment += `Inaccuracies: ${this.FirstMoverStatistics.inaccuracies}\n`;
          comment += `Mistakes: ${this.FirstMoverStatistics.mistakes}\n`;
          comment += `Blunders: ${this.FirstMoverStatistics.blunders}\n`;
        }
        if (this.AnalyzeOnMover == "both") {
          comment += "\n";
        }
        if (this.AnalyzeOnMover == "black" || this.AnalyzeOnMover == "both") {
          comment += "Analysis Result on Second Mover:\n";
          comment += `Best moves: ${this.SecondMoverStatistics.best_moves}\n`;
          comment += `Inaccuracies: ${this.SecondMoverStatistics.inaccuracies}\n`;
          comment += `Mistakes: ${this.SecondMoverStatistics.mistakes}\n`;
          comment += `Blunders: ${this.SecondMoverStatistics.blunders}\n`;
        }
        this.OnAnalysisFinishedCallback(comment + "\n\n");
      }
    }
    this.CurrentMoveIndex++;
  }
}
