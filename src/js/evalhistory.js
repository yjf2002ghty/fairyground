const EVAL_END = 1 / 0;
const EVAL_UNKNOWN = -1 / 0;

const POINT_TYPE_VALID = 0;
const POINT_TYPE_UNKNOWN = 1;
const POINT_TYPE_INVALID = 2;
const POINT_TYPE_END = 3;

const EPSILON = 1e-6;

export class EvaluationHistoryGraph {
  constructor(Container, OnSelectMoveCallback) {
    if (
      !(Container instanceof HTMLElement) ||
      (typeof OnSelectMoveCallback != "function" &&
        typeof OnSelectMoveCallback != "undefined")
    ) {
      throw TypeError();
    }
    const container_style = window.getComputedStyle(Container);
    this.PI2 = 2 * Math.PI;
    this.Container = Container;
    this.Padding = 5;
    this.PointSize = 4;
    this.LineWidth = this.PointSize / 2;
    this.MinHorizonalPointToPointDistance = 2.5 * this.PointSize;
    this.MinPointCount = 20;
    this.MaxEvaluationScore = 10;
    this.MinEvaluationScore = -10;
    this.EvaluationScores = [];
    this.SANMoves = [];
    this.OriginalEvaluationStrings = [];
    this.Canvas = document.createElement("canvas");
    this.Canvas.classList.add("eval-history-canvas");
    this.CanvasContext = this.Canvas.getContext("2d");
    this.PointsContainer = document.createElement("div");
    this.PointsContainer.classList.add("eval-history-point-container");
    this.DescriptionElement = document.createElement("pre");
    this.DescriptionElement.classList.add("eval-history-description");
    this.DescriptionElement.classList.add("inaccessable");
    this.DescriptionElement.style.opacity = "0";
    this.PointsContainer.appendChild(this.DescriptionElement);
    this.PointElements = [];
    this.CurrentIndex = 0;
    this.XOffset = 0;
    this.Canvas.width = this.Width = parseFloat(container_style.width);
    this.Canvas.height = this.Height = parseFloat(container_style.height);
    this.OnResizeCallback = this.OnResize.bind(this);
    this.HideDescriptionCallback = this.HideDescription.bind(this);
    this.OnSelectMoveCallback = OnSelectMoveCallback;
    this.PreviousClickPosX = 0;
    this.PreviousXOffset = 0;
    this.__Draw = this.Draw.bind(this);
    this.DragHandler = (event) => {
      this.XOffset =
        this.PreviousXOffset + (this.PreviousClickPosX - event.clientX);
      if (this.XOffset < 0) {
        this.XOffset = 0;
      }
      requestAnimationFrame(this.__Draw);
    };
    Container.appendChild(this.Canvas);
    Container.appendChild(this.PointsContainer);
    document.addEventListener("click", this.HideDescriptionCallback);
    window.addEventListener("resize", this.OnResizeCallback);
    Container.addEventListener("contextmenu", (event) => {
      event.preventDefault();
      this.XOffset = 0;
      this.Draw();
    });
    Container.addEventListener("mousedown", (event) => {
      if (event.target.closest(".eval-history-point")) {
        return;
      }
      this.PreviousXOffset = this.XOffset;
      this.PreviousClickPosX = event.clientX;
      Container.addEventListener("mousemove", this.DragHandler);
    });
    Container.addEventListener("mouseup", () => {
      Container.removeEventListener("mousemove", this.DragHandler);
    });
    Container.addEventListener("redraw", this.__Draw);
  }

  destructor() {
    window.removeEventListener("resize", this.OnResizeCallback);
    document.addEventListener("click", this.HideDescriptionCallback);
  }

  OnResize() {
    this.Draw();
  }

  SetScoreRange(MaxEvaluationScore, MinEvaluationScore) {
    if (
      typeof MaxEvaluationScore != "number" ||
      typeof MinEvaluationScore != "number"
    ) {
      throw TypeError();
    }
    this.MaxEvaluationScore = MaxEvaluationScore;
    this.MinEvaluationScore = MinEvaluationScore;
  }

  SetEvaluationHistory(EvaluationScoreHistory, SANMoveHistory) {
    if (
      !(EvaluationScoreHistory instanceof Array) ||
      !(SANMoveHistory instanceof Array)
    ) {
      throw TypeError();
    }
    this.EvaluationScores = [];
    const san_moves = SANMoveHistory.filter((val) => typeof val == "string");
    const evaluation_scores = EvaluationScoreHistory.filter(
      (val) => typeof val == "string",
    );
    if (san_moves.length != evaluation_scores.length) {
      console.warn(
        "Move history length and evaluation history length do not match.",
      );
      console.warn(EvaluationScoreHistory, SANMoveHistory);
    }
    this.SANMoves = san_moves;
    this.OriginalEvaluationStrings = evaluation_scores;
    let i = 0;
    let value = "";
    for (i = 0; i < evaluation_scores.length; i++) {
      value = evaluation_scores[i];
      if (value.startsWith("#-")) {
        this.EvaluationScores.push(this.MinEvaluationScore);
      } else if (value.startsWith("#+")) {
        this.EvaluationScores.push(this.MaxEvaluationScore);
      } else if (value == "#0") {
        this.EvaluationScores.push(EVAL_END);
      } else if (value == "") {
        this.EvaluationScores.push(EVAL_UNKNOWN);
      } else {
        this.EvaluationScores.push(parseFloat(value));
      }
    }
  }

  SetCurrentIndex(Index) {
    if (typeof Index != "number") {
      throw TypeError();
    }
    this.CurrentIndex = Index;
  }

  ShowDescription(Description, X, Y) {
    if (
      typeof Description != "string" ||
      typeof X != "number" ||
      typeof Y != "number"
    ) {
      throw TypeError();
    }
    this.DescriptionElement.style.opacity = "1";
    this.DescriptionElement.textContent = Description;
    const style = window.getComputedStyle(this.DescriptionElement);
    this.DescriptionElement.style.left = `${X - parseFloat(style.width) / 2}px`;
    this.DescriptionElement.style.top = `${Y + 4 * this.PointSize}px`;
  }

  HideDescription(event) {
    if (event instanceof PointerEvent) {
      if (event.isTrusted) {
        this.DescriptionElement.style.opacity = "0";
      }
    }
  }

  Draw() {
    const container_style = window.getComputedStyle(this.Container);
    this.Canvas.width = this.Width = parseFloat(container_style.width);
    this.Canvas.height = this.Height = parseFloat(container_style.height);
    this.CanvasContext.clearRect(0, 0, this.Width, this.Height);
    this.DescriptionElement.style.opacity = "0";
    const root_style = window.getComputedStyle(document.querySelector(":root"));
    const point_positions = [];
    const point_types = [];
    const point_pitch = Math.max(
      (this.Width - 2 * this.Padding) /
        (Math.max(this.MinPointCount, this.EvaluationScores.length) - 1),
      this.MinHorizonalPointToPointDistance,
    );
    const resize_factor =
      (this.Height - 2 * this.Padding) /
      (this.MaxEvaluationScore - this.MinEvaluationScore);
    const zero_y = this.MaxEvaluationScore * resize_factor + this.Padding;
    const color = root_style.getPropertyValue("--accent");
    const bad_color = root_style.getPropertyValue("--bad");
    const grid_color = root_style.getPropertyValue("--border2");
    const grid_pitch = (this.Height - 2 * this.Padding) / 4;
    const min_x = this.Padding - EPSILON;
    const max_x = this.Width - this.Padding + EPSILON;
    let i = 0;
    let offset_x = this.Padding - this.XOffset;
    let score = 0;
    let offset_y = 0;
    let eval_str = "";
    let point_type = 0;
    let elem;
    let current_x = 0;

    // Draw the grid
    this.CanvasContext.setLineDash([]);
    // Zero evaluation score line
    this.CanvasContext.beginPath();
    this.CanvasContext.strokeStyle = grid_color;
    this.CanvasContext.lineWidth = this.PointSize / 2;
    this.CanvasContext.setLineDash([]);
    this.CanvasContext.moveTo(this.Padding, zero_y);
    this.CanvasContext.lineTo(this.Width, zero_y);
    this.CanvasContext.stroke();
    // Left border
    this.CanvasContext.beginPath();
    this.CanvasContext.strokeStyle = grid_color;
    this.CanvasContext.lineWidth = this.PointSize / 2;
    this.CanvasContext.moveTo(this.Padding, this.Padding);
    this.CanvasContext.lineTo(this.Padding, this.Height - this.Padding);
    this.CanvasContext.stroke();
    // 5 evaluation lines on graph
    this.CanvasContext.setLineDash([5, 15]);
    for (i = 0; i < 5; i++) {
      this.CanvasContext.beginPath();
      this.CanvasContext.strokeStyle = grid_color;
      this.CanvasContext.lineWidth = this.PointSize / 4;
      this.CanvasContext.moveTo(this.Padding, this.Padding + i * grid_pitch);
      this.CanvasContext.lineTo(this.Width, this.Padding + i * grid_pitch);
      this.CanvasContext.stroke();
    }

    // Calculate point positions on canvas
    for (i = 0; i < this.EvaluationScores.length; i++) {
      score = this.EvaluationScores[i];
      if (score == EVAL_UNKNOWN) {
        point_positions.push({ x: offset_x, y: zero_y });
        point_types.push(POINT_TYPE_UNKNOWN);
      } else if (isNaN(score)) {
        point_positions.push({ x: offset_x, y: zero_y });
        point_types.push(POINT_TYPE_INVALID);
      } else if (score == EVAL_END) {
        point_positions.push({ x: offset_x, y: zero_y });
        point_types.push(POINT_TYPE_END);
      } else {
        offset_y =
          (this.MaxEvaluationScore - score) * resize_factor + this.Padding;
        if (offset_y < this.Padding) {
          offset_y = this.Padding;
        } else if (offset_y > this.Height - this.Padding) {
          offset_y = this.Height - this.Padding;
        }
        point_positions.push({ x: offset_x, y: offset_y });
        point_types.push(POINT_TYPE_VALID);
      }
      offset_x += point_pitch;
    }

    // Create more click event handler if not enough
    while (this.PointElements.length < point_positions.length) {
      elem = document.createElement("div");
      elem.classList.add("eval-history-point");
      elem.style.width = elem.style.height = `${this.PointSize * 2}px`;
      elem.style.borderRadius = `${this.PointSize}px`;
      elem.hidden = false;
      this.PointElements.push(elem);
      this.PointsContainer.appendChild(elem);
    }

    // Draw the line graph
    this.CanvasContext.setLineDash([]);
    for (i = 0; i < point_positions.length; i++) {
      point_type = point_types[i];
      current_x = point_positions[i].x;
      if (current_x > min_x && current_x < max_x) {
        this.CanvasContext.beginPath();
        this.CanvasContext.arc(
          current_x,
          point_positions[i].y,
          this.PointSize,
          0,
          this.PI2,
        );
        this.CanvasContext.fillStyle =
          point_type == POINT_TYPE_VALID ? color : bad_color;
        this.CanvasContext.fill();
        this.CanvasContext.closePath();
      }
      if (
        i > 0 &&
        point_type == POINT_TYPE_VALID &&
        point_types[i - 1] == POINT_TYPE_VALID
      ) {
        if (
          (current_x > min_x && current_x < max_x) ||
          (point_positions[i - 1].x > min_x && point_positions[i - 1].x < max_x)
        ) {
          this.CanvasContext.beginPath();
          this.CanvasContext.strokeStyle = color;
          this.CanvasContext.lineWidth = this.LineWidth;
          this.CanvasContext.moveTo(
            point_positions[i - 1].x,
            point_positions[i - 1].y,
          );
          this.CanvasContext.lineTo(current_x, point_positions[i].y);
          this.CanvasContext.stroke();
        }
      }
      if (point_type == POINT_TYPE_VALID || point_type == POINT_TYPE_END) {
        eval_str = this.OriginalEvaluationStrings[i];
      } else if (point_type == POINT_TYPE_UNKNOWN) {
        eval_str = "(not set)";
      } else if (point_type == POINT_TYPE_INVALID) {
        eval_str = "(invalid evaluation)";
      } else {
        eval_str = "Error: Bad point type";
      }
      elem = this.PointElements[i];
      if (elem instanceof HTMLElement) {
        const X = current_x;
        const Y = point_positions[i].y;
        const move = this.SANMoves[i];
        const eval_description = eval_str;
        let current_index = i;
        elem.style.left = `${X - this.PointSize}px`;
        elem.style.top = `${Y - this.PointSize}px`;
        elem.hidden = current_x <= min_x || current_x >= max_x;
        elem.onclick = (event) => {
          event.stopPropagation();
          event.preventDefault();
          this.ShowDescription(
            `${move || "Initial position"}\nEvaluation: ${eval_description}`,
            X,
            Y,
          );
        };
        elem.oncontextmenu = (event) => {
          event.stopPropagation();
          event.preventDefault();
          if (this.OnSelectMoveCallback) {
            this.OnSelectMoveCallback(current_index);
          }
        };
      }
      if (i == this.CurrentIndex && current_x > min_x && current_x < max_x) {
        this.CanvasContext.beginPath();
        this.CanvasContext.strokeStyle = `rgba(128,128,128,0.5)`;
        this.CanvasContext.lineWidth = this.PointSize * 2;
        this.CanvasContext.moveTo(current_x, 0);
        this.CanvasContext.lineTo(current_x, this.Height);
        this.CanvasContext.stroke();
      }
    }

    // Hide unused elements
    for (i = point_positions.length; i < this.PointElements.length; i++) {
      this.PointElements[i].hidden = true;
    }
  }
}
