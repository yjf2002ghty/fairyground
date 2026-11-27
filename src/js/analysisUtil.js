export function EvaluationToString(eval_num, is_mate) {
  if (is_mate) {
    return `#${eval_num > 0 ? "+" : ""}${eval_num}`;
  } else {
    return `${eval_num > 0 ? "+" : ""}${eval_num}`;
  }
}

export function GetEvaluationLevelDifference(
  eval_num_before,
  is_mate_before,
  eval_num_after,
  is_mate_after,
  is_first_mover = true,
) {
  function sigmoid(x) {
    return 11 * (2 / (1 + Math.exp(-(0.35 * x))) - 1);
  }
  let eval_before = is_mate_before
    ? 1000000 / eval_num_before
    : eval_num_before;
  let eval_after = is_mate_after ? 1000000 / eval_num_after : eval_num_after;
  if (is_first_mover) {
    return Math.floor(sigmoid(eval_after) - sigmoid(eval_before));
  } else {
    return Math.ceil(sigmoid(eval_before) - sigmoid(eval_after));
  }
}

export function GetEvaluationDescription(eval_num, is_mate) {
  const better_side = eval_num > 0 ? "First" : eval_num < 0 ? "Second" : "none";
  const score = Math.abs(eval_num);
  if (isNaN(eval_num)) {
    return "Invalid evaluation";
  }
  if (is_mate) {
    if (eval_num == 0) {
      return "The game has ended";
    } else {
      return `${better_side} mover can win in ${score} move(s)`;
    }
  } else {
    if (score < 0.2) {
      return "The position is equal";
    } else if (score < 0.4) {
      return `${better_side} mover is minimally better`;
    } else if (score < 0.8) {
      return `${better_side} mover is slightly better`;
    } else if (score < 1.5) {
      return `${better_side} mover is better`;
    } else if (score < 2.5) {
      return `${better_side} mover is clearly better`;
    } else if (score < 5) {
      return `${better_side} mover has a decisive advantage`;
    } else if (score < 10) {
      return `${better_side} mover is winning`;
    } else {
      return `${better_side} mover is clearly winning`;
    }
  }
}
