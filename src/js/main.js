// ffish.js test using chessgroundx
const Chessground = require("chessgroundx").Chessground;
const ZIP = require("jszip");
const m = require("mithril");
import * as util from "chessgroundx/util";
import * as pocketutil from "chessgroundx/pocket";
import * as moveutil from "./move.js";
import * as pgnutil from "./pgn.js";
import * as imageutil from "./image.js";
import * as themeutil from "./chessgroundtheme.js";
import * as myvariants from "./myVariants.js";
import * as evalhistory from "./evalhistory.js";
import * as boardpeek from "./boardInMoveListPanel.js";
import * as fge from "./binaryEngine.js";
import * as fgs from "./savedGames.js";

// From <script src="./lib/stockfish.js"></script> in index.html
if (typeof window.FairyStockfish == "undefined") {
  window.alert("Cannot load fairy stockfish!");
  throw Error("Cannot load fairy stockfish!");
}
const FairyStockfish = window.FairyStockfish;
window.m = m;

// Constants and variables previously in main.js

const files = [
  "a",
  "b",
  "c",
  "d",
  "e",
  "f",
  "g",
  "h",
  "i",
  "j",
  "k",
  "l",
  "m",
  "n",
  "o",
  "p",
  "q",
  "r",
  "s",
  "t",
  "u",
  "v",
  "w",
  "x",
  "y",
  "z",
];
const pieces = [
  "a",
  "b",
  "c",
  "d",
  "e",
  "f",
  "g",
  "h",
  "i",
  "j",
  "k",
  "l",
  "m",
  "n",
  "o",
  "p",
  "q",
  "r",
  "s",
  "t",
  "u",
  "v",
  "w",
  "x",
  "y",
  "z",
  "+a",
  "+b",
  "+c",
  "+d",
  "+e",
  "+f",
  "+g",
  "+h",
  "+i",
  "+j",
  "+k",
  "+l",
  "+m",
  "+n",
  "+o",
  "+p",
  "+q",
  "+r",
  "+s",
  "+t",
  "+u",
  "+v",
  "+w",
  "+x",
  "+y",
  "+z",
  "A",
  "B",
  "C",
  "D",
  "E",
  "F",
  "G",
  "H",
  "I",
  "J",
  "K",
  "L",
  "M",
  "N",
  "O",
  "P",
  "Q",
  "R",
  "S",
  "T",
  "U",
  "V",
  "W",
  "X",
  "Y",
  "Z",
  "+A",
  "+B",
  "+C",
  "+D",
  "+E",
  "+F",
  "+G",
  "+H",
  "+I",
  "+J",
  "+K",
  "+L",
  "+M",
  "+N",
  "+O",
  "+P",
  "+Q",
  "+R",
  "+S",
  "+T",
  "+U",
  "+V",
  "+W",
  "+X",
  "+Y",
  "+Z",
  "*",
];
const simplenotations = [
  "DEFAULT",
  "SAN",
  "LAN",
  "SHOGI_HOSKING",
  "SHOGI_HODGES",
  "SHOGI_HODGES_NUMBER",
  "JANGGI",
  "XIANGQI_WXF",
  "THAI_SAN",
  "THAI_LAN",
];
const chessgroundnotations = [
  "ALGEBRAIC", // English letters on bottom, Arabic numbers on side
  "SHOGI_ENGLET", // Arabic numbers on top, English letters on side
  "SHOGI_ARBNUM", // Arabic numbers on top and side
  "SHOGI_HANNUM", // Arabic numbers on top, Kanji numbers on side
  "JANGGI", // Arabic numbers on bottom and side, with 0 denoting 10th rank
  "XIANGQI_ARBNUM", // Arabic numbers on top and bottom
  "XIANGQI_HANNUM", // Arabic numbers on top, Hanzi numbers on bottom
  "THAI_ALGEBRAIC", // Thai letters on bottom, Thai numbers on side
];
const MoveTextActionPartsMatcher = new RegExp("\\[.*?\\]", "g");
const CompleteBlankStringMatcher = new RegExp("^\\s*$", "");
const MoveNumberMatcher = new RegExp("\\d+\\.+", "g");
const CurlyBracketsMatcher = new RegExp("\\{|\\}", "g");
const SpaceSplitterMatcher = new RegExp("[ ]+", "");
const SpaceReplacer = new RegExp("[ ]+", "g");
const GameResults = ["1-0", "0-1", "1/2-1/2", "*"];
const GameTerminations = [
  "undefined",
  "abandoned",
  "adjudication",
  "death",
  "emergency",
  "normal",
  "rules infraction",
  "time forfeit",
  "unterminated",
  "unknown",
  "normal",
];
const FriendlyGameTerminationNames = [
  "(Not set)",
  "Game abandoned",
  "Ended by adjudication",
  "Player death",
  "Emergency condition happened",
  "Player resigned or agreed draw",
  "Rules infraction",
  "Player run out of time",
  "Ongoing, not terminated",
  "Reason not specified",
  "Ended by game rule",
];

let ffishnotationobjects = null;
var PositionVariantsDirectory = new Map();
// Read access for the UI (variant picker): Map<positiontype, Map<name, game>>
window.fairyground.GetPositionVariants = function (variant) {
  return PositionVariantsDirectory.get(variant);
};
// Used by the variant editor of the UI.
window.fairyground.MyVariants = myvariants;
let EmptyMap = new Map();
let ffish = null;
let board = null;
let chessground = null;
let chessground_mini = null;
const PgnDivThrottleDurationMs = 100;
let PgnDivThrottleStartTime = 0;
let PgnDivCalledDuringThrottle = false;
var i = 0;
const WHITE = true;
const BLACK = false;
var evaluation = 0.0;
var multipvrecord = [];
var evaluationindex = [];
const mateevalfactor = 2147483647;
const maxmultipvcount = 4096;
var recordedmultipv = 1;
var previousclicktime = Date.now();
var hasdoubleclicked = false;
var previousclicksquare = "00";
var multipvminiboardtimer = null;
// Gating (e.g., duck move) click selection state
var gatingPending = false;
var gatingContext = null;
// Open promotion/gating choice on the board, see showPromotionChoice()
var promotionChoice = null;
// Timer event correction after popup dialogs
var timerElapsePreviousPlayer = false;
// Spacebar best-move globals
var lastPVPosSig = "";
var lastPVBestMove = ""; // Also used by buttonAnalyzeRecommendedMove
var lastPVTime = 0;
var spacebarDebounce = false;

class GameTree {
  constructor() {
    this.MoveTree = new moveutil.MoveTree();
    this.OriginalFEN = "";
    this.Variant = "chess";
    this.Is960 = false;
    this.BlankSplitter = new RegExp("[ ]+");
    this.CurrentMove = this.MoveTree.RootNode;
    this.HistoryStack = [];
    this.CurrentHistory = -1;
    this.GameHeaders = new Map();
  }

  destructor() {}

  AddHistory() {
    if (this.CurrentHistory < this.HistoryStack.length - 1) {
      this.HistoryStack.splice(this.CurrentHistory + 1);
    }
    this.HistoryStack.push({
      fen: this.OriginalFEN,
      movetree: this.MoveTree.ToString(),
      moves: this.GetMoveListOfMove(this.CurrentMove),
      rootnodetext: this.MoveTree.RootNode.Move.TextAfter,
    });
    this.CurrentHistory = this.HistoryStack.length - 1;
  }

  UpdateHistory() {
    if (this.CurrentHistory < 0) {
      this.HistoryStack = [
        {
          fen: this.OriginalFEN,
          movetree: this.MoveTree.ToString(),
          moves: this.GetMoveListOfMove(this.CurrentMove),
          rootnodetext: this.MoveTree.RootNode.Move.TextAfter,
        },
      ];
      this.CurrentHistory = 0;
    } else {
      this.HistoryStack[this.CurrentHistory] = {
        fen: this.OriginalFEN,
        movetree: this.MoveTree.ToString(),
        moves: this.GetMoveListOfMove(this.CurrentMove),
        rootnodetext: this.MoveTree.RootNode.Move.TextAfter,
      };
    }
  }

  ClearHistory() {
    console.log("clear history");
    this.HistoryStack = [];
    this.CurrentHistory = -1;
  }

  Undo() {
    if (this.CurrentHistory > 0) {
      this.CurrentHistory--;
      this.OriginalFEN = this.HistoryStack[this.CurrentHistory].fen;
      this.MoveTree.FromString(this.HistoryStack[this.CurrentHistory].movetree);
      this.MoveTree.RootNode.Move.TextAfter =
        this.HistoryStack[this.CurrentHistory].rootnodetext;
      this.GoToMoveList(this.HistoryStack[this.CurrentHistory].moves);
      return true;
    }
    return false;
  }

  Redo() {
    if (this.CurrentHistory < this.HistoryStack.length - 1) {
      this.CurrentHistory++;
      this.OriginalFEN = this.HistoryStack[this.CurrentHistory].fen;
      this.MoveTree.FromString(this.HistoryStack[this.CurrentHistory].movetree);
      this.MoveTree.RootNode.Move.TextAfter =
        this.HistoryStack[this.CurrentHistory].rootnodetext;
      this.GoToMoveList(this.HistoryStack[this.CurrentHistory].moves);
      return true;
    }
    return false;
  }

  GoToMoveList(MoveList) {
    if (typeof MoveList != "string") {
      throw TypeError();
    }
    const trimmedmoves = MoveList.trim();
    let node_id = -1;
    let i = 0,
      j = 0;
    let pointer = this.MoveTree.RootNode;
    let movelist = trimmedmoves.split(this.BlankSplitter);
    if (trimmedmoves.length == 0) {
      this.CurrentMove = this.MoveTree.RootNode;
      return;
    }
    for (i = 0; i < movelist.length; i++) {
      node_id = -1;
      for (j = 0; j < pointer.NextNodes.length; j++) {
        if (pointer.NextNodes[j].Move.Move == movelist[i]) {
          node_id = j;
          break;
        }
      }
      if (node_id >= 0) {
        pointer = pointer.NextNodes[node_id];
      } else {
        break;
      }
    }
    this.CurrentMove = pointer;
  }

  SetCurrentMoveList(Variant, Is960, FEN, MoveList) {
    if (
      typeof Variant != "string" ||
      typeof Is960 != "boolean" ||
      typeof FEN != "string" ||
      typeof MoveList != "string"
    ) {
      throw TypeError();
    }
    const trimmedmoves = MoveList.trim();
    let movelist = trimmedmoves.split(this.BlankSplitter);
    let i = 0,
      j = 0;
    let node_id = -1;
    let pointer = this.MoveTree.RootNode;
    let variant = Variant == "" ? "chess" : Variant;
    let fen = FEN == "" ? ffish.startingFen(variant) : FEN;
    if (
      fen != this.OriginalFEN ||
      variant != this.Variant ||
      Is960 != this.Is960
    ) {
      this.MoveTree.RootNode.NextNodes = [];
      this.MoveTree.RootNode.Move.TextAfter = "";
      this.OriginalFEN = fen;
      this.Variant = variant;
      this.Is960 = Is960;
      this.ClearHistory();
    }
    if (trimmedmoves.length == 0) {
      this.CurrentMove = this.MoveTree.RootNode;
      return;
    }
    for (i = 0; i < movelist.length; i++) {
      node_id = -1;
      for (j = 0; j < pointer.NextNodes.length; j++) {
        if (pointer.NextNodes[j].Move.Move == movelist[i]) {
          node_id = j;
          break;
        }
      }
      if (node_id == -1) {
        for (j = i; j < movelist.length; j++) {
          pointer.AddVariationNode(
            new moveutil.MoveTreeNode(
              new moveutil.Move(movelist[j], 0, 0),
              undefined,
              [],
            ),
          );
          pointer = pointer.NextNodes[pointer.NextNodes.length - 1];
        }
        this.ClearHistory();
        break;
      } else {
        pointer = pointer.NextNodes[node_id];
      }
    }
    this.CurrentMove = pointer;
  }

  GetMoveListOfMove(MoveNode) {
    if (!(MoveNode instanceof moveutil.MoveTreeNode)) {
      throw TypeError();
    }
    let pointer = MoveNode;
    let moves = [];
    while (pointer != this.MoveTree.RootNode) {
      moves.push(pointer.Move.Move);
      pointer = pointer.PreviousNode;
    }
    return moves.reverse().join(" ");
  }

  GetCompleteMainLineMoveListOfMove(MoveNode) {
    if (!(MoveNode instanceof moveutil.MoveTreeNode)) {
      throw TypeError();
    }
    let pointer = MoveNode;
    let moves = [];
    while (pointer != this.MoveTree.RootNode) {
      if (pointer == null) {
        return null;
      }
      moves.push(pointer.Move.Move);
      pointer = pointer.PreviousNode;
    }
    moves.reverse();
    pointer = MoveNode;
    while (pointer.NextNodes[0]) {
      pointer = pointer.NextNodes[0];
      moves.push(pointer.Move.Move);
    }
    return moves.join(" ");
  }

  GetMainLineMoveList() {
    let moves = [];
    let pointer = this.MoveTree.RootNode;
    while (pointer.NextNodes[0]) {
      pointer = pointer.NextNodes[0];
      moves.push(pointer.Move.Move);
    }
    return moves.join(" ");
  }

  ClearMoves() {
    this.UpdateHistory();
    this.MoveTree.RootNode.NextNodes = [];
    this.CurrentMove = this.MoveTree.RootNode;
    this.MoveTree.RootNode.Move.TextAfter = "";
    this.MoveTree.RootNode.Move.TextBefore = "";
    this.MoveTree.RootNode.Move.Symbol = [];
    this.AddHistory();
  }

  ClearComments() {
    let pointer = this.MoveTree.RootNode;
    let stack = [];
    let i = 0;
    this.UpdateHistory();
    while (true) {
      if (i < pointer.NextNodes.length) {
        stack.push(i);
        pointer = pointer.NextNodes[i];
        i = 0;
      } else {
        pointer.Move.TextAfter = "";
        pointer.Move.TextBefore = "";
        pointer.Move.Symbol = [];
        if (stack.length == 0) {
          break;
        }
        i = stack.pop() + 1;
        pointer = pointer.PreviousNode;
      }
    }
    this.AddHistory();
  }

  SetCurrentMoveToMainBranch() {
    if (
      this.CurrentMove != this.MoveTree.RootNode ||
      this.CurrentMove.RelativePositionInParentNode > 0
    ) {
      this.UpdateHistory();
      this.CurrentMove.ParentNode().SetVariationNodeToMainNode(
        this.CurrentMove.RelativePositionInParentNode,
      );
      this.AddHistory();
    }
  }

  SetCurrentMoveBranchAsMainLine() {
    if (this.CurrentMove != this.MoveTree.RootNode) {
      let pointer = this.CurrentMove;
      this.UpdateHistory();
      while (pointer.PreviousNode) {
        pointer
          .ParentNode()
          .SetVariationNodeToMainNode(pointer.RelativePositionInParentNode);
        pointer = pointer.PreviousNode;
      }
      this.AddHistory();
    }
  }

  RemoveCurrentMoveBranch() {
    let pointer = this.CurrentMove;
    this.UpdateHistory();
    while (pointer.PreviousNode) {
      if (pointer.RelativePositionInParentNode != 0) {
        break;
      }
      pointer = pointer.PreviousNode;
    }
    if (pointer == this.MoveTree.RootNode) {
      this.MoveTree.RootNode.NextNodes = [];
      this.CurrentMove = this.MoveTree.RootNode;
    } else {
      pointer.ParentNode().RemoveNode(pointer.RelativePositionInParentNode);
      this.CurrentMove = pointer.PreviousNode;
    }
    this.AddHistory();
  }

  RemoveNonCurrentMoveBranch() {
    let pointer = this.CurrentMove;
    this.UpdateHistory();
    while (pointer.PreviousNode) {
      pointer.ParentNode().NextNodes = [pointer];
      pointer.RelativePositionInParentNode = 0;
      pointer = pointer.PreviousNode;
    }
    this.AddHistory();
  }

  CutCurrentMove() {
    this.UpdateHistory();
    if (this.CurrentMove == this.MoveTree.RootNode) {
      this.MoveTree.RootNode.NextNodes = [];
      this.CurrentMove = this.MoveTree.RootNode;
    } else {
      this.CurrentMove.ParentNode().RemoveNode(
        this.CurrentMove.RelativePositionInParentNode,
      );
      this.CurrentMove = this.CurrentMove.PreviousNode;
    }
    this.AddHistory();
  }

  CropCurrentMove() {
    if (this.CurrentMove == this.MoveTree.RootNode) {
      return;
    }
    let moves = [];
    let pointer = this.CurrentMove.ParentNode();
    let tmpboard = new ffish.Board(this.Variant, this.OriginalFEN, this.Is960);
    this.UpdateHistory();
    this.MoveTree.RootNode.Move.TextAfter = pointer.Move.TextAfter;
    while (pointer != this.MoveTree.RootNode) {
      moves.push(pointer.Move.Move);
      pointer = pointer.PreviousNode;
    }
    if (moves.length > 0) {
      tmpboard.pushMoves(moves.reverse().join(" "));
    }
    this.OriginalFEN = tmpboard.fen();
    this.MoveTree.RootNode.NextNodes = [this.CurrentMove];
    this.CurrentMove.PreviousNode = this.MoveTree.RootNode;
    this.CurrentMove.RelativePositionInParentNode = 0;
    this.AddHistory();
    tmpboard.delete();
  }

  RemoveVariationsOfCurrentMove() {
    if (this.CurrentMove.NextNodes.length > 1) {
      this.UpdateHistory();
      this.CurrentMove.NextNodes = [this.CurrentMove.NextNodes[0]];
      this.AddHistory();
    }
  }

  ShowOrHideCurrentMove() {
    if (this.CurrentMove == this.MoveTree.RootNode) {
      return;
    }
    this.UpdateHistory();
    this.CurrentMove.Move.HideSubsequentMoves =
      !this.CurrentMove.Move.HideSubsequentMoves;
    this.AddHistory();
  }

  UncommentCurrentMove() {
    this.UpdateHistory();
    this.CurrentMove.Move.TextAfter = "";
    this.CurrentMove.Move.TextBefore = "";
    this.CurrentMove.Move.Symbol = [];
    this.AddHistory();
  }

  SetTextBeforeOfCurrentMove(TextBefore) {
    if (typeof TextBefore != "string") {
      throw TypeError();
    }
    if (this.CurrentMove == this.MoveTree.RootNode) {
      return;
    }
    this.UpdateHistory();
    this.CurrentMove.Move.TextBefore = TextBefore.replace(
      CurlyBracketsMatcher,
      "",
    );
    this.AddHistory();
  }

  SetTextAfterOfCurrentMove(TextAfter) {
    if (typeof TextAfter != "string") {
      throw TypeError();
    }
    this.UpdateHistory();
    this.CurrentMove.Move.TextAfter = TextAfter.replace(
      CurlyBracketsMatcher,
      "",
    );
    this.AddHistory();
  }

  SetSymbolsOfCurrentMove(MoveSymbols) {
    if (!(MoveSymbols instanceof Array)) {
      throw TypeError();
    }
    if (this.CurrentMove == this.MoveTree.RootNode) {
      return;
    }
    let result = [];
    let i = 0;
    let index = 0;
    this.UpdateHistory();
    for (i = 0; i < MoveSymbols.length; i++) {
      index = moveutil.NumericAnnotationGlyphs.indexOf(MoveSymbols[i]);
      if (index > 0) {
        result.push(`$${index}`);
      }
    }
    this.CurrentMove.Move.Symbol = result;
    this.AddHistory();
  }

  SetHeaders(GameEvent, Site, GameDate, Round, WhiteName, BlackName) {
    if (
      typeof GameEvent != "string" ||
      typeof Site != "string" ||
      !(GameDate instanceof Date) ||
      typeof Round != "number" ||
      typeof WhiteName != "string" ||
      typeof BlackName != "string"
    ) {
      throw TypeError();
    }
    this.GameHeaders.set("Event", GameEvent);
    this.GameHeaders.set("Site", Site);
    this.GameHeaders.set("Round", Round > 0 ? String(Round) : "1");
    this.GameHeaders.set(
      "Date",
      `${GameDate.getFullYear()}.${GameDate.getMonth() + 1}.${GameDate.getDate()}`,
    );
    this.GameHeaders.set("White", WhiteName);
    this.GameHeaders.set("Black", BlackName);
  }

  GetHeaderString(FallbackWhiteName, FallbackBlackName) {
    if (
      typeof FallbackWhiteName != "string" ||
      typeof FallbackBlackName != "string"
    ) {
      throw TypeError();
    }
    let result = [];
    let termination = "";
    let tmpboard = new ffish.Board(this.Variant, this.OriginalFEN, this.Is960);
    let tmpboardresult;
    const today = new Date();
    tmpboard.pushMoves(this.GetMainLineMoveList());
    tmpboardresult = getBoardResult(tmpboard);
    if (tmpboardresult == "*") {
      let pointer = this.MoveTree.RootNode;
      let index = 0,
        indexend = 0;
      let terminationstr;
      while (pointer.NextNodes[0]) {
        pointer = pointer.NextNodes[0];
      }
      index = pointer.Move.TextAfter.indexOf("[%end ");
      if (index >= 0) {
        indexend = pointer.Move.TextAfter.indexOf("]", index + 6);
        if (indexend >= 0) {
          terminationstr = pointer.Move.TextAfter.substring(
            index + 6,
            indexend,
          ).split(",");
          if (
            GameResults.includes(terminationstr[0]) &&
            GameTerminations.includes(terminationstr[1])
          ) {
            tmpboardresult = terminationstr[0];
            termination = terminationstr[1];
          }
        }
      }
    } else {
      termination = "normal";
    }
    result.push(
      `[Event "${this.GameHeaders.get("Event") || "Fairy-Stockfish playground game"}"]`,
    );
    result.push(
      `[Site "${this.GameHeaders.get("Site") || window.location.host}"]`,
    );
    result.push(`[Round "${this.GameHeaders.get("Round") || "1"}"]`);
    result.push(
      `[Date "${this.GameHeaders.get("Date") || String(today.getFullYear()) + "." + String(today.getMonth() + 1) + "." + String(today.getDate())}"]`,
    );
    result.push(
      `[White "${this.GameHeaders.get("White") || FallbackWhiteName}"]`,
    );
    result.push(
      `[Black "${this.GameHeaders.get("Black") || FallbackBlackName}"]`,
    );
    result.push(`[Result "${tmpboardresult}"]`);
    result.push(`[FEN "${this.OriginalFEN}"]\n[SetUp "1"]`);
    result.push(
      `[Variant "${this.Is960 ? this.Variant + "960" : this.Variant}"]`,
    );
    if (termination != "") {
      result.push(`[Termination "${termination}"]`);
    }
    tmpboard.delete();
    return result.join("\n");
  }

  ForEachMove(Callback) {
    if (typeof Callback != "function") {
      throw TypeError();
    }
    let pointer = this.MoveTree.RootNode;
    let stack = [];
    let i = 0;
    while (true) {
      if (i < pointer.NextNodes.length) {
        stack.push(i);
        pointer = pointer.NextNodes[i];
        i = 0;
      } else {
        Callback(pointer.Move, pointer, stack.slice());
        if (stack.length == 0) {
          break;
        }
        i = stack.pop() + 1;
        pointer = pointer.PreviousNode;
      }
    }
  }

  ForEachMoveUntilMove(MoveNode, Callback) {
    if (
      !(MoveNode instanceof moveutil.MoveTreeNode) ||
      typeof Callback != "function"
    ) {
      throw TypeError();
    }
    let pointer = MoveNode;
    let moves = [];
    let i = 0;
    while (pointer.PreviousNode) {
      moves.push(pointer);
      pointer = pointer.PreviousNode;
    }
    moves.push(this.MoveTree.RootNode);
    moves.reverse();
    for (i = 0; i < moves.length; i++) {
      Callback(moves[i].Move, moves[i]);
    }
  }

  ForEachMoveOnBranchOfMove(MoveNode, Callback) {
    if (
      !(MoveNode instanceof moveutil.MoveTreeNode) ||
      typeof Callback != "function"
    ) {
      throw TypeError();
    }
    let pointer = MoveNode;
    let moves = [];
    let i = 0;
    while (pointer.PreviousNode) {
      moves.push(pointer);
      pointer = pointer.PreviousNode;
    }
    moves.push(this.MoveTree.RootNode);
    moves.reverse();
    pointer = MoveNode;
    while (pointer.NextNodes[0]) {
      pointer = pointer.NextNodes[0];
      moves.push(pointer);
    }
    for (i = 0; i < moves.length; i++) {
      Callback(moves[i].Move, moves[i]);
    }
  }

  ToString(Notation, AlwaysShowResult) {
    if (Notation == null || typeof AlwaysShowResult != "boolean") {
      throw TypeError();
    }
    let fenitems = this.OriginalFEN.split(this.BlankSplitter);
    let initialmoverround = fenitems[1] == "b" ? 1 : 0;
    let initialmovenumber = parseInt(fenitems.pop());
    if (isNaN(initialmovenumber)) {
      // FENs without move counters (e.g., custom variant start FENs) start at move 1
      initialmovenumber = 1;
    }
    this.MoveTree.SetInitialCondition(initialmovenumber, initialmoverround, 2);
    let tokens = this.MoveTree.ToPGNTokens(2).slice(1);
    console.log(this.MoveTree);
    let i = 0;
    let tmpboard = new ffish.Board(this.Variant, this.OriginalFEN, this.Is960);
    let result = [];
    let stack = [];
    let lastmainlinemove = this.MoveTree.RootNode;
    let movestack = [];
    if (this.MoveTree.RootNode.Move.TextAfter) {
      result.push("{" + this.MoveTree.RootNode.Move.TextAfter + "}");
    }
    for (i = 0; i < tokens.length; i++) {
      if (tokens[i].IsSplitter) {
        if (tokens[i].Move.Move == "(") {
          stack.push(movestack.join(" "));
          tmpboard.pop();
          movestack.pop();
          result.push("(");
        } else if (tokens[i].Move.Move == ")") {
          movestack = stack[stack.length - 1].split(" ");
          tmpboard.reset();
          tmpboard.setFen(this.OriginalFEN);
          tmpboard.pushMoves(stack.pop());
          result.push(")");
        }
      } else {
        if (tokens[i].Move.TextBefore) {
          if (i > 0 && tokens[i - 1].Move.Move == "(") {
            result.push("{" + tokens[i].Move.TextBefore + "}");
            if (tokens[i].Move.MoverRound == 0) {
              result.push(Math.ceil(tokens[i].Move.HalfMoveNumber / 2) + ".");
            } else {
              result.push(Math.ceil(tokens[i].Move.HalfMoveNumber / 2) + "...");
            }
          } else {
            if (tokens[i].Move.MoverRound == 0) {
              result.push(Math.ceil(tokens[i].Move.HalfMoveNumber / 2) + ".");
            } else {
              result.push(Math.ceil(tokens[i].Move.HalfMoveNumber / 2) + "...");
            }
            result.push("{" + tokens[i].Move.TextBefore + "}");
          }
        } else {
          if (
            i == 0 ||
            (i > 0 &&
              (tokens[i - 1].IsSplitter || tokens[i - 1].Move.TextAfter))
          ) {
            if (tokens[i].Move.MoverRound == 0) {
              result.push(Math.ceil(tokens[i].Move.HalfMoveNumber / 2) + ".");
            } else {
              result.push(Math.ceil(tokens[i].Move.HalfMoveNumber / 2) + "...");
            }
          } else if (tokens[i].Move.MoverRound == 0) {
            result.push(Math.ceil(tokens[i].Move.HalfMoveNumber / 2) + ".");
          }
        }
        if (stack.length == 0) {
          lastmainlinemove = tokens[i].Node;
        }
        result.push(tmpboard.sanMove(tokens[i].Move.Move, Notation));
        tmpboard.push(tokens[i].Move.Move);
        movestack.push(tokens[i].Move.Move);
        if (tokens[i].Move.Symbol.length > 0) {
          result.push(tokens[i].Move.Symbol.join(" "));
        }
        if (tokens[i].Move.TextAfter) {
          result.push("{" + tokens[i].Move.TextAfter + "}");
        }
      }
    }
    let tmpboardresult = getBoardResult(tmpboard);
    if (tmpboardresult == "*") {
      if (lastmainlinemove.Move.TextAfter) {
        let index = 0,
          indexend = 0;
        let terminationstr;
        index = lastmainlinemove.Move.TextAfter.indexOf("[%end ");
        if (index >= 0) {
          indexend = lastmainlinemove.Move.TextAfter.indexOf("]", index + 6);
          if (indexend >= 0) {
            terminationstr = lastmainlinemove.Move.TextAfter.substring(
              index + 6,
              indexend,
            ).split(",");
            if (
              GameResults.includes(terminationstr[0]) &&
              GameTerminations.includes(terminationstr[1])
            ) {
              tmpboardresult = terminationstr[0];
            }
          }
        }
      }
    }
    if (AlwaysShowResult || tmpboardresult != "*") {
      result.push(tmpboardresult);
    }
    tmpboard.delete();
    return result.join(" ").replace(/\n/g, "\\n");
  }

  ToPGNDiv(Notation, Mode = "flat", Orientation = "white") {
    if (
      Notation == null ||
      typeof Mode != "string" ||
      typeof Orientation != "string"
    ) {
      throw TypeError();
    }
    function new_info_struct() {
      return {
        text_content: "",
        fenstr: "",
        lastmove: [],
        moveturn: "",
        checked: [],
        gameresult: "",
        startingfen: "",
        moves: "",
        boardmarkers: "",
      };
    }
    let fenitems = this.OriginalFEN.split(this.BlankSplitter);
    let initialmoverround = fenitems[1] == "b" ? 1 : 0;
    let initialmovenumber = parseInt(fenitems.pop());
    if (isNaN(initialmovenumber)) {
      // FENs without move counters (e.g., custom variant start FENs) start at move 1
      initialmovenumber = 1;
    }
    this.MoveTree.SetInitialCondition(initialmovenumber, initialmoverround, 2);
    let tokens = this.MoveTree.ToPGNTokens(2);
    let i = 0,
      j = 0;
    let tmpboard = new ffish.Board(this.Variant, this.OriginalFEN, this.Is960);
    let stack = [];
    let movestack = [];
    let info_struct = new_info_struct();
    let move = null;
    let gameresult = "";
    let parsedtext;
    let boardmarkers = "";
    let hidesubsequentmovelevel = 0;
    let glyph = 0;
    let displaytextbefore = "";
    let displaytextafter = "";
    let lastmainlinemove = this.MoveTree.RootNode;
    let terminationstr;
    let evalstr = "";
    let pgn_container_vnodes = [];
    let vnode_types = [];
    let previous_onclick_handler = null;

    const dimensions = getDimensions(tmpboard);
    const board_width = dimensions.width;
    const board_height = dimensions.height;
    const has_pocket = this.OriginalFEN.includes("[");
    const wrap = document.getElementById("chessground-board");
    const cg_board = wrap ? wrap.getElementsByTagName("cg-board")[0] : null;
    const square_aspect_ratio = cg_board
      ? parseFloat(
          window
            .getComputedStyle(cg_board)
            .getPropertyValue("--square-aspect-ratio"),
        ) || 1
      : 1;

    const VNODE_SPLITTER_START = 0;
    const VNODE_SPLITTER_END = 1;
    const VNODE_MOVE_NUMBER = 2;
    const VNODE_FIRST_MOVE = 3;
    const VNODE_SECOND_MOVE = 4;
    const VNODE_INLINE_OBJECT = 5;
    const VNODE_BLOCK_OBJECT = 6;

    info_struct.moveturn = tmpboard.turn() ? "white" : "black";
    info_struct.checked = getCheckSquares(tmpboard);
    info_struct.gameresult = getBoardResult(tmpboard);
    info_struct.startingfen = info_struct.fenstr = this.OriginalFEN;

    let _info_struct_pointer = info_struct;
    previous_onclick_handler = (event) => {
      if (event instanceof PointerEvent) {
        if (isGameStarted.checked) {
          onMoveElementClicked(_info_struct_pointer, event.target);
        } else {
          if (
            _info_struct_pointer.moves !=
            textMoves.value.trim().replace(SpaceReplacer, " ")
          ) {
            textMoves.value = _info_struct_pointer.moves;
            buttonSetFen.click();
          }
        }
      }
    };

    for (i = 0; i < tokens.length; i++) {
      if (tokens[i].IsSplitter) {
        if (tokens[i].Move.Move == "(") {
          stack.push(movestack.join(" "));
          tmpboard.pop();
          movestack.pop();
          if (hidesubsequentmovelevel > 0) {
            hidesubsequentmovelevel++;
          } else {
            pgn_container_vnodes.push(
              m(`p.splitter${stack.length == 1 ? ".mainline" : ""}`, "("),
            );
            vnode_types.push(VNODE_SPLITTER_START);
          }
        } else if (tokens[i].Move.Move == ")") {
          movestack = stack[stack.length - 1].split(" ");
          tmpboard.reset();
          tmpboard.setFen(this.OriginalFEN);
          tmpboard.pushMoves(stack.pop());
          if (hidesubsequentmovelevel > 0) {
            hidesubsequentmovelevel--;
          }
          if (hidesubsequentmovelevel == 0) {
            pgn_container_vnodes.push(
              m(`p.splitter${stack.length == 0 ? ".mainline" : ""}`, ")"),
            );
            vnode_types.push(VNODE_SPLITTER_END);
          }
        }
      } else {
        if (stack.length == 0) {
          lastmainlinemove = tokens[i].Node;
        }
        if (hidesubsequentmovelevel > 0) {
          continue;
        }
        if (i > 0 && tokens[i].Move.TextBefore) {
          displaytextbefore = tokens[i].Move.TextBefore.replace(
            MoveTextActionPartsMatcher,
            "",
          );
          if (CompleteBlankStringMatcher.test(displaytextbefore)) {
            displaytextbefore = "";
          } else {
            pgn_container_vnodes.push(
              m(
                `p.text-before${tokens[i].Move.TextBefore.includes("\n") ? ".full-line" : ""}`,
                displaytextbefore,
              ),
            );
            vnode_types.push(VNODE_BLOCK_OBJECT);
          }
        } else {
          displaytextbefore = "";
        }
        if (
          i == 1 ||
          (i > 1 && (tokens[i - 1].IsSplitter || displaytextafter)) ||
          displaytextbefore
        ) {
          if (tokens[i].Move.MoverRound == 0) {
            pgn_container_vnodes.push(
              m(
                "p.move-number",
                `${Math.ceil(tokens[i].Move.HalfMoveNumber / 2)}.`,
              ),
            );
          } else {
            pgn_container_vnodes.push(
              m(
                "p.move-number",
                `${Math.ceil(tokens[i].Move.HalfMoveNumber / 2)}...`,
              ),
            );
          }
          vnode_types.push(VNODE_MOVE_NUMBER);
        } else if (i > 0 && tokens[i].Move.MoverRound == 0) {
          pgn_container_vnodes.push(
            m(
              "p.move-number",
              `${Math.ceil(tokens[i].Move.HalfMoveNumber / 2)}.`,
            ),
          );
          vnode_types.push(VNODE_MOVE_NUMBER);
        }
        if (i == 0) {
          gameresult = getBoardResult(tmpboard);
        } else {
          move = moveutil.ParseUCIMove(tokens[i].Move.Move);
          info_struct = new_info_struct();
          info_struct.text_content = tmpboard.sanMove(
            tokens[i].Move.Move,
            Notation,
          );
          for (j = 0; j < tokens[i].Move.Symbol.length; j++) {
            glyph = parseInt(tokens[i].Move.Symbol[j].substring(1));
            if (moveutil.NumericAnnotationGlyphs[glyph]) {
              info_struct.text_content +=
                (j == 0 ? "" : " ") + moveutil.NumericAnnotationGlyphs[glyph];
            }
          }
          tmpboard.push(tokens[i].Move.Move);
          movestack.push(tokens[i].Move.Move);
          gameresult = getBoardResult(tmpboard);
          info_struct.fenstr = tmpboard.fen();
          if (move[0].includes("@")) {
            info_struct.lastmove = [
              move[0],
              convertSquareToChessgroundXKey(move[1]),
            ];
          } else {
            info_struct.lastmove = [
              convertSquareToChessgroundXKey(move[0]),
              convertSquareToChessgroundXKey(move[1]),
            ];
          }
          info_struct.moveturn = tmpboard.turn() ? "white" : "black";
          info_struct.checked = getCheckSquares(tmpboard);
          info_struct.gameresult = gameresult;
          info_struct.startingfen = this.OriginalFEN;
          info_struct.moves = movestack.join(" ");
          let info_struct_pointer = info_struct; // Create new pointer variable to point to correct object, as info_struct will be overwritten in the loop
          previous_onclick_handler = (event) => {
            if (event instanceof PointerEvent) {
              if (isGameStarted.checked) {
                onMoveElementClicked(info_struct_pointer, event.target);
              } else {
                if (
                  info_struct_pointer.moves !=
                  textMoves.value.trim().replace(SpaceReplacer, " ")
                ) {
                  textMoves.value = info_struct_pointer.moves;
                  buttonSetFen.click();
                }
              }
            }
          };
          pgn_container_vnodes.push(
            m(
              `p.position-display-label${tokens[i].Node == this.CurrentMove ? ".current-move" : ""}`,
              {
                onclick: previous_onclick_handler,
              },
              info_struct.text_content,
            ),
          );
          vnode_types.push(
            tmpboard.turn() ? VNODE_SECOND_MOVE : VNODE_FIRST_MOVE,
          );
        }
        if (tokens[i].Move.TextAfter) {
          parsedtext = moveutil.ParseTextActions(tokens[i].Move.TextAfter);
          boardmarkers =
            (parsedtext.get("cal") ?? "") + "," + (parsedtext.get("csl") ?? "");
          terminationstr = (parsedtext.get("end") ?? "").split(",");
          evalstr = parsedtext.get("eval") ?? "";
          if (evalstr) {
            if (evalstr.startsWith("#")) {
              pgn_container_vnodes.push(
                m(
                  "p.evaluation-text",
                  {
                    title: getEvaluationDescription(
                      parseFloat(evalstr.substring(1)),
                      true,
                    ),
                  },
                  evalstr,
                ),
              );
            } else {
              pgn_container_vnodes.push(
                m(
                  "p.evaluation-text",
                  {
                    title: getEvaluationDescription(parseFloat(evalstr), false),
                  },
                  evalstr,
                ),
              );
            }
            vnode_types.push(VNODE_INLINE_OBJECT);
          }
          if (boardmarkers.length > 1) {
            if (i > 0) {
              info_struct.boardmarkers = boardmarkers;
            }
            pgn_container_vnodes.push(
              m("img.has-move-note-sign", {
                src: "./assets/images/pgn/colorring.svg",
                width: "20",
                height: "20",
                title:
                  "This position has additional markers on the board. Click this move to view it on the mini board.",
              }),
            );
            vnode_types.push(VNODE_INLINE_OBJECT);
          }
          if (gameresult != "*") {
            if (terminationstr.length == 2) {
              pgn_container_vnodes.push(
                m(
                  "p.marked-result",
                  gameresult +
                    ": " +
                    FriendlyGameTerminationNames[
                      FriendlyGameTerminationNames.length - 1
                    ],
                ),
              );
              vnode_types.push(VNODE_BLOCK_OBJECT);
            }
          } else if (terminationstr.length == 2) {
            if (
              GameResults.includes(terminationstr[0]) &&
              GameTerminations.includes(terminationstr[1])
            ) {
              if (i > 0) {
                info_struct.gameresult = terminationstr[0];
              }
              pgn_container_vnodes.push(
                m(
                  "p.marked-result",
                  {
                    title: "This position has a termination mark.",
                  },
                  terminationstr[0] +
                    ": " +
                    FriendlyGameTerminationNames[
                      GameTerminations.indexOf(terminationstr[1])
                    ],
                ),
              );
              vnode_types.push(VNODE_BLOCK_OBJECT);
            }
          }

          displaytextafter = tokens[i].Move.TextAfter.replace(
            MoveTextActionPartsMatcher,
            "",
          );
          if (CompleteBlankStringMatcher.test(displaytextafter)) {
            displaytextafter = "";
          } else {
            pgn_container_vnodes.push(
              m(
                `p.text-after${tokens[i].Move.TextAfter.includes("\n") ? ".full-line" : ""}`,
                displaytextafter,
              ),
            );
            vnode_types.push(VNODE_BLOCK_OBJECT);
          }
          if (tokens[i].Move.TextAfter.includes("[#]")) {
            displaytextafter += "[#]";
            pgn_container_vnodes.push(
              m(
                "div.board-peek",
                {
                  title:
                    "Preview of the position. Click to go to this position.",
                  style: `--square-aspect-ratio: ${square_aspect_ratio};`,
                  onclick: previous_onclick_handler,
                },
                [
                  boardpeek.GenerateBoardDisplayElement(
                    info_struct.fenstr.split(" ")[0],
                    move ? move[0] + move[1] : "",
                    info_struct.checked,
                    has_pocket,
                    Orientation,
                    board_width,
                    board_height,
                    themedetector,
                  ),
                ],
              ),
            );
            vnode_types.push(VNODE_BLOCK_OBJECT);
          }
        } else {
          displaytextafter = "";
        }
        if (tokens[i].Move.HideSubsequentMoves) {
          hidesubsequentmovelevel = 1;
          let move_node = tokens[i].Move;
          pgn_container_vnodes.push(
            m(
              "p.hide-subsequent-moves-sign",
              {
                title:
                  "Moves after this move are not displayed. Click here to show them.",
                onclick: () => {
                  move_node.HideSubsequentMoves = false;
                  updatePGNDivision(false);
                },
              },
              "...",
            ),
          );
          vnode_types.push(VNODE_INLINE_OBJECT);
        }
      }
    }
    let tmpboardresult = getBoardResult(tmpboard);
    if (tmpboardresult == "*") {
      if (lastmainlinemove.Move.TextAfter) {
        let index = 0,
          indexend = 0;
        index = lastmainlinemove.Move.TextAfter.indexOf("[%end ");
        if (index >= 0) {
          indexend = lastmainlinemove.Move.TextAfter.indexOf("]", index + 6);
          if (indexend >= 0) {
            terminationstr = lastmainlinemove.Move.TextAfter.substring(
              index + 6,
              indexend,
            ).split(",");
            if (
              GameResults.includes(terminationstr[0]) &&
              GameTerminations.includes(terminationstr[1])
            ) {
              tmpboardresult = terminationstr[0];
            }
          }
        }
      }
    }
    if (tmpboardresult != "*") {
      pgn_container_vnodes.push(m("p.result", tmpboardresult));
      vnode_types.push(VNODE_BLOCK_OBJECT);
    }
    tmpboard.delete();

    if (Mode == "flat") {
      return m("div#pgndiv.board-display-san", pgn_container_vnodes);
    } else if (Mode == "tree-flat") {
      let stack = [];
      let level = 0;
      let current_list = [];
      let previous_list;
      let element;
      for (i = 0; i < pgn_container_vnodes.length; i++) {
        if (vnode_types[i] == VNODE_SPLITTER_START) {
          stack.push(current_list);
          current_list = [];
          level++;
        } else if (vnode_types[i] == VNODE_SPLITTER_END) {
          previous_list = current_list;
          element = stack.pop();
          current_list = element;
          current_list.push(m("div.branch", previous_list));
          level--;
        } else {
          current_list.push(pgn_container_vnodes[i]);
        }
      }
      return m("div#pgndiv.board-display-san", current_list);
    } else if (Mode == "tree-grid" || Mode == "grid") {
      const RECURSE = Mode == "tree-grid";
      function generate_move_element(move_element, is_final_move = false) {
        if (move_element.first_move_elements.length == 0) {
          move_element.first_move_elements = "...";
        }
        if (move_element.second_move_elements.length == 0) {
          move_element.second_move_elements = is_final_move ? null : "...";
        }
        return m("div.move-grid", [
          move_element.move_number,
          m("div.first-move-column", move_element.first_move_elements),
          m("div.second-move-column", move_element.second_move_elements),
        ]);
      }
      function new_move_grid() {
        return {
          move_number: null,
          first_move_elements: [],
          second_move_elements: [],
        };
      }
      let stack = [];
      let level = 0;
      let current_list = [];
      let current_move_element = new_move_grid();
      let current_move_inline_elements = [];
      let previous_list;
      let element;
      for (i = 0; i < pgn_container_vnodes.length; i++) {
        if (vnode_types[i] == VNODE_SPLITTER_START) {
          if (RECURSE || level == 0) {
            if (current_move_element.move_number) {
              current_list.push(generate_move_element(current_move_element));
              current_move_element = new_move_grid();
            }
            stack.push(current_list);
            current_list = [];
          } else {
            current_list.push(pgn_container_vnodes[i]);
          }
          level++;
        } else if (vnode_types[i] == VNODE_SPLITTER_END) {
          if (RECURSE || level == 1) {
            if (RECURSE && current_move_element.move_number) {
              current_list.push(
                generate_move_element(current_move_element, true),
              );
              current_move_element = new_move_grid();
            }
            previous_list = current_list;
            element = stack.pop();
            current_list = element;
            current_list.push(m("div.branch", previous_list));
          } else {
            current_list.push(pgn_container_vnodes[i]);
          }
          level--;
        } else {
          if (RECURSE || level == 0) {
            if (vnode_types[i] == VNODE_MOVE_NUMBER) {
              if (current_move_element.move_number) {
                current_list.push(generate_move_element(current_move_element));
                current_move_element = new_move_grid();
              }
              current_move_element.move_number = pgn_container_vnodes[i];
            } else if (vnode_types[i] == VNODE_FIRST_MOVE) {
              current_move_inline_elements =
                current_move_element.first_move_elements;
              current_move_element.first_move_elements.push(
                pgn_container_vnodes[i],
              );
            } else if (vnode_types[i] == VNODE_SECOND_MOVE) {
              current_move_inline_elements =
                current_move_element.second_move_elements;
              current_move_element.second_move_elements.push(
                pgn_container_vnodes[i],
              );
            } else if (vnode_types[i] == VNODE_INLINE_OBJECT) {
              current_move_inline_elements.push(pgn_container_vnodes[i]);
            } else if (vnode_types[i] == VNODE_BLOCK_OBJECT) {
              if (current_move_element.move_number) {
                current_list.push(generate_move_element(current_move_element));
                current_move_element = new_move_grid();
              }
              current_list.push(m("div.grid-block", [pgn_container_vnodes[i]]));
            }
          } else {
            current_list.push(pgn_container_vnodes[i]);
          }
        }
      }
      if (current_move_element.move_number) {
        current_list.push(generate_move_element(current_move_element, true));
      }
      return m("div#pgndiv.board-display-san", current_list);
    } else if (Mode == "tree-grid-half" || Mode == "grid-half") {
      const RECURSE = Mode == "tree-grid-half";
      function generate_move_element(move_element) {
        return m("div.move-grid", [
          move_element.move_number,
          m("div.half-move-column", move_element.half_move_elements),
        ]);
      }
      function new_move_grid() {
        return {
          move_number: null,
          half_move_elements: [],
        };
      }
      let stack = [];
      let level = 0;
      let current_list = [];
      let current_move_element = new_move_grid();
      let current_move_inline_elements = [];
      let previous_list;
      let element;
      let current_half_move_number = this.MoveTree.InitialHalfMoveNumber;
      let half_move_number_stack = [];
      for (i = 0; i < pgn_container_vnodes.length; i++) {
        if (vnode_types[i] == VNODE_MOVE_NUMBER) {
          continue;
        } else if (vnode_types[i] == VNODE_SPLITTER_START) {
          half_move_number_stack.push(current_half_move_number--);
          if (RECURSE || level == 0) {
            if (current_move_element.move_number) {
              current_list.push(generate_move_element(current_move_element));
              current_move_element = new_move_grid();
            }
            stack.push(current_list);
            current_list = [];
          } else {
            current_list.push(pgn_container_vnodes[i]);
          }
          level++;
        } else if (vnode_types[i] == VNODE_SPLITTER_END) {
          current_half_move_number = half_move_number_stack.pop();
          if (RECURSE || level == 1) {
            if (RECURSE && current_move_element.move_number) {
              current_list.push(
                generate_move_element(current_move_element, true),
              );
              current_move_element = new_move_grid();
            }
            previous_list = current_list;
            element = stack.pop();
            current_list = element;
            current_list.push(m("div.branch", previous_list));
          } else {
            current_list.push(pgn_container_vnodes[i]);
          }
          level--;
        } else {
          if (RECURSE || level == 0) {
            if (vnode_types[i] == VNODE_FIRST_MOVE) {
              if (current_move_element.move_number) {
                current_list.push(generate_move_element(current_move_element));
                current_move_element = new_move_grid();
              }
              current_move_inline_elements =
                current_move_element.half_move_elements;
              current_move_element.move_number = m(
                "p.move-number",
                `${current_half_move_number++}.`,
              );
              current_move_element.half_move_elements.push(
                pgn_container_vnodes[i],
              );
            } else if (vnode_types[i] == VNODE_SECOND_MOVE) {
              if (current_move_element.move_number) {
                current_list.push(generate_move_element(current_move_element));
                current_move_element = new_move_grid();
              }
              current_move_inline_elements =
                current_move_element.half_move_elements;
              current_move_element.move_number = m(
                "p.move-number",
                `${current_half_move_number++}.`,
              );
              current_move_element.half_move_elements.push(
                pgn_container_vnodes[i],
              );
            } else if (vnode_types[i] == VNODE_INLINE_OBJECT) {
              current_move_inline_elements.push(pgn_container_vnodes[i]);
            } else if (vnode_types[i] == VNODE_BLOCK_OBJECT) {
              if (current_move_element.move_number) {
                current_list.push(generate_move_element(current_move_element));
                current_move_element = new_move_grid();
              }
              current_list.push(m("div.grid-block", [pgn_container_vnodes[i]]));
            }
          } else {
            if (
              vnode_types[i] == VNODE_FIRST_MOVE ||
              vnode_types[i] == VNODE_SECOND_MOVE
            ) {
              current_list.push(
                m("p.move-number", `${current_half_move_number++}.`),
              );
            }
            current_list.push(pgn_container_vnodes[i]);
          }
        }
      }
      if (current_move_element.move_number) {
        current_list.push(generate_move_element(current_move_element, true));
      }
      return m("div#pgndiv.board-display-san", current_list);
    } else {
      return m("div#pgndiv.board-display-san", pgn_container_vnodes);
    }
  }
}

let gametree = new GameTree();

// Contents previously <script> in index.html

let themes = [[], [], []];
let themenames = [[], []];
let variantsettings = [[], [], [], [], []];
let allvariants = [];
let uithemes = [[], []];
let currentthemeobj = null;
let currentuicss = null;

//Feature loading status global variable
var pageloaded = false;
var uithemesparsed = false;
var themesloaded = false;
var positionvariantsloaded = false;
var variantsettingsloaded = false;
var variantsystemready = false;

let previouschangeuitime = 0;
const $ = (...args) => document.querySelector(...args);

class UIThemeObject {
  constructor(ID, Name) {
    if (typeof ID != "string" || typeof Name != "string") {
      throw TypeError("UIThemeObject(ID:string, Name:string)");
    }
    this.Name = Name;
    this.ID = ID;
    this.StyleNodeList = [];
    this.StyleDurations = [];
    this.CurrentThemeIndex = 0;
    this.CurrentThemeRemainingTime = 0;
    this.Initialized = false;
    this.Timer = null;
    this.CanvasWorker = null;
    this.CanvasInstance = null;
    this.CanvasState = "Uninitialized";
    this.StyleDurationsLoaded = false;
    this.PendingCanvasReloading = false;
    this.CanvasFrameRate = 50;
    this.OnWindowResizeHandlerFunction = null;
  }

  destructor() {
    if (this.Timer != null) {
      clearTimeout(this.Timer);
    }
  }

  SetStyleDurations(StyleDurationsInSeconds) {
    if (!Array.isArray(StyleDurationsInSeconds)) {
      throw TypeError("SetStyleDurations(StyleDurations:number[])");
    }
    let i = 0;
    this.StyleDurations = [];
    this.StyleDurationsLoaded = true;
    for (i = 0; i < StyleDurationsInSeconds.length; i++) {
      if (typeof StyleDurationsInSeconds[i] != "number") {
        throw TypeError("SetStyleDurations(StyleDurations:number[])");
      }
      this.StyleDurations.push(StyleDurationsInSeconds[i] * 1000);
    }
  }

  SetCanvasWorker(CanvasWorkerName) {
    if (typeof CanvasWorkerName != "string") {
      throw TypeError("SetCanvasWorker(CanvasWorkerName:string)");
    }
    if (this.CanvasWorker != null) {
      return;
    }
    this.CanvasWorker = new Worker(
      `./lib/canvas/${CanvasWorkerName}.canvas.worker.js`,
    );
    this.CanvasWorker.onmessage = (event) => {
      const message = event.data;
      if (message.message == "CanvasHandlerDestroyed") {
        this.CanvasInstance.remove();
        this.CanvasInstance = null;
        this.CanvasState = "Uninitialized";
        if (this.PendingCanvasReloading) {
          this.PendingCanvasReloading = false;
          this.StartCanvasAnimation();
        }
      }
    };
    this.OnWindowResizeHandlerFunction =
      this.WindowResizeEventHandler.bind(this);
  }

  Initialize(OnInitializedCallback, OnErrorCallback) {
    if (
      typeof OnInitializedCallback != "function" ||
      typeof OnErrorCallback != "function"
    ) {
      throw TypeError(
        "Initialize(OnInitializedCallback:function(typeof this), OnErrorCallback:function(typeof this, Error))",
      );
    }
    if (!this.StyleDurationsLoaded) {
      throw Error(
        "Set style durations first. (Call SetStyleDurations(StyleDurations:number[]))",
      );
    }
    let received = 0;
    let totalreceives = 0;
    this.StyleNodeList = [];
    if (this.StyleDurations.length == 0) {
      this.CurrentThemeRemainingTime = -1;
      this.CurrentThemeIndex = 0;
      getFileFromServer(
        `./assets/theme-ui-${this.ID}.css`,
        (res) => {
          let element = document.createElement("style");
          element.style = "text/css";
          element.appendChild(document.createTextNode(res));
          this.StyleNodeList.push(element);
          this.Initialized = true;
          OnInitializedCallback(this);
        },
        (error) => {
          console.error(`UI theme CSS ${this.ID} fetch failed.`);
          OnErrorCallback(this, error);
        },
      );
    } else {
      let i = 0;
      this.CurrentThemeRemainingTime = this.StyleDurations[0];
      this.CurrentThemeIndex = 0;
      this.StyleNodeList = [];
      this.StyleNodeList.length = this.StyleDurations.length;
      totalreceives = this.StyleDurations.length;
      let HasError = false;
      for (i = 0; i < this.StyleDurations.length; i++) {
        ((index) => {
          getFileFromServer(
            `./assets/theme-ui-${this.ID}[${index}].css`,
            (res) => {
              let element = document.createElement("style");
              element.style = "text/css";
              element.appendChild(document.createTextNode(res));
              this.StyleNodeList[index] = element;
              received++;
              if (received >= totalreceives) {
                if (HasError) {
                  OnErrorCallback(this, error);
                } else {
                  this.Initialized = true;
                  OnInitializedCallback(this);
                }
              }
            },
            (error) => {
              HasError = true;
              console.error(`UI theme CSS ${this.ID}[${index}] fetch failed.`);
              received++;
              if (received >= totalreceives) {
                if (HasError) {
                  OnErrorCallback(this, error);
                } else {
                  this.Initialized = true;
                  OnInitializedCallback(this);
                }
              }
            },
          );
        })(i);
      }
    }
  }

  StoredThemeCount() {
    return this.StyleNodeList.length;
  }

  CancelTimer() {
    if (this.Timer != null) {
      clearTimeout(this.Timer);
      this.Timer = null;
    }
  }

  CurrentTheme() {
    if (this.StyleDurations.length == 0) {
      return this.StyleNodeList[0];
    } else {
      return this.StyleNodeList[this.CurrentThemeIndex];
    }
  }

  SetCurrentTheme(ThemeIndex, SaveCurrentThemeIndexToLocalStorage) {
    if (
      typeof ThemeIndex != "number" ||
      typeof SaveCurrentThemeIndexToLocalStorage != "boolean"
    ) {
      throw TypeError(
        "SetCurrentTheme(ThemeIndex:number, SaveCurrentThemeIndexToLocalStorage:boolean)",
      );
    }
    if (ThemeIndex < 0 || ThemeIndex >= this.StyleNodeList.length) {
      throw RangeError(
        `Max index is ${this.StyleNodeList.length}, Min index is 0.`,
      );
    }
    this.CancelTimer();
    this.CurrentThemeIndex = ThemeIndex;
    this.CurrentThemeRemainingTime = this.StyleDurations[ThemeIndex];
    if (SaveCurrentThemeIndexToLocalStorage) {
      localStorage.setItem(
        `UITheme-${this.ID}-CurrentThemeIndex`,
        `${ThemeIndex}`,
      );
    }
  }

  NextTheme(
    OnNextThemeTimeOutFinishCallback,
    SaveCurrentThemeIndexToLocalStorage,
  ) {
    if (
      typeof OnNextThemeTimeOutFinishCallback != "function" ||
      typeof SaveCurrentThemeIndexToLocalStorage != "boolean"
    ) {
      throw TypeError(
        "Next(OnNextThemeTimeOutFinishCallback:function(HTMLStyleElement), SaveCurrentThemeIndexToLocalStorage:boolean)",
      );
    }
    if (this.StyleDurations.length == 0) {
      return;
    }
    if (this.Timer) {
      this.CancelTimer();
      this.CurrentThemeIndex++;
      if (this.CurrentThemeIndex >= this.StyleNodeList.length) {
        this.CurrentThemeIndex = 0;
      }
      this.CurrentThemeRemainingTime =
        this.StyleDurations[this.CurrentThemeIndex];
      if (SaveCurrentThemeIndexToLocalStorage) {
        localStorage.setItem(
          `UITheme-${this.ID}-CurrentThemeIndex`,
          `${this.CurrentThemeIndex}`,
        );
      }
      OnNextThemeTimeOutFinishCallback(this.CurrentTheme());
    }
    this.Timer = setTimeout(() => {
      this.CurrentThemeIndex++;
      if (this.CurrentThemeIndex >= this.StyleNodeList.length) {
        this.CurrentThemeIndex = 0;
      }
      this.CurrentThemeRemainingTime =
        this.StyleDurations[this.CurrentThemeIndex];
      if (SaveCurrentThemeIndexToLocalStorage) {
        localStorage.setItem(
          `UITheme-${this.ID}-CurrentThemeIndex`,
          `${this.CurrentThemeIndex}`,
        );
      }
      OnNextThemeTimeOutFinishCallback(this.CurrentTheme());
    }, this.CurrentThemeRemainingTime);
  }

  GetCurrentThemeIndexFromLocalStorage() {
    let ThemeIndex = localStorage.getItem(
      `UITheme-${this.ID}-CurrentThemeIndex`,
    );
    if (
      ThemeIndex != null &&
      parseInt(ThemeIndex) >= 0 &&
      parseInt(ThemeIndex) < this.StyleNodeList.length
    ) {
      this.SetCurrentTheme(parseInt(ThemeIndex), false);
    }
  }

  SetCanvasFrameRate(FrameRate) {
    if (typeof FrameRate != "number") {
      throw TypeError("SetCanvasFrameRate(FrameRate:number)");
    }
    this.CanvasFrameRate = FrameRate;
  }

  StartCanvasAnimation() {
    if (this.CanvasWorker == null) {
      return false;
    } else if (this.CanvasState != "Uninitialized") {
      this.PendingCanvasReloading = true;
      return true;
    }
    let canvas = document.createElement("canvas");
    let pagebackground = document.getElementById("pagebackgroundcanvas");
    canvas.setAttribute("width", `${window.innerWidth}`);
    canvas.setAttribute("height", `${window.innerHeight}`);
    canvas.classList.add("background-canvas");
    const offscreenCanvas = canvas.transferControlToOffscreen();
    pagebackground.appendChild(canvas);
    this.CanvasWorker.postMessage(
      {
        message: "Start",
        canvas: offscreenCanvas,
        framerate: this.CanvasFrameRate,
        id: 0,
      },
      [offscreenCanvas],
    );
    this.CanvasInstance = canvas;
    this.CanvasState = "Running";
    window.addEventListener("resize", this.OnWindowResizeHandlerFunction);
    return true;
  }

  PauseCanvasAnimation() {
    if (this.CanvasWorker == null || this.CanvasState != "Running") {
      return false;
    }
    this.CanvasWorker.postMessage({ message: "Stop" });
    this.CanvasState = "Stopped";
    return true;
  }

  ContinueCanvasAnimation() {
    if (this.CanvasWorker == null || this.CanvasState != "Stopped") {
      return false;
    }
    this.CanvasWorker.postMessage({ message: "Continue" });
    this.CanvasState = "Running";
    return true;
  }

  ResizeCanvas(Width, Height) {
    if (typeof Width != "number" || typeof Height != "number") {
      throw TypeError("ResizeCanvas(Width:number,Height:number)");
    }
    if (this.CanvasWorker == null) {
      return;
    }
    this.CanvasWorker.postMessage({
      message: "Resize",
      width: Width,
      height: Height,
    });
  }

  CloseCanvas() {
    if (this.CanvasWorker == null || this.CanvasState == "Uninitialized") {
      return false;
    }
    this.PendingCanvasReloading = false;
    this.CanvasWorker.postMessage({ message: "Terminate" });
    this.CanvasState = "Closing";
    window.removeEventListener("resize", this.OnWindowResizeHandlerFunction);
    return true;
  }

  WindowResizeEventHandler() {
    this.ResizeCanvas(window.innerWidth, window.innerHeight);
  }

  MoveCanvasToNewContainer(Container) {
    if (!(Container instanceof HTMLDivElement)) {
      throw TypeError("MoveCanvasToNewContainer(Container:HTMLDivElement)");
    }
    if (this.CanvasWorker == null || this.CanvasState == "Uninitialized") {
      return false;
    }
    this.CanvasInstance.remove();
    Container.appendChild(this.CanvasInstance);
    return true;
  }
}

document.addEventListener("onpageload", () => {
  pageloaded = true;
  if (uithemesparsed) {
    document.getElementById("setupuithemes").click();
    console.log(
      "%c UI Theme System %c READY %c UI theme subsystem is ready.",
      "color: #fff; background: #5f5f5f",
      "color: #fff; background: #4bc729",
      "",
    );
  }
  if (themesloaded && positionvariantsloaded && variantsettingsloaded) {
    document
      .getElementById("updatevarianttypedropdown")
      .dispatchEvent(new Event("click"));
    console.log(
      "%c Variant System %c READY %c Variant subsystem is ready.",
      "color: #fff; background: #5f5f5f",
      "color: #fff; background: #4bc729",
      "",
    );
    variantsystemready = true;
  }
  document.getElementById("dropdown-variant").addEventListener("change", () => {
    setTimeout(() => {
      updateInfoDivWidth();
    }, 10);
  });
  document.getElementById("dropdown-uitheme").addEventListener("change", () => {
    setTimeout(() => {
      updateInfoDivWidth();
    }, 10);
  });

  setTimeout(() => {
    document.getElementById("sannotation").selectedIndex =
      parseInt(localStorage.getItem("SanNotation")) || 2;
    document.getElementById("sannotation").dispatchEvent(new Event("change"));
    document.getElementById("boardcoordinate").selectedIndex =
      parseInt(localStorage.getItem("BoardCoordinate")) || 0;
    document
      .getElementById("boardcoordinate")
      .dispatchEvent(new Event("change"));
    document.getElementById("pgnstyle").selectedIndex =
      parseInt(localStorage.getItem("PGNStyle")) || 0;
    document.getElementById("pgnstyle").dispatchEvent(new Event("change"));
    if (localStorage.getItem("InnerCoordinate") == "true") {
      document.getElementById("check-innercoordinate").click();
    }
    if (localStorage.getItem("ShowDestinations") == "false") {
      document.getElementById("check-dests").click();
    }
    if (localStorage.getItem("ShowAdjudication") == "false") {
      document.getElementById("check-adjudicate").click();
    }
    if (localStorage.getItem("UseIntegerInput") == "true") {
      document.getElementById("check-granularity").click();
    }
    if (localStorage.getItem("AdvancedPGNMode") == "false") {
      document.getElementById("isadvpgnmode").click();
    }
    if (localStorage.getItem("ShowMovesDialog") == "true") {
      document.getElementById("showmovediv").click();
    }
    if (localStorage.getItem("ShowEvaluationHistoryGraph") == "true") {
      document.getElementById("showevalgraph").click();
    }
    document.getElementById("range-volume").value =
      localStorage.getItem("SoundVolume") || 1;
    document.getElementById("range-volume").dispatchEvent(new Event("change"));
  }, 500);

  let chessgroundmini = document.getElementById("chessground-mini");
  let chessgroundminiboardwrapper = document.getElementById(
    "chessground-mini-board-wrapper-div",
  );
  let maindiv = document.getElementsByTagName("main")[0];
  let pgnlabel = document.getElementById("label-pgn");
  let pvinfo = document.getElementById("pvinfo");
  let lockminiboard = document.getElementById("lockminiboard");
  let operationdiv = document.getElementById(
    "chessground-mini-board-operation-div",
  );
  let terminationsettingsdiv = document.getElementById("terminationsettings");
  let pgnoperationsdiv = document.getElementById("pgn-operations");
  let startX, startY, initialX, initialY;
  chessgroundminiboardwrapper.style.cursor = "move";
  chessgroundmini.locked = false;
  chessgroundmini.pinned = false;
  window.addEventListener("resize", () => {
    updateInfoDivWidth();
    const maindivrect = maindiv.getBoundingClientRect();
    const chessgroundminirect = chessgroundmini.getBoundingClientRect();
    const scrollbarwidthright =
      window.innerWidth - maindivrect.right > 0
        ? window.innerWidth - maindivrect.right
        : 0;
    const padding = 10;
    if (chessgroundmini.pinned) {
      const windowwidth = window.innerWidth;
      if (chessgroundminirect.right > windowwidth) {
        chessgroundmini.style.left = `${windowwidth - chessgroundminirect.width - padding - scrollbarwidthright}px`;
      }
    } else {
      if (chessgroundminirect.left < maindivrect.left + padding) {
        chessgroundmini.style.left = `${maindivrect.left + padding}px`;
      } else if (chessgroundminirect.right > maindivrect.right - padding) {
        chessgroundmini.style.left = `${maindivrect.right - padding - chessgroundminirect.width}px`;
      }
    }
  });
  function onMouseMove(e) {
    chessgroundmini.style.left = `${startX + e.clientX - initialX}px`;
    chessgroundmini.style.top = `${startY + e.clientY - initialY}px`;
  }
  function onMouseUp() {
    document.removeEventListener("mousemove", onMouseMove);
    document.removeEventListener("mouseup", onMouseUp);
    chessgroundminiboardwrapper.style.cursor = "move";
    const maindivrect = maindiv.getBoundingClientRect();
    const chessgroundminirect = chessgroundmini.getBoundingClientRect();
    const padding = 10;
    const scrollbarwidthright =
      window.innerWidth - maindivrect.right > 0
        ? window.innerWidth - maindivrect.right
        : 0;
    const scrollbarwidthleft = maindivrect.left > 0 ? maindivrect.left : 0;
    if (chessgroundmini.pinned) {
      if (chessgroundminirect.left < padding + scrollbarwidthleft) {
        chessgroundmini.style.left = `${padding + scrollbarwidthleft}px`;
      } else if (
        chessgroundminirect.right >
        window.innerWidth - padding - scrollbarwidthright
      ) {
        chessgroundmini.style.left = `${window.innerWidth - chessgroundminirect.width - padding - scrollbarwidthright}px`;
      }
      if (chessgroundminirect.top < padding) {
        chessgroundmini.style.top = `${padding}px`;
      } else if (chessgroundminirect.bottom > window.innerHeight - padding) {
        chessgroundmini.style.top = `${window.innerHeight - chessgroundminirect.height - padding}px`;
      }
    } else {
      chessgroundmini.style.left = `${chessgroundminirect.left - maindivrect.left}px`;
      chessgroundmini.style.top = `${chessgroundminirect.top - maindivrect.top}px`;
      chessgroundmini.style.position = "";
      if (chessgroundminirect.left < maindivrect.left + padding) {
        chessgroundmini.style.left = `${maindivrect.left + padding}px`;
      } else if (chessgroundminirect.right > maindivrect.right - padding) {
        chessgroundmini.style.left = `${maindivrect.right - padding - chessgroundminirect.width}px`;
      }
      if (chessgroundminirect.top < maindivrect.top + padding) {
        chessgroundmini.style.top = `${padding}px`;
      }
    }
  }
  function onTouchMove(e) {
    chessgroundmini.style.left = `${startX + e.touches[0].clientX - initialX}px`;
    chessgroundmini.style.top = `${startY + e.touches[0].clientY - initialY}px`;
  }
  function onTouchEnd() {
    document.removeEventListener("touchmove", onTouchMove);
    document.removeEventListener("touchend", onTouchEnd);
    document.removeEventListener("touchcancel", onTouchEnd);
    const maindivrect = maindiv.getBoundingClientRect();
    const chessgroundminirect = chessgroundmini.getBoundingClientRect();
    const padding = 10;
    const scrollbarwidthright =
      window.innerWidth - maindivrect.right > 0
        ? window.innerWidth - maindivrect.right
        : 0;
    const scrollbarwidthleft = maindivrect.left > 0 ? maindivrect.left : 0;
    if (chessgroundmini.pinned) {
      if (chessgroundminirect.left < padding + scrollbarwidthleft) {
        chessgroundmini.style.left = `${padding + scrollbarwidthleft}px`;
      } else if (
        chessgroundminirect.right >
        window.innerWidth - padding - scrollbarwidthright
      ) {
        chessgroundmini.style.left = `${window.innerWidth - chessgroundminirect.width - padding - scrollbarwidthright}px`;
      }
      if (chessgroundminirect.top < padding) {
        chessgroundmini.style.top = `${padding}px`;
      } else if (chessgroundminirect.bottom > window.innerHeight - padding) {
        chessgroundmini.style.top = `${window.innerHeight - chessgroundminirect.height - padding}px`;
      }
    } else {
      chessgroundmini.style.left = `${chessgroundminirect.left - maindivrect.left}px`;
      chessgroundmini.style.top = `${chessgroundminirect.top - maindivrect.top}px`;
      chessgroundmini.style.position = "";
      if (chessgroundminirect.left < maindivrect.left + padding) {
        chessgroundmini.style.left = `${maindivrect.left + padding}px`;
      } else if (chessgroundminirect.right > maindivrect.right - padding) {
        chessgroundmini.style.left = `${maindivrect.right - padding - chessgroundminirect.width}px`;
      }
      if (chessgroundminirect.top < maindivrect.top + padding) {
        chessgroundmini.style.top = `${padding}px`;
      }
    }
  }
  document.addEventListener("click", (event) => {
    if (
      !event.isTrusted ||
      (event.button !== undefined && event.button !== 0)
    ) {
      return;
    }
    if (
      !chessgroundmini.locked &&
      !chessgroundmini.contains(event.target) &&
      !pgnlabel.contains(event.target) &&
      !pvinfo.contains(event.target)
    ) {
      chessgroundmini.style.display = "none";
    }
    if (
      !terminationsettingsdiv.contains(event.target) &&
      !pgnoperationsdiv.contains(event.target)
    ) {
      terminationsettingsdiv.style.display = "none";
    }
  });
  chessgroundminiboardwrapper.addEventListener("mousedown", (event) => {
    event.stopPropagation();
    if (
      !event.isTrusted ||
      (event.button !== undefined && event.button !== 0)
    ) {
      return;
    }
    const chessgroundminirect = chessgroundmini.getBoundingClientRect();
    if (!chessgroundmini.pinned) {
      chessgroundmini.style.left = `${chessgroundminirect.left}px`;
      chessgroundmini.style.top = `${chessgroundminirect.top}px`;
      chessgroundmini.style.position = "fixed";
    }
    startX = chessgroundminirect.left;
    startY = chessgroundminirect.top;
    initialX = event.clientX;
    initialY = event.clientY;
    document.addEventListener("mousemove", onMouseMove);
    document.addEventListener("mouseup", onMouseUp);
    chessgroundminiboardwrapper.style.cursor = "grabbing";
  });
  chessgroundminiboardwrapper.addEventListener("touchstart", (event) => {
    event.stopPropagation();
    event.preventDefault();
    if (event.touches && event.touches.length > 1) {
      return;
    }
    const chessgroundminirect = chessgroundmini.getBoundingClientRect();
    if (!chessgroundmini.pinned) {
      chessgroundmini.style.left = `${chessgroundminirect.left}px`;
      chessgroundmini.style.top = `${chessgroundminirect.top}px`;
      chessgroundmini.style.position = "fixed";
    }
    startX = chessgroundminirect.left;
    startY = chessgroundminirect.top;
    initialX = event.touches[0].clientX;
    initialY = event.touches[0].clientY;
    document.addEventListener("touchmove", onTouchMove);
    document.addEventListener("touchend", onTouchEnd);
    document.addEventListener("touchcancel", onTouchEnd);
  });

  setTimeout(() => {
    document.dispatchEvent(new Event("initializeripples"));
  }, 10);

  /*pgnlabel.addEventListener("mousemove", Throttle((event) => {
      event.stopPropagation();
      if (chessgroundmini.style.display != "none") {
          const rect = maindiv.getBoundingClientRect();
          const chessgroundministyle = window.getComputedStyle(chessgroundmini);
          const chessgroundminiwidth = parseFloat(chessgroundministyle.width);
          const chessgroundminiheight = parseFloat(chessgroundministyle.height);
          const padding = 10;
          const maindivwidth = rect.width;
          const maindivheight = rect.height;
          const offsetX = event.clientX - rect.left;
          const offsetY = event.clientY - rect.top;
          let finalX = offsetX;
          let finalY = offsetY + 40;
          if (finalX + chessgroundminiwidth > maindivwidth - 2 * padding) {
              finalX -= chessgroundminiwidth;
          }
          chessgroundmini.style.left = `${finalX}px`;
          chessgroundmini.style.top = `${finalY}px`;
      }
  }, 50));*/
});

document.addEventListener("uithemesparsed", () => {
  uithemesparsed = true;
  if (pageloaded) {
    document.getElementById("setupuithemes").click();
    console.log(
      "%c UI Theme System %c READY %c UI theme subsystem is ready.",
      "color: #fff; background: #5f5f5f",
      "color: #fff; background: #4bc729",
      "",
    );
  }
});

document.addEventListener("positionvariantsloaded", () => {
  positionvariantsloaded = true;
  if (pageloaded && themesloaded && variantsettingsloaded) {
    document
      .getElementById("updatevarianttypedropdown")
      .dispatchEvent(new Event("click"));
    console.log(
      "%c Variant System %c READY %c Variant subsystem is ready.",
      "color: #fff; background: #5f5f5f",
      "color: #fff; background: #4bc729",
      "",
    );
    variantsystemready = true;
  }
});

document.addEventListener("themesloaded", () => {
  themesloaded = true;
  if (pageloaded && positionvariantsloaded && variantsettingsloaded) {
    document
      .getElementById("updatevarianttypedropdown")
      .dispatchEvent(new Event("click"));
    console.log(
      "%c Variant System %c READY %c Variant subsystem is ready.",
      "color: #fff; background: #5f5f5f",
      "color: #fff; background: #4bc729",
      "",
    );
    variantsystemready = true;
  }
});

document.addEventListener("variantsettingsloaded", () => {
  variantsettingsloaded = true;
  if (pageloaded && positionvariantsloaded && themesloaded) {
    document
      .getElementById("updatevarianttypedropdown")
      .dispatchEvent(new Event("click"));
    console.log(
      "%c Variant System %c READY %c Variant subsystem is ready.",
      "color: #fff; background: #5f5f5f",
      "color: #fff; background: #4bc729",
      "",
    );
    variantsystemready = true;
  }
});

document.addEventListener("uilayoutchange", (event) => {
  if (currentthemeobj instanceof UIThemeObject) {
    if (event.detail.message == null) {
      currentthemeobj.MoveCanvasToNewContainer(
        document.getElementById("pagebackgroundcanvas"),
      );
    } else if (typeof event.detail.message == "string") {
      let element = document.getElementById(event.detail.message);
      currentthemeobj.MoveCanvasToNewContainer(
        element == null
          ? document.getElementById("pagebackgroundcanvas")
          : element,
      );
    }
  }
});

document.addEventListener("visibilitychange", () => {
  if (currentthemeobj instanceof UIThemeObject) {
    if (document.visibilityState === "hidden") {
      currentthemeobj.PauseCanvasAnimation();
    } else if (document.visibilityState === "visible") {
      currentthemeobj.ContinueCanvasAnimation();
    }
  }
});

document.addEventListener("initializeripples", () => {
  let list = document.querySelectorAll(".ripple");
  let val = null;
  let i = 0;
  for (i = 0; i < list.length; i++) {
    val = list.item(i);
    if (val instanceof HTMLElement) {
      if (!Array.isArray(val.rippleelements)) {
        val.rippleelements = [];
        val.addEventListener("mousedown", function (event) {
          if (!event.isTrusted) {
            return;
          }
          const targetrect = this.getBoundingClientRect();
          const x = event.clientX - targetrect.left;
          const y = event.clientY - targetrect.top;
          const mx = targetrect.right - event.clientX;
          const my = targetrect.bottom - event.clientY;
          let radius = Math.ceil(
            2 *
              Math.sqrt(
                Math.max(
                  x * x + y * y,
                  x * x + my * my,
                  mx * mx + y * y,
                  mx * mx + my * my,
                ),
              ),
          );
          let ripplewrapper = document.createElement("div");
          ripplewrapper.classList.add("ripple-wrapper");
          ripplewrapper.style.top = `${this.scrollTop}px`;
          ripplewrapper.style.left = `${this.scrollLeft}px`;
          let rippleelem = document.createElement("span");
          rippleelem.classList.add("ripple-effect");
          rippleelem.style.left = `${x}px`;
          rippleelem.style.top = `${y}px`;
          ripplewrapper.appendChild(rippleelem);
          this.appendChild(ripplewrapper);
          this.rippleelements.push(ripplewrapper);
          setTimeout(() => {
            rippleelem.style.width = rippleelem.style.height = `${radius}px`;
          }, 10);
        });
        val.addEventListener("mouseleave", function (event) {
          if (!event.isTrusted) {
            return;
          }
          let i = 0;
          if (Array.isArray(this.rippleelements)) {
            let style = null;
            for (i = 0; i < this.rippleelements.length; i++) {
              style = window.getComputedStyle(this.rippleelements[i]);
              if (parseFloat(style.opacity) == 0 || style.display == "none") {
                this.rippleelements[i].remove();
                this.rippleelements.splice(i, 1);
                i--;
              } else {
                this.rippleelements[i].classList.add("ripple-fade-out");
              }
            }
          }
        });
        val.addEventListener("mouseup", function (event) {
          if (!event.isTrusted) {
            return;
          }
          let i = 0;
          if (Array.isArray(this.rippleelements)) {
            let style = null;
            for (i = 0; i < this.rippleelements.length; i++) {
              style = window.getComputedStyle(this.rippleelements[i]);
              if (parseFloat(style.opacity) == 0 || style.display == "none") {
                this.rippleelements[i].remove();
                this.rippleelements.splice(i, 1);
                i--;
              } else {
                this.rippleelements[i].classList.add("ripple-fade-out");
              }
            }
          }
        });
        val.addEventListener("scroll", function (event) {
          let i = 0;
          if (Array.isArray(this.rippleelements)) {
            for (i = 0; i < this.rippleelements.length; i++) {
              this.rippleelements[i].style.top = `${this.scrollTop}px`;
              this.rippleelements[i].style.left = `${this.scrollLeft}px`;
            }
          }
        });
      }
    }
  }
});

//Remove duplicated elements
function uniqArr(arr) {
  var newArr = new Set(arr);
  return Array.from(newArr);
}

//Throttle function, used to prevent lag when operating DOM objects.
function Throttle(func, wait) {
  let timer = null;
  return function () {
    if (!timer) {
      timer = setTimeout(() => {
        func.apply(this, arguments);
        timer = null;
      }, wait);
      func.apply(this, arguments);
    }
  };
}

function OpenURL(url) {
  let link = document.createElement("a");
  link.href = url;
  link.id = "tmplink";
  link.target = "_blank";
  document.body.appendChild(link);
  link.click();
  document.body.removeChild(link);
}

function getFileFromServer(url, doneCallback, errorCallback) {
  if (
    typeof url != "string" ||
    typeof doneCallback != "function" ||
    (typeof errorCallback != "function" && errorCallback != undefined)
  ) {
    throw TypeError(
      "getFileFromServer(url:string, doneCallback:function(string), errorCallback:function(Error) | undefined)",
    );
  }
  fetch(url)
    .then((response) => {
      if (!response.ok) {
        throw new Error(
          `Network response error: Code ${response.status} (${response.statusText})`,
        );
      }
      return response.text();
    })
    .then((content) => {
      doneCallback(content);
    })
    .catch((error) => {
      console.error(`There has been a problem when fetching "${url}":`, error);
      if (typeof errorCallback == "function") {
        errorCallback(error);
      }
    });
}

function setVariantStylesheet(variant) {
  document.getElementById("current-variant-stylesheet").href =
    `./assets/theme-variant-${variant}.css`;
}

const copyText = async (val) => {
  if (navigator.clipboard && navigator.permissions) {
    await navigator.clipboard.writeText(val);
  } else {
    const textArea = document.createElement("textArea");
    textArea.value = val;
    textArea.style.width = 0;
    textArea.style.position = "fixed";
    textArea.style.left = "-999px";
    textArea.style.top = "10px";
    textArea.setAttribute("readonly", "readonly");
    document.body.appendChild(textArea);

    textArea.select();
    document.execCommand("copy");
    document.body.removeChild(textArea);
  }
};

const formatMB = (n) => {
  return (n ? (n / 1e6).toPrecision(3) : "?") + "MB";
};

const isSupported = () => {
  let error_information = [];
  if (typeof WebAssembly !== "object") {
    error_information.push(
      "WebAssembly is not available in current browser environment.",
    );
  } else {
    const source = Uint8Array.from([
      0, 97, 115, 109, 1, 0, 0, 0, 1, 5, 1, 96, 0, 1, 123, 3, 2, 1, 0, 7, 8, 1,
      4, 116, 101, 115, 116, 0, 0, 10, 15, 1, 13, 0, 65, 0, 253, 17, 65, 0, 253,
      17, 253, 186, 1, 11,
    ]);
    if (
      typeof WebAssembly.validate !== "function" ||
      !WebAssembly.validate(source)
    ) {
      error_information.push(
        "WebAssembly.validate is not available in current browser environment, or WebAssembly.validate fails to recognize a valid WASM.",
      );
    }
  }
  if (typeof Atomics !== "object") {
    error_information.push(
      "Atomics is not available in current browser environment.",
    );
  }
  if (typeof SharedArrayBuffer !== "function") {
    error_information.push(
      "SharedArrayBuffer is not available in current browser environment.",
    );
  }
  if (typeof FileReader === "undefined") {
    error_information.push(
      "FileReader is not available in current browser environment.",
    );
  }
  if (typeof WebSocket === "undefined") {
    error_information.push(
      "WebSocket is not available in current browser environment.",
    );
  }
  if (typeof localStorage === "undefined") {
    error_information.push(
      "localStorage is not available in current browser environment.",
    );
  }
  if (typeof Worker === "undefined") {
    error_information.push(
      "Worker is not available in current browser environment.",
    );
  }
  return {
    supported: error_information.length == 0,
    error_messages: error_information,
  };
};

const RequestProgress = ({ attrs: { url, onFinishDownload } }) => {
  let state = "INIT"; // 'LOADING', 'DONE', 'FAILED'
  let loaded = 0;
  let total = 0;

  const oninit = () => {
    state = "LOADING";
    m.request({
      url: url,
      method: "GET",
      responseType: "arraybuffer",
      headers: { Accept: "*/*" },
      config: (xhr) => {
        xhr.onprogress = (e) => {
          // TODO:
          // When gzip compressed, the value of "loaded/total" gets messed up.
          // On Chrome, "loaded" is the value after decompression, but on the other hand,
          // On Firefox, "loaded" is the value before decompression.
          loaded = e.loaded;
          total =
            e.total ||
            Number(e.target.getResponseHeader("x-decompressed-content-length"));
          m.redraw();
        };
      },
    }).then(
      (response) => {
        state = "DONE";
        onFinishDownload(response);
      },
      (e) => {
        console.error(e);
        state = "FAILED";
        onFinishDownload(null);
      },
    );
  };

  const view = () => {
    const fraction =
      total == -1 ? `?MB/?MB` : `${formatMB(loaded)}/${formatMB(total)}`;
    return m("span", [
      `${fraction} [${state}] `,
      m(
        "span",
        {
          style: "cursor: pointer;",
          onclick: () =>
            window.alert(
              "On some browsers, download size might look contradictory due to file compression.",
            ),
        },
        "[?]",
      ),
    ]);
  };

  return { oninit, view };
};

const LoadVariantSettings = (side, clientdata) => {
  function StartLoad(data, dispatchevent) {
    if (typeof data == "string") {
      let rawText = data
        .replace(/\r\n/g, "\n")
        .replace(/\r/g, "\n")
        .split("\n");
      let i = 0;
      let variantdescriptionitem = [];
      for (i = 0; i < rawText.length; i++) {
        if (rawText[i].length < 1 || rawText[i].charAt(0) == "#") {
          continue;
        }
        variantdescriptionitem = rawText[i].split("|");
        if (variantdescriptionitem.length != 5) {
          console.warn(
            `At line ${i + 1} in variantsettings.txt: Syntax error.`,
          );
          continue;
        }
        if (variantsettings[0].includes(variantdescriptionitem[0])) {
          console.warn(
            `At line ${i + 1} in variantsettings.txt: Variant ${variantdescriptionitem[0]} already exists.`,
          );
          continue;
        }
        if (variantdescriptionitem[0] == "") {
          console.warn(
            `At line ${i + 1} in variantsettings.txt: Variant ID must not be null.`,
          );
          continue;
        }
        if (variantdescriptionitem[1] == "") {
          console.warn(
            `At line ${i + 1} in variantsettings.txt: Variant type must not be null.`,
          );
          continue;
        }
        if (variantdescriptionitem[2] == "") {
          console.warn(
            `At line ${i + 1} in variantsettings.txt: Variant name must not be null.`,
          );
          continue;
        }
        variantsettings[0].push(variantdescriptionitem[0]);
        variantsettings[1].push(variantdescriptionitem[1]);
        variantsettings[2].push(variantdescriptionitem[2]);
        variantsettings[3].push(variantdescriptionitem[3]);
        variantsettings[4].push(variantdescriptionitem[4]);
      }
      //console.log(variantsettings);
    } else {
      console.error(`Bad data type from variantsettings.txt: ${typeof data}`);
    }
    if (dispatchevent) {
      document.dispatchEvent(new Event("variantsettingsloaded"));
    }
  }
  if (side == "server") {
    getFileFromServer("./variantsettings.txt", (res) => {
      console.log("res3:", res);
      StartLoad(res, true);
    });
  } else if (side == "client") {
    StartLoad(clientdata, false);
  }
};

const LoadThemes = () => {
  themes = [[], [], []];
  themenames = [[], []];
  function StartLoad(data, namedata) {
    let rawText;
    let themesettings;
    if (typeof data == "string") {
      data = data.replace(/\r\n/g, "\n");
      data = data.replace(/\r/g, "\n");
      rawText = data.split("\n");
      console.log("theme data:", rawText);
      let i = 0;
      let j = 0;
      let css_name = "";
      let index = 0;
      let require_list = [];
      themesettings = [];
      let apply_to_all_list = [];
      let loaded_css_list = [];
      let require_board_list = [];
      let board_apply_to_all_list = [];
      let themeavailable = [];
      let boardthemeavailable = [];
      let link = null;
      for (i = 0; i < rawText.length; i++) {
        if (rawText[i].length < 1 || rawText[i].charAt(0) == "#") {
          continue;
        }
        themesettings = rawText[i].trim().split("|");
        if (themesettings.length != 3) {
          console.warn(`At line ${i + 1} in themes.txt: Bad syntax\n`);
          continue;
        }
        themeavailable = themesettings[1].split(",");
        boardthemeavailable = themesettings[2].split(",");
        if (themeavailable.length == 1 && themeavailable[0] == "") {
          themeavailable = [];
        }
        if (boardthemeavailable.length == 1 && boardthemeavailable[0] == "") {
          boardthemeavailable = [];
        }
        if (
          (themesettings[1].length < 1 && themesettings[2].length < 1) ||
          themeavailable.includes("") ||
          boardthemeavailable.includes("")
        ) {
          console.warn(
            `At line ${i + 1} in themes.txt: Piece and Board style names must not be both null or contain null element\n`,
          );
          continue;
        }
        if (themesettings[1].length > 0) {
          require_list = themeavailable.filter((element) => {
            return element.charAt(0) == "@";
          });
          themeavailable = themeavailable.filter((element) => {
            return element.charAt(0) != "@";
          });
          for (j = 0; j < require_list.length; j++) {
            if (themes[0].includes(require_list[j].substring(1))) {
              index = themes[0].indexOf(require_list[j].substring(1));
              themeavailable = themeavailable.concat(themes[1][index]);
            } else {
              console.warn(
                `At line ${i + 1} in themes.txt: Variant ${require_list[
                  j
                ].substring(
                  1,
                )} has not been defined yet. You need to put it before this line.\n`,
              );
            }
          }
          themeavailable = uniqArr(themeavailable);
        }
        if (themesettings[2].length > 0) {
          require_board_list = boardthemeavailable.filter((element) => {
            return element.charAt(0) == "@";
          });
          boardthemeavailable = boardthemeavailable.filter((element) => {
            return element.charAt(0) != "@";
          });
          for (j = 0; j < require_board_list.length; j++) {
            if (themes[0].includes(require_board_list[j].substring(1))) {
              index = themes[0].indexOf(require_board_list[j].substring(1));
              boardthemeavailable = boardthemeavailable.concat(
                themes[2][index],
              );
            } else {
              console.warn(
                `At line ${i + 1} in themes.txt: Variant ${require_board_list[
                  j
                ].substring(
                  1,
                )} has not been defined yet. You need to put it before this line.\n`,
              );
            }
          }
          boardthemeavailable = uniqArr(boardthemeavailable);
        }
        if (themesettings[0] == "*") {
          if (themesettings[1].length > 0) {
            apply_to_all_list = apply_to_all_list.concat(themeavailable);
          }
          if (themesettings[2].length > 0) {
            board_apply_to_all_list =
              board_apply_to_all_list.concat(boardthemeavailable);
          }
        } else if (themes[0].includes(themesettings[0])) {
          if (themesettings[1].length > 0) {
            index = themes[0].indexOf(themesettings[0]);
            themes[1][index] = uniqArr(themes[1][index].concat(themeavailable));
          }
          if (themesettings[2].length > 0) {
            index = themes[0].indexOf(themesettings[0]);
            themes[2][index] = uniqArr(
              themes[2][index].concat(boardthemeavailable),
            );
          }
        } else {
          themeavailable = uniqArr(themeavailable.concat(apply_to_all_list));
          boardthemeavailable = uniqArr(
            boardthemeavailable.concat(board_apply_to_all_list),
          );
          themes[0].push(themesettings[0]);
          themes[1].push(themeavailable);
          themes[2].push(boardthemeavailable);
        }
      }
      for (i = 0; i < themes[0].length; i++) {
        for (j = 0; j < themes[1][i].length; j++) {
          css_name = "theme-piece-" + themes[1][i][j];
          if (loaded_css_list.includes(css_name)) {
            continue;
          }
          loaded_css_list.push(css_name);
          link = document.createElement("link");
          link.setAttribute("rel", "stylesheet");
          link.setAttribute("href", "./assets/" + css_name + ".css");
          document.head.appendChild(link);
        }
        for (j = 0; j < themes[2][i].length; j++) {
          css_name = "theme-board-" + themes[2][i][j];
          if (loaded_css_list.includes(css_name)) {
            continue;
          }
          loaded_css_list.push(css_name);
          link = document.createElement("link");
          link.setAttribute("rel", "stylesheet");
          link.setAttribute("href", "./assets/" + css_name + ".css");
          document.head.appendChild(link);
        }
      }

      // Needs to be after piece and board stylesheets to override them.
      css_name = "theme-variant-";
      if (!loaded_css_list.includes(css_name)) {
        loaded_css_list.push(css_name);
        link = document.createElement("link");
        link.setAttribute("rel", "stylesheet");
        link.setAttribute("href", "./assets/" + css_name + ".css");
        link.setAttribute("id", "current-variant-stylesheet");
        document.head.appendChild(link);
      }

      console.log(themes);
    } else {
      console.error(`Bad data type from themes.txt: ${typeof data}`);
    }

    if (typeof namedata == "string") {
      namedata = namedata.replace(/\r\n/g, "\n");
      namedata = namedata.replace(/\r/g, "\n");
      rawText = namedata.split("\n");
      console.log("theme name:", rawText);
      for (i = 0; i < rawText.length; i++) {
        if (rawText[i].length < 1 || rawText[i].charAt(0) == "#") {
          continue;
        }
        themesettings = rawText[i].trim().split("|");
        if (themesettings.length != 2) {
          console.warn(`At line ${i + 1} in themename.txt: Bad syntax\n`);
          continue;
        }
        themenames[0].push(themesettings[0]);
        themenames[1].push(themesettings[1]);
      }

      console.log(themenames);
    } else {
      console.error(`Bad data type from themename.txt: ${typeof namedata}`);
    }

    document.dispatchEvent(new Event("themesloaded"));
  }
  getFileFromServer("./themes.txt", (res) => {
    console.log("res:", res);
    getFileFromServer(
      "./themenames.txt",
      (res2) => {
        console.log("res2:", res2);
        StartLoad(res, res2);
      },
      () => {
        console.warn("themes.txt load failed.");
        getFileFromServer("./themenames.txt", (res2) => {
          console.log("res2:", res2);
          StartLoad("", res2);
        });
      },
    );
  });
};

const LoadUIThemes = () => {
  let received = 0;
  let totalreceives = 0;
  function ClearInvalid() {
    let i = 0;
    for (i = 0; i < uithemes[0].length; i++) {
      if (!uithemes[1][i].Initialized) {
        uithemes[0].splice(i, 1);
        uithemes[1].splice(i, 1);
        i--;
      }
    }
  }
  function StartLoad(data) {
    if (typeof data == "string") {
      let i = 0;
      let j = 0;
      let rawText = data
        .replace(/\r\n/g, "\n")
        .replace(/\r/g, "\n")
        .split("\n");
      for (i = 0; i < rawText.length; i++) {
        if (rawText[i] == "" || rawText[i].startsWith("#")) {
          continue;
        }
        let uithemesettings = rawText[i].split("|");
        if (uithemesettings.length < 2 && uithemesettings.length > 4) {
          console.warn(`At line ${i + 1} in uithemes.txt: Bad syntax\n`);
          continue;
        }
        if (uithemesettings[0] == "" || uithemesettings[1] == "") {
          console.warn(
            `At line ${i + 1} in uithemes.txt: ID and display name must not be empty.\n`,
          );
          continue;
        }
        if (uithemes[0].indexOf(uithemesettings[0]) >= 0) {
          console.warn(
            `At line ${i + 1} in uithemes.txt: Theme ${uithemesettings[0]} already exists.\n`,
          );
          continue;
        }
        let multiuithemedurations = [];
        let canvasjs = "";
        let canvasframerate = 50;
        if (uithemesettings.length == 3 || uithemesettings.length == 4) {
          let durations = uithemesettings[2].split(",");
          if (uithemesettings[2] == "" && uithemesettings.length == 3) {
            console.warn(
              `At line ${i + 1} in uithemes.txt: Bad syntax for sub-theme duration.\n`,
            );
            continue;
          }
          let haserror = false;
          if (uithemesettings[2] != "") {
            for (j = 0; j < durations.length; j++) {
              if (isNaN(parseInt(durations[j]))) {
                console.warn(
                  `At token ${j + 1} of sub-theme in line ${i + 1} in uithemes.txt: Sub-theme duration must be a positive integer.\n`,
                );
                haserror = true;
                break;
              } else {
                let durationlength = parseInt(durations[j]);
                if (durationlength < 1) {
                  console.warn(
                    `At token ${j + 1} of sub-theme in line ${i + 1} in uithemes.txt: Sub-theme duration must be a positive integer.\n`,
                  );
                  haserror = true;
                  break;
                }
                multiuithemedurations.push(durationlength);
              }
            }
          }
          if (haserror) {
            continue;
          }
          if (uithemesettings.length == 4) {
            let canvasoption = uithemesettings[3].split(",");
            if (canvasoption.length != 2) {
              console.warn(
                `At line ${i + 1} in uithemes.txt: Bad syntax for canvas settings.\n`,
              );
              continue;
            }
            if (canvasoption[0] == "") {
              console.warn(
                `At line ${i + 1} in uithemes.txt: Canvas worker name must not be null.\n`,
              );
              continue;
            } else {
              canvasjs = canvasoption[0];
            }
            let frameratenum = parseInt(canvasoption[1]);
            if (isNaN(frameratenum) || frameratenum < 1) {
              console.warn(
                `At line ${i + 1} in uithemes.txt: Frame rate must be a positive integer.\n`,
              );
              continue;
            } else {
              canvasframerate = frameratenum;
            }
          }
        }
        let uithemeobj = new UIThemeObject(
          uithemesettings[0],
          uithemesettings[1],
        );
        uithemeobj.SetStyleDurations(multiuithemedurations);
        if (canvasjs != "") {
          try {
            uithemeobj.SetCanvasWorker(canvasjs);
          } catch (error) {
            console.error("Error loading worker:", error);
            console.warn(
              `At line ${i + 1} in uithemes.txt: Unable to initialize worker.\n`,
            );
            continue;
          }
          uithemeobj.SetCanvasFrameRate(canvasframerate);
        }
        uithemes[0].push(uithemesettings[0]);
        uithemes[1].push(uithemeobj);
      }
      totalreceives = uithemes[0].length;
      for (i = 0; i < uithemes[0].length; i++) {
        ((index) => {
          uithemes[1][index].Initialize(
            () => {
              received++;
              uithemes[1][index].GetCurrentThemeIndexFromLocalStorage();
              if (received >= totalreceives) {
                ClearInvalid();
                document.dispatchEvent(new Event("uithemesparsed"));
              }
            },
            () => {
              received++;
              if (received >= totalreceives) {
                ClearInvalid();
                document.dispatchEvent(new Event("uithemesparsed"));
              }
            },
          );
        })(i);
      }
    } else {
      console.error(`Bad data type from uithemes.txt: ${typeof data}`);
    }
  }
  getFileFromServer(
    "./uithemes.txt",
    (res) => {
      StartLoad(res);
    },
    () => {
      console.error(
        "Failed to load uithemes.txt. UI themes are not available.",
      );
    },
  );
};

function ApplyUIThemeStyleNode(HTMLStyleElementObject) {
  if (HTMLStyleElementObject instanceof HTMLStyleElement) {
    const pagebackground = document.getElementById("pagebackground");
    const htmlComputedStyle = window.getComputedStyle(pagebackground);
    const BGBefore = htmlComputedStyle.backgroundImage;
    const BGBeforeSize = htmlComputedStyle.backgroundSize;
    const BGBeforeRepeat = htmlComputedStyle.backgroundRepeat;
    const BGBeforePosition = htmlComputedStyle.backgroundPosition;
    const BGBeforeAttachment = htmlComputedStyle.backgroundAttachment;
    if (currentuicss != null) {
      document.head.removeChild(currentuicss);
    }
    currentuicss = HTMLStyleElementObject;
    document.head.appendChild(currentuicss);
    // The theme stylesheet loaded early in <head> (to avoid a light
    // flash before the theme system starts) is no longer needed.
    const earlytheme = document.getElementById("early-ui-theme");
    if (earlytheme) {
      earlytheme.remove();
    }
    const htmlComputedStyleAfter = window.getComputedStyle(pagebackground);
    const BGAfter = htmlComputedStyleAfter.backgroundImage;
    const BGAfterSize = htmlComputedStyleAfter.backgroundSize;
    const BGAfterRepeat = htmlComputedStyleAfter.backgroundRepeat;
    const BGAfterPosition = htmlComputedStyleAfter.backgroundPosition;
    const BGAfterAttachment = htmlComputedStyleAfter.backgroundAttachment;

    const tempbackground1 = document.getElementById("tempbackground1");
    const tempbackground2 = document.getElementById("tempbackground2");
    let tmpbg1, tmpbg2;

    if (tempbackground1.classList.contains("show")) {
      tmpbg1 = tempbackground1;
      tmpbg2 = tempbackground2;
    } else {
      tmpbg1 = tempbackground2;
      tmpbg2 = tempbackground1;
    }

    tmpbg1.style.backgroundImage = BGBefore;
    tmpbg1.style.backgroundSize = BGBeforeSize;
    tmpbg1.style.backgroundRepeat = BGBeforeRepeat;
    tmpbg1.style.backgroundPosition = BGBeforePosition;
    tmpbg1.style.backgroundAttachment = BGBeforeAttachment;
    tmpbg1.style.zIndex = "-51";

    tmpbg2.style.backgroundImage = BGAfter;
    tmpbg2.style.backgroundSize = BGAfterSize;
    tmpbg2.style.backgroundRepeat = BGAfterRepeat;
    tmpbg2.style.backgroundPosition = BGAfterPosition;
    tmpbg2.style.backgroundAttachment = BGAfterAttachment;
    tmpbg2.style.zIndex = "-52";

    tmpbg1.classList.remove("show");
    tmpbg2.classList.add("show");

    if (BGBefore != "none" && BGAfter != "none") {
      pagebackground.style.opacity = "0";
    } else if (BGBefore != "none") {
    } else if (BGAfter != "none") {
      pagebackground.style.opacity = "0";
    }
    setTimeout(() => {
      pagebackground.style.opacity = "";
    }, 1000);
  } else {
    throw TypeError(
      "ApplyUIThemeStyleNode(HTMLStyleElementObject:HTMLStyleElement)",
    );
  }
}

function getThemeName(themeid) {
  if (typeof themeid != "string") {
    return null;
  }
  let index = themenames[0].indexOf(themeid);
  if (index < 0) {
    return themeid + " ⚠";
  } else {
    return themenames[1][index];
  }
}

function getVariantType(variant) {
  if (typeof variant != "string") {
    return null;
  }
  let index = variantsettings[0].indexOf(variant);
  if (index < 0) {
    return "<|NC|>";
  } else {
    return variantsettings[1][index];
  }
}

function getVariantName(variant, useplaceholder, showid) {
  if (
    typeof variant != "string" ||
    typeof useplaceholder != "boolean" ||
    typeof showid != "boolean"
  ) {
    return null;
  }
  let index = variantsettings[0].indexOf(variant);
  if (index < 0) {
    if (useplaceholder) {
      return variant;
    } else {
      return undefined;
    }
  } else {
    if (showid) {
      return variantsettings[2][index] + ` (${variant})`;
    } else {
      return variantsettings[2][index];
    }
  }
}

function getVariantDescription(variant, useplaceholder) {
  if (typeof variant != "string" || typeof useplaceholder != "boolean") {
    return null;
  }
  let index = variantsettings[0].indexOf(variant);
  if (index < 0) {
    if (useplaceholder) {
      return variant;
    } else {
      return undefined;
    }
  } else {
    return variantsettings[3][index];
  }
}

function getVariantWikiPageURL(variant, useplaceholder) {
  if (typeof variant != "string" || typeof useplaceholder != "boolean") {
    return null;
  }
  let index = variantsettings[0].indexOf(variant);
  if (index < 0) {
    if (useplaceholder) {
      return "";
    } else {
      return undefined;
    }
  } else {
    return variantsettings[4][index];
  }
}

// Responsive board sizing: scales the chessground wrapper (and pockets)
// to the available width of the board column and notifies chessground.
let lastBoardSizeKey = "";
function updateBoardSize(force) {
  const container = document.getElementById("chessground-container-div");
  const wrap = document.getElementById("chessground-board");
  const column = document.getElementById("boardcol");
  if (!container || !wrap || !column) {
    return;
  }
  let files = 8;
  let ranks = 8;
  let i = 0;
  for (i = 0; i < container.classList.length; i++) {
    const match = /^board([0-9]+)x([0-9]+)$/.exec(container.classList[i]);
    if (match) {
      files = parseInt(match[1]);
      ranks = parseInt(match[2]);
      break;
    }
  }
  const pockets = container.classList.contains("pockets");
  const maxdim = pockets ? 512 : 640;
  // Board themes with non-square squares (e.g. shogi boards) define
  // their natural size in CSS, which the inline size below overrides.
  // Read it without the inline size to keep the theme's aspect ratio,
  // otherwise the board background is cropped and no longer lines up
  // with the pieces. The chessground default of 640x640 means square
  // squares. The max-width is lifted as well, since on narrow screens
  // it would clamp the natural width and distort the ratio.
  const inlinewidth = wrap.style.width;
  const inlineheight = wrap.style.height;
  wrap.style.width = "";
  wrap.style.height = "";
  wrap.style.maxWidth = "none";
  wrap.style.width = inlinewidth;
  wrap.style.height = inlineheight;
  wrap.style.maxWidth = "";
  const cg_board = wrap.getElementsByTagName("cg-board")[0];
  // square_aspect_ratio = square_width / square_height
  let square_aspect_ratio = cg_board
    ? parseFloat(
        window
          .getComputedStyle(cg_board)
          .getPropertyValue("--square-aspect-ratio"),
      ) || 1
    : 1;
  let aspect = (files / ranks) * square_aspect_ratio;
  const w0 = aspect < 1 ? maxdim * aspect : maxdim;
  const h0 = aspect < 1 ? maxdim : maxdim / aspect;
  const columnstyle = window.getComputedStyle(column);
  const avail =
    column.clientWidth -
    parseFloat(columnstyle.paddingLeft) -
    parseFloat(columnstyle.paddingRight);
  const availheight = Math.max(280, window.innerHeight - 300);
  let scale = Math.min(1, avail / w0, availheight / h0);
  if (!(scale > 0)) {
    scale = 1;
  }
  scale = Math.max(scale, 0.3);
  const w = Math.round(w0 * scale);
  const h = Math.round(h0 * scale);
  const key = `${files}x${ranks}:${pockets}:${w}x${h}`;
  if (!force && key == lastBoardSizeKey) {
    return;
  }
  lastBoardSizeKey = key;
  wrap.style.width = `${w}px`;
  wrap.style.height = `${h}px`;
  const pocketwraps = container.querySelectorAll(
    ".cg-wrap.pocket-top, .cg-wrap.pocket-bottom",
  );
  for (i = 0; i < pocketwraps.length; i++) {
    pocketwraps[i].style.width = `${w}px`;
  }
  document.body.dispatchEvent(new Event("chessground.resize"));
  const cgcontainer = wrap.getElementsByTagName("cg-container")[0];
  if (cgcontainer) {
    ["pocket-top", "pocket-bottom"].forEach((id) => {
      const pocket = document.getElementById(id);
      if (pocket && pocket.style.getPropertyValue("--pocketLength")) {
        pocket.style.setProperty("--cg-width", cgcontainer.style.width);
        pocket.style.setProperty("--cg-height", cgcontainer.style.height);
      }
    });
  }
}

function updateInfoDivWidth() {
  document.body.style.overflowX = "hidden";
  updateBoardSize(false);
}

document.addEventListener("onpageload", () => {
  const container = document.getElementById("chessground-container-div");
  const column = document.getElementById("boardcol");
  if (window.ResizeObserver && column) {
    new ResizeObserver(() => {
      updateBoardSize(false);
    }).observe(column);
  }
  if (window.MutationObserver && container) {
    new MutationObserver(() => {
      window.setTimeout(() => {
        updateBoardSize(true);
      }, 0);
    }).observe(container, {
      attributes: true,
      attributeFilter: ["class"],
    });
  }
  window.setTimeout(() => {
    updateBoardSize(true);
  }, 50);
  // Clicking a move in the move list displays that position on the
  // main board (the same navigation as the previous/next buttons).
  // Context menu (right click / long press) on a move with the PGN tools,
  // similar to the lichess analysis board. The move is made the current
  // move first, then the chosen tool button is clicked.
  const moveMenuItems = [
    ["movetree-settomainbranch", "Promote variation"],
    ["movetree-setasmainline", "Make main line"],
    ["movetree-cut", "Delete from here"],
    ["movetree-cutbranch", "Delete this variation"],
    ["movetree-removevariations", "Delete other variations"],
    ["movetree-crop", "Start game here"],
    ["movetree-cropbranch", "Keep only this line"],
    ["movetree-hideshow", "Hide / show following moves"],
    ["movetree-textbefore", "Comment before move"],
    ["movetree-textafter", "Comment after move"],
    ["movetree-symbol", "Symbols (!, ?, …)"],
    ["movetree-markers", "Save board markers"],
    ["movetree-termination", "Result / termination"],
    ["movetree-uncomment", "Remove comments"],
  ];
  const moveMenu = document.createElement("div");
  moveMenu.id = "movecontextmenu";
  moveMenu.className = "ctxmenu";
  moveMenu.hidden = true;
  moveMenu.oncontextmenu = function (e) {
    e.preventDefault();
  };
  moveMenuItems.forEach(([id, label]) => {
    const item = document.createElement("button");
    item.type = "button";
    item.textContent = label;
    item.addEventListener("click", (event) => {
      event.stopPropagation();
      moveMenu.hidden = true;
      const tool = document.getElementById(id);
      if (tool && !tool.disabled) {
        tool.click();
      }
    });
    moveMenu.appendChild(item);
  });
  document.body.appendChild(moveMenu);
  const hideMoveMenu = () => {
    moveMenu.hidden = true;
  };
  document.addEventListener("click", hideMoveMenu);
  document.addEventListener("keydown", (event) => {
    if (event.key == "Escape") {
      hideMoveMenu();
    }
  });
  window.addEventListener("scroll", hideMoveMenu, true);
  const openMoveMenu = (element, x, y) => {
    const moveinput = document.getElementById("move");
    const setposition = document.getElementById("setpos");
    const isgamestarted = document.getElementById("isgamestarted");
    if (
      !moveinput ||
      !setposition ||
      setposition.disabled ||
      (isgamestarted && isgamestarted.checked)
    ) {
      return;
    }
    element.click();
    const miniboard = document.getElementById("chessground-mini");
    if (miniboard && !miniboard.locked) {
      miniboard.style.display = "none";
    }
    moveMenu.hidden = false;
    const rect = moveMenu.getBoundingClientRect();
    const left = Math.max(8, Math.min(x, window.innerWidth - rect.width - 8));
    const top = Math.max(8, Math.min(y, window.innerHeight - rect.height - 8));
    moveMenu.style.left = `${left}px`;
    moveMenu.style.top = `${top}px`;
  };
  let longPressTimer = null;
  const movelist = document.getElementById("pgn-container");
  if (movelist) {
    // movelist.addEventListener("click", (event) => {
    //   const element = event.target.closest(".position-display-label");
    //   const isgamestarted = document.getElementById("isgamestarted");
    //   if (
    //     !element ||
    //     element.moves === undefined ||
    //     (isgamestarted && isgamestarted.checked)
    //   ) {
    //     return;
    //   }
    //   const moveinput = document.getElementById("move");
    //   const setposition = document.getElementById("setpos");
    //   if (!moveinput || !setposition || setposition.disabled) {
    //     return;
    //   }
    //   moveinput.value = element.moves;
    //   setposition.click();
    //   // The move list click also opens the preview mini board; the
    //   // main board now shows the position, so close the preview.
    //   // const miniboard = document.getElementById("chessground-mini");
    //   // if (miniboard && !miniboard.locked) {
    //   //   miniboard.style.display = "none";
    //   // }
    // });
    movelist.addEventListener("contextmenu", (event) => {
      const element = event.target.closest(".position-display-label");
      if (!element) {
        return;
      }
      event.preventDefault();
      if (longPressTimer) {
        window.clearTimeout(longPressTimer);
        longPressTimer = null;
      }
      openMoveMenu(element, event.clientX, event.clientY);
    });
    movelist.addEventListener(
      "touchstart",
      (event) => {
        const element = event.target.closest(".position-display-label");
        if (!element || event.touches.length != 1) {
          return;
        }
        const touch = event.touches[0];
        longPressTimer = window.setTimeout(() => {
          longPressTimer = null;
          openMoveMenu(element, touch.clientX, touch.clientY);
        }, 500);
      },
      { passive: true },
    );
    ["touchend", "touchmove", "touchcancel"].forEach((name) => {
      movelist.addEventListener(
        name,
        () => {
          if (longPressTimer) {
            window.clearTimeout(longPressTimer);
            longPressTimer = null;
          }
        },
        { passive: true },
      );
    });
  }
});

const getVariantTheme = (variant, is_board_theme) => {
  let stored_data = is_board_theme
    ? localStorage.getItem("UserSelectedBoardTheme")
    : localStorage.getItem("UserSelectedPieceTheme");
  let theme_str = stored_data || "{}";
  let parsed_json = {};
  try {
    parsed_json = JSON.parse(theme_str);
  } catch (e) {
    parsed_json = {};
  }
  let result = parsed_json[variant];
  if (typeof result == "string") {
    return result;
  } else {
    return null;
  }
};

const setVariantTheme = (variant, theme_name, is_board_theme) => {
  let stored_data = is_board_theme
    ? localStorage.getItem("UserSelectedBoardTheme")
    : localStorage.getItem("UserSelectedPieceTheme");
  let theme_str = stored_data || "{}";
  let parsed_json = {};
  if (variant == "") {
    return;
  }
  try {
    parsed_json = JSON.parse(theme_str);
  } catch (e) {
    parsed_json = {};
  }
  parsed_json[variant] = theme_name;
  if (is_board_theme) {
    localStorage.setItem("UserSelectedBoardTheme", JSON.stringify(parsed_json));
  } else {
    localStorage.setItem("UserSelectedPieceTheme", JSON.stringify(parsed_json));
  }
};

const App = () => {
  let stockfish = null;
  let stockfish_state = "INIT"; // 'READY', 'FAILED'
  let engineoutput = "";
  let first_engine_output = "";
  let second_engine_output = "";
  let analysis_engine_output = "";
  let show_dests = true;
  let adjudicate = true;
  let analysis_mode = false;
  let play_white = false;
  let play_black = false;
  let play_move = false;
  let review_mode = false;
  let board_setup_mode = false;
  let advanced_time_control = false;
  let during_play = false;
  let game_started = false;
  let select_move_dialog = false;
  let in_browser_fsf_hash = 16;
  let in_browser_fsf_skill = 20;
  let random_mover_white = false;
  let random_mover_black = false;
  let advanced_pgn_mode = true;
  let white_start_time = 0;
  let black_start_time = 0;
  let white_remaining_time = 0;
  let black_remaining_time = 0;
  let white_moving_time_list = [];
  let black_moving_time_list = [];
  let white_time_gain = 0;
  let black_time_gain = 0;
  let white_timer_type = "infinite";
  let black_timer_type = "infinite";
  let timer_interval = 100;
  let white_byoyomi_time_per_period = 0;
  let black_byoyomi_time_per_period = 0;
  let white_byoyomi_period_count = 0;
  let black_byoyomi_period_count = 0;
  let white_remaining_byoyomi_periods = 0;
  let black_remaining_byoyomi_periods = 0;
  let white_time_margin = 0;
  let black_time_margin = 0;
  let timeout_margin = 500;
  let previous_mover = "";
  let white_time_exceeded = false;
  let black_time_exceeded = false;
  let previous_reality_time = -1;
  let move_finish_timer_updating = false;
  let changing_variant_type = false;
  let clear_log = true;
  let game_list = [];
  let throttle_threshold = 400; //in milliseconds, increase this if the GUI lags
  let engine_match_mode = false;
  let fischer_random_mode = false;
  let during_engine_match = false;
  let engine_match_total_game_count = 0;
  let engine_match_played_game_count = 0;
  let engine_match_white_wins = 0;
  let engine_match_black_wins = 0;
  let engine_match_draws = 0;
  let engine_match_game_list = [];
  let timer;

  let websocket;
  let websocket_status = "Unestablished";

  let return_early = false;

  let variants = [];
  let varianttypes = [];

  let engine_list = [];

  let piece_palette_orientation = "white";
  let board_orientation = "white";

  let use_integer_inputs = false;

  let mover_color_scheme = "chess";

  let show_evaluation_history_graph = false;

  const default_start_time = 300000;
  const default_time_increment = 3000;
  const default_byoyomi_periods = 3;
  const default_byoyomi_period_length = 30000;
  const default_timeout_margin = 0;
  const default_movetime = 500;
  const default_depth = 12;
  const default_nodes = 1000000;

  document.addEventListener("gameend", (event) => {
    finishGame(event.detail.result, event.detail.reason);
    if (engine_match_mode && during_engine_match) {
      if (event.detail.result == "1-0") {
        engine_match_white_wins++;
      } else if (event.detail.result == "0-1") {
        engine_match_black_wins++;
      } else if (event.detail.result == "1/2-1/2") {
        engine_match_draws++;
      }
      engine_match_played_game_count++;
      document.getElementById("enginematchinfo").innerText =
        `Games played: ${engine_match_played_game_count} | Total games to play: ${engine_match_total_game_count} | First engine (WHITE) wins: ${engine_match_white_wins} | Second engine (BLACK) wins: ${engine_match_black_wins} | Draws: ${engine_match_draws}`;
      let info = fgs.GetCurrentGameInformation(window.ffishlib);
      engine_match_game_list.push(
        new fgs.Game(
          info.Variant,
          info.FEN,
          info.UCIMoves,
          info.Result,
          "Fairy-Stockfish Playground engine match",
          info.Site,
          info.Date,
          engine_match_played_game_count,
          info.FirstPlayerName,
          info.SecondPlayerName,
          0,
          0,
          "0000",
          "0000",
          0.0,
          info.Termination,
          fischer_random_mode,
        ),
      );
      if (engine_match_played_game_count < engine_match_total_game_count) {
        setTimeout(() => {
          document.getElementById("restart").click();
          play_white = true;
          play_black = true;
          if (advanced_time_control) {
            setTimeout(() => {
              document.getElementById("gamestart").click();
            }, 500);
          } else {
            setTimeout(() => {
              document.getElementById("set").click();
            }, 500);
          }
        }, 500);
      } else {
        setTimeout(() => {
          document.getElementById("stop").click();
        }, 500);
      }
    }
  });

  const checkconnectionnumber = parseInt(Math.random() * 100000);
  let wsport = window.location.port;
  if (wsport == "") {
    wsport = 5001;
  } else {
    wsport = +wsport + 1;
  }

  const connectToWebSocketServer = (port, callbackfn) => {
    let i = 0;
    for (i = 0; i < fge.WebSocketReconnectionTime; i++) {
      try {
        websocket_status = "CONNECTING";
        websocket = new WebSocket("ws://localhost:" + port.toString());

        websocket.addEventListener("open", function (event) {
          websocket.send(`CONNECT\x10${checkconnectionnumber}`);
        });

        websocket.addEventListener("message", function (event) {
          if (typeof event.data != "string") {
            console.error(
              `%c WebSocket %c ERROR %c Received bad data type from server: ${typeof event.data}`,
              "color: #fff; background: #5f5f5f",
              "color: #fff; background: #f03a17",
              "",
            );
            websocket.close();
            websocket_status = "ERROR";
            const binenginediv = document.getElementById("binengineinput");
            if (binenginediv) {
              binenginediv.style.display = "none";
            }
            fge.state.first_engine = null;
            fge.state.second_engine = null;
            fge.state.analysis_engine = null;
            return;
          }
          let msg = event.data.split("|");
          if (websocket_status == "CONNECTING") {
            if (event.data == `${checkconnectionnumber}`) {
              console.log(
                `%c WebSocket %c CONNECTED %c WebSocket connection established.`,
                "color: #fff; background: #5f5f5f",
                "color: #fff; background: #4bc729",
                "",
              );
              websocket_status = "CONNECTED";
              websocket.send("READYOK");
              const binenginediv = document.getElementById("binengineinput");
              if (binenginediv) {
                binenginediv.hidden = false;
                binenginediv.style.display = "";
              }
            } else {
              console.error(
                `%c WebSocket %c ERROR %c WebSocket Server connection failed: Server returns bad verification code.`,
                "color: #fff; background: #5f5f5f",
                "color: #fff; background: #f03a17",
                "",
              );
              websocket.close();
              websocket_status = "ERROR";
              const binenginediv = document.getElementById("binengineinput");
              if (binenginediv) {
                binenginediv.style.display = "none";
              }
              fge.state.first_engine = null;
              fge.state.second_engine = null;
              fge.state.analysis_engine = null;
            }
          } else if (websocket_status == "CONNECTED") {
            if (msg[0] == "UPDATE_DATA") {
              fge.GetEngineList((data) => {
                engine_list = data;
              }, websocket);
              console.log(engine_list);
            }
          }
        });

        websocket.addEventListener("close", function (event) {
          if (websocket_status == "ERROR") {
            return;
          }
          console.error(
            `%c WebSocket %c CLOSED %c WebSocket Connection Closed.`,
            "color: #fff; background: #5f5f5f",
            "color: #fff; background: #f03a17",
            "",
          );
          console.error(event);
          websocket_status = "CLOSED";
          const binenginediv = document.getElementById("binengineinput");
          if (binenginediv) {
            binenginediv.style.display = "none";
          }
          fge.state.first_engine = null;
          fge.state.second_engine = null;
          fge.state.analysis_engine = null;
          window.alert(
            "WebSocket connection has closed. You will be unable to use binary engines. Try reloading this page to fix this.",
          );
        });

        websocket.addEventListener("error", function (event) {
          websocket_status = "ERROR";
          console.error(
            `%c WebSocket %c ERROR %c Errors occurred during establishing WebSocket connection.`,
            "color: #fff; background: #5f5f5f",
            "color: #fff; background: #f03a17",
            "",
          );
          console.error(event);
          const binenginediv = document.getElementById("binengineinput");
          if (binenginediv) {
            binenginediv.style.display = "none";
          }
          fge.state.first_engine = null;
          fge.state.second_engine = null;
          fge.state.analysis_engine = null;
          window.alert(
            `Errors occurred in WebSocket connection ws://localhost:${port}`,
          );
        });

        break;
      } catch {
        console.warn(
          `%c WebSocket %c WARNING %c Cannot initiate WebSocket connection. Retrying... (${i + 1}/${fge.WebSocketReconnectionTime})`,
          "color: #fff; background: #5f5f5f",
          "color: #fff; background: #ffc83d",
          "",
        );
        continue;
      }
    }
    if (i == fge.WebSocketReconnectionTime) {
      console.error(
        `%c WebSocket %c ERROR %c Cannot initiate WebSocket connection. Binary engine loading feature will be disabled.`,
        "color: #fff; background: #5f5f5f",
        "color: #fff; background: #f03a17",
        "",
      );
      websocket_status = "ERROR";
      window.alert(
        `Cannot initiate WebSocket connection to ws://localhost:${port}. Binary engine loading feature will be disabled.`,
      );
      const binenginediv = document.getElementById("binengineinput");
      if (binenginediv) {
        binenginediv.style.display = "none";
      }
      fge.state.first_engine = null;
      fge.state.second_engine = null;
      fge.state.analysis_engine = null;
    }
  };

  if (window.location.hostname == "localhost") {
    connectToWebSocketServer(wsport);
  } else {
    console.log(
      `%c WebSocket %c PENDING %c Cannot automatically initiate WebSocket connection in online versions. Waiting user action...`,
      "color: #fff; background: #5f5f5f",
      "color: #fff; background: #3f48cc",
      "",
    );
    websocket = null;
    websocket_status = "Unestablished";
    const binenginediv = document.getElementById("binengineinput");
    if (binenginediv) {
      binenginediv.style.display = "none";
    }
    fge.state.first_engine = null;
    fge.state.second_engine = null;
    fge.state.analysis_engine = null;
  }

  const playerColor = (scheme, side) => {
    if (scheme == "chess") {
      return side == "white" ? "White" : "Black";
    } else if (scheme == "janggi") {
      return side == "white" ? "Blue" : "Red";
    } else if (scheme == "shogi") {
      return side == "white" ? "Black" : "White";
    } else if (scheme == "xiangqi") {
      return side == "white" ? "Red" : "Black";
    } else {
      return "Unknown Color";
    }
  };

  const getVariants = () => {
    stockfish.postMessage(`uci`);
  };

  const setVariant = () => {
    play_move = false;
    stop(true);
    const variant = $("#dropdown-variant").value;
    stockfish.postMessage(`ucinewgame`);
    if (variant == "") {
      stockfish.postMessage(`setoption name UCI_Variant value chess`);
    } else {
      stockfish.postMessage(`setoption name UCI_Variant value ${variant}`);
    }
    stockfish.postMessage(
      `setoption name UCI_Chess960 value ${fischer_random_mode}`,
    );
    stockfish.postMessage(`position startpos`);
    if (websocket_status == "CONNECTED") {
      if (fge.state.first_engine instanceof fge.Engine) {
        if (fge.state.first_engine.SetVariant(variant, fischer_random_mode)) {
          document.getElementById("whiteunsupportedvariant").hidden = true;
        } else {
          document.getElementById("whiteunsupportedvariant").hidden = false;
        }
      }
      if (fge.state.second_engine instanceof fge.Engine) {
        if (fge.state.second_engine.SetVariant(variant, fischer_random_mode)) {
          document.getElementById("blackunsupportedvariant").hidden = true;
        } else {
          document.getElementById("blackunsupportedvariant").hidden = false;
        }
      }
      if (fge.state.analysis_engine instanceof fge.Engine) {
        if (
          fge.state.analysis_engine.SetVariant(variant, fischer_random_mode)
        ) {
          document.getElementById("analysisunsupportedvariant").hidden = true;
        } else {
          document.getElementById("analysisunsupportedvariant").hidden = false;
        }
      }
    }
    resetTimer();

    setVariantStylesheet(variant);
  };

  const setFen = (interrupt_ponder, automatically_start_engine_thinking) => {
    stop(interrupt_ponder);
    const fen = $("#fen").value.trim();
    const moves = $("#move").value.trim();
    const movelist = moves.split(" ");
    let i = 0;
    let count = 0;
    for (i = 0; i < movelist.length; i++) {
      if (movelist[i].length == 0) {
        continue;
      }
      count++;
    }
    $("#gotomovenum").value = count;

    if (fen.length > 0) {
      stockfish.postMessage(`position fen ${fen} moves ${moves}`);
    } else {
      stockfish.postMessage(`position startpos moves ${moves}`);
    }
    const stm = $("#label-stm").innerText;
    if (websocket_status == "CONNECTED") {
      if (fge.state.analysis_engine instanceof fge.Engine) {
        fge.state.analysis_engine.SetPosition(
          fen,
          moves,
          fge.GetBoardWidth(),
          fge.GetBoardHeight(),
        );
      }
      if (
        interrupt_ponder ||
        !advanced_time_control ||
        (advanced_time_control && !during_play)
      ) {
        if (fge.state.first_engine instanceof fge.Engine) {
          fge.state.first_engine.SetPosition(
            fen,
            moves,
            fge.GetBoardWidth(),
            fge.GetBoardHeight(),
          );
        }
        if (fge.state.second_engine instanceof fge.Engine) {
          fge.state.second_engine.SetPosition(
            fen,
            moves,
            fge.GetBoardWidth(),
            fge.GetBoardHeight(),
          );
        }
      } else {
        if (stm == "white") {
          if (fge.state.first_engine instanceof fge.Engine) {
            if (fge.state.first_engine.Ponder && advanced_time_control) {
              if (
                fge.state.first_engine.PonderMove != "0000" &&
                fge.state.first_engine.PonderMove !=
                  $("#move").value.trim().split(" ").at(-1)
              ) {
                fge.state.first_engine.SetPonderMiss();
                fge.state.first_engine.SetPosition(
                  fen,
                  moves,
                  fge.GetBoardWidth(),
                  fge.GetBoardHeight(),
                );
                console.log(
                  `%c Ponder %c MISS %c WHITE Ponder misses`,
                  "color: #fff; background: #5f5f5f",
                  "color: #fff; background: #f03a17",
                  "",
                );
              } else if (fge.state.first_engine.PonderMove == "0000") {
                fge.state.first_engine.SetPosition(
                  fen,
                  moves,
                  fge.GetBoardWidth(),
                  fge.GetBoardHeight(),
                );
              }
            } else {
              fge.state.first_engine.SetPosition(
                fen,
                moves,
                fge.GetBoardWidth(),
                fge.GetBoardHeight(),
              );
            }
          }
          if (fge.state.second_engine instanceof fge.Engine) {
            if (
              fge.state.second_engine.Ponder &&
              fge.state.second_engine.PonderMove != "0000" &&
              advanced_time_control
            ) {
              fge.state.second_engine.SetPosition(
                fen,
                moves + ` ${fge.state.second_engine.PonderMove}`,
                fge.GetBoardWidth(),
                fge.GetBoardHeight(),
              );
            } else {
              if (
                fge.state.second_engine.Ponder &&
                fge.state.second_engine.IsUsing
              ) {
                console.log(
                  `%c Ponder %c WARNING %c BLACK makes no ponder move but Ponder=true`,
                  "color: #fff; background: #5f5f5f",
                  "color: #fff; background: #ffc83d",
                  "",
                );
              }
              fge.state.second_engine.SetPosition(
                fen,
                moves,
                fge.GetBoardWidth(),
                fge.GetBoardHeight(),
              );
            }
          }
        } else if (stm == "black") {
          if (fge.state.second_engine instanceof fge.Engine) {
            if (fge.state.second_engine.Ponder && advanced_time_control) {
              if (
                fge.state.second_engine.PonderMove != "0000" &&
                fge.state.second_engine.PonderMove !=
                  $("#move").value.trim().split(" ").at(-1)
              ) {
                fge.state.second_engine.SetPonderMiss();
                fge.state.second_engine.SetPosition(
                  fen,
                  moves,
                  fge.GetBoardWidth(),
                  fge.GetBoardHeight(),
                );
                console.log(
                  `%c Ponder %c MISS %c BLACK Ponder misses`,
                  "color: #fff; background: #5f5f5f",
                  "color: #fff; background: #f03a17",
                  "",
                );
              } else if (fge.state.second_engine.PonderMove == "0000") {
                fge.state.second_engine.SetPosition(
                  fen,
                  moves,
                  fge.GetBoardWidth(),
                  fge.GetBoardHeight(),
                );
              }
            } else {
              fge.state.second_engine.SetPosition(
                fen,
                moves,
                fge.GetBoardWidth(),
                fge.GetBoardHeight(),
              );
            }
          }
          if (fge.state.first_engine instanceof fge.Engine) {
            if (
              fge.state.first_engine.Ponder &&
              fge.state.first_engine.PonderMove != "0000" &&
              advanced_time_control
            ) {
              fge.state.first_engine.SetPosition(
                fen,
                moves + ` ${fge.state.first_engine.PonderMove}`,
                fge.GetBoardWidth(),
                fge.GetBoardHeight(),
              );
            } else {
              if (
                fge.state.first_engine.Ponder &&
                fge.state.first_engine.IsUsing
              ) {
                console.log(
                  `%c Ponder %c WARNING %c WHITE makes no ponder move but Ponder=true`,
                  "color: #fff; background: #5f5f5f",
                  "color: #fff; background: #ffc83d",
                  "",
                );
              }
              fge.state.first_engine.SetPosition(
                fen,
                moves,
                fge.GetBoardWidth(),
                fge.GetBoardHeight(),
              );
            }
          }
        }
      }
    }
    updateTimerOnMove();

    if (
      automatically_start_engine_thinking &&
      stm != "undefined" &&
      ((play_white && stm == "white") ||
        (play_black && stm == "black") ||
        analysis_mode)
    ) {
      setTimeout(go(false, false), 10);
    } else if (automatically_start_engine_thinking) {
      if (fge.state.first_engine instanceof fge.Engine) {
        if (
          fge.state.first_engine.IsUsing &&
          fge.state.first_engine.Ponder &&
          stm != "undefined" &&
          play_white
        ) {
          setTimeout(go(true, false), 10);
        }
      }
      if (fge.state.second_engine instanceof fge.Engine) {
        if (
          fge.state.second_engine.IsUsing &&
          fge.state.second_engine.Ponder &&
          stm != "undefined" &&
          play_black
        ) {
          setTimeout(go(false, true), 10);
        }
      }
      if (
        (random_mover_white && !play_white && stm == "white") ||
        (random_mover_black && !play_black && stm == "black")
      ) {
        setTimeout(() => {
          if (random_mover_white || random_mover_black)
            document.getElementById("randommovergo").click();
        }, 200);
      }
    }
  };

  const sendCommandToEngine = () => {
    let cmd = $("#enginecmd")
      .value.split(" ")
      .filter(function (item) {
        return item != null && item != undefined && item != "";
      });
    if (cmd[0] == "quit") {
      window.alert(
        "Cannot send this command: Quitting engine will cause the engine to not work.",
      );
      return;
    }
    if (cmd[0] == "position") {
      window.alert(
        "Cannot send this command: Setting position will cause the UI's position and the engine's position to be different. Set the position in the \"Position\" section instead.",
      );
      return;
    }
    if (cmd[0] == "flip") {
      window.alert(
        "Cannot send this command: Flipping the side will cause the UI's position and the engine's position to be different. Set the position in the \"Position\" section instead.",
      );
      return;
    }
    if (cmd[0] == "go") {
      window.alert(
        "Cannot send this command: Perform this action in the UI instead.",
      );
      return;
    }
    if (cmd[0] == "stop") {
      window.alert(
        "Cannot send this command: Perform this action in the UI instead.",
      );
      return;
    }
    if (cmd[0] == "ucinewgame") {
      window.alert(
        "Cannot send this command: Perform this action in the UI instead.",
      );
      return;
    }
    if (cmd[0] == "ponderhit") {
      window.alert(
        "Cannot send this command: Engine ponder hit is only allowed to be sent by the GUI.",
      );
      return;
    }
    if (cmd[0] == "setoption" && cmd[1] == "name" && cmd[2] == "VariantPath") {
      window.alert(
        'Cannot send this command: To select variants.ini, select the ini file by clicking the "Select File" button of variants.ini at the top of the page.',
      );
      return;
    }
    if (
      cmd[0] == "setoption" &&
      cmd[1] == "name" &&
      (cmd[2] == "UCI_Variant" ||
        cmd[2] == "USI_Variant" ||
        cmd[2] == "UCCI_Variant")
    ) {
      window.alert(
        "Cannot send this command: To change the variant, select the items in the variants dropdown.",
      );
      return;
    }
    if (cmd[0] == "setoption" && cmd[1] == "name" && cmd[2] == "Ponder") {
      window.alert(
        "Cannot send this command: Setting this value manually does not make sense.",
      );
      return;
    }
    if (cmd[0] == "usi") {
      window.alert(
        "Cannot send this command: Change engine protocol in engine management UI. In browser Fairy-Stockfish only accepts UCI protocol.",
      );
      return;
    }
    if (cmd[0] == "ucci") {
      window.alert(
        "Cannot send this command: Change engine protocol in engine management UI. In browser Fairy-Stockfish only accepts UCI protocol.",
      );
      return;
    }
    if (cmd[0] == "xboard") {
      window.alert(
        "Cannot send this command: Change engine protocol in engine management UI. In browser Fairy-Stockfish only accepts UCI protocol.",
      );
      return;
    }
    if (cmd[0] == "ucicyclone") {
      window.alert(
        "Cannot send this command: Change engine protocol in engine management UI. In browser Fairy-Stockfish only accepts UCI protocol.",
      );
      return;
    }
    if (cmd[0] == "uci") {
      window.alert(
        "Cannot send this command: Change engine protocol in engine management UI. In browser Fairy-Stockfish only accepts UCI protocol.",
      );
      return;
    }
    const targetengine = document.getElementById("targetengine");
    if (targetengine[targetengine.selectedIndex].value == "WHITE") {
      if (websocket_status == "CONNECTED") {
        if (fge.state.first_engine instanceof fge.Engine) {
          fge.state.first_engine.PostMessage($("#enginecmd").value.trim());
        } else {
          window.alert("1st engine is not loaded.");
        }
      } else if (window.location.hostname != "localhost") {
        window.alert("This feature is only available in offline versions.");
      } else {
        window.alert(
          "Connection lost with the server. Try reloading the page.",
        );
      }
    } else if (targetengine[targetengine.selectedIndex].value == "BLACK") {
      if (websocket_status == "CONNECTED") {
        if (fge.state.second_engine instanceof fge.Engine) {
          fge.state.second_engine.PostMessage($("#enginecmd").value.trim());
        } else {
          window.alert("2nd engine is not loaded.");
        }
      } else if (window.location.hostname != "localhost") {
        window.alert("This feature is only available in offline versions.");
      } else {
        window.alert(
          "Connection lost with the server. Try reloading the page.",
        );
      }
    } else if (targetengine[targetengine.selectedIndex].value == "ANALYSIS") {
      if (websocket_status == "CONNECTED") {
        if (fge.state.analysis_engine instanceof fge.Engine) {
          fge.state.analysis_engine.PostMessage($("#enginecmd").value.trim());
        } else {
          window.alert("Analysis engine is not loaded.");
        }
      } else if (window.location.hostname != "localhost") {
        window.alert("This feature is only available in offline versions.");
      } else {
        window.alert(
          "Connection lost with the server. Try reloading the page.",
        );
      }
    } else if (targetengine[targetengine.selectedIndex].value == "DEFAULT") {
      stockfish.postMessage($("#enginecmd").value.trim());
    }
  };

  // const totalMoveNumber = () => {
  //   let listlength = 0;
  //   let i = 0;
  //   moves_split = $("#move").value.split(" ");
  //   for (i = 0; i < moves_split.length; i++) {
  //     if (moves_split[i].length == 0) {
  //       continue;
  //     }
  //     listlength++;
  //   }
  //   return listlength;
  // };

  const reset = () => {
    review_mode = false;
    // if (board_setup_mode) {
    //   board_setup_mode = false;
    //   triggerBoardSetupPieceIdentifier(false);
    // }
  };

  // const undo = () => {
  //   if (board_setup_mode) {
  //     return;
  //   }
  //   play_move = false;
  // };

  const go = (
    white_engine_ponder_and_human_black,
    black_engine_ponder_and_human_white,
  ) => {
    if (board_setup_mode) {
      return;
    }
    return_early = play_move;
    console.log(`return early: ${return_early}`);
    if (return_early) return; // avoid race condition
    let args = "";
    let wargs = "";
    let bargs = "";
    const movetime = $("#movetime").value;
    const depth = $("#depth").value;
    const nodes = $("#nodes").value;
    const threadnum = $("#threads").value;
    const hashsize = $("#hash").value;
    const multipleprincipalvariation = $("#multipv").value;
    const whiteengineoutput = document.getElementById("whiteengineoutput");
    const blackengineoutput = document.getElementById("blackengineoutput");
    const analysisengineoutput = document.getElementById(
      "analysisengineoutput",
    );
    let whitedepthv = parseInt($("#whitedepth").value);
    let whitemovetimev = parseInt($("#whitemovetime").value);
    let whitenodesv = parseInt($("#whitenodes").value);
    let blackdepthv = parseInt($("#blackdepth").value);
    let blackmovetimev = parseInt($("#blackmovetime").value);
    let blacknodesv = parseInt($("#blacknodes").value);
    let winf = false;
    let binf = false;
    let wtime = 0;
    let btime = 0;
    let winc = 0;
    let binc = 0;
    if (analysis_mode) {
      let analysisargs = "";
      if ($("#depth").validity.valid && depth > 0) {
        analysisargs += ` depth ${depth}`;
      }
      if ($("#movetime").validity.valid && movetime > 0) {
        analysisargs += ` movetime ${movetime}`;
      }
      if ($("#nodes").validity.valid && nodes > 0) {
        analysisargs += ` nodes ${nodes}`;
      }
      args += analysisargs != "" ? analysisargs : " infinite";
    } else if (advanced_time_control) {
      if (
        white_timer_type == "infinite" &&
        $("#label-stm").innerHTML == "white"
      ) {
        args += "infinite";
        wargs += "infinite";
        winf = true;
        console.log("wtime infinite");
      } else if (
        black_timer_type == "infinite" &&
        $("#label-stm").innerHTML == "black"
      ) {
        args += "infinite";
        bargs += "infinite";
        binf = true;
        console.log("btime infinite");
      }
      if (white_timer_type == "time per move") {
        wtime += +white_moving_time_list[0].remaining_time;
        winc += +white_moving_time_list[0].remaining_time;
      } else if (white_timer_type == "tournament") {
        wtime += +(+white_remaining_time);
        winc += +white_time_gain;
      } else if (white_timer_type == "hourglass") {
        //How to tell that it's hourglass to engine?
        wtime += +white_remaining_time;
      } else if (white_timer_type == "byoyomi") {
        wtime += +white_remaining_time;
        if (
          white_remaining_time < white_byoyomi_time_per_period &&
          white_remaining_byoyomi_periods > 0
        ) {
          winc += +white_byoyomi_time_per_period;
        }
        if (white_remaining_byoyomi_periods == white_byoyomi_period_count) {
          wtime += +white_byoyomi_time_per_period;
          winc = 0;
        }
      }
      if (black_timer_type == "time per move") {
        btime += +black_moving_time_list[0].remaining_time;
        binc += +black_moving_time_list[0].remaining_time;
      } else if (black_timer_type == "tournament") {
        btime += +(+black_remaining_time);
        binc = +black_time_gain;
      } else if (black_timer_type == "hourglass") {
        //How to tell that it's hourglass to engine?
        btime += +black_remaining_time;
      } else if (black_timer_type == "byoyomi") {
        btime += +black_remaining_time;
        if (
          black_remaining_time < black_byoyomi_time_per_period &&
          black_remaining_byoyomi_periods > 0
        ) {
          binc += +black_byoyomi_time_per_period;
        }
        if (black_remaining_byoyomi_periods == black_byoyomi_period_count) {
          btime += +black_byoyomi_time_per_period;
          binc = 0;
        }
      }
      console.log(`wtime ${wtime} winc ${winc} btime ${btime} binc ${binc}`);
      args += `wtime ${wtime} winc ${winc} btime ${btime} binc ${binc}`;
      stockfish.postMessage(
        `setoption name Move Overhead value ${timer_interval}`,
      );
      // A side without a clock but with a search limit (depth,
      // nodes, time per move) uses that limit instead.
      const limitedside = $("#label-stm").innerHTML;
      const limitargs = sideLimitArgs(limitedside);
      if (
        limitargs != "" &&
        ((limitedside == "white" && white_timer_type == "infinite") ||
          (limitedside == "black" && black_timer_type == "infinite"))
      ) {
        args = limitargs;
      }
    } else {
      const limitargs = sideLimitArgs($("#label-stm").innerHTML);
      if (limitargs != "") {
        args += limitargs;
      }
      if (!($("#whitedepth").validity.valid && whitedepthv > 0)) {
        whitedepthv = -1;
      }
      if (!($("#whitemovetime").validity.valid && whitemovetimev > 0)) {
        whitemovetimev = -1;
      }
      if (!($("#whitenodes").validity.valid && whitenodesv > 0)) {
        whitenodesv = -1;
      }
      if (!($("#blackdepth").validity.valid && blackdepthv > 0)) {
        blackdepthv = -1;
      }
      if (!($("#blackmovetime").validity.valid && blackmovetimev > 0)) {
        blackmovetimev = -1;
      }
      if (!($("#blacknodes").validity.valid && blacknodesv > 0)) {
        blacknodesv = -1;
      }
    }

    if (threadnum.length <= 0 || threadnum < 1) {
      stockfish.postMessage(`setoption name Threads value 1`);
    } else if (threadnum > 512) {
      stockfish.postMessage(`setoption name Threads value 512`);
    } else {
      stockfish.postMessage(`setoption name Threads value ${threadnum}`);
    }
    if (hashsize.length <= 0 || hashsize < 1) {
      if (in_browser_fsf_hash != 16) {
        stockfish.postMessage(`setoption name Hash value 16`);
        in_browser_fsf_hash = 16;
        console.log(`sethash: 16`);
      }
    } else if (hashsize > 33554432) {
      if (in_browser_fsf_hash != 33554432) {
        stockfish.postMessage(`setoption name Hash value 33554432`);
        in_browser_fsf_hash = 33554432;
        console.log(`sethash: 33554432`);
      }
    } else if (in_browser_fsf_hash != hashsize) {
      stockfish.postMessage(`setoption name Hash value ${hashsize}`);
      in_browser_fsf_hash = hashsize;
      console.log(`sethash: ${hashsize}`);
    }
    if (
      multipleprincipalvariation.length <= 0 ||
      multipleprincipalvariation < 1
    ) {
      stockfish.postMessage(`setoption name MultiPV value 1`);
    } else if (multipleprincipalvariation > 500) {
      stockfish.postMessage(`setoption name MultiPV value 500`);
    } else {
      stockfish.postMessage(
        `setoption name MultiPV value ${multipleprincipalvariation}`,
      );
    }
    // Skill level only applies when the engine plays; analysis always
    // uses full strength.
    const skilllevel = analysis_mode ? 20 : engine_skill;
    if (skilllevel != in_browser_fsf_skill) {
      stockfish.postMessage(`setoption name Skill Level value ${skilllevel}`);
      in_browser_fsf_skill = skilllevel;
    }
    stockfish.postMessage(`isready`);

    const stm = $("#label-stm").innerText;
    play_move =
      (play_white && stm == "white") ||
      (play_black && stm == "black") ||
      analysis_mode;
    if (websocket_status == "CONNECTED") {
      if (analysis_mode) {
        if (fge.state.analysis_engine instanceof fge.Engine) {
          if (fge.state.analysis_engine.IsUsing) {
            if (clear_log) {
              analysisengineoutput.textContent = "";
              analysis_engine_output = "";
            }
            fge.state.analysis_engine.IsAnalysisEngine = true;
            fge.state.analysis_engine.StartThinking(
              stm,
              true,
              false,
              false,
              false,
              false,
              -1,
              -1,
              -1,
              wtime,
              winc,
              btime,
              binc,
              white_byoyomi_time_per_period,
            );
          } else {
            if (clear_log) {
              engineoutput = "";
            }
            stockfish.postMessage(`go ${args}`);
          }
        } else {
          if (clear_log) {
            engineoutput = "";
          }
          stockfish.postMessage(`go ${args}`);
        }
      } else if (stm == "white") {
        if (fge.state.first_engine instanceof fge.Engine) {
          if (fge.state.first_engine.IsUsing) {
            if (
              advanced_time_control &&
              fge.state.first_engine.Ponder &&
              fge.state.first_engine.PonderMove ==
                $("#move").value.trim().split(" ").at(-1)
            ) {
              fge.state.first_engine.StartThinking(
                stm,
                false,
                true,
                false,
                true,
                white_timer_type == "byoyomi",
                whitedepthv,
                whitemovetimev,
                whitenodesv,
                wtime,
                winc,
                btime,
                binc,
                white_byoyomi_time_per_period,
              );
              console.log(
                `%c Ponder %c HIT %c WHITE Ponder Hits`,
                "color: #fff; background: #5f5f5f",
                "color: #fff; background: #4bc729",
                "",
              );
            } else {
              if (clear_log) {
                whiteengineoutput.textContent = "";
                first_engine_output = "";
              }
              fge.state.first_engine.StartThinking(
                stm,
                winf,
                advanced_time_control,
                false,
                false,
                white_timer_type == "byoyomi",
                whitedepthv,
                whitemovetimev,
                whitenodesv,
                wtime,
                winc,
                btime,
                binc,
                white_byoyomi_time_per_period,
              );
              //console.log("WHITE: go " + wargs);
            }
          } else if (!black_engine_ponder_and_human_white) {
            if (clear_log) {
              engineoutput = "";
            }
            stockfish.postMessage(`go ${args}`);
          }
        } else if (!black_engine_ponder_and_human_white) {
          if (clear_log) {
            engineoutput = "";
          }
          stockfish.postMessage(`go ${args}`);
        }
        if (fge.state.second_engine instanceof fge.Engine) {
          if (fge.state.second_engine.IsUsing) {
            if (
              advanced_time_control &&
              fge.state.second_engine.Ponder &&
              fge.state.second_engine.PonderMove != "0000"
            ) {
              if (clear_log) {
                blackengineoutput.textContent = "";
                second_engine_output = "";
              }
              fge.state.second_engine.StartThinking(
                stm,
                false,
                true,
                true,
                false,
                black_timer_type == "byoyomi",
                blackdepthv,
                blackmovetimev,
                blacknodesv,
                wtime,
                winc,
                btime,
                binc,
                black_byoyomi_time_per_period,
              );
            }
          }
        }
      } else if (stm == "black") {
        if (fge.state.second_engine instanceof fge.Engine) {
          if (fge.state.second_engine.IsUsing) {
            if (
              advanced_time_control &&
              fge.state.second_engine.Ponder &&
              fge.state.second_engine.PonderMove ==
                $("#move").value.trim().split(" ").at(-1)
            ) {
              fge.state.second_engine.StartThinking(
                stm,
                false,
                true,
                false,
                true,
                black_timer_type == "byoyomi",
                blackdepthv,
                blackmovetimev,
                blacknodesv,
                wtime,
                winc,
                btime,
                binc,
                black_byoyomi_time_per_period,
              );
              console.log(
                `%c Ponder %c HIT %c BLACK Ponder Hits`,
                "color: #fff; background: #5f5f5f",
                "color: #fff; background: #4bc729",
                "",
              );
            } else {
              if (clear_log) {
                blackengineoutput.textContent = "";
                second_engine_output = "";
              }
              fge.state.second_engine.StartThinking(
                stm,
                binf,
                advanced_time_control,
                false,
                false,
                black_timer_type == "byoyomi",
                blackdepthv,
                blackmovetimev,
                blacknodesv,
                wtime,
                winc,
                btime,
                binc,
                white_byoyomi_time_per_period,
              );
              //console.log("BLACK: go " + bargs);
            }
          } else if (!white_engine_ponder_and_human_black) {
            if (clear_log) {
              engineoutput = "";
            }
            stockfish.postMessage(`go ${args}`);
          }
        } else if (!white_engine_ponder_and_human_black) {
          if (clear_log) {
            engineoutput = "";
          }
          stockfish.postMessage(`go ${args}`);
        }
        if (fge.state.first_engine instanceof fge.Engine) {
          if (fge.state.first_engine.IsUsing) {
            if (
              advanced_time_control &&
              fge.state.first_engine.Ponder &&
              fge.state.first_engine.PonderMove != "0000"
            ) {
              if (clear_log) {
                whiteengineoutput.textContent = "";
                first_engine_output = "";
              }
              fge.state.first_engine.StartThinking(
                stm,
                false,
                true,
                true,
                false,
                white_timer_type == "byoyomi",
                whitedepthv,
                whitemovetimev,
                whitenodesv,
                wtime,
                winc,
                btime,
                binc,
                white_byoyomi_time_per_period,
              );
            }
          }
        }
      }
    } else {
      if (clear_log) {
        engineoutput = "";
      }
      stockfish.postMessage(`go ${args}`);
    }
  };

  const setupTimer = () => {
    $("#timeoutside").value = 0;
    white_timer_type = $("#dropdown-whitetimemode").value;
    black_timer_type = $("#dropdown-blacktimemode").value;
    white_remaining_time = parseInt($("#whitestarttime").value);
    black_remaining_time = parseInt($("#blackstarttime").value);
    if (
      isNaN(white_remaining_time) ||
      white_remaining_time.length < 1 ||
      white_remaining_time < 1
    ) {
      white_remaining_time = play_white ? 20000 : 600000;
    }
    if (
      isNaN(black_remaining_time) ||
      black_remaining_time.length < 1 ||
      black_remaining_time < 1
    ) {
      black_remaining_time = play_black ? 20000 : 600000;
    }
    white_time_gain = parseInt($("#whitetimegain").value);
    black_time_gain = parseInt($("#blacktimegain").value);
    if (
      isNaN(white_time_gain) ||
      white_time_gain.length < 1 ||
      white_time_gain < 0
    ) {
      white_time_gain = 0;
    }
    if (
      isNaN(black_time_gain) ||
      black_time_gain.length < 1 ||
      black_time_gain < 0
    ) {
      black_time_gain = 0;
    }
    white_byoyomi_time_per_period = parseInt($("#whitebyoyomitime").value);
    black_byoyomi_time_per_period = parseInt($("#blackbyoyomitime").value);
    if (
      isNaN(white_byoyomi_time_per_period) ||
      white_byoyomi_time_per_period.length < 1 ||
      white_byoyomi_time_per_period < 1
    ) {
      white_byoyomi_time_per_period = 30000;
    }
    if (
      isNaN(black_byoyomi_time_per_period) ||
      black_byoyomi_time_per_period.length < 1 ||
      black_byoyomi_time_per_period < 1
    ) {
      black_byoyomi_time_per_period = 30000;
    }
    white_byoyomi_period_count = parseInt($("#whitebyoyomiperiodcount").value);
    black_byoyomi_period_count = parseInt($("#blackbyoyomiperiodcount").value);
    if (
      isNaN(white_byoyomi_period_count) ||
      white_byoyomi_period_count.length < 1 ||
      white_byoyomi_period_count < 1
    ) {
      white_byoyomi_period_count = 1;
    }
    if (
      isNaN(black_byoyomi_period_count) ||
      black_byoyomi_period_count.length < 1 ||
      black_byoyomi_period_count < 1
    ) {
      black_byoyomi_period_count = 1;
    }
    white_remaining_byoyomi_periods = white_byoyomi_period_count;
    black_remaining_byoyomi_periods = black_byoyomi_period_count;
    white_time_margin = parseInt($("#whitetimemargin").value);
    black_time_margin = parseInt($("#blacktimemargin").value);
    if (
      isNaN(white_time_margin) ||
      white_time_margin.length < 1 ||
      white_time_margin < 0
    ) {
      white_time_margin = timeout_margin;
    }
    if (
      isNaN(black_time_margin) ||
      black_time_margin.length < 1 ||
      black_time_margin < 0
    ) {
      black_time_margin = timeout_margin;
    }
    white_moving_time_list = [];
    black_moving_time_list = [];
    const now = Date.now();
    white_moving_time_list.push({
      remaining_time: white_remaining_time,
      time_stamp: now,
    }); //Start time white
    black_moving_time_list.push({
      remaining_time: black_remaining_time,
      time_stamp: now,
    }); //Start time black
    $("#whitetime").innerHTML = `${parseInt(white_remaining_time / 1000)}`;
    $("#blacktime").innerHTML = `${parseInt(black_remaining_time / 1000)}`;
    if (white_timer_type == "infinite") {
      $("#whitetime").innerHTML = "∞";
    }
    if (black_timer_type == "infinite") {
      $("#blacktime").innerHTML = "∞";
    }
    previous_mover = "";
  };

  const resetTimer = () => {
    $("#whitetime").innerHTML = "--";
    $("#blacktime").innerHTML = "--";
    previous_mover = "";
    $("#timeoutside").value = 0;
    white_time_exceeded = false;
    black_time_exceeded = false;
    document.getElementById("whitetimer").classList.remove("timer-active");
    document.getElementById("blacktimer").classList.remove("timer-active");
    document.getElementById("whitetime").classList.remove("time-exceeded");
    document.getElementById("blacktime").classList.remove("time-exceeded");
  };

  function updateTimerOnMove() {
    if (!during_play) {
      return;
    }
    move_finish_timer_updating = true;
    const stm = document.getElementById("label-stm").innerText;
    console.log(`${$("#gamestatus").innerText}`);
    //console.log(white_moving_time_list);
    //console.log(white_moving_time_list);
    const realtimenow = Date.now();
    if (stm == "white") {
      if (previous_mover == "") {
        if (white_timer_type == "tournament") {
          white_remaining_time =
            +white_remaining_time + +white_time_gain + +timer_interval;
        }
        white_moving_time_list.push({
          remaining_time: white_remaining_time,
          time_stamp: realtimenow,
        }); //Time stamp for white's turn begin
      } else {
        black_moving_time_list.push({
          remaining_time: black_remaining_time < 0 ? 0 : black_remaining_time,
          time_stamp: realtimenow,
        }); //Time stamp for black's turn end
        if (white_remaining_time < 0) {
          white_remaining_time = 0;
        }
        //white_remaining_time = (+white_moving_time_list.at(-1).remaining_time) + ((+white_moving_time_list.at(-1).time_stamp) - (+now));
        if (white_timer_type == "tournament") {
          white_remaining_time =
            +white_remaining_time + +white_time_gain + +timer_interval;
        } else if (white_timer_type == "time per move") {
          white_remaining_time =
            +white_moving_time_list[0].remaining_time + +timer_interval;
        } else if (white_timer_type == "byoyomi") {
          if (white_remaining_byoyomi_periods < white_byoyomi_period_count) {
            white_remaining_time =
              +white_byoyomi_time_per_period + +timer_interval;
          } else {
            white_remaining_time = +white_remaining_time + +timer_interval;
          }
        }
        if (black_timer_type == "hourglass") {
          white_remaining_time =
            +white_remaining_time +
            +black_moving_time_list.at(-2).remaining_time -
            +black_moving_time_list.at(-1).remaining_time;
        }
        white_moving_time_list.push({
          remaining_time: white_remaining_time,
          time_stamp: realtimenow,
        }); //Time stamp for white's turn begin
      }
      previous_mover = "WHITE";
      document.getElementById("whitetimer").classList.add("timer-active");
      document.getElementById("blacktimer").classList.remove("timer-active");
    } else if (stm == "black") {
      if (previous_mover == "") {
        if (black_timer_type == "tournament") {
          black_remaining_time =
            +black_remaining_time + +black_time_gain + +timer_interval;
        }
        black_moving_time_list.push({
          remaining_time: black_remaining_time,
          time_stamp: realtimenow,
        }); //Time stamp for black's turn begin
      } else {
        white_moving_time_list.push({
          remaining_time: white_remaining_time < 0 ? 0 : white_remaining_time,
          time_stamp: realtimenow,
        }); //Time stamp for white's turn end
        if (black_remaining_time < 0) {
          black_remaining_time = 0;
        }
        //black_remaining_time = (+black_moving_time_list.at(-1).remaining_time) + ((+black_moving_time_list.at(-1).time_stamp) - (+now));
        if (black_timer_type == "tournament") {
          black_remaining_time =
            +black_remaining_time + +black_time_gain + +timer_interval;
        } else if (black_timer_type == "time per move") {
          black_remaining_time =
            +black_moving_time_list[0].remaining_time + +timer_interval;
        } else if (black_timer_type == "byoyomi") {
          if (black_remaining_byoyomi_periods < black_byoyomi_period_count) {
            black_remaining_time =
              +black_byoyomi_time_per_period + +timer_interval;
          } else {
            black_remaining_time = +black_remaining_time + +timer_interval;
          }
        }
        if (white_timer_type == "hourglass") {
          black_remaining_time =
            +black_remaining_time +
            +white_moving_time_list.at(-2).remaining_time -
            +white_moving_time_list.at(-1).remaining_time;
        }
        black_moving_time_list.push({
          remaining_time: black_remaining_time,
          time_stamp: realtimenow,
        }); //Time stamp for black's turn begin
      }
      previous_mover = "BLACK";
      document.getElementById("whitetimer").classList.remove("timer-active");
      document.getElementById("blacktimer").classList.add("timer-active");
    } else {
      document.getElementById("whitetimer").classList.remove("timer-active");
      document.getElementById("blacktimer").classList.remove("timer-active");
    }
    if (white_time_exceeded) {
      document.getElementById("whitetime").classList.remove("time-exceeded");
    }
    if (black_time_exceeded) {
      document.getElementById("blacktime").classList.remove("time-exceeded");
    }
    white_time_exceeded = false;
    black_time_exceeded = false;
    move_finish_timer_updating = false;
  }

  function updateTimer() {
    const gamestatus = document.getElementById("gamestatus");
    if (gamestatus.innerText == "END") {
      deleteTimer();
      gameEnd();
      return;
    }
    if (move_finish_timer_updating) {
      //avoid race condition
      return;
    }
    let deltatimereality = 0;
    let realitytimenow = Date.now();
    if (previous_reality_time >= 0) {
      deltatimereality = realitytimenow - previous_reality_time;
    }
    previous_reality_time = realitytimenow;
    gamestatus.click();
    const whitetimelabel = document.getElementById("whitetime");
    const blacktimelabel = document.getElementById("blacktime");
    if (gamestatus.innerText == "PLAYING_WHITE") {
      if (white_timer_type == "infinite") {
        previous_mover = "WHITE";
        return;
      }
      white_remaining_time = white_remaining_time - deltatimereality;
      if (white_timer_type == "byoyomi" && white_remaining_time <= 0) {
        if (white_remaining_byoyomi_periods == 0) {
        } else {
          white_remaining_byoyomi_periods--;
          white_remaining_time = +white_byoyomi_time_per_period;
          console.log(
            "WHITE byoyomi remaining periods: " +
              white_remaining_byoyomi_periods,
          );
        }
      }
      if (white_remaining_time < -white_time_margin) {
        deleteTimer();
        $("#timeoutside").value = 1;
        timeIsUpFor("WHITE");
        whitetimelabel.classList.remove("time-exceeded");
        return;
      }
      if (white_timer_type == "infinite") {
        whitetimelabel.innerText = "∞";
      } else if (white_remaining_time >= 10000) {
        whitetimelabel.innerText = `${parseInt(white_remaining_time / 1000)}`;
      } else {
        whitetimelabel.innerText = `${(
          parseInt(white_remaining_time / 100) / 10
        ).toFixed(1)}`;
        if (white_remaining_time <= 0 && !white_time_exceeded) {
          white_time_exceeded = true;
          whitetimelabel.classList.add("time-exceeded");
        }
      }
      if (black_timer_type == "infinite") {
        blacktimelabel.innerText = "∞";
      } else if (black_remaining_time >= 10000) {
        blacktimelabel.innerText = `${parseInt(black_remaining_time / 1000)}`;
      } else {
        blacktimelabel.innerText = `${(
          parseInt(black_remaining_time / 100) / 10
        ).toFixed(1)}`;
        if (black_remaining_time <= 0 && !black_time_exceeded) {
          black_time_exceeded = true;
          blacktimelabel.classList.add("time-exceeded");
        }
      }
      if (white_timer_type == "byoyomi") {
        whitetimelabel.innerText += ` (${white_remaining_byoyomi_periods})`;
      }
      if (black_timer_type == "byoyomi") {
        blacktimelabel.innerText += ` (${black_remaining_byoyomi_periods})`;
      }
      previous_mover = "WHITE";
    } else if (gamestatus.innerText == "PLAYING_BLACK") {
      if (black_timer_type == "infinite") {
        previous_mover = "BLACK";
        return;
      }
      black_remaining_time = black_remaining_time - deltatimereality;
      if (black_timer_type == "byoyomi" && black_remaining_time <= 0) {
        if (black_remaining_byoyomi_periods == 0) {
        } else {
          black_remaining_byoyomi_periods--;
          black_remaining_time = +black_byoyomi_time_per_period;
          console.log(
            "BLACK byoyomi remaining periods: " +
              black_remaining_byoyomi_periods,
          );
        }
      }
      if (black_remaining_time < -black_time_margin) {
        deleteTimer();
        $("#timeoutside").value = 2;
        timeIsUpFor("BLACK");
        blacktimelabel.classList.remove("time-exceeded");
        return;
      }
      if (white_timer_type == "infinite") {
        whitetimelabel.innerText = "∞";
      } else if (white_remaining_time >= 10000) {
        whitetimelabel.innerText = `${parseInt(white_remaining_time / 1000)}`;
      } else {
        whitetimelabel.innerText = `${(
          parseInt(white_remaining_time / 100) / 10
        ).toFixed(1)}`;
        if (white_remaining_time <= 0 && !white_time_exceeded) {
          white_time_exceeded = true;
          whitetimelabel.classList.add("time-exceeded");
        }
      }
      if (black_timer_type == "infinite") {
        blacktimelabel.innerText = "∞";
      } else if (black_remaining_time >= 10000) {
        blacktimelabel.innerText = `${parseInt(black_remaining_time / 1000)}`;
      } else {
        blacktimelabel.innerText = `${(
          parseInt(black_remaining_time / 100) / 10
        ).toFixed(1)}`;
        if (black_remaining_time <= 0 && !black_time_exceeded) {
          black_time_exceeded = true;
          blacktimelabel.classList.add("time-exceeded");
        }
      }
      if (white_timer_type == "byoyomi") {
        whitetimelabel.innerText += ` (${white_remaining_byoyomi_periods})`;
      }
      if (black_timer_type == "byoyomi") {
        blacktimelabel.innerText += ` (${black_remaining_byoyomi_periods})`;
      }
      previous_mover = "BLACK";
    }
  }

  const createTimer = () => {
    timer = setInterval(() => {
      updateTimer();
    }, timer_interval);
    console.log(`${timer}`);
  };

  const deleteTimer = () => {
    console.log("Timer delete!");
    clearInterval(timer);
  };

  const timeIsUpFor = (side) => {
    force_stop();
    if (side == "WHITE") {
      white_remaining_time = 0;
      $("#timeoutside").value = 1;
      $("#whitetime").innerHTML = "Out Of Time";
    } else if (side == "BLACK") {
      black_remaining_time = 0;
      $("#timeoutside").value = 2;
      $("#blacktime").innerHTML = "Out Of Time";
    }
    gameEnd();
    document.dispatchEvent(
      new CustomEvent("gameend", {
        detail: {
          result: side == "WHITE" ? "0-1" : "1-0",
          reason: "time forfeit",
        },
      }),
    );
  };

  const gameEnd = () => {
    const gamestatusobj = document.getElementById("gamestatus");
    during_play = false;
    gamestatusobj.click();
    if (gamestatusobj.innerText == "END") {
      $("#gameresult").click();
    }
    gamestatusobj.innerText = "END";
    //advanced_time_control = false;
    force_stop();
    //$("#currentposition").click();
    // $("#input").style.display = "";
    // $("#input2").style.display = "";
    // $("#input3").style.display = "";
    // $("#posvariantdiv").style.display = "";
    // $("#pgn-operations").style.display = "";
  };

  const gameAbort = () => {
    deleteTimer();
    gameEnd();
  };

  const goWithTimeControl = () => {
    if ($("#gamestatus").innerText != "END") {
      return;
    }
    //We need to prevent user from doing unnecessary actions during countdown, so we'll hide these divs
    // $("#input").style.display = "none"; //These divs are unable to be hidden by {hidden: during_play}
    // $("#input2").style.display = "none";
    // $("#input3").style.display = "none";
    // $("#posvariantdiv").style.display = "none";
    // $("#pgn-operations").style.display = "none";
    //$("#movecontrol").style.display = "none";
    resetTimer();
    setupTimer();
    $("#gamestatus").click();
    during_play = true;
    //$("#currentposition").click();
    if (fge.state.first_engine instanceof fge.Engine) {
      fge.state.first_engine.PonderMove = "0000";
      fge.state.first_engine.PonderMiss = false;
    }
    if (fge.state.second_engine instanceof fge.Engine) {
      fge.state.second_engine.PonderMove = "0000";
      fge.state.second_engine.PonderMiss = false;
    }
    createTimer();
    const stm = $("#label-stm").innerText;
    console.log(
      `white: ${play_white} black: ${play_black} move: ${
        (play_white && stm == "white") || (play_black && stm == "black")
      }`,
    );
    console.log("Go!");
    previous_reality_time = -1;
    document.getElementById("set").click();
  };

  const stop = (interrupt_pondering) => {
    stockfish.postMessage(`stop`);
    if (fge.state.first_engine instanceof fge.Engine) {
      fge.state.first_engine.StopThinking(
        interrupt_pondering,
        advanced_time_control,
      );
    }
    if (fge.state.second_engine instanceof fge.Engine) {
      fge.state.second_engine.StopThinking(
        interrupt_pondering,
        advanced_time_control,
      );
    }
    if (fge.state.analysis_engine instanceof fge.Engine) {
      fge.state.analysis_engine.StopThinking(true, false);
    }
  };

  const force_stop = () => {
    play_white = play_black = random_mover_white = random_mover_black = false;
    play_move = false;
    stop(true);
  };

  const initPieceTheme = () => {
    const variant = document.getElementById("dropdown-variant").value;
    const chessground = document.getElementById("chessground-container-div");
    let index = themes[0].indexOf(variant);
    let theme_name = "";
    let available_themes = [];
    let DOMListValue;
    let stored_theme = getVariantTheme(variant, false);
    if (index < 0 || variant == "") {
      index = themes[0].indexOf("");
    }
    if (index < 0) {
      theme_name = "default";
    } else {
      available_themes = themes[1][index];
      if (available_themes.length == 0) {
        available_themes = themes[1][themes[0].indexOf("")];
      }
    }
    if (stored_theme && available_themes.includes(stored_theme)) {
      console.log(
        `Using stored piece theme preference for variant "${variant}": ${stored_theme}`,
      );
      changePieceSet(stored_theme, false);
    } else {
      DOMListValue = chessground.classList.value.split(" ");
      if (available_themes.length > 0) {
        // index = available_themes.indexOf(DOMListValue[1]) + 1;
        // if (index != 0) {
        //   console.log("No need to change pieces.");
        //   updateThemeDropdowns(DOMListValue[1], null);
        //   return;
        // }
        // if (index >= available_themes.length) {
        //   index = 0;
        // }
        // theme_name = available_themes[index];
        theme_name = available_themes[0];
      } else {
        theme_name = "default";
      }
      changePieceSet(theme_name, false);
    }
  };

  const initBoardTheme = (onlyChangeWhenInvalid) => {
    const variant = document.getElementById("dropdown-variant").value;
    const chessground = document.getElementById("chessground-container-div");
    let index = themes[0].indexOf(variant);
    let theme_name = "";
    let available_themes = [];
    let DOMListValue;
    let stored_theme = getVariantTheme(variant, true);
    if (index < 0 || variant == "") {
      index = themes[0].indexOf("");
    }
    if (index < 0) {
      theme_name = "defaultboard";
    } else {
      available_themes = themes[2][index];
      if (available_themes.length == 0) {
        available_themes = themes[2][themes[0].indexOf("")];
      }
    }
    if (stored_theme && available_themes.includes(stored_theme)) {
      console.log(
        `Using stored board theme preference for variant "${variant}": ${stored_theme}`,
      );
      changeBoardSet(stored_theme, false);
    } else {
      DOMListValue = chessground.classList.value.split(" ");
      if (available_themes.length > 0) {
        // index = available_themes.indexOf(DOMListValue[0]) + 1;
        // if (index != 0) {
        //   console.log("No need to change board.");
        //   updateThemeDropdowns(null, DOMListValue[0]);
        //   return;
        // }
        // if (index >= available_themes.length) {
        //   index = 0;
        // }
        // theme_name = available_themes[index];
        theme_name = available_themes[0];
      } else {
        theme_name = "defaultboard";
      }
      changeBoardSet(theme_name, false);
    }
  };

  const setupThemeDropdowns = () => {
    let piecethemedropdown = $("#dropdown-piecetheme");
    let boardthemedropdown = $("#dropdown-boardtheme");
    while (piecethemedropdown.options.length > 0) {
      piecethemedropdown.remove(0);
    }
    while (boardthemedropdown.options.length > 0) {
      boardthemedropdown.remove(0);
    }
    let index = 0;
    let piececlasses = [];
    let boardclasses = [];
    index = themes[0].indexOf($("#dropdown-variant").value);
    if (index < 0 || $("#dropdown-variant").value == "") {
      index = themes[0].indexOf("");
    }
    if (index < 0) {
      null;
    } else {
      piececlasses = themes[1][index];
      if (piececlasses.length < 1) {
        piececlasses = themes[1][themes[0].indexOf("")];
      }
      boardclasses = themes[2][index];
      if (boardclasses.length < 1) {
        boardclasses = themes[2][themes[0].indexOf("")];
      }
    }
    if (piececlasses.length > 0) {
      piececlasses.forEach((val) => {
        let newOption = document.createElement("option");
        newOption.text = getThemeName(val);
        newOption.value = val;
        piecethemedropdown.add(newOption);
        //console.log(val);
      });
    } else {
      let newOption = document.createElement("option");
      newOption.text = "Default Pieces";
      newOption.value = "default";
      piecethemedropdown.add(newOption);
      newOption = document.createElement("option");
      newOption.text = getThemeName("userdefined");
      newOption.value = "userdefined";
      piecethemedropdown.add(newOption);
    }
    if (boardclasses.length > 0) {
      boardclasses.forEach((val) => {
        let newOption = document.createElement("option");
        newOption.text = getThemeName(val);
        newOption.value = val;
        boardthemedropdown.add(newOption);
        //console.log(val);
      });
    } else {
      let newOption = document.createElement("option");
      newOption.text = "Default Board";
      newOption.value = "defaultboard";
      boardthemedropdown.add(newOption);
    }
  };

  const updateThemeDropdowns = (piecethemeid, boardthemeid) => {
    let piecethemedropdown = $("#dropdown-piecetheme");
    let boardthemedropdown = $("#dropdown-boardtheme");
    let i = 0;
    if (piecethemeid) {
      for (i = 0; i < piecethemedropdown.options.length; i++) {
        if (piecethemedropdown[i].value == piecethemeid) {
          piecethemedropdown.selectedIndex = i;
          break;
        }
      }
      if (i == piecethemedropdown.options.length) {
        piecethemedropdown.selectedIndex = -1;
      }
    }
    if (boardthemeid) {
      for (i = 0; i < boardthemedropdown.options.length; i++) {
        if (boardthemedropdown[i].value == boardthemeid) {
          boardthemedropdown.selectedIndex = i;
          break;
        }
      }
      if (i == boardthemedropdown.options.length) {
        boardthemedropdown.selectedIndex = -1;
      }
    }
  };

  const updateVariantDropdownTitles = () => {
    const variantdropdown = $("#dropdown-variant");
    let i = 0;
    let index = 0;
    for (i = 0; i < variantdropdown.children.length; i++) {
      index = variantsettings[0].indexOf(variantdropdown.children[i].value);
      if (index < 0) {
        continue;
      }
      variantdropdown.children[i].title = variantsettings[2][index];
    }
  };

  const updateVariantDropdown = () => {
    const varianttypedropdown = $("#dropdown-varianttype");
    const variantdropdown = $("#dropdown-variant");
    const selectedtype =
      varianttypedropdown[varianttypedropdown.selectedIndex].value;
    if (selectedtype == "") {
      variants = [""].concat(allvariants);
    } else if (selectedtype == "<|NC|>") {
      let tmpvariants = [""];
      allvariants.forEach((val) => {
        if (!variantsettings[0].includes(val)) {
          tmpvariants.push(val);
        }
      });
      variants = tmpvariants;
    } else {
      let tmpvariants = [];
      allvariants.forEach((val) => {
        if (getVariantType(val) == selectedtype) {
          tmpvariants.push(val);
        }
      });
      variants = tmpvariants;
    }
    while (variantdropdown.children.length > 0) {
      variantdropdown.removeChild(variantdropdown[0]);
    }
    variants.forEach((val) => {
      let option = document.createElement("option");
      let name = "(default)";
      let title = getVariantDescription(val, true);
      if (val != "") {
        name = getVariantName(val, true, true);
      }
      option.value = val;
      option.text = name;
      if (title != "") {
        option.title = title;
      }
      variantdropdown.appendChild(option);
    });
    let chess_index_in_variants = variants.indexOf("chess");
    variantdropdown.selectedIndex =
      chess_index_in_variants < 0 ? 0 : chess_index_in_variants;
    //updateVariantDropdownTitles();
  };

  const updateVariantTypeDropdown = () => {
    const varianttypedropdown = $("#dropdown-varianttype");
    while (varianttypedropdown.children.length > 2) {
      varianttypedropdown.removeChild(varianttypedropdown[2]);
    }
    let varianttypevariantcount = [[], []];
    variantsettings[1].forEach((val) => {
      if (varianttypevariantcount[0].includes(val)) {
        return;
      }
      varianttypevariantcount[0].push(val);
      varianttypevariantcount[1].push(0);
    });
    console.log(allvariants);
    variantsettings[0].forEach((val, ind) => {
      if (allvariants.includes(val)) {
        let index = varianttypevariantcount[0].indexOf(variantsettings[1][ind]);
        if (index >= 0) {
          varianttypevariantcount[1][index]++;
        }
      }
    });
    console.log(varianttypevariantcount);
    varianttypevariantcount[0].forEach((val, ind) => {
      if (varianttypevariantcount[1][ind] > 0) {
        if (!varianttypes.includes(val)) {
          varianttypes.push(val);
        }
      }
    });
    varianttypes.sort();
    varianttypes.forEach((val) => {
      let option = document.createElement("option");
      option.text = val;
      option.value = val;
      varianttypedropdown.appendChild(option);
    });
    varianttypedropdown.selectedIndex = 0;
    changing_variant_type = true;
    $("#dropdown-variant").dispatchEvent(new Event("change"));
    // Both the engine and the variant subsystem are up by now, so a
    // variant or position asked for in the URL can be applied.
    if (stockfish_state == "READY" && allvariants.length > 0) {
      applyUrlState();
    }
  };

  const updateUIThemeDropdown = (ui_id) => {
    const uithemedropdown = document.getElementById("dropdown-uitheme");
    uithemedropdown.selectedIndex = uithemes[0].indexOf(ui_id);
  };

  const setupUIThemeDropdown = () => {
    const uithemedropdown = document.getElementById("dropdown-uitheme");
    let i = 0;
    if (uithemes[0].length > 0) {
      while (uithemedropdown[0]) {
        uithemedropdown.removeChild(uithemedropdown[0]);
      }
      for (i = 0; i < uithemes[0].length; i++) {
        let option = document.createElement("option");
        option.value = uithemes[0][i];
        option.text = uithemes[1][i].Name;
        uithemedropdown.appendChild(option);
      }
    }
  };

  const scrollOutput = () => {
    //Mithril.js will automatically create a variable for an element that has ID, with its name the same as the ID
    output2.scrollTo({
      top: output2.scrollHeight,
      behavior: "instant",
    });
  };

  const displayGameResult = () => {
    if (review_mode || board_setup_mode) {
      return;
    }
    let elem = document.getElementById("gameresultcontainermain");
    while (elem) {
      document.body.removeChild(elem);
      elem = document.getElementById("gameresultcontainermain");
    }
    let div = document.createElement("div");
    div.id = "gameresultcontainermain";
    div.classList.add("inaccessble");
    div.style.position = "fixed";
    div.style.display = "flex";
    div.style.overflow = "hidden";
    div.style.top = "0";
    div.style.bottom = "0";
    div.style.left = "0";
    div.style.right = "0";
    div.style.justifyContent = "center";
    div.style.alignItems = "center";
    div.style.zIndex = "1000";
    div.style.background = "#0000";
    div.style.pointerEvents = "none";
    let span = document.createElement("spangameresult");
    span.innerText = $("#gameresult").value;
    div.appendChild(span);
    setTimeout(() => {
      span.style.opacity = "1";
      span.style.fontSize = "400px";
    }, 100);
    setTimeout(() => {
      span.style.opacity = "0";
      span.style.fontSize = "1px";
    }, 2600);
    document.body.appendChild(div);
  };

  const onMouseMoveBoardSetupIdentifier = (event) => {
    let identifier = document.getElementById("boardsetuppieceidentifier");
    identifier.style.left = `${event.clientX + 60}px`;
    identifier.style.top = `${event.clientY + 60}px`;
  };

  const triggerBoardSetupPieceIdentifier = (moveidentifier) => {
    let identifier = document.getElementById("boardsetuppieceidentifier");
    let fakeboard = document.getElementById("fakeboard");
    let fakewrap = document.getElementById("fakewrap");
    let fakeboardclasses = fakeboard.classList.value.split(" ");
    let chessgrounddiv = document.getElementById("chessground-board");
    let chessgroundcontainer = document.getElementById(
      "chessground-container-div",
    );
    fakeboardclasses[1] = chessgroundcontainer.classList[1];
    if (chessgrounddiv.classList.contains("orientation-white")) {
      fakewrap.classList.remove("orientation-black");
      fakewrap.classList.add("orientation-white");
      piece_palette_orientation = "white";
    } else if (chessgrounddiv.classList.contains("orientation-black")) {
      fakewrap.classList.remove("orientation-white");
      fakewrap.classList.add("orientation-black");
      piece_palette_orientation = "black";
    }
    fakeboard.classList.value = fakeboardclasses.join(" ");
    if (board_setup_mode) {
      if (moveidentifier) {
        let isboardsetuprect = document
          .getElementById("isboardsetup")
          .getBoundingClientRect();
        identifier.style.top = `${isboardsetuprect.top + 60}px`;
        identifier.style.left = `${isboardsetuprect.left + 60}px`;
      }
      document
        .getElementById("dropdown-setpiece")
        .dispatchEvent(new Event("change"));
      identifier.style.display = "block";
      document.addEventListener("mousemove", onMouseMoveBoardSetupIdentifier);
    } else {
      identifier.style.display = "";
      document.removeEventListener(
        "mousemove",
        onMouseMoveBoardSetupIdentifier,
      );
    }
  };

  // Make error catchable
  const loadStockfish = async (params) => {
    return await FairyStockfish(params);
  };

  const onFinishDownload = (data) => {
    if (!data) {
      stockfish_state = "FAILED";
      m.redraw();
      return;
    }

    loadStockfish({ wasmBinary: data })
      .then(
        (_stockfish) => {
          stockfish = _stockfish;
          window.stockfish = _stockfish;
          stockfish_state = "READY";
          stockfish.addMessageListener((line) => {
            if (
              ini_engine_quiet &&
              !/^(info |bestmove|option |id |uciok|readyok)/.test(line)
            ) {
              return;
            }
            if (line.startsWith("option")) {
              if (line.startsWith("option name UCI_Variant")) {
                allvariants = line
                  .replace(
                    "option name UCI_Variant type combo default chess var ",
                    "",
                  )
                  .replace(/ var /g, " ")
                  .split(" ")
                  .sort();
                console.log(
                  "Detected UCI_Variant parameter from Fairy-Stockfish. Updating variants and dropdowns...",
                );
                if (variantsystemready) {
                  updateVariantTypeDropdown();
                } else {
                  console.log(
                    "Note: Fairy-Stockfish loaded before variant subsystem.",
                  );
                }
              }
            } else if (line.startsWith(" ")) {
            } else {
              if (!review_mode && line.startsWith("bestmove") && play_move) {
                play_move = false;
                if (analysis_mode) {
                  return;
                }
                $("#move").value += " " + line.split(" ")[1];
                $("#set").click();
              }
              engineoutput += line + "\n";
              if (fge.state.analysis_engine instanceof fge.Engine) {
                if (!fge.state.analysis_engine.IsUsing) {
                  $("#engineoutputline").value = line;
                  $("#engineoutputline").click();
                }
              } else {
                $("#engineoutputline").value = line;
                $("#engineoutputline").click();
              }
            }
            m.redraw();
          });
          whenBundleReady(() => {
            loadMyVariantsIntoEngine();
            getVariants();
          });
        },
        (err) => {
          console.error(err);
          throw err;
        },
      )
      .catch((e) => {
        stockfish_state = "FAILED";
        window.alert(
          "There is something wrong with in browser Fairy-Stockfish. Press Ctrl+Shift+I to see more details.",
        );
        throw e;
      })
      .finally(() => m.redraw());
  };

  const onSelectNnueFile = async (e) => {
    const selected = e.currentTarget.files[0];
    if (selected) {
      //
      // TODO:
      // On Archlinux Chromium 92.0.4515.107, most of times this code fails with the error saying:
      //   TypeError: Failed to execute 'decode' on 'TextDecoder': The provided ArrayBufferView value must not be shared.
      // On the other hand, either Chrome with the same version or Firefox never fail.
      //
      const FS = stockfish.FS;
      const buffer = await selected.arrayBuffer();
      const array = new Uint8Array(buffer);
      const filename = "/" + selected.name;
      FS.writeFile(filename, array);
      stockfish.postMessage(`setoption name EvalFile value ${filename}`);
      // Automatically set variant
      const variant = selected.name.split(/[_.-]+/)[0];
      $("#dropdown-variant").value = variant;
      $("#dropdown-variant").dispatchEvent(new Event("change"));
    }
  };

  const onSelectVariantsFile = async (e) => {
    const selected = e.currentTarget.files[0];
    //console.log(`${selected}`);
    if (selected) {
      const FS = stockfish.FS;
      const buffer = await selected.arrayBuffer();
      const array = new Uint8Array(buffer);
      const filename = "/" + selected.name;
      FS.writeFile(filename, array);
      stockfish.postMessage(`check ${filename}`);
      stockfish.postMessage(`load ${filename}`);
      getVariants();
    }
  };

  function isLetter(str) {
    return str.length === 1 && str.match(/[a-z]/i);
  }

  function changePieceSet(piece_set, save_to_local_storage) {
    const el = document.getElementById("chessground-container-div");
    const chessgroundmini = document.getElementById(
      "chessground-mini-container-div",
    );
    let DOMListValue = el.classList.value.split(" ");
    DOMListValue[1] = piece_set;
    chessgroundmini.classList.value = el.classList.value =
      DOMListValue.join(" ");
    document.dispatchEvent(
      new CustomEvent("themechange", {
        detail: { piece: DOMListValue[1], board: DOMListValue[0] },
      }),
    );
    updateThemeDropdowns(piece_set, null);
    if (board_setup_mode) {
      triggerBoardSetupPieceIdentifier(false);
    }
    if (save_to_local_storage) {
      setVariantTheme(
        document.getElementById("dropdown-variant").value,
        piece_set,
        false,
      );
    }
  }

  function changeBoardSet(board_set, save_to_local_storage) {
    const el = document.getElementById("chessground-container-div");
    const chessgroundmini = document.getElementById(
      "chessground-mini-container-div",
    );
    let DOMListValue = el.classList.value.split(" ");
    DOMListValue[0] = board_set;
    chessgroundmini.classList.value = el.classList.value =
      DOMListValue.join(" ");
    document.dispatchEvent(
      new CustomEvent("themechange", {
        detail: { piece: DOMListValue[1], board: DOMListValue[0] },
      }),
    );
    updateThemeDropdowns(null, board_set);
    if (save_to_local_storage) {
      setVariantTheme(
        document.getElementById("dropdown-variant").value,
        board_set,
        true,
      );
    }
  }

  function changeUI(ui_id, save_to_local_storage, change_canvas) {
    if (uithemes[0].indexOf(ui_id) < 0) {
      return;
    }
    let index = uithemes[0].indexOf(ui_id);
    if (currentthemeobj) {
      currentthemeobj.CancelTimer();
      if (change_canvas) {
        currentthemeobj.CloseCanvas();
      }
    }
    currentthemeobj = uithemes[1][index];
    ApplyUIThemeStyleNode(uithemes[1][index].CurrentTheme());
    uithemes[1][index].NextTheme(() => {
      changeUI(ui_id, false, false);
    }, true);
    if (change_canvas) {
      uithemes[1][index].StartCanvasAnimation();
    }
    updateUIThemeDropdown(ui_id);
    document
      .getElementById("evalhistorycontainer")
      .dispatchEvent(new Event("redraw"));
    if (save_to_local_storage) {
      localStorage.setItem("UserSelectedUITheme", ui_id);
    }
  }

  const onSelectUserGraphics = async (e) => {
    var files_count = e.currentTarget.files.length;
    var files = [];

    if (!e.currentTarget.files.length) {
    } else {
      style = document.createElement("style");

      // See what files are being loaded.
      for (let i = 0; i < files_count; i++) {
        const selected = e.currentTarget.files[i];
        var filename = e.currentTarget.files[i].name.toLowerCase();

        files[files.length] = e.currentTarget.files[i];
      }

      console.log("File count: " + files.length);

      for (let i = 0; i < files.length; i++) {
        const selected = files[i];
        var bloburl = URL.createObjectURL(selected);
        var filename = files[i].name.split(".")[0].toLowerCase();
        var piececolor = filename.substr(0, 1);
        var pieceletter = filename.substr(1, 2).replace("+", "p");
        // Skip the file if it does not match the naming convention.
        if (piececolor == "b") {
          piececolor = "black";
        } else if (piececolor == "w") {
          piececolor = "white";
        } else {
          console.log(`File '${filename}' does not match naming convention.`);
          continue;
        }
        if (filename.length != 2 && filename.length != 3) {
          console.log(`File '${filename}' does not match naming convention.`);
          continue;
        }
        if (filename.length == 2 && !isLetter(filename.substr(1, 1))) {
          console.log(`File '${filename}' does not match naming convention.`);
          continue;
        }
        if (filename.length == 3 && filename.substr(1, 1) != "+") {
          console.log(`File '${filename}' does not match naming convention.`);
          continue;
        }
        if (filename.length == 3 && !isLetter(filename.substr(2, 1))) {
          console.log(`File '${filename}' does not match naming convention.`);
          continue;
        }
        //console.log(filename);
        //console.log(piececolor);
        //console.log(pieceletter);
        console.log(`${bloburl}`);
        //console.log(`${selected}`);
        if (selected) {
          style.textContent =
            style.textContent +
            `.userdefined .cg-wrap piece.${pieceletter}-piece.${piececolor} { background-image: url('${bloburl}');} `;
        }
      }

      //console.log(`${style.textContent}`);
      document.head.appendChild(style);

      changePieceSet("userdefined");
    }
  };

  const onSelectVariantSettings = async (e) => {
    const selected = e.currentTarget.files[0];
    if (selected) {
      let reader = new FileReader();
      reader.readAsText(selected);
      reader.onload = function () {
        console.log(reader.result);
        LoadVariantSettings("client", reader.result);
        updateVariantTypeDropdown();
      };
    }
  };

  const oninit = () => {
    stockfish_state = "LOADING";
  };

  // ---------------------------------------------------------------
  // UI state of the redesigned shell (tabs, drawer, dialogs)
  // ---------------------------------------------------------------
  let active_tab = "moves";
  let settings_open = false;
  let newgame_open = false;
  let engine_debug = false;
  let move_input = "either"; // "either" | "click" | "drag"
  let app_mode = "analysis"; // "analysis" | "play" | "setup"
  // Whether the game of play mode has ended, and how. This is the single
  // source of truth for the game end: the header buttons, the abort
  // button and the result display are all derived from it, and it is
  // only changed by startGame(), finishGame() and endGame().
  let game_over = false;
  let game_outcome = null; // { result, reason } once the game is over
  // Game settings chosen in the "New game" dialog (kept between games).
  const game_white = {
    player: "you",
    mode: "infinite",
    depth: 8,
    nodes: 4,
    movetime: 2,
  };
  const game_black = {
    player: "fsf",
    mode: "movetime",
    depth: 8,
    nodes: 4,
    movetime: 2,
  };
  let game_games = 1;
  let game_continue = false;
  let pgn_tools_open = false;
  // Search limit of the in browser engine per side while a game runs.
  let engine_limit_white = null;
  let engine_limit_black = null;
  let fen_copied = false;
  let variant_picker_open = false;
  let position_picker_open = false;
  let variant_search = "";
  let variant_filter = "";
  // Variant editor: variant definitions in the variants.ini format are
  // edited with live diagnostics, tried out under temporary names and
  // saved to "My variants" under their real names.
  const INI_STORAGE_KEY = "VariantEditorIni";
  const INI_TEMPLATE = [
    "# Define variants in the variants.ini format of Fairy-Stockfish.",
    "# Press Ctrl+Space for suggestions. Documentation:",
    "# https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Variant-configuration",
    "",
    "# 6x6 chess with an archbishop (bishop + knight) instead of bishops.",
    "[minicapa:chess]",
    "maxRank = 6",
    "maxFile = f",
    "bishop = -",
    "archbishop = a",
    "startFen = rnaqkr/pppppp/6/6/PPPPPP/RNAQKR w - - 0 1",
    "promotionRegionWhite = *6",
    "promotionRegionBlack = *1",
    "promotionPieceTypes = qarn",
    "doubleStep = false",
    "castling = false",
    "pieceToCharTable = -",
    "",
  ].join("\n");
  const MY_VARIANTS_TYPE = "My variants";
  let ini_text = (() => {
    try {
      const stored = localStorage.getItem(INI_STORAGE_KEY);
      return stored != null ? stored : INI_TEMPLATE;
    } catch (e) {
      return INI_TEMPLATE;
    }
  })();
  let ini_editor = null; // controller of the CodeMirror editor
  let ini_editor_state = "idle"; // "idle" | "loading" | "ready" | "failed"
  let ini_busy = false;
  let ini_messages = []; // [{ kind: "ok" | "error" | "info", text }]
  let ini_diagnostics = null; // live diagnostics, null until checked
  let ini_context = null; // option at the cursor
  let ini_preview = null; // Betza preview of the piece at the cursor
  let ini_option_search = "";
  let ini_try_counter = 0;
  // Temporary variants of "Try": id -> name, and the latest id per name.
  const ini_drafts = new Map();
  const ini_latest_draft = new Map();
  // Saved variants whose changed definition is used after a reload.
  const ini_pending_reload = new Set();
  // Hides the output of variant loading and checking from the engine
  // console.
  let ini_engine_quiet = false;
  let ini_engine_chain = Promise.resolve();

  const NOT_CLASSIFIED = "<|NC|>";
  const NOT_SUPPORTED = "(not supported)";
  const PSEUDO_VARIANTS = "Pseudo Variants";
  // Variant picker filter for the favorite variants.
  const FAVORITES_FILTER = "<|FAV|>";
  const FAVORITES_STORAGE_KEY = "FavoriteVariants";
  const favorite_variants = new Set(
    (() => {
      try {
        const stored = JSON.parse(localStorage.getItem(FAVORITES_STORAGE_KEY));
        return Array.isArray(stored) ? stored : [];
      } catch (e) {
        return [];
      }
    })(),
  );
  const toggleFavorite = (id) => {
    if (favorite_variants.has(id)) {
      favorite_variants.delete(id);
    } else {
      favorite_variants.add(id);
    }
    try {
      localStorage.setItem(
        FAVORITES_STORAGE_KEY,
        JSON.stringify([...favorite_variants]),
      );
    } catch (e) {
      console.warn("Cannot store the favorite variants:", e);
    }
  };
  const currentVariantId = () => {
    const dropdown = document.getElementById("dropdown-variant");
    return dropdown ? dropdown.value : "";
  };
  const variantDisplayName = (id) =>
    id == "" ? "Loading..." : getVariantName(id, true, false);
  const variantTypeLabel = (type) =>
    type == NOT_CLASSIFIED || !type ? "Other" : type;
  const positionVariantsFor = (id) => {
    if (!window.fairyground || !window.fairyground.GetPositionVariants) {
      return undefined;
    }
    const key = (id == "" ? "chess" : id) + (fischer_random_mode ? "960" : "");
    return window.fairyground.GetPositionVariants(key);
  };
  const selectVariant = (id) => {
    const typedropdown = document.getElementById("dropdown-varianttype");
    const variantdropdown = document.getElementById("dropdown-variant");
    if (!typedropdown || !variantdropdown) {
      return;
    }
    let present = false;
    for (let i = 0; i < variantdropdown.length; i++) {
      if (variantdropdown[i].value == id) {
        present = true;
        break;
      }
    }
    if (!present) {
      typedropdown.value = "";
      updateVariantDropdown();
    }
    changing_variant_type = false;
    variantdropdown.value = id;
    variantdropdown.dispatchEvent(new Event("change"));
    variant_picker_open = false;
    window.setTimeout(() => m.redraw(), 200);
  };

  const variantEditorApi = () =>
    window.fairyground && window.fairyground.VariantEditor;
  const myVariantsApi = () =>
    window.fairyground && window.fairyground.MyVariants;
  const myVariants = () =>
    myVariantsApi() ? myVariantsApi().loadLibrary() : [];
  const isMyVariant = (id) => myVariants().some((e) => e.name == id);
  // Shows a variant of the editor in the variant picker.
  const registerEditorVariant = (id, name, description) => {
    const index = variantsettings[0].indexOf(id);
    if (index >= 0) {
      variantsettings[2][index] = name;
      variantsettings[3][index] = description;
      return;
    }
    variantsettings[0].push(id);
    variantsettings[1].push(MY_VARIANTS_TYPE);
    variantsettings[2].push(name);
    variantsettings[3].push(description);
    variantsettings[4].push("");
  };

  // Loads the saved variants into the engine. ffish.js loads them in
  // main.js.
  const loadMyVariantsIntoEngine = () => {
    const entries = myVariants();
    if (entries.length == 0) {
      return;
    }
    const filename = "/fairyground-my-variants.ini";
    stockfish.FS.writeFile(filename, myVariantsApi().libraryText(entries));
    stockfish.postMessage(`load ${filename}`);
    entries.forEach((entry) =>
      registerEditorVariant(
        entry.name,
        entry.name,
        "Saved in the variant editor.",
      ),
    );
  };
  // The saved variants are read by bundle.js, which may still load.
  const whenBundleReady = (callback) => {
    if (myVariantsApi() || document.readyState != "loading") {
      callback();
    } else {
      document.addEventListener("DOMContentLoaded", () => callback(), {
        once: true,
      });
    }
  };

  // Runs engine commands for the variant editor one after another.
  const queueEngineTask = (task) => {
    ini_engine_chain = ini_engine_chain.then(task, task);
    return ini_engine_chain;
  };
  // Checks a variants.ini with the engine and returns its messages, or
  // null if the engine is not available.
  const checkIniWithEngine = (text) =>
    queueEngineTask(
      () =>
        new Promise((resolve) => {
          if (stockfish_state != "READY" || !stockfish) {
            resolve(null);
            return;
          }
          const filename = "/fairyground-variant-check.ini";
          const output = [];
          let timer = null;
          const listener = (line) => {
            if (line == "readyok") {
              done();
            } else if (!/^(info|bestmove) /.test(line)) {
              output.push(line);
            }
          };
          const done = () => {
            window.clearTimeout(timer);
            stockfish.removeMessageListener(listener);
            ini_engine_quiet = false;
            resolve(output);
          };
          stockfish.FS.writeFile(filename, text);
          ini_engine_quiet = true;
          stockfish.addMessageListener(listener);
          stockfish.postMessage(`check ${filename}`);
          stockfish.postMessage(`isready`);
          timer = window.setTimeout(done, 3000);
        }),
    );
  // Loads a variants.ini into ffish.js and the engine. Resolves when
  // the engine reported its updated list of variants.
  const loadIniIntoEngine = (text, filename) =>
    queueEngineTask(
      () =>
        new Promise((resolve) => {
          const ffish = window.ffishlib;
          if (stockfish_state != "READY" || !stockfish || !ffish) {
            resolve(false);
            return;
          }
          try {
            ffish.loadVariantConfig(text);
            stockfish.FS.writeFile(filename, text);
          } catch (e) {
            console.error(e);
            resolve(false);
            return;
          }
          const listener = (line) => {
            if (line == "uciok") {
              stockfish.removeMessageListener(listener);
              ini_engine_quiet = false;
              resolve(true);
            }
          };
          ini_engine_quiet = true;
          stockfish.addMessageListener(listener);
          stockfish.postMessage(`load ${filename}`);
          getVariants();
        }),
    );
  const isLoadedVariant = (id) =>
    allvariants.includes(id) &&
    window.ffishlib &&
    window.ffishlib.variants().split(" ").includes(id);

  const setIniText = (text) => {
    ini_text = text;
    try {
      localStorage.setItem(INI_STORAGE_KEY, text);
    } catch (e) {
      console.warn("Cannot store the variant definition:", e);
    }
  };
  const setEditorText = (text) => {
    setIniText(text);
    if (ini_editor) {
      ini_editor.setText(text);
    }
  };
  const editorHasUnsavedText = () => {
    const api = variantEditorApi();
    if (!api || ini_text.trim() == "" || ini_text == INI_TEMPLATE) {
      return false;
    }
    const saved = new Map(myVariants().map((e) => [e.name, e.text]));
    const sections = api.sectionTexts(ini_text);
    return (
      sections.length == 0 || sections.some((s) => saved.get(s.name) != s.text)
    );
  };
  // Problems with the name of a variant that the engine does not know.
  const iniNameProblem = (name) => {
    if (
      allvariants.includes(name) &&
      !isMyVariant(name) &&
      !ini_drafts.has(name)
    ) {
      return `There is a built-in variant named ${name}. Use another name to save it to My variants.`;
    }
    return null;
  };
  const iniErrorCount = () =>
    ini_diagnostics
      ? ini_diagnostics.filter((d) => d.severity == "error").length
      : 0;
  // The variant to show after loading: the one at the cursor, or the
  // last one.
  const variantToShow = (names) => {
    const current = ini_editor ? ini_editor.currentSection() : null;
    return names.includes(current) ? current : names[names.length - 1];
  };

  // Loads the variants of the editor under temporary names and shows
  // one of them on the board.
  const tryIni = async (keepmessages) => {
    const api = variantEditorApi();
    if (ini_busy || !api) {
      return;
    }
    const sections = api.parseIni(ini_text).sections;
    if (sections.length == 0) {
      ini_messages = [
        {
          kind: "error",
          text: "No variant found. Start a variant with a section header like [myvariant:chess].",
        },
      ];
      return;
    }
    ini_busy = true;
    if (keepmessages !== true) {
      ini_messages = [];
    }
    const n = ++ini_try_counter;
    const ids = new Map();
    const text = api.renameSections(ini_text, (name) => {
      const id = `${name}-try${n}`;
      ids.set(name, id);
      return id;
    });
    const loaded = await loadIniIntoEngine(text, `/fairyground-try-${n}.ini`);
    const shown = [];
    ids.forEach((id, name) => {
      if (loaded && isLoadedVariant(id)) {
        ini_drafts.set(id, name);
        ini_latest_draft.set(name, id);
        registerEditorVariant(
          id,
          `${name} (draft)`,
          "Draft from the variant editor.",
        );
        shown.push(name);
      } else {
        ini_messages.push({
          kind: "error",
          text: `${name} could not be loaded. See the problems above.`,
        });
      }
    });
    if (shown.length > 0) {
      const name = variantToShow(shown);
      ini_messages.push({
        kind: "ok",
        text: `Trying ${name} on the board.`,
      });
      // The engine resets the variant after updating the variant
      // list, so select it once that has settled.
      window.setTimeout(() => {
        selectVariant(ini_latest_draft.get(name));
        ini_busy = false;
        m.redraw();
      }, 50);
    } else {
      ini_busy = false;
    }
    m.redraw();
  };

  // Saves the variants of the editor to My variants and loads them
  // under their names.
  const saveIniToMyVariants = async () => {
    const api = variantEditorApi();
    const library = myVariantsApi();
    if (ini_busy || !api || !library) {
      return;
    }
    const sections = api.sectionTexts(ini_text);
    if (sections.length == 0) {
      ini_messages = [
        {
          kind: "error",
          text: "No variant found. Start a variant with a section header like [myvariant:chess].",
        },
      ];
      return;
    }
    const names = sections.map((s) => s.name);
    const invalid = sections.filter(
      (s, i) =>
        s.name == "" ||
        /\s/.test(s.name) ||
        names.indexOf(s.name) != i ||
        iniNameProblem(s.name),
    );
    if (invalid.length > 0) {
      ini_messages = invalid.map((s) => ({
        kind: "error",
        text:
          iniNameProblem(s.name) ||
          `Cannot save the variant "${s.name}": use a unique name without spaces.`,
      }));
      return;
    }
    if (
      iniErrorCount() > 0 &&
      !window.confirm(
        "The definition has errors. Save it to My variants anyway?",
      )
    ) {
      return;
    }
    ini_busy = true;
    ini_messages = [];
    const entries = library.loadLibrary();
    const fresh = [];
    const changed = [];
    sections.forEach((section) => {
      const index = entries.findIndex((e) => e.name == section.name);
      const unchanged = index >= 0 && entries[index].text == section.text;
      if (index >= 0) {
        entries[index] = section;
      } else {
        entries.push(section);
      }
      if (!allvariants.includes(section.name)) {
        fresh.push(section);
      } else if (!unchanged || ini_pending_reload.has(section.name)) {
        changed.push(section.name);
      }
    });
    if (!library.saveLibrary(entries)) {
      ini_busy = false;
      ini_messages = [
        {
          kind: "error",
          text: "Cannot save: the storage of the browser is not available.",
        },
      ];
      return;
    }
    if (fresh.length > 0) {
      await loadIniIntoEngine(
        library.libraryText(fresh),
        "/fairyground-save.ini",
      );
    }
    const loaded = fresh
      .map((s) => s.name)
      .filter((name) => isLoadedVariant(name));
    loaded.forEach((name) =>
      registerEditorVariant(name, name, "Saved in the variant editor."),
    );
    changed.forEach((name) => ini_pending_reload.add(name));
    ini_messages.push({
      kind: "ok",
      text: `Saved ${names.join(", ")} to My variants.`,
    });
    fresh
      .filter((s) => !loaded.includes(s.name))
      .forEach((s) =>
        ini_messages.push({
          kind: "error",
          text: `${s.name} could not be loaded. See the problems above.`,
        }),
      );
    if (changed.length > 0) {
      ini_messages.push({
        kind: "info",
        text: `The changed definition of ${changed.join(", ")} is used under its name after reloading the page. Until then it is shown as a draft.`,
      });
    }
    ini_busy = false;
    const show = variantToShow(names);
    if (changed.includes(show)) {
      tryIni(true);
    } else if (loaded.includes(show)) {
      window.setTimeout(() => {
        selectVariant(show);
        m.redraw();
      }, 50);
    }
    m.redraw();
  };

  const editMyVariant = (entry) => {
    if (
      editorHasUnsavedText() &&
      !window.confirm(
        "The editor has unsaved changes. Replace them with " + entry.name + "?",
      )
    ) {
      return;
    }
    setEditorText(entry.text + "\n");
    ini_messages = [];
  };
  const deleteMyVariant = (entry) => {
    const library = myVariantsApi();
    if (!library) {
      return;
    }
    const children = library
      .loadLibrary()
      .filter((e) => library.templateOf(e) == entry.name)
      .map((e) => e.name);
    if (children.length > 0) {
      ini_messages = [
        {
          kind: "error",
          text: `Cannot delete ${entry.name}: ${children.join(", ")} ${children.length == 1 ? "is" : "are"} based on it.`,
        },
      ];
      return;
    }
    if (
      !window.confirm(
        `Delete ${entry.name} from My variants? It stays available until the page is reloaded.`,
      )
    ) {
      return;
    }
    library.saveLibrary(
      library.loadLibrary().filter((e) => e.name != entry.name),
    );
    ini_pending_reload.delete(entry.name);
    ini_messages = [
      { kind: "info", text: `Deleted ${entry.name} from My variants.` },
    ];
  };

  let ini_preview_timer = null;
  const onIniContext = (context) => {
    ini_context = context;
    window.clearTimeout(ini_preview_timer);
    const api = variantEditorApi();
    if (!context.betza || !api || !window.ffishlib) {
      ini_preview = null;
      m.redraw();
      return;
    }
    const betza = context.betza;
    // Computing a preview takes a moment, so wait for a pause.
    ini_preview_timer = window.setTimeout(() => {
      try {
        ini_preview = {
          betza,
          result: api.betzaPreview(window.ffishlib, betza),
        };
      } catch (e) {
        console.warn("Cannot compute the Betza preview:", e);
        ini_preview = { betza, result: null };
      }
      m.redraw();
    }, 150);
    if (ini_preview && ini_preview.betza != betza) {
      ini_preview = null;
    }
    m.redraw();
  };

  const loadVariantEditor = () => {
    if (ini_editor_state != "idle") {
      return;
    }
    ini_editor_state = "loading";
    const script = document.createElement("script");
    script.src = "./lib/varianteditor.js";
    script.async = true;
    script.onload = () => {
      ini_editor_state = variantEditorApi() ? "ready" : "failed";
      m.redraw();
    };
    script.onerror = () => {
      ini_editor_state = "failed";
      m.redraw();
    };
    document.head.appendChild(script);
  };
  const mountVariantEditor = (dom) => {
    const api = variantEditorApi();
    if (ini_editor || ini_editor_state != "ready" || !api) {
      return;
    }
    ini_editor = api.createVariantEditor({
      parent: dom,
      doc: ini_text,
      onChange: setIniText,
      onContext: onIniContext,
      onDiagnostics: (diagnostics) => {
        ini_diagnostics = diagnostics;
        m.redraw();
      },
      onRun: () => {
        tryIni();
        m.redraw();
      },
      runCheck: checkIniWithEngine,
      nameProblem: iniNameProblem,
      variantNames: () => allvariants.filter((id) => !ini_drafts.has(id)),
    });
  };

  const openIniFile = (e) => {
    const selected = e.currentTarget.files[0];
    e.currentTarget.value = "";
    if (!selected) {
      return;
    }
    if (
      editorHasUnsavedText() &&
      !window.confirm(
        `The editor has unsaved changes. Replace them with ${selected.name}?`,
      )
    ) {
      return;
    }
    selected.text().then((text) => {
      setEditorText(text);
      ini_messages = [{ kind: "info", text: `Opened ${selected.name}.` }];
      m.redraw();
    });
  };
  const downloadIniFile = () => {
    const url = URL.createObjectURL(
      new Blob([ini_text], { type: "text/plain" }),
    );
    const link = document.createElement("a");
    link.href = url;
    link.download = "variants.ini";
    document.body.appendChild(link);
    link.click();
    link.remove();
    window.setTimeout(() => URL.revokeObjectURL(url), 1000);
  };
  // Example value when an option is added from the option search.
  const exampleValue = (option) => {
    if (option.type == "Piece") {
      return option.key[0];
    }
    if (option.type == "CustomPiece") {
      return "a:W";
    }
    if (option.default !== null) {
      return option.default;
    }
    if (option.values) {
      return option.values[0];
    }
    return "";
  };
  const selectPosition = (type, name) => {
    const typedropdown = document.getElementById("dropdown-posvarianttype");
    const namedropdown = document.getElementById("dropdown-posvariantname");
    if (!typedropdown || !namedropdown) {
      return;
    }
    // While the board editor is active the board shows the editor's
    // own state, so leave it, apply the position and re-enter it.
    const editor = document.getElementById("isboardsetup");
    const wasediting = editor && editor.checked;
    if (wasediting) {
      editor.click();
    }
    typedropdown.value = type;
    typedropdown.dispatchEvent(new Event("change"));
    if (type != "(default)") {
      namedropdown.value = name;
      namedropdown.dispatchEvent(new Event("change"));
    }
    position_picker_open = false;
    window.setTimeout(() => {
      if (
        wasediting &&
        editor &&
        !editor.checked &&
        !board_setup_mode &&
        !review_mode &&
        !advanced_time_control &&
        !engine_match_mode
      ) {
        editor.click();
      }
      m.redraw();
    }, 300);
  };

  // ---------------------------------------------------------------
  // Deep links
  //
  // The query string can carry the variant and the position, so that a
  // board can be shared and reopened exactly as it is:
  //   ?variant=<id>&fen=<FEN>&moves=<UCI moves>&chess960=1
  // It is read once on startup. The address bar is left alone after
  // that; the share button builds the link when it is clicked.
  // ---------------------------------------------------------------
  const SHARE_URL_MAX_LENGTH = 1800;
  let url_state_applied = false;
  let share_copied = false;

  const readUrlState = () => {
    const params = new URLSearchParams(window.location.search);
    const value = (name) => {
      const raw = params.get(name);
      return raw == null ? "" : raw.trim();
    };
    return {
      variant: value("variant"),
      fen: value("fen"),
      moves: value("moves"),
      chess960: ["1", "true", "yes", "on"].includes(
        value("chess960").toLowerCase(),
      ),
    };
  };

  const buildShareUrl = () => {
    const url = new URL(window.location.href);
    // Share the site root rather than .../index.html.
    url.pathname = url.pathname.replace(/index\.html$/, "");
    url.hash = "";
    const field = (id) => {
      const element = document.getElementById(id);
      if (!element) {
        return "";
      }
      return (element.value ?? element.textContent ?? "").trim();
    };
    const build = (withmoves) => {
      const params = new URLSearchParams();
      const variant = currentVariantId();
      if (variant != "" && variant != "chess") {
        params.set("variant", variant);
      }
      if (fischer_random_mode) {
        params.set("chess960", "1");
      }
      const startfen = field("fen");
      const moves = field("move");
      if (withmoves) {
        // The start position plus the moves keeps the whole game.
        if (startfen != "") {
          params.set("fen", startfen);
        }
        if (moves != "") {
          params.set("moves", moves);
        }
      } else {
        const currentfen = field("currentboardfen");
        if (currentfen != "") {
          params.set("fen", currentfen);
        }
      }
      url.search = params.toString();
      return url.toString();
    };
    const withmoves = build(true);
    // Long games would make the link unwieldy, so fall back to sharing
    // the current position only.
    return withmoves.length > SHARE_URL_MAX_LENGTH ? build(false) : withmoves;
  };

  const applyUrlState = () => {
    if (url_state_applied) {
      return;
    }
    url_state_applied = true;
    const state = readUrlState();
    if (state.variant != "" && !allvariants.includes(state.variant)) {
      console.warn(
        `Unknown variant '${state.variant}' in the URL. Ignoring it.`,
      );
      state.variant = "";
    }
    const chess960 = document.getElementById("isfischerrandommode");
    if (chess960 && chess960.checked != state.chess960) {
      chess960.click();
    }
    if (state.variant == "") {
      selectVariant("chess");
    } else {
      selectVariant(state.variant);
    }
    if (state.fen == "" && state.moves == "") {
      return;
    }
    // Changing the variant reloads the board, so set the position once
    // that has settled.
    window.setTimeout(() => {
      const fenfield = document.getElementById("fen");
      const movefield = document.getElementById("move");
      const setpos = document.getElementById("setpos");
      if (!fenfield || !movefield || !setpos) {
        return;
      }
      fenfield.value = state.fen;
      movefield.value = state.moves;
      m.redraw.sync();
      if (!setpos.disabled) {
        setpos.click();
      }
    }, 300);
  };

  const shareBoard = () => {
    const url = buildShareUrl();
    if (navigator.share) {
      navigator.share({ title: "fairyground", url }).catch(() => undefined);
      return;
    }
    Promise.resolve(copyText(url)).catch((e) => {
      console.warn("Cannot copy the share link:", e);
      window.prompt("Copy the link to this board:", url);
    });
    share_copied = true;
    window.setTimeout(() => {
      share_copied = false;
      m.redraw();
    }, 1500);
  };

  const ICONS = {
    first: "M19 20 9 12l10-8v16zM5 19V5",
    prev: "m15 18-6-6 6-6",
    next: "m9 18 6-6-6-6",
    last: "m5 4 10 8-10 8V4zM19 5v14",
    current:
      "M12 22a10 10 0 1 0 0-20 10 10 0 0 0 0 20zM12 18a6 6 0 1 0 0-12 6 6 0 0 0 0 12zM12 14a2 2 0 1 0 0-4 2 2 0 0 0 0 4z",
    goto: "M11 19a8 8 0 1 0 0-16 8 8 0 0 0 0 16zM21 21l-4.3-4.3",
    flip: "M3 12a9 9 0 0 1 15.5-6.3L21 8M21 3v5h-5M21 12a9 9 0 0 1-15.5 6.3L3 16M3 21v-5h5",
    undo: "M3 7v6h6M3 13a9 9 0 1 0 3-6.7L3 9",
    gear: "M12 15a3 3 0 1 0 0-6 3 3 0 0 0 0 6zM19.4 15a1.7 1.7 0 0 0 .3 1.8l.1.1a2 2 0 1 1-2.8 2.8l-.1-.1a1.7 1.7 0 0 0-1.8-.3 1.7 1.7 0 0 0-1 1.5V21a2 2 0 1 1-4 0v-.1a1.7 1.7 0 0 0-1.1-1.5 1.7 1.7 0 0 0-1.8.3l-.1.1a2 2 0 1 1-2.8-2.8l.1-.1a1.7 1.7 0 0 0 .3-1.8 1.7 1.7 0 0 0-1.5-1H3a2 2 0 1 1 0-4h.1a1.7 1.7 0 0 0 1.5-1.1 1.7 1.7 0 0 0-.3-1.8l-.1-.1a2 2 0 1 1 2.8-2.8l.1.1a1.7 1.7 0 0 0 1.8.3H9a1.7 1.7 0 0 0 1-1.5V3a2 2 0 1 1 4 0v.1a1.7 1.7 0 0 0 1 1.5 1.7 1.7 0 0 0 1.8-.3l.1-.1a2 2 0 1 1 2.8 2.8l-.1.1a1.7 1.7 0 0 0-.3 1.8V9a1.7 1.7 0 0 0 1.5 1H21a2 2 0 1 1 0 4h-.1a1.7 1.7 0 0 0-1.5 1z",
    moon: "M21 12.8A9 9 0 1 1 11.2 3 7 7 0 0 0 21 12.8z",
    edit: "M11 4H4a2 2 0 0 0-2 2v14a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2v-7M18.5 2.5a2.1 2.1 0 0 1 3 3L12 15l-4 1 1-4 9.5-9.5z",
    move: "M5 9l-3 3 3 3M9 5l3-3 3 3M15 19l-3 3-3-3M19 9l3 3-3 3M2 12h20M12 2v20",
    check: "m20 6-11 11-5-5",
    copy: "M20 9h-9a2 2 0 0 0-2 2v9a2 2 0 0 0 2 2h9a2 2 0 0 0 2-2v-9a2 2 0 0 0-2-2zM5 15H4a2 2 0 0 1-2-2V4a2 2 0 0 1 2-2h9a2 2 0 0 1 2 2v1",
    arrowup: "M12 19V5M5 12l7-7 7 7",
    chevronsup: "m17 11-5-5-5 5M17 18l-5-5-5 5",
    arrowupright: "M7 17 17 7M7 7h10v10",
    crop: "M6 2v14a2 2 0 0 0 2 2h14M18 22V8a2 2 0 0 0-2-2H2",
    lineonly: "M12 3v6M12 15v6M12 15a3 3 0 1 0 0-6 3 3 0 0 0 0 6z",
    branchx:
      "M6 3v12M6 21a3 3 0 1 0 0-6 3 3 0 0 0 0 6zM18 9a3 3 0 1 0 0-6 3 3 0 0 0 0 6zM18 9a9 9 0 0 1-9 9M14 15l6 6M20 15l-6 6",
    branchcut:
      "M6 3v12M6 21a3 3 0 1 0 0-6 3 3 0 0 0 0 6zM18 9a3 3 0 1 0 0-6 3 3 0 0 0 0 6zM18 9a9 9 0 0 1-9 9M13 13l7 7M20 13l-7 7",
    commentx:
      "M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2zM9.5 7.5l5 5M14.5 7.5l-5 5",
    commentclear:
      "M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2zM8 10l8 0M8 13h5",
    commentbefore:
      "M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2zM10 7.5l-3 3 3 3M7 10.5h8",
    commentafter:
      "M21 15a2 2 0 0 1-2 2H7l-4 4V5a2 2 0 0 1 2-2h14a2 2 0 0 1 2 2zM14 7.5l3 3-3 3M17 10.5H9",
    collapse:
      "M8 3v3a2 2 0 0 1-2 2H3M21 8h-3a2 2 0 0 1-2-2V3M3 16h3a2 2 0 0 1 2 2v3M16 21v-3a2 2 0 0 1 2-2h3",
    eraser:
      "m20 20-9 0M7.4 20 2.6 15.2a2 2 0 0 1 0-2.8L13.2 1.8a2 2 0 0 1 2.8 0l5.6 5.6a2 2 0 0 1 0 2.8L11.4 20",
    doc: "M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8zM14 2v6h6M16 13H8M16 17H8M10 9H8",
    eyeoff:
      "M17.9 17.9A10 10 0 0 1 12 20c-7 0-11-8-11-8a18 18 0 0 1 5.1-6M9.9 4.2A9 9 0 0 1 12 4c7 0 11 8 11 8a18 18 0 0 1-2.2 3.2M14.1 14.1a3 3 0 1 1-4.2-4.2M1 1l22 22",
    redo: "M21 7v6h-6M21 13a9 9 0 1 1-3-6.7L21 9",
    save: "M19 21H5a2 2 0 0 1-2-2V5a2 2 0 0 1 2-2h11l5 5v11a2 2 0 0 1-2 2zM17 21v-8H7v8M7 3v5h8",
    image: "M3 5h18v14H3zM3 15l5-5 4 4 3-3 6 6M15 9h.01",
    expand: "M15 3h6v6M9 21H3v-6M21 3l-7 7M3 21l7-7",
    flag: "M4 15s1-1 4-1 5 2 8 2 4-1 4-1V3s-1 1-4 1-5-2-8-2-4 1-4 1v12zM4 22v-7",
    chev: "m6 9 6 6 6-6",
    grid: "M3 3h7v7H3zM14 3h7v7h-7zM14 14h7v7h-7zM3 14h7v7H3z",
    github:
      "M9 19c-5 1.5-5-2.5-7-3m14 6v-3.9a3.4 3.4 0 0 0-.9-2.6c3.1-.3 6.4-1.5 6.4-7A5.4 5.4 0 0 0 20 4.8 5 5 0 0 0 19.9 1s-1.2-.3-3.9 1.5a13.4 13.4 0 0 0-7 0C6.3.7 5.1 1 5.1 1A5 5 0 0 0 5 4.8a5.4 5.4 0 0 0-1.5 3.8c0 5.4 3.3 6.6 6.4 7a3.4 3.4 0 0 0-.9 2.6V22",
    play: "m6 4 14 8-14 8V4z",
    stop: "M6 6h12v12H6z",
    plus: "M12 5v14M5 12h14",
    x: "M18 6 6 18M6 6l12 12",
    info: "M12 22a10 10 0 1 0 0-20 10 10 0 0 0 0 20zM12 16v-4M12 8h.01",
    book: "M4 19.5A2.5 2.5 0 0 1 6.5 17H20M4 19.5A2.5 2.5 0 0 0 6.5 22H20V2H6.5A2.5 2.5 0 0 0 4 4.5v15z",
    list: "M8 6h13M8 12h13M8 18h13M3 6h.01M3 12h.01M3 18h.01",
    cpu: "M4 4h16v16H4zM9 9h6v6H9zM9 1v3M15 1v3M9 20v3M15 20v3M20 9h3M20 14h3M1 9h3M1 14h3",
    sliders:
      "M4 21v-7M4 10V3M12 21v-9M12 8V3M20 21v-5M20 12V3M1 14h6M9 8h6M17 16h6",
    terminal: "m4 17 6-6-6-6M12 19h8",
    code: "m16 18 6-6-6-6M8 6l-6 6 6 6",
    star: "M12 2.5l2.9 6 6.6.9-4.8 4.6 1.2 6.5-5.9-3.2-5.9 3.2 1.2-6.5-4.8-4.6 6.6-.9z",
    wall: "M3 3h18v18H3zM3 9h18M3 15h18M9 9v6M15 3v6M15 15v6",
    skip: "m5 4 10 8-10 8V4zM19 5v14",
    user: "M20 21v-2a4 4 0 0 0-4-4H8a4 4 0 0 0-4 4v2M12 11a4 4 0 1 0 0-8 4 4 0 0 0 0 8z",
    link: "M10 13a5 5 0 0 0 7.5.5l3-3a5 5 0 0 0-7-7l-1.7 1.7M14 11a5 5 0 0 0-7.5-.5l-3 3a5 5 0 0 0 7 7l1.7-1.7",
    clock: "M12 22a10 10 0 1 0 0-20 10 10 0 0 0 0 20zM12 6v6l4 2",
    target:
      "M12 22a10 10 0 1 0 0-20 10 10 0 0 0 0 20zM12 18a6 6 0 1 0 0-12 6 6 0 0 0 0 12zM12 14a2 2 0 1 0 0-4 2 2 0 0 0 0 4z",
    swap: "M17 1l4 4-4 4M3 11V9a4 4 0 0 1 4-4h14M7 23l-4-4 4-4M21 13v2a4 4 0 0 1-4 4H3",
    send: "m22 2-7 20-4-9-9-4 20-7z",
    trash: "M3 6h18M8 6V4h8v2M19 6l-1 14H6L5 6M10 11v6M14 11v6",
    upload: "M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4M17 8l-5-5-5 5M12 3v12",
    install: "M12 3v12M8 11l4 4 4-4M3 17v2a2 2 0 0 0 2 2h14a2 2 0 0 0 2-2v-2",
    dice: "m 7,4.5 a 3,3 0 0 0 -3,3 v 10 a 3,3 0 0 0 3,3 h 10 a 3,3 0 0 0 3,-3 v -10 a 3,3 0 0 0 -3,-3 z M 8,10 a 1.5,1.5 0 1 1 0,-3 1.5,1.5 0 0 1 0,3 m 8,0 a 1.5,1.5 0 1 1 0,-3 1.5,1.5 0 0 1 0,3 m 1.5,6.5 a 1.5,1.5 0 1 1 -3,0 1.5,1.5 0 0 1 3,0 M 8,18 a 1.5,1.5 0 1 1 0,-3 1.5,1.5 0 0 1 0,3",
    diamond:
      "m 10.95097,4.435 c 0.58,-0.58 1.52,-0.58 2.1,0 l 6.515,6.516 c 0.58,0.58 0.58,1.519 0,2.098 l -6.515,6.516 c -0.58,0.58 -1.519,0.58 -2.098,0 L 4.4359698,13.05 a 1.48,1.48 0 0 1 0,-2.098 z",
    border:
      "M 4,4 H 20 V 20 H 4 Z m 1,1 v 6.5 h 6.5 V 5 Z m 7.5,0 v 6.5 H 19 V 5 Z M 19,12.5 H 12.5 V 19 H 19 Z M 11.5,19 V 12.5 H 5 V 19 Z",
  };

  const icon = (name, size) => {
    const s = size || 18;
    return m(
      "svg.icon",
      {
        width: s,
        height: s,
        viewBox: "0 0 24 24",
        fill: "none",
        stroke: "currentColor",
        "stroke-width": 2,
        "stroke-linecap": "round",
        "stroke-linejoin": "round",
        "aria-hidden": "true",
      },
      m("path", { d: ICONS[name] }),
    );
  };

  const helpButton = (text) =>
    m(
      "span.help",
      {
        title: "Help",
        onclick: () => window.alert(text),
      },
      "[?]",
    );

  const isDarkUITheme = (id) =>
    getComputedStyle($(":root")).colorScheme.toLowerCase() == "dark";

  let integer_input_engine_depth = "";
  let integer_input_engine_movetime = "";
  let integer_input_engine_nodes = "";
  let integer_input_engine_hash = "";
  let integer_input_engine_threads = "";
  let integer_input_engine_multipv = "";

  // let integer_input_white_start_time = default_start_time;
  // let integer_input_white_time_increment = default_time_increment;
  // let integer_input_white_byoyomi_periods = default_byoyomi_periods;
  // let integer_input_white_byoyomi_period_length = default_byoyomi_period_length;
  // let integer_input_white_timeout_margin = default_timeout_margin;
  // let integer_input_white_depth = default_depth;
  // let integer_input_white_movetime = default_movetime;
  // let integer_input_white_nodes = default_nodes;
  // let integer_input_black_start_time = default_start_time;
  // let integer_input_black_time_increment = default_time_increment;
  // let integer_input_black_byoyomi_periods = default_byoyomi_periods;
  // let integer_input_black_byoyomi_period_length = default_byoyomi_period_length;
  // let integer_input_black_timeout_margin = default_timeout_margin;
  // let integer_input_black_depth = default_depth;
  // let integer_input_black_movetime = default_movetime;
  // let integer_input_black_nodes = default_nodes;

  let integer_input_white_start_time = "";
  let integer_input_white_time_increment = "";
  let integer_input_white_byoyomi_periods = "";
  let integer_input_white_byoyomi_period_length = "";
  let integer_input_white_timeout_margin = "";
  let integer_input_white_depth = "";
  let integer_input_white_movetime = "";
  let integer_input_white_nodes = "";
  let integer_input_black_start_time = "";
  let integer_input_black_time_increment = "";
  let integer_input_black_byoyomi_periods = "";
  let integer_input_black_byoyomi_period_length = "";
  let integer_input_black_timeout_margin = "";
  let integer_input_black_depth = "";
  let integer_input_black_movetime = "";
  let integer_input_black_nodes = "";

  // Switch infinite analysis on or off from anywhere in the UI.
  // Turning it on releases the players and the time control (they
  // are exclusive with analysis) and starts the engine right away;
  // turning it off stops the engine.
  // Engine resources shown as sliders (lichess style). The hidden
  // number inputs #threads, #hash and #multipv carry the values that
  // the engine logic reads.
  const hashSteps = [4, 8, 16, 32, 64, 128, 256, 512, 1024];
  const maxThreads = Math.max(
    1,
    Math.min(32, navigator.hardwareConcurrency || 1),
  );
  let engine_threads = window.crossOriginIsolated
    ? Math.max(1, Math.min(4, Math.floor(maxThreads / 2)))
    : 1;
  let engine_hash_index = 2; // 16 MB
  let engine_multipv = 1;
  let engine_skill = 20;
  // Search limits; the last slider position means "no limit".
  const depthSteps = [1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 20, 25, 30, 40];
  const movetimeSteps = [
    100, 200, 500, 1000, 2000, 5000, 10000, 20000, 30000, 60000, 120000, 300000,
  ];
  const nodesSteps = [
    10000, 50000, 100000, 500000, 1000000, 5000000, 10000000, 50000000,
    100000000,
  ];
  let engine_depth_index = depthSteps.length;
  let engine_movetime_index = movetimeSteps.length;
  let engine_nodes_index = nodesSteps.length;
  // Time control values shown as sliders; the hidden number inputs
  // keep the millisecond values the timer logic reads.
  const startTimeSteps = [
    15000, 30000, 60000, 120000, 180000, 300000, 600000, 900000, 1200000,
    1800000, 2700000, 3600000, 5400000, 7200000,
  ];
  const incrementSteps = [
    0, 1000, 2000, 3000, 5000, 10000, 15000, 20000, 30000, 60000,
  ];
  const byoyomiSteps = [5000, 10000, 15000, 20000, 30000, 45000, 60000];
  const marginSteps = [0, 100, 200, 500, 1000, 2000, 5000];
  const tc_white = {
    start: 5,
    gain: 3,
    byoyomi: 4,
    periods: 3,
    margin: 0,
  };
  const tc_black = {
    start: 5,
    gain: 3,
    byoyomi: 4,
    periods: 3,
    margin: 0,
  };
  const formatClock = (ms) => {
    if (ms >= 60000) {
      const minutes = ms / 60000;
      return `${Number.isInteger(minutes) ? minutes : minutes.toFixed(1)} min`;
    }
    return `${ms / 1000} s`;
  };
  const timeSliders = (side, mode, tc) =>
    m(
      `div.${use_integer_inputs ? "integer-inputs" : "sliders"}.timecontrol`,
      { hidden: mode == "infinite" },
      [
        use_integer_inputs
          ? integerInput(
              mode == "time per move"
                ? "Time per move (ms)"
                : "Start time (ms)",
              "1",
              "",
              default_start_time,
              (value) => {
                if (side == "white") {
                  integer_input_white_start_time = value;
                } else {
                  integer_input_black_start_time = value;
                }
              },
              "The time in milliseconds at the beginning of the game.",
              true,
            )
          : sliderRow(
              mode == "time per move" ? "Time per move" : "Start time",
              formatClock(startTimeSteps[tc.start]),
              0,
              startTimeSteps.length - 1,
              tc.start,
              (value) => {
                tc.start = value;
              },
              "The time at the beginning of the game.",
            ),
        m("div", { hidden: mode != "tournament" }, [
          use_integer_inputs
            ? integerInput(
                "Time Increment (ms)",
                "0",
                "",
                default_time_increment,
                (value) => {
                  if (side == "white") {
                    integer_input_white_time_increment = value;
                  } else {
                    integer_input_black_time_increment = value;
                  }
                },
                "Time in milliseconds added after every move.",
                true,
              )
            : sliderRow(
                "Increment",
                formatClock(incrementSteps[tc.gain]),
                0,
                incrementSteps.length - 1,
                tc.gain,
                (value) => {
                  tc.gain = value;
                },
                "Time added after every move.",
              ),
        ]),
        m("div", { hidden: mode != "byoyomi" }, [
          use_integer_inputs
            ? integerInput(
                "Byo-yomi period length (ms)",
                "0",
                "",
                default_byoyomi_period_length,
                (value) => {
                  if (side == "white") {
                    integer_input_white_byoyomi_period_length = value;
                  } else {
                    integer_input_black_byoyomi_period_length = value;
                  }
                },
                "Length in milliseconds of each byo-yomi period.",
                true,
              )
            : sliderRow(
                "Byo-yomi period",
                formatClock(byoyomiSteps[tc.byoyomi]),
                0,
                byoyomiSteps.length - 1,
                tc.byoyomi,
                (value) => {
                  tc.byoyomi = value;
                },
                "Length of each byo-yomi period.",
              ),
        ]),
        m("div", { hidden: mode != "byoyomi" }, [
          use_integer_inputs
            ? integerInput(
                "Byo-yomi period count",
                "1",
                "",
                default_byoyomi_periods,
                (value) => {
                  if (side == "white") {
                    integer_input_white_byoyomi_periods = value;
                  } else {
                    integer_input_black_byoyomi_periods = value;
                  }
                },
                "Number of byo-yomi periods.",
                true,
              )
            : sliderRow(
                "Periods",
                tc.periods,
                1,
                10,
                tc.periods,
                (value) => {
                  tc.periods = value;
                },
                "Number of byo-yomi periods.",
              ),
        ]),
        use_integer_inputs
          ? integerInput(
              "Timeout margin (ms)",
              "0",
              "",
              default_timeout_margin,
              (value) => {
                if (side == "white") {
                  integer_input_white_timeout_margin = value;
                } else {
                  integer_input_black_timeout_margin = value;
                }
              },
              "The time may be exceeded by this much milliseconds before this side loses on time.",
              true,
            )
          : sliderRow(
              "Timeout margin",
              formatClock(marginSteps[tc.margin]),
              0,
              marginSteps.length - 1,
              tc.margin,
              (value) => {
                tc.margin = value;
              },
              "The time may be exceeded by this much before this side loses on time.",
            ),
      ],
    );

  const allLimitsInfinite = () =>
    engine_depth_index >= depthSteps.length &&
    engine_movetime_index >= movetimeSteps.length &&
    engine_nodes_index >= nodesSteps.length;
  const limitValue = (steps, index) =>
    index >= steps.length ? "" : String(steps[index]);
  const limitLabel = (steps, index, format) =>
    index >= steps.length ? "∞" : format(steps[index]);
  const formatSeconds = (ms) =>
    ms >= 60000 ? `${ms / 60000} min` : `${ms / 1000} s`;
  const formatNodes = (n) =>
    n >= 1000000 ? `${n / 1000000}M` : `${n / 1000}k`;

  const sliderRow = (label, shown, min, max, value, onchange, help) =>
    m("div.sliderrow", { title: help }, [
      m("div.sliderhead", [
        m("span.label", label),
        m("span.val", String(shown)),
      ]),
      m("input[type=range]", {
        min: min,
        max: max,
        step: 1,
        value: value,
        disabled: stockfish_state != "READY",
        oninput: (e) => {
          onchange(parseInt(e.target.value));
        },
      }),
    ]);

  //min, max, value can be strings
  const integerInput = (
    label,
    min,
    max,
    value,
    onchangefn,
    help,
    usedefault = false,
  ) =>
    m("div.integerrow", { title: help }, [
      m("input[type=number]", {
        placeholder: label,
        min: isNaN(parseInt(min)) ? "-2147483648" : min,
        max: isNaN(parseInt(max)) ? "2147483647" : max,
        step: "1",
        //defaultValue: value,
        disabled: stockfish_state != "READY",
        onchange: (e) => {
          let number = parseInt(e.target.value);
          if (!usedefault && e.target.value) {
            onchangefn("");
          } else if (isNaN(number)) {
            if (isNaN(parseInt(e.target.defaultValue))) {
              onchangefn("");
            } else {
              onchangefn(parseInt(e.target.defaultValue));
            }
          }
          if (number < parseInt(e.target.min)) {
            onchangefn(parseInt(e.target.min));
          } else if (number > parseInt(e.target.max)) {
            onchangefn(parseInt(e.target.max));
          } else {
            onchangefn(parseInt(number));
          }
        },
      }),
    ]);

  // The player settings (who plays which side) only take effect in
  // play mode. In analysis mode the engine never plays a side, but the
  // settings themselves are kept. Engine matches manage the players
  // on their own and are left alone.
  const isClockModeValue = (mode) =>
    mode == "tournament" ||
    mode == "time per move" ||
    mode == "hourglass" ||
    mode == "byoyomi";
  const isEngineSide = (game) => game.player == "fsf" || game.player == "ext";
  const playerName = (game, fallback) => {
    if (app_mode != "play") {
      return fallback;
    }
    if (game.player == "fsf") {
      return "Fairy-Stockfish";
    }
    if (game.player == "ext") {
      return "External engine";
    }
    if (game.player == "random") {
      return "Random mover";
    }
    return "You";
  };
  const playerIcon = (game) =>
    app_mode == "play" && isEngineSide(game)
      ? "cpu"
      : app_mode == "play" && game.player == "random"
        ? "dice"
        : "user";

  // The players only take effect while a game runs (play mode, until
  // the game is over). Engine matches manage the players on their own
  // and are left alone.
  const applyPlayerSettings = () => {
    if (engine_match_mode || during_engine_match) {
      return;
    }
    const active = gameRunning();
    play_white = active && isEngineSide(game_white);
    play_black = active && isEngineSide(game_black);
    random_mover_white = active && game_white.player == "random";
    random_mover_black = active && game_black.player == "random";
    [
      ["playwhite", play_white],
      ["playblack", play_black],
      ["randommoverwhite", random_mover_white],
      ["randommoverblack", random_mover_black],
    ].forEach(([id, value]) => {
      const element = document.getElementById(id);
      if (element) {
        element.checked = value;
      }
    });
  };

  const gameRunning = () => app_mode == "play" && !game_over;

  // Ends the running game: stops the clock and all engines and records
  // the outcome. The moves stay on the board. Games of an engine match
  // are handled by the match itself; the match as a whole ends through
  // the stop button.
  const finishGame = (result, reason) => {
    if (!gameRunning() || during_engine_match) {
      return;
    }
    if (during_play) {
      gameAbort();
    }
    force_stop();
    game_over = true;
    game_outcome = { result: result, reason: reason };
    document.getElementById("isgamestarted").checked = game_started = false;
    m.redraw();
  };

  const abortGame = () => {
    if (during_engine_match) {
      document.getElementById("stop").click();
    } else {
      finishGame("*", "aborted");
    }
    document.getElementById("isgamestarted").checked = game_started = false;
  };

  const outcomeText = (outcome) => {
    if (outcome.reason == "aborted") {
      return "Game aborted";
    }
    if (outcome.reason == "engine match finished") {
      return "Engine match finished";
    }
    const winner = {
      "1-0": "White wins",
      "0-1": "Black wins",
      "1/2-1/2": "Draw",
    }[outcome.result];
    if (!winner) {
      return "Game over";
    }
    const suffix = outcome.reason == "time forfeit" ? " on time" : "";
    return `${outcome.result} · ${winner}${suffix}`;
  };

  const sideLimitArgs = (side) => {
    const limit = side == "white" ? engine_limit_white : engine_limit_black;
    if (!limit) {
      return "";
    }
    return ` ${limit.type} ${limit.value}`;
  };

  const startGame = () => {
    newgame_open = false;
    setAnalysisMode(false);
    // A previous game that is still running ends first.
    abortGame();
    game_over = false;
    game_outcome = null;
    // Either back to the initial position of the current game, or
    // re-set the current position, which also clears the clock state
    // of a previous game (e.g. a time forfeit).
    const setup = document.getElementById(game_continue ? "setpos" : "restart");
    if (setup && !setup.disabled) {
      setup.click();
    }
    [
      ["white", game_white],
      ["black", game_black],
    ].forEach(([side, game]) => {
      const clock = isClockModeValue(game.mode);
      const modedropdown = document.getElementById(`dropdown-${side}timemode`);
      modedropdown.value = clock ? game.mode : "infinite";
      modedropdown.dispatchEvent(new Event("change"));
      let limit = null;
      if (!clock && isEngineSide(game)) {
        limit =
          game.mode == "depth"
            ? {
                type: "depth",
                value: use_integer_inputs
                  ? side == "white"
                    ? integer_input_white_depth || default_depth
                    : integer_input_black_depth || default_depth
                  : depthSteps[game.depth],
              }
            : game.mode == "nodes"
              ? {
                  type: "nodes",
                  value: use_integer_inputs
                    ? side == "white"
                      ? integer_input_white_nodes || default_nodes
                      : integer_input_black_nodes || default_nodes
                    : nodesSteps[game.nodes],
                }
              : {
                  type: "movetime",
                  value: use_integer_inputs
                    ? side == "white"
                      ? integer_input_white_movetime || default_movetime
                      : integer_input_black_movetime || default_movetime
                    : movetimeSteps[game.movetime],
                };
      }
      if (side == "white") {
        engine_limit_white = limit;
      } else {
        engine_limit_black = limit;
      }
      // External engines read their limits from these inputs.
      const external = game.player == "ext";
      ["depth", "movetime", "nodes"].forEach((type) => {
        const input = document.getElementById(`${side}${type}`);
        if (input) {
          input.value =
            external && limit && limit.type == type ? String(limit.value) : "";
        }
      });
    });
    advanced_time_control =
      isClockModeValue(game_white.mode) || isClockModeValue(game_black.mode);
    const advtimebox = document.getElementById("advtimectrl");
    if (advtimebox) {
      advtimebox.checked = advanced_time_control;
    }
    const bothengines = isEngineSide(game_white) && isEngineSide(game_black);
    engine_match_mode = bothengines && game_games > 1;
    const matchbox = document.getElementById("isenginematchmode");
    if (matchbox) {
      matchbox.checked = engine_match_mode;
    }
    app_mode = "play";
    applyPlayerSettings();
    m.redraw();
    window.setTimeout(() => {
      if (!gameRunning()) {
        return;
      }
      if (engine_match_mode) {
        // Start the engine match directly: the per-side limits chosen
        // in the dialog replace the old global limit validation.
        document.getElementById("enginematchgamecount").value =
          String(game_games);
        engine_match_game_list = [];
        play_white = true;
        play_black = true;
        during_engine_match = true;
        engine_match_played_game_count = 0;
        engine_match_total_game_count = game_games;
        engine_match_white_wins = 0;
        engine_match_black_wins = 0;
        engine_match_draws = 0;
        document.getElementById("enginematchinfo").innerText =
          `Games played: 0 | Total games to play: ${engine_match_total_game_count}`;
        if (advanced_time_control) {
          document.getElementById("gamestart").click();
        } else {
          document.getElementById("set").click();
        }
        m.redraw();
        return;
      }
      // A game continued from a finished position is over at once.
      if ($("#label-stm").innerText == "undefined") {
        finishGame($("#gameresult").value, "normal");
        return;
      }
      if (advanced_time_control) {
        goWithTimeControl();
        return;
      }
      const stm = $("#label-stm").innerText;
      const mover = stm == "black" ? game_black : game_white;
      if (isEngineSide(mover)) {
        startEngineNow();
      } else if (mover.player == "random") {
        document.getElementById("randommovergo").click();
      }
    }, 250);
    document.getElementById("isgamestarted").checked = game_started = true;
  };

  const endGame = () => {
    abortGame();
    game_over = false;
    game_outcome = null;
    engine_match_mode = false;
    const matchbox = document.getElementById("isenginematchmode");
    if (matchbox) {
      matchbox.checked = false;
    }
    advanced_time_control = false;
    const advtimebox = document.getElementById("advtimectrl");
    if (advtimebox) {
      advtimebox.checked = false;
    }
    engine_limit_white = null;
    engine_limit_black = null;
    app_mode = "analysis";
    applyPlayerSettings();
    m.redraw();
  };

  const enterSetup = () => {
    if (app_mode != "analysis") {
      return;
    }
    setAnalysisMode(false);
    app_mode = "setup";
    window.setTimeout(() => {
      const editor = document.getElementById("isboardsetup");
      if (editor && !editor.checked && !editor.disabled) {
        editor.click();
      }
      m.redraw();
    }, 60);
  };

  const leaveSetup = () => {
    const editor = document.getElementById("isboardsetup");
    if (editor && editor.checked) {
      editor.click();
    }
    app_mode = "analysis";
    m.redraw();
  };

  // Board editor piece palette: mirrors the options of the (hidden)
  // #dropdown-setpiece select, which main.js fills per variant.
  const pieceThemeClasses = () => {
    const container = document.getElementById("chessground-container-div");
    if (!container) {
      return "";
    }
    return [...container.classList]
      .filter(
        (c) => !/^board\d+x\d+$/.test(c) && c != "pockets" && c != "inner",
      )
      .join(" ");
  };
  const pieceChoices = () => {
    const dropdown = document.getElementById("dropdown-setpiece");
    if (!dropdown) {
      return [];
    }
    const choices = [];
    for (let i = 0; i < dropdown.length; i++) {
      const value = dropdown[i].value;
      const selected = dropdown.selectedIndex == i;
      if (value == "<move>") {
        choices.push({
          value,
          selected,
          icon: "move",
          title: "Move pieces",
        });
      } else if (value == "<delete>") {
        choices.push({
          value,
          selected,
          icon: "trash",
          title: "Delete pieces",
        });
      } else if (value == "*") {
        choices.push({
          value,
          selected,
          icon: "wall",
          title: "Wall square",
        });
      } else {
        const promoted = value.charAt(0) == "+";
        const letter = promoted ? value.charAt(1) : value.charAt(0);
        if (!letter) {
          continue;
        }
        const white = letter == letter.toUpperCase();
        choices.push({
          value,
          selected,
          title: `${promoted ? "Promoted " : ""}${white ? "white" : "black"} ${letter} (${white ? "First" : "Second"} mover)`,
          pieceClass: `${promoted ? "p" : ""}${letter.toLowerCase()}-piece ${white ? "white" : "black"}`,
        });
      }
    }
    return choices;
  };

  const analysisBlocked = () =>
    app_mode != "analysis" ||
    board_setup_mode ||
    engine_match_mode ||
    during_play ||
    during_engine_match;

  // Start the engine with the current settings (the former "Go").
  const startEngineNow = () => {
    if (stockfish_state != "READY") {
      return;
    }
    if (!analysis_mode && $("#advtimectrl").checked == true) {
      $("#advtimectrl").click();
    }
    if (board_setup_mode) {
      return;
    }
    document.getElementById("setpos").click();
    window.setTimeout(() => {
      go(false, false);
    }, 10);
  };

  const setAnalysisMode = (on) => {
    if (on == analysis_mode) {
      return;
    }
    analysis_mode = on;
    const analysischeckbox = document.getElementById("analysis");
    if (analysischeckbox) {
      analysischeckbox.checked = on;
      analysischeckbox.dispatchEvent(new Event("change"));
    }
    if (on) {
      window.setTimeout(() => {
        if (analysis_mode) {
          startEngineNow();
        }
      }, 50);
    } else {
      force_stop();
    }
    m.redraw();
  };

  const toggleDarkMode = () => {
    const dropdown = document.getElementById("dropdown-uitheme");
    if (!dropdown) {
      return;
    }
    const current = dropdown.value;
    const target = isDarkUITheme(current) ? "light" : "dark";
    let found = false;
    for (let i = 0; i < dropdown.length; i++) {
      if (dropdown[i].value == target) {
        found = true;
        break;
      }
    }
    if (found) {
      changeUI(target, true, true);
    }
  };

  const tabButton = (id, label, iconname) =>
    m(
      "button.tab",
      {
        type: "button",
        class: active_tab == id ? "on" : "",
        onclick: () => {
          active_tab = id;
        },
      },
      [icon(iconname, 16), label],
    );

  const view = () => {
    const is_ready = stockfish_state == "READY";
    applyPlayerSettings();
    const engine_status_class =
      stockfish_state == "READY"
        ? "ready"
        : stockfish_state == "FAILED"
          ? "failed"
          : "";

    // ---------------- top bar ----------------
    const topbar = m("header.topbar", [
      m("a.brand", { href: "./", target: "_self" }, [
        m("img.mark", {
          src: "./assets/images/app/logo.png",
          alt: "",
          width: 30,
          height: 30,
        }),
        m("span.text", "fairyground"),
      ]),
      m("div.variantbar#posvariantdiv", [
        m(
          "button.pickbtn.variantpick",
          {
            type: "button",
            disabled: !is_ready || review_mode || board_setup_mode,
            title: "Choose the chess variant",
            onclick: () => {
              variant_picker_open = true;
              variant_search = "";
              window.setTimeout(() => {
                const field = document.getElementById("variantsearch");
                if (field) {
                  field.focus();
                }
              }, 30);
            },
          },
          [
            icon("grid", 18),
            m("span.picklabel", [
              m("span.name", variantDisplayName(currentVariantId())),
              m(
                "span.type",
                variantTypeLabel(
                  currentVariantId() == ""
                    ? "please wait..."
                    : getVariantType(currentVariantId()),
                ),
              ),
            ]),
            m(
              "span.enginestatus",
              {
                class: engine_status_class,
                title:
                  stockfish_state == "READY"
                    ? "Fairy-Stockfish (WebAssembly) is loaded and ready."
                    : stockfish_state == "FAILED"
                      ? "Fairy-Stockfish (WebAssembly) failed to load."
                      : "Loading Fairy-Stockfish (WebAssembly)...",
              },
              [
                m("span.dot"),
                m("span.visually-hidden", [
                  `Fairy-Stockfish ${stockfish_state} `,
                  m(RequestProgress, {
                    url: "./lib/stockfish.wasm",
                    onFinishDownload,
                  }),
                ]),
              ],
            ),
            icon("chev", 16),
          ],
        ),
        m("div.internals", [
          m("div.varsel", [
            m(
              "select#dropdown-varianttype",
              {
                disabled: !is_ready || review_mode || board_setup_mode,
                title:
                  "The available types or categories of variants are shown in this list. Select one to see available variants in next dropdown.",
                onchange: (e) => {
                  changing_variant_type = true;
                  $("#dropdown-variant").dispatchEvent(new Event("change"));
                },
              },
              [
                m("option", { value: "" }, "(all)"),
                m("option", { value: "<|NC|>" }, "(not classified)"),
              ],
            ),
            m(
              "select#dropdown-variant",
              {
                disabled: !is_ready || review_mode || board_setup_mode,
                title:
                  "The available variants of the selected type are shown in this list. Select one to start a game of that variant.",
                onchange: (e) => {
                  if (changing_variant_type) {
                    updateVariantDropdown();
                    changing_variant_type = false;
                  }
                  setVariant();
                },
              },
              [m("option", { value: "" }, "(default)")],
            ),
          ]),
          m("div.varsel", [
            m(
              "select#dropdown-posvarianttype",
              {
                disabled: !is_ready || review_mode,
                title:
                  "The available types or categories of custom positions of this variant are shown in this list. Select one to see available positions in next dropdown.",
              },
              [m("option", { value: "(default)" }, "(default)")],
            ),
            m(
              "select#dropdown-posvariantname",
              {
                disabled: !is_ready || review_mode,
                title:
                  "The available custom positions of the selected type are shown in this list. Select one to set the position.",
              },
              [],
            ),
          ]),
        ]),
      ]),
      m("nav.topactions", [
        m(
          "button.primary.newgame",
          {
            type: "button",
            hidden: app_mode == "setup",
            disabled: !is_ready || review_mode || during_engine_match,
            title: "New game: players, strength and time control",
            onclick: () => {
              newgame_open = true;
            },
          },
          [icon("plus", 16), m("span", "New game")],
        ),
        m(
          "button.ghost.text",
          {
            type: "button",
            hidden: app_mode != "analysis",
            disabled: !is_ready || review_mode,
            title: "Set up a position: board editor, FEN and moves",
            onclick: () => {
              enterSetup();
            },
          },
          [icon("edit", 16), "Setup"],
        ),
        m(
          "span.pill.gameoutcome#gameoutcome",
          { hidden: app_mode != "play" || !game_over },
          game_outcome ? outcomeText(game_outcome) : "",
        ),
        m(
          game_over ? "button.soft" : "button.danger",
          {
            type: "button",
            hidden: app_mode != "play",
            title: game_over
              ? "Return to the analysis board (the moves are kept)."
              : "End the game and return to the analysis board (the moves are kept).",
            onclick: () => {
              endGame();
            },
          },
          game_over
            ? [icon("cpu", 16), m("span", "Analyze")]
            : [icon("stop", 16), m("span", "End game")],
        ),
        m("a.btn.ghost.text", { href: "./resources.html", target: "_self" }, [
          icon("book", 16),
          "Resources",
        ]),
        m(
          "a.btn.ghost.iconbtn",
          {
            href: "https://github.com/fairy-stockfish/fairyground",
            title: "GitHub",
          },
          icon("github"),
        ),
        m(
          "button.iconbtn.ghost",
          {
            type: "button",
            title: "Toggle dark mode",
            onclick: toggleDarkMode,
          },
          icon("moon"),
        ),
        m(
          "button.iconbtn.ghost",
          {
            type: "button",
            title: "Settings",
            onclick: () => {
              settings_open = true;
            },
          },
          icon("gear"),
        ),
      ]),
    ]);

    // ---------------- board column ----------------
    const boardcol = m("section.boardcol#boardcol", [
      m("div.playerbar.top", [
        m(
          "div.avatar",
          board_orientation == "white"
            ? icon(playerIcon(game_black), 16)
            : icon(playerIcon(game_white), 16),
        ),
        m("div", [
          board_orientation == "white"
            ? m(
                "p.name",
                playerName(
                  game_black,
                  playerColor(mover_color_scheme, "black"),
                ),
              )
            : m(
                "p.name",
                playerName(
                  game_white,
                  playerColor(mover_color_scheme, "white"),
                ),
              ),
          board_orientation == "white"
            ? m("p.sub", "Second mover")
            : m("p.sub", "First mover"),
        ]),
      ]),
      m(
        "div#timers",
        { hidden: !advanced_time_control || app_mode != "play" },
        [
          m("div#whitetimer", [
            m("p", "White Time"),
            m("p#whitetime", "--"),
            m("p#whitetimetype", "infinite"),
          ]),
          m("div#blacktimer", [
            m("p", "Black Time"),
            m("p#blacktime", "--"),
            m("p#blacktimetype", "infinite"),
          ]),
        ],
      ),
      m(
        "div#chessground-container-div.defaultboard.default.board8x8",
        {
          onwheel: (event) => {
            if (event instanceof WheelEvent) {
              if (!game_started && !board_setup_mode) {
                event.stopPropagation();
                event.preventDefault();
                if (event.ctrlKey) {
                  requestAnimationFrame(() => {
                    if (event.deltaY < 0) {
                      document.getElementById("initialposition").click();
                    } else {
                      document.getElementById("finalposition").click();
                    }
                  });
                } else {
                  requestAnimationFrame(() => {
                    if (event.deltaY < 0) {
                      document.getElementById("previousposition").click();
                    } else {
                      document.getElementById("nextposition").click();
                    }
                  });
                }
              }
            }
          },
        },
        [
          m("div.cg-wrap.pocket-top", [m("div#pocket-top")]),
          m("div#chessground-board"),
          m("div.cg-wrap.pocket-bottom", [m("div#pocket-bottom")]),
        ],
      ),
      m("div.playerbar.bottom", [
        m(
          "div.avatar",
          board_orientation == "white"
            ? icon(playerIcon(game_white), 16)
            : icon(playerIcon(game_black), 16),
        ),
        m("div", [
          board_orientation == "white"
            ? m(
                "p.name",
                playerName(
                  game_white,
                  playerColor(mover_color_scheme, "white"),
                ),
              )
            : m(
                "p.name",
                playerName(
                  game_black,
                  playerColor(mover_color_scheme, "black"),
                ),
              ),
          board_orientation == "white"
            ? m("p.sub", "First mover")
            : m("p.sub", "Second mover"),
        ]),
      ]),
      m(
        "div#timecontrolduringplay",
        { hidden: !advanced_time_control || !gameRunning() },
        [
          m(
            "button#addtimeforwhite.sm",
            {
              type: "button",
              title: "Add 10 seconds to the remaining time of first mover.",
              onclick: () => {
                white_remaining_time = +white_remaining_time + 10000;
              },
            },
            "+10 s white",
          ),
          m(
            "button#addtimeforblack.sm",
            {
              type: "button",
              title: "Add 10 seconds to the remaining time of second mover.",
              onclick: () => {
                black_remaining_time = +black_remaining_time + 10000;
              },
            },
            "+10 s black",
          ),
          m(
            "button#gameabort.sm.danger",
            {
              type: "button",
              title:
                "Stop the clock and end the game without a result (the moves are kept).",
              onclick: () => {
                if (confirm("Are you sure to abort the game?")) {
                  abortGame();
                }
              },
            },
            "Abort game",
          ),
        ],
      ),
      m("div.boardnav", [
        m("div#movecontrol", { hidden: during_play }, [
          m("div.navgroup", [
            m(
              "button#initialposition.iconbtn",
              {
                type: "button",
                disabled: !is_ready,
                title:
                  "Initial position\nClick to display the initial position of current game.",
              },
              icon("first"),
            ),
            m(
              "button#previousposition.iconbtn",
              {
                type: "button",
                disabled: !is_ready,
                title:
                  "Previous position\nClick to display previous position of the displayed position.",
              },
              icon("prev"),
            ),
            m(
              "button#nextposition.iconbtn",
              {
                type: "button",
                disabled: !is_ready,
                title:
                  "Next position\nClick to display next position of the displayed position.",
              },
              icon("next"),
            ),
            m(
              "button#finalposition.iconbtn",
              {
                type: "button",
                disabled: !is_ready,
                title:
                  "Final position\nClick to display the latest position of the displayed position.",
              },
              icon("last"),
            ),
            m(
              "button#currentposition.iconbtn",
              {
                type: "button",
                disabled: !is_ready,
                title:
                  "Current position\nClick to display the latest position of current game.",
              },
              icon("current"),
            ),
          ]),
          m("div.internals", [
            m("input[type=number]#gotomovenum", {
              placeholder: "#",
              disabled: !is_ready,
              title:
                "The half number to the half move to display (A turn that both player make a move is 1 full move, 2 half moves).",
              min: 0,
            }),
            m(
              "button#specifiedposition.iconbtn",
              {
                type: "button",
                disabled: !is_ready,
                title:
                  "Go to move\nClick to display the position that the half move specified in the input box is moved.",
              },
              icon("goto"),
            ),
          ]),
        ]),
        m("div.navgroup", [
          m(
            "button#undo.iconbtn",
            {
              type: "button",
              disabled: !is_ready || review_mode || board_setup_mode,
              title: "Undo\nClick to undo last move.",
            },
            icon("undo"),
          ),
          m(
            "button#passmove",
            {
              type: "button",
              disabled: !is_ready,
              title: "Click to pass your turn.",
            },
            [icon("skip", 16), m("span.txt", "Pass")],
          ),
          m(
            "button#placewall.iconbtn",
            {
              type: "button",
              disabled: !is_ready,
              title: "Place a wall\nClick to place a wall only.",
            },
            icon("wall"),
          ),
          m(
            "button#button-flip.iconbtn",
            {
              type: "button",
              title: "Flip board",
              onclick: () => {
                setTimeout(() => {
                  if (board_setup_mode) {
                    triggerBoardSetupPieceIdentifier(false);
                  }
                }, 50);
              },
            },
            icon("flip"),
          ),
        ]),
      ]),
      m("div.boardnotes", [
        m(
          "p.hint",
          { hidden: !(app_mode == "play" && engine_match_mode) },
          `Engine match: ${engine_match_played_game_count} / ${engine_match_total_game_count} games played · ${playerColor(mover_color_scheme, "white")} ${engine_match_white_wins} · ${playerColor(mover_color_scheme, "black")} ${engine_match_black_wins} · Draws ${engine_match_draws}`,
        ),
        m(
          "p#reviewmodenote1",
          { hidden: !review_mode },
          "Review mode enabled.",
        ),
        m(
          "p#reviewmodenote2",
          { hidden: !review_mode },
          "You can go to previous moves played to analyze your game, but you cannot make changes to the game. To exit review mode, click <reset>, <current position> or <start here>.",
        ),
      ]),
    ]);

    const consoleTab = m(
      "div.enginedebug#tab-console",
      { hidden: !engine_debug },
      [
        m("div#output2", { onupdate: scrollOutput }, [
          m("pre#fsfoutput", engineoutput),
          m(
            "pre#whiteengineoutput",
            { hidden: true },
            "This is the console where you can see the message communication.\nLines start with ▶▶ are the messages sent to the engine.\nLines start with ◀◀ are the messages received from the engine.\n\n",
          ),
          m(
            "pre#blackengineoutput",
            { hidden: true },
            "This is the console where you can see the message communication.\nLines start with ▶▶ are the messages sent to the engine.\nLines start with ◀◀ are the messages received from the engine.\n\n",
          ),
          m(
            "pre#analysisengineoutput",
            { hidden: true },
            "This is the console where you can see the message communication.\nLines start with ▶▶ are the messages sent to the engine.\nLines start with ◀◀ are the messages received from the engine.\n\n",
          ),
        ]),
        m("div#enginecmddiv", [
          m(
            "select#targetengine",
            {
              title:
                "Select the console of the engine. This is the target engine of the command sent, and the engine that sends the message above.",
              onchange: () => {
                let index = $("#targetengine").selectedIndex;
                if (index == 0) {
                  document.getElementById("fsfoutput").hidden = false;
                  document.getElementById("whiteengineoutput").hidden = true;
                  document.getElementById("blackengineoutput").hidden = true;
                  document.getElementById("analysisengineoutput").hidden = true;
                } else if (index == 1) {
                  document.getElementById("fsfoutput").hidden = true;
                  document.getElementById("whiteengineoutput").hidden = false;
                  document.getElementById("blackengineoutput").hidden = true;
                  document.getElementById("analysisengineoutput").hidden = true;
                } else if (index == 2) {
                  document.getElementById("fsfoutput").hidden = true;
                  document.getElementById("whiteengineoutput").hidden = true;
                  document.getElementById("blackengineoutput").hidden = false;
                  document.getElementById("analysisengineoutput").hidden = true;
                } else if (index == 3) {
                  document.getElementById("fsfoutput").hidden = true;
                  document.getElementById("whiteengineoutput").hidden = true;
                  document.getElementById("blackengineoutput").hidden = true;
                  document.getElementById("analysisengineoutput").hidden =
                    false;
                }
              },
            },
            [
              m("option", { value: "DEFAULT" }, "In browser Fairy-Stockfish"),
              m("option", { value: "WHITE" }, "1st binary engine"),
              m("option", { value: "BLACK" }, "2nd binary engine"),
              m("option", { value: "ANALYSIS" }, "Analysis binary engine"),
            ],
          ),
          m(
            "label#label-clearlogonstartthinking.toggle",
            {
              title:
                "When checked, automatically clear the console of the engine that starts thinking.",
            },
            [
              m("input[type=checkbox]#clearlogonstartthinking", {
                disabled: !is_ready,
                checked: clear_log,
                onclick: () => {
                  clear_log = !clear_log;
                },
              }),
              m("span", "Clear log when thinking starts"),
            ],
          ),
          m(
            "button.sm",
            {
              type: "button",
              title: "Click to clear all consoles.",
              onclick: () => {
                first_engine_output = "";
                second_engine_output = "";
                analysis_engine_output = "";
                document.getElementById("whiteengineoutput").textContent = "";
                document.getElementById("blackengineoutput").textContent = "";
                document.getElementById("analysisengineoutput").textContent =
                  "";
                engineoutput = "";
                scrollOutput();
              },
            },
            [icon("trash", 14), "Clear logs"],
          ),
          m("input[type=text]#enginecmd", {
            placeholder: "Send command to engine...",
            title: "The command to send to the engine.",
            maxlength: 9999,
            disabled: !is_ready || during_play,
            onkeyup: (e) => {
              if (e.keyCode != 13) {
                e.redraw = false;
                return;
              }
              if (during_play) {
                return;
              }
              sendCommandToEngine();
            },
          }),
          m(
            "button#sendenginecmd.primary",
            {
              type: "button",
              disabled: during_play,
              title: "Click to send the command.",
              onclick: () => {
                if (during_play) {
                  return;
                }
                sendCommandToEngine();
              },
            },
            [icon("send", 16), "Send"],
          ),
        ]),
      ],
    );

    // ---------------- moves tab ----------------
    const movesTab = m(
      "div.tabpanel#tab-moves",
      {
        class: active_tab == "moves" ? "on" : "",
        hidden: app_mode == "setup",
      },
      [
        m("div.analysisbar", { hidden: app_mode != "analysis" }, [
          m(
            "button.analysistoggle",
            {
              type: "button",
              class: analysis_mode ? "on" : "",
              disabled: !is_ready || analysisBlocked(),
              "aria-pressed": analysis_mode ? "true" : "false",
              title:
                app_mode != "analysis"
                  ? "Switch to Analysis in the top bar to analyse."
                  : analysisBlocked()
                    ? "Analysis is not available during a timed game, an engine match or while editing the board."
                    : "Toggle engine analysis of the current position.",
              onclick: () => {
                setAnalysisMode(!analysis_mode);
              },
            },
            [
              m("span.sw"),
              m("span.lbl", [
                icon("cpu", 16),
                analysis_mode ? "Engine analysis on" : "Engine analysis",
              ]),
            ],
          ),
          m("div", { hidden: !analysis_mode }, [
            m(
              "button.sm.iconbtn",
              {
                type: "button",
                disabled: !is_ready || analysisBlocked(),
                hidden: !analysis_mode,
                title: "Click to restart engine analysis.",
                onclick: () => {
                  startEngineNow();
                },
              },
              [icon("play")],
            ),
            m(
              "button.sm.iconbtn",
              {
                type: "button",
                disabled: !is_ready || analysisBlocked(),
                hidden: !analysis_mode,
                title: "Click to stop engine analysis.",
                onclick: () => {
                  force_stop();
                },
              },
              [icon("stop")],
            ),
            m(
              "button#analyze-nextmove.sm.iconbtn",
              {
                type: "button",
                disabled: !is_ready || analysisBlocked(),
                hidden: !analysis_mode,
                title: "Click to go to next played move and continue analysis.",
              },
              [icon("next")],
            ),
            m(
              "button#analyze-recommended.sm.iconbtn",
              {
                type: "button",
                disabled: !is_ready || analysisBlocked(),
                hidden: !analysis_mode,
                title:
                  "Click to make engine's recommended move and continue analysis.",
              },
              [icon("star")],
            ),
            m(
              "button#seteval.sm",
              {
                type: "button",
                disabled: !is_ready || analysisBlocked(),
                hidden: !analysis_mode,
                title: "Click to set current evaluation score on this move.",
              },
              [icon("diamond"), "Set evaluation"],
            ),
          ]),
        ]),
        m("div#evaluation", { hidden: !analysis_mode }, [
          m("div#evalbar", [m("p#cp", "0.00"), m("div#evalbarprogress")]),
          m("p#evalcomment", ""),
          m("p#evalinfo", ""),
          m("p#pvinfo", ""),
        ]),
        m("div.row", [
          m(
            "button.sm",
            {
              type: "button",
              disabled: !is_ready || review_mode,
              title:
                "Game library\nClick to open PGN file and EPD file parser.",
              onclick: () => {
                if (!is_ready || review_mode) {
                  return;
                }
                if (ffish) {
                  fgs.ShowPGNOrEPDFileUI(game_list, window.ffishlib);
                }
              },
            },
            [icon("book", 14), "PGN/EPD library"],
          ),
          m("span", { style: "flex: 1;" }),
          m(
            "label.toggle",
            {
              title:
                "Show the engine console (raw UCI communication) below the move list.",
            },
            [
              m("input[type=checkbox]#enginedebug", {
                checked: engine_debug,
                onclick: (e) => {
                  engine_debug = e.target.checked;
                },
              }),
              m("span", "Engine debug"),
            ],
          ),
        ]),
        m("p#positioninfo", ""),
        m("p#checkcounts"),
        m("div#pgn-container", [
          m("p#label-pgn", {
            oncontextmenu: (e) => {
              e.preventDefault();
            },
          }),
        ]),
        m("div#evalhistory", { hidden: !show_evaluation_history_graph }, [
          m(
            "span.label",
            {
              onclick: () => {
                window.alert(
                  "(Assuming you use left button as primary mouse button)\nUsage:\nDrag on the graph to pan.\nRight click on the graph to reset view.\nLeft click the points to show move information.\nRight click the points to display that position.",
                );
              },
            },
            "Evaluation History",
          ),
          m("div#evalhistorycontainer"),
        ]),
        m(
          "div#pgn-operation-container.pgntools",
          { hidden: !advanced_pgn_mode || game_started },
          [
            m("div.row", [
              m("span.label", "PGN tools"),
              m(
                "button.sm.ghost.toolstoggle",
                {
                  type: "button",
                  title: "Show or hide the PGN tools",
                  onclick: () => {
                    pgn_tools_open = !pgn_tools_open;
                  },
                },
                pgn_tools_open ? "Hide" : "Show",
              ),
            ]),
            m(
              "div#pgn-operations",
              { class: pgn_tools_open ? "" : "collapsed" },
              [
                m(
                  "button#movetree-clear",
                  {
                    type: "button",
                    title:
                      "Clear Moves\nClick to clear the variation tree. Your position will be set to the initial position.",
                  },
                  icon("trash", 16),
                ),
                m(
                  "button#movetree-clearcomments",
                  {
                    type: "button",
                    title:
                      "Clear Comments\nClick to clear all comments (Text before, text after, symbols).",
                  },
                  icon("commentclear", 16),
                ),
                m(
                  "button#movetree-hideshow",
                  {
                    type: "button",
                    title:
                      "Show or Hide Move\nClick to hide/show subsequent moves of current move.",
                  },
                  icon("eyeoff", 16),
                ),
                m(
                  "button#movetree-removevariations",
                  {
                    type: "button",
                    title:
                      "Remove Variations\nClick to remove variation moves of current move.",
                  },
                  icon("branchx", 16),
                ),
                m("span.toolgap"),
                m(
                  "button#movetree-settomainbranch",
                  {
                    type: "button",
                    title:
                      "Promote Move\nClick to set the current move as the main branch of previous move.",
                  },
                  icon("arrowup", 16),
                ),
                m(
                  "button#movetree-setasmainline",
                  {
                    type: "button",
                    title:
                      "Promote Branch\nClick to set all the antecedent moves of current move as the main line moves.",
                  },
                  icon("chevronsup", 16),
                ),
                m(
                  "button#movetree-cutbranch",
                  {
                    type: "button",
                    title:
                      "Cut Branch\nClick to remove all the moves on the variation branch of current move.",
                  },
                  icon("branchcut", 16),
                ),
                m(
                  "button#movetree-cropbranch",
                  {
                    type: "button",
                    title:
                      "Crop Branch\nClick to remove all the moves that are not on the branch of current move.",
                  },
                  icon("lineonly", 16),
                ),
                m(
                  "button#movetree-cut",
                  {
                    type: "button",
                    title:
                      "Cut Move\nClick to remove current move and all of its subsequent moves.",
                  },
                  icon("x", 16),
                ),
                m(
                  "button#movetree-crop",
                  {
                    type: "button",
                    title:
                      "Crop Move\nClick to remove all antecedent moves of current move and set the initial position to the position before current move.",
                  },
                  icon("crop", 16),
                ),
                m("span.toolgap"),
                m(
                  "button#movetree-uncomment",
                  {
                    type: "button",
                    title:
                      "Uncomment Move\nClick to remove all texts and symbols of current move.",
                  },
                  icon("commentx", 16),
                ),
                m(
                  "button#movetree-textbefore",
                  {
                    type: "button",
                    title:
                      "Set Text Before\nClick to set text before current move.",
                  },
                  icon("commentbefore", 16),
                ),
                m(
                  "button#movetree-textafter",
                  {
                    type: "button",
                    title:
                      "Set Text After\nClick to set text after current move.",
                  },
                  icon("commentafter", 16),
                ),
                m(
                  "button#movetree-symbol",
                  {
                    type: "button",
                    title:
                      "Set Symbols\nClick to set symbols (e.g. !!,??,!,?) for current move.",
                  },
                  m("span.txticon", "!?"),
                ),
                m(
                  "button#movetree-markers",
                  {
                    type: "button",
                    title:
                      "Set Markers\nClick to set the markers (i.e. arrows & strokes) drawn on the main board to current move.",
                  },
                  icon("arrowupright", 16),
                ),
                m(
                  "button#movetree-termination",
                  {
                    type: "button",
                    title:
                      "Set Termination\nClick to set result and termination on current move.",
                  },
                  icon("flag", 16),
                ),
                m(
                  "button#movetree-boardpreview",
                  {
                    type: "button",
                    title:
                      "Toggle Board Preview\nClick to show or hide the board of current move in the list.",
                  },
                  icon("border", 16),
                ),
                m(
                  "button#movetree-headers",
                  {
                    type: "button",
                    title:
                      "Set Game Headers\nClick to set the PGN headers of this game, e.g. Event, Site, Round.",
                  },
                  icon("doc", 16),
                ),
                m("span.toolgap"),
                m(
                  "button#movetree-undo",
                  {
                    type: "button",
                    title:
                      "Undo\nClick to undo last change made to the variation tree. Making new moves on the main board will clear change history.",
                  },
                  icon("undo", 16),
                ),
                m(
                  "button#movetree-redo",
                  {
                    type: "button",
                    title:
                      "Redo\nClick to redo last change made to the variation tree. Making new moves on the main board will clear change history.",
                  },
                  icon("redo", 16),
                ),
                m("span.toolgap"),
                m(
                  "button#movetree-save",
                  {
                    type: "button",
                    title:
                      "Save\nClick to save whole variation tree to a PGN file.",
                  },
                  icon("save", 16),
                ),
                m(
                  "button#movetree-imagesave",
                  {
                    type: "button",
                    title:
                      "Save Board as Image...\nClick to open board image generator.",
                  },
                  icon("image", 16),
                ),
                m(
                  "button#movetree-resize",
                  {
                    type: "button",
                    title:
                      "Enlarge PGN Viewer\nClick to make PGN viewer larger.",
                  },
                  [
                    m("span.when-small", icon("expand", 16)),
                    m("span.when-large", icon("collapse", 16)),
                  ],
                ),
              ],
            ),
          ],
        ),
        m("div.fenrow", [
          m("span.label", "FEN"),
          m("p#currentboardfen"),
          m(
            "button.sm.iconbtn",
            {
              type: "button",
              title: "Copy the current FEN to the clipboard",
              onclick: () => {
                const fen = document
                  .getElementById("currentboardfen")
                  .textContent.trim();
                copyText(fen);
                fen_copied = true;
                window.setTimeout(() => {
                  fen_copied = false;
                  m.redraw();
                }, 1500);
              },
            },
            icon(fen_copied ? "check" : "copy", 14),
          ),
          m(
            "button.sm.iconbtn",
            {
              type: "button",
              title:
                "Copy a link to this board: variant and position, ready to share",
              onclick: shareBoard,
            },
            icon(share_copied ? "check" : "link", 14),
          ),
        ]),
        consoleTab,
      ],
    );

    // ---------------- engine tab ----------------
    const engineTab = m(
      "div.tabpanel#tab-engine",
      {
        class: active_tab == "engine" ? "on" : "",
        hidden: app_mode == "setup",
      },
      [
        m("div.subsection", [
          m("div.secthead", [
            m("span.sect", "Fairy-Stockfish · analysis"),
            m("input[type=checkbox]#analysis", {
              hidden: true,
              checked: analysis_mode,
            }),
          ]),

          m("div.sliders", { hidden: use_integer_inputs }, [
            sliderRow(
              "Lines",
              engine_multipv,
              1,
              8,
              engine_multipv,
              (value) => {
                engine_multipv = value;
              },
              "Number of principal variations (engine lines) shown.",
            ),
            sliderRow(
              "Threads",
              engine_threads,
              1,
              maxThreads,
              engine_threads,
              (value) => {
                engine_threads = value;
              },
              "Parallel search threads of in browser Fairy-Stockfish.",
            ),
            sliderRow(
              "Memory",
              hashSteps[engine_hash_index] + " MB",
              0,
              hashSteps.length - 1,
              engine_hash_index,
              (value) => {
                engine_hash_index = value;
              },
              "Size of the engine's hash table.",
            ),
          ]),
          m("div.sliders", { hidden: use_integer_inputs }, [
            sliderRow(
              "Depth",
              limitLabel(depthSteps, engine_depth_index, (v) => String(v)),
              0,
              depthSteps.length,
              engine_depth_index,
              (value) => {
                engine_depth_index = value;
              },
              "Stop the analysis at this depth. Rightmost: no limit.",
            ),
            sliderRow(
              "Time",
              limitLabel(movetimeSteps, engine_movetime_index, formatSeconds),
              0,
              movetimeSteps.length,
              engine_movetime_index,
              (value) => {
                engine_movetime_index = value;
              },
              "Stop the analysis after this time. Rightmost: no limit.",
            ),
            sliderRow(
              "Nodes",
              limitLabel(nodesSteps, engine_nodes_index, formatNodes),
              0,
              nodesSteps.length,
              engine_nodes_index,
              (value) => {
                engine_nodes_index = value;
              },
              "Stop the analysis after this many nodes. Rightmost: no limit.",
            ),
          ]),

          m("div.integer-inputs", { hidden: !use_integer_inputs }, [
            integerInput(
              "Depth",
              "1",
              "255",
              "",
              (value) => {
                integer_input_engine_depth = value;
              },
              "Stop the analysis at this depth.",
            ),
            integerInput(
              "Move Time (ms)",
              "1",
              "",
              "",
              (value) => {
                integer_input_engine_movetime = value;
              },
              "Stop the analysis after this time in milliseconds.",
            ),
            integerInput(
              "Nodes",
              "1",
              "",
              "",
              (value) => {
                integer_input_engine_nodes = value;
              },
              "Stop the analysis after this many nodes.",
            ),
          ]),
          m("div.integer-inputs", { hidden: !use_integer_inputs }, [
            integerInput(
              "MultiPV",
              "1",
              "500",
              "",
              (value) => {
                integer_input_engine_multipv = value;
              },
              "Number of principal variations (engine lines) shown.",
            ),
            integerInput(
              "Threads",
              "1",
              "512",
              "",
              (value) => {
                integer_input_engine_threads = value;
              },
              "Parallel search threads of in browser Fairy-Stockfish.",
            ),
            integerInput(
              "Hash",
              "1",
              "33554432",
              "",
              (value) => {
                integer_input_engine_hash = value;
              },
              "Size of the engine's hash table in megabytes.",
            ),
          ]),

          m(
            "p.hint",
            'These settings apply to the engine analysis. Players, strength and time control of a game are chosen in "New game".',
          ),
          m("div.filerow", { hidden: during_play }, [
            m("span.filename", [
              "NNUE network file ",
              helpButton(
                "You can upload a Fairy-Stockfish compatible .nnue file. Downloads: https://fairy-stockfish.github.io/nnue/#current-best-nnue-networks.",
              ),
            ]),
            m("input", {
              type: "file",
              disabled: !is_ready,
              onchange: onSelectNnueFile,
            }),
          ]),
          ,
          m("div.hiddeninputs", [
            m("input[type=number]#depth", {
              hidden: true,
              value: use_integer_inputs
                ? integer_input_engine_depth
                : limitValue(depthSteps, engine_depth_index),
              min: 1,
              max: 255,
            }),
            m("input[type=number]#movetime", {
              hidden: true,
              value: use_integer_inputs
                ? integer_input_engine_movetime
                : limitValue(movetimeSteps, engine_movetime_index),
              min: 1,
            }),
            m("input[type=number]#nodes", {
              hidden: true,
              value: use_integer_inputs
                ? integer_input_engine_nodes
                : limitValue(nodesSteps, engine_nodes_index),
              min: 1,
            }),
            m("input[type=number]#threads", {
              hidden: true,
              value: use_integer_inputs
                ? integer_input_engine_threads
                : engine_threads,
              min: 1,
              max: 512,
            }),
            m("input[type=number]#hash", {
              hidden: true,
              value: use_integer_inputs
                ? integer_input_engine_hash
                : hashSteps[engine_hash_index],
              min: 1,
              max: 33554432,
            }),
            m("input[type=number]#multipv", {
              hidden: true,
              value: use_integer_inputs
                ? integer_input_engine_multipv
                : engine_multipv,
              min: 1,
              max: 500,
            }),
          ]),
          ,
        ]),
        m("div.hr"),
        m("div.subsection", [
          m("span.sect", "External engines"),
          m("div#divconnectserver.row", { hidden: during_play }, [
            m(
              "button",
              {
                type: "button",
                disabled: !is_ready,
                title:
                  "Connect to a local fairyground server to load native engine binaries.",
                onclick: () => {
                  if (!is_ready) {
                    return;
                  }
                  if (websocket_status == "CONNECTED") {
                    window.alert("You are already connected.");
                    return;
                  } else if (websocket_status == "CONNECTING") {
                    window.alert("Connection is during establishment process.");
                    return;
                  }
                  let port = window.prompt(
                    "Please enter the WebSocket port of local fairyground server:",
                    "5016",
                  );
                  if (port) {
                    connectToWebSocketServer(port);
                  }
                },
              },
              [icon("link", 16), "Connect"],
            ),
            m("span.hint", [
              "Runs native engines from ",
              m("code.mono", "node server.js"),
              " on this machine. ",
            ]),
            helpButton(
              "If you are using online version of fairyground, external binary engine loading feature will not be enabled automatically. You need to provide the port of local (i.e. offline version) fairyground server in order to make it work.",
            ),
          ]),
          m(
            "div#binengineinput",
            {
              hidden: during_play || websocket_status != "CONNECTED",
            },
            [
              m("div.row", [
                m(
                  "button",
                  {
                    type: "button",
                    title: "Click to enter binary engine management UI.",
                    onclick: () => {
                      fge.ShowEngineManagementUI(engine_list, websocket);
                    },
                  },
                  [icon("sliders", 16), "Engine management"],
                ),
              ]),
              m("div#whiteenginesettings", [
                m("p", "1st binary engine (First mover)"),
                m("input[type=number]#whitedepth", {
                  placeholder: "Depth",
                  title:
                    "The maximum depth that the engine is allowed to search.",
                  disabled:
                    !is_ready ||
                    websocket_status != "CONNECTED" ||
                    analysis_mode,
                  min: 1,
                }),
                m("input[type=number]#whitemovetime", {
                  placeholder: "Movetime (ms)",
                  title:
                    "The time in milliseconds that the engine can think at most.",
                  disabled:
                    !is_ready ||
                    websocket_status != "CONNECTED" ||
                    analysis_mode,
                  min: 0,
                }),
                m("input[type=number]#whitenodes", {
                  placeholder: "Nodes",
                  title: "The number of moves that the engine should search.",
                  disabled:
                    !is_ready ||
                    websocket_status != "CONNECTED" ||
                    analysis_mode,
                  min: 1,
                }),
                m(
                  "p#whiteunsupportedvariant",
                  { hidden: true },
                  "1st engine does not support this variant. In browser Fairy-Stockfish will be used instead.",
                ),
              ]),
              m("div#blackenginesettings", [
                m("p", "2nd binary engine (Second mover)"),
                m("input[type=number]#blackdepth", {
                  placeholder: "Depth",
                  title:
                    "The maximum depth that the engine is allowed to search.",
                  disabled:
                    !is_ready ||
                    websocket_status != "CONNECTED" ||
                    analysis_mode,
                  min: 1,
                }),
                m("input[type=number]#blackmovetime", {
                  placeholder: "Movetime (ms)",
                  title:
                    "The time in milliseconds that the engine can think at most.",
                  disabled:
                    !is_ready ||
                    websocket_status != "CONNECTED" ||
                    analysis_mode,
                  min: 0,
                }),
                m("input[type=number]#blacknodes", {
                  placeholder: "Nodes",
                  title: "The number of moves that the engine should search.",
                  disabled:
                    !is_ready ||
                    websocket_status != "CONNECTED" ||
                    analysis_mode,
                  min: 1,
                }),
                m(
                  "p#blackunsupportedvariant",
                  { hidden: true },
                  "2nd engine does not support this variant. In browser Fairy-Stockfish will be used instead.",
                ),
              ]),
              m("div#analysisenginesettings", [
                m(
                  "p#analysisunsupportedvariant",
                  { hidden: true },
                  "Analysis engine does not support this variant. In browser Fairy-Stockfish will be used instead.",
                ),
              ]),
            ],
          ),
        ]),
        ,
        m("div#input2", { hidden: true }, [
          m("input[type=checkbox]#playwhite", {
            hidden: true,
            checked: play_white,
          }),
          m("input[type=checkbox]#playblack", {
            hidden: true,
            checked: play_black,
          }),
          m("input[type=checkbox]#randommoverwhite", {
            hidden: true,
            checked: random_mover_white,
          }),
          m("input[type=checkbox]#randommoverblack", {
            hidden: true,
            checked: random_mover_black,
          }),
          m(
            "button#go.sm",
            {
              type: "button",
              disabled: !is_ready || analysis_mode || allLimitsInfinite(),
              title: analysis_mode
                ? "Not needed while analysis is running."
                : allLimitsInfinite()
                  ? "Set a depth, time or node limit first, otherwise the engine would think forever."
                  : "Let the engine think and move now with the limits above (used when the engine plays a side).",
              onclick: () => {
                startEngineNow();
              },
            },
            [icon("play", 14), "Engine: move now"],
          ),
          ,
          m(
            "button#stop.sm",
            {
              type: "button",
              disabled: !is_ready,
              title:
                "Immediately stop all engines from thinking (also ends an engine match).",
              onclick: () => {
                force_stop();
                if (fge.state.first_engine instanceof fge.Engine) {
                  fge.state.first_engine.ForceStop();
                }
                if (fge.state.second_engine instanceof fge.Engine) {
                  fge.state.second_engine.ForceStop();
                }
                if (fge.state.analysis_engine instanceof fge.Engine) {
                  fge.state.analysis_engine.ForceStop();
                }
                if (during_engine_match) {
                  during_engine_match = false;
                  finishGame("*", "engine match finished");
                  setTimeout(() => {
                    if (
                      window.confirm(
                        `Played games: ${engine_match_played_game_count}\nFirst engine (WHITE) wins: ${engine_match_white_wins}\nSecond engine (BLACK) wins: ${engine_match_black_wins}\nDraws: ${engine_match_draws}\n\nDo you want to save the PGN of played games?`,
                      )
                    ) {
                      document.getElementById("saveenginematchgames").click();
                    }
                  }, 500);
                }
              },
            },
            [icon("stop", 14), "Stop engine"],
          ),
          ,
          m("div.internals", [
            m("p#label-stm", { hidden: true }),
            m("input#displaymoves", {
              placeholder: "Moves displayed on board for analysis",
              hidden: true,
            }),
            m("input[type=number]#displayready", {
              placeholder: "Board display update ready status",
              hidden: true,
            }),
            m("input[type=number]#isreviewmode", {
              placeholder: "Stores value to judge whether it is in review mode",
              hidden: true,
            }),
            m("input#gameresult", {
              placeholder: "The game result",
              hidden: true,
              onclick: () => {
                displayGameResult();
              },
            }),
            m(
              "p#gamestatus",
              {
                hidden: true,
              },
              "END",
            ),
            m("input#engineoutputline", { hidden: true }),
            m("input[type=number]#timeoutside", {
              placeholder: "Stores value that the side that run out of time",
              hidden: true,
            }),
            m(
              "p#set",
              {
                onclick: () => {
                  if (review_mode) {
                    return;
                  }
                  play_move = false;
                  window.setTimeout(() => {
                    setFen(false, true);
                  }, 10);
                },
                hidden: true,
              },
              "Set position (internal)",
            ),
            m(
              "p#loadthemes",
              {
                hidden: true,
                onclick: () => {
                  LoadThemes();
                  LoadVariantSettings("server", null);
                  LoadUIThemes();
                },
              },
              "Load Themes (internal)",
            ),
            m(
              "p#initializethemes",
              {
                hidden: true,
                onclick: () => {
                  setupThemeDropdowns();
                  initPieceTheme();
                  initBoardTheme();
                },
              },
              "Initialize Themes (internal)",
            ),
            m(
              "p#setupuithemes",
              {
                hidden: true,
                onclick: () => {
                  setupUIThemeDropdown();
                  let UserSelectedUITheme = localStorage.getItem(
                    "UserSelectedUITheme",
                  );
                  if (UserSelectedUITheme) {
                    changeUI(UserSelectedUITheme, false, true);
                  } else {
                    // Default to the dark theme when available.
                    const uidropdown = $("#dropdown-uitheme");
                    let defaulttheme =
                      uidropdown[uidropdown.selectedIndex].value;
                    for (let i = 0; i < uidropdown.length; i++) {
                      if (uidropdown[i].value == "dark") {
                        defaulttheme = "dark";
                        break;
                      }
                    }
                    changeUI(defaulttheme, false, true);
                  }
                },
              },
              "Initialize UI Themes (internal)",
            ),
            m(
              "p#updatevarianttypedropdown",
              {
                hidden: true,
                onclick: () => {
                  updateVariantTypeDropdown();
                },
              },
              "Update Variant Type Dropdown (internal)",
            ),
            m(
              "p#copysetfen",
              {
                hidden: true,
                onclick: () => {
                  copyText($("#fen").value);
                  // main.js triggers this after a successful "Apply" in the board
                  // editor: leave the editor so the position is used right away.
                  if (board_setup_mode) {
                    window.setTimeout(() => {
                      const editor = document.getElementById("isboardsetup");
                      if (editor && editor.checked) {
                        editor.click();
                      }
                      if (app_mode == "setup") {
                        app_mode = "analysis";
                        m.redraw();
                      }
                    }, 0);
                  }
                },
              },
              "Copy Set FEN (internal)",
            ),
            m(
              "p#randommovergo",
              {
                hidden: true,
              },
              "Random Mover Go (internal)",
            ),
            m(
              "p#binengineoutputinit",
              {
                hidden: true,
                onclick: () => {
                  if (fge.state.first_engine instanceof fge.Engine) {
                    const target = document.getElementById("whiteengineoutput");
                    const OutputUpdateThrottleFunction = Throttle(() => {
                      target.textContent += first_engine_output;
                      first_engine_output = "";
                      scrollOutput();
                    }, throttle_threshold);
                    fge.state.first_engine.OutputUpdateCallBack = (
                      color,
                      msg,
                    ) => {
                      first_engine_output += "◀◀ " + msg + "\n";
                      OutputUpdateThrottleFunction();
                    };
                    fge.state.first_engine.SendMessageCallBack = (msg) => {
                      first_engine_output += "\n▶▶ " + msg + "\n\n";
                      OutputUpdateThrottleFunction();
                    };
                    fge.state.first_engine.OnErrorMessageCallBack = (msg) => {
                      if (during_play) {
                        window.alert(msg);
                      }
                    };
                  }
                  if (fge.state.second_engine instanceof fge.Engine) {
                    const target = document.getElementById("blackengineoutput");
                    const OutputUpdateThrottleFunction = Throttle(() => {
                      target.textContent += second_engine_output;
                      second_engine_output = "";
                      scrollOutput();
                    }, throttle_threshold);
                    fge.state.second_engine.OutputUpdateCallBack = (
                      color,
                      msg,
                    ) => {
                      second_engine_output += "◀◀ " + msg + "\n";
                      OutputUpdateThrottleFunction();
                    };
                    fge.state.second_engine.SendMessageCallBack = (msg) => {
                      second_engine_output += "\n▶▶ " + msg + "\n\n";
                      OutputUpdateThrottleFunction();
                    };
                    fge.state.second_engine.OnErrorMessageCallBack = (msg) => {
                      if (during_play) {
                        window.alert(msg);
                      }
                    };
                  }
                  if (fge.state.analysis_engine instanceof fge.Engine) {
                    const target = document.getElementById(
                      "analysisengineoutput",
                    );
                    const outputline =
                      document.getElementById("engineoutputline");
                    const OutputUpdateThrottleFunction = Throttle(() => {
                      target.textContent += analysis_engine_output;
                      analysis_engine_output = "";
                      scrollOutput();
                    }, throttle_threshold);
                    fge.state.analysis_engine.OutputUpdateCallBack = (
                      color,
                      msg,
                    ) => {
                      analysis_engine_output += "◀◀ " + msg + "\n";
                      OutputUpdateThrottleFunction();
                    };
                    fge.state.analysis_engine.EvaluationUpdateCallBack = (
                      msg,
                    ) => {
                      outputline.value = msg;
                      outputline.click();
                    };
                    fge.state.analysis_engine.SendMessageCallBack = (msg) => {
                      analysis_engine_output += "\n▶▶ " + msg + "\n\n";
                      OutputUpdateThrottleFunction();
                    };
                  }
                  scrollOutput();
                },
              },
              "Binary Engine Output Event Handler Initialization (internal)",
            ),
            m(
              "input#pgnstring",
              { hidden: true },
              "Advanced PGN Cross Domain Handler (internal)",
            ),
            m("input[type=checkbox]#isgamestarted", {
              hidden: true,
            }),
            m("p#boardorientation", {
              hidden: true,
              onclick: (e) => {
                board_orientation = e.target.textContent;
              },
            }),
          ]),
          ,
          m("input[type=checkbox]#isenginematchmode", {
            checked: engine_match_mode,
            disabled:
              !is_ready ||
              during_engine_match ||
              analysis_mode ||
              review_mode ||
              board_setup_mode ||
              random_mover_white ||
              random_mover_black,
            onclick: () => {
              engine_match_mode = !engine_match_mode;
            },
          }),
          ,
          m(
            "div#enginematch",
            {
              hidden:
                !engine_match_mode || (!during_engine_match && during_play),
            },
            [
              m("div#enginematchsettings", [
                m("input[type=number]#enginematchgamecount", {
                  placeholder: "Game count",
                  min: 1,
                  title:
                    "The count of the games to let the engines play against each other.",
                }),
                m(
                  "button#startenginematch.soft",
                  {
                    type: "button",
                    title: "Click to start a series of engine vs engine games.",
                    disabled: !is_ready || during_engine_match || review_mode,
                    onclick: () => {
                      if (
                        !engine_match_mode ||
                        during_engine_match ||
                        review_mode
                      ) {
                        return;
                      }
                      const whitedepth = document.getElementById("whitedepth");
                      const whitemovetime =
                        document.getElementById("whitemovetime");
                      const whitenodes = document.getElementById("whitenodes");
                      const blackdepth = document.getElementById("blackdepth");
                      const blackmovetime =
                        document.getElementById("blackmovetime");
                      const blacknodes = document.getElementById("blacknodes");
                      const depth = document.getElementById("depth");
                      const movetime = document.getElementById("movetime");
                      const nodes = document.getElementById("nodes");
                      if (advanced_time_control) {
                        if (
                          white_timer_type == "infinite" ||
                          black_timer_type == "infinite"
                        ) {
                          window.alert(
                            "Cannot start engine match with infinite time.",
                          );
                          return;
                        }
                      } else {
                        if (fge) {
                          if (
                            fge.state.first_engine instanceof fge.Engine &&
                            fge.state.first_engine.IsUsing
                          ) {
                            if (
                              (!whitedepth.validity.valid ||
                                whitedepth.value == "") &&
                              (!whitemovetime.validity.valid ||
                                whitemovetime.value == "") &&
                              (!whitenodes.validity.valid ||
                                whitenodes.value == "")
                            ) {
                              window.alert(
                                "Move control is not set or invalid for first binary engine. Set depth/movetime/nodes before starting an engine match.",
                              );
                              return;
                            }
                          } else {
                            if (
                              (!depth.validity.valid || depth.value == "") &&
                              (!movetime.validity.valid ||
                                movetime.value == "") &&
                              (!nodes.validity.valid || nodes.value == "")
                            ) {
                              window.alert(
                                "Move control is not set or invalid for in browser Fairy-Stockfish. Set depth/movetime/nodes before starting an engine match.",
                              );
                              return;
                            }
                          }
                          if (
                            fge.state.second_engine instanceof fge.Engine &&
                            fge.state.second_engine.IsUsing
                          ) {
                            if (
                              (!blackdepth.validity.valid ||
                                blackdepth.value == "") &&
                              (!blackmovetime.validity.valid ||
                                blackmovetime.value == "") &&
                              (!blacknodes.validity.valid ||
                                blacknodes.value == "")
                            ) {
                              window.alert(
                                "Move control is not set or invalid for second binary engine. Set depth/movetime/nodes before starting an engine match.",
                              );
                              return;
                            }
                          } else {
                            if (
                              (!depth.validity.valid || depth.value == "") &&
                              (!movetime.validity.valid ||
                                movetime.value == "") &&
                              (!nodes.validity.valid || nodes.value == "")
                            ) {
                              window.alert(
                                "Move control is not set or invalid for in browser Fairy-Stockfish. Set depth/movetime/nodes before starting an engine match.",
                              );
                              return;
                            }
                          }
                        } else {
                          if (
                            (!depth.validity.valid || depth.value == "") &&
                            (!movetime.validity.valid ||
                              movetime.value == "") &&
                            (!nodes.validity.valid || nodes.value == "")
                          ) {
                            window.alert(
                              "Move control is not set or invalid for in browser Fairy-Stockfish. Set depth/movetime/nodes before starting an engine match.",
                            );
                            return;
                          }
                        }
                      }
                      engine_match_game_list = [];
                      let game_count = document.getElementById(
                        "enginematchgamecount",
                      ).value;
                      play_white = true;
                      play_black = true;
                      during_engine_match = true;
                      engine_match_played_game_count = 0;
                      if (
                        !document.getElementById("enginematchgamecount")
                          .validity.valid ||
                        game_count == ""
                      ) {
                        engine_match_total_game_count = 1;
                      } else {
                        engine_match_total_game_count = parseInt(game_count);
                      }
                      engine_match_white_wins = 0;
                      engine_match_black_wins = 0;
                      engine_match_draws = 0;
                      document.getElementById("enginematchinfo").innerText =
                        `Games played: 0 | Total games to play: ${engine_match_total_game_count}`;
                      if (advanced_time_control) {
                        document.getElementById("gamestart").click();
                      } else {
                        document.getElementById("set").click();
                      }
                    },
                  },
                  [icon("play", 16), "Start match"],
                ),
                m(
                  "button#saveenginematchgames.ghost",
                  {
                    type: "button",
                    title:
                      "Click to save the games played in engine match to PGN file.",
                    disabled: !is_ready || during_engine_match || review_mode,
                    onclick: () => {
                      if (
                        !engine_match_mode ||
                        during_engine_match ||
                        review_mode
                      ) {
                        return;
                      }
                      let filecontent = "";
                      engine_match_game_list.forEach((val) => {
                        filecontent += `${val.ToPortableGameNotation(window.ffishlib)}\n`;
                      });
                      const blob = new Blob([filecontent], {
                        type: "text/plain",
                      });
                      const a = document.createElement("a");
                      a.href = URL.createObjectURL(blob);
                      a.download = "EngineMatch.pgn";
                      document.body.appendChild(a);
                      a.click();
                      document.body.removeChild(a);
                    },
                  },
                  "Save games as PGN",
                ),
                helpButton(
                  'You can let the engines play against each other (Supports binary engines, based on your settings) for a certain count of games automatically and Fairyground will collect the statistics on win/draw/loss counts for you to test variant balance or engine strength.\nYou need to setup time settings first, e.g. depth/move time/nodes controlled moving or use advanced time control. All the matches uses that setting after you click <Start Engine Match>.\nYou can click <Stop> to exit this mode at any time.\nThis will not swap sides, so if you want to let engines play each side, you can let them play N games and then swap side manually to play another N games.\nDo not do unnecessary things like setting FEN or changing variant during the match, otherwise something unexpected may happen.\nNote: If the match stops unexpectedly, then it usually indicates an engine crash. Check the console (Press Ctrl+Shift+I and select "Console" to see it) to see what\'s going on.',
                ),
              ]),
              m(
                "p#enginematchinfo",
                'Click <Start match> to automatically start engine vs engine games for some times specified in "Game count".',
              ),
            ],
          ),
          ,
        ]),
      ],
    );

    // ---------------- setup panel (board editor) ----------------
    const setupTab = m(
      "div.tabpanel#tab-setup",
      {
        class: app_mode == "setup" ? "on" : "",
        hidden: app_mode != "setup",
      },
      [
        m("div.secthead", [
          m("span.sect", "Position"),
          m(
            "button.sm.primary",
            {
              type: "button",
              title:
                'Leave board editor. Changes made in "board editor" section that are not applied will be discarded.',
              onclick: () => {
                leaveSetup();
              },
            },
            [icon("check", 14), "Done"],
          ),
        ]),
        m("div#input", { hidden: during_play }, [
          m("span.sect", "Position"),
          m("div.field", [
            m(
              "span.label",
              "FEN · leave blank for the variant's start position",
            ),
            m("input[type=text]#fen", {
              placeholder: "Input FEN Here",
              title:
                "Input the Forsyth-Edwards Notation (FEN) of the position you want to load. Leave it blank to use default position.",
              maxlength: 9999,
              disabled: !is_ready || review_mode,
              onkeyup: (e) => {
                if (e.keyCode != 13) {
                  e.redraw = false;
                  return;
                }
                document.getElementById("setpos").click();
              },
            }),
          ]),
          m("div.field", [
            m("span.label", "Moves · UCI, space separated"),
            m("input[type=text]#move", {
              placeholder: "Input Move Here",
              title:
                "Input the moves in UCI format based on the FEN. Leave it blank to indicate no move.",
              maxlength: 9999,
              disabled: !is_ready || review_mode,
              onkeyup: (e) => {
                if (e.keyCode != 13) {
                  e.redraw = false;
                  return;
                }
                document.getElementById("setpos").click();
              },
            }),
          ]),
          m("div.row", [
            m(
              "button#setpos.primary",
              {
                type: "button",
                disabled: !is_ready || review_mode,
                title: "Click to set the FEN and the moves to the board.",
                onclick: () => {
                  if (review_mode) {
                    return;
                  }
                  resetTimer();
                  stockfish.postMessage(`stop`);
                  stockfish.postMessage(`ucinewgame`);
                  if (fge.state.first_engine instanceof fge.Engine) {
                    fge.state.first_engine.NewGame();
                  }
                  if (fge.state.second_engine instanceof fge.Engine) {
                    fge.state.second_engine.NewGame();
                  }
                  if (fge.state.analysis_engine instanceof fge.Engine) {
                    fge.state.analysis_engine.NewGame();
                  }
                  play_move = false;
                  window.setTimeout(() => {
                    setFen(true, false);
                  }, 10);
                },
              },
              "Set position",
            ),
            m(
              "button#reset",
              {
                type: "button",
                disabled: !is_ready,
                title: "Click to reset the position to default position.",
                onclick: reset,
              },
              "Reset",
            ),
            m(
              "button#restart",
              {
                type: "button",
                disabled: !is_ready || review_mode,
                title:
                  "Click to clear the moves and set the position to initial position.",
              },
              "Restart",
            ),
          ]),
        ]),
        ,
        m("div.hr"),
        m("span.sect", "Start position"),
        m("div.row", [
          m(
            "button.pickbtn.positionpick",
            {
              type: "button",
              disabled:
                !is_ready ||
                review_mode ||
                !positionVariantsFor(currentVariantId()),
              title: positionVariantsFor(currentVariantId())
                ? "Choose a start position for this variant"
                : "This variant has no predefined start positions",
              onclick: () => {
                position_picker_open = true;
              },
            },
            [
              m("span.picklabel", [
                m(
                  "span.name",
                  (() => {
                    const namedropdown = document.getElementById(
                      "dropdown-posvariantname",
                    );
                    return namedropdown && namedropdown.selectedIndex >= 0
                      ? namedropdown.value
                      : "Start position";
                  })(),
                ),
              ]),
              icon("chev", 16),
            ],
          ),
          m(
            "button#aboutposition.sm",
            {
              type: "button",
              disabled: !is_ready || review_mode,
              title:
                "Position info\nClick to show the information of current selected custom position (position variant).",
            },
            [icon("target", 14), "Position info"],
          ),
          m(
            "button#aboutvariant.sm",
            {
              type: "button",
              disabled: !is_ready || review_mode,
              title:
                "Variant info\nClick to show the information and the wiki page (if it has, otherwise not shown) of current variant.",
              onclick: () => {
                let name = getVariantName(
                  $("#dropdown-variant").value,
                  true,
                  false,
                );
                let description = getVariantDescription(
                  $("#dropdown-variant").value,
                  false,
                );
                let wiki = getVariantWikiPageURL(
                  $("#dropdown-variant").value,
                  false,
                );
                if (description) {
                  if (wiki) {
                    if (
                      window.confirm(
                        `Variant ${name} (ID: ${$("#dropdown-variant").value}):\n${description}\n\nWiki: ${wiki}\n\nDo you want to visit the wiki page?`,
                      )
                    ) {
                      OpenURL(wiki);
                    }
                  } else {
                    window.alert(
                      `Variant ${name} (ID: ${$("#dropdown-variant").value}):\n${description}`,
                    );
                  }
                } else {
                  window.alert(
                    "This variant does not provide a description. You can upload a variantsettings.txt yourself to add a description for it.",
                  );
                }
              },
            },
            [icon("info", 14), "Variant info"],
          ),
        ]),
        m("div.hr"),
        m("span.sect", "Board editor"),
        m("label#label-boardsetup", { hidden: true }, [
          m("input[type=checkbox]#isboardsetup", {
            checked: board_setup_mode,
            disabled:
              review_mode ||
              during_play ||
              engine_match_mode ||
              during_engine_match,
            title:
              review_mode ||
              during_play ||
              engine_match_mode ||
              during_engine_match
                ? "The board editor is not available during a game, in review mode or during an engine match."
                : "Edit the position. This switches analysis, the time control and the moves dialog off.",
            onclick: (e) => {
              const on = e.target.checked;
              if (on) {
                // The editor is exclusive with analysis, timed
                // games and the moves dialog: switch them off.
                setAnalysisMode(false);
                advanced_time_control = false;
                select_move_dialog = false;
                ["advtimectrl", "showmovediv"].forEach((id) => {
                  const element = document.getElementById(id);
                  if (element) {
                    element.checked = false;
                  }
                });
              }
              board_setup_mode = on;
              triggerBoardSetupPieceIdentifier(true);
            },
          }),
          ,
        ]),
        m("div#boardsetupsettings", { hidden: !board_setup_mode }, [
          m("div#boardpiecechange", { disabled: !is_ready }, [
            m("div.piecepalette", [
              pieceChoices().map((choice) =>
                m(
                  "button.palettebtn",
                  {
                    type: "button",
                    key: choice.value,
                    class: choice.selected ? "on" : "",
                    title: choice.title,
                    onclick: () => {
                      const dropdown =
                        document.getElementById("dropdown-setpiece");
                      dropdown.value = choice.value;
                      dropdown.dispatchEvent(new Event("change"));
                    },
                  },
                  choice.icon
                    ? icon(choice.icon, 18)
                    : m("div.palettewrap", { class: pieceThemeClasses() }, [
                        m(
                          `div.cg-wrap.orientation-${piece_palette_orientation}`,
                          [m("piece", { class: choice.pieceClass })],
                        ),
                      ]),
                ),
              ),
            ]),
            m(
              "p.hint",
              "Pick a piece, then click a square to place it. Drag pieces to move them, drop them off the board to remove them.",
            ),
            m(
              "p.hint",
              'Changes made here will not be effective until you click "Apply" button.',
            ),
            m(
              "select#dropdown-setpiece",
              {
                hidden: true,
                title:
                  "<move>: Move the pieces on the board.\n<delete>: Click on a square to delete the piece on that square.\n<letter>: Click on a square to place a piece of that letter. If there is a plus ahead, it means the promoted from.",
                onchange: () => {
                  let fakepiece = document.getElementById("fakepiece");
                  let dropdownsetpiece =
                    document.getElementById("dropdown-setpiece");
                  let values = [];
                  let value =
                    dropdownsetpiece[dropdownsetpiece.selectedIndex].value;
                  if (value == undefined || value == "") {
                    return;
                  }
                  let chcode = value.charCodeAt(0);
                  let ch = value.charAt(0);
                  let promoted = false;
                  if (value.charAt(0) == "+") {
                    chcode = value.charCodeAt(1);
                    ch = value.charAt(1);
                    promoted = true;
                  }
                  if (value == "<move>") {
                    values.push("move-piece");
                  } else if (value == "<delete>") {
                    values.push("delete-piece");
                  } else if (
                    value.length > 2 ||
                    (value.length == 2 && value.charAt(0) != "+")
                  ) {
                    return;
                  } else if (chcode >= 65 && chcode <= 90) {
                    values.push(
                      `${promoted ? "p" : ""}${ch.toLowerCase()}-piece`,
                    );
                    values.push("white");
                  } else if (chcode >= 97 && chcode <= 122) {
                    values.push(`${promoted ? "p" : ""}${ch}-piece`);
                    values.push("black");
                  } else if (value == "*") {
                    values.push("_-piece");
                    values.push("black");
                  } else {
                    return;
                  }
                  fakepiece.classList.value = values.join(" ");
                },
              },
              [
                m("option", { value: "<move>" }, "<move>"),
                m("option", { value: "<delete>" }, "<delete>"),
                m("option", { value: "b" }, "b"),
                m("option", { value: "k" }, "k"),
                m("option", { value: "n" }, "n"),
                m("option", { value: "p" }, "p"),
                m("option", { value: "q" }, "q"),
                m("option", { value: "r" }, "r"),
                m("option", { value: "B" }, "B"),
                m("option", { value: "K" }, "K"),
                m("option", { value: "N" }, "N"),
                m("option", { value: "P" }, "P"),
                m("option", { value: "Q" }, "Q"),
                m("option", { value: "R" }, "R"),
              ],
            ),
            m("div#boardeditorbuttons", [
              m(
                "button#addtopocket.sm",
                {
                  type: "button",
                  disabled: !is_ready,
                  title:
                    "Click to add the piece selected in the dropdown to pocket.",
                },
                "Add to pocket",
              ),
              m(
                "button#clearboard.sm",
                {
                  type: "button",
                  disabled: !is_ready,
                  title: "Click to remove all pieces.",
                },
                "Clear board",
              ),
              m(
                "button#initboardpos.sm",
                {
                  type: "button",
                  disabled: !is_ready,
                  title: "Click to set the board to default position.",
                },
                "Reset board",
              ),
              m(
                "button#validatepos.sm.soft",
                {
                  type: "button",
                  disabled: !is_ready,
                  title: "Click to validate this position.",
                },
                "Validate",
              ),
              m(
                "button#boardsetupcopyfen.sm.primary",
                {
                  type: "button",
                  disabled: !is_ready,
                  title:
                    "Click to set the position, and then uncheck Board Setup to play or analyze.",
                },
                "Apply",
              ),
            ]),
          ]),
          m("div#pocketpiecechange", { hidden: true }, [
            m("form#pieceinpocket", { disabled: !is_ready }, [
              m("table#tablepieceinpocket", [
                m("tr", [m("td", "Piece ID"), m("td", "Amount")]),
              ]),
            ]),
          ]),
        ]),
        ,
        m("div#boardsetupsettings2", { hidden: !board_setup_mode }, [
          m("div", [
            m("span.label", "Side to move"),
            m(
              "select#dropdown-sidetomove.sm",
              { title: "Select the side to move in this position." },
              [
                m("option", { value: "First Mover" }, "First Mover"),
                m("option", { value: "Second Mover" }, "Second Mover"),
              ],
            ),
          ]),
          m("div", [
            m(
              "label.toggle",
              {
                title: "Check if first mover has the right to castle kingside.",
              },
              [
                m("input[type=checkbox]#whitekingsidecastle.box"),
                m("span", "White O-O"),
              ],
            ),
            m(
              "label.toggle",
              {
                title:
                  "Check if first mover has the right to castle queenside.",
              },
              [
                m("input[type=checkbox]#whitequeensidecastle.box"),
                m("span", "White O-O-O"),
              ],
            ),
            m(
              "label.toggle",
              {
                title:
                  "Check if second mover has the right to castle kingside.",
              },
              [
                m("input[type=checkbox]#blackkingsidecastle.box"),
                m("span", "Black O-O"),
              ],
            ),
            m(
              "label.toggle",
              {
                title:
                  "Check if second mover has the right to castle queenside.",
              },
              [
                m("input[type=checkbox]#blackqueensidecastle.box"),
                m("span", "Black O-O-O"),
              ],
            ),
          ]),
          m("div", [
            m("input[type=number]#halfmoveclock", {
              placeholder: "Half move clock",
              title:
                "The number in half move clock, which records the moves that does not capture or is not irreversible for N-move rule.",
              min: 0,
            }),
            m("input[type=number]#whiteremainingchecks", {
              placeholder: "White remaining checks",
              title:
                "The remaining checks of first mover, used in variants that limit check count such as 3 Check.",
              min: 1,
            }),
            m("input[type=number]#blackremainingchecks", {
              placeholder: "Black remaining checks",
              title:
                "The remaining checks of second mover, used in variants that limit check count such as 3 Check.",
              min: 1,
            }),
            m("input[type=number]#currentmovenum", {
              placeholder: "Current move number",
              title:
                "The number of current move in full move format (A turn that both player make a move is 1 full move, 2 half moves).",
              min: 1,
            }),
          ]),
          m("div", [
            m("input[type=number]#enpassantfile", {
              placeholder: "En passant file number",
              title: "The file (column) number of en passant square.",
              min: 1,
              max: 12,
            }),
            m("input[type=number]#enpassantrank", {
              placeholder: "En passant rank number",
              title: "The rank (row) number of en passant square.",
              min: 1,
              max: 10,
            }),
          ]),
          m("div", [
            m("input[type=text]#seirwangatingfiles", {
              placeholder: "Seirawan gating files (e.g. ABab)",
              title:
                'The files (e.g. 1st column is a-file, 2nd column is b-file, etc.) where players can perform seirawan gating.\nGateable files for first mover is in upper case and for second mover in lower case.\nExample: "ABcd" means first mover can gate at A and B file while second mover can gate at C and D file.',
              maxlength: 9999,
            }),
          ]),
        ]),
        ,
      ],
    );

    // ---------------- variant editor tab ----------------
    if (active_tab == "variant") {
      loadVariantEditor();
    }
    const editor_api = variantEditorApi();
    const can_load_ini =
      is_ready &&
      !ini_busy &&
      !!editor_api &&
      app_mode == "analysis" &&
      !review_mode &&
      !board_setup_mode &&
      !during_engine_match;
    const load_ini_title =
      app_mode != "analysis"
        ? "Variants can be loaded on the analysis board."
        : null;
    const saved_variants = myVariants();
    const option_results = (() => {
      const words = ini_option_search
        .trim()
        .toLowerCase()
        .split(/\s+/)
        .filter((w) => w != "");
      if (!editor_api || words.length == 0) {
        return [];
      }
      const scored = [];
      editor_api.variantOptions.options.forEach((option) => {
        const key = option.key.toLowerCase();
        const text = `${key} ${option.description.toLowerCase()}`;
        if (!words.every((w) => text.includes(w))) {
          return;
        }
        scored.push({
          option,
          score: words.every((w) => key.includes(w))
            ? key.startsWith(words[0])
              ? 0
              : 1
            : 2,
        });
      });
      scored.sort(
        (a, b) => a.score - b.score || a.option.key.localeCompare(b.option.key),
      );
      return scored.slice(0, 40).map((s) => s.option);
    })();
    const optionMeta = (option) =>
      [
        option.type,
        option.values ? option.values.join(" | ") : null,
        option.default !== null && option.default !== ""
          ? `default ${option.default}`
          : null,
      ]
        .filter((part) => part)
        .join(" · ");
    const error_count = iniErrorCount();
    const warning_count = ini_diagnostics
      ? ini_diagnostics.length - error_count
      : 0;
    const contextHelp = (() => {
      if (!ini_context || !editor_api) {
        return null;
      }
      if (ini_context.option) {
        const option = ini_context.option;
        return m("div.inihelp", [
          m("div.inihelphead", [
            m("span.mono.key", option.key),
            m("span.pill", option.group),
          ]),
          optionMeta(option) ? m("p.hint.mono", optionMeta(option)) : null,
          m("p", option.description),
          option.type && editor_api.variantOptions.types[option.type]
            ? m(
                "p.hint",
                `${option.type}: ${editor_api.variantOptions.types[option.type].description}` +
                  (editor_api.variantOptions.types[option.type].hint
                    ? ` [${editor_api.variantOptions.types[option.type].hint}]`
                    : ""),
              )
            : null,
        ]);
      }
      if (ini_context.key) {
        return m("div.inihelp", [
          m("div.inihelphead", [m("span.mono.key", ini_context.key)]),
          m(
            "p.hint",
            "This is not a documented option. Search the options below or press Ctrl+Space for suggestions.",
          ),
        ]);
      }
      return null;
    })();
    const betzaPreviewView = (() => {
      if (!ini_context || !ini_context.betza) {
        return null;
      }
      const preview =
        ini_preview && ini_preview.betza == ini_context.betza
          ? ini_preview.result
          : undefined;
      if (preview === undefined) {
        return m("div.betzapreview", m("p.hint", "Computing moves…"));
      }
      if (preview === null) {
        return m(
          "div.betzapreview",
          m("p.hint.warn", "This Betza notation cannot be previewed."),
        );
      }
      const rows = [];
      for (let rank = preview.size; rank >= 1; rank--) {
        for (let file = 0; file < preview.size; file++) {
          const square = preview.files[file] + rank;
          const quiet = preview.quiet.has(square);
          const capture = preview.capture.has(square);
          rows.push(
            m(
              "span.betzasq",
              {
                key: square,
                class: [
                  (file + rank) % 2 ? "light" : "dark",
                  square == preview.center ? "piece" : "",
                  quiet && capture
                    ? "both"
                    : quiet
                      ? "quiet"
                      : capture
                        ? "capture"
                        : "",
                  preview.hop.has(square) ? "hop" : "",
                ].join(" "),
                title:
                  square == preview.center
                    ? "Piece"
                    : quiet && capture
                      ? "Move or capture"
                      : quiet
                        ? "Move only"
                        : capture
                          ? "Capture only"
                          : "",
              },
              square == preview.center ? icon("target", 14) : null,
            ),
          );
        }
      }
      return m("div.betzapreview", [
        m("div.inihelphead", [
          m("span.sect", "Movement"),
          m("span.mono.key", ini_context.betza),
        ]),
        m(
          "div.betzaboard",
          {
            style: `--betza-size:${preview.size}; --betza-rows:${Math.ceil(rows.length / preview.size)};`,
          },
          rows,
        ),
        m("div.betzalegend", [
          m("span", [m("span.betzasq.quiet"), "Move"]),
          m("span", [m("span.betzasq.capture"), "Capture"]),
          m("span", [m("span.betzasq.both"), "Both"]),
        ]),
        preview.hop.size > 0
          ? m(
              "p.hint",
              "Hopping moves are shown with a screen piece next to the piece.",
            )
          : null,
        preview.initial
          ? m("p.hint", "Initial moves (i) are not shown.")
          : null,
        m("p.hint", "White moves up the board."),
      ]);
    })();
    const variantTab = m(
      "div.tabpanel#tab-variant",
      {
        class: active_tab == "variant" ? "on" : "",
        hidden: app_mode == "setup",
      },
      [
        m("div.secthead", [
          m("span.sect", "Variant editor"),
          m(
            "a.btn.sm.ghost",
            {
              href: "https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Variant-configuration",
              target: "_blank",
              rel: "noopener",
              title: "Documentation of the variants.ini format",
            },
            [icon("book", 14), "Docs"],
          ),
        ]),
        m("div#variantini", {
          oncreate: (vnode) => mountVariantEditor(vnode.dom),
          onupdate: (vnode) => mountVariantEditor(vnode.dom),
        }),
        ini_editor_state == "failed"
          ? m("p.hint.warn", "The variant editor could not be loaded.")
          : ini_editor_state != "ready"
            ? m("p.hint", "Loading the variant editor…")
            : m(
                "p.inistatus",
                {
                  class:
                    error_count > 0
                      ? "error"
                      : warning_count > 0
                        ? "warn"
                        : "ok",
                },
                ini_diagnostics === null
                  ? "Checking…"
                  : error_count + warning_count == 0
                    ? [icon("check", 14), "No problems found"]
                    : `${error_count} error${error_count == 1 ? "" : "s"} · ${warning_count} warning${warning_count == 1 ? "" : "s"}`,
              ),
        ini_diagnostics && ini_diagnostics.length > 0
          ? m(
              "ul.inimessages",
              ini_diagnostics
                .slice()
                .sort((a, b) => a.line - b.line)
                .map((d) =>
                  m(
                    "li.clickable",
                    {
                      class: d.severity == "error" ? "error" : "warn",
                      title: "Go to this line",
                      onclick: () => {
                        if (ini_editor) {
                          ini_editor.goToLine(d.line);
                        }
                      },
                    },
                    `${d.line}: ${d.message}`,
                  ),
                ),
            )
          : null,
        m("div.row", [
          m(
            "button.sm.primary",
            {
              type: "button",
              disabled: !can_load_ini,
              title:
                load_ini_title ||
                "Try the variants on the board under temporary names (Ctrl+Enter).",
              onclick: () => tryIni(),
            },
            [icon("play", 16), ini_busy ? "Loading…" : "Try"],
          ),
          m(
            "button.sm",
            {
              type: "button",
              disabled: !can_load_ini,
              title:
                load_ini_title ||
                "Save the variants to My variants under their names. They are loaded on every visit.",
              onclick: saveIniToMyVariants,
            },
            [icon("save", 14), "Save to My variants"],
          ),
        ]),
        ini_messages.length > 0
          ? m(
              "ul.inimessages",
              { "aria-live": "polite" },
              ini_messages.map((message) =>
                m("li", { class: message.kind }, message.text),
              ),
            )
          : null,
        contextHelp || betzaPreviewView
          ? m("div.inicontext", [contextHelp, betzaPreviewView])
          : null,
        m("div.stack.inioptions", [
          m("span.sect", "Options"),
          m("input[type=search]", {
            placeholder: "Search options, e.g., promotion…",
            value: ini_option_search,
            disabled: !editor_api,
            oninput: (e) => {
              ini_option_search = e.target.value;
            },
          }),
          option_results.length > 0
            ? m(
                "div.inioptionlist",
                option_results.map((option) =>
                  m(
                    "button.inioption",
                    {
                      type: "button",
                      key: option.key,
                      title: `Add ${option.key} to the variant at the cursor`,
                      onclick: () => {
                        if (
                          ini_editor &&
                          !ini_editor.insertOption(
                            option.key,
                            exampleValue(option),
                          )
                        ) {
                          ini_messages = [
                            {
                              kind: "error",
                              text: "Add a variant section like [myvariant:chess] first.",
                            },
                          ];
                        }
                      },
                    },
                    [
                      m("span.rowhead", [
                        m("span.mono.key", option.key),
                        optionMeta(option)
                          ? m("span.hint.mono", optionMeta(option))
                          : null,
                      ]),
                      m("span.desc", option.description),
                    ],
                  ),
                ),
              )
            : ini_option_search.trim() != "" && editor_api
              ? m("p.hint", "No option matches.")
              : null,
        ]),
        m("div.stack", [
          m("span.sect", "My variants"),
          saved_variants.length == 0
            ? m(
                "p.hint",
                "Variants saved here are available in the variant picker on every visit.",
              )
            : m(
                "div.myvariants",
                saved_variants.map((entry) =>
                  m("div.myvariant", { key: entry.name }, [
                    m("span.mono.key", entry.name),
                    ini_pending_reload.has(entry.name)
                      ? m(
                          "span.pill",
                          {
                            title:
                              "The changed definition is used after reloading the page.",
                          },
                          "reload to update",
                        )
                      : null,
                    m("span.spacer"),
                    m(
                      "button.sm.ghost",
                      {
                        type: "button",
                        disabled:
                          !can_load_ini || !allvariants.includes(entry.name),
                        title: "Show this variant on the board",
                        onclick: () => selectVariant(entry.name),
                      },
                      [icon("play", 14), "Play"],
                    ),
                    m(
                      "button.sm.ghost",
                      {
                        type: "button",
                        disabled: !editor_api,
                        title: "Open this variant in the editor",
                        onclick: () => editMyVariant(entry),
                      },
                      [icon("edit", 14), "Edit"],
                    ),
                    m(
                      "button.sm.ghost.iconbtn",
                      {
                        type: "button",
                        title: "Delete this variant from My variants",
                        onclick: () => deleteMyVariant(entry),
                      },
                      icon("trash", 14),
                    ),
                  ]),
                ),
              ),
        ]),
        m("div.row", [
          m("label.btn.sm.ghost", { title: "Open a variants.ini file" }, [
            icon("upload", 14),
            "Open file",
            m("input[type=file]", {
              hidden: true,
              accept: ".ini,.txt,text/plain",
              disabled: !editor_api,
              onchange: openIniFile,
            }),
          ]),
          m(
            "button.sm.ghost",
            {
              type: "button",
              title: "Download the definition as variants.ini",
              onclick: downloadIniFile,
            },
            [icon("install", 14), "Download"],
          ),
          m(
            "button.sm.ghost",
            {
              type: "button",
              disabled: !editor_api,
              title: "Replace the definition with an example",
              onclick: () => {
                if (
                  !editorHasUnsavedText() ||
                  window.confirm(
                    "The editor has unsaved changes. Replace them with the example?",
                  )
                ) {
                  setEditorText(INI_TEMPLATE);
                  ini_messages = [];
                }
              },
            },
            [icon("doc", 14), "Example"],
          ),
        ]),
      ],
    );

    // ---------------- console tab ----------------
    const panel = m("section.panel.card#info", [
      m("div.tabs#outputs", { hidden: app_mode == "setup" }, [
        tabButton("moves", "Moves", "list"),
        tabButton("engine", "Engine", "cpu"),
        tabButton("variant", "Variant", "code"),
      ]),
      movesTab,
      engineTab,
      variantTab,
      setupTab,
    ]);

    // ---------------- new game dialog ----------------
    const clockModes = ["tournament", "time per move", "hourglass", "byoyomi"];
    const isClockMode = (mode) => clockModes.includes(mode);
    const isEnginePlayer = (player) => player == "fsf" || player == "ext";
    const externalAvailable = websocket_status == "CONNECTED";
    const sideSetup = (side, label, game, tc) => {
      const engine = isEnginePlayer(game.player);
      const modeOptions = engine
        ? [
            [
              "movetime",
              "Time per move",
              "This player needs to make each move within a fixed search time limit.",
            ],
            [
              "depth",
              "Depth per move",
              "This player needs to make each move within a fixed search depth limit.",
            ],
            [
              "nodes",
              "Nodes per move",
              "This player needs to make each move within a fixed search node limit.",
            ],
            [
              "tournament",
              "Tournament clock",
              "This player has limited time and may get a time increment after a move.",
            ],
            [
              "hourglass",
              "Hourglass clock",
              "This player has limited time and used time will be added to opponent's time.",
            ],
            [
              "byoyomi",
              "Byo-yomi clock",
              "This player will enter the countdown (byoyomi) period(s) after their initial time runs out. During countdown periods, if the player make a move before the countdown period time runs out, the time will be reset to full time of countdown periods, otherwise the remaining period count will be decreased by 1 and the time will be reset to full time of countdown periods. If there's no countdown periods left and the remaining time runs out, this player runs out of time.",
            ],
          ]
        : [
            ["infinite", "No clock", "This player has infinite time."],
            [
              "tournament",
              "Tournament",
              "This player has limited time and may get a time increment after a move.",
            ],
            [
              "time per move",
              "Time per move",
              "This player needs to make each move within a fixed time limit.",
            ],
            [
              "hourglass",
              "Hourglass",
              "This player has limited time and used time will be added to opponent's time.",
            ],
            [
              "byoyomi",
              "Byo-yomi",
              "This player will enter the countdown (byoyomi) period(s) after their initial time runs out. During countdown periods, if the player make a move before the countdown period time runs out, the time will be reset to full time of countdown periods, otherwise the remaining period count will be decreased by 1 and the time will be reset to full time of countdown periods. If there's no countdown periods left and the remaining time runs out, this player runs out of time.",
            ],
          ];
      const limitRow = m("div", [
        m("div", { hidden: game.mode != "depth" }, [
          use_integer_inputs
            ? integerInput(
                "Depth",
                "1",
                "255",
                default_depth,
                (value) => {
                  if (side == "white") {
                    integer_input_white_depth = value;
                  } else {
                    integer_input_black_depth = value;
                  }
                },
                "Search depth per move.",
                true,
              )
            : sliderRow(
                "Depth",
                String(depthSteps[game.depth]),
                0,
                depthSteps.length - 1,
                game.depth,
                (value) => {
                  game.depth = value;
                },
                "Search depth per move.",
              ),
        ]),
        m("div", { hidden: game.mode != "nodes" }, [
          use_integer_inputs
            ? integerInput(
                "Nodes",
                "1",
                "",
                default_nodes,
                (value) => {
                  if (side == "white") {
                    integer_input_white_nodes = value;
                  } else {
                    integer_input_black_nodes = value;
                  }
                },
                "Searched nodes per move.",
                true,
              )
            : sliderRow(
                "Nodes",
                formatNodes(nodesSteps[game.nodes]),
                0,
                nodesSteps.length - 1,
                game.nodes,
                (value) => {
                  game.nodes = value;
                },
                "Searched nodes per move.",
              ),
        ]),
        m("div", { hidden: game.mode != "movetime" }, [
          use_integer_inputs
            ? integerInput(
                "Move Time (ms)",
                "1",
                "",
                default_movetime,
                (value) => {
                  if (side == "white") {
                    integer_input_white_movetime = value;
                  } else {
                    integer_input_black_movetime = value;
                  }
                },
                "Thinking time per move in milliseconds.",
                true,
              )
            : sliderRow(
                "Time per move",
                formatSeconds(movetimeSteps[game.movetime]),
                0,
                movetimeSteps.length - 1,
                game.movetime,
                (value) => {
                  game.movetime = value;
                },
                "Thinking time per move.",
              ),
        ]),
      ]);
      return m("div.sidesetup", [
        m("span.sect", label),
        m("div.nums.two", [
          m("div.field", [
            m("span.label", "Player"),
            m(
              "select",
              {
                onchange: (e) => {
                  game.player = e.target.value;
                  if (
                    isEnginePlayer(game.player) &&
                    !isClockMode(game.mode) &&
                    game.mode != "depth" &&
                    game.mode != "nodes"
                  ) {
                    game.mode = "movetime";
                  } else if (
                    game.player == "random" ||
                    (!isEnginePlayer(game.player) && !isClockMode(game.mode))
                  ) {
                    game.mode = "infinite";
                  }
                },
              },
              [
                m(
                  "option",
                  { value: "you", selected: game.player == "you" },
                  "You",
                ),
                m(
                  "option",
                  { value: "fsf", selected: game.player == "fsf" },
                  "Fairy-Stockfish",
                ),
                m(
                  "option",
                  { value: "random", selected: game.player == "random" },
                  "Random mover",
                ),
                m(
                  "option",
                  {
                    value: "ext",
                    selected: game.player == "ext",
                    disabled: !externalAvailable,
                  },
                  externalAvailable
                    ? "External engine"
                    : "External engine (not connected)",
                ),
              ],
            ),
          ]),
          game.player == "random"
            ? m("div.field", [
                m("span.label", "Clock"),
                m("p.hint", "Moves instantly, no clock needed."),
              ])
            : m("div.field", [
                m("span.label", engine ? "Thinks by" : "Clock"),
                m(
                  "select",
                  {
                    onchange: (e) => {
                      game.mode = e.target.value;
                    },
                    title: engine
                      ? "Change engine move control here."
                      : "Change time control here.",
                  },
                  modeOptions.map(([value, text, title]) =>
                    m(
                      "option",
                      {
                        value,
                        selected: game.mode == value,
                        title: title,
                      },
                      text,
                    ),
                  ),
                ),
              ]),
        ]),
        limitRow
          ? m(
              `div.${use_integer_inputs ? "integer-inputs" : "sliders"}.timecontrol`,
              [limitRow],
            )
          : null,
        isClockMode(game.mode) ? timeSliders(side, game.mode, tc) : null,
      ]);
    };
    const bothEngines =
      isEnginePlayer(game_white.player) && isEnginePlayer(game_black.player);
    const anyFsf = game_white.player == "fsf" || game_black.player == "fsf";
    const newGameDialog = m(
      "div.backdrop",
      {
        hidden: !newgame_open,
        onclick: (e) => {
          if (e.target === e.currentTarget) {
            newgame_open = false;
          }
        },
      },
      m("div.dialog.card", [
        m("div.dialoghead", [
          m("h2", "New game"),
          m(
            "button.iconbtn.ghost",
            {
              type: "button",
              title: "Close",
              onclick: () => {
                newgame_open = false;
              },
            },
            icon("x"),
          ),
        ]),
        m(
          "label.toggle",
          {
            title:
              "On: the game continues from the position currently shown on the board, keeping the moves played so far. Off: the game starts from the initial position of the current game (the variant's or the chosen start position).",
          },
          [
            m("input[type=checkbox]", {
              checked: game_continue,
              onclick: (e) => {
                game_continue = e.target.checked;
              },
            }),
            m("span", "Continue from the current position"),
          ],
        ),
        m(
          "p.hint",
          game_continue
            ? "The game continues from the position on the board."
            : "The game starts from the initial position; the moves on the board are cleared. Choose the variant and start position in the top bar.",
        ),
        sideSetup(
          "white",
          playerColor(mover_color_scheme, "white") + " (First mover)",
          game_white,
          tc_white,
        ),
        sideSetup(
          "black",
          playerColor(mover_color_scheme, "black") + " (Second mover)",
          game_black,
          tc_black,
        ),
        m("div.hr"),
        anyFsf
          ? m("div.sliders.timecontrol", [
              sliderRow(
                "Fairy-Stockfish Skill level",
                engine_skill,
                -20,
                20,
                engine_skill,
                (value) => {
                  engine_skill = value;
                },
                "Playing strength of Fairy-Stockfish (-20 = weakest, 20 = full strength).",
              ),
            ])
          : null,
        bothEngines
          ? m("div.nums.two", [
              m("div.field", [
                m("span.label", "Number of games (engine match)"),
                m("input[type=number]", {
                  min: 1,
                  value: game_games,
                  oninput: (e) => {
                    game_games = Math.max(1, parseInt(e.target.value) || 1);
                  },
                }),
              ]),
            ])
          : null,
        m("div.internals", [
          m("label#label-advtimectrl", [
            m("input[type=checkbox]#advtimectrl", {
              checked: advanced_time_control,
              disabled:
                app_mode != "play" ||
                review_mode ||
                board_setup_mode ||
                during_play ||
                during_engine_match,
              onclick: () => {
                advanced_time_control = !advanced_time_control;
                if (advanced_time_control && analysis_mode) {
                  // Timed games are exclusive with infinite analysis:
                  // stop the analysis and switch it off.
                  analysis_mode = false;
                  const analysischeckbox = document.getElementById("analysis");
                  if (analysischeckbox) {
                    analysischeckbox.checked = false;
                  }
                  force_stop();
                }
              },
            }),
            ,
          ]),
          m("div#advancedtimesettings", [
            m("div#whitetimesettings", [
              m("p", "White"),
              m(
                "select#dropdown-whitetimemode",
                {
                  disabled: !is_ready || review_mode,
                  title: "The time control mode for first mover (white).",
                  onchange: () => {
                    $("#whitetimetype").innerHTML = $(
                      "#dropdown-whitetimemode",
                    ).value;
                    white_timer_type = $("#dropdown-whitetimemode").value;
                  },
                },
                [
                  m(
                    "option",
                    {
                      value: "infinite",
                      title: "First mover has infinite time",
                    },
                    "Infinite",
                  ),
                  m(
                    "option",
                    {
                      value: "tournament",
                      title:
                        "First mover's time is limited and they can get time increment after every move.",
                    },
                    "Tournament",
                  ),
                  m(
                    "option",
                    {
                      value: "time per move",
                      title:
                        "First mover must make every move within a fixed time limit.",
                    },
                    "Time Per Move",
                  ),
                  m(
                    "option",
                    {
                      value: "hourglass",
                      title:
                        "First mover's time is limited and their used time on making a move will be added to second mover.",
                    },
                    "Hourglass",
                  ),
                  m(
                    "option",
                    {
                      value: "byoyomi",
                      title:
                        "(See [Why can I choose different time modes for two sides?] for more details on this mode)",
                    },
                    "Byo-yomi",
                  ),
                ],
              ),
              timeSliders("white", white_timer_type, tc_white),
              m("input[type=number]#whitestarttime", {
                hidden: true,
                value: use_integer_inputs
                  ? integer_input_white_start_time
                  : startTimeSteps[tc_white.start],
                min: 1,
              }),
              m("input[type=number]#whitetimegain", {
                hidden: true,
                value: use_integer_inputs
                  ? integer_input_white_time_increment
                  : incrementSteps[tc_white.gain],
                min: 0,
              }),
              m("input[type=number]#whitebyoyomitime", {
                hidden: true,
                value: use_integer_inputs
                  ? integer_input_white_byoyomi_period_length
                  : byoyomiSteps[tc_white.byoyomi],
                min: 1,
              }),
              m("input[type=number]#whitebyoyomiperiodcount", {
                hidden: true,
                value: use_integer_inputs
                  ? integer_input_white_byoyomi_periods
                  : tc_white.periods,
                min: 1,
              }),
              m("input[type=number]#whitetimemargin", {
                hidden: true,
                value: use_integer_inputs
                  ? integer_input_white_timeout_margin
                  : marginSteps[tc_white.margin],
                min: 0,
              }),
            ]),
            ,
            m("div#blacktimesettings", [
              m("p", "Black"),
              m(
                "select#dropdown-blacktimemode",
                {
                  disabled: !is_ready || review_mode,
                  title: "The time control mode for second mover (black).",
                  onchange: () => {
                    $("#blacktimetype").innerHTML = $(
                      "#dropdown-blacktimemode",
                    ).value;
                    black_timer_type = $("#dropdown-blacktimemode").value;
                  },
                },
                [
                  m(
                    "option",
                    {
                      value: "infinite",
                      title: "Second mover has infinite time",
                    },
                    "Infinite",
                  ),
                  m(
                    "option",
                    {
                      value: "tournament",
                      title:
                        "Second mover's time is limited and they can get time increment after every move.",
                    },
                    "Tournament",
                  ),
                  m(
                    "option",
                    {
                      value: "time per move",
                      title:
                        "Second mover must make every move within a fixed time limit.",
                    },
                    "Time Per Move",
                  ),
                  m(
                    "option",
                    {
                      value: "hourglass",
                      title:
                        "Second mover's time is limited and their used time on making a move will be added to first mover.",
                    },
                    "Hourglass",
                  ),
                  m(
                    "option",
                    {
                      value: "byoyomi",
                      title:
                        "(See [Why can I choose different time modes for two sides?] for more details on this mode)",
                    },
                    "Byo-yomi",
                  ),
                ],
              ),
              timeSliders("black", black_timer_type, tc_black),
              m("input[type=number]#blackstarttime", {
                hidden: true,
                value: use_integer_inputs
                  ? integer_input_black_start_time
                  : startTimeSteps[tc_black.start],
                min: 1,
              }),
              m("input[type=number]#blacktimegain", {
                hidden: true,
                value: use_integer_inputs
                  ? integer_input_black_time_increment
                  : incrementSteps[tc_black.gain],
                min: 0,
              }),
              m("input[type=number]#blackbyoyomitime", {
                hidden: true,
                value: use_integer_inputs
                  ? integer_input_black_byoyomi_period_length
                  : byoyomiSteps[tc_black.byoyomi],
                min: 1,
              }),
              m("input[type=number]#blackbyoyomiperiodcount", {
                hidden: true,
                value: use_integer_inputs
                  ? integer_input_black_byoyomi_periods
                  : tc_black.periods,
                min: 1,
              }),
              m("input[type=number]#blacktimemargin", {
                hidden: true,
                value: use_integer_inputs
                  ? integer_input_black_timeout_margin
                  : marginSteps[tc_black.margin],
                min: 0,
              }),
            ]),
            ,
            m("div#gamecontrol-start", [
              m(
                "p",
                {
                  onclick: () => {
                    alert(
                      'This time control system allows user select different time modes for two sides and gives user more choice on time odds settings.\nThe time modes are:\nInfinite: Selected side has infinite time.\nTournament: Selected side has limited time and may get a time increment after a move.\nTime per move: Selected side need to make each move within a fixed time limit.\nHourglass: Selected side has limited time and used time will be added to opponent\'s time.\nByo-yomi: Selected side will enter the countdown(byoyomi) period(s) after their initial time runs out. During countdown periods, if the player make a move before the countdown period time runs out, the time will be reset to full time of countdown periods(Specified in "Byoyomi period length"), otherwise the remaining period count will be decreased by 1 and the time will be reset to full time of countdown periods(Specified in "Byoyomi period length"). If there\'s no countdown periods (Specified in "Byoyomi period count") left and the remaining time runs out, this side runs out of time.\nNote: if you set engine\'s time mode to infinite, it will think forever!',
                    );
                  },
                },
                "Why can I choose different time modes for two sides?",
              ),
              m(
                "p",
                {
                  onclick: () => {
                    alert(
                      "Start time: The initial time (in milliseconds) at the beginning of the game. Not applicable to infinite.\nTime gain: Get a time increment of this many milliseconds after every move. Only applicable to tournament.\nByoyomi period length: The time (in milliseconds) of each period when in extra countdown(byoyomi) periods. Only applicable to byo-yomi.\nByoyomi period count: The count of countdown(byoyomi) periods. Only applicable to byo-yomi.\nTimeout margin: The time can be exceeded by this many milliseconds. The remaining time will be shown as minus numbers if exceeded. Not applicable to infinite.",
                    );
                  },
                },
                "What are these parameters?",
              ),
            ]),
            ,
          ]),
        ]),
        m("div.dialogfoot", [
          m(
            "button.ghost",
            {
              type: "button",
              onclick: () => {
                newgame_open = false;
              },
            },
            "Cancel",
          ),
          m(
            "button#gamestart.primary",
            {
              type: "button",
              hidden: true,
              disabled:
                !is_ready ||
                review_mode ||
                !advanced_time_control ||
                app_mode != "play",
              title: "Click to start a game in advanced timing system.",
              onclick: () => {
                newgame_open = false;
                goWithTimeControl();
              },
            },
            [icon("play", 16), "Start game"],
          ),
          ,
          m(
            "button.primary",
            {
              type: "button",
              disabled:
                !is_ready ||
                review_mode ||
                board_setup_mode ||
                during_engine_match,
              title: "Start the game with these settings.",
              onclick: () => {
                startGame();
              },
            },
            [icon("play", 16), "Start game"],
          ),
        ]),
      ]),
    );

    // ---------------- variant picker ----------------
    const variantList = (() => {
      const query = variant_search.trim().toLowerCase();
      const items = [];
      allvariants.forEach((id) => {
        // Only the latest draft of a variant of the editor is listed.
        if (
          ini_drafts.has(id) &&
          ini_latest_draft.get(ini_drafts.get(id)) != id &&
          id != currentVariantId()
        ) {
          return;
        }
        const type = getVariantType(id);
        if (variant_filter == FAVORITES_FILTER) {
          if (!favorite_variants.has(id)) {
            return;
          }
        } else if (variant_filter != "" && type != variant_filter) {
          return;
        }
        const name = getVariantName(id, true, false) || id;
        const description = getVariantDescription(id, false) || "";
        let score = 0;
        if (query != "") {
          const lowername = name.toLowerCase();
          if (lowername.startsWith(query)) {
            score = 0;
          } else if (lowername.includes(query)) {
            score = 1;
          } else if (id.toLowerCase().includes(query)) {
            score = 2;
          } else if (description.toLowerCase().includes(query)) {
            score = 3;
          } else {
            return;
          }
        }
        items.push({ id, name, type, description, score });
      });
      // Pseudo variants (named by piece symbols) are listed last.
      const last = (item) => (item.type == PSEUDO_VARIANTS ? 1 : 0);
      items.sort(
        (a, b) =>
          last(a) - last(b) ||
          a.score - b.score ||
          a.name.localeCompare(b.name),
      );
      return items;
    })();
    // Own categories first, the remaining ones last.
    const variantTypesForFilter = (() => {
      const first = [MY_VARIANTS_TYPE];
      const last = [PSEUDO_VARIANTS, NOT_CLASSIFIED, NOT_SUPPORTED];
      const present = varianttypes.slice();
      if (allvariants.some((id) => getVariantType(id) == NOT_CLASSIFIED)) {
        present.push(NOT_CLASSIFIED);
      }
      return first
        .filter((type) => present.includes(type))
        .concat(
          present.filter(
            (type) => !first.includes(type) && !last.includes(type),
          ),
          last.filter((type) => present.includes(type)),
        );
    })();
    const variantPicker = m(
      "div.backdrop",
      {
        hidden: !variant_picker_open,
        onclick: (e) => {
          if (e.target === e.currentTarget) {
            variant_picker_open = false;
          }
        },
      },
      m("div.dialog.card.picker", [
        m("div.dialoghead", [
          m("h2", "Variant"),
          m(
            "button.sm.ghost",
            {
              type: "button",
              title:
                "Define your own variant in the variants.ini format and try it out",
              onclick: () => {
                variant_picker_open = false;
                active_tab = "variant";
                // On narrow screens the panel is below the board.
                window.setTimeout(() => {
                  const tab = document.getElementById("tab-variant");
                  if (
                    tab &&
                    tab.getBoundingClientRect().top > window.innerHeight / 2
                  ) {
                    tab.scrollIntoView({ block: "start" });
                  }
                }, 50);
              },
            },
            [icon("code", 14), "Define variant"],
          ),
          m(
            "button.iconbtn.ghost",
            {
              type: "button",
              title: "Close",
              onclick: () => {
                variant_picker_open = false;
              },
            },
            icon("x"),
          ),
        ]),
        m("input[type=search]#variantsearch", {
          placeholder: "Search variants…",
          value: variant_search,
          oninput: (e) => {
            variant_search = e.target.value;
          },
          onkeydown: (e) => {
            if (e.key == "Enter" && variantList.length > 0) {
              selectVariant(variantList[0].id);
            } else if (e.key == "Escape") {
              variant_picker_open = false;
            }
          },
        }),
        m("div.chips", [
          m(
            "button.chip",
            {
              type: "button",
              class: variant_filter == "" ? "on" : "",
              onclick: () => {
                variant_filter = "";
              },
            },
            "All",
          ),
          m(
            "button.chip",
            {
              type: "button",
              class: variant_filter == FAVORITES_FILTER ? "on" : "",
              onclick: () => {
                variant_filter = FAVORITES_FILTER;
              },
            },
            [icon("star", 12), "Favorites"],
          ),
          variantTypesForFilter.map((type) =>
            m(
              "button.chip",
              {
                type: "button",
                class: variant_filter == type ? "on" : "",
                onclick: () => {
                  variant_filter = type;
                },
              },
              variantTypeLabel(type),
            ),
          ),
        ]),
        m("div.pickerlist", [
          variantList.length == 0
            ? m(
                "p.hint",
                variant_filter == FAVORITES_FILTER &&
                  variant_search.trim() == ""
                  ? "No favorites yet. Mark variants with the star to find them here."
                  : "No variant matches.",
              )
            : variantList.map((item) =>
                m("div.pickitem", { key: item.id }, [
                  m(
                    "button.pickrow",
                    {
                      type: "button",
                      class:
                        item.id == currentVariantId() ||
                        (currentVariantId() == "" && item.id == "chess")
                          ? "on"
                          : "",
                      title: getVariantDescription(item.id, true),
                      onclick: () => {
                        selectVariant(item.id);
                      },
                    },
                    [
                      m("span.rowhead", [
                        m("span.name", item.name),
                        m("span.id.mono", item.id),
                        m("span.pill", variantTypeLabel(item.type)),
                      ]),
                      item.description
                        ? m("span.desc", item.description)
                        : null,
                    ],
                  ),
                  m(
                    "button.iconbtn.ghost.favbtn",
                    {
                      type: "button",
                      class: favorite_variants.has(item.id) ? "on" : "",
                      title: favorite_variants.has(item.id)
                        ? "Remove from favorites"
                        : "Add to favorites",
                      "aria-pressed": favorite_variants.has(item.id)
                        ? "true"
                        : "false",
                      onclick: () => {
                        toggleFavorite(item.id);
                      },
                    },
                    icon("star", 16),
                  ),
                ]),
              ),
        ]),
      ]),
    );

    // ---------------- position picker ----------------
    const positionGroups = (() => {
      const directory = positionVariantsFor(currentVariantId());
      const groups = [];
      if (directory) {
        directory.forEach((names, type) => {
          const entries = [];
          names.forEach((game, name) => {
            entries.push({ name, description: game.Description || "" });
          });
          groups.push({ type, entries });
        });
      }
      return groups;
    })();
    const positionPicker = m(
      "div.backdrop",
      {
        hidden: !position_picker_open,
        onclick: (e) => {
          if (e.target === e.currentTarget) {
            position_picker_open = false;
          }
        },
      },
      m("div.dialog.card.picker", [
        m("div.dialoghead", [
          m("h2", "Start position"),
          m(
            "button.iconbtn.ghost",
            {
              type: "button",
              title: "Close",
              onclick: () => {
                position_picker_open = false;
              },
            },
            icon("x"),
          ),
        ]),
        m("div.pickerlist", [
          m(
            "button.pickrow",
            {
              type: "button",
              onclick: () => {
                selectPosition("(default)", "");
              },
            },
            [m("span.rowhead", [m("span.name", "Default start position")])],
          ),
          positionGroups.map((group) => [
            m("span.sect.groupsect", group.type),
            group.entries.map((entry) =>
              m(
                "button.pickrow",
                {
                  type: "button",
                  key: group.type + "/" + entry.name,
                  onclick: () => {
                    selectPosition(group.type, entry.name);
                  },
                },
                [
                  m("span.rowhead", [m("span.name", entry.name)]),
                  entry.description ? m("span.desc", entry.description) : null,
                ],
              ),
            ),
          ]),
        ]),
      ]),
    );

    // ---------------- settings drawer ----------------
    const settingsDrawer = m("div.settings-ui", { hidden: !settings_open }, [
      m("div.drawerbackdrop", {
        onclick: () => {
          settings_open = false;
        },
      }),
      m("aside.drawer.card", [
        m("div.dialoghead", [
          m("h2", "Settings"),
          m(
            "button.iconbtn.ghost",
            {
              type: "button",
              title: "Close",
              onclick: () => {
                settings_open = false;
              },
            },
            icon("x"),
          ),
        ]),
        m("div#controls.stack", [
          m("span.sect", "Appearance"),
          m("div", [
            m("div.setting", [
              m("span", "Pieces"),
              m("div.withbtn", [
                m(
                  "select#dropdown-piecetheme.sm",
                  {
                    onchange: () => {
                      changePieceSet(
                        $("#dropdown-piecetheme")[
                          $("#dropdown-piecetheme").selectedIndex
                        ].value,
                        true,
                      );
                    },
                  },
                  [
                    m("option", { value: "default" }, "Default Pieces"),
                    m(
                      "option",
                      { value: "userdefined" },
                      getThemeName("userdefined"),
                    ),
                  ],
                ),
                m(
                  "button.sm.iconbtn",
                  {
                    type: "button",
                    title: "Next piece set",
                    onclick: () => {
                      const dropdown = document.getElementById(
                        "dropdown-piecetheme",
                      );
                      changePieceSet(
                        dropdown[(dropdown.selectedIndex + 1) % dropdown.length]
                          .value,
                        true,
                      );
                    },
                  },
                  icon("swap", 14),
                ),
              ]),
            ]),
            m("div.setting", [
              m("span", "Board"),
              m("div.withbtn", [
                m(
                  "select#dropdown-boardtheme.sm",
                  {
                    onchange: () => {
                      changeBoardSet(
                        $("#dropdown-boardtheme")[
                          $("#dropdown-boardtheme").selectedIndex
                        ].value,
                        true,
                      );
                    },
                  },
                  [m("option", { value: "defaultboard" }, "Default Board")],
                ),
                m(
                  "button.sm.iconbtn",
                  {
                    type: "button",
                    title: "Next board",
                    onclick: () => {
                      const dropdown = document.getElementById(
                        "dropdown-boardtheme",
                      );
                      changeBoardSet(
                        dropdown[(dropdown.selectedIndex + 1) % dropdown.length]
                          .value,
                        true,
                      );
                    },
                  },
                  icon("swap", 14),
                ),
              ]),
            ]),
            m("div.setting", [
              m("span", "UI theme"),
              m("div.withbtn", [
                m(
                  "select#dropdown-uitheme.sm",
                  {
                    onchange: () => {
                      changeUI(
                        $("#dropdown-uitheme")[
                          $("#dropdown-uitheme").selectedIndex
                        ].value,
                        true,
                        true,
                      );
                    },
                  },
                  [m("option", { value: "defaultui" }, "Default UI")],
                ),
                m(
                  "button.sm.iconbtn",
                  {
                    type: "button",
                    title: "Next UI theme",
                    onclick: () => {
                      let time = Date.now();
                      if (time - previouschangeuitime < 750) {
                        return;
                      }
                      previouschangeuitime = time;
                      const uithemesdropdown =
                        document.getElementById("dropdown-uitheme");
                      changeUI(
                        uithemesdropdown[
                          (uithemesdropdown.selectedIndex + 1) %
                            uithemesdropdown.length
                        ].value,
                        true,
                        true,
                      );
                    },
                  },
                  icon("swap", 14),
                ),
              ]),
            ]),
          ]),
          m("div", [
            m("div.setting", [
              m("span", "Move notation"),
              m(
                "select#sannotation.sm",
                {
                  title:
                    "Select the move notation system that is used in move history and engine principal variations.\nPlayer colors will also change based on the notation. (Chess, Janggi, Shogi and Xiangqi have different player colors)",
                  onchange: () => {
                    const dropdownnotation =
                      document.getElementById("sannotation");
                    const evalbar = document.getElementById("evalbar");
                    const value =
                      dropdownnotation[dropdownnotation.selectedIndex].value;
                    evalbar.classList.remove("xiangqi");
                    evalbar.classList.remove("shogi");
                    evalbar.classList.remove("janggi");
                    if (/xiangqi|ucci/i.test(value)) {
                      evalbar.classList.add("xiangqi");
                      mover_color_scheme = "xiangqi";
                    } else if (/shogi|usi/i.test(value)) {
                      evalbar.classList.add("shogi");
                      mover_color_scheme = "shogi";
                    } else if (/janggi/i.test(value)) {
                      evalbar.classList.add("janggi");
                      mover_color_scheme = "janggi";
                    } else {
                      mover_color_scheme = "chess";
                    }
                    localStorage.setItem(
                      "SanNotation",
                      dropdownnotation.selectedIndex,
                    );
                  },
                },
                [
                  m("option", { value: "" }, "--Select Notation System--"),
                  m(
                    "option",
                    { value: "DEFAULT" },
                    "Standard/Short Algebraic Notation Without Piece Type Omission (DEFAULT)",
                  ),
                  m(
                    "option",
                    { value: "SAN" },
                    "Standard/Short Algebraic Notation (SAN)",
                  ),
                  m(
                    "option",
                    { value: "LAN" },
                    "Long Algebraic Notation (LAN)",
                  ),
                  m(
                    "option",
                    { value: "SHOGI_HOSKING" },
                    "Shogi Hosking Notation (SHOGI_HOSKING)",
                  ),
                  m(
                    "option",
                    { value: "SHOGI_HODGES" },
                    "Shogi George Hodges Notation (SHOGI_HODGES)",
                  ),
                  m(
                    "option",
                    { value: "SHOGI_HODGES_NUMBER" },
                    "Shogi George Hodges Number-only Notation (SHOGI_HODGES_NUMBER)",
                  ),
                  m("option", { value: "JANGGI" }, "Janggi Notation (JANGGI)"),
                  m(
                    "option",
                    { value: "XIANGQI_WXF" },
                    "World Xiangqi Federation Notation (XIANGQI_WXF)",
                  ),
                  m(
                    "option",
                    { value: "THAI_SAN" },
                    "Thai Standard/Short Algebraic Notation (THAI_SAN)",
                  ),
                  m(
                    "option",
                    { value: "THAI_LAN" },
                    "Thai Long Algebraic Notation (THAI_LAN)",
                  ),
                  m(
                    "option",
                    { value: "FEN" },
                    "Forsyth–Edwards Notation (Fairy-Stockfish) (FEN)",
                  ),
                  m("option", { value: "PGN" }, "Portable Game Notation (PGN)"),
                  m(
                    "option",
                    { value: "EPD" },
                    "Extended Position Description (EPD)",
                  ),
                  m(
                    "option",
                    { value: "FEN+UCIMOVE" },
                    "Forsyth–Edwards Notation (Fairy-Stockfish) and UCI Moves (FEN+UCIMOVE)",
                  ),
                  m(
                    "option",
                    { value: "FEN+USIMOVE" },
                    "Forsyth–Edwards Notation (Fairy-Stockfish) and USI Moves (FEN+USIMOVE)",
                  ),
                  m(
                    "option",
                    { value: "FEN+UCCIMOVE" },
                    "Forsyth–Edwards Notation (Fairy-Stockfish) and UCCI (CECP) Moves (FEN+UCCIMOVE)",
                  ),
                  m(
                    "option",
                    { value: "SFEN+USIMOVE" },
                    "Shogi Forsyth–Edwards Notation and USI Moves (SFEN+USIMOVE)",
                  ),
                ],
              ),
            ]),
            m("div.setting", [
              m("span", "Coordinates"),
              m(
                "select#boardcoordinate.sm",
                {
                  title: "Choose the coordinate system for the chess board.",
                  onchange: () => {
                    localStorage.setItem(
                      "BoardCoordinate",
                      document.getElementById("boardcoordinate").selectedIndex,
                    );
                  },
                },
                [
                  m(
                    "option",
                    {
                      value: "ALGEBRAIC",
                      title:
                        "English letters on bottom, Arabic numbers on side.",
                    },
                    "Chess Letter-Algebraic (ALGEBRAIC)",
                  ),
                  m(
                    "option",
                    {
                      value: "SHOGI_ENGLET",
                      title: "Arabic numbers on top, English letters on side.",
                    },
                    "Shogi Algebraic-Letter (SHOGI_ENGLET)",
                  ),
                  m(
                    "option",
                    {
                      value: "SHOGI_ARBNUM",
                      title: "Arabic numbers on top and side.",
                    },
                    "Shogi Algebraic (SHOGI_ARBNUM)",
                  ),
                  m(
                    "option",
                    {
                      value: "SHOGI_HANNUM",
                      title: "Arabic numbers on top, Kanji numbers on side.",
                    },
                    "Shogi Algebraic-Kanji (SHOGI_HANNUM)",
                  ),
                  m(
                    "option",
                    {
                      value: "JANGGI",
                      title:
                        "Arabic numbers on bottom and side, with 0 denoting 10th rank.",
                    },
                    "Janggi Algebraic (JANGGI)",
                  ),
                  m(
                    "option",
                    {
                      value: "XIANGQI_ARBNUM",
                      title: "Arabic numbers on top and bottom.",
                    },
                    "Xiangqi Algebraic (XIANGQI_ARBNUM)",
                  ),
                  m(
                    "option",
                    {
                      value: "XIANGQI_HANNUM",
                      title: "Arabic numbers on top, Hanzi numbers on bottom.",
                    },
                    "Xiangqi Algebraic-Hanzi (XIANGQI_HANNUM)",
                  ),
                  m(
                    "option",
                    {
                      value: "THAI_ALGEBRAIC",
                      title: "Thai letters on bottom, Thai numbers on side.",
                    },
                    "Makruk Thai Letter-Thai Algebraic (THAI_ALGEBRAIC)",
                  ),
                ],
              ),
            ]),
            m(
              "div.setting",
              {
                title:
                  "When checked, the board coordinates are shown inside of the board. Otherwise they are outside of the board.",
              },
              [
                m(
                  "span",

                  "Inner board coordinates",
                ),
                m("input[type=checkbox]#check-innercoordinate", {
                  disabled: !is_ready,
                  onclick: () => {
                    if (
                      document.getElementById("check-innercoordinate").checked
                    ) {
                      document
                        .getElementById("chessground-container-div")
                        .classList.add("inner");
                    } else {
                      document
                        .getElementById("chessground-container-div")
                        .classList.remove("inner");
                    }
                    localStorage.setItem(
                      "InnerCoordinate",
                      document.getElementById("check-innercoordinate").checked,
                    );
                  },
                }),
              ],
            ),
            m(
              "div.setting",
              {
                title:
                  "When checked, the legal moves of the selected piece are shown on the board.",
              },
              [
                m(
                  "span",

                  "Show legal moves & drops",
                ),
                m("input[type=checkbox]#check-dests", {
                  checked: show_dests,
                  onclick: () => {
                    show_dests = !show_dests;
                    localStorage.setItem("ShowDestinations", show_dests);
                  },
                }),
              ],
            ),
            m(
              "div.setting",
              {
                title: "(Legacy) When checked, show the game result in PGN.",
              },
              [
                m(
                  "span",

                  "Adjudicate (show result in PGN)",
                ),
                m("input[type=checkbox]#check-adjudicate", {
                  checked: adjudicate,
                  onclick: () => {
                    adjudicate = !adjudicate;
                    localStorage.setItem("ShowAdjudication", adjudicate);
                  },
                }),
              ],
            ),
            m(
              "div.setting",
              {
                title:
                  'When checked, engine analysis parameters and timer settings in "New Game" will use integer input boxes instead of sliders for better granularity.',
              },
              [
                m(
                  "span",

                  "Integer input for engine / timer parameters",
                ),
                m("input[type=checkbox]#check-granularity", {
                  checked: use_integer_inputs,
                  onclick: () => {
                    use_integer_inputs = !use_integer_inputs;
                    localStorage.setItem("UseIntegerInput", use_integer_inputs);
                  },
                }),
              ],
            ),
            m(
              "div.setting",
              {
                title:
                  "When checked, contents in move list panel are clickable instead of being plain text, and a mini board is shown which displays the position at that time when you click the move in the move list (PV line or move history). Meanwhile the PGN editing tools are shown in the Moves tab. Note that enabling this mode might make the page become slower.",
              },
              [
                m(
                  "span",

                  "Move visualization & PGN tools",
                ),
                m("input[type=checkbox]#isadvpgnmode", {
                  checked: advanced_pgn_mode,
                  disabled: !is_ready,
                  onclick: () => {
                    advanced_pgn_mode = !advanced_pgn_mode;
                    localStorage.setItem("AdvancedPGNMode", advanced_pgn_mode);
                  },
                }),
              ],
            ),
            m("div.setting", { hidden: !advanced_pgn_mode }, [
              m("span", "PGN Display style"),
              m(
                "select#pgnstyle.sm",
                {
                  title: "Choose the display style of move list panel.",
                  onchange: () => {
                    localStorage.setItem(
                      "PGNStyle",
                      document.getElementById("pgnstyle").selectedIndex,
                    );
                  },
                },
                [
                  m(
                    "option",
                    {
                      value: "flat",
                      title:
                        "The layout is the same as plain text: From left to right, change line if no space left.",
                    },
                    "Flat",
                  ),
                  m(
                    "option",
                    {
                      value: "grid",
                      title:
                        "Main line moves are put into grid layout, while variations moves are still flat. Lichess.org style.",
                    },
                    "Grid",
                  ),
                  m(
                    "option",
                    {
                      value: "grid-half",
                      title:
                        "Variation moves are put into identation blocks, and brackets are removed. Half move per line, and move numbers are half move numbers. Lishogi.org style.",
                    },
                    "Grid (Half moves)",
                  ),
                  m(
                    "option",
                    {
                      value: "tree-flat",
                      title:
                        "Variation moves are put into identation blocks, and brackets are removed. ChessBase.com style.",
                    },
                    "Flat (Tree)",
                  ),
                  m(
                    "option",
                    {
                      value: "tree-grid",
                      title:
                        "Variation moves are also in grid layouts, and are put into identation blocks. Brackets are removed.",
                    },
                    "Grid (Tree)",
                  ),
                  m(
                    "option",
                    {
                      value: "tree-grid-half",
                      title:
                        "Variation moves are also in grid layouts, and are put into identation blocks. Brackets are removed. Half move per line, and move numbers are half move numbers.",
                    },
                    "Grid (Half moves, Tree)",
                  ),
                ],
              ),
            ]),
            m(
              "div.setting",
              {
                title:
                  "If you cannot make your move on the board, you can open this dialog to make the move.",
              },
              [
                m(
                  "span",

                  "Show moves dialog",
                ),
                m("input[type=checkbox]#showmovediv", {
                  checked: select_move_dialog,
                  disabled: review_mode || board_setup_mode,
                  onclick: () => {
                    select_move_dialog = !select_move_dialog;
                    localStorage.setItem("ShowMovesDialog", select_move_dialog);
                  },
                }),
              ],
            ),
            m(
              "div.setting",
              {
                title:
                  "When checked, display evaluation history graph under move list panel.",
              },
              [
                m(
                  "span",

                  "Show evaluation history graph",
                ),
                m("input[type=checkbox]#showevalgraph", {
                  checked: show_evaluation_history_graph,
                  onclick: () => {
                    show_evaluation_history_graph =
                      !show_evaluation_history_graph;
                    if (show_evaluation_history_graph) {
                      setTimeout(DrawEvaluationHistoryGraph, 100);
                    }
                    localStorage.setItem(
                      "ShowEvaluationHistoryGraph",
                      show_evaluation_history_graph,
                    );
                  },
                }),
              ],
            ),
            m("div.setting", [
              m("span", "Sound volume"),
              m(
                "input[type=range]#range-volume",
                {
                  min: 0,
                  max: 1,
                  step: 0.05,
                  title: "Adjust sound volume here.",
                  onchange: () => {
                    localStorage.setItem(
                      "SoundVolume",
                      document.getElementById("range-volume").value,
                    );
                  },
                },
                "range",
              ),
            ]),
          ]),
        ]),

        m("div.stack", [
          m("div#input3.subsection", { hidden: during_play }, [
            m("span.sect", "Game options"),
            m(
              "div.setting",
              {
                title:
                  "When checked, enable fischer random (chess960) mode, which enables fischer random castling rules. This has no effect to variants that do not have castling.",
              },
              [
                m("span", "Fischer random start position"),
                m("input[type=checkbox]#isfischerrandommode", {
                  checked: fischer_random_mode,
                  disabled:
                    !is_ready ||
                    during_engine_match ||
                    during_play ||
                    review_mode ||
                    board_setup_mode,
                  onclick: () => {
                    fischer_random_mode = !fischer_random_mode;
                    document
                      .getElementById("dropdown-variant")
                      .dispatchEvent(new Event("change"));
                  },
                }),
              ],
            ),
          ]),
          ,
          m("span.sect", "Board options"),
          m("div#gamesettings", [
            m("div.field", [
              m("span.label", "Move input mode"),
              m(
                "select#moveinput",
                {
                  disabled: review_mode,
                  title:
                    "How pieces are moved: by dragging, by clicking the piece and then the target square, or either.",
                  onchange: (e) => {
                    move_input = e.target.value;
                    const clickbox = document.getElementById("clickclickmove");
                    const dragbox = document.getElementById("dragmove");
                    clickbox.checked = move_input != "drag";
                    dragbox.checked = move_input != "click";
                    clickbox.dispatchEvent(new Event("change"));
                    dragbox.dispatchEvent(new Event("change"));
                  },
                },
                [
                  m(
                    "option",
                    {
                      value: "either",
                      selected: move_input == "either",
                    },
                    "Either",
                  ),
                  m(
                    "option",
                    { value: "click", selected: move_input == "click" },
                    "Click two squares",
                  ),
                  m(
                    "option",
                    { value: "drag", selected: move_input == "drag" },
                    "Drag",
                  ),
                ],
              ),
              m("input[type=checkbox]#clickclickmove", {
                hidden: true,
                checked: move_input != "drag",
              }),
              m("input[type=checkbox]#dragmove", {
                hidden: true,
                checked: move_input != "click",
              }),
            ]),
            m("div.field", [
              m("span.label", "Quick promote / demote"),
              m(
                "select#dropdown-quickpromotion",
                {
                  disabled: !is_ready || review_mode || board_setup_mode,
                  title:
                    "Select an option to make the promotion or demotion automatically if available.",
                },
                [
                  m("option", { value: "" }, "<DISABLED>"),
                  m("option", { value: "a" }, "To piece a"),
                  m("option", { value: "b" }, "To piece b"),
                  m("option", { value: "c" }, "To piece c"),
                  m("option", { value: "d" }, "To piece d"),
                  m("option", { value: "e" }, "To piece e"),
                  m("option", { value: "f" }, "To piece f"),
                  m("option", { value: "g" }, "To piece g"),
                  m("option", { value: "h" }, "To piece h"),
                  m("option", { value: "i" }, "To piece i"),
                  m("option", { value: "j" }, "To piece j"),
                  m("option", { value: "k" }, "To piece k"),
                  m("option", { value: "l" }, "To piece l"),
                  m("option", { value: "m" }, "To piece m"),
                  m("option", { value: "n" }, "To piece n"),
                  m("option", { value: "o" }, "To piece o"),
                  m("option", { value: "p" }, "To piece p"),
                  m("option", { value: "q" }, "To piece q"),
                  m("option", { value: "r" }, "To piece r"),
                  m("option", { value: "s" }, "To piece s"),
                  m("option", { value: "t" }, "To piece t"),
                  m("option", { value: "u" }, "To piece u"),
                  m("option", { value: "v" }, "To piece v"),
                  m("option", { value: "w" }, "To piece w"),
                  m("option", { value: "x" }, "To piece x"),
                  m("option", { value: "y" }, "To piece y"),
                  m("option", { value: "z" }, "To piece z"),
                  m("option", { value: "+" }, "Promote (+)"),
                  m("option", { value: "-" }, "Demote (-)"),
                  m("option", { value: "=" }, "Keep (=)"),
                ],
              ),
            ]),
            m("p.hint.fullrow", [
              m(
                "span.help",
                {
                  onclick: () =>
                    window.alert(
                      "A null move is considered as a move that have the same original square and destination square. Double click a square (No matter whether it's empty or not) will make a null move on that square.\nNote:\n1. In most cases passing a turn is equivalent to making a null move on the king.\n2. In Atlantis variant, placing a wall without moving any piece requires to make a null move on the most bottom then the most left piece of your color.\n3. Click <show moves dialog> to see all legal moves if you are not sure how to make a move.",
                    ),
                },
                "How to make null moves?",
              ),
            ]),
          ]),
          m("div#visualeffects", [
            m("div.field", [
              m("span.label", "Visual effect"),
              m(
                "select#dropdown-visualeffect",
                {
                  disabled: !is_ready || board_setup_mode,
                  title:
                    "A visual effect is a change on the visibility of the board. Usually it's restricting piece visibility.",
                },
                [
                  m(
                    "option",
                    {
                      value: "<DISABLED>",
                      title: "No visual effect. The board is shown as is.",
                    },
                    "<DISABLED>",
                  ),
                  m(
                    "option",
                    {
                      value: "fogofwar",
                      title:
                        "Fog of war is a visual effect that can prevent a player from seeing unreachable squares except wall squares.",
                    },
                    "Fog Of War",
                  ),
                  m(
                    "option",
                    {
                      value: "wargame",
                      title:
                        "War game is a visual effect that can prevent a player from seeing opponent's pieces",
                    },
                    "War Game",
                  ),
                ],
              ),
            ]),
            m("div.field", [
              m("span.label", "Effect Perspective"),
              m(
                "select#dropdown-visualeffectperspective",
                {
                  disabled: !is_ready || board_setup_mode,
                  title: "Choose the perspective of visual effect.",
                },
                [
                  m(
                    "option",
                    {
                      value: "white",
                      title: "See the board at white's perspective.",
                    },
                    "White's View",
                  ),
                  m(
                    "option",
                    {
                      value: "black",
                      title: "See the board at black's perspective.",
                    },
                    "Black's View",
                  ),
                  m(
                    "option",
                    {
                      value: "alternate",
                      title: "See the board at current mover's perspective.",
                    },
                    "View Alternately",
                  ),
                ],
              ),
            ]),
          ]),
          ,
        ]),
        m("div.hr"),
        m("div#pageheader"),
        m("div#misc", { hidden: during_play }, [
          m("span.sect", "Custom data files"),
          m("div", { hidden: during_play }, [
            m("span.filename", [
              "variants.ini ",
              helpButton(
                "You can upload a Fairy-Stockfish compatible variants.ini file. See here for details: https://github.com/fairy-stockfish/Fairy-Stockfish/wiki/Variant-configuration.",
              ),
            ]),
            m("input#variants-ini", {
              type: "file",
              disabled: !is_ready || review_mode || board_setup_mode,
              onchange: onSelectVariantsFile,
            }),
          ]),
          m("div", { hidden: during_play }, [
            m("span.filename", [
              "positionvariants.txt ",
              helpButton(
                "You can select a Position Variant file to load different positions for different variants. Contents will be appended to the position variants provided by the server.",
              ),
            ]),
            m("input#posvariant-txt", {
              type: "file",
              disabled: !is_ready || review_mode || board_setup_mode,
            }),
          ]),
          m("div", { hidden: during_play }, [
            m("span.filename", [
              "User piece graphics ",
              helpButton(
                "You can upload user defined piece graphics. They must be named as follows [piece colour][+][piece letter].svg.",
              ),
            ]),
            m("input#user-graphics", {
              type: "file",
              multiple: true,
              disabled: !is_ready || review_mode || board_setup_mode,
              onchange: onSelectUserGraphics,
            }),
          ]),
          m("div", { hidden: during_play }, [
            m("span.filename", [
              "variantsettings.txt ",
              helpButton(
                "You can upload a Variant Settings file to load settings for the variants including classification, names and descriptions. Contents will be appended to the variant descriptions provided by the server.",
              ),
            ]),
            m("input#variantsettings-txt", {
              type: "file",
              disabled: !is_ready || review_mode || board_setup_mode,
              onchange: onSelectVariantSettings,
            }),
          ]),
        ]),
        m("div.hr"),
        m("div.stack", [
          m("span.sect", "App"),
          m("div.setting", [
            m("span", "Install fairyground as an app"),
            m(
              "button#installapp.sm.soft",
              {
                type: "button",
                hidden: !window.fairygroundInstallPrompt,
                onclick: () => {
                  const prompt = window.fairygroundInstallPrompt;
                  if (prompt) {
                    prompt.prompt();
                    prompt.userChoice.finally(() => {
                      window.fairygroundInstallPrompt = null;
                    });
                  }
                },
              },
              [icon("install", 14), "Install"],
            ),
            m(
              "span.hint",
              { hidden: !!window.fairygroundInstallPrompt },
              'Use your browser\'s "Install app" or "Add to home screen" option.',
            ),
          ]),
        ]),
      ]),
    ]);

    return m("main.app", { class: "mode-" + app_mode }, [
      topbar,
      m("div.layout", [boardcol, panel]),
      m("p#pagetitle", { hidden: true }, "Advanced analysis"),
      newGameDialog,
      variantPicker,
      positionPicker,
      settingsDrawer,
      m("div#moveselectiondialog", { hidden: !select_move_dialog }, [
        m("div#moveslectdiv", [
          m("p", "Moves"),
          m(
            "select#availablemovelist.sm",
            { title: "Select search result here." },
            [m("option", { value: "" }, "--SELECT MOVE--")],
          ),
          m("input[type=text]#movesearchfilter", {
            placeholder: "Search UCI move...",
            maxlength: 9999,
            title:
              "Input the UCI move string or part of it that you want to search.",
          }),
          m(
            "label#label-regexp1.toggle",
            { title: "Use regular expression to match moves." },
            [
              m("input[type=checkbox]#regexp1.box", {
                disabled: review_mode || board_setup_mode,
              }),
              m("span", "Regular Expression"),
            ],
          ),
          m(
            "button#searchmove.sm",
            {
              type: "button",
              title: "Click to search moves with search filters.",
            },
            "Search Moves",
          ),
        ]),
        m("div#movefilters", [
          m("p#searchresultinfo", "Click <Search Moves> to search!"),
          m("hr#separatorsearchresult"),
          m(
            "p",
            "Note: Click <Search Moves> to find available moves with filter. Leave the search field blank to find all moves. Click <Make Move> to make selected move. Click <Highlight Move> to show the move on the board. If you are in analysis mode, the highlighted move can be replaced by recommended move (Blue) and threat move (Red) and you need to highlight it again.",
          ),
          m(
            "p",
            "Check <Regular Expression> to search with regular expression, e.g. /[a-z]+/g",
          ),
          m("hr#separatormoveselectiondialog"),
          m("span.label", "Additional Search Restrictions"),
          m("input[type=text]#origfilter", {
            placeholder:
              "Original Square... (e.g. e2, leave empty to search all, useless for drops)",
            maxlength: 9999,
          }),
          m("input[type=text]#destfilter", {
            placeholder:
              "Destination Square... (e.g. e4, leave empty to search all, effective on drops)",
            maxlength: 9999,
          }),
          m("label#label-isdrop.toggle", [
            m("input[type=checkbox]#isdrop.box", {
              disabled: review_mode || board_setup_mode,
              checked: true,
            }),
            m("span", "Include drops"),
          ]),
          m("label#label-haswallgating.toggle", [
            m("input[type=checkbox]#haswallgating.box", {
              disabled: review_mode || board_setup_mode,
              checked: true,
            }),
            m("span", "Include moves having wall gating"),
          ]),
          m("label#label-haspiecechange.toggle", [
            m("input[type=checkbox]#haspiecechange.box", {
              disabled: review_mode || board_setup_mode,
              checked: true,
            }),
            m(
              "span",
              "Include moves having promotion/demotion or seirawan gating",
            ),
          ]),
          m("div.row", [
            m(
              "button#makemove.sm.primary",
              {
                type: "button",
                title: "Make the selected move on the board.",
              },
              "Make Move",
            ),
            m(
              "button#highlightmove.sm",
              {
                type: "button",
                title:
                  "Highlight the selected move on the board using yellow markers.",
              },
              "Highlight Move (Yellow Marks)",
            ),
            m(
              "button#closemovedialog.sm",
              {
                type: "button",
                title: "Close move selection dialog.",
                onclick: () => {
                  document.getElementById("showmovediv").click();
                },
              },
              "Close",
            ),
          ]),
        ]),
      ]),
      m("div#chessground-mini", [
        m("div#chessground-mini-board-operation-div", [
          m(
            "button#lockminiboard.operationdivbutton",
            {
              type: "button",
              title:
                "Status: Unlocked\nWhen locked, the mini board will not be closed if somewhere else is clicked.",
              onclick: () => {
                const chessgroundmini =
                  document.getElementById("chessground-mini");
                if (chessgroundmini.locked) {
                  chessgroundmini.locked = false;
                  chessgroundmini.classList.remove("locked");
                  document.getElementById("lockminiboard").title =
                    "Status: Unlocked\nWhen locked, the mini board will not be closed if somewhere else is clicked.";
                } else {
                  chessgroundmini.locked = true;
                  chessgroundmini.classList.add("locked");
                  document.getElementById("lockminiboard").title =
                    "Status: Locked\nWhen locked, the mini board will not be closed if somewhere else is clicked.";
                }
              },
            },
            "",
          ),
          m(
            "button#pinminiboard.operationdivbutton",
            {
              type: "button",
              title:
                "Status: Placed On Document\nWhen placed on document, the mini board will move with the webpage when you scroll.\nWhen pinned to window, the mini board will not move when you scroll.",
              onclick: () => {
                const maindiv = document.getElementsByTagName("main")[0];
                const chessgroundmini =
                  document.getElementById("chessground-mini");
                const maindivrect = maindiv.getBoundingClientRect();
                const chessgroundminirect =
                  chessgroundmini.getBoundingClientRect();
                const chessgroundminiboardwrapper = document.getElementById(
                  "chessground-mini-board-wrapper-div",
                );
                if (chessgroundmini.pinned) {
                  chessgroundmini.pinned = false;
                  chessgroundmini.classList.remove("pinned");
                  document.getElementById("pinminiboard").title =
                    "Status: Placed On Document\nWhen placed on document, the mini board will move with the webpage when you scroll.\nWhen pinned to window, the mini board will not move when you scroll.";
                  chessgroundmini.style.left = `${chessgroundminirect.left - maindivrect.left}px`;
                  chessgroundmini.style.top = `${chessgroundminirect.top - maindivrect.top}px`;
                  chessgroundmini.style.position = "";
                } else {
                  chessgroundmini.pinned = true;
                  chessgroundmini.classList.add("pinned");
                  document.getElementById("pinminiboard").title =
                    "Status: Pinned To Window\nWhen placed on document, the mini board will move with the webpage when you scroll.\nWhen pinned to window, the mini board will not move when you scroll.";
                  chessgroundmini.style.left = `${chessgroundminirect.left}px`;
                  chessgroundmini.style.top = `${chessgroundminirect.top}px`;
                  chessgroundmini.style.position = "fixed";
                }
              },
            },
            "",
          ),
          m(
            "button#setpositiontomainboard.operationdivbutton",
            {
              type: "button",
              title:
                "Click to move the position on mini board to main board for further investigation.",
              disabled: during_play || during_engine_match || game_started,
              onclick: () => {
                if (during_play || during_engine_match || game_started) {
                  return;
                }
                const chessgroundmini =
                  document.getElementById("chessground-mini");
                const fen = document.getElementById("fen");
                const move = document.getElementById("move");
                if (chessgroundmini.startingfen == undefined) {
                  fen.value = "";
                } else {
                  fen.value = chessgroundmini.startingfen;
                }
                if (chessgroundmini.moves == undefined) {
                  move.value = "";
                } else {
                  move.value = chessgroundmini.moves;
                }
                document.getElementById("setpos").click();
              },
            },
            "",
          ),
          m(
            "button#closeminiboard.operationdivbutton",
            {
              type: "button",
              title: "Click to close mini board.",
              onclick: () => {
                document.getElementById("chessground-mini").style.display =
                  "none";
              },
            },
            "",
          ),
        ]),
        m("div#chessground-mini-board-wrapper-div", [
          m(
            "div#chessground-mini-container-div.defaultboard.default.board8x8",
            [
              m("div.cg-wrap.pocket-top.movemode", [m("div#pocket-top-mini")]),
              m("div#chessground-board-mini.micro"),
              m("div.cg-wrap.pocket-bottom.movemode", [
                m("div#pocket-bottom-mini"),
              ]),
            ],
          ),
        ]),
      ]),
      m("div#boardsetuppieceidentifier", [
        m("div#fakeboard.defaultboard.default.board8x8", [
          m("div#fakewrap.cg-wrap.orientation-white", [m("piece#fakepiece")]),
        ]),
      ]),
      m("div#imagegenerator.hidden.popup", [
        m("p#imagegeneratortitle.title", "Board Image Generator"),
        m("div#filetypeselection", [
          m("p", "File type:"),
          m(
            "select#dropdown-filetype",
            {
              disabled: !is_ready,
              title:
                "Select image file type here. GIF format can save the whole game.",
              onchange: () => {
                const dropdown = document.getElementById("dropdown-filetype");
                document.getElementById("frameduration").disabled =
                  dropdown[dropdown.selectedIndex].value != "GIF";
                document.getElementById("imagequality").disabled =
                  dropdown[dropdown.selectedIndex].value == "PNG";
              },
            },
            [
              m(
                "option",
                { value: "PNG", title: "Save as PNG image." },
                "Portable Network Graphics (*.png)",
              ),
              m(
                "option",
                { value: "JPEG", title: "Save as JPEG image." },
                "Joint Photographic Experts Group (*.jpeg)",
              ),
              m(
                "option",
                {
                  value: "GIF",
                  title:
                    "Save as GIF image. When generating whole game, all positions will be included in one GIF file.",
                },
                "Graphics Interchange Format (*.gif)",
              ),
            ],
          ),
        ]),
        m("div#generationmode", [
          m("p", "Image generation mode:"),
          m(
            "select#dropdown-genmode",
            { title: "Select image generation mode here." },
            [
              m(
                "option",
                {
                  value: "current",
                  title: "Only generate image of displayed position.",
                },
                "Displayed Position",
              ),
              m(
                "option",
                {
                  value: "all",
                  title:
                    "Generate images of all positions from initial position to displayed position.\nGIF images will save all positions as frames in one file.\nPNG/JPEG images will be saved in a ZIP archive.",
                },
                "Whole Game",
              ),
            ],
          ),
        ]),
        m("div#imageresolution", [
          m("p", "Image resolution (pixels):"),
          m("input[type=number]#imagewidth", {
            min: 1,
            placeholder: "Width",
            title: "The image width in pixels.",
          }),
          m("p", "×"),
          m("input[type=number]#imageheight", {
            min: 1,
            placeholder: "Height",
            title: "The image height in pixels.",
          }),
          m(
            "label#label-keepaspectratio.toggle",
            {
              title:
                "When checked, the image will be generated with all squares keep 1:1 ratio according to image width. Image height is ignored in this case.",
            },
            [
              m("input[type=checkbox]#keepaspectratio.box", {
                onchange: () => {
                  document.getElementById("imageheight").disabled =
                    document.getElementById("keepaspectratio").checked;
                },
              }),
              m("span", "Keep aspect ratio"),
            ],
          ),
        ]),
        m("div#imagequalityselection", [
          m("p", "Image quality factor (JPEG & GIF):"),
          m("input[type=number]#imagequality", {
            min: 0,
            max: 1,
            step: 0.01,
            title:
              "Choose image quality factor. Higher means larger file size with better quality, taking longer time to generate and vice versa.\nMin: 0, Max: 1, Recommended value: 0.9.",
          }),
        ]),
        m("div#imageframedelayselection", [
          m("p", "Frame duration (milliseconds, GIF only):"),
          m("input[type=number]#frameduration", {
            min: 1,
            title:
              "Input the duration for each frame of GIF image. Each frame displays a move.",
          }),
        ]),
        m("div#additionalinformationselection", [
          m("p", "Additional information:"),
          m(
            "label.toggle",
            {
              title:
                "When checked, the generated image will contain side to move information and player names.",
            },
            [
              m("input[type=checkbox]#showplayerinformation.box"),
              m("span", "Show player information"),
            ],
          ),
        ]),
        m("div#imagegeneratoractions", [
          m(
            "button#exitimagegenerator.ghost",
            {
              type: "button",
              disabled: !is_ready,
              title: "Click to close image generator.",
            },
            "Close",
          ),
          m(
            "button#generateimage.primary",
            {
              type: "button",
              disabled: !is_ready,
              title: "Click to generate and download image or ZIP archive.",
            },
            "Generate Image",
          ),
        ]),
        m("p#imagegenerationprogress", "Ready."),
      ]),
      m("div#pgnheader.hidden.popup", [
        m("p#pgnheadertitle.title", "PGN Headers"),
        m("div#pgneventinput", [
          m("p", "Event:"),
          m("input[type=text]#pgnevent"),
        ]),
        m("div#pgnsiteinput", [m("p", "Site:"), m("input[type=text]#pgnsite")]),
        m("div#pgnroundinput", [
          m("p", "Round:"),
          m("input[type=number]#pgnround", {
            min: 1,
            step: 1,
          }),
        ]),
        m("div#pgndateinput", [m("p", "Date:"), m("input[type=date]#pgndate")]),
        m("div#pgnwhitenameinput", [
          m("p", "First player name:"),
          m("input[type=text]#pgnwhitename"),
        ]),
        m("div#pgnblacknameinput", [
          m("p", "Second player name:"),
          m("input[type=text]#pgnblackname"),
        ]),
        m("div#pgnheadercontrol", [
          m("button#pgnheadercancel.ghost", { type: "button" }, "Cancel"),
          m("button#pgnheadersave.primary", { type: "button" }, "Save"),
        ]),
      ]),
      m("div#terminationsettings", [
        m("p", "Set termination on current move:"),
        m("div#pgnresultinput", [
          m("p", "Result:"),
          m("select#pgnresult.sm", [
            m("option", { value: "1-0" }, "1-0"),
            m("option", { value: "0-1" }, "0-1"),
            m("option", { value: "1/2-1/2" }, "1/2-1/2"),
            m("option", { value: "*" }, "*"),
          ]),
        ]),
        m("div#pgnterminationinput", [
          m("p", "Termination:"),
          m("select#pgntermination.sm", [
            m("option", { value: "undefined" }, "(Not set)"),
            m("option", { value: "abandon" }, "Game abandoned"),
            m("option", { value: "adjudication" }, "Ended by adjudication"),
            m("option", { value: "death" }, "Player death"),
            m("option", { value: "emergency" }, "Emergency condition happened"),
            m("option", { value: "normal" }, "Player resigned or agreed draw"),
            m("option", { value: "rules infraction" }, "Rules infraction"),
            m("option", { value: "time forfeit" }, "Player run out of time"),
            m("option", { value: "unterminated" }, "Ongoing, not terminated"),
            m(
              "option",
              { value: "unknown", hidden: true },
              "Reason not specified",
            ),
            m(
              "option",
              { value: "normal", hidden: true },
              "Ended by game rule",
            ),
          ]),
        ]),
        m("button#terminationset.sm.primary", { type: "button" }, "Set"),
      ]),
      m("div#pgnsymbols.hidden.popup", [
        m("p#pgnsymbolstitle.title", "Symbols"),
        m("div#movecommentarysymbols", [
          m("p", "Move commentary symbols:"),
          m("select#movecommentarysymbolsselect", [
            m("option", { value: "" }, "(Not set)"),
            m("option", { value: "!" }, "[!] - Good move"),
            m("option", { value: "?" }, "[?] - Bad move (Mistake)"),
            m("option", { value: "!!" }, "[!!] - Brilliant move"),
            m("option", { value: "??" }, "[??] - Disastrous move (Blunder)"),
            m("option", { value: "!?" }, "[!?] - Interesting move"),
            m("option", { value: "?!" }, "[?!] - Dubious move (Inaccuracy)"),
            m("option", { value: "□" }, "[□] - Forced move"),
            m("option", { value: "⨀" }, "[⨀] - Zugzwang"),
          ]),
        ]),
        m("div#positioncommentarysymbols", [
          m("p", "Position commentary symbols:"),
          m("select#positioncommentarysymbolsselect", [
            m("option", { value: "" }, "(Not set)"),
            m("option", { value: "=" }, "[=] - This position is equal"),
            m("option", { value: "∞" }, "[∞] - This position is unclear"),
            m("option", { value: "⩲" }, "[⩲] - First mover is slightly better"),
            m(
              "option",
              { value: "⩱" },
              "[⩱] - Second mover is slightly better",
            ),
            m("option", { value: "±" }, "[±] - First mover is clearly better"),
            m("option", { value: "∓" }, "[∓] - Second mover is clearly better"),
            m("option", { value: "+-" }, "[+-] - First mover is winning"),
            m("option", { value: "-+" }, "[-+] - Second mover is winning"),
          ]),
        ]),
        m("p", "Status commentary symbols:"),
        m("div#statuscommentarysymbols", [
          m("label.toggle", [
            m("input[type=checkbox]#spaceadvantagesymbol.box"),
            m("span", "[○] - Space advantage"),
          ]),
          m("label.toggle", [
            m("input[type=checkbox]#developmentsymbol.box"),
            m("span", "[↑↑] - Development lead"),
          ]),
          m("label.toggle", [
            m("input[type=checkbox]#initiativesymbol.box"),
            m("span", "[↑] - With initiative"),
          ]),
          m("label.toggle", [
            m("input[type=checkbox]#attacksymbol.box"),
            m("span", "[→] - With an attack"),
          ]),
          m("label.toggle", [
            m("input[type=checkbox]#withcompensationsymbol.box"),
            m("span", "[=/∞] - With compensation for material deficit"),
          ]),
          m("label.toggle", [
            m("input[type=checkbox]#counterplaysymbol.box"),
            m("span", "[⇆] - Counterplay"),
          ]),
          m("label.toggle", [
            m("input[type=checkbox]#timetroublesymbol.box"),
            m("span", "[⨁] - Time trouble"),
          ]),
          m("label.toggle", [
            m("input[type=checkbox]#withtheideasymbol.box"),
            m("span", "[∆] - With the idea"),
          ]),
          m("label.toggle", [
            m("input[type=checkbox]#noveltysymbol.box"),
            m("span", "[N] - Novelty"),
          ]),
        ]),
        m("div#pgnsymbolscontrol", [
          m("button#pgnsymbolscancel.ghost", { type: "button" }, "Cancel"),
          m("button#pgnsymbolssave.primary", { type: "button" }, "Save"),
        ]),
      ]),
      m("div#pgntext.hidden.popup", [
        m("p#pgntexttitle.title", "Text"),
        m(
          "p.hint",
          'Note: Contents enclosed by square brackets, like "[%csl Ye4]", are special values used to represent additional information on this position, such as board markers, termination and evaluations. Deleting these will remove such information. Meanwhile, curly brackets ("{", "}") are not allowed in comments.',
        ),
        m("textarea#pgntextinput"),
        m("div#pgntextcontrol", [
          m("button#pgntextcancel.ghost", { type: "button" }, "Cancel"),
          m("button#pgntextsave.primary", { type: "button" }, "Save"),
        ]),
      ]),
      m("div#themedetectorcontainer"),
      m("div#tempbackground1.pagebackground"),
      m("div#tempbackground2.pagebackground.show"),
    ]);
  };

  return { oninit, view };
};

const support_condition = isSupported();
if (!support_condition.supported) {
  let query = new URLSearchParams();
  query.append("title", "Browser Not Supported");
  query.append(
    "text",
    "Your browser is not supported for the following reason(s):\n\n" +
      support_condition.error_messages.join("\n\n") +
      "\n\nRecommendations:\n1. Use up-to-date Chrome, Edge or Firefox browser to open this page.\n2. This webpage cannot be opened directly from file explorer. You need to set up a http server to access it.\n3. Make sure that you have set the following response headers on the http server:\nCross-Origin-Opener-Policy: same-origin\nCross-Origin-Embedder-Policy: require-corp",
  );
  let error_page_path = window.location.pathname;
  if (error_page_path.endsWith("/")) {
    error_page_path += "error.html";
  } else {
    error_page_path = error_page_path.replace("index.html", "");
    if (error_page_path.endsWith("/")) {
      error_page_path += "error.html";
    } else {
      error_page_path += "/error.html";
    }
  }
  window.location.replace(
    `${window.location.protocol}//${window.location.host}${error_page_path}?${query.toString()}`,
  );
} else {
  m.mount($("#root"), App);
}

// Contents previously in main.js

const divMain = document.getElementsByTagName("main")[0];
const variantsIni = document.getElementById("variants-ini");
const dropdownVariant = document.getElementById("dropdown-variant");
const buttonReset = document.getElementById("reset");
const buttonRestart = document.getElementById("restart");
const buttonFlip = document.getElementById("button-flip");
const buttonUndo = document.getElementById("undo");
const rangeVolume = document.getElementById("range-volume");
const checkboxDests = document.getElementById("check-dests");
const checkboxAdjudicate = document.getElementById("check-adjudicate");
const textFen = document.getElementById("fen");
const textMoves = document.getElementById("move");
const buttonSetFen = document.getElementById("setpos");
const buttonStop = document.getElementById("stop");
const pSetFen = document.getElementById("set");
const labelPgn = document.getElementById("label-pgn");
const labelStm = document.getElementById("label-stm");
const chessgroundContainerEl = document.getElementById(
  "chessground-container-div",
);
const chessgroundMiniContainerEl = document.getElementById(
  "chessground-mini-container-div",
);
const chessgroundMini = document.getElementById("chessground-mini");
const chessgroundMiniBoardWrapper = document.getElementById(
  "chessground-mini-board-wrapper-div",
);
const chessgroundMiniBoardOperations = document.getElementById(
  "chessground-mini-board-operation-div",
);
const chessgroundEl = document.getElementById("chessground-board");
const chessgroundMiniEl = document.getElementById("chessground-board-mini");
const pocketTopEl = document.getElementById("pocket-top");
const pocketTopMiniEl = document.getElementById("pocket-top-mini");
const pocketBottomEl = document.getElementById("pocket-bottom");
const pocketBottomMiniEl = document.getElementById("pocket-bottom-mini");
const imageGenerator = document.getElementById("imagegenerator");
const chessgroundThemeDetector = document.getElementById(
  "themedetectorcontainer",
);
const dropdownImageFileType = document.getElementById("dropdown-filetype");
const dropdownGenerationMode = document.getElementById("dropdown-genmode");
const inputImageWidth = document.getElementById("imagewidth");
const inputImageHeight = document.getElementById("imageheight");
const checkboxKeepAspectRatio = document.getElementById("keepaspectratio");
const inputImageQuality = document.getElementById("imagequality");
const inputFrameDuration = document.getElementById("frameduration");
const checkboxShowPlayerInformation = document.getElementById(
  "showplayerinformation",
);
const buttonGenerateImage = document.getElementById("generateimage");
const buttonExitImageGenerator = document.getElementById("exitimagegenerator");
const textImageGenerationProgress = document.getElementById(
  "imagegenerationprogress",
);
const pgnHeader = document.getElementById("pgnheader");
const inputPGNEvent = document.getElementById("pgnevent");
const inputPGNSite = document.getElementById("pgnsite");
const inputPGNRound = document.getElementById("pgnround");
const inputPGNDate = document.getElementById("pgndate");
const inputPGNWhiteName = document.getElementById("pgnwhitename");
const inputPGNBlackName = document.getElementById("pgnblackname");
const dropdownPGNResult = document.getElementById("pgnresult");
const dropdownPGNTermination = document.getElementById("pgntermination");
const buttonPGNHeaderSave = document.getElementById("pgnheadersave");
const buttonPGNHeaderCancel = document.getElementById("pgnheadercancel");
const terminationSettings = document.getElementById("terminationsettings");
const terminationSet = document.getElementById("terminationset");
const pgnSymbols = document.getElementById("pgnsymbols");
const dropdownMoveCommentarySymbols = document.getElementById(
  "movecommentarysymbolsselect",
);
const dropdownPositionCommentarySymbols = document.getElementById(
  "positioncommentarysymbolsselect",
);
const checkboxSpaceAdvantageSymbol = document.getElementById(
  "spaceadvantagesymbol",
);
const checkboxDevelopmentSymbol = document.getElementById("developmentsymbol");
const checkboxInitiativeSymbol = document.getElementById("initiativesymbol");
const checkboxAttackSymbol = document.getElementById("attacksymbol");
const checkboxWithCompensationSymbol = document.getElementById(
  "withcompensationsymbol",
);
const checkboxCounterplaySymbol = document.getElementById("counterplaysymbol");
const checkboxTimeTroubleSymbol = document.getElementById("timetroublesymbol");
const checkboxWithTheIdeaSymbol = document.getElementById("withtheideasymbol");
const checkboxNoveltySymbol = document.getElementById("noveltysymbol");
const buttonPgnSymbolsSave = document.getElementById("pgnsymbolssave");
const buttonPgnSymbolsCancel = document.getElementById("pgnsymbolscancel");
const pgnText = document.getElementById("pgntext");
const pgnTextTitle = document.getElementById("pgntexttitle");
const textareaPgnTextInput = document.getElementById("pgntextinput");
const buttonPgnTextSave = document.getElementById("pgntextsave");
const buttonPgnTextCancel = document.getElementById("pgntextcancel");
const buttonNextPosition = document.getElementById("nextposition");
const buttonPreviousPosition = document.getElementById("previousposition");
const buttonInitialPosition = document.getElementById("initialposition");
const buttonFinalPosition = document.getElementById("finalposition");
const buttonCurrentPosition = document.getElementById("currentposition");
const buttonSpecifiedPosition = document.getElementById("specifiedposition");
const inputHalfMoveNumber = document.getElementById("gotomovenum");
const isGameStarted = document.getElementById("isgamestarted");
const buttonGameStart = document.getElementById("gamestart");
const playWhite = document.getElementById("playwhite");
const playBlack = document.getElementById("playblack");
const randomMoverWhite = document.getElementById("randommoverwhite");
const randomMoverBlack = document.getElementById("randommoverblack");
const currentBoardFen = document.getElementById("currentboardfen");
const gameResult = document.getElementById("gameresult");
const gameStatus = document.getElementById("gamestatus");
const whiteTime = document.getElementById("whitetime");
const blackTime = document.getElementById("blacktime");
const timeOutSide = document.getElementById("timeoutside");
const loadThemes = document.getElementById("loadthemes");
const initializeThemes = document.getElementById("initializethemes");
const isBoardSetup = document.getElementById("isboardsetup");
const isAdvPGNMode = document.getElementById("isadvpgnmode");
const buttonMoveTreeClear = document.getElementById("movetree-clear");
const buttonMoveTreeClearComments = document.getElementById(
  "movetree-clearcomments",
);
const buttonMoveTreeHideShow = document.getElementById("movetree-hideshow");
const buttonMoveTreeRemoveVariations = document.getElementById(
  "movetree-removevariations",
);
const buttonMoveTreeSetToMainBranch = document.getElementById(
  "movetree-settomainbranch",
);
const buttonMoveTreeSetAsMainLine = document.getElementById(
  "movetree-setasmainline",
);
const buttonMoveTreeCutBranch = document.getElementById("movetree-cutbranch");
const buttonMoveTreeCropBranch = document.getElementById("movetree-cropbranch");
const buttonMoveTreeCut = document.getElementById("movetree-cut");
const buttonMoveTreeCrop = document.getElementById("movetree-crop");
const buttonMoveTreeUncomment = document.getElementById("movetree-uncomment");
const buttonMoveTreeTextBefore = document.getElementById("movetree-textbefore");
const buttonMoveTreeTextAfter = document.getElementById("movetree-textafter");
const buttonMoveTreeSymbol = document.getElementById("movetree-symbol");
const buttonMoveTreeMarkers = document.getElementById("movetree-markers");
const buttonMoveTreeTermination = document.getElementById(
  "movetree-termination",
);
const buttonMoveTreeUndo = document.getElementById("movetree-undo");
const buttonMoveTreeRedo = document.getElementById("movetree-redo");
const buttonMoveTreeHeaders = document.getElementById("movetree-headers");
const buttonMoveTreeBoardPreview = document.getElementById(
  "movetree-boardpreview",
);
const buttonMoveTreeSave = document.getElementById("movetree-save");
const buttonMoveTreeSaveImage = document.getElementById("movetree-imagesave");
const buttonMoveTreeResize = document.getElementById("movetree-resize");
const dropdownSetPiece = document.getElementById("dropdown-setpiece");
const buttonClearBoard = document.getElementById("clearboard");
const buttonInitialBoardPosition = document.getElementById("initboardpos");
const buttonAddToPocket = document.getElementById("addtopocket");
const buttonBoardSetupCopyFEN = document.getElementById("boardsetupcopyfen");
const buttonValidatePosition = document.getElementById("validatepos");
const dropdownSideToMove = document.getElementById("dropdown-sidetomove");
const whiteOO = document.getElementById("whitekingsidecastle");
const whiteOOO = document.getElementById("whitequeensidecastle");
const blackOO = document.getElementById("blackkingsidecastle");
const blackOOO = document.getElementById("blackqueensidecastle");
const halfMoveClock = document.getElementById("halfmoveclock");
const whiteRemainingChecks = document.getElementById("whiteremainingchecks");
const blackRemainingChecks = document.getElementById("blackremainingchecks");
const currentMoveNumber = document.getElementById("currentmovenum");
const enPassantFile = document.getElementById("enpassantfile");
const enPassantRank = document.getElementById("enpassantrank");
const seirawanGatingFiles = document.getElementById("seirwangatingfiles");
const copySetFEN = document.getElementById("copysetfen");
const dropdownPositionVariantType = document.getElementById(
  "dropdown-posvarianttype",
);
const dropdownPositionVariantName = document.getElementById(
  "dropdown-posvariantname",
);
const buttonAboutPosition = document.getElementById("aboutposition");
const positionInformation = document.getElementById("positioninfo");
const clickClickMove = document.getElementById("clickclickmove");
const dragMove = document.getElementById("dragmove");
const positionVariantTxt = document.getElementById("posvariant-txt");
const quickPromotionPiece = document.getElementById("dropdown-quickpromotion");
const buttonPassMove = document.getElementById("passmove");
const buttonPlaceWall = document.getElementById("placewall");
const dropdownVisualEffect = document.getElementById("dropdown-visualeffect");
const dropdownVisualEffectPerspective = document.getElementById(
  "dropdown-visualeffectperspective",
);
const engineOutput = document.getElementById("engineoutputline");
const setPgnString = document.getElementById("pgnstring");
const isAnalysis = document.getElementById("analysis");
const pcheckCounts = document.getElementById("checkcounts");
const evaluationBar = document.getElementById("evalbarprogress");
const evalscore = document.getElementById("cp");
const multipv = document.getElementById("multipv");
const evalcomment = document.getElementById("evalcomment");
const evalinfo = document.getElementById("evalinfo");
const pvinfo = document.getElementById("pvinfo");
const availablemovelist = document.getElementById("availablemovelist");
const movesearchfilter = document.getElementById("movesearchfilter");
const issearchregexp = document.getElementById("regexp1");
const buttonsearchmove = document.getElementById("searchmove");
const origfilter = document.getElementById("origfilter");
const destfilter = document.getElementById("destfilter");
const isdrop = document.getElementById("isdrop");
const haswallgating = document.getElementById("haswallgating");
const haspiecechange = document.getElementById("haspiecechange");
const buttonmakemove = document.getElementById("makemove");
const buttonhighlightmove = document.getElementById("highlightmove");
const searchresultinfo = document.getElementById("searchresultinfo");
const dropdownNotationSystem = document.getElementById("sannotation");
const pRandomMoverGo = document.getElementById("randommovergo");
const pBoardOrientation = document.getElementById("boardorientation");
const buttonSetEvaluation = document.getElementById("seteval");
const evalHistoryContainer = document.getElementById("evalhistorycontainer");
const checkboxShowEvalHistoryGraph = document.getElementById("showevalgraph");
const buttonAnalyzeNextMove = document.getElementById("analyze-nextmove");
const buttonAnalyzeRecommendedMove = document.getElementById(
  "analyze-recommended",
);
const divPgnContainer = document.getElementById("pgn-container");
const dropdownPGNStyle = document.getElementById("pgnstyle");
const dropdownBoardCoordinate = document.getElementById("boardcoordinate");
const checkboxFischerRandom = document.getElementById("isfischerrandommode");
const checkBoxInnerCoordinate = document.getElementById(
  "check-innercoordinate",
);
const soundMove = new Audio("assets/sound/thearst3rd/move.mp3");
const soundCapture = new Audio("assets/sound/thearst3rd/capture.mp3");
const soundCheck = new Audio("assets/sound/thearst3rd/check.mp3");
const soundTerminal = new Audio("assets/sound/thearst3rd/terminal.mp3");

// Compact number formatting for the engine statistics (1.2M, 850k).
function formatCount(value) {
  const n = parseInt(value);
  if (isNaN(n)) {
    return "?";
  }
  if (n >= 1000000000) {
    return `${(n / 1000000000).toFixed(1)}G`;
  }
  if (n >= 1000000) {
    return `${(n / 1000000).toFixed(1)}M`;
  }
  if (n >= 1000) {
    return `${(n / 1000).toFixed(0)}k`;
  }
  return String(n);
}

function formatSecondsShort(milliseconds) {
  const n = parseInt(milliseconds);
  if (isNaN(n)) {
    return "?";
  }
  return `${(n / 1000).toFixed(1)}s`;
}

class MultiplePrincipalVariationEntry {
  constructor(IsValid, HeaderString, Variant, Is960, FEN, UCIMoves) {
    if (
      typeof IsValid != "boolean" ||
      typeof HeaderString != "string" ||
      typeof Variant != "string" ||
      typeof Is960 != "boolean" ||
      typeof FEN != "string" ||
      typeof UCIMoves != "string"
    ) {
      throw TypeError();
    }
    this.IsValid = IsValid;
    this.HeaderString = HeaderString;
    this.Variant = Variant;
    this.Is960 = Is960;
    this.FEN = FEN;
    this.UCIMoves = UCIMoves;
  }

  destructor() {}
}

class MultiplePrincipalVariationMiniBoardHandler {
  constructor() {
    this.Element = document.createElement("div");
    this.Element.classList.add("multipv-miniboard-div");
    this.StoredPrincipalVariationCount = 0;
    this.ValidPrincipalVariationCount = 0;
    this.PrincipalVariationElementList = [];
    this.PrincipalVariationDataList = [
      new MultiplePrincipalVariationEntry(false, "", "", false, "", ""),
    ];
  }

  destructor() {}

  SetValidPrincipalVariationCount(PrincipalVariationCount) {
    if (typeof PrincipalVariationCount != "number") {
      throw TypeError(
        "SetValidPrincipalVariationCount(PrincipalVariationCount:number)",
      );
    }
    this.ValidPrincipalVariationCount = PrincipalVariationCount;
  }

  SetPrincipalVariation(
    PrincipalVariationNumber,
    VariantID,
    Is960,
    CurrentBoardFEN,
    UCIMoves,
    IsMate,
    EvaluationNumber,
    Depth,
    SelectiveDepth,
  ) {
    if (
      typeof PrincipalVariationNumber != "number" ||
      typeof VariantID != "string" ||
      typeof Is960 != "boolean" ||
      typeof CurrentBoardFEN != "string" ||
      typeof UCIMoves != "string" ||
      typeof IsMate != "boolean" ||
      typeof EvaluationNumber != "number" ||
      typeof Depth != "number" ||
      typeof SelectiveDepth != "number"
    ) {
      throw TypeError(
        "SetPrincipalVariation(PrincipalVariationNumber:number, VariantID:string, Is960:boolean, CurrentBoardFEN:string, UCIMoves:string, IsMate:boolean, EvaluationNumber:number, Depth:number, SelectiveDepth:number)",
      );
    }
    let i = 0;
    if (this.PrincipalVariationDataList.length < PrincipalVariationNumber) {
      for (
        i = this.PrincipalVariationDataList.length;
        i < PrincipalVariationNumber;
        i++
      ) {
        this.PrincipalVariationDataList.push(
          new MultiplePrincipalVariationEntry(false, "", "", false, "", ""),
        );
      }
      this.ValidPrincipalVariationCount = PrincipalVariationNumber;
    }
    let selected =
      this.PrincipalVariationDataList[PrincipalVariationNumber - 1];
    let evaluation = "";
    if (IsMate) {
      if (EvaluationNumber > 0) {
        evaluation = `#+${parseInt(EvaluationNumber)}`;
      } else {
        evaluation = `#${parseInt(EvaluationNumber)}`;
      }
    } else {
      if (EvaluationNumber > 0) {
        evaluation = `+${EvaluationNumber.toFixed(2)}`;
      } else {
        evaluation = `${EvaluationNumber.toFixed(2)}`;
      }
    }
    selected.IsValid = true;
    selected.HeaderString = `${PrincipalVariationNumber == 1 ? "" : "<hr />"}<evalnum>${evaluation}</evalnum><span class="pvmeta">d${Depth > -1 ? Depth : "?"}/${SelectiveDepth > -1 ? SelectiveDepth : "?"}</span> `;
    selected.Variant = VariantID;
    selected.Is960 = Is960;
    selected.FEN = CurrentBoardFEN;
    selected.UCIMoves = UCIMoves;
  }

  GetMovesDivElement() {
    if (
      this.PrincipalVariationDataList.length < this.ValidPrincipalVariationCount
    ) {
      throw Error("Missing PV.");
    }
    let i = 0;
    let deletelater = [];
    let movestack = gametree.GetMoveListOfMove(gametree.CurrentMove);
    let selecteddata,
      selected,
      moveselem,
      notationindex,
      existingmoveelem,
      textelem,
      lineelem;
    if (
      this.PrincipalVariationElementList.length <
      this.ValidPrincipalVariationCount
    ) {
      for (
        i = this.PrincipalVariationElementList.length;
        i < this.ValidPrincipalVariationCount;
        i++
      ) {
        lineelem = document.createElement("div");
        lineelem.classList.add("multipv-miniboard-pvline");
        textelem = document.createElement("p");
        textelem.classList.add("multipv-miniboard-pvline-header");
        lineelem.appendChild(textelem);
        this.PrincipalVariationElementList.push(lineelem);
      }
    }
    if (
      this.StoredPrincipalVariationCount < this.ValidPrincipalVariationCount
    ) {
      for (
        i = this.StoredPrincipalVariationCount;
        i < this.ValidPrincipalVariationCount;
        i++
      ) {
        this.Element.appendChild(this.PrincipalVariationElementList[i]);
      }
      this.StoredPrincipalVariationCount = this.ValidPrincipalVariationCount;
    } else if (
      this.StoredPrincipalVariationCount > this.ValidPrincipalVariationCount
    ) {
      for (
        i = this.ValidPrincipalVariationCount;
        i < this.StoredPrincipalVariationCount;
        i++
      ) {
        this.Element.removeChild(this.PrincipalVariationElementList[i]);
      }
      this.StoredPrincipalVariationCount = this.ValidPrincipalVariationCount;
    }
    for (i = 0; i < this.ValidPrincipalVariationCount; i++) {
      selecteddata = this.PrincipalVariationDataList[i];
      if (selecteddata.IsValid) {
        selecteddata.IsValid = false;
        selected = this.PrincipalVariationElementList[i];
        moveselem = null;
        notationindex = simplenotations.indexOf(
          dropdownNotationSystem[dropdownNotationSystem.selectedIndex].value,
        );
        selected.childNodes.item(0).innerHTML = selecteddata.HeaderString;
        existingmoveelem = selected.childNodes.item(1);
        if (notationindex < 0) {
          if (existingmoveelem) {
            existingmoveelem.innerHTML = "";
            existingmoveelem.innerText = getNotation(
              dropdownNotationSystem[dropdownNotationSystem.selectedIndex]
                .value,
              selecteddata.Variant,
              selecteddata.FEN,
              selecteddata.Is960,
              selecteddata.UCIMoves,
              false,
            );
          } else {
            moveselem = document.createElement("div");
            moveselem.classList.add("multipv-miniboard-pvline-moves");
            moveselem.innerText = getNotation(
              dropdownNotationSystem[dropdownNotationSystem.selectedIndex]
                .value,
              selecteddata.Variant,
              selecteddata.FEN,
              selecteddata.Is960,
              selecteddata.UCIMoves,
              false,
            );
            selected.appendChild(moveselem);
          }
        } else {
          if (existingmoveelem) {
            deletelater.push(selected.removeChild(existingmoveelem));
          }
          moveselem = parseUCIMovesToPreviewElements(
            selecteddata.Variant,
            selecteddata.FEN,
            selecteddata.Is960,
            selecteddata.UCIMoves,
            `movediv-${i}`,
            ffishnotationobjects[notationindex],
            gametree.OriginalFEN,
            movestack,
          );
          moveselem.classList.add("multipv-miniboard-pvline-moves");
          selected.appendChild(moveselem);
        }
      }
    }
    setTimeout(() => {
      let tmp = deletelater;
      deletelater = null;
    }, 500);
    return this.Element;
  }
}

let multipvminiboardhandler = new MultiplePrincipalVariationMiniBoardHandler();
let themedetector = new themeutil.ChessgroundThemeDetector(
  chessgroundThemeDetector,
);
let evalhistorygraph = new evalhistory.EvaluationHistoryGraph(
  evalHistoryContainer,
  (index) => {
    let moves = gametree
      .GetCompleteMainLineMoveListOfMove(gametree.CurrentMove)
      .split(" ");
    if (index >= 0 && index <= moves.length && !isGameStarted.checked) {
      textMoves.value = moves.slice(0, index).join(" ");
      buttonSetFen.click();
    }
  },
);

document.addEventListener("themechange", (event) => {
  if (event instanceof CustomEvent) {
    themedetector.SetThemes(event.detail.piece, event.detail.board);
    updatePGNDivision(false);
  }
});

document.addEventListener("gameend", (event) => {
  if (event instanceof CustomEvent) {
    if (event.detail.reason != "normal") {
      gametree.CurrentMove.Move.TextAfter =
        gametree.CurrentMove.Move.TextAfter.replace(/\[%end.*?\]/g, "");
      gametree.CurrentMove.Move.TextAfter += `[%end ${event.detail.result},${event.detail.reason}]`;
      updatePGNDivision(false);
    }
  }
});

// Spacebar to play current best engine move (analysis mode)
document.addEventListener("keydown", function (ev) {
  const tag =
    ev.target && ev.target.tagName ? ev.target.tagName.toLowerCase() : "";
  const isEditable =
    tag === "input" ||
    tag === "textarea" ||
    (ev.target && ev.target.isContentEditable === true);
  if (isEditable) return;
  if (ev.altKey || ev.ctrlKey || ev.metaKey) return;
  if (ev.repeat) return;

  if (
    (ev.code === "Space" || ev.key === " ") &&
    isAnalysis &&
    isAnalysis.checked
  ) {
    ev.preventDefault();
    if (gatingPending) return;
    if (spacebarDebounce) return;

    // Require a fresh PV for the current position
    const currentSig = `${textFen.value.trim()}|${textMoves.value.trim()}|${getColor(board)}`;
    if (
      !lastPVBestMove ||
      lastPVBestMove === "0000" ||
      lastPVPosSig !== currentSig ||
      Date.now() - lastPVTime > 4000
    ) {
      return;
    }

    spacebarDebounce = true;
    textMoves.value = (textMoves.value + " " + lastPVBestMove).trim();
    pSetFen.click();
    setTimeout(function () {
      spacebarDebounce = false;
    }, 300);
  }
});

for (i = 0; i < maxmultipvcount; i++) {
  //multipvrecord: Array<Struct<IsMate:boolean, EvaluationNumber:number, BestMove:string, PonderMove:string, PrincipalVariationUCIMove:string, Depth:number, SelectiveDepth:number>>
  multipvrecord.push([null, null, null, null, null, null, null]);
  evaluationindex.push(0);
}

document.dispatchEvent(new Event("onpageload"));

function getEvaluationDescription(eval_num, is_mate) {
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

function convertChessgroundXKeyToSquare(key) {
  const ranks = [
    "1",
    "2",
    "3",
    "4",
    "5",
    "6",
    "7",
    "8",
    "9",
    ":",
    ";",
    "<",
    "=",
    ">",
    "?",
    "@",
  ];
  const files = [
    "a",
    "b",
    "c",
    "d",
    "e",
    "f",
    "g",
    "h",
    "i",
    "j",
    "k",
    "l",
    "m",
    "n",
    "o",
    "p",
  ];
  return key.charAt(0) + (ranks.indexOf(key.charAt(1)) + 1).toString();
}

function DownloadFile(content, fileName, mimeType) {
  const blob = new Blob([content], { type: mimeType });
  const a = document.createElement("a");
  a.href = URL.createObjectURL(blob);
  a.download = fileName;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
}

function convertSquareToChessgroundXKey(square) {
  const ranks = [
    "1",
    "2",
    "3",
    "4",
    "5",
    "6",
    "7",
    "8",
    "9",
    ":",
    ";",
    "<",
    "=",
    ">",
    "?",
    "@",
  ];
  const files = [
    "a",
    "b",
    "c",
    "d",
    "e",
    "f",
    "g",
    "h",
    "i",
    "j",
    "k",
    "l",
    "m",
    "n",
    "o",
    "p",
  ];
  return square.charAt(0) + ranks[parseInt(square.substring(1)) - 1];
}

function getPieceRoles(pieceLetters) {
  const uniqueLetters = new Set(pieceLetters.toLowerCase().split(""));
  return [...uniqueLetters].map((char) => char + "-piece");
}

function getRepresentativePiece() {
  const startingfen = ffish.startingFen(board.variant());
  const uniqueletters = [...new Set(startingfen.split(""))].join("");
  let whitepiece = "";
  let blackpiece = "";
  let i = 0;
  if (uniqueletters.includes("K")) {
    whitepiece = "K";
  } else {
    for (i = 0; i < uniqueletters.length; i++) {
      if (
        uniqueletters.charCodeAt(i) >= 65 &&
        uniqueletters.charCodeAt(i) <= 90
      ) {
        whitepiece = uniqueletters[i];
        break;
      }
    }
  }
  if (uniqueletters.includes("k")) {
    blackpiece = "k";
  } else {
    for (i = 0; i < uniqueletters.length; i++) {
      if (
        uniqueletters.charCodeAt(i) >= 97 &&
        uniqueletters.charCodeAt(i) <= 122
      ) {
        blackpiece = uniqueletters[i];
        break;
      }
    }
  }
  return { white: whitepiece, black: blackpiece };
}

function generateMoveNotationSVG(text, backgroundcolor, textcolor, position) {
  if (
    typeof text != "string" ||
    typeof backgroundcolor != "string" ||
    typeof textcolor != "string" ||
    typeof position != "string"
  ) {
    return null;
  }
  if (position == "TopRight") {
    return `<svg xmlns='http://www.w3.org/2000/svg'version='1.1'width='100px'height='100px'><path style="fill:${backgroundcolor};stroke:none;stroke-width:0;stroke-linecap:round;stroke-linejoin:round;stroke-dasharray:none"d="m 100,2 a 20,20 0 0 0 -20,19.999999 20,20 0 0 0 20,20 z"/><g transform="scale(1.5)"><text style="fill:${textcolor}"font-size="15"font-family="Arial"font-weight="bold"x="60"y="15"text-anchor="middle"dominant-baseline="central">${text.replace("-", "━").replace("+", "✚")}</text></g></svg>`;
  } else if (position == "TopLeft") {
    return `<svg xmlns='http://www.w3.org/2000/svg'version='1.1'width='100px'height='100px'><path style="fill:${backgroundcolor};stroke:none;stroke-width:0;stroke-linecap:round;stroke-linejoin:round;stroke-dasharray:none"d="m 0,2 a 20,20 0 0 1 20,19.999999 20,20 0 0 1 -20,20 z"/><g transform="scale(1.5)"><text style="fill:${textcolor}"font-size="15"font-family="Arial"font-weight="bold"x="6"y="15"text-anchor="middle"dominant-baseline="central">${text.replace("-", "━").replace("+", "✚")}</text></g></svg>`;
  } else {
    return null;
  }
}

function generatePassTurnNotationSVG(backgroundcolor) {
  if (typeof backgroundcolor != "string") {
    return null;
  }
  let bgcolor = "#0078d7";
  if (backgroundcolor != "") {
    bgcolor = backgroundcolor;
  }
  return `<svg width="100"height="100"viewBox="0 0 26.458333 26.458333"version="1.1"xmlns="http://www.w3.org/2000/svg"xmlns:svg="http://www.w3.org/2000/svg"><g><ellipse style="fill:${bgcolor};stroke:#000000;stroke-width:1.05833333;stroke-linecap:square;stroke-dasharray:none;stroke-opacity:1;fill-opacity:1"id="background"cx="13.229165"cy="13.229164"rx="11.906248"ry="11.906247"/><path id="foreground"style="fill:#ffffff;fill-opacity:1;stroke:#ffffff;stroke-width:0;stroke-linecap:butt;stroke-linejoin:round;stroke-dasharray:none;stroke-dashoffset:0;stroke-opacity:1;image-rendering:auto"d="m 13.229166,3.9687505 -2.778125,2.7781249 2.778125,2.7781248 V 7.672917 a 5.5562497,5.5562497 0 0 1 5.55625,5.556251 5.5562497,5.5562497 0 0 1 -3.271893,5.06248 l 1.377486,1.377487 a 7.4083326,7.4083326 0 0 0 3.74649,-6.439967 7.4083326,7.4083326 0 0 0 -7.408333,-7.4083344 z m -3.6607575,2.821533 a 7.4083326,7.4083326 0 0 0 -3.7475747,6.4388845 7.4083326,7.4083326 0 0 0 7.4083322,7.408331 v 1.852084 l 2.778125,-2.778125 -2.778125,-2.778125 v 1.852083 A 5.5562497,5.5562497 0 0 1 7.672917,13.229168 5.5562497,5.5562497 0 0 1 10.945171,8.1670469 Z"/></g></svg>`;
}

function initBoard(variant) {
  if (board !== null) board.delete();
  board = new ffish.Board(
    variant,
    ffish.startingFen(variant),
    checkboxFischerRandom.checked,
  );
  console.log(
    "Variant:",
    board.variant(),
    "; Is fischer random: ",
    board.is960(),
  ); // Figuring out pocket roles from initial FEN

  const fenBoard = board.fen().split(" ")[0];
  var pocketRoles = undefined;
  resetTimer();
  clearMovesList();
  recordedmultipv = 1;
  if (fenBoard.includes("[")) {
    const wpocket = board.pocket(WHITE);
    const bpocket = board.pocket(BLACK); // Variants with empty hands at start (zh, shogi, etc.)

    if (ffish.capturesToHand(variant)) {
      const pieceLetters = fenBoard.replace(/[^A-Za-z]/g, "");
      const pieceRoles = getPieceRoles(pieceLetters);
      console.log(pieceRoles);
      pocketRoles = {
        white: pieceRoles,
        black: pieceRoles,
      }; // Variants having pieces in hand at start (placement, sittuyin, etc.)
    } else {
      pocketRoles = {
        white: getPieceRoles(wpocket),
        black: getPieceRoles(bpocket),
      };
    }
  }

  const config = {
    autoCastle: false,
    dimensions: getDimensions(board),
    fen: fenBoard,
    movable: {
      free: true,
      showDests: checkboxDests.checked,
      events: {
        after: afterChessgroundMove,
        afterNewPiece: afterChessgroundDrop,
      },
    },
    draggable: {
      enabled: dragMove.checked || isBoardSetup.checked,
      showGhost: true,
    },
    selectable: {
      enabled: clickClickMove.checked,
    },
    pocketRoles: pocketRoles,
    events: {
      select: onSelectSquare,
    },
    notation: dropdownBoardCoordinate.selectedIndex,
  };

  const configmini = {
    dimensions: getDimensions(board),
    fen: fenBoard,
    movable: {
      color: undefined,
      dests: EmptyMap,
    },
    premovable: {
      enabled: false,
    },
    draggable: {
      enabled: false,
    },
    selectable: {
      enabled: false,
    },
    drawable: {
      enabled: false,
    },
    pocketRoles: pocketRoles,
    viewOnly: true,
    notation: dropdownBoardCoordinate.selectedIndex,
  };
  chessground = Chessground(chessgroundEl, config, pocketTopEl, pocketBottomEl);
  chessground_mini = Chessground(
    chessgroundMiniEl,
    configmini,
    pocketTopMiniEl,
    pocketBottomMiniEl,
  );
  chessgroundMini.startingfen = undefined;
  chessgroundMini.moves = undefined;
  chessground.state.drawable.brushes.black = {
    key: "black",
    color: "#000000",
    opacity: 1,
    lineWidth: 10,
  };

  if (pocketRoles === undefined) {
    pocketTopEl.classList.add("no-inital-pocket-piece");
    pocketBottomEl.classList.add("no-inital-pocket-piece");
    pocketTopMiniEl.style.display = "none";
    pocketBottomMiniEl.style.display = "none";
  } else {
    pocketTopEl.classList.remove("no-inital-pocket-piece");
    pocketBottomEl.classList.remove("no-inital-pocket-piece");
  }

  pBoardOrientation.textContent = "white";
  pBoardOrientation.click();
}

function forceCoordinateRecalculation() {
  // Force a layout reflow to ensure chessground coordinates are properly mapped
  // This addresses the coordinate mapping issue that occurs after clicking "Start game"
  const container = chessgroundContainerEl;
  if (container) {
    // Force layout recalculation by accessing layout properties
    container.offsetHeight;
    container.getBoundingClientRect();

    // Trigger a small scroll to force coordinate recalculation
    // This mimics the user scroll/zoom that fixes the issue manually
    const currentScrollTop = window.pageYOffset;
    window.scrollTo(0, currentScrollTop + 1);
    window.scrollTo(0, currentScrollTop);
  }
}

function rerenderChessgroundPockets(falsefen) {
  let mainboard = chessgroundContainerEl.getElementsByTagName("cg-board")[0];
  let mainboardcontainer =
    chessgroundContainerEl.getElementsByTagName("cg-container")[0];
  let css_height = mainboardcontainer.style.height;
  let css_width = mainboardcontainer.style.width;
  let state = chessground.state;
  let pockettoplength = 0;
  let pocketbottomlength = 0;
  let dimensions = getDimensions(board);
  let elements = {
    board: mainboard,
    pocketTop: pocketTopEl,
    pocketBottom: pocketBottomEl,
    wrap: chessgroundEl,
    container: chessgroundContainerEl,
  };
  if (chessground.state.orientation == "white") {
    pocketbottomlength = chessground.state.pocketRoles.white.length;
    pockettoplength = chessground.state.pocketRoles.black.length;
  } else {
    pocketbottomlength = chessground.state.pocketRoles.black.length;
    pockettoplength = chessground.state.pocketRoles.white.length;
  }
  let pocketlength = Math.max(pockettoplength, pocketbottomlength);
  pocketTopEl.setAttribute(
    "style",
    `--pocketLength: ${pocketlength}; --files: ${dimensions.width}; --ranks: ${dimensions.height}; --cg-width: ${css_width}; --cg-height: ${css_height}`,
  );
  pocketBottomEl.setAttribute(
    "style",
    `--pocketLength: ${pocketlength}; --files: ${dimensions.width}; --ranks: ${dimensions.height}; --cg-width: ${css_width}; --cg-height: ${css_height}`,
  );
  pocketutil.renderPocketsInitial(state, elements, pocketTopEl, pocketBottomEl);
  pocketutil.renderPockets(state);
  pocketTopEl.setAttribute(
    "style",
    `--pocketLength: ${pocketlength}; --files: ${dimensions.width}; --ranks: ${dimensions.height}; --cg-width: ${css_width}; --cg-height: ${css_height}`,
  );
  pocketBottomEl.setAttribute(
    "style",
    `--pocketLength: ${pocketlength}; --files: ${dimensions.width}; --ranks: ${dimensions.height}; --cg-width: ${css_width}; --cg-height: ${css_height}`,
  );
  if (falsefen) {
    chessground.set({
      fen: falsefen,
    });
  }
}

function redrawChessground(customFEN) {
  closePromotionChoice();
  let fenBoard = "";
  if (customFEN) {
    fenBoard = customFEN;
    console.log("CustomFEN:", customFEN);
  } else {
    fenBoard = chessground.state.fen;
  }
  const config = {
    autoCastle: false,
    dimensions: getDimensions(board),
    orientation: chessground.state.orientation,
    fen: fenBoard,
    check: chessground.state.check,
    lastMove: chessground.state.lastMove,
    movable: {
      free: true,
      color: chessground.state.movable.color,
      dests: chessground.state.movable.dests,
      showDests: checkboxDests.checked,
      events: {
        after: afterChessgroundMove,
        afterNewPiece: afterChessgroundDrop,
      },
    },
    draggable: {
      enabled: dragMove.checked || isBoardSetup.checked,
      showGhost: true,
    },
    selectable: {
      enabled: clickClickMove.checked,
    },
    pocketRoles: chessground.state.pocketRoles,
    events: {
      select: onSelectSquare,
    },
    notation: dropdownBoardCoordinate.selectedIndex,
    turnColor: chessground.state.turnColor,
  };
  chessground = Chessground(chessgroundEl, config, pocketTopEl, pocketBottomEl);
  chessground.state.drawable.brushes.black = {
    key: "black",
    color: "#000000",
    opacity: 1,
    lineWidth: 10,
  };
  if (chessground.state.pocketRoles === undefined) {
    pocketTopEl.classList.add("no-inital-pocket-piece");
    pocketBottomEl.classList.add("no-inital-pocket-piece");
  } else {
    pocketTopEl.classList.remove("no-inital-pocket-piece");
    pocketBottomEl.classList.remove("no-inital-pocket-piece");
  }
  updateInnerCoordinateColor(chessground);
}

function updateInnerCoordinateColor(chessground) {
  const coordinateobj =
    chessground.state.dom.elements.container.getElementsByTagName("coords");
  let i, j;
  let elem, childs;
  for (i = 0; i < coordinateobj.length; i++) {
    elem = coordinateobj[i];
    if (elem instanceof HTMLElement) {
      childs = elem.childNodes;
      for (j = 0; j < childs.length; j++) {
        childs.item(j).classList.remove("light");
        childs.item(j).classList.remove("dark");
      }
    }
  }
  if (!checkBoxInnerCoordinate.checked) {
    return;
  }
  const size = getCurrentBoardSize();
  let classes, styles;
  let isblack = chessground.state.orientation == "black";
  //If the parity of rank number and the parity of file number are the same, it's a dark square. Otherwise it's a light square.
  for (i = 0; i < coordinateobj.length; i++) {
    elem = coordinateobj[i];
    if (elem instanceof HTMLElement) {
      classes = elem.classList;
      styles = window.getComputedStyle(elem);
      if (classes.contains("bottom")) {
        childs = elem.childNodes;
        let startsdark = false;
        if (styles.flexDirection == "row") {
          if (isblack) {
            //If the start square is a light square, the coordinate should start with dark color.
            if ((size.width & 1) != (size.height & 1)) {
              startsdark = true;
            }
          }
        } else if (styles.flexDirection == "row-reverse") {
          if (isblack) {
            if (1 != (size.height & 1)) {
              startsdark = true;
            }
          } else {
            if ((size.width & 1) != 1) {
              startsdark = true;
            }
          }
        }
        if (startsdark) {
          for (j = 0; j < size.width; j++) {
            if (j & 1) {
              childs.item(j).classList.add("light");
            } else {
              childs.item(j).classList.add("dark");
            }
          }
        } else {
          for (j = 0; j < size.width; j++) {
            if (j & 1) {
              childs.item(j).classList.add("dark");
            } else {
              childs.item(j).classList.add("light");
            }
          }
        }
      } else if (classes.contains("top")) {
        childs = elem.childNodes;
        let startsdark = false;
        if (styles.flexDirection == "row") {
          if (isblack) {
            if ((size.width & 1) != 1) {
              startsdark = true;
            }
          } else {
            if (1 != (size.height & 1)) {
              startsdark = true;
            }
          }
        } else if (styles.flexDirection == "row-reverse") {
          if (!isblack) {
            if ((size.width & 1) != (size.height & 1)) {
              startsdark = true;
            }
          }
        }
        if (startsdark) {
          for (j = 0; j < size.width; j++) {
            if (j & 1) {
              childs.item(j).classList.add("light");
            } else {
              childs.item(j).classList.add("dark");
            }
          }
        } else {
          for (j = 0; j < size.width; j++) {
            if (j & 1) {
              childs.item(j).classList.add("dark");
            } else {
              childs.item(j).classList.add("light");
            }
          }
        }
      } else if (classes.contains("side")) {
        childs = elem.childNodes;
        let startsdark = false;
        if (styles.flexDirection == "column") {
          if (!isblack) {
            if ((size.width & 1) != (size.height & 1)) {
              startsdark = true;
            }
          }
        } else if (styles.flexDirection == "column-reverse") {
          if (isblack) {
            if (1 != (size.height & 1)) {
              startsdark = true;
            }
          } else {
            if ((size.width & 1) != 1) {
              startsdark = true;
            }
          }
        }
        if (startsdark) {
          for (j = 0; j < size.height; j++) {
            if (j & 1) {
              childs.item(j).classList.add("light");
            } else {
              childs.item(j).classList.add("dark");
            }
          }
        } else {
          for (j = 0; j < size.height; j++) {
            if (j & 1) {
              childs.item(j).classList.add("dark");
            } else {
              childs.item(j).classList.add("light");
            }
          }
        }
      }
    }
  }
}

function onSelectSquare(key) {
  // Handle gating (e.g., duck move) selection by click
  if (gatingPending && gatingContext && typeof key === "string") {
    // If user clicked on a valid gating destination, finalize the move
    if (
      gatingContext.destToChoiceMap &&
      gatingContext.destToChoiceMap.has(key)
    ) {
      const gatingChoice = gatingContext.destToChoiceMap.get(key);
      let gating =
        gatingChoice === "=" || gatingChoice == null ? "" : "," + gatingChoice;
      let finalmove = gatingContext.baseMove + gatingContext.promotion + gating;
      if (!board.push(finalmove)) {
        const foundmove = board
          .legalMoves()
          .match(new RegExp(`${gatingContext.baseMove}[^ ]+`));
        if (foundmove) {
          finalmove = foundmove[0];
        } else {
          finalmove = null;
        }
      }
      const didCapture = gatingContext.capture === true;
      // Restore UI selection behavior
      chessground.unselect();
      chessground.set({
        selectable: {
          enabled:
            gatingContext.prevSelectableEnabled ?? clickClickMove.checked,
        },
        movable: { dests: EmptyMap },
      });
      chessground.setAutoShapes([]);
      gatingPending = false;
      gatingContext = null;
      afterMove(finalmove, didCapture);
      return;
    }
    // During gating, ignore other clicks
    return;
  }

  console.log("key:", key);
  console.log(chessground.state);
  if (isBoardSetup.checked) {
    let piece = { role: "", color: "" };
    let pieceid = "";
    console.log("pieceid selected: ", dropdownSetPiece.value);
    if (
      dropdownSetPiece.value == null ||
      dropdownSetPiece.value == "<delete>"
    ) {
      if (chessground.state.boardState.pieces.has(key)) {
        chessground.state.boardState.pieces.delete(key);
      }
    } else if (dropdownSetPiece.value == "<move>") {
    } else {
      pieceid = dropdownSetPiece.value;
      if (pieceid.charAt(0) == "+") {
        piece.role = "p";
        pieceid = pieceid.substring(1);
      }
      if (
        ("a" <= pieceid.charAt(0) && pieceid.charAt(0) <= "z") ||
        pieceid.charAt(0) == "*"
      ) {
        piece.color = "black";
      } else {
        piece.color = "white";
      }
      if (pieceid.charAt(0) == "*") {
        piece.role = "_-piece";
      } else {
        piece.role = piece.role + pieceid.charAt(0).toLowerCase() + "-piece";
      }
      console.log("final piece id:", piece.role);
      chessground.state.boardState.pieces.set(key, piece);
    }
    chessground.set({
      lastMove: undefined,
    });
    hasdoubleclicked = false;
  } else {
    if (
      Date.now() - previousclicktime < 1000 &&
      key == previousclicksquare &&
      !hasdoubleclicked
    ) {
      let square = convertChessgroundXKeyToSquare(key);
      afterChessgroundMove(square, square, {
        premove: false,
        ctrlKey: false,
        holdTime: 0,
        captured: {
          role: null,
          color: null,
          promoted: false,
        },
        predrop: false,
      });
      chessground.cancelMove();
      hasdoubleclicked = true;
    } else {
      hasdoubleclicked = false;
    }
    previousclicktime = Date.now();
    previousclicksquare = key;
  }
}

function getWallSquarePosition() {
  let FEN = board.fen().split(" ")[0];
  let ranks = FEN.split("/");
  let wall_square_list = [];
  let file = [];
  let i = 0;
  let j = 0;
  let current_file = 0;
  let tmp_num = 0;
  for (i = 0; i < ranks.length; i++) {
    file = ranks[i].split("");
    current_file = 0;
    tmp_num = 0;
    for (j = 0; j < file.length; j++) {
      if (/^[0-9]{1}$/.test(file[j])) {
        tmp_num = tmp_num * 10 + +parseInt(file[j]);
        continue;
      } else {
        current_file = +current_file + +tmp_num;
        tmp_num = 0;
      }
      if (file[j] == "*") {
        wall_square_list.push(`${files[current_file]}${ranks.length - i}`);
      }
      current_file++;
    }
  }
  console.log(wall_square_list);
  return wall_square_list;
}

function parseBoardMarkers(boardmarkers, movercolor) {
  let notes = boardmarkers.split(",");
  let i = 0;
  let color = "";
  let note = "";
  let moveturns = [];
  let moves = [];
  let colors = [];
  let notepositions = [];
  let moveturn = movercolor == "white";
  for (i = 0; i < notes.length; i++) {
    note = notes[i].trim();
    if (note == "") {
      continue;
    }
    if (note[0] == "Y") {
      color = "yellow";
    } else if (note[0] == "G") {
      color = "green";
    } else if (note[0] == "R") {
      color = "red";
    } else if (note[0] == "B") {
      color = "blue";
    } else {
      continue;
    }
    note = note.substring(1);
    moveturns.push(moveturn);
    colors.push(color);
    notepositions.push("TopRight");
    if (note.match(/[a-z][0-9]+/g).length == 1) {
      moves.push("@" + note);
    } else {
      moves.push(note);
    }
  }
  return {
    moves: moves,
    colors: colors,
    moveturns: moveturns,
    notepositions: notepositions,
  };
}

function onMoveElementClicked(info_struct, target) {
  chessground_mini.set({
    fen: info_struct.fenstr,
    orientation: chessground.state.orientation,
    turnColor: info_struct.moveturn,
    check: info_struct.checked,
    lastMove: info_struct.lastmove,
    notation: chessground.state.notation,
  });
  chessground_mini.setAutoShapes([]);
  if (info_struct.boardmarkers) {
    let parsedmarkers = parseBoardMarkers(
      info_struct.boardmarkers,
      info_struct.moveturn,
    );
    //The arrows can be drawed correctly only when the board is visible, so we have to wait for the browser rendering the board.
    window.setTimeout(() => {
      highlightMoveOnBoard(
        parsedmarkers.moveturns,
        chessground_mini,
        parsedmarkers.moves,
        parsedmarkers.colors,
        parsedmarkers.notepositions,
        true,
      );
    }, 100);
  }
  chessgroundMini.startingfen = info_struct.startingfen;
  chessgroundMini.moves = info_struct.moves;
  //console.log(info_struct.fenstr, info_struct.moveturn, info_struct.checked, info_struct.lastmove);
  if (chessgroundMini.style.display == "none") {
    const rect = target.getBoundingClientRect();
    const mainrect = divMain.getBoundingClientRect();
    let chessgroundminirect = chessgroundMini.getBoundingClientRect();
    while (chessgroundminirect.width == 0) {
      chessgroundMini.style.display = "";
      chessgroundminirect = chessgroundMini.getBoundingClientRect();
    }
    const padding = 10;
    let offsetX = 0;
    let offsetY = 0;
    if (chessgroundMini.pinned) {
      offsetX = rect.left;
      offsetY = rect.top;
    } else {
      offsetX = rect.left - mainrect.left;
      offsetY = rect.top - mainrect.top;
    }
    let finalX = offsetX;
    let finalY = offsetY + 40;
    if (chessgroundMini.pinned) {
      if (finalX + chessgroundminirect.width > window.innerWidth - padding) {
        finalX -= chessgroundminirect.width;
      }
      if (finalY + chessgroundminirect.height > window.innerHeight - padding) {
        finalY = window.innerHeight - chessgroundminirect.height - padding;
      }
    } else {
      if (offsetX + chessgroundminirect.width > mainrect.right - padding) {
        finalX -= chessgroundminirect.width;
      }
    }
    chessgroundMini.style.left = `${finalX}px`;
    chessgroundMini.style.top = `${finalY}px`;
    setTimeout(() => {
      chessgroundMini.style.display = "";
    }, 25);
  }
  if (info_struct.gameresult != "*") {
    let elem = document.getElementById("gameresultcontainermini");
    while (elem) {
      chessgroundMiniBoardWrapper.removeChild(elem);
      elem = document.getElementById("gameresultcontainermini");
    }
    let operationrect = chessgroundMiniBoardOperations.getBoundingClientRect();
    let div = document.createElement("div");
    div.id = "gameresultcontainermini";
    div.classList.add("inaccessble");
    div.style.position = "absolute";
    div.style.display = "flex";
    div.style.overflow = "hidden";
    div.style.top = "0";
    div.style.left = `${operationrect.width}px`;
    div.style.bottom = "0";
    div.style.right = "0";
    div.style.justifyContent = "center";
    div.style.alignItems = "center";
    div.style.zIndex = "1000";
    div.style.background = "rgba(0,0,0,0)";
    div.style.pointerEvents = "none";
    let spangameresultmini = document.createElement("spangameresultmini");
    //let wrapperrect = chessgroundMiniBoardWrapper.getBoundingClientRect();

    //let chessgroundminirect = chessgroundMini.getBoundingClientRect();
    spangameresultmini.innerText = info_struct.gameresult;
    //spangameresultmini.style.left = `${(operationrect.width / chessgroundminirect.width + wrapperrect.width / 2 / chessgroundminirect.width) * 100}%`;
    //spangameresultmini.style.top = "50%";
    div.appendChild(spangameresultmini);
    setTimeout(() => {
      spangameresultmini.style.opacity = "1";
      spangameresultmini.style.fontSize = "90px";
    }, 100);
    setTimeout(() => {
      spangameresultmini.style.opacity = "0";
      spangameresultmini.style.fontSize = "1px";
    }, 2600);
    chessgroundMiniBoardWrapper.appendChild(div);
  }
}

//Only supposed to be called in analysis PV display
function parseUCIMovesToPreviewElements(
  variant,
  fen,
  is960,
  ucimoves,
  elementid,
  sannotation,
  originalfen,
  originalmoves,
) {
  function new_info_struct() {
    return {
      text_content: "",
      fenstr: "",
      lastmove: "",
      moveturn: "",
      checked: [""],
      gameresult: "",
      startingfen: "",
      moves: "",
      boardmarkers: "",
    };
  }
  let moves = ucimoves.trim().split(" ");
  let i = 0;
  let movesparagraph = document.createElement("div");
  movesparagraph.id = elementid;
  movesparagraph.classList.add("board-display-san");
  let movesan = "";
  for (i = 0; i < moves.length; i++) {
    if (moves[i] == "") {
      moves.splice(i, 1);
      i--;
    }
  }
  let tmpboard = new ffish.Board(variant, fen, is960);
  let gameresult = "";
  let info_struct = new_info_struct();
  for (i = 0; i < moves.length; i++) {
    if (i == 0) {
      if (tmpboard.turn()) {
        let fullmovenum = document.createElement("p");
        fullmovenum.innerText = `${tmpboard.fullmoveNumber()}.`;
        movesparagraph.appendChild(fullmovenum);
      } else {
        let fullmovenum = document.createElement("p");
        fullmovenum.innerText = `${tmpboard.fullmoveNumber()}...`;
        movesparagraph.appendChild(fullmovenum);
      }
    } else if (tmpboard.turn()) {
      let fullmovenum = document.createElement("p");
      fullmovenum.innerText = `${tmpboard.fullmoveNumber()}.`;
      movesparagraph.appendChild(fullmovenum);
    }
    movesan = tmpboard.sanMove(moves[i], sannotation);
    if (!tmpboard.push(moves[i])) {
      tmpboard.delete();
      return null;
    }
    gameresult = getBoardResult(tmpboard);
    info_struct = new_info_struct();
    let moveelement = document.createElement("p");
    let move = moveutil.ParseUCIMove(moves[i]);
    moveelement.innerText = movesan;
    moveelement.classList.add("position-display-label");
    info_struct.fenstr = tmpboard.fen();
    info_struct.lastmove = [
      convertSquareToChessgroundXKey(move[0]),
      convertSquareToChessgroundXKey(move[1]),
    ];
    info_struct.moveturn = tmpboard.turn() ? "white" : "black";
    info_struct.checked = getCheckSquares(tmpboard);
    info_struct.gameresult = gameresult;
    info_struct.startingfen = originalfen;
    info_struct.moves = (
      originalmoves.trim() +
      " " +
      moves.slice(0, i + 1).join(" ")
    ).trim();
    /*
        
        TODO: Due to dynamic element removing and adding, sometimes clicking the element has no effect, especially when it's frequently updated.
              The shorter the intervals of deleting previous div and creating a new one using this function is, the more frequent it happens.
              For example, let 2 random movers play against each other and this happens frequently.

              This is likely to be caused by clicking during the initialization period of these elements, so probably use static allocation which does not delete and create DOM objects, but modifies its content instead.
        
        */
    let info_struct_pointer = info_struct;
    moveelement.onclick = (event) => {
      onMoveElementClicked(info_struct_pointer, event.target);
    };
    movesparagraph.appendChild(moveelement);
    if (gameresult != "*") {
      break;
    }
  }
  if (gameresult != "*") {
    let pgameresult = document.createElement("p");
    pgameresult.innerText = gameresult;
    movesparagraph.appendChild(pgameresult);
  }
  tmpboard.delete();
  movesparagraph.movecount = moves.length;
  return movesparagraph;
}

/*function generateStaticPreviewDiv(maxfullmovenumber) {
    let i = 0;
    let j = 0;
    let movesparagraph = document.createElement("div");
    movesparagraph.maxfullmovenumber = maxfullmovenumber;
    movesparagraph.classList.add("board-display-san");
    for (i = 0; i < maxfullmovenumber; i++) {
        let fullmovenum = document.createElement("p");
        movesparagraph.appendChild(fullmovenum);
        for (i = 0; i < 2; j++) {
            let moveelement = document.createElement("p");
            moveelement.classList.add("position-display-label");
            moveelement.fenstr = "";
            moveelement.lastmove = [];
            moveelement.moveturn = "";
            moveelement.isincheck = false;
            moveelement.gameresult = "";
            moveelement.style.display = "none";
            moveelement.onclick = function () {
                chessground_mini.set({
                    fen: this.fenstr,
                    orientation: chessground.state.orientation,
                    turnColor: this.moveturn,
                    check: this.isincheck,
                    lastMove: this.lastmove,
                    notation: chessground.state.notation,
                });
                if (chessgroundMini.style.display == "none") {
                    const rect = this.getBoundingClientRect();
                    const mainrect = divMain.getBoundingClientRect();
                    let chessgroundminirect = chessgroundMini.getBoundingClientRect();
                    while (chessgroundminirect.width == 0) {
                        chessgroundMini.style.display = "";
                        chessgroundminirect = chessgroundMini.getBoundingClientRect();
                    }
                    const padding = 10;
                    let offsetX = 0;
                    let offsetY = 0;
                    if (chessgroundMini.pinned) {
                        offsetX = rect.left;
                        offsetY = rect.top;
                    }
                    else {
                        offsetX = rect.left - mainrect.left;
                        offsetY = rect.top - mainrect.top;
                    }
                    let finalX = offsetX;
                    let finalY = offsetY + 40;
                    if (chessgroundMini.pinned) {
                        if (offsetX + chessgroundminirect.width > window.innerWidth - padding) {
                            finalX -= chessgroundminirect.width;
                        }
                        if (offsetY + chessgroundminirect.height > window.innerHeight - padding) {
                            finalY = window.innerHeight - chessgroundminirect.height - padding;
                        }
                    }
                    else {
                        if (offsetX + chessgroundminirect.width > mainrect.right - padding) {
                            finalX -= chessgroundminirect.width;
                        }
                    }
                    chessgroundMini.style.left = `${finalX}px`;
                    chessgroundMini.style.top = `${finalY}px`;
                    setTimeout(() => {
                        chessgroundMini.style.display = "";
                    }, 25);
                }
                if (this.gameresult != "*") {
                    let elem = document.getElementById("gameresultcontainermini");
                    while (elem) {
                        chessgroundMiniBoardWrapper.removeChild(elem);
                        elem = document.getElementById("gameresultcontainermini");
                    }
                    let operationrect = chessgroundMiniBoardOperations.getBoundingClientRect();
                    let div = document.createElement("div");
                    div.id = "gameresultcontainermini";
                    div.classList.add("inaccessble");
                    div.style.position = "absolute";
                    div.style.display = "flex";
                    div.style.overflow = "hidden";
                    div.style.top = "0";
                    div.style.left = `${operationrect.width}px`;
                    div.style.bottom = "0";
                    div.style.right = "0";
                    div.style.justifyContent = "center";
                    div.style.alignItems = "center";
                    div.style.zIndex = "1000";
                    div.style.background = "rgba(0,0,0,0)";
                    div.style.pointerEvents = "none";
                    let spangameresultmini = document.createElement("spangameresultmini");
                    spangameresultmini.innerText = this.gameresult;
                    div.appendChild(spangameresultmini);
                    setTimeout(() => {
                        spangameresultmini.style.opacity = "1";
                        spangameresultmini.style.fontSize = "80px";
                    }, 100);
                    setTimeout(() => {
                        spangameresultmini.style.opacity = "0";
                        spangameresultmini.style.fontSize = "1px";
                    }, 2600);
                    setTimeout(() => {
                        chessgroundMiniBoardWrapper.removeChild(div);
                    }, 3200);
                    chessgroundMiniBoardWrapper.appendChild(div);
                }
            };
            movesparagraph.appendChild(moveelement);
        }
    }
    return movesparagraph;
}

function parseUCIMovesToPreviewElementsStatic(movesparagraph, variant, fen, is960, ucimoves, sannotation) {
    if (movesparagraph == null || movesparagraph.maxfullmovenumber == undefined) {
        return null;
    }
    let moves = ucimoves.trim().split(' ');
    let i = 0;
    let j = 0;
    let tmpboard = new ffish.Board(variant, fen, is960);
    let movesan = "";
    for (i = 0; i < moves.length; i++) {
        if (moves[i] == "") {
            moves.splice(i, 1);
            i--;
        }
    }
    let childnodes = movesparagraph.childNodes;
    for (i = 0, j = 0; true; i += 3) {
        if (moves[j] == undefined) {
            break;
        }
        if (i == 0) {
            if (tmpboard.turn()) {
                childnodes.item(0).innerText = `${tmpboard.fullmoveNumber()}.`;
            }
            else {
                childnodes.item(0).innerText = `${tmpboard.fullmoveNumber()}...`;
            }
            childnodes.item(0).style.display = "";
            childnodes.item(1).style.display = "none";
            childnodes.item(2).style.display = "none";
        }
        else {
            childnodes.item(i).innerText = `${tmpboard.fullmoveNumber()}.`;
            childnodes.item(i).style.display = "";
        }
        movesan = tmpboard.sanMove(moves[j], sannotation);
        if (!tmpboard.push(moves[j])) {
            break;
        }
        let move = parseUCIMove(moves[j]);
        if (!tmpboard.turn()) {
            childnodes.item(i + 1).innerText = movesan;
            childnodes.item(i + 1).fenstr = tmpboard.fen();
            childnodes.item(i + 1).lastmove = [move[0].replace("10", ":"), move[1].replace("10", ":")];
            childnodes.item(i + 1).moveturn = "black";
            childnodes.item(i + 1).isincheck = tmpboard.isCheck();
            childnodes.item(i + 1).gameresult = tmpboard.result();
            childnodes.item(i + 1).style.display = "";
            if (moves[j + 1] == undefined) {
                break;
            }
            movesan = tmpboard.sanMove(moves[j + 1], sannotation);
            if (!tmpboard.push(moves[j + 1])) {
                break;
            }
            move = parseUCIMove(moves[j + 1]);
            childnodes.item(i + 2).innerText = movesan;
            childnodes.item(i + 2).fenstr = tmpboard.fen();
            childnodes.item(i + 2).lastmove = [move[0].replace("10", ":"), move[1].replace("10", ":")];
            childnodes.item(i + 2).moveturn = "white";
            childnodes.item(i + 2).isincheck = tmpboard.isCheck();
            childnodes.item(i + 2).gameresult = tmpboard.result();
            childnodes.item(i + 2).style.display = "";
            j += 2;
        }
        else {
            childnodes.item(i + 1).style.display = "none";
            childnodes.item(i + 2).innerText = movesan;
            childnodes.item(i + 2).fenstr = tmpboard.fen();
            childnodes.item(i + 2).lastmove = [move[0].replace("10", ":"), move[1].replace("10", ":")];
            childnodes.item(i + 2).moveturn = "white";
            childnodes.item(i + 2).isincheck = tmpboard.isCheck();
            childnodes.item(i + 2).gameresult = tmpboard.result();
            childnodes.item(i + 2).style.display = "";
            j++;
        }
    }
    if (tmpboard.result() != "*") {
        childnodes.item(i).innerText = tmpboard.result();
        childnodes.item(i).style.display = "";
        i++;
    }
    for (i = i; i < 3 * movesparagraph.maxfullmovenumber; i++) {
        childnodes.item(i).style.display = "none";
    }
    tmpboard.delete();
    return movesparagraph;
}*/

function GenerateBoardImage(
  GenerationMode,
  ImageWidth,
  ImageHeight,
  KeepAspectRatio,
  OnFinishedCallback,
) {
  if (
    typeof GenerationMode != "string" ||
    typeof ImageWidth != "number" ||
    typeof ImageHeight != "number" ||
    typeof KeepAspectRatio != "boolean" ||
    typeof OnFinishedCallback != "function"
  ) {
    throw TypeError();
  }
  let dimensions = getDimensions(board);
  let asseturl = themedetector.GetThemes();
  let coordcolors = themedetector.GetInnerCoordinateColor();
  let moves = gametree.GetMoveListOfMove(gametree.CurrentMove);
  let representativepieces = getRepresentativePiece();
  let tmpboard = new ffish.Board(
    gametree.Variant,
    gametree.OriginalFEN,
    gametree.Is960,
  );
  let imagewidth = ImageWidth;
  let imageheight = ImageHeight;
  let notation = dropdownBoardCoordinate.selectedIndex;
  let whitename = "";
  let blackname = "";
  if (playWhite.checked) {
    if (fge.state.first_engine instanceof fge.Engine) {
      whitename = fge.state.first_engine.Name;
    } else {
      whitename = "In browser Fairy-Stockfish";
    }
  } else {
    whitename = "Human Player";
  }
  if (playBlack.checked) {
    if (fge.state.second_engine instanceof fge.Engine) {
      blackname = fge.state.second_engine.Name;
    } else {
      blackname = "In browser Fairy-Stockfish";
    }
  } else {
    blackname = "Human Player";
  }
  whitename = gametree.GameHeaders.get("White") || whitename;
  blackname = gametree.GameHeaders.get("Black") || blackname;
  if (GenerationMode == "current") {
    tmpboard.pushMoves(moves);
    let hiddenpieces = getHiddenDroppablePiece(tmpboard);
    let fen = tmpboard.fen().split(" ")[0];
    let checkedpieces = tmpboard.checkedPieces();
    let checkedsquares = [];
    if (checkedpieces) {
      checkedsquares = checkedpieces.split(" ");
    }
    if (hiddenpieces.length > 0) {
      let index = fen.indexOf("[");
      if (index < 0) {
        fen = fen + `[${hiddenpieces}]`;
      } else {
        fen =
          fen.substring(0, index + 1) + hiddenpieces + fen.substring(index + 1);
      }
    }
    if (KeepAspectRatio) {
      let displayheight = dimensions.height;
      if (fen.includes("[")) {
        displayheight += 2;
      }
      if (checkboxShowPlayerInformation.checked) {
        displayheight += 2;
      }
      imageheight = (imagewidth / dimensions.width) * displayheight;
    }
    imageutil.GenerateBoardImage(
      fen,
      gametree.CurrentMove.Move.Move,
      checkedsquares,
      fen.includes("["),
      chessground.state.orientation,
      dimensions.width,
      dimensions.height,
      notation,
      coordcolors.dark,
      coordcolors.light,
      checkboxShowPlayerInformation.checked,
      whitename,
      blackname,
      representativepieces.white,
      representativepieces.black,
      tmpboard.turn() ? "white" : "black",
      asseturl.pieces,
      asseturl.board,
      imagewidth,
      imageheight,
      (canvas) => {
        if (canvas instanceof HTMLCanvasElement) {
          OnFinishedCallback([canvas]);
        }
      },
    );
  } else if (GenerationMode == "all") {
    let i = 0;
    let movelist = moves.split(" ").filter((val) => val != "");
    let haspocket = false;
    let hiddenpieces;
    let fen, checkedpieces;
    let fens = [];
    let moveturns = [];
    let checkedsquarelist = [];
    let drawncanvascount = 0;
    let totalcanvascount = movelist.length + 1;
    let canvaslist = [];
    for (i = -1; i < movelist.length; i++) {
      if (i >= 0) {
        tmpboard.push(movelist[i]);
      }
      hiddenpieces = getHiddenDroppablePiece(tmpboard);
      fen = tmpboard.fen().split(" ")[0];
      checkedpieces = tmpboard.checkedPieces();
      if (checkedpieces) {
        checkedsquarelist.push(checkedpieces.split(" "));
      } else {
        checkedsquarelist.push([]);
      }
      if (hiddenpieces.length > 0) {
        let index = fen.indexOf("[");
        if (index < 0) {
          fen = fen + `[${hiddenpieces}]`;
        } else {
          fen =
            fen.substring(0, index + 1) +
            hiddenpieces +
            fen.substring(index + 1);
        }
      }
      haspocket = haspocket || fen.includes("[");
      fens.push(fen);
      moveturns.push(tmpboard.turn() ? "white" : "black");
      canvaslist.push(null);
    }
    if (KeepAspectRatio) {
      let displayheight = dimensions.height;
      if (haspocket) {
        displayheight += 2;
      }
      if (checkboxShowPlayerInformation.checked) {
        displayheight += 2;
      }
      imageheight = (imagewidth / dimensions.width) * displayheight;
    }
    for (i = 0; i < fens.length; i++) {
      (function (index) {
        imageutil.GenerateBoardImage(
          fens[index],
          index == 0 ? "" : movelist[index - 1],
          checkedsquarelist[index],
          haspocket,
          chessground.state.orientation,
          dimensions.width,
          dimensions.height,
          notation,
          coordcolors.dark,
          coordcolors.light,
          checkboxShowPlayerInformation.checked,
          whitename,
          blackname,
          representativepieces.white,
          representativepieces.black,
          moveturns[index],
          asseturl.pieces,
          asseturl.board,
          imagewidth,
          imageheight,
          (canvas) => {
            drawncanvascount++;
            if (canvas instanceof HTMLCanvasElement) {
              canvaslist[index] = canvas;
            }
            if (drawncanvascount >= totalcanvascount) {
              OnFinishedCallback(canvaslist);
            }
          },
        );
      })(i);
    }
  }
  tmpboard.delete();
}

function showWallSquares() {
  let wall_square_list = getWallSquarePosition();
  let i = 0;
  let DrawShapeClass = {
    orig: "a1",
    brush: "red",
    customSvg: "./assets/images/wallsquare/barrier.svg",
  };
  let DrawShapeList = [];
  for (i = 0; i < wall_square_list.length; i++) {
    DrawShapeClass.orig = wall_square_list[i];
    DrawShapeList.push(DrawShapeClass);
  }
  chessground.setAutoShapes(DrawShapeList);
}

function getUsedPieceID(variant, isfischerrandom) {
  console.log("Now testing piece set! You may see a lot of warnings here.");
  let validPieceID = pieces.filter((element) => {
    let result = ffish.validateFen(element, variant, isfischerrandom);
    return result != -10 && result != -12;
  });
  return validPieceID;
}

function setPieceList(used_piece_list) {
  while (dropdownSetPiece.length > 2) {
    dropdownSetPiece.remove(2);
  }
  let option = null;
  let i = 0;
  for (i = 0; i < used_piece_list.length; i++) {
    option = document.createElement("option");
    option.text = used_piece_list[i];
    option.value = used_piece_list[i];
    dropdownSetPiece.add(option);
  }
}

function addPieceToPocket(pieceid, color) {
  if (pieceid.charAt(0) == "+") {
    pieceid = "p" + pieceid.substring(1);
  }
  let piecerole = pieceid + "-piece";
  if (!chessground.state.boardState.pockets.white.has(piecerole)) {
    chessground.state.boardState.pockets.white.set(piecerole, 0);
  }
  if (!chessground.state.boardState.pockets.black.has(piecerole)) {
    chessground.state.boardState.pockets.black.set(piecerole, 0);
  }
  if (!chessground.state.pocketRoles.white.includes(piecerole)) {
    chessground.state.pocketRoles.white.push(piecerole);
  }
  if (!chessground.state.pocketRoles.black.includes(piecerole)) {
    chessground.state.pocketRoles.black.push(piecerole);
  }
  if (color == "white") {
    chessground.state.boardState.pockets.white.set(
      piecerole,
      chessground.state.boardState.pockets.white.get(piecerole) + 1,
    );
  } else if (color == "black") {
    chessground.state.boardState.pockets.black.set(
      piecerole,
      chessground.state.boardState.pockets.black.get(piecerole) + 1,
    );
  }
  chessground.set({
    lastMove: undefined,
    pocketRoles: {
      white: chessground.state.pocketRoles.white,
      black: chessground.state.pocketRoles.black,
    },
  });
  redrawChessground(getFEN(false));
}

function clearMovesList() {
  while (availablemovelist.length > 1) {
    availablemovelist.removeChild(availablemovelist[1]);
  }
  searchresultinfo.innerText = "Click <Search Moves> to search!";
}

function generateRegExp(expstr) {
  if (typeof expstr != "string") {
    return null;
  }
  if (expstr.trim().charAt(0) == "/") {
    let i = 0;
    let str = expstr.trim().slice(1);
    let index = 0;
    for (i = 0; i < str.length; i++) {
      if (str.charAt(i) == "\\") {
        i++;
        continue;
      }
      if (str.charAt(i) == "/") {
        if (i == 0) {
          window.alert(
            'There is a syntax error in the regular expression. The syntax is /<search items...>/<flags...>. You can google "regular expression" to get more informaion.',
          );
          return null;
        } else {
          index = i;
          break;
        }
      }
    }
    let params = [str.slice(0, index), str.slice(index + 1)];
    try {
      let regexp = new RegExp(params[0], params[1]);
      return regexp;
    } catch {
      window.alert(
        'There is a syntax error in the regular expression. The syntax is /<search items...>/<flags...>. You can google "regular expression" to get more information.',
      );
      return null;
    }
  } else {
    window.alert(
      "There is a syntax error in the regular expression. It must start with '/'. E.G. /[a-z]+/g",
    );
    return null;
  }
}

function filterMoves(
  moveslist,
  searchstr,
  isregexp,
  orig,
  dest,
  isdrop,
  haswallgating,
  haspiecechange,
) {
  if (
    typeof moveslist != typeof [""] ||
    typeof searchstr != "string" ||
    typeof isregexp != "boolean" ||
    typeof orig != "string" ||
    typeof dest != "string" ||
    typeof isdrop != "boolean" ||
    typeof haswallgating != "boolean" ||
    typeof haspiecechange != "boolean"
  ) {
    return null;
  }
  let result = [];
  if (isregexp) {
    let regexp = generateRegExp(searchstr);
    if (regexp == null) {
      return null;
    }
    moveslist.forEach((val) => {
      if (regexp.test(val)) {
        let res = moveutil.ParseUCIMove(val);
        if (!isdrop && res[0].includes("@")) {
          return;
        }
        if (!haspiecechange && res[2] != "") {
          return;
        }
        if (!haswallgating && res[3] != "") {
          return;
        }
        if (orig != "" && !res[0].includes("@") && orig != res[0]) {
          return;
        }
        if (dest != "" && res[1] != dest) {
          return;
        }
        result.push(val);
      }
    });
  } else {
    let str = searchstr.trim();
    moveslist.forEach((val) => {
      if (val.includes(str)) {
        let res = moveutil.ParseUCIMove(val);
        if (!isdrop && res[0].includes("@")) {
          return;
        }
        if (!haspiecechange && res[2] != "") {
          return;
        }
        if (!haswallgating && res[3] != "") {
          return;
        }
        if (orig != "" && !res[0].includes("@") && orig != res[0]) {
          return;
        }
        if (dest != "" && res[1] != dest) {
          return;
        }
        result.push(val);
      }
    });
  }
  return result;
}

function highlightMoveOnBoard(
  moveturns,
  chessground,
  moves,
  colors,
  notepositions,
  isautoshape,
) {
  if (
    !Array.isArray(moveturns) ||
    !Array.isArray(moves) ||
    !Array.isArray(colors) ||
    !Array.isArray(notepositions) ||
    typeof isautoshape != "boolean" ||
    chessground == null
  ) {
    return;
  }
  let i = 0;
  let bestmove = null;
  let autoshapes = [];
  let color = "";
  let notecolor = "";
  let moveturn = true;
  let noteposition = "";
  for (i = 0; i < moves.length; i++) {
    bestmove = moveutil.ParseUCIMove(moves[i]);
    if (
      bestmove[0] == null ||
      bestmove[1] == null ||
      bestmove[2] == null ||
      bestmove[3] == null
    ) {
      continue;
    }
    color = colors[i];
    moveturn = moveturns[i];
    noteposition = notepositions[i];
    if (color == "blue") {
      notecolor = "#003088";
    } else if (color == "red") {
      notecolor = "#882020";
    } else if (color == "yellow") {
      notecolor = "#e68f00";
    } else if (color == "green") {
      notecolor = "#15781b";
    } else {
      notecolor = "#000000";
    }
    if (bestmove[0].startsWith("@")) {
      autoshapes.push({
        brush: color,
        orig: convertSquareToChessgroundXKey(bestmove[1]),
      });
    } else if (bestmove[0].includes("@")) {
      autoshapes.push({
        brush: color,
        orig: convertSquareToChessgroundXKey(bestmove[1]),
      });
      if (moveturn) {
        if (bestmove[0].charAt(0) == "+") {
          autoshapes.push({
            brush: color,
            dest: "a0",
            orig: convertSquareToChessgroundXKey(bestmove[1]),
            piece: {
              color: "white",
              role: "p" + bestmove[0].toLowerCase().charAt(1) + "-piece",
              scale: 0.7,
            },
            modifiers: { hilite: true },
          });
        } else {
          autoshapes.push({
            brush: color,
            dest: "a0",
            orig: convertSquareToChessgroundXKey(bestmove[1]),
            piece: {
              color: "white",
              role: bestmove[0].toLowerCase().charAt(0) + "-piece",
              scale: 0.7,
            },
            modifiers: { hilite: true },
          });
        }
      } else {
        if (bestmove[0].charAt(0) == "+") {
          autoshapes.push({
            brush: color,
            dest: "a0",
            orig: convertSquareToChessgroundXKey(bestmove[1]),
            piece: {
              color: "black",
              role: "p" + bestmove[0].toLowerCase().charAt(1) + "-piece",
              scale: 0.7,
            },
            modifiers: { hilite: true },
          });
        } else {
          autoshapes.push({
            brush: color,
            dest: "a0",
            orig: convertSquareToChessgroundXKey(bestmove[1]),
            piece: {
              color: "black",
              role: bestmove[0].toLowerCase().charAt(0) + "-piece",
              scale: 0.7,
            },
            modifiers: { hilite: true },
          });
        }
      }
    } else {
      if (bestmove[0] == bestmove[1]) {
        autoshapes.push({
          brush: "black",
          orig: convertSquareToChessgroundXKey(bestmove[0]),
          customSvg: generatePassTurnNotationSVG(notecolor),
        });
      } else {
        autoshapes.push({
          brush: color,
          dest: convertSquareToChessgroundXKey(bestmove[1]),
          orig: convertSquareToChessgroundXKey(bestmove[0]),
        });
      }
      if (bestmove[2] != "") {
        let piecerole = chessground.state.boardState.pieces.get(
          convertSquareToChessgroundXKey(bestmove[0]),
        ).role;
        autoshapes.push({
          brush: "black",
          orig: convertSquareToChessgroundXKey(bestmove[1]),
          customSvg: generateMoveNotationSVG(
            bestmove[2],
            notecolor,
            "#ffffff",
            noteposition,
          ),
        });
        if (bestmove[2] == "+") {
          if (moveturn) {
            autoshapes.push({
              brush: color,
              orig: convertSquareToChessgroundXKey(bestmove[1]),
              dest: convertSquareToChessgroundXKey(bestmove[0]),
              piece: { color: "white", role: "p" + piecerole },
            });
          } else {
            autoshapes.push({
              brush: color,
              orig: convertSquareToChessgroundXKey(bestmove[1]),
              dest: convertSquareToChessgroundXKey(bestmove[0]),
              piece: { color: "black", role: "p" + piecerole },
            });
          }
        } else if (bestmove[2] == "-") {
          if (moveturn) {
            autoshapes.push({
              brush: color,
              orig: convertSquareToChessgroundXKey(bestmove[1]),
              dest: convertSquareToChessgroundXKey(bestmove[0]),
              piece: { color: "white", role: piecerole.slice(1) },
            });
          } else {
            autoshapes.push({
              brush: color,
              orig: convertSquareToChessgroundXKey(bestmove[1]),
              dest: convertSquareToChessgroundXKey(bestmove[0]),
              piece: { color: "black", role: piecerole.slice(1) },
            });
          }
        } else {
          if (moveturn) {
            autoshapes.push({
              brush: color,
              orig: convertSquareToChessgroundXKey(bestmove[1]),
              dest: convertSquareToChessgroundXKey(bestmove[0]),
              piece: { color: "white", role: bestmove[2] + "-piece" },
            });
          } else {
            autoshapes.push({
              brush: color,
              orig: convertSquareToChessgroundXKey(bestmove[1]),
              dest: convertSquareToChessgroundXKey(bestmove[0]),
              piece: { color: "black", role: bestmove[2] + "-piece" },
            });
          }
        }
      }
    }
    if (bestmove[3] != "") {
      autoshapes.push({
        brush: color,
        orig: convertSquareToChessgroundXKey(bestmove[3]),
      });
      autoshapes.push({
        brush: color,
        dest: "a0",
        orig: convertSquareToChessgroundXKey(bestmove[3]),
        piece: {
          color: "black",
          role: "_-piece",
          scale: 0.7,
        },
        modifiers: { hilite: true },
      });
    }
  }
  if (isautoshape) {
    chessground.setAutoShapes(autoshapes);
  } else {
    chessground.setShapes(autoshapes);
  }
}

function convertChessgroundHighlightsToBoardMarkers(chessground, isautoshape) {
  let shapes = isautoshape
    ? chessground.state.drawable.autoShapes
    : chessground.state.drawable.shapes;
  let i = 0;
  let item;
  let color;
  let resultcal = [];
  let resultcsl = [];
  for (i = 0; i < shapes.length; i++) {
    item = shapes[i];
    if (item.brush == "green") {
      color = "G";
    } else if (item.brush == "yellow") {
      color = "Y";
    } else if (item.brush == "blue") {
      color = "B";
    } else if (item.brush == "red") {
      color = "R";
    } else {
      continue;
    }
    if (item.dest) {
      resultcal.push(
        `${color}${convertChessgroundXKeyToSquare(item.orig)}${convertChessgroundXKeyToSquare(item.dest)}`,
      );
    } else {
      resultcsl.push(`${color}${convertChessgroundXKeyToSquare(item.orig)}`);
    }
  }
  return { cal: resultcal.join(","), csl: resultcsl.join(",") };
}

function getNotation(
  notation,
  variant,
  startfen,
  is960,
  ucimovestr,
  usemovetree,
) {
  if (
    typeof notation != "string" ||
    typeof variant != "string" ||
    typeof startfen != "string" ||
    typeof is960 != "boolean" ||
    typeof ucimovestr != "string" ||
    typeof usemovetree != "boolean"
  ) {
    throw TypeError();
  }
  if (notation == "") {
    return "(Missing notation system, please select one in the dropdown...)";
  }
  if (ffish) {
    const variants = ffish.variants().split(" ");
    let ucimoves = ucimovestr.trim();
    if (variants.includes(variant)) {
      // if (ffish.validateFen(startfen, variant, is960) >= 0)
      if (1) {
        let tmpboard = new ffish.Board(variant, startfen, is960);
        let moveslist = ucimoves.split(/[ ]+/).reverse();
        let result = "";
        let tmpboardresult = "";
        let notationindex = simplenotations.indexOf(notation);
        if (moveslist.length == 1 && moveslist[0] == "") {
        } else {
          while (moveslist.length > 0) {
            if (!tmpboard.push(moveslist.pop())) {
              return null;
            }
          }
        }
        tmpboardresult = getBoardResult(tmpboard);
        if (notationindex >= 0) {
          if (usemovetree) {
            result = gametree.ToString(
              ffishnotationobjects[notationindex],
              false,
            );
          } else {
            tmpboard.setFen(startfen);
            result =
              tmpboard.variationSan(
                ucimoves,
                ffishnotationobjects[notationindex],
              ) + (tmpboardresult !== "*" ? " " + tmpboardresult : "");
          }
        } else if (notation == "FEN") {
          result = tmpboard.fen();
        } else if (notation == "PGN") {
          const gameresult = tmpboardresult;
          tmpboard.setFen(startfen);
          const today = new Date();
          const year = today.getFullYear();
          const month = today.getMonth() + 1;
          const day = today.getDate();
          //const hours = today.getHours();
          //const minutes = today.getMinutes();
          //const seconds = today.getSeconds();
          let whitename = "";
          let blackname = "";
          if (playWhite.checked) {
            if (fge.state.first_engine instanceof fge.Engine) {
              whitename = fge.state.first_engine.Name;
            } else {
              whitename = "In browser Fairy-Stockfish";
            }
          } else {
            whitename = "Human Player";
          }
          if (playBlack.checked) {
            if (fge.state.second_engine instanceof fge.Engine) {
              blackname = fge.state.second_engine.Name;
            } else {
              blackname = "In browser Fairy-Stockfish";
            }
          } else {
            blackname = "Human Player";
          }
          result = `[Event "Fairy-Stockfish Playground Game"]\n[Site "${window.location.host}"]\n[Date "${year.toString() + "." + month.toString() + "." + day.toString()}"]\n`;
          result += `[Round "1"]\n[White "${whitename}"]\n[Black "${blackname}"]\n`;
          result += `[FEN "${startfen}"]\n[Result "${gameresult}"]\n[Variant "${tmpboard.variant()}"]\n\n`;
          result += tmpboard.variationSan(ucimoves, ffish.Notation.SAN);
        } else if (notation == "EPD") {
          const today = new Date();
          const year = today.getFullYear();
          const month = today.getMonth() + 1;
          const day = today.getDate();
          //const hours = today.getHours();
          //const minutes = today.getMinutes();
          //const seconds = today.getSeconds();
          let whitename = "";
          let blackname = "";
          if (playWhite.checked) {
            if (fge.state.first_engine instanceof fge.Engine) {
              whitename = fge.state.first_engine.Name;
            } else {
              whitename = "In browser Fairy-Stockfish";
            }
          } else {
            whitename = "Human Player";
          }
          if (playBlack.checked) {
            if (fge.state.second_engine instanceof fge.Engine) {
              blackname = fge.state.second_engine.Name;
            } else {
              blackname = "In browser Fairy-Stockfish";
            }
          } else {
            blackname = "Human Player";
          }
          result = `${tmpboard.fen()};`;
          result += ` acd 0;`;
          result += ` acn 0;`;
          result += ` acs 0;`;
          result += ` am 0000;`;
          result += ` bm 0000;`;
          result += ` ce 0.0;`;
          result += ` dm 0;`;
          result += ` draw_accept "null";`;
          result += ` draw_claim "null";`;
          result += ` draw_reject "null";`;
          result += ` eco "null";`;
          result += ` fmvn 0;`;
          result += ` hmvc 0;`;
          result += ` id "Fairy-Stockfish Playground Match";`;
          result += ` nic "null";`;
          result += ` pm 0000;`;
          result += ` pv 0;`;
          result += ` rc 0;`;
          result += ` resign "null";`;
          result += ` sm 0000;`;
          result += ` tcgs "null";`;
          result += ` tcri "null";`;
          result += ` tcsi "null";`;
          result += ` v0 "null";`;
          result += ` variant "${tmpboard.variant()}";`;
          result += ` site "${window.location.host}";`;
          result += ` date "${year.toString() + "." + month.toString() + "." + day.toString()}";`;
          result += ` result "${tmpboardresult}";`;
          result += ` first_player "${whitename}";`;
          result += ` second_player "${blackname}";`;
        } else if (notation == "FEN+UCIMOVE") {
          tmpboard.setFen(startfen);
          result = tmpboard.fen() + "|" + ucimoves;
        } else if (notation == "FEN+USIMOVE") {
          tmpboard.setFen(startfen);
          let dimensions = getDimensions(board);
          const convertedmoves = fge.convertUCImovestoUSImoves(
            ucimoves,
            dimensions.width,
            dimensions.height,
          );
          if (convertedmoves != null) {
            result = tmpboard.fen() + "|" + convertedmoves;
          } else {
            result =
              tmpboard.fen() +
              "|(There are moves that cannot be displayed in USI moves, such as pawn promotion or seirawan gating)";
          }
        } else if (notation == "FEN+UCCIMOVE") {
          tmpboard.setFen(startfen);
          let dimensions = getDimensions(board);
          const convertedmoves = fge.convertUCImovestoUCCImoves(
            ucimoves,
            dimensions.width,
            dimensions.height,
          );
          if (convertedmoves != null) {
            result = tmpboard.fen() + "|" + convertedmoves;
          } else {
            result =
              tmpboard.fen() +
              "|(There are moves that cannot be displayed in UCCI moves, such as pawn promotion or seirawan gating)";
          }
        } else if (notation == "SFEN+USIMOVE") {
          tmpboard.setFen(startfen);
          let dimensions = getDimensions(board);
          const convertedmoves = fge.convertUCImovestoUSImoves(
            ucimoves,
            dimensions.width,
            dimensions.height,
          );
          if (convertedmoves != null) {
            result =
              fge.ConvertFENtoSFEN(tmpboard.fen()) +
              "|" +
              fge.convertUCImovestoUSImoves(
                ucimoves,
                dimensions.width,
                dimensions.height,
              );
          } else {
            result =
              fge.ConvertFENtoSFEN(tmpboard.fen()) +
              "|(There are moves that cannot be displayed in USI moves, such as pawn promotion or seirawan gating)";
          }
        }
        tmpboard.delete();
        return result;
      } else {
        return "Illegal FEN";
      }
    } else {
      return null;
    }
  } else {
    throw Error("ffish.js is not initialized!!!");
  }
}

function onPositionSet() {
  const fen = textFen.value.trim();
  const WhiteSpaceMatcher = new RegExp("[ ]+", "");

  if (!fen || validateFEN(fen, false)) {
    if (fen) board.setFen(fen);
    else board.reset();
    const moves = textMoves.value.trim().split(WhiteSpaceMatcher);
    let move = "";
    let i = 0;

    for (i = 0; i < moves.length; i++) {
      move = moves[i];
      if (move == "") {
        continue;
      }
      if (!board.push(move)) {
        buttonStop.click();
        moves.splice(i, 1);
        i--;
        window.alert(`Illegal move: ${move}`);
      }
    }
    textMoves.value = moves.join(" ");

    updateChessground(true);

    if (
      board.isGameOver() ||
      board.isGameOver(true) ||
      board.isGameOver(false)
    ) {
      let result = getBoardResult(board);
      if (result != "*") {
        document.dispatchEvent(
          new CustomEvent("gameend", {
            detail: { result: result, reason: "normal" },
          }),
        );
      }
    }
  } else {
    const moves = gametree.GetMoveListOfMove(gametree.CurrentMove);
    board.setFen(gametree.OriginalFEN);
    board.pushMoves(moves);
    textFen.value = gametree.OriginalFEN;
    textMoves.value = moves;
    updateChessground(true);
  }
  recordedmultipv = 1;
}

function getDimensions(board) {
  if (!board) {
    return {
      width: 8,
      height: 8,
    };
  }
  const fenBoard = board.fen().split(" ")[0];
  const ranks = fenBoard.split("/").length;
  const lastRank = fenBoard.split("/")[0].replace(/[^0-9a-z*]/gi, "");
  let files = lastRank.length;

  for (const match of lastRank.matchAll(/\d+/g)) {
    files += parseInt(match[0]) - match[0].length;
  }

  //console.log("Board: %dx%d", files, ranks);
  return {
    width: files,
    height: ranks,
  };
}

function getBoardResult(board) {
  let result = board.result();
  if (result == "*") {
    if (board.result(true) != "*") {
      result = board.result(true);
    } else if (board.result(false) != "*") {
      result = board.result(false);
    }
  }
  return result;
}

import Module from "ffish-es6";
new Module().then((loadedModule) => {
  ffish = loadedModule;
  console.log("ffish.js initialized!");
  window.ffishlib = loadedModule; //Used in dev tools for debugging purposes and transfer to <script>
  // Variants saved in the variant editor. The UI loads them into the engine.
  const savedvariants = myvariants.loadLibrary();
  if (savedvariants.length > 0) {
    ffish.loadVariantConfig(myvariants.libraryText(savedvariants));
  }
  initBoard(dropdownVariant.value);
  soundMove.volume = rangeVolume.value;
  soundCapture.volume = rangeVolume.value;
  soundCheck.volume = rangeVolume.value;
  soundTerminal.volume = rangeVolume.value;
  loadThemes.click();
  LoadPositionVariant("server", null);
  ffishnotationobjects = [
    ffish.Notation.DEFAULT,
    ffish.Notation.SAN,
    ffish.Notation.LAN,
    ffish.Notation.SHOGI_HOSKING,
    ffish.Notation.SHOGI_HODGES,
    ffish.Notation.SHOGI_HODGES_NUMBER,
    ffish.Notation.JANGGI,
    ffish.Notation.XIANGQI_WXF,
    ffish.Notation.THAI_SAN,
    ffish.Notation.THAI_LAN,
  ];
  const singleblankmatcher = new RegExp("[ ]+");
  let last_evaluation = "";

  variantsIni.onchange = function (e) {
    const selected = e.currentTarget.files[0];
    resetTimer();
    recordedmultipv = 1;
    if (selected) {
      selected.text().then(function (ini) {
        console.log(ini);
        ffish.loadVariantConfig(ini);
      });
    }
  };

  dropdownVariant.onchange = function () {
    if (!ffish.variants().includes(dropdownVariant.value)) {
      window.alert(
        `Error: Selected variant "${dropdownVariant.value}" is not present in ffish.js. This means that there is a version mismatch between Fairy-Stockfish WebAssembly port and ffish.js. Please report this issue on Github Issues of this project.`,
      );
      return;
    }
    const oldDimensions = getDimensions(board);
    initBoard(dropdownVariant.value);
    const newDimensions = getDimensions(board);
    chessgroundContainerEl.setAttribute(
      "style",
      `--files:${newDimensions.width};--ranks:${newDimensions.height}`,
    );
    chessgroundMiniContainerEl.setAttribute(
      "style",
      `--files:${newDimensions.width};--ranks:${newDimensions.height}`,
    );
    chessgroundContainerEl.classList.toggle(
      `board${oldDimensions["width"]}x${oldDimensions["height"]}`,
    );
    chessgroundContainerEl.classList.toggle(
      `board${newDimensions["width"]}x${newDimensions["height"]}`,
    );

    chessgroundMiniContainerEl.classList.toggle(
      `board${oldDimensions["width"]}x${oldDimensions["height"]}`,
    );
    chessgroundMiniContainerEl.classList.toggle(
      `board${newDimensions["width"]}x${newDimensions["height"]}`,
    );

    themedetector.SetBoardDimensions(newDimensions.width, newDimensions.height);

    if (ffish.capturesToHand(dropdownVariant.value)) {
      console.log("pockets");
      chessgroundContainerEl.classList.add("pockets");
      chessgroundMiniContainerEl.classList.add("pockets");
    } else {
      chessgroundContainerEl.classList.remove("pockets");
      chessgroundMiniContainerEl.classList.remove("pockets");
    }
    resetTimer();
    clearMovesList();

    initializeThemes.click();
    setPieceList(
      getUsedPieceID(dropdownVariant.value, checkboxFischerRandom.checked),
    );
    positionInformation.innerHTML = "";
    UpdateVariantsPositionTypeDropdown();
    UpdateVariantsPositionNameDropdown();
    pvinfo.innerHTML = "";

    updateInnerCoordinateColor(chessground);

    window.setTimeout(() => {
      buttonReset.click();
    }, 10);
  };

  buttonFlip.onclick = function () {
    chessground.toggleOrientation();
    chessground_mini.toggleOrientation();
    themedetector.SetOrientation(chessground.state.orientation);
    pBoardOrientation.textContent = chessground.state.orientation;
    pBoardOrientation.click();
    updateInnerCoordinateColor(chessground);
    updatePGNDivision(false);
  };

  buttonUndo.onclick = function () {
    gametree.CutCurrentMove();
    gametree.ClearHistory();
    textFen.value = gametree.OriginalFEN;
    textMoves.value = gametree.GetMoveListOfMove(gametree.CurrentMove);
    chessground.cancelPremove();
    buttonSetFen.click();
  };

  buttonMoveTreeClear.onclick = function () {
    if (!buttonMoveTreeClear.disabled) {
      gametree.ClearMoves();
      textFen.value = gametree.OriginalFEN;
      textMoves.value = "";
      buttonSetFen.click();
    }
  };

  buttonMoveTreeClearComments.onclick = function () {
    if (!buttonMoveTreeClearComments.disabled) {
      gametree.ClearComments();
      updatePGNDivision(false);
    }
  };

  buttonMoveTreeCrop.onclick = function () {
    if (!buttonMoveTreeCrop.disabled) {
      gametree.CropCurrentMove();
      textFen.value = gametree.OriginalFEN;
      textMoves.value = gametree.GetMoveListOfMove(gametree.CurrentMove);
      buttonSetFen.click();
    }
  };

  buttonMoveTreeCropBranch.onclick = function () {
    if (!buttonMoveTreeCropBranch.disabled) {
      gametree.RemoveNonCurrentMoveBranch();
      updatePGNDivision(false);
    }
  };

  buttonMoveTreeCut.onclick = function () {
    if (!buttonMoveTreeCut.disabled) {
      gametree.CutCurrentMove();
      textFen.value = gametree.OriginalFEN;
      textMoves.value = gametree.GetMoveListOfMove(gametree.CurrentMove);
      buttonSetFen.click();
    }
  };

  buttonMoveTreeCutBranch.onclick = function () {
    if (!buttonMoveTreeCutBranch.disabled) {
      gametree.RemoveCurrentMoveBranch();
      textFen.value = gametree.OriginalFEN;
      textMoves.value = gametree.GetMoveListOfMove(gametree.CurrentMove);
      buttonSetFen.click();
    }
  };

  buttonMoveTreeHeaders.onclick = function () {
    let datestr = gametree.GameHeaders.get("Date");
    pgnHeader.classList.remove("hidden");
    inputPGNEvent.value = gametree.GameHeaders.get("Event") ?? "";
    inputPGNSite.value = gametree.GameHeaders.get("Site") ?? "";
    inputPGNRound.value = gametree.GameHeaders.get("Round") ?? "1";
    if (datestr) {
      let date = datestr.split(".");
      let year = parseInt(date[0]);
      let month = parseInt(date[1]);
      let day = parseInt(date[2]);
      if (
        isNaN(year) ||
        isNaN(month) ||
        isNaN(day) ||
        year < 1 ||
        month < 1 ||
        month > 12 ||
        day < 1 ||
        day > 31
      ) {
        datestr = "";
      } else {
        datestr = `${String(year).padStart(4, "0")}-${String(month).padStart(2, "0")}-${String(day).padStart(2, "0")}`;
      }
    }
    inputPGNDate.value = datestr ?? "";
    inputPGNWhiteName.value = gametree.GameHeaders.get("White") ?? "";
    inputPGNBlackName.value = gametree.GameHeaders.get("Black") ?? "";
  };

  buttonMoveTreeHideShow.onclick = function () {
    if (!buttonMoveTreeHideShow.disabled) {
      gametree.ShowOrHideCurrentMove();
      updatePGNDivision(false);
    }
  };

  buttonMoveTreeMarkers.onclick = function () {
    if (!buttonMoveTreeMarkers.disabled) {
      gametree.CurrentMove.Move.TextAfter =
        gametree.CurrentMove.Move.TextAfter.replace(/\[%c(a|s)l.*?\]/g, "");
      let boardmarkers = convertChessgroundHighlightsToBoardMarkers(
        chessground,
        false,
      );
      let result = gametree.CurrentMove.Move.TextAfter;
      if (boardmarkers.cal) {
        result += `[%cal ${boardmarkers.cal}]`;
      }
      if (boardmarkers.csl) {
        result += `[%csl ${boardmarkers.csl}]`;
      }
      gametree.SetTextAfterOfCurrentMove(result);
      updatePGNDivision(false);
    }
  };

  buttonMoveTreeRemoveVariations.onclick = function () {
    if (!buttonMoveTreeRemoveVariations.disabled) {
      gametree.RemoveVariationsOfCurrentMove();
      updatePGNDivision(false);
    }
  };

  buttonMoveTreeRedo.onclick = function () {
    if (!buttonMoveTreeRedo.disabled) {
      gametree.Redo();
      textFen.value = gametree.OriginalFEN;
      textMoves.value = gametree.GetMoveListOfMove(gametree.CurrentMove);
      buttonSetFen.click();
    }
  };

  buttonMoveTreeResize.onclick = function () {
    labelPgn.classList.toggle("larger");
    buttonMoveTreeResize.classList.toggle("larger");
    if (buttonMoveTreeResize.classList.contains("larger")) {
      buttonMoveTreeResize.title =
        "Shrink PGN Viewer\nClick to make PGN viewer smaller.";
    } else {
      buttonMoveTreeResize.title =
        "Enlarge PGN Viewer\nClick to make PGN viewer larger.";
    }
  };

  buttonMoveTreeSave.onclick = function () {
    let result = "";
    let whitename = "";
    let blackname = "";
    if (playWhite.checked) {
      if (fge.state.first_engine instanceof fge.Engine) {
        whitename = fge.state.first_engine.Name;
      } else {
        whitename = "In browser Fairy-Stockfish";
      }
    } else {
      whitename = "Human Player";
    }
    if (playBlack.checked) {
      if (fge.state.second_engine instanceof fge.Engine) {
        blackname = fge.state.second_engine.Name;
      } else {
        blackname = "In browser Fairy-Stockfish";
      }
    } else {
      blackname = "Human Player";
    }
    result = gametree.GetHeaderString(whitename, blackname);
    result += "\n\n" + gametree.ToString(ffish.Notation.SAN, true) + "\n";
    DownloadFile(result, "game.pgn", "text/plain");
  };

  buttonMoveTreeSaveImage.onclick = function () {
    imageGenerator.classList.remove("hidden");
    themedetector.SetOrientation(chessground.state.orientation);
    inputFrameDuration.disabled =
      dropdownImageFileType[dropdownImageFileType.selectedIndex].value != "GIF";
    inputImageQuality.disabled =
      dropdownImageFileType[dropdownImageFileType.selectedIndex].value == "PNG";
  };

  buttonMoveTreeSetAsMainLine.onclick = function () {
    if (!buttonMoveTreeSetAsMainLine.disabled) {
      gametree.SetCurrentMoveBranchAsMainLine();
      updatePGNDivision(false);
    }
  };

  buttonMoveTreeSetToMainBranch.onclick = function () {
    if (!buttonMoveTreeSetToMainBranch.disabled) {
      gametree.SetCurrentMoveToMainBranch();
      updatePGNDivision(false);
    }
  };

  buttonMoveTreeSymbol.onclick = function () {
    if (!buttonMoveTreeSymbol.disabled) {
      const dropdownMoveCommentarySymbolValues = [
        "",
        "!",
        "?",
        "!!",
        "??",
        "!?",
        "?!",
        "□",
        "⨀",
      ];
      const dropdownPositionCommentarySymbolValues = [
        "",
        "=",
        "∞",
        "⩲",
        "⩱",
        "±",
        "∓",
        "+-",
        "-+",
        "+#",
        "-#",
      ];
      let symbols = gametree.CurrentMove.Move.Symbol;
      let i = 0;
      let glyph;
      let index;
      dropdownMoveCommentarySymbols.selectedIndex = 0;
      dropdownPositionCommentarySymbols.selectedIndex = 0;
      checkboxSpaceAdvantageSymbol.checked =
        checkboxDevelopmentSymbol.checked =
        checkboxInitiativeSymbol.checked =
        checkboxAttackSymbol.checked =
        checkboxWithCompensationSymbol.checked =
        checkboxCounterplaySymbol.checked =
        checkboxTimeTroubleSymbol.checked =
        checkboxWithTheIdeaSymbol.checked =
        checkboxNoveltySymbol.checked =
          false;
      for (i = 0; i < symbols.length; i++) {
        glyph = parseInt(symbols[i].slice(1));
        index = dropdownMoveCommentarySymbolValues.indexOf(
          moveutil.NumericAnnotationGlyphs[glyph],
        );
        if (index > 0) {
          dropdownMoveCommentarySymbols.selectedIndex = index;
          continue;
        }
        index = dropdownPositionCommentarySymbolValues.indexOf(
          moveutil.NumericAnnotationGlyphs[glyph],
        );
        if (index > 0) {
          dropdownPositionCommentarySymbols.selectedIndex = index;
          continue;
        }
        switch (moveutil.NumericAnnotationGlyphs[glyph]) {
          case "○": {
            checkboxSpaceAdvantageSymbol.checked = true;
            break;
          }
          case "↑↑": {
            checkboxDevelopmentSymbol.checked = true;
            break;
          }
          case "↑": {
            checkboxInitiativeSymbol.checked = true;
            break;
          }
          case "→": {
            checkboxAttackSymbol.checked = true;
            break;
          }
          case "=/∞": {
            checkboxWithCompensationSymbol.checked = true;
            break;
          }
          case "⇆": {
            checkboxCounterplaySymbol.checked = true;
            break;
          }
          case "⨁": {
            checkboxTimeTroubleSymbol.checked = true;
            break;
          }
          case "∆": {
            checkboxWithTheIdeaSymbol.checked = true;
            break;
          }
          case "N": {
            checkboxNoveltySymbol.checked = true;
            break;
          }
        }
      }
      pgnSymbols.classList.remove("hidden");
    }
  };

  buttonMoveTreeTermination.onclick = function () {
    if (buttonMoveTreeTermination.disabled) {
      return;
    }
    let tmpboard = new ffish.Board(
      gametree.Variant,
      gametree.OriginalFEN,
      gametree.Is960,
    );
    let result = "*",
      termination = "undefined";
    let index = 0,
      indexend = 0;
    let terminationstr = "";
    let buttonrect = buttonMoveTreeTermination.getBoundingClientRect();
    let mainrect = divMain.getBoundingClientRect();
    let rect = terminationSettings.getBoundingClientRect();
    tmpboard.pushMoves(gametree.GetMoveListOfMove(gametree.CurrentMove));
    result = getBoardResult(tmpboard);
    dropdownPGNResult.disabled = dropdownPGNTermination.disabled =
      result != "*";
    while (rect.width == 0) {
      terminationSettings.style.display = "";
      rect = terminationSettings.getBoundingClientRect();
    }
    if (result != "*") {
      termination = "end";
    } else if (gametree.CurrentMove.Move.TextAfter) {
      index = gametree.CurrentMove.Move.TextAfter.indexOf("[%end ");
      if (index >= 0) {
        indexend = gametree.CurrentMove.Move.TextAfter.indexOf("]", index + 6);
        if (indexend >= 0) {
          terminationstr = gametree.CurrentMove.Move.TextAfter.substring(
            index + 6,
            indexend,
          ).split(",");
          if (
            GameResults.includes(terminationstr[0]) &&
            GameTerminations.includes(terminationstr[1])
          ) {
            result = terminationstr[0];
            termination = terminationstr[1];
          }
        }
      }
    }
    dropdownPGNResult.selectedIndex = GameResults.indexOf(result);
    if (termination == "end") {
      dropdownPGNTermination.selectedIndex = dropdownPGNTermination.length - 1;
    } else {
      dropdownPGNTermination.selectedIndex =
        GameTerminations.indexOf(termination);
    }
    terminationSettings.style.left = `${buttonrect.left - mainrect.left - rect.width}px`;
    terminationSettings.style.top = `${buttonrect.bottom - mainrect.top}px`;
    terminationSettings.style.display = "";
    tmpboard.delete();
  };

  buttonMoveTreeTextAfter.onclick = function () {
    if (!buttonMoveTreeTextAfter.disabled) {
      pgnTextTitle.textContent = "Text After";
      textareaPgnTextInput.value = gametree.CurrentMove.Move.TextAfter;
      pgnText.classList.remove("hidden");
    }
  };

  buttonMoveTreeTextBefore.onclick = function () {
    if (!buttonMoveTreeTextBefore.disabled) {
      pgnTextTitle.textContent = "Text Before";
      textareaPgnTextInput.value = gametree.CurrentMove.Move.TextBefore;
      pgnText.classList.remove("hidden");
    }
  };

  buttonMoveTreeUncomment.onclick = function () {
    if (!buttonMoveTreeUncomment.disabled) {
      gametree.UncommentCurrentMove();
      updatePGNDivision(false);
    }
  };

  buttonMoveTreeUndo.onclick = function () {
    if (!buttonMoveTreeUndo.disabled) {
      gametree.Undo();
      textFen.value = gametree.OriginalFEN;
      textMoves.value = gametree.GetMoveListOfMove(gametree.CurrentMove);
      buttonSetFen.click();
    }
  };

  buttonMoveTreeBoardPreview.onclick = function () {
    if (!buttonMoveTreeBoardPreview.disabled) {
      let text_after = gametree.CurrentMove.Move.TextAfter;
      if (text_after.includes("[#]")) {
        text_after = text_after.replace(/\[#\]/g, "");
      } else {
        text_after += "[#]";
      }
      gametree.SetTextAfterOfCurrentMove(text_after);
      updatePGNDivision(false);
    }
  };

  rangeVolume.oninput = function () {
    soundMove.volume = rangeVolume.value;
    soundCapture.volume = rangeVolume.value;
    soundCheck.volume = rangeVolume.value;
    soundTerminal.volume = rangeVolume.value;
  };

  checkboxDests.oninput = function () {
    chessground.set({
      movable: {
        showDests: checkboxDests.checked,
      },
    });
  };

  pSetFen.onclick = onPositionSet;

  buttonSetFen.onclick = onPositionSet;

  buttonNextPosition.onclick = function () {
    if (gametree.CurrentMove.NextNodes[0]) {
      textMoves.value = gametree.GetMoveListOfMove(
        gametree.CurrentMove.NextNodes[0],
      );
      buttonSetFen.click();
    }
  };

  buttonPreviousPosition.onclick = function () {
    if (gametree.CurrentMove.PreviousNode) {
      textMoves.value = gametree.GetMoveListOfMove(
        gametree.CurrentMove.PreviousNode,
      );
      buttonSetFen.click();
    }
  };

  buttonInitialPosition.onclick = function () {
    textMoves.value = "";
    buttonSetFen.click();
  };

  buttonFinalPosition.onclick = function () {
    textMoves.value = gametree.GetCompleteMainLineMoveListOfMove(
      gametree.CurrentMove,
    );
    buttonSetFen.click();
  };

  buttonCurrentPosition.onclick = function () {
    textMoves.value = gametree.GetMainLineMoveList();
    buttonSetFen.click();
  };

  buttonSpecifiedPosition.onclick = function () {
    let level = 0;
    let pointer = gametree.CurrentMove;
    let targetlevel = parseInt(inputHalfMoveNumber.value);
    if (isNaN(targetlevel) || targetlevel < 0) {
      targetlevel = 0;
    }
    while (pointer != gametree.MoveTree.RootNode) {
      pointer = pointer.PreviousNode;
      level++;
    }
    pointer = gametree.CurrentMove;
    if (level > targetlevel) {
      while (level != targetlevel) {
        pointer = pointer.PreviousNode;
        level--;
      }
      textMoves.value = gametree.GetMoveListOfMove(pointer);
      buttonSetFen.click();
    } else if (level < targetlevel) {
      while (level != targetlevel) {
        if (pointer.NextNodes[0]) {
          pointer = pointer.NextNodes[0];
          level++;
        } else {
          break;
        }
      }
      textMoves.value = gametree.GetMoveListOfMove(pointer);
      buttonSetFen.click();
    }
  };

  buttonAnalyzeNextMove.onclick = function () {
    if (gametree.CurrentMove.NextNodes[0]) {
      textMoves.value = gametree.GetMoveListOfMove(
        gametree.CurrentMove.NextNodes[0],
      );
      pSetFen.click();
    }
  };

  buttonAnalyzeRecommendedMove.onclick = function () {
    const currentSig = `${textFen.value.trim()}|${textMoves.value.trim()}|${getColor(board)}`;
    if (!lastPVBestMove || lastPVPosSig != currentSig) {
      window.alert("Engine analysis is not started on displayed position.");
      return;
    } else if (lastPVBestMove == "0000") {
      window.alert("No recommended move on displayed position.");
      return;
    }
    textMoves.value = (textMoves.value + " " + lastPVBestMove).trim();
    pSetFen.click();
  };

  gameStatus.onclick = function () {
    let result = getGameStatus(false);
    if (timerElapsePreviousPlayer) {
      if (result == "PLAYING_WHITE") {
        result = "PLAYING_BLACK";
      } else if (result == "PLAYING_BLACK") {
        result = "PLAYING_WHITE";
      }
    }
    timerElapsePreviousPlayer = false;
    gameStatus.innerText = result;
  };

  setPgnString.onclick = function () {
    let tokens = setPgnString.value.split("\x01");
    let result = pgnutil.ParsePGNMovesToMoveTree(
      tokens[2],
      board.variant(),
      board.is960(),
      tokens[0],
      ffish.Notation.SAN,
      ffish,
    );
    if (result) {
      let headers = tokens[3].split("\x02");
      gametree.MoveTree = result;
      gametree.ClearHistory();
      gametree.OriginalFEN = tokens[0];
      gametree.GoToMoveList(tokens[1]);
      gametree.SetHeaders(
        headers[0],
        headers[1],
        new Date(parseInt(headers[2])),
        parseInt(headers[3]),
        headers[4],
        headers[5],
      );
      if (
        !gametree.CurrentMove.Move.TextAfter.includes("[%end ") &&
        headers[7] != ""
      ) {
        gametree.CurrentMove.Move.TextAfter += `[%end ${headers[6]},${headers[7]}]`;
      } else if (headers[6] != "" && headers[6] != "*" && headers[7] == "") {
        gametree.CurrentMove.Move.TextAfter += `[%end ${headers[6]},unknown]`;
      }
      textFen.value = tokens[0];
      textMoves.value = tokens[1];
      buttonSetFen.click();
    } else {
      window.alert(
        "There is a problem when parsing the PGN. Press Ctrl+Shift+I to see what's going on.",
      );
    }
  };

  buttonGameStart.onclick = function () {
    if (
      (playWhite.checked == true || randomMoverWhite.checked == true) &&
      playBlack.checked == false &&
      randomMoverBlack.checked == false
    ) {
      chessground.set({
        orientation: "black",
      });
      updateInnerCoordinateColor(chessground);
      pBoardOrientation.textContent = "black";
      pBoardOrientation.click();
    }
    if (
      playWhite.checked == false &&
      randomMoverWhite.checked == false &&
      (playBlack.checked == true || randomMoverBlack.checked == true)
    ) {
      chessground.set({
        orientation: "white",
      });
      updateInnerCoordinateColor(chessground);
      pBoardOrientation.textContent = "white";
      pBoardOrientation.click();
    }
    themedetector.SetOrientation(chessground.state.orientation);
    timerElapsePreviousPlayer = false;

    updatePGNDivision(false);

    // Force coordinate recalculation to fix coordinate mapping issues
    // This addresses the bug where coordinates get messed up after game start
    setTimeout(() => {
      forceCoordinateRecalculation();
    }, 100);
  };

  isBoardSetup.onchange = function () {
    if (isBoardSetup.checked) {
      updateChessground(false);
      chessground.set({
        check: [],
        movable: {
          color: "both",
          dests: EmptyMap,
        },
        draggable: {
          enabled: true,
          deleteOnDropOff: true,
        },
      });
    } else {
      buttonSetFen.click();
    }
  };

  isAdvPGNMode.onchange = function () {
    dropdownNotationSystem.dispatchEvent(new Event("change"));
  };

  buttonClearBoard.onclick = function () {
    chessground.state.boardState.pieces.clear();
    chessground.set({
      lastMove: undefined,
    });
  };

  buttonInitialBoardPosition.onclick = function () {
    chessground.set({
      fen: ffish.startingFen(dropdownVariant.value),
      lastMove: undefined,
    });
  };

  buttonAddToPocket.onclick = function () {
    if (
      ffish.capturesToHand(dropdownVariant.value) ||
      ffish.startingFen(dropdownVariant.value).includes("[")
    ) {
      if (dropdownSetPiece.value.includes("+")) {
        window.alert(
          "Promoted pieces cannot go into pockets. If you have dropLoop = true, Please directly add the target piece. For example, if you have a:c, then instead of adding +a, you need to add c.",
        );
      } else if (
        "a" <= dropdownSetPiece.value &&
        dropdownSetPiece.value <= "z"
      ) {
        addPieceToPocket(dropdownSetPiece.value.toLowerCase(), "black");
      } else if (
        "A" <= dropdownSetPiece.value &&
        dropdownSetPiece.value <= "Z"
      ) {
        addPieceToPocket(dropdownSetPiece.value.toLowerCase(), "white");
      } else if (dropdownSetPiece.value == "*") {
        window.alert("Error: Cannot add wall squares to pocket.");
      } else {
        window.alert(
          "Please select a piece (in a letter with or without promotion mark, such as 'a' or '+a') in order to add to pocket.",
        );
      }
    } else {
      window.alert("This variant does not have a pocket.");
    }
  };

  buttonBoardSetupCopyFEN.onclick = function () {
    let FEN = getFEN(true);
    if (FEN == null) {
      return;
    }
    if (validateFEN(FEN, false)) {
      textFen.value = FEN;
      textMoves.value = "";
      copySetFEN.click();
    } else {
      window.alert("Failed to apply the position. There are errors in it.");
    }
  };

  buttonValidatePosition.onclick = function () {
    validateFEN(getFEN(true), true);
  };

  dropdownSetPiece.onchange = function () {
    if (dropdownSetPiece.value == "<move>") {
      chessground.set({
        movable: {
          color: "both",
          dests: EmptyMap,
        },
        draggable: {
          enabled: true,
          deleteOnDropOff: true,
        },
      });
    } else {
      disableBoardMove();
    }
  };

  dropdownPositionVariantType.onchange = function () {
    if (dropdownPositionVariantType.value == "(default)") {
      textFen.value = "";
      textMoves.value = "";
      buttonSetFen.click();
    }
    UpdateVariantsPositionNameDropdown();
    positionInformation.innerHTML = "";
  };

  dropdownPositionVariantName.onchange = function () {
    let VariantTypeDirectory = null;
    let VariantNameDirectory = null;
    if (PositionVariantsDirectory.has(dropdownVariant.value)) {
      VariantTypeDirectory = PositionVariantsDirectory.get(
        dropdownVariant.value,
      );
      if (VariantTypeDirectory.has(dropdownPositionVariantType.value)) {
        VariantNameDirectory = VariantTypeDirectory.get(
          dropdownPositionVariantType.value,
        );
        if (VariantNameDirectory.has(dropdownPositionVariantName.value)) {
          let game = VariantNameDirectory.get(
            dropdownPositionVariantName.value,
          );
          textFen.value = game.FEN;
          positionInformation.innerHTML = game.Description;
          textMoves.value = game.Moves;
          pSetFen.click();
        } else {
          dropdownPositionVariantName.selectedIndex = -1;
          positionInformation.innerHTML = "";
        }
      } else {
        dropdownPositionVariantName.selectedIndex = -1;
        positionInformation.innerHTML = "";
      }
    } else {
      dropdownPositionVariantName.selectedIndex = -1;
      positionInformation.innerHTML = "";
    }
    recordedmultipv = 1;
  };

  buttonAboutPosition.onclick = function () {
    if (dropdownPositionVariantName.selectedIndex == -1) {
      window.alert(
        'Please select a position in "Position Variant Name"!\nIf there is nothing, it means that this chess variant does not have any position variant!',
      );
      return;
    }
    window.alert(
      dropdownVariant.value +
        "\\" +
        dropdownPositionVariantType.value +
        "\\" +
        dropdownPositionVariantName.value +
        ":\n" +
        positionInformation.innerHTML,
    );
  };

  positionVariantTxt.onchange = onSelectPositionVariantsFile;

  dragMove.onchange = function () {
    chessground.set({
      draggable: {
        enabled: dragMove.checked || isBoardSetup.checked,
      },
    });
  };

  clickClickMove.onchange = function () {
    if (clickClickMove.checked == true) {
      chessground.set({
        selectable: {
          enabled: true,
        },
      });
    } else {
      chessground.set({
        selectable: {
          enabled: false,
        },
      });
    }
  };

  buttonReset.onclick = function () {
    textFen.value = "";
    textMoves.value = "";
    gametree.ClearMoves();
    gametree.ClearHistory();
    dropdownPositionVariantType.selectedIndex = 0;
    dropdownPositionVariantType.onchange();
    clearMovesList();
  };

  buttonRestart.onclick = function () {
    textMoves.value = "";
    gametree.ClearMoves();
    gametree.ClearHistory();
    buttonSetFen.click();
  };

  buttonPassMove.onclick = function () {
    if (
      chessground.state.movable.color == "both" ||
      chessground.state.movable.color == undefined
    ) {
      return;
    }
    const moves = board
      .legalMoves()
      .trim()
      .split(" ")
      .filter((element) => {
        if (typeof element != "string" || element.length < 4) {
          return false;
        }
        const files = element.split(/[0-9]+/).filter((elem1) => {
          return elem1 != "";
        });
        const ranks = element.split(/[a-z]+/).filter((elem1) => {
          return elem1 != "";
        });
        return files[0] == files[1] && ranks[0] == ranks[1];
      });
    if (moves == null || moves.length == 0) {
      alert(
        "Cannot pass your turn currently. This variant does not allow passing or there are restrictions on passing your turn.",
      );
      return;
    }
    const passmove = {
      orig: moves[0].match(/[a-z]+[0-9]+/g)[0],
      dest: moves[0].match(/[a-z]+[0-9]+/g)[1],
    };
    if (passmove.orig == null || passmove.dest == null) {
      return;
    }
    afterChessgroundMove(passmove.orig, passmove.dest, {
      premove: false,
      ctrlKey: false,
      holdTime: 0,
      captured: {
        role: null,
        color: null,
        promoted: false,
      },
      predrop: false,
    });
  };

  buttonPlaceWall.onclick = function () {
    if (
      chessground.state.movable.color == "both" ||
      chessground.state.movable.color == undefined
    ) {
      return;
    }
    const moves = board
      .legalMoves()
      .trim()
      .split(" ")
      .filter((element) => {
        if (
          typeof element != "string" ||
          element.length < 4 ||
          !element.includes(",")
        ) {
          return false;
        }
        let elem = element.substring(0, element.indexOf(","));
        const files = elem.split(/[0-9]+/).filter((elem1) => {
          return elem1 != "";
        });
        const ranks = elem.split(/[a-z]+/).filter((elem1) => {
          return elem1 != "";
        });
        return files[0] == files[1] && ranks[0] == ranks[1];
      });
    if (moves == null || moves.length == 0) {
      alert(
        "Cannot place a wall without moving currently. This variant does not allow walling or there are restrictions on walling without moving.",
      );
      return;
    }
    const wallmove = {
      orig: moves[0].match(/[a-z]+[0-9]+/g)[0],
      dest: moves[0].match(/[a-z]+[0-9]+/g)[1],
    };
    if (wallmove.orig == null || wallmove.dest == null) {
      return;
    }
    afterChessgroundMove(wallmove.orig, wallmove.dest, {
      premove: false,
      ctrlKey: false,
      holdTime: 0,
      captured: {
        role: null,
        color: null,
        promoted: false,
      },
      predrop: false,
    });
  };

  engineOutput.onclick = function () {
    if (isAnalysis.checked == false) {
      return;
    }
    let text = engineOutput.value;
    let multipvid = 0;
    let bestpv = 0;
    let index = 0;
    if (/( upperbound )|( lowerbound )/.test(text)) {
      return;
    }
    if (text.includes(" multipv ")) {
      let textparselist = text.split(singleblankmatcher);
      let pvindex = textparselist.indexOf("pv");
      if (pvindex < 0) {
        return;
      }
      let pvmove = textparselist[pvindex + 1];
      let tmpboard = new ffish.Board(
        board.variant(),
        board.fen(),
        board.is960(),
      );
      if (!tmpboard.push(pvmove)) {
        tmpboard.delete();
        return;
      }
      tmpboard.delete();
      multipvid =
        parseInt(textparselist[textparselist.indexOf("multipv") + 1]) - 1;
      if (multipvid + 1 > recordedmultipv) {
        recordedmultipv = multipvid + 1;
      }
    }
    let bestmove = "";
    let ponder = "";
    if (text.includes(" score ") && text.includes(" pv ")) {
      let textparselist = text.split(singleblankmatcher);
      let scoreindex = textparselist.indexOf("score");
      let pvindex = textparselist.indexOf("pv");
      let evaltext = textparselist.at(scoreindex + 1);
      if (evaltext == "mate") {
        let matenum = parseInt(textparselist.at(scoreindex + 2));
        if (!board.turn()) {
          matenum = matenum * -1;
        }
        multipvrecord[multipvid][0] = true;
        multipvrecord[multipvid][1] = matenum;
        evaluationindex[multipvid] = mateevalfactor / matenum;
        evaluation = evaluationindex[multipvid];
      } else if (evaltext == "cp") {
        let evalval = parseInt(textparselist.at(scoreindex + 2)) / 100;
        if (!board.turn()) {
          evalval = evalval * -1;
        }
        multipvrecord[multipvid][0] = false;
        multipvrecord[multipvid][1] = evalval;
        evaluationindex[multipvid] = evalval;
        evaluation = evaluationindex[multipvid];
      } else {
        multipvrecord[multipvid][0] = false;
        multipvrecord[multipvid][1] = 0;
        evaluationindex[multipvid] = 0;
        console.log("Detected bad evaluation");
      }
      let moves = textparselist.slice(pvindex + 1);
      if (moves.length == 0) {
        return;
      } else if (moves.length == 1) {
        bestmove = moves[0];
      } else {
        bestmove = moves[0];
        ponder = moves[1];
      }
      multipvrecord[multipvid][2] = bestmove;
      multipvrecord[multipvid][3] = ponder;
      multipvrecord[multipvid][4] = moves.join(" ");
      index = textparselist.indexOf("depth");
      if (index > 0) {
        multipvrecord[multipvid][5] = parseInt(textparselist[index + 1]);
      } else {
        multipvrecord[multipvid][5] = -1;
      }
      index = textparselist.indexOf("seldepth");
      if (index > 0) {
        multipvrecord[multipvid][6] = parseInt(textparselist[index + 1]);
      } else {
        multipvrecord[multipvid][6] = -1;
      }
      //Update Evaluation Section
      let k = 0;
      let seldepthlist = [];
      let depthlist = [];
      if (isAdvPGNMode.checked) {
        if (multipvminiboardtimer == null) {
          multipvminiboardtimer = setTimeout(() => {
            pvinfo.innerHTML = "";
            pvinfo.appendChild(multipvminiboardhandler.GetMovesDivElement());
            multipvminiboardtimer = null;
          }, 1000);
        }
        multipvminiboardhandler.SetValidPrincipalVariationCount(
          recordedmultipv,
        );
        for (k = 0; k < recordedmultipv; k++) {
          multipvminiboardhandler.SetPrincipalVariation(
            k + 1,
            board.variant(),
            board.is960(),
            board.fen(),
            multipvrecord[k][4],
            multipvrecord[k][0],
            multipvrecord[k][1],
            multipvrecord[k][5],
            multipvrecord[k][6],
          );
          depthlist.push(multipvrecord[k][5]);
          seldepthlist.push(multipvrecord[k][6]);
        }
      } else {
        let pvinfostr = "";
        let showevalnum = "";
        for (k = 0; k < recordedmultipv; k++) {
          if (multipvrecord[k][0]) {
            if (multipvrecord[k][1] > 0) {
              showevalnum = `#+${parseInt(multipvrecord[k][1])}`;
            } else {
              showevalnum = `#${parseInt(multipvrecord[k][1])}`;
            }
          } else {
            if (multipvrecord[k][1] > 0) {
              showevalnum = `+${multipvrecord[k][1].toFixed(2)}`;
            } else {
              showevalnum = multipvrecord[k][1].toFixed(2).toString();
            }
          }
          pvinfostr += `${k > 0 ? "<hr />" : ""}<evalnum>${showevalnum}</evalnum><span class="pvmeta">d${multipvrecord[k][5] > -1 ? multipvrecord[k][5] : "?"}/${multipvrecord[k][6] > -1 ? multipvrecord[k][6] : "?"}</span> ${getNotation(
            dropdownNotationSystem[dropdownNotationSystem.selectedIndex].value,
            board.variant(),
            board.fen(),
            board.is960(),
            multipvrecord[k][4],
            false,
          )}\n`;
          depthlist.push(multipvrecord[k][5]);
          seldepthlist.push(multipvrecord[k][6]);
        }
        pvinfo.innerHTML = pvinfostr;
      }
      let nodeinfo = "❓";
      index = textparselist.indexOf("nodes");
      if (index > 0) {
        nodeinfo = textparselist[index + 1];
      }
      let npsinfo = "❓";
      index = textparselist.indexOf("nps");
      if (index > 0) {
        npsinfo = textparselist[index + 1];
      }
      let timeinfo = "❓";
      index = textparselist.indexOf("time");
      if (index > 0) {
        timeinfo = textparselist[index + 1];
      }
      let maxdepth = Math.max(...depthlist);
      let maxseldepth = Math.max(...seldepthlist);
      evalinfo.textContent = `depth ${maxdepth > 0 ? maxdepth : "❓"}/${maxseldepth > 0 ? maxseldepth : "❓"} · ${formatCount(nodeinfo)} nodes · ${formatCount(npsinfo)} n/s · ${formatSecondsShort(timeinfo)}`;
      evalinfo.title = `Depth (Average depth): ${maxdepth > 0 ? maxdepth : "❓"}\nSelective Depth (Max depth): ${maxseldepth > 0 ? maxseldepth : "❓"}\nSearched Nodes: ${nodeinfo} positions\nNodes Searched Per Second: ${npsinfo} nodes/s\nTime Elapsed: ${timeinfo} ms`;
    } else if (text.includes("bestmove")) {
      let textparselist = text.split(" ");
      if (board.turn()) {
        bestpv = evaluationindex.indexOf(
          Math.max(...evaluationindex.slice(0, recordedmultipv)),
        );
      } else {
        bestpv = evaluationindex.indexOf(
          Math.min(...evaluationindex.slice(0, recordedmultipv)),
        );
      }
      if (bestpv < 0) {
        bestpv = 0;
      }
      bestmove = textparselist[1];
      if (textparselist[3] != undefined && textparselist[3] != "0000") {
        ponder = textparselist[3];
      }
      multipvrecord[bestpv][2] = bestmove;
      multipvrecord[bestpv][3] = ponder;
    } else if (text.includes("score mate 0")) {
      if (board.turn()) {
        evaluationBar.style.width = "0%";
        evalscore.innerText = "Checkmate";
      } else {
        evaluationBar.style.width = "100%";
        evalscore.innerText = "Checkmate";
      }
      last_evaluation = "#0";
      evalcomment.textContent = getEvaluationDescription(0, true);
      return;
    } else {
      return;
    }
    if (board.turn()) {
      bestpv = evaluationindex.indexOf(
        Math.max(...evaluationindex.slice(0, recordedmultipv)),
      );
    } else {
      bestpv = evaluationindex.indexOf(
        Math.min(...evaluationindex.slice(0, recordedmultipv)),
      );
    }
    if (bestpv < 0) {
      bestpv = 0;
    }
    console.log("Best PV:", bestpv + 1);
    if (multipvrecord[bestpv][0]) {
      let matemoves = multipvrecord[bestpv][1];
      if (isNaN(matemoves) || matemoves == null) {
        evaluationBar.style.width = "50%";
        evalscore.textContent = "Mate in ❓";
        evalcomment.textContent = "The evaluation is invalid";
      } else {
        if (matemoves > 0) {
          evaluationBar.style.width = "100%";
          evalscore.textContent = `Mate in ${matemoves}`;
          last_evaluation = `#+${matemoves}`;
        } else if (matemoves < 0) {
          evaluationBar.style.width = "0%";
          evalscore.textContent = `Mate in ${-matemoves}`;
          last_evaluation = `#${matemoves}`;
        } else {
          if (board.turn()) {
            evaluationBar.style.width = "0%";
            evalscore.textContent = "Checkmate";
          } else {
            evaluationBar.style.width = "100%";
            evalscore.textContent = "Checkmate";
          }
          last_evaluation = "#0";
        }
        evalcomment.textContent = getEvaluationDescription(matemoves, true);
      }
    } else {
      evaluation = multipvrecord[bestpv][1];
      if (isNaN(evaluation) || evaluation == null) {
        evalscore.textContent = "❓";
        evaluationBar.style.width = "50%";
        evalcomment.textContent = "The evaluation is invalid";
      } else {
        if (evaluation > 0) {
          evalscore.textContent = last_evaluation =
            "+" + evaluation.toFixed(2).toString();
        } else {
          evalscore.textContent = last_evaluation = evaluation.toFixed(2);
        }
        if (evaluation <= -9.8) {
          evaluationBar.style.width = "1%";
        } else if (evaluation >= 9.8) {
          evaluationBar.style.width = "99%";
        } else {
          evaluationBar.style.width = `${parseInt((evaluation * 100 + 1000) / 20)}%`;
        }
        evalcomment.textContent = getEvaluationDescription(evaluation, false);
      }
    }
    bestmove = multipvrecord[bestpv][2];
    ponder = multipvrecord[bestpv][3];
    if (bestmove) {
      // Record latest PV best move and position signature for Spacebar action
      lastPVBestMove = bestmove;
      lastPVPosSig = `${textFen.value.trim()}|${textMoves.value.trim()}|${getColor(board)}`;
      lastPVTime = Date.now();
      if (ponder) {
        highlightMoveOnBoard(
          [board.turn(), !board.turn()],
          chessground,
          [bestmove, ponder],
          ["blue", "red"],
          ["TopRight", "TopLeft"],
          true,
        );
      } else {
        highlightMoveOnBoard(
          [board.turn()],
          chessground,
          [bestmove],
          ["blue"],
          ["TopRight"],
          true,
        );
      }
    }
  };

  isAnalysis.onchange = function () {
    recordedmultipv = 1;
    if (isAnalysis.checked) {
      //console.log("Observing.");
    } else {
      //console.log("Clear auto shapes.");
      chessground.setAutoShapes([]);
    }
    dropdownVisualEffect.dispatchEvent(new Event("change"));
  };

  dropdownBoardCoordinate.onchange = function () {
    let index = dropdownBoardCoordinate.selectedIndex;
    chessground.set({ notation: index });
    chessground_mini.set({ notation: index });
    let containerdiv = document.getElementById("chessground-container-div");
    if (index >= 1 && index <= 3) {
      containerdiv.classList.add("shogi");
      containerdiv.classList.remove("xiangqi");
    } else if (index == 5 || index == 6) {
      containerdiv.classList.add("xiangqi");
      containerdiv.classList.remove("shogi");
    } else {
      containerdiv.classList.remove("xiangqi");
      containerdiv.classList.remove("shogi");
    }
    redrawChessground();
  };

  buttonsearchmove.onclick = function () {
    const legalmovesstr = board.legalMoves();
    if (legalmovesstr == "") {
      window.alert("There is no legal move in this position.");
      return;
    }
    const legalmoves = legalmovesstr.trim().split(" ");
    const moves = filterMoves(
      legalmoves,
      movesearchfilter.value,
      issearchregexp.checked,
      origfilter.value,
      destfilter.value,
      isdrop.checked,
      haswallgating.checked,
      haspiecechange.checked,
    );
    console.log(moves);
    if (moves == null || moves == undefined) {
      return;
    }
    while (availablemovelist.length > 1) {
      availablemovelist.removeChild(availablemovelist[1]);
    }
    let notationindex = simplenotations.indexOf(
      dropdownNotationSystem[dropdownNotationSystem.selectedIndex].value,
    );
    let notation = ffish.Notation.SAN;
    if (notationindex >= 0) {
      notation = ffishnotationobjects[notationindex];
    }
    moves.forEach((val) => {
      let opt = document.createElement("option");
      opt.value = val;
      opt.text = `${val} (${board.sanMove(val, notation)})`;
      availablemovelist.appendChild(opt);
    });
    if (moves.length < 1) {
      window.alert("No matches found with given search restriction.");
    }
    searchresultinfo.innerText = `Found ${moves.length} result(s).`;
  };

  buttonmakemove.onclick = function () {
    const move = availablemovelist[availablemovelist.selectedIndex].value;
    if (move == null || move == undefined || move == "") {
      window.alert(
        "Select a move in the drop down list first. If there are no moves listed, search for a move first. You can read the note to know how to make a search.",
      );
      return;
    }
    if (!board.push(move)) {
      window.alert("Cannot make the selected move as it's illegal.");
      return;
    }

    afterMove(move, isCapture(board, move));
  };

  buttonhighlightmove.onclick = function () {
    const move = availablemovelist[availablemovelist.selectedIndex].value;
    if (move == null || move == undefined || move == "") {
      window.alert(
        "Select a move in the drop down list first. If there are no moves listed, search for a move first. You can read the note to know how to make a search.",
      );
      return;
    }
    highlightMoveOnBoard(
      [board.turn()],
      chessground,
      [move],
      ["yellow"],
      ["TopRight"],
      true,
    );
  };

  dropdownNotationSystem.onchange = function () {
    updatePGNDivision(false);
  };

  pRandomMoverGo.onclick = function () {
    let movelist = textMoves.value.trim().split(/[ ]+/);
    let legalmoves = board.legalMoves().trim().split(/[ ]+/);
    movelist.push(legalmoves[Math.floor(Math.random() * legalmoves.length)]);
    textMoves.value = movelist.join(" ");
    pSetFen.click();
  };

  dropdownVisualEffect.onchange = dropdownVisualEffectPerspective.onchange =
    function () {
      updateChessground(false);
      setTimeout(() => {
        let elem = document.getElementById("gameresultcontainermini");
        while (elem) {
          chessgroundMiniBoardWrapper.removeChild(elem);
          elem = document.getElementById("gameresultcontainermini");
        }
      }, 20);
    };

  checkBoxInnerCoordinate.oninput = function () {
    updateInnerCoordinateColor(chessground);
  };

  buttonGenerateImage.onclick = function () {
    if (buttonGenerateImage.disabled) {
      return;
    }
    buttonGenerateImage.disabled = true;
    textImageGenerationProgress.textContent = "Busy.";
    let width = parseInt(inputImageWidth.value);
    let height = parseInt(inputImageHeight.value);
    let quality = parseFloat(inputImageQuality.value);
    let framedelay = parseInt(inputFrameDuration.value);
    let mode =
      dropdownGenerationMode[dropdownGenerationMode.selectedIndex].value;
    if (isNaN(width) || width <= 0) {
      width = 640;
    }
    if (isNaN(height) || height <= 0) {
      height = 640;
    }
    if (isNaN(quality) || quality < 0 || quality > 1) {
      quality = 0.9;
    }
    if (isNaN(framedelay) || framedelay <= 0) {
      framedelay = 1000;
    }
    GenerateBoardImage(
      mode,
      width,
      height,
      checkboxKeepAspectRatio.checked,
      (canvaslist) => {
        if (canvaslist instanceof Array) {
          let list = canvaslist.filter(
            (val) => val instanceof HTMLCanvasElement,
          );
          let i = 0;
          const filetype =
            dropdownImageFileType[dropdownImageFileType.selectedIndex].value;
          if (filetype == "JPEG" || filetype == "PNG") {
            const mimetype = filetype == "PNG" ? "image/png" : "image/jpeg";
            if (mode == "all") {
              let storedfilecount = 0;
              let totalfilecount = list.length;
              const zipfile = new ZIP();
              for (i = 0; i < list.length; i++) {
                (function (index) {
                  list[index].toBlob(
                    (blob) => {
                      blob.arrayBuffer().then((buf) => {
                        zipfile.file(
                          `board-frame-${index}.${filetype.toLowerCase()}`,
                          buf,
                          { binary: true, compression: "DEFLATE" },
                        );
                        storedfilecount++;
                        textImageGenerationProgress.textContent = `Generating images... (Progress: ${storedfilecount}/${totalfilecount})`;
                        if (storedfilecount >= totalfilecount) {
                          zipfile
                            .generateAsync({ type: "blob" })
                            .then((blob) => {
                              const url = URL.createObjectURL(blob);
                              const a = document.createElement("a");
                              a.href = url;
                              a.download = "board.zip";
                              document.body.appendChild(a);
                              a.click();
                              document.body.removeChild(a);
                              buttonGenerateImage.disabled = false;
                              textImageGenerationProgress.textContent =
                                "Ready.";
                              setTimeout(() => {
                                URL.revokeObjectURL(url);
                              }, 100);
                            });
                        }
                      });
                    },
                    mimetype,
                    quality,
                  );
                })(i);
              }
            } else {
              list[0].toBlob(
                (blob) => {
                  const url = URL.createObjectURL(blob);
                  const a = document.createElement("a");
                  a.href = url;
                  a.download = `board.${filetype.toLowerCase()}`;
                  document.body.appendChild(a);
                  a.click();
                  document.body.removeChild(a);
                  buttonGenerateImage.disabled = false;
                  textImageGenerationProgress.textContent = "Ready.";
                  setTimeout(() => {
                    URL.revokeObjectURL(url);
                  }, 100);
                },
                mimetype,
                quality,
              );
            }
          } else if (filetype == "GIF") {
            const gif = new GIF({
              workers: 2,
              quality: 101 - Math.round(quality * 100),
            });
            for (i = 0; i < list.length; i++) {
              gif.addFrame(list[i], { delay: framedelay });
            }
            gif.on("finished", function (blob) {
              const url = URL.createObjectURL(blob);
              const a = document.createElement("a");
              a.href = url;
              a.download = "board.gif";
              document.body.appendChild(a);
              a.click();
              document.body.removeChild(a);
              buttonGenerateImage.disabled = false;
              textImageGenerationProgress.textContent = "Ready.";
              setTimeout(() => {
                URL.revokeObjectURL(url);
              }, 100);
            });
            gif.on("progress", function (percentage) {
              textImageGenerationProgress.textContent = `Generating GIF... (Progress: ${(percentage * 100).toFixed(2)}%)`;
            });
            gif.render();
          }
        }
      },
    );
  };

  buttonExitImageGenerator.onclick = function () {
    imageGenerator.classList.add("hidden");
  };

  terminationSet.onclick = function () {
    let result = GameResults[dropdownPGNResult.selectedIndex];
    let termination = GameTerminations[dropdownPGNTermination.selectedIndex];
    gametree.CurrentMove.Move.TextAfter =
      gametree.CurrentMove.Move.TextAfter.replace(/\[%end.*?\]/g, "");
    if (termination != "undefined") {
      gametree.SetTextAfterOfCurrentMove(
        gametree.CurrentMove.Move.TextAfter + `[%end ${result},${termination}]`,
      );
    }
    updatePGNDivision(false);
  };

  buttonPGNHeaderSave.onclick = function () {
    let date = new Date();
    let datestr = inputPGNDate.value.split("-");
    let round = parseInt(inputPGNRound.value);
    if (datestr.length == 3) {
      date.setFullYear(
        parseInt(datestr[0]),
        parseInt(datestr[1]) - 1,
        parseInt(datestr[2]),
      );
    }
    if (isNaN(round) || round < 1) {
      round = 1;
    }
    gametree.SetHeaders(
      inputPGNEvent.value,
      inputPGNSite.value,
      date,
      round,
      inputPGNWhiteName.value,
      inputPGNBlackName.value,
    );
    pgnHeader.classList.add("hidden");
    updatePGNDivision(false);
  };

  buttonPGNHeaderCancel.onclick = function () {
    pgnHeader.classList.add("hidden");
  };

  buttonPgnSymbolsSave.onclick = function () {
    let result = [];
    if (dropdownMoveCommentarySymbols.selectedIndex > 0) {
      result.push(
        dropdownMoveCommentarySymbols[
          dropdownMoveCommentarySymbols.selectedIndex
        ].value,
      );
    }
    if (dropdownPositionCommentarySymbols.selectedIndex > 0) {
      result.push(
        dropdownPositionCommentarySymbols[
          dropdownPositionCommentarySymbols.selectedIndex
        ].value,
      );
    }
    if (checkboxSpaceAdvantageSymbol.checked) {
      result.push("○");
    }
    if (checkboxDevelopmentSymbol.checked) {
      result.push("↑↑");
    }
    if (checkboxInitiativeSymbol.checked) {
      result.push("↑");
    }
    if (checkboxAttackSymbol.checked) {
      result.push("→");
    }
    if (checkboxWithCompensationSymbol.checked) {
      result.push("=/∞");
    }
    if (checkboxCounterplaySymbol.checked) {
      result.push("⇆");
    }
    if (checkboxTimeTroubleSymbol.checked) {
      result.push("⨁");
    }
    if (checkboxWithTheIdeaSymbol.checked) {
      result.push("∆");
    }
    if (checkboxNoveltySymbol.checked) {
      result.push("N");
    }
    gametree.SetSymbolsOfCurrentMove(result);
    pgnSymbols.classList.add("hidden");
    updatePGNDivision(false);
  };

  buttonPgnSymbolsCancel.onclick = function () {
    pgnSymbols.classList.add("hidden");
  };

  buttonPgnTextSave.onclick = function () {
    if (pgnTextTitle.textContent.includes("Text Before")) {
      gametree.SetTextBeforeOfCurrentMove(textareaPgnTextInput.value);
    } else {
      gametree.SetTextAfterOfCurrentMove(textareaPgnTextInput.value);
    }
    updatePGNDivision(false);
    pgnText.classList.add("hidden");
  };

  buttonPgnTextCancel.onclick = function () {
    pgnText.classList.add("hidden");
  };

  buttonSetEvaluation.onclick = function () {
    if (gametree.CurrentMove.Move.TextAfter.includes("[%eval")) {
      gametree.CurrentMove.Move.TextAfter =
        gametree.CurrentMove.Move.TextAfter.replace(/\[\%eval.*?\]/g, "");
    }
    gametree.CurrentMove.Move.TextAfter += `[%eval ${last_evaluation}]`;
    updatePGNDivision(false);
  };

  dropdownPGNStyle.addEventListener("change", () => {
    updatePGNDivision(false);
  });

  updateInnerCoordinateColor(chessground);

  updateChessground(true);
}); // Chessground helper functions

const onSelectPositionVariantsFile = async (e) => {
  const selected = e.currentTarget.files[0];
  if (selected) {
    const reader = new FileReader();
    reader.onload = function () {
      console.log(reader.result);
      if (LoadPositionVariant("client", reader.result)) {
        UpdateVariantsPositionTypeDropdown();
      }
    };
    reader.readAsText(selected);
  }
};

function getFEN(deleteinvalidpocket) {
  let FEN = chessground.getFen();
  let width = chessground.state.dimensions.width;
  let height = chessground.state.dimensions.height;
  if (
    deleteinvalidpocket &&
    !ffish.capturesToHand(dropdownVariant.value) &&
    !ffish.startingFen(dropdownVariant.value).includes("[")
  ) {
    FEN = FEN.replace(/\[[A-Za-z]*\]/, "");
  }
  if (dropdownSideToMove.value == "First Mover") {
    FEN += " w";
  } else if (dropdownSideToMove.value == "Second Mover") {
    FEN += " b";
  }
  let castling = " ";
  if (whiteOO.checked) {
    castling += "K";
  }
  if (whiteOOO.checked) {
    castling += "Q";
  }
  if (blackOO.checked) {
    castling += "k";
  }
  if (blackOOO.checked) {
    castling += "q";
  }
  if (seirawanGatingFiles.value.length > 0) {
    if (/^[A-Za-z]*$/.test(seirawanGatingFiles.value)) {
      let matcher = new RegExp(
        "[^A-" +
          files[width - 1].toUpperCase() +
          "a-" +
          files[width - 1].toLowerCase() +
          "]",
      );
      if (!matcher.test(seirawanGatingFiles.value)) {
        castling += seirawanGatingFiles.value;
      } else {
        window.alert(
          `Bad Seirawan gating files: File out of range. File range is A-${files[
            width - 1
          ].toUpperCase()}`,
        );
        return null;
      }
    } else {
      window.alert(
        "Bad Seirawan gating files: All files should be given in letters. (e.g. ABCDabcd)",
      );
      return null;
    }
  }
  if (castling == " ") {
    castling = " -";
  }
  FEN += castling;
  if (enPassantFile.value.length < 1 || enPassantRank.value.length < 1) {
    FEN += " -";
  } else if (
    enPassantFile.value > 0 &&
    enPassantFile.value <= width &&
    enPassantRank.value > 0 &&
    enPassantRank.value <= height
  ) {
    FEN += " " + files[enPassantFile.value - 1] + enPassantRank.value;
  } else {
    window.alert("Bad en passant file or rank number.");
    return null;
  }
  if (
    whiteRemainingChecks.value.length > 0 &&
    blackRemainingChecks.value.length > 0
  ) {
    if (ffish.startingFen(dropdownVariant.value).split(" ").length != 7) {
      window.alert("This variant does not have check number limits.");
      return null;
    }
    if (whiteRemainingChecks.value > 0 && blackRemainingChecks.value > 0) {
      FEN += ` ${whiteRemainingChecks.value}+${blackRemainingChecks.value}`;
    } else {
      window.alert(
        "Bad remaining checks. Remaining checks should be larger than 0.",
      );
      return null;
    }
  }
  if (halfMoveClock.value.length > 0) {
    if (halfMoveClock.value >= 0) {
      FEN += ` ${halfMoveClock.value}`;
    } else {
      window.alert(
        "Bad half move clock. Half move clock should be larger than or equal to 0.",
      );
      return null;
    }
  } else {
    FEN += " 0";
  }
  if (currentMoveNumber.value.length > 0) {
    if (currentMoveNumber.value > 0) {
      FEN += ` ${currentMoveNumber.value}`;
    } else {
      window.alert(
        "Bad current move number. Current move number should be larger than 0.",
      );
      return null;
    }
  } else {
    FEN += " 1";
  }
  console.log(FEN);
  return FEN;
}

function validateFEN(FEN, showNoErrorMessage) {
  if (FEN == null) {
    return false;
  }
  let result = ffish.validateFen(FEN, board.variant(), board.is960());
  if (result >= 0) {
    if (showNoErrorMessage) {
      window.alert("No errors found.");
    }
    return true;
  }
  if (result == -14) {
    window.alert("Error: Invalid counting rule specification.");
    return false;
  }
  if (result == -13) {
    window.alert("Error: Invalid check count specification.");
    return false;
  }
  if (result == -12) {
    window.alert("Error: Pieces without promoted type are in promoted form.");
    return false;
  }
  if (result == -11) {
    window.alert("Error: Syntax error in FEN string.");
    return false;
  }
  if (result == -10) {
    window.alert("Error: Contains invalid piece characters or syntax error.");
    return false;
  }
  if (result == -9) {
    window.alert("Error: King pieces are next to each other.");
    return false;
  }
  if (result == -8) {
    window.alert("Error: Invalid row or column count.");
    return false;
  }
  if (result == -7) {
    window.alert("Error: Invalid piece character in pocket.");
    return false;
  }
  if (result == -6) {
    window.alert("Error: Invalid side to move specification.");
    return false;
  }
  if (result == -5) {
    window.alert("Error: Invalid castling specification.");
    return false;
  }
  if (result == -4) {
    window.alert("Error: Invalid en passant square.");
    return false;
  }
  if (result == -3) {
    window.alert("Error: Inavlid king piece count.");
    return false;
  }
  if (result == -2) {
    window.alert("Error: Invalid half move clock.");
    return false;
  }
  if (result == -1) {
    window.alert("Error: Invalid move counter.");
    return false;
  }
}

function LoadPositionVariant(side, file) {
  function StartLoad(data, dispatchevent) {
    let VariantTypeDirectory = new Map();
    let VariantNameDirectory = new Map();
    //This creates a tree structure to store position variants
    //it looks like this:
    //<Root dir: PositionVariantsDirectory>  //Items are classified by chess variant names
    //    <Sub dir1: VariantTypeDirectory>  //Items are classified by position variant types, e.g. Mate in X, Handicaps, etc.
    //        <Sub Sub dir1: VariantNameDirectory>  //Items are classified by the position variant name provided in the file.
    //            <File: VariantPositionItem>  //This contains the FEN and the description
    //        <Sub Sub dir2: VariantNameDirectory>
    //            <File: VariantPositionItem>
    //            ...
    //    <Sub dir2: VariantTypeDirectory>
    //        <Sub Sub dir: VariantNameDirectory>
    //            ...
    //Syntax for each line: <chess variant name>|<position variant type>|<position variant name>|<FEN>|<description>
    data = data.replace(/\r\n/g, "\n");
    data = data.replace(/\r/g, "\n");
    let rawText = data.split("\n");
    let variantsettings = "";
    let i = 0;
    for (i = 0; i < rawText.length; i++) {
      if (rawText[i].length < 1 || rawText[i].charAt(0) == "#") {
        continue;
      }
      variantsettings = rawText[i].trim().split("||");
      if (variantsettings.length != 5 && variantsettings.length != 6) {
        console.warn(
          `At line ${i} in paragraph of <position variant file>: Bad syntax\n`,
        );
        continue;
      }
      if (PositionVariantsDirectory.has(variantsettings[0])) {
        VariantTypeDirectory = PositionVariantsDirectory.get(
          variantsettings[0],
        );
      } else {
        VariantTypeDirectory = new Map();
      }
      if (VariantTypeDirectory.has(variantsettings[1])) {
        VariantNameDirectory = VariantTypeDirectory.get(variantsettings[1]);
      } else {
        VariantNameDirectory = new Map();
      }
      if (VariantNameDirectory.has(variantsettings[2])) {
        console.warn(
          `Variant "<ROOT>\\${variantsettings[0]}\\${variantsettings[1]}\\${variantsettings[2]}" already exists. This position variant will not get loaded.\n`,
        );
        continue;
      }
      if (variantsettings.length == 5) {
        VariantNameDirectory.set(variantsettings[2], {
          FEN: variantsettings[3],
          Moves: "",
          Description: variantsettings[4].replace("\\n", "\n"),
        });
      } else if (variantsettings.length == 6) {
        VariantNameDirectory.set(variantsettings[2], {
          FEN: variantsettings[3],
          Moves: variantsettings[4],
          Description: variantsettings[5].replace("\\n", "\n"),
        });
      }

      VariantTypeDirectory.set(variantsettings[1], VariantNameDirectory);
      PositionVariantsDirectory.set(variantsettings[0], VariantTypeDirectory);
    }
    console.log("PositionVariants:", PositionVariantsDirectory);
    if (dispatchevent) {
      document.dispatchEvent(new Event("positionvariantsloaded"));
    }
    return true;
  }
  if (side == "server") {
    return getFileFromServer("./positionvariants.txt", (res) => {
      console.log("res:", res);
      StartLoad(res, true);
    });
  } else if (side == "client") {
    if (file == null || file == undefined) {
      console.warn("Empty files provided.");
      return false;
    }
    StartLoad(file, false);
    return true;
  }
  return false;
}

function UpdateVariantsPositionTypeDropdown() {
  while (dropdownPositionVariantType.length > 1) {
    dropdownPositionVariantType.remove(1);
  }
  let VariantTypeDirectory = null;
  let VariantTypeList = [];
  let i = 0;
  let option = null;
  let VariantName = checkboxFischerRandom.checked
    ? dropdownVariant.value + "960"
    : dropdownVariant.value;
  if (PositionVariantsDirectory.has(VariantName)) {
    VariantTypeDirectory = PositionVariantsDirectory.get(VariantName);
    VariantTypeList = [...VariantTypeDirectory];
    for (i = 0; i < VariantTypeList.length; i++) {
      option = document.createElement("option");
      option.text = VariantTypeList[i][0];
      option.value = VariantTypeList[i][0];
      dropdownPositionVariantType.add(option);
    }
  }
  dropdownPositionVariantType.selectedIndex = 0;
}

function UpdateVariantsPositionNameDropdown() {
  while (dropdownPositionVariantName.length > 0) {
    dropdownPositionVariantName.remove(0);
  }
  let VariantTypeDirectory = null;
  let VariantNameDirectory = null;
  let i = 0;
  let option = null;
  let VariantName = checkboxFischerRandom.checked
    ? dropdownVariant.value + "960"
    : dropdownVariant.value;
  let VariantNameList = [];
  if (PositionVariantsDirectory.has(VariantName)) {
    VariantTypeDirectory = PositionVariantsDirectory.get(VariantName);
    if (VariantTypeDirectory.has(dropdownPositionVariantType.value)) {
      VariantNameDirectory = VariantTypeDirectory.get(
        dropdownPositionVariantType.value,
      );
      VariantNameList = [...VariantNameDirectory];
      for (i = 0; i < VariantNameList.length; i++) {
        option = document.createElement("option");
        option.text = VariantNameList[i][0];
        option.value = VariantNameList[i][0];
        dropdownPositionVariantName.add(option);
      }
    }
  }
  dropdownPositionVariantName.selectedIndex = -1;
}

function getGameStatus(showresult) {
  let result = "null";
  if (board.isGameOver() || board.isGameOver(true) || board.isGameOver(false)) {
    if (board.result() != "*") {
      gameResult.value = board.result();
      result = "END";
    } else if (board.result(true) != "*") {
      gameResult.value = board.result(true);
      result = "END";
    } else if (board.result(false) != "*") {
      gameResult.value = board.result(false);
      result = "END";
    } else {
      gameResult.value = "Unterminated";
      result = "UNFINISHED";
    }
    if (showresult) {
      gameResult.click();
    }
  } else if (timeOutSide.value == 1) {
    //console.log("White time out");
    gameResult.value = "0-1";
    result = "END";
    if (showresult) {
      gameResult.click();
    }
  } else if (timeOutSide.value == 2) {
    //console.log("Black time out");
    gameResult.value = "1-0";
    result = "END";
    if (showresult) {
      gameResult.click();
    }
  } else {
    //console.log("continue");
    if (board.turn() == WHITE) {
      result = "PLAYING_WHITE";
    } else if (board.turn() == BLACK) {
      result = "PLAYING_BLACK";
    }
  }
  return result;
}

function resetTimer() {
  console.log("Timer reset!");
  whiteTime.innerHTML = "--";
  blackTime.innerHTML = "--";
  timeOutSide.value = 0;
}

function getDests(board) {
  const dests = new Map();
  const moves = board
    .legalMoves()
    .split(" ")
    .filter((m) => m !== "");

  for (let i = 0; i < moves.length; i++) {
    const move = moves[i];
    const match = move.match(/(\D\d+)(\D\d+)/);
    if (match) {
      const from = convertSquareToChessgroundXKey(match[1]);
      const to = convertSquareToChessgroundXKey(match[2]);
      if (dests.get(from) === undefined) dests.set(from, []);
      dests.get(from).push(to);
    }

    const dropmatch = move.match(/([A-Z]+@)([a-z]+[0-9]+)/);
    if (dropmatch) {
      const dropfrom = dropmatch[1];
      const dropto = convertSquareToChessgroundXKey(dropmatch[2]);
      if (dests.get(dropfrom) === undefined) dests.set(dropfrom, []);
      dests.get(dropfrom).push(dropto);
    }
  }

  return dests;
}

function getColorOrUndefined(board) {
  if (getGameStatus(false) == "END") return undefined;
  return getColor(board);
}

function getColor(board) {
  return board.turn() ? "white" : "black";
}

function getPiecesAsArray(board) {
  // Is board.toString really the best way to get the pieces?
  const pieces = [];
  const piecesLines = board.toString().split(/\r?\n/);

  for (let i = 0; i < piecesLines.length; i++) {
    pieces[piecesLines.length - i - 1] = piecesLines[i].split(" ");
  }

  return pieces;
}

function squareGetCoords(square) {
  if (square.length < 2) return [-1, -1];
  const coords = [-1, -1];
  coords[0] = parseInt(square.substring(1)) - 1;
  if (coords[0] === NaN || coords[0] < 0 || coords[0] >= 1000) return [-1, -1];
  coords[1] = square.charCodeAt(0) - "a".charCodeAt(0);
  if (coords[1] === NaN || coords[1] < 0 || coords[1] >= 26) return [-1, -1];
  return coords;
}

function isCapture(board, move) {
  if (move.includes("@")) {
    return false;
  }
  const pieces = getPiecesAsArray(board);
  const moveFromStr = move.charAt(0) + parseInt(move.substring(1));
  const moveToStr =
    move.charAt(moveFromStr.length) +
    parseInt(move.substring(moveFromStr.length + 1));
  const moveFrom = squareGetCoords(moveFromStr);
  const moveTo = squareGetCoords(moveToStr);
  if (pieces[moveTo[0]][moveTo[1]] !== ".") return true; // En passant

  if (pieces[moveFrom[0]][moveFrom[1]].toLowerCase() === "p")
    return moveFrom[1] !== moveTo[1];
  return false;
}

// Describe a promotion, demotion or gating option of a move for showPromotionChoice()
// option: a piece letter, "+" (promote), "-" (demote) or "=" (keep)
// piece: the chessgroundx piece that is moved or dropped
// uci: the move with the option applied (without any gating move after ",")
function describePromotionOption(option, piece, uci, legalmoves) {
  const legalmove = legalmoves.find((m) => m.split(",")[0] == uci);
  const san = legalmove ? board.sanMove(legalmove) : uci;
  let result = null;
  if (piece) {
    // Promoted roles are prefixed with "p", e.g. "pp-piece" for a tokin
    const promoted = piece.role.indexOf("-") == 2;
    let role = piece.role;
    if (option == "+") {
      role = promoted ? role : "p" + role;
    } else if (option == "-") {
      role = promoted ? role.substring(1) : role;
    } else if (option != "=") {
      role = util.roleOf(option);
    }
    result = { role: role, color: piece.color };
  }
  return {
    value: option,
    piece: result,
    label: san,
    // In SAN a gated piece is written after "/", e.g. "Nc3/H"
    gating: /^[a-z]$/.test(option) && san.split(",")[0].includes("/"),
  };
}

// Let the player pick one of several promotion or gating options on top of the board.
// choices: list of { value, piece, label }, a null piece shows an empty choice
// anchor: chessgroundx key of the square the choices start from
// callback: called with the value of the chosen option, or null if cancelled
function showPromotionChoice(choices, anchor, callback) {
  closePromotionChoice();
  const container = chessgroundEl.querySelector("cg-container");
  if (!container) {
    callback(null);
    return;
  }
  // Offer keeping the piece unchanged last, furthest from the anchor square
  choices = choices
    .filter((c) => c.value != "=")
    .concat(choices.filter((c) => c.value == "="));
  const orientation = chessground.state.orientation;
  const width = chessground.state.dimensions.width;
  const height = chessground.state.dimensions.height;
  const pos = util.key2pos(anchor);
  const col = orientation == "white" ? pos[0] : width - 1 - pos[0];
  const row = orientation == "white" ? height - 1 - pos[1] : pos[1];
  const count = choices.length;
  const cells = [];
  if (count <= height) {
    // Stack the choices from the anchor square towards the board center
    const step = row < height / 2 ? 1 : -1;
    const first =
      step > 0 ? Math.min(row, height - count) : Math.max(row, count - 1);
    for (let i = 0; i < count; i++) {
      cells.push([col, first + step * i]);
    }
  } else {
    // Too many choices for one file, show them as a grid in the center
    let cols = Math.min(width, Math.ceil(Math.sqrt(count)));
    if (Math.ceil(count / cols) > height) {
      cols = Math.min(width, Math.ceil(count / height));
    }
    const rows = Math.ceil(count / cols);
    const left = Math.floor((width - cols) / 2);
    const top = Math.floor((height - rows) / 2);
    for (let i = 0; i < count; i++) {
      cells.push([left + (i % cols), top + Math.floor(i / cols)]);
    }
  }

  const overlay = document.createElement("div");
  overlay.className = "promotion-choice";
  overlay.setAttribute("role", "dialog");
  overlay.setAttribute("aria-label", "Choose a move option");
  const select = (value) => {
    closePromotionChoice();
    callback(value);
  };
  const buttons = choices.map((choice, i) => {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "promotion-choice-option";
    button.title = choice.label;
    button.setAttribute("aria-label", choice.label);
    button.style.left = `${(cells[i][0] * 100) / width}%`;
    button.style.top = `${(cells[i][1] * 100) / height}%`;
    button.style.width = `${100 / width}%`;
    button.style.height = `${100 / height}%`;
    if (choice.piece) {
      const pieceEl = document.createElement("piece");
      pieceEl.className = util.pieceClasses(choice.piece, orientation);
      button.appendChild(pieceEl);
    } else {
      button.classList.add("empty");
    }
    button.addEventListener("click", (event) => {
      event.stopPropagation();
      select(choice.value);
    });
    overlay.appendChild(button);
    return button;
  });
  overlay.addEventListener("click", () => select(null));
  // Keep chessground and the page from handling presses on the overlay
  ["mousedown", "touchstart", "contextmenu"].forEach((type) =>
    overlay.addEventListener(type, (event) => event.stopPropagation()),
  );
  const onKeyDown = (event) => {
    if (!overlay.isConnected) {
      closePromotionChoice();
      return;
    }
    let value = null;
    if (event.key == "Escape") {
      event.preventDefault();
      event.stopPropagation();
      select(null);
      return;
    } else if (
      event.key.length == 1 &&
      !event.ctrlKey &&
      !event.metaKey &&
      !event.altKey
    ) {
      value = choices.find((c) => c.value == event.key.toLowerCase());
    }
    if (value) {
      event.preventDefault();
      event.stopPropagation();
      select(value.value);
    }
  };
  document.addEventListener("keydown", onKeyDown, true);
  container.appendChild(overlay);
  promotionChoice = { overlay: overlay, onKeyDown: onKeyDown };
  buttons[0].focus({ preventScroll: true });
}

function closePromotionChoice() {
  if (!promotionChoice) {
    return;
  }
  promotionChoice.overlay.remove();
  document.removeEventListener("keydown", promotionChoice.onKeyDown, true);
  promotionChoice = null;
}

function afterChessgroundMove(orig, dest, metadata) {
  // Auto promote to queen for now
  let promotion = quickPromotionPiece.value;
  let i = 0;

  if (isBoardSetup.checked) {
    chessground.set({
      movable: {
        color: "both",
        dests: EmptyMap,
      },
    });
    return;
  }

  //console.log("move:", orig, dest, metadata);

  const move =
    convertChessgroundXKeyToSquare(orig) + convertChessgroundXKeyToSquare(dest);
  console.log(`${move}`);
  const capture = isCapture(board, move);

  //UCI notation syntax (piece move): <begin_file><begin_rank><end_file><end_rank>[[+ | -] | piece_id ][,<gating_move>]
  //"[+ | -]" is the promotion/demotion mark for this move. If missing, it means that the piece keeps its current status. This type is used for piece advance (shogi type promotion, can be demoted)
  //"[piece_id]" is the character to refer to the piece type, e.g. q=queen, r=rook. This type is used for pawn promotion (chess type promotion, cannot be demoted)
  //[,<gating_move>] is used in games which have arrowGating = true, duckGating = true, staticGating = true or pastGating = true. They all require pieceDrop = false

  const legalmoves = board.legalMoves().trim().split(" "); //This will set all possible moves (with promotion marks and gating moves) at current in uci format into array

  let possiblepromotions = [];
  let possiblegatings = [];
  let legalmove = "";
  let legalgate = "";
  console.log(`${legalmoves}`);
  for (i = 0; i < legalmoves.length; i++) {
    //Now look at each possible moves
    if (legalmoves[i].trim().length == 0) {
      continue;
    }
    legalmove = legalmoves[i].trim().split(",")[0];
    legalgate = legalmoves[i].trim().split(",")[1]; //this can be undefined
    //if it is a legal promotion/demotion move that matches the move player has made (see the syntax of uci notation, which is given above)
    if (
      move.trim() == legalmove.substring(0, move.trim().length) &&
      legalmove.length == move.trim().length + 1
    ) {
      if (/^[a-z+-]+$/.test(legalmove.charAt(move.trim().length))) {
        if (
          !possiblepromotions.includes(legalmove.charAt(move.trim().length))
        ) {
          possiblepromotions.push(legalmove.charAt(move.trim().length));
        }
      }
      if (legalgate == undefined) {
        //now check the gating move
        if (!possiblegatings.includes("=")) {
          possiblegatings.push("="); //we use = to represent that not gating is legal
        }
      } else {
        if (!possiblegatings.includes(legalgate)) {
          possiblegatings.push(legalgate);
        }
      }
      //if it is legal to not promote/demote
    } else if (move.trim() == legalmove) {
      if (!possiblepromotions.includes("=")) {
        possiblepromotions.push("="); //we use = to represent that not promoting/demoting is legal
      }
      if (legalgate == undefined) {
        //now check the gating move
        if (!possiblegatings.includes("=")) {
          possiblegatings.push("="); //we use = to represent that not gating is legal
        }
      } else {
        if (!possiblegatings.includes(legalgate)) {
          possiblegatings.push(legalgate);
        }
      }
    }
  }
  console.log(`possible promotion choices: ${possiblepromotions}`);
  console.log(`possible gating choices: ${possiblegatings}`);
  let choice = null;
  if (
    quickPromotionPiece.value != "" &&
    !metadata.ctrlKey &&
    possiblepromotions.includes(promotion)
  ) {
    choice = promotion;
    console.log(`Using quick promotion: ${promotion}`);
  } else if (possiblepromotions.length > 1) {
    //if there are more than one option, let the player pick one on the board
    const piece = chessground.state.boardState.pieces.get(dest);
    const choices = possiblepromotions.map((option) =>
      describePromotionOption(
        option,
        piece,
        move + (option == "=" ? "" : option),
        legalmoves,
      ),
    );
    // Gating pieces (e.g. seirawan) appear on the origin square of the move
    const gating = choices.some((c) => c.gating);
    if (gating) {
      choices.forEach((c) => {
        if (c.value == "=") {
          c.piece = null;
          c.label = `${c.label} (no gating)`;
        }
      });
    }
    showPromotionChoice(choices, gating ? orig : dest, (selected) => {
      if (selected == null) {
        afterMove(null, false);
      } else {
        finishChessgroundMove(move, capture, selected, possiblegatings);
      }
    });
    return;
  } else if (possiblepromotions.length == 1) {
    //if there is only one option
    choice = possiblepromotions[0];
  } else {
    console.log("Did you make an illegal move? Why is there no legal action?");
  }
  finishChessgroundMove(move, capture, choice, possiblegatings);
}

function finishChessgroundMove(move, capture, choice, possiblegatings) {
  let promotion = "";
  let gating = "";
  console.log(`final move choice: ${choice}`);

  if (choice == null || choice == undefined) {
    promotion = "";
  } else if (choice == "=") {
    promotion = "";
  } else {
    promotion = choice;
  }

  choice = null;

  if (possiblegatings.length > 1) {
    // Click-to-place gating with translucent dots for legal targets
    let fromKey = null;
    const destToChoiceMap = new Map();
    for (let gi = 0; gi < possiblegatings.length; gi++) {
      const g = possiblegatings[gi];
      if (g === "=") continue; // skip explicit "no gate"
      const coords = g.match(/[a-z]+[0-9]+/g);
      if (!coords || coords.length < 2) continue;
      if (!fromKey) fromKey = convertSquareToChessgroundXKey(coords[0]);
      const destKey = convertSquareToChessgroundXKey(coords[1]);
      destToChoiceMap.set(destKey, g);
    }
    if (!fromKey || destToChoiceMap.size === 0) {
      afterMove(null, false);
      return;
    }
    // Build a temporary dests map for green dots
    const gatingDests = new Map();
    gatingDests.set(fromKey, Array.from(destToChoiceMap.keys()));
    gatingPending = true;
    gatingContext = {
      baseMove: move,
      promotion: promotion,
      capture: capture,
      fromKey: fromKey,
      destToChoiceMap: destToChoiceMap,
      prevSelectableEnabled: chessground.state.selectable.enabled,
    };
    // Show standard CG dots from the duck's square, disable click-move to avoid triggering moves
    chessground.set({
      movable: { color: "both", dests: gatingDests },
      selectable: { enabled: false },
    });
    chessground.selectSquare(fromKey, true);
    chessground.setAutoShapes([]);
    // Defer finalization until user clicks a destination square
    return;
  } else if (possiblegatings.length == 1) {
    //if there is only one option
    choice = possiblegatings[0];
  } else {
    console.log("Did you make an illegal move? Why is there no legal action?");
  }
  console.log(`final gating choice: ${choice}`);

  if (choice == null || choice == undefined) {
    gating = "";
  } else if (choice == "=") {
    gating = "";
  } else {
    gating = "," + choice;
  }

  let finalmove = move + promotion + gating;

  if (!board.push(finalmove)) {
    const foundmove = board.legalMoves().match(new RegExp(`${move}[^ ]+`));
    if (foundmove) {
      finalmove = foundmove[0];
    } else {
      finalmove = null;
    }
  }

  afterMove(finalmove, capture);
}

function afterChessgroundDrop(piece, dest, metadata) {
  let promotion = quickPromotionPiece.value;
  let i = 0;

  // A pocket piece was dropped while a choice was still open
  if (promotionChoice) {
    closePromotionChoice();
    afterMove(null, false);
    return;
  }

  if (isBoardSetup.checked) {
    chessground.set({
      movable: {
        color: "both",
        dests: EmptyMap,
      },
    });
    return;
  }

  //When dropPromoted = true in variant.ini, FairyStockfish allows an unpromoted piece to be dropped in promoted form (not compulsory)
  //Therefore, you need to consider about adding drop promoted piece function support.

  //Moreover, if capturesToHand = true && dropLoop = true && pieceDemotion = true, then promoted piece will become advanced, not promoted form*.
  //Lets give an example, suppose a rook can be promoted to chancellor (RN), when promoted it will be +R, which can be demoted.
  //However, once captured, the opponent will get a true chancellor(C) piece, not the promoted rook(+R). The new piece(C) cannot be demoted.
  //So, dropping piece does not have demotion features. pieceDemotion option does not affect drop promotion function.
  //Pawns cannot be dropped in promoted status which they get it by reaching the promotion zone

  //Piece drop notation are the same for uci and san. They are all [+]<piece id>@<file><rank>, e.g. Q@d2, +R@c4
  //This means that the format is different from moving, as the promotion mark is at the beginning. Just making some small changes will solve this.
  //The program logic is the same as moving.

  const role = piece.role;
  const move = util.dropOrigOf(role) + convertChessgroundXKeyToSquare(dest);
  console.log(`${move}`);

  const legalmoves = board.legalMoves().trim().split(" ");
  let possiblepromotions = [];
  console.log(`${legalmoves}`);
  for (i = 0; i < legalmoves.length; i++) {
    if (legalmoves[i].trim().length == 0) {
      continue;
    }
    //if it is a legal promotion drop that matches the drop player has made
    if (
      move.trim() ==
        legalmoves[i].trim().substring(1, move.trim().length + 1) &&
      legalmoves[i].trim().length == move.trim().length + 1
    ) {
      if (/^[+-]+$/.test(legalmoves[i].trim().charAt(0))) {
        possiblepromotions.push(legalmoves[i].trim().charAt(0));
      }
      //if it is legal to not promote/demote
    } else if (move.trim() == legalmoves[i].trim()) {
      possiblepromotions.push("="); //we use = to represent that not promoting is legal
    }
  }
  console.log(`possible choice: ${possiblepromotions}`);
  let choice = null;
  if (
    quickPromotionPiece.value != "" &&
    !metadata.ctrlKey &&
    possiblepromotions.includes(promotion)
  ) {
    choice = promotion;
    console.log(`Using quick promotion: ${promotion}`);
  } else if (possiblepromotions.length > 1) {
    //if there are more than one option, let the player pick one on the board
    showPromotionChoice(
      possiblepromotions.map((option) =>
        describePromotionOption(
          option,
          piece,
          (option == "=" ? "" : option) + move,
          legalmoves,
        ),
      ),
      dest,
      (selected) => {
        if (selected == null) {
          afterMove(null, false);
        } else {
          finishChessgroundDrop(move, selected);
        }
      },
    );
    return;
  } else if (possiblepromotions.length == 1) {
    //if there is only one option
    choice = possiblepromotions[0];
  } else {
    console.log("Did you make an illegal drop? Why is there no legal action?");
  }
  finishChessgroundDrop(move, choice);
}

function finishChessgroundDrop(move, choice) {
  let promotion = "";
  console.log(`final choice: ${choice}`);

  if (choice == null) {
    promotion = "";
  } else if (choice == "=") {
    promotion = "";
  } else {
    promotion = choice;
  }

  let finalmove = promotion + move;

  if (!board.push(finalmove)) {
    finalmove = null;
  }
  afterMove(finalmove, false);
}

function afterMove(move, capture) {
  if (move) {
    textMoves.value = (textMoves.value + " " + move).trim();
    timerElapsePreviousPlayer = true;
  }

  pSetFen.click();

  if (move) {
    if (capture) {
      soundCapture.currentTime = 0.0;
      soundCapture.play();
    } else {
      soundMove.currentTime = 0.0;
      soundMove.play();
    }
  }

  if (getGameStatus(false) == "END") {
    soundTerminal.currentTime = 0.0;
    soundTerminal.play();
  } else if (board.isCheck()) {
    soundCheck.currentTime = 0.0;
    soundCheck.play();
  }
  recordedmultipv = 1;
}

function getPgn(board) {
  if (
    dropdownNotationSystem[dropdownNotationSystem.selectedIndex].value == ""
  ) {
    /*let pgn = "";
    const reversedMoves = [];
    let moveStack = board.moveStack();

    while (moveStack.length > 0) {
      // TODO: improve this :/
      reversedMoves.push(moveStack.split(" ").pop());
      board.pop();
      moveStack = board.moveStack();
    }

    if (!board.turn() && reversedMoves.length > 0) {
      pgn += board.fullmoveNumber() + "... ";
    }

    while (reversedMoves.length > 0) {
      const move = reversedMoves.pop();

      if (board.turn()) {
        pgn += board.fullmoveNumber() + ". ";
      }

      pgn += board.sanMove(move) + " ";
      board.push(move);
    }

    const result = board.result(checkboxAdjudicate.checked);
    if (result !== "*") pgn += result;
    return pgn.trim();*/
    return "Please select a notation system in the dropdown...";
  } else {
    return getNotation(
      dropdownNotationSystem[dropdownNotationSystem.selectedIndex].value,
      board.variant(),
      textFen.value == "" ? ffish.startingFen(board.variant()) : textFen.value,
      board.is960(),
      textMoves.value,
      true,
    );
  }
}

function getPgnDiv(board) {
  let notationindex = simplenotations.indexOf(
    dropdownNotationSystem[dropdownNotationSystem.selectedIndex].value,
  );
  if (notationindex < 0) {
    buttonMoveTreeUndo.disabled =
      buttonMoveTreeRedo.disabled =
      buttonMoveTreeHideShow.disabled =
      buttonMoveTreeRemoveVariations.disabled =
      buttonMoveTreeSymbol.disabled =
      buttonMoveTreeTextAfter.disabled =
      buttonMoveTreeTextBefore.disabled =
      buttonMoveTreeCrop.disabled =
      buttonMoveTreeHideShow.disabled =
      buttonMoveTreeSetToMainBranch.disabled =
      buttonMoveTreeSetAsMainLine.disabled =
      buttonMoveTreeUncomment.disabled =
      buttonMoveTreeCut.disabled =
      buttonMoveTreeCutBranch.disabled =
      buttonMoveTreeCropBranch.disabled =
      buttonMoveTreeClear.disabled =
      buttonMoveTreeClearComments.disabled =
      buttonMoveTreeMarkers.disabled =
      buttonMoveTreeTermination.disabled =
      buttonMoveTreeBoardPreview.disabled =
        true;
    return m("div", getPgn(board) ?? "");
  } else {
    // let result = parseUCIMovesToPreviewElements(
    //   board.variant(),
    //   textFen.value == "" ? ffish.startingFen(board.variant()) : textFen.value,
    //   board.is960(),
    //   textMoves.value,
    //   "pgndiv",
    //   ffishnotationobjects[notationindex],
    // );
    buttonMoveTreeUndo.disabled = gametree.CurrentHistory <= 0;
    buttonMoveTreeRedo.disabled =
      gametree.CurrentHistory >= gametree.HistoryStack.length - 1;
    buttonMoveTreeHideShow.disabled =
      buttonMoveTreeSymbol.disabled =
      buttonMoveTreeTextBefore.disabled =
      buttonMoveTreeCrop.disabled =
      buttonMoveTreeHideShow.disabled =
      buttonMoveTreeSetAsMainLine.disabled =
      buttonMoveTreeCut.disabled =
      buttonMoveTreeCutBranch.disabled =
      buttonMoveTreeCropBranch.disabled =
        gametree.CurrentMove == gametree.MoveTree.RootNode;
    buttonMoveTreeSetToMainBranch.disabled =
      gametree.CurrentMove == gametree.MoveTree.RootNode ||
      gametree.CurrentMove.RelativePositionInParentNode == 0;
    buttonMoveTreeRemoveVariations.disabled =
      gametree.CurrentMove.NextNodes.length <= 1;
    buttonMoveTreeClear.disabled =
      buttonMoveTreeClearComments.disabled =
      buttonMoveTreeUncomment.disabled =
      buttonMoveTreeMarkers.disabled =
      buttonMoveTreeTextAfter.disabled =
      buttonMoveTreeTermination.disabled =
      buttonMoveTreeBoardPreview.disabled =
        false;
    return gametree.ToPGNDiv(
      ffishnotationobjects[notationindex],
      dropdownPGNStyle[dropdownPGNStyle.selectedIndex].value,
      chessground.state.orientation,
    );
  }
}

function disableBoardMove() {
  chessground.set({
    movable: {
      color: undefined,
    },
    draggable: {
      enabled: dragMove.checked,
      deleteOnDropOff: false,
    },
  });
}

function enableBoardMove() {
  chessground.set({
    movable: {
      color: getColorOrUndefined(board),
      dests: getDests(board),
    },
    draggable: {
      enabled: dragMove.checked || isBoardSetup.checked,
      deleteOnDropOff: isBoardSetup.checked,
    },
  });
}

function getCurrentBoardSize() {
  let boardsize = [];
  let i = 0;
  const ClassList = document.getElementById(
    "chessground-container-div",
  ).classList;
  const matcherobj = new RegExp("board[0-9]+x[0-9]+");
  for (i = 0; i < ClassList.length; i++) {
    if (matcherobj.test(ClassList[i])) {
      boardsize = ClassList[i].replace("board", "").split("x"); //[width, height]
      break;
    }
  }
  return { width: parseInt(boardsize[0]), height: parseInt(boardsize[1]) };
}

function getKnownAndUnknownSquares(board) {
  let moves = board.legalMoves().split(" ");
  let unknownsquares = new Set();
  let knownsquares = new Set();
  let i = 0;
  let j = 0;
  let boardsize = getCurrentBoardSize();
  let square = "";
  let parseresult = [];
  let orig = "";
  let dest = "";
  for (i = 0; i < moves.length; i++) {
    parseresult = moveutil.ParseUCIMove(moves[i]);
    orig = parseresult[0];
    dest = parseresult[1];
    if (!orig.includes("@")) {
      knownsquares.add(orig);
    }
    knownsquares.add(dest);
  }
  for (i = 0; i < boardsize.width; i++) {
    for (j = 0; j < boardsize.height; j++) {
      square = `${files[i]}${j + 1}`;
      if (!knownsquares.has(square)) {
        unknownsquares.add(square);
      }
    }
  }
  return { KnownSquares: knownsquares, UnknownSquares: unknownsquares };
}

function getHiddenDroppablePiece(board) {
  let legalmoves = board.legalMoves();
  if (legalmoves == "") {
    return "";
  }
  let originalfen = board.fen();
  let moves = legalmoves.split(" ");
  let i = 0;
  let movepart = [];
  let hiddenpieces = [];
  for (i = 0; i < moves.length; i++) {
    if (moves[i] == "") {
      continue;
    }
    movepart = moveutil.ParseUCIMove(moves[i]);
    if (movepart[0].endsWith("@")) {
      if (movepart[0].charAt(0) == "+") {
        let pieceid = board.turn()
          ? movepart[0].charAt(1)
          : movepart[0].charAt(1).toLowerCase();
        if (!pieceDisplayedInPocketOfFEN(originalfen, pieceid)) {
          if (hiddenpieces.indexOf(pieceid) < 0) {
            hiddenpieces.push(pieceid);
          }
        }
      } else {
        let pieceid = board.turn()
          ? movepart[0].charAt(0)
          : movepart[0].charAt(0).toLowerCase();
        if (!pieceDisplayedInPocketOfFEN(originalfen, pieceid)) {
          if (hiddenpieces.indexOf(pieceid) < 0) {
            hiddenpieces.push(pieceid);
          }
        }
      }
    }
  }
  return hiddenpieces.join("");
}

function displayHiddenDroppablePiece(board) {
  let legalmoves = board.legalMoves();
  if (legalmoves == "") {
    return;
  }
  let originalfen = board.fen();
  let moves = legalmoves.split(" ");
  let i = 0;
  let movepart = [];
  let hiddenpieces = [];
  let whitehiddenpieces = "";
  let blackhiddenpieces = "";
  for (i = 0; i < moves.length; i++) {
    if (moves[i] == "") {
      continue;
    }
    movepart = moveutil.ParseUCIMove(moves[i]);
    if (movepart[0].endsWith("@")) {
      if (movepart[0].charAt(0) == "+") {
        let pieceid = board.turn()
          ? movepart[0].charAt(1)
          : movepart[0].charAt(1).toLowerCase();
        if (!pieceDisplayedInPocketOfFEN(originalfen, pieceid)) {
          if (board.turn()) {
            whitehiddenpieces += pieceid;
          } else {
            blackhiddenpieces += pieceid;
          }
          if (hiddenpieces.indexOf(pieceid) < 0) {
            hiddenpieces.push(pieceid);
          }
        }
      } else {
        let pieceid = board.turn()
          ? movepart[0].charAt(0)
          : movepart[0].charAt(0).toLowerCase();
        if (!pieceDisplayedInPocketOfFEN(originalfen, pieceid)) {
          if (board.turn()) {
            whitehiddenpieces += pieceid;
          } else {
            blackhiddenpieces += pieceid;
          }
          if (hiddenpieces.indexOf(pieceid) < 0) {
            hiddenpieces.push(pieceid);
          }
        }
      }
    }
  }
  if (hiddenpieces.length) {
    if (chessground.state.pocketRoles == undefined) {
      chessground.state.pocketRoles = { white: [], black: [] };
    }
    let whitehiddenpieceroles = getPieceRoles(whitehiddenpieces);
    let blackhiddenpieceroles = getPieceRoles(blackhiddenpieces);
    if (chessground.state.boardState.pockets == undefined) {
      chessground.state.boardState.pockets = {
        white: new Map(),
        black: new Map(),
      };
    }
    for (i = 0; i < whitehiddenpieceroles.length; i++) {
      if (
        chessground.state.pocketRoles.white.indexOf(whitehiddenpieceroles[i]) <
        0
      ) {
        chessground.state.pocketRoles.white.push(whitehiddenpieceroles[i]);
      }
      chessground.state.boardState.pockets.white.set(
        whitehiddenpieceroles[i],
        1,
      );
    }
    for (i = 0; i < blackhiddenpieceroles.length; i++) {
      if (
        chessground.state.pocketRoles.black.indexOf(blackhiddenpieceroles[i]) <
        0
      ) {
        chessground.state.pocketRoles.black.push(blackhiddenpieceroles[i]);
      }
      chessground.state.boardState.pockets.black.set(
        blackhiddenpieceroles[i],
        1,
      );
    }
    let fen = board.fen();
    if (fen.includes("[")) {
      let endoffenpocket = fen.indexOf("]");
      fen =
        fen.substring(0, endoffenpocket) +
        hiddenpieces.join("") +
        fen.substring(endoffenpocket);
    } else {
      let fenlist = fen.split(" ");
      fenlist[0] += `[${hiddenpieces.join("")}]`;
      fen = fenlist.join(" ");
    }
    chessgroundContainerEl.classList.add("pockets");
    console.log("Hidden pieces:", hiddenpieces);
    console.log("Fake FEN:", fen);
    rerenderChessgroundPockets(fen);
    pocketTopEl.classList.add("has-hidden-pocket-piece");
    pocketBottomEl.classList.add("has-hidden-pocket-piece");
  } else {
    pocketTopEl.classList.remove("has-hidden-pocket-piece");
    pocketBottomEl.classList.remove("has-hidden-pocket-piece");
  }
}

function pieceDisplayedInPocketOfFEN(fen, pieceid) {
  if (fen.includes("[")) {
    let pieces = fen.substring(fen.indexOf("[") + 1, fen.indexOf("]"));
    return pieces.includes(pieceid);
  } else {
    return false;
  }
}

function getCheckSquares(board) {
  let checks = board.checkedPieces();
  if (checks == "") {
    return [];
  }
  let checklist = checks.split(" ");
  let i = 0;
  for (i = 0; i < checklist.length; i++) {
    checklist[i] = convertSquareToChessgroundXKey(checklist[i]);
  }
  return checklist;
}

function ApplyVisualEffectToBoard(effect, perspective, chessground, board) {
  if (effect == "fogofwar") {
    if (perspective == "white") {
      if (board.turn()) {
        const fogofwarsquarevisibility = getKnownAndUnknownSquares(board);
        const unknownsquares = Array.from(
          fogofwarsquarevisibility.UnknownSquares,
        );
        let i = 0;
        let val1;
        for (i = 0; i < unknownsquares.length; i++) {
          val1 = convertSquareToChessgroundXKey(unknownsquares[i]);
          if (chessground.state.boardState.pieces.has(val1)) {
            let piece = chessground.state.boardState.pieces.get(val1);
            if (piece.role == "_-piece" || piece.color == "white") {
              continue;
            }
            piece.role = "unknown";
          } else {
            chessground.state.boardState.pieces.set(val1, {
              color: "black",
              role: "unknown",
            });
          }
        }
      } else {
        let i = 0;
        let j = 0;
        let boardsize = getCurrentBoardSize();
        let square = "";
        chessground.set({
          movable: {
            color: undefined,
            dests: EmptyMap,
          },
        });
        for (i = 0; i < boardsize.width; i++) {
          for (j = 0; j < boardsize.height; j++) {
            square = convertSquareToChessgroundXKey(`${files[i]}${j + 1}`);
            if (
              chessground.state.boardState.pieces.has(square) &&
              (chessground.state.boardState.pieces.get(square).color ==
                "white" ||
                chessground.state.boardState.pieces.get(square).role ==
                  "_-piece")
            ) {
              continue;
            } else {
              chessground.state.boardState.pieces.set(square, {
                color: "black",
                role: "unknown",
              });
            }
          }
        }
      }
    } else if (perspective == "black") {
      if (board.turn()) {
        let i = 0;
        let j = 0;
        let boardsize = getCurrentBoardSize();
        let square = "";
        chessground.set({
          movable: {
            color: undefined,
            dests: EmptyMap,
          },
        });
        for (i = 0; i < boardsize.width; i++) {
          for (j = 0; j < boardsize.height; j++) {
            square = convertSquareToChessgroundXKey(`${files[i]}${j + 1}`);
            if (
              chessground.state.boardState.pieces.has(square) &&
              (chessground.state.boardState.pieces.get(square).color ==
                "black" ||
                chessground.state.boardState.pieces.get(square).role ==
                  "_-piece")
            ) {
              continue;
            } else {
              chessground.state.boardState.pieces.set(square, {
                color: "white",
                role: "unknown",
              });
            }
          }
        }
      } else {
        const fogofwarsquarevisibility = getKnownAndUnknownSquares(board);
        const unknownsquares = Array.from(
          fogofwarsquarevisibility.UnknownSquares,
        );
        let i = 0;
        let val1;
        for (i = 0; i < unknownsquares.length; i++) {
          val1 = convertSquareToChessgroundXKey(unknownsquares[i]);
          if (chessground.state.boardState.pieces.has(val1)) {
            let piece = chessground.state.boardState.pieces.get(val1);
            if (piece.role == "_-piece" || piece.color == "black") {
              continue;
            }
            piece.role = "unknown";
          } else {
            chessground.state.boardState.pieces.set(val1, {
              color: "white",
              role: "unknown",
            });
          }
        }
      }
    } else if (perspective == "alternate") {
      const fogofwarsquarevisibility = getKnownAndUnknownSquares(board);
      const unknownsquares = Array.from(
        fogofwarsquarevisibility.UnknownSquares,
      );
      let i = 0;
      let val1;
      const movercolor = getColor(board);
      for (i = 0; i < unknownsquares.length; i++) {
        val1 = convertSquareToChessgroundXKey(unknownsquares[i]);
        if (chessground.state.boardState.pieces.has(val1)) {
          let piece = chessground.state.boardState.pieces.get(val1);
          if (piece.role == "_-piece" || piece.color == movercolor) {
            continue;
          }
          piece.role = "unknown";
        } else {
          chessground.state.boardState.pieces.set(val1, {
            color: board.turn() ? "black" : "white",
            role: "unknown",
          });
        }
      }
    }
  } else if (effect == "wargame") {
    if (perspective == "white") {
      let i = 0;
      let j = 0;
      let boardsize = getCurrentBoardSize();
      let square = "";
      if (!board.turn()) {
        chessground.set({
          movable: {
            color: undefined,
            dests: EmptyMap,
          },
        });
      }
      for (i = 0; i < boardsize.width; i++) {
        for (j = 0; j < boardsize.height; j++) {
          square = convertSquareToChessgroundXKey(`${files[i]}${j + 1}`);
          if (
            chessground.state.boardState.pieces.has(square) &&
            chessground.state.boardState.pieces.get(square).color == "black" &&
            chessground.state.boardState.pieces.get(square).role != "_-piece"
          ) {
            chessground.state.boardState.pieces.delete(square);
          }
        }
      }
    } else if (perspective == "black") {
      let i = 0;
      let j = 0;
      let boardsize = getCurrentBoardSize();
      let square = "";
      if (board.turn()) {
        chessground.set({
          movable: {
            color: undefined,
            dests: EmptyMap,
          },
        });
      }
      for (i = 0; i < boardsize.width; i++) {
        for (j = 0; j < boardsize.height; j++) {
          square = convertSquareToChessgroundXKey(`${files[i]}${j + 1}`);
          if (
            chessground.state.boardState.pieces.has(square) &&
            chessground.state.boardState.pieces.get(square).color == "white" &&
            chessground.state.boardState.pieces.get(square).role != "_-piece"
          ) {
            chessground.state.boardState.pieces.delete(square);
          }
        }
      }
    } else if (perspective == "alternate") {
      let i = 0;
      let j = 0;
      let boardsize = getCurrentBoardSize();
      let square = "";
      if (board.turn()) {
        for (i = 0; i < boardsize.width; i++) {
          for (j = 0; j < boardsize.height; j++) {
            square = convertSquareToChessgroundXKey(`${files[i]}${j + 1}`);
            if (
              chessground.state.boardState.pieces.has(square) &&
              chessground.state.boardState.pieces.get(square).color ==
                "black" &&
              chessground.state.boardState.pieces.get(square).role != "_-piece"
            ) {
              chessground.state.boardState.pieces.delete(square);
            }
          }
        }
      } else {
        for (i = 0; i < boardsize.width; i++) {
          for (j = 0; j < boardsize.height; j++) {
            square = convertSquareToChessgroundXKey(`${files[i]}${j + 1}`);
            if (
              chessground.state.boardState.pieces.has(square) &&
              chessground.state.boardState.pieces.get(square).color ==
                "white" &&
              chessground.state.boardState.pieces.get(square).role != "_-piece"
            ) {
              chessground.state.boardState.pieces.delete(square);
            }
          }
        }
      }
    }
  }
}

function DisplayLastMoveWithVisualEffect(
  effect,
  chessground,
  lastMoveFrom,
  lastMoveTo,
) {
  if (effect == "fogofwar") {
    if (
      chessground.state.boardState.pieces.has(lastMoveFrom) &&
      chessground.state.boardState.pieces.get(lastMoveFrom).role == "unknown"
    ) {
      if (
        chessground.state.boardState.pieces.get(lastMoveTo) == undefined ||
        chessground.state.boardState.pieces.get(lastMoveTo).role != "unknown"
      ) {
        chessground.set({
          lastMove: [lastMoveTo, lastMoveTo],
        });
      } else {
        chessground.set({
          lastMove: undefined,
        });
      }
    } else if (
      chessground.state.boardState.pieces.has(lastMoveTo) &&
      chessground.state.boardState.pieces.get(lastMoveTo).role == "unknown"
    ) {
      if (
        chessground.state.boardState.pieces.get(lastMoveFrom) == undefined ||
        chessground.state.boardState.pieces.get(lastMoveFrom).role != "unknown"
      ) {
        chessground.set({
          lastMove: [lastMoveFrom, lastMoveFrom],
        });
      } else {
        chessground.set({
          lastMove: undefined,
        });
      }
    } else {
      chessground.set({
        lastMove: [lastMoveFrom, lastMoveTo],
      });
    }
  } else if (effect == "wargame") {
    if (chessground.state.boardState.pieces.has(lastMoveTo)) {
      chessground.set({
        lastMove: [lastMoveFrom, lastMoveTo],
      });
    } else {
      chessground.set({
        lastMove: undefined,
      });
    }
  }
}

function DrawEvaluationHistoryGraph() {
  let notation_index = simplenotations.indexOf(
    dropdownNotationSystem[dropdownNotationSystem.selectedIndex].value,
  );
  let notation = ffishnotationobjects[notation_index < 0 ? 2 : notation_index];
  let tmpboard = new ffish.Board(
    gametree.Variant,
    gametree.OriginalFEN,
    gametree.Is960,
  );
  let moves = gametree.GetCompleteMainLineMoveListOfMove(gametree.CurrentMove);
  let moves_san = tmpboard
    .variationSan(moves, notation)
    .replace(MoveNumberMatcher, "")
    .trim()
    .split(SpaceSplitterMatcher);
  let eval_score_list = [];
  let move_number = -1;
  let passed_current_move = false;
  if (moves_san[0] != "") {
    moves_san.unshift("");
  }
  gametree.ForEachMoveOnBranchOfMove(gametree.CurrentMove, (move) => {
    if (move instanceof moveutil.Move) {
      if (!passed_current_move) {
        move_number++;
      }
      if (move == gametree.CurrentMove.Move) {
        passed_current_move = true;
      }
      let index = move.TextAfter.indexOf("[%eval ");
      if (index >= 0) {
        let index2 = move.TextAfter.indexOf("]", index + 7);
        if (index2 >= 0) {
          eval_score_list.push(move.TextAfter.substring(index + 7, index2));
          return;
        }
      }
      eval_score_list.push("");
    }
  });
  evalhistorygraph.SetEvaluationHistory(eval_score_list, moves_san);
  evalhistorygraph.SetCurrentIndex(move_number);
  evalhistorygraph.Draw();
}

function updatePGNDivisionTimeoutCheck() {
  if (PgnDivCalledDuringThrottle) {
    updatePGNDivision(true);
  }
}

function updatePGNDivision(force_update = false, auto_scroll = true) {
  if (!ffish) {
    return;
  }
  if (
    force_update ||
    Date.now() - PgnDivThrottleStartTime > PgnDivThrottleDurationMs
  ) {
    if (isAdvPGNMode.checked) {
      m.render(labelPgn, getPgnDiv(board));
    } else {
      m.render(labelPgn, getPgn(board) ?? "");
    }
    if (checkboxShowEvalHistoryGraph.checked) {
      DrawEvaluationHistoryGraph();
    }
    if (auto_scroll) {
      let current_move_element =
        labelPgn.getElementsByClassName("current-move")[0];
      if (current_move_element) {
        current_move_element.scrollIntoView({
          container: "nearest",
          block: "nearest",
          inline: "nearest",
        });
      } else {
        labelPgn.scrollTo(0, 0);
      }
    }
    PgnDivThrottleStartTime = Date.now();
    PgnDivCalledDuringThrottle = false;
    setTimeout(updatePGNDivisionTimeoutCheck, PgnDivThrottleDurationMs);
  } else {
    PgnDivCalledDuringThrottle = true;
  }
}

function updateChessground(showresult) {
  closePromotionChoice();
  const boardfenval = board.fen();
  const boardfenvallist = boardfenval.split(" ");
  currentBoardFen.textContent = boardfenval;

  if (boardfenvallist.length == 7) {
    const checknums = boardfenvallist[4].split("+");
    pcheckCounts.textContent = `First mover remaining checks: ${checknums[1]} ·········· Second mover remaining checks: ${checknums[0]}`;
    pcheckCounts.hidden = false;
  } else {
    pcheckCounts.textContent = "";
    pcheckCounts.hidden = true;
  }

  if (showresult) {
    gametree.SetCurrentMoveList(
      board.variant(),
      board.is960(),
      textFen.value,
      textMoves.value,
    );
    updatePGNDivision(false);
  }

  //if (labelPgn) labelPgn.innerText = getPgn(board);

  if (labelStm) labelStm.innerText = getColorOrUndefined(board);

  if (
    dropdownVisualEffect.value == "<DISABLED>" ||
    isBoardSetup.checked ||
    isAnalysis.checked ||
    labelStm.innerText == "undefined"
  ) {
    chessground.set({
      fen: boardfenval,
      check: getCheckSquares(board),
      turnColor: getColor(board),
      movable: {
        color: getColorOrUndefined(board),
        dests: getDests(board),
      },
    });
    displayHiddenDroppablePiece(board);
    if (showresult && gametree.CurrentMove.Move.TextAfter) {
      let parsedtext = moveutil.ParseTextActions(
        gametree.CurrentMove.Move.TextAfter,
      );
      let boardmarkers =
        (parsedtext.get("cal") ?? "") + "," + (parsedtext.get("csl") ?? "");
      if (boardmarkers.length > 1) {
        let parsedmarkers = parseBoardMarkers(boardmarkers, getColor(board));
        highlightMoveOnBoard(
          parsedmarkers.moveturns,
          chessground,
          parsedmarkers.moves,
          parsedmarkers.colors,
          parsedmarkers.notepositions,
          false,
        );
      }
    }
  } else {
    if (dropdownVisualEffectPerspective.value == "alternate") {
      chessground.set({ animation: { enabled: false } });
    }
    chessground.set({
      fen: boardfenval,
      check: getCheckSquares(board),
      turnColor: getColor(board),
      movable: {
        color: getColorOrUndefined(board),
        dests: getDests(board),
      },
    });
    displayHiddenDroppablePiece(board);
    ApplyVisualEffectToBoard(
      dropdownVisualEffect.value,
      dropdownVisualEffectPerspective.value,
      chessground,
      board,
    );
    if (dropdownVisualEffectPerspective.value == "alternate") {
      chessground.set({ animation: { enabled: true } });
    }
  }

  const moveStack = board.moveStack();
  clearMovesList();

  if (moveStack.length === 0) {
    chessground.set({
      lastMove: undefined,
    });
    buttonUndo.disabled = true;
  } else {
    const lastMove = moveStack.split(" ").pop();
    const matchresult = lastMove.match(/[a-z]+[0-9]+/g);
    let lastMoveFrom = null;
    let lastMoveTo = null;
    if (lastMove.includes("@")) {
      lastMoveFrom = lastMove.match(/[A-Z]+@/g)[0];
      lastMoveTo = convertSquareToChessgroundXKey(matchresult[0]);
    } else {
      lastMoveFrom = convertSquareToChessgroundXKey(matchresult[0]);
      lastMoveTo = convertSquareToChessgroundXKey(matchresult[1]);
      if (lastMoveFrom == lastMoveTo && lastMove.includes(",")) {
        lastMoveFrom = lastMoveTo = convertSquareToChessgroundXKey(
          matchresult[3],
        );
      }
    }
    if (
      dropdownVisualEffect.value == "<DISABLED>" ||
      isBoardSetup.checked ||
      isAnalysis.checked ||
      labelStm.innerText == "undefined"
    ) {
      chessground.set({
        lastMove: [lastMoveFrom, lastMoveTo],
      });
    } else {
      DisplayLastMoveWithVisualEffect(
        dropdownVisualEffect.value,
        chessground,
        lastMoveFrom,
        lastMoveTo,
      );
    }
    buttonUndo.disabled = false;
  }

  chessground.setAutoShapes([]);

  getGameStatus(showresult);
}
