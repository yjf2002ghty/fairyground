import * as moveutil from "./move.js";

export function ParseFEN(fen) {
  if (typeof fen != "string") {
    throw TypeError();
  }
  let i = 0;
  let j = 0;
  const pieceprefixes = ["+", "|"];
  const piecesuffixes = ["~"];
  const specialpieces = ["*"];
  let boardwidth = 0;
  let boardheight = 0;
  let chcode = 0;
  let ParserState = -1;
  let pieces = [];
  let piececolor = "";
  let pieceid = "";
  let firstrow = true;
  let columncount = 0;
  let prefix = "";
  let suffix = "";
  let blankcount = 0;
  let ch;
  const fenelem = fen.split(/[ ]+/);
  const position = fenelem[0];
  for (i = 0; i < position.length; i++) {
    ch = position[i];
    chcode = ch.charCodeAt(0);
    if (ParserState == -1) {
      //Initial state
      if (chcode >= 65 && chcode <= 90) {
        boardheight = 1;
        columncount++;
        piececolor = "white";
        pieceid = String.fromCharCode(chcode + 32);
        ParserState = 1;
      } else if (chcode >= 97 && chcode <= 122) {
        boardheight = 1;
        columncount++;
        piececolor = "black";
        pieceid = ch;
        ParserState = 1;
      } else if (chcode >= 48 && chcode <= 57) {
        boardheight = 1;
        blankcount = parseInt(ch);
        ParserState = 0;
      } else if (pieceprefixes.includes(ch)) {
        if (prefix.includes(ch)) {
          console.warn(
            `Duplicated piece prefix "${ch}" at char ${i + 1} of FEN.`,
          );
          return null;
        }
        boardheight = 1;
        prefix += ch;
        ParserState = 0;
      } else if (specialpieces.includes(ch)) {
        columncount++;
        boardheight = 1;
        pieces.push({ role: ch, color: null, prefix: null, suffix: null });
        ParserState = 0;
      } else {
        console.warn(`Illegal character "${ch}" at char ${i + 1} of FEN.`);
        return null;
      }
    } else if (ParserState == 0) {
      //Main state
      if (blankcount > 0 && (chcode < 48 || chcode > 57)) {
        for (j = 0; j < blankcount; j++) {
          pieces.push({ role: null, color: null, prefix: null, suffix: null });
        }
        columncount += blankcount;
        blankcount = 0;
      }
      if (chcode >= 65 && chcode <= 90) {
        piececolor = "white";
        pieceid = String.fromCharCode(chcode + 32);
        columncount++;
        ParserState = 1;
      } else if (chcode >= 97 && chcode <= 122) {
        piececolor = "black";
        pieceid = ch;
        columncount++;
        ParserState = 1;
      } else if (chcode >= 48 && chcode <= 57) {
        if (prefix.length > 0) {
          console.warn(
            `Illegal prefix "${prefix}" describing empty squares at char ${i + 1} of FEN.`,
          );
          return null;
        }
        blankcount = blankcount * 10 + parseInt(ch);
        prefix = "";
        suffix = "";
      } else if (pieceprefixes.includes(ch)) {
        if (prefix.includes(ch)) {
          console.warn(
            `Duplicated piece prefix "${ch}" at char ${i + 1} of FEN.`,
          );
          return null;
        }
        prefix += ch;
      } else if (specialpieces.includes(ch)) {
        if (prefix.length > 0) {
          console.warn(
            `Illegal prefix "${prefix}" describing special piece at char ${i + 1} of FEN.`,
          );
          return null;
        }
        columncount++;
        pieces.push({ role: ch, color: null, prefix: null, suffix: null });
      } else if (ch == "/") {
        if (firstrow) {
          boardwidth = columncount;
          firstrow = false;
        } else if (columncount != boardwidth) {
          console.warn(
            `Column count mismatch at row ${boardheight}. Expected: ${boardwidth}, Actual: ${columncount}`,
          );
          return null;
        }
        columncount = 0;
        boardheight++;
        if (prefix.length > 0) {
          console.warn(
            `Illegal prefix "${prefix}" at end of row at char ${i + 1} of FEN.`,
          );
          return null;
        }
      } else {
        console.warn(`Illegal character "${ch}" at char ${i + 1} of FEN.`);
        return null;
      }
    } else if (ParserState == 1) {
      //Parsing suffixes
      if (piecesuffixes.includes(ch)) {
        suffix += ch;
      } else {
        pieces.push({
          role: pieceid,
          color: piececolor,
          prefix: prefix,
          suffix: suffix,
        });
        prefix = "";
        suffix = "";
        i--;
        ParserState = 0;
      }
    }
  }
  if (ParserState == 0) {
    if (blankcount > 0) {
      for (j = 0; j < blankcount; j++) {
        pieces.push({ role: null, color: null, prefix: null, suffix: null });
      }
      columncount += blankcount;
    }
  } else if (ParserState == 1) {
    pieces.push({
      role: pieceid,
      color: piececolor,
      prefix: prefix,
      suffix: suffix,
    });
    prefix = "";
  }
  if (firstrow) {
    boardwidth = columncount;
  } else if (columncount != boardwidth) {
    console.warn(
      `Column count mismatch at row ${boardheight}. Expected: ${boardwidth}, Actual: ${columncount}`,
    );
    return null;
  }
  if (prefix.length > 0) {
    console.warn(
      `Illegal prefix "${prefix}" at end of row at char ${i + 1} of FEN.`,
    );
    return null;
  }
  return pieces;
}

export function GetBoardAndPocket(FEN) {
  if (typeof FEN != "string") {
    throw TypeError();
  }
  let fenpieces = FEN.split(" ")[0];
  let index = fenpieces.indexOf("[");
  let index2 = fenpieces.indexOf("]");
  if (index >= 0 && index2 > index) {
    return {
      board: fenpieces.substring(0, index),
      pocket: fenpieces.substring(index + 1, index2),
    };
  } else {
    return { board: fenpieces, pocket: "" };
  }
}

export function ConvertSquareToCoordinate(Square, BoardHeight) {
  if (typeof Square != "string" || typeof BoardHeight != "number") {
    throw TypeError();
  }
  let x = Square.charCodeAt(0) - 97;
  let y = BoardHeight - parseInt(Square.substring(1));
  if (x >= 0 && x <= 25 && y >= 0) {
    return { x: x, y: y };
  } else {
    return { x: -1, y: -1 };
  }
}

export function ConvertMoveToCoordinate(UCIMove, BoardHeight) {
  if (typeof UCIMove != "string" || typeof BoardHeight != "number") {
    throw TypeError();
  }
  let move = moveutil.ParseUCIMove(UCIMove);
  let from = move[0];
  let to = move[1];
  if (typeof from == "string" && typeof to == "string") {
    let from_sq = ConvertSquareToCoordinate(from, BoardHeight);
    let to_sq = ConvertSquareToCoordinate(to, BoardHeight);
    return {
      from_x: from_sq.x,
      from_y: from_sq.y,
      to_x: to_sq.x,
      to_y: to_sq.y,
    };
  } else {
    return { from_x: -1, from_y: -1, to_x: -1, to_y: -1 };
  }
}

export function CoordinateListIncludes(CoordinateList, X, Y) {
  if (
    !(CoordinateList instanceof Array) ||
    typeof X != "number" ||
    typeof Y != "number"
  ) {
    throw TypeError();
  }
  let i = 0;
  for (i = 0; i < CoordinateList.length; i++) {
    if (CoordinateList[i].x == X && CoordinateList[i].y == Y) {
      return true;
    }
  }
  return false;
}
