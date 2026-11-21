const m = require("mithril");
import * as boardutil from "./boardImageUtil.js";
import * as themeutil from "./chessgroundtheme.js";

function CountCharacters(str) {
  if (typeof str != "string") {
    throw TypeError();
  }
  let i = 0;
  let char;
  const whitepieces = new Map();
  const blackpieces = new Map();
  for (i = 0; i < str.length; i++) {
    char = str[i];
    if (char.charCodeAt(0) >= 65 && char.charCodeAt(0) <= 90) {
      whitepieces.set(char, (whitepieces.get(char) || 0) + 1);
    } else if (char.charCodeAt(0) >= 97 && char.charCodeAt(0) <= 122) {
      blackpieces.set(char, (blackpieces.get(char) || 0) + 1);
    }
  }
  return { white: whitepieces, black: blackpieces };
}

export function GenerateBoardDisplayElement(
  StatelessFEN,
  LastMove,
  CheckedSquares,
  HasPocket,
  Orientation,
  BoardWidth,
  BoardHeight,
  ThemeDetector,
) {
  // console.log(typeof StatelessFEN != "string")
  // console.log(typeof LastMove != "string")
  // console.log(!(CheckedSquares instanceof Array))
  // console.log(typeof HasPocket != "boolean")
  // console.log(typeof Orientation != "string")
  // console.log(typeof BoardWidth != "number")
  // console.log(typeof BoardHeight != "number")
  if (
    typeof StatelessFEN != "string" ||
    typeof LastMove != "string" ||
    !(CheckedSquares instanceof Array) ||
    typeof HasPocket != "boolean" ||
    typeof Orientation != "string" ||
    typeof BoardWidth != "number" ||
    typeof BoardHeight != "number" ||
    !(ThemeDetector instanceof themeutil.ChessgroundThemeDetector)
  ) {
    throw TypeError();
  }
  let i = 0,
    j = 0;
  let fenparts = boardutil.GetBoardAndPocket(StatelessFEN);
  let pieces = boardutil.ParseFEN(fenparts.board);
  let pocket = CountCharacters(fenparts.pocket);
  let lastmove = boardutil.ConvertMoveToCoordinate(LastMove, BoardHeight);
  let whitepocket = [...pocket.white.keys()];
  let blackpocket = [...pocket.black.keys()];
  let pocketsize = Math.max(whitepocket.length, blackpocket.length);
  let checkedsquarescoordinate = [];
  for (i = 0; i < CheckedSquares.length; i++) {
    checkedsquarescoordinate.push(
      boardutil.ConvertSquareToCoordinate(CheckedSquares[i], BoardHeight),
    );
  }

  let theme = ThemeDetector.GetThemes();

  const pocket_element_height = (HasPocket ? 1 / (BoardHeight + 2) : 0) * 100;
  const pocket_element_width =
    (pocketsize >= BoardWidth ? 1 : pocketsize / BoardWidth) * 100;
  const board_element_height =
    (HasPocket ? BoardHeight / (BoardHeight + 2) : 1) * 100;
  const board_element_width =
    (pocketsize <= BoardWidth ? 1 : BoardWidth / pocketsize) * 100;

  const aspect_ratio =
    Math.max(pocketsize, BoardWidth) /
    (HasPocket ? BoardHeight + 2 : BoardHeight);

  let pocket_top_vnodes = [];
  let pocket_bottom_vnodes = [];
  let board_elements = [];
  let index = 0;

  let board_vnodes = [];

  for (i = 0; i < pieces.length; i++) {
    board_elements.push([]);
  }

  for (i = 0; i < checkedsquarescoordinate.length; i++) {
    board_elements[
      checkedsquarescoordinate[i].y * BoardWidth + checkedsquarescoordinate[i].x
    ].push(m("div.checked-square"));
  }

  for (i = 0; i < BoardHeight; i++) {
    for (j = 0; j < BoardWidth; j++) {
      index = i * BoardWidth + j;
      if (
        (lastmove.from_x == j && lastmove.from_y == i) ||
        (lastmove.to_x == j && lastmove.to_y == i)
      ) {
        board_elements[index].push(m("div.last-move-square"));
      }
      if (pieces[index].role) {
        if (pieces[index].color == "white") {
          board_elements[index].push(
            m("div.piece", {
              style: `background-image: url("${theme.pieces.get(pieces[index].prefix + pieces[index].role.toUpperCase())}");`,
            }),
          );
        } else if (pieces[index].color == "black") {
          board_elements[index].push(
            m("div.piece", {
              style: `background-image: url("${theme.pieces.get(pieces[index].prefix + pieces[index].role)}");`,
            }),
          );
        } else {
          board_elements[index].push(
            m("div.piece", {
              style: `background-image: url("${theme.pieces.get(pieces[index].role)}");`,
            }),
          );
        }
      }
    }
  }

  const square_height = 100 / BoardHeight;
  const square_width = 100 / BoardWidth;

  if (Orientation == "white") {
    for (i = 0; i < whitepocket.length; i++) {
      pocket_bottom_vnodes.push(
        m(
          "div.pocket-square",
          {
            style: `left: ${i * square_width}%; top: 0; width: ${square_width}%; height: ${square_height}%;`,
          },
          [
            m("div.piece", {
              style: `background-image: url("${theme.pieces.get(whitepocket[i])}");`,
            }),
            m("div.piece-count", `${pocket.white.get(whitepocket[i])}`),
          ],
        ),
      );
    }
    for (i = 0; i < blackpocket.length; i++) {
      pocket_top_vnodes.push(
        m(
          "div.pocket-square",
          {
            style: `left: ${i * square_width}%; top: 0; width: ${square_width}%; height: ${square_height}%;`,
          },
          [
            m("div.piece", {
              style: `background-image: url("${theme.pieces.get(blackpocket[i])}");`,
            }),
            m("div.piece-count", `${pocket.black.get(blackpocket[i])}`),
          ],
        ),
      );
    }
  } else {
    board_elements.reverse();
    for (i = 0; i < whitepocket.length; i++) {
      pocket_top_vnodes.push(
        m(
          "div.pocket-square",
          {
            style: `left: ${i * square_width}%; top: 0; width: ${square_width}%; height: ${square_height}%;`,
          },
          [
            m("div.piece", {
              style: `background-image: url("${theme.pieces.get(whitepocket[i])}");`,
            }),
            m("div.piece-count", `${pocket.white.get(whitepocket[i])}`),
          ],
        ),
      );
    }
    for (i = 0; i < blackpocket.length; i++) {
      pocket_bottom_vnodes.push(
        m(
          "div.pocket-square",
          {
            style: `left: ${i * square_width}%; top: 0; width: ${square_width}%; height: ${square_height}%;`,
          },
          [
            m("div.piece", {
              style: `background-image: url("${theme.pieces.get(blackpocket[i])}");`,
            }),
            m("div.piece-count", `${pocket.black.get(blackpocket[i])}`),
          ],
        ),
      );
    }
  }

  let rank = 0;
  let file = 0;
  for (i = 0; i < board_elements.length; i++) {
    rank = Math.floor(i / BoardWidth);
    file = i % BoardWidth;
    board_vnodes.push(
      m(
        "div.board-square",
        {
          style: `left: ${file * square_width}%; top: ${rank * square_height}%; width: ${square_width}%; height: ${square_height}%;`,
        },
        board_elements[i],
      ),
    );
  }

  return m(
    "div.pgn-board-element",
    {
      style: `--pgn-board-aspect-ratio: ${aspect_ratio};`,
    },
    [
      m(
        "div.pgn-board-pocket-top",
        {
          style: `width: ${pocket_element_width}%; height: ${pocket_element_height}%;`,
        },
        pocket_top_vnodes,
      ),
      m(
        "div.pgn-board-board",
        {
          style: `background-image: url("${theme.board}"); width: ${board_element_width}%; height: ${board_element_height}%;`,
        },
        board_vnodes,
      ),
      m(
        "div.pgn-board-pocket-bottom",
        {
          style: `width: ${pocket_element_width}%; height: ${pocket_element_height}%;`,
        },
        pocket_bottom_vnodes,
      ),
    ],
  );
}
