# How the KQ-vs-K proof works

This explains `KQKStrategy.lean` in plain language. The proof has three layers, and only the middle one has anything to do with chess.

## 1. What "white wins" means

Before you can prove white wins, you have to say exactly what that means. The file defines it from two rules. White wins from a position if:

- white has a move that checkmates immediately, or
- white has a move after which black isn't stalemated, and every black reply leads to a position from which white again wins.

Lean only accepts a "white wins" claim if it is built from these two rules a finite number of times. So the definition automatically means "white wins in a finite number of moves".

The rules also cover the traps without mentioning them:

- **Stalemate** fits neither rule, so it isn't a win.
- **Hanging the queen:** if black can take the queen, that reply would also have to be a winning position for white. A bare king can't win, so hanging the queen is ruled out.

## 2. The key theorem: a method plus a countdown gives a win

Suppose you have three things:

- a **strategy**, which tells white what to play in every position;
- a **measure**, a whole number attached to each position, meaning roughly "how much work is left";
- a **promise**: after white plays the strategy's move, either it's mate, or whatever black replies, the new position has a strictly smaller measure.

Then white wins.

The reason is that a whole number can't keep going down forever: from 1000 you can step down at most 1000 times. So the game can't go on forever. And the only way it can end under these rules is checkmate, because stalemate and losing the queen are excluded by the promise.

In Lean this is a short induction proof (`Game.WinningMethod.wins`), and it knows nothing about chess. That's the reusable part: with more pieces, you write a new strategy and measure and use the same theorem.

## 3. The chess part: which strategy and which measure

The human insight goes here. It's the classic **box method**. The queen's row and column cut the board into rectangles. The black king is trapped in one of them, its box, because it can't step onto a line the queen controls.

White's plan:

- shrink the box with the queen whenever that's safe;
- if the black king guards the square the queen needs, bring the white king to a square next to the queen where it can protect that square;
- never take away all of black's moves unless it's mate.

The **measure** turns that plan into a number. In order of importance, it counts:

1. a huge penalty if black has no legal moves (stalemate danger);
2. how close the black king is to an edge;
3. how big the box is;
4. how far the white king is from its target square.

The subtle part was choosing the white king's target. My first attempt measured "distance between the two kings". It failed: black can step away each move and undo white's progress. Black's moves can't change the box or the target square (they depend only on the queen and the box), so black can never undo progress on those. I tested candidate measures in Python and kept refining them until no position broke the promise.

The **strategy** is then simply: play the move that guarantees the lowest measure, whatever black replies. Following it, white mates in at most 17 moves (perfect play needs at most 10).

## 4. Checking the promise

One fact remains: in every legal position, the strategy's move keeps the promise. That's the theorem `all_steps_ok`.

Lean checks it position by position, all 262,144 placements of the three pieces, looking only one move ahead each time. This is different from solving chess by brute force:

- A **brute-force solver** searches deep into the game to *find* wins.
- Here Lean only *confirms* that my strategy and measure behave as claimed one move at a time. If the strategy were bad, the check would simply fail.

The rest of the file is bookkeeping that turns this check into the exact form the key theorem needs.

## Result

Combining sections 2 and 4 gives the main theorem, `white_always_wins`: in every legal position with white to move, white can force mate.

## Limits to keep in mind

- **The definitions are trusted.** Lean guarantees the proof is correct *given the definitions*. If the move rules had a bug, the theorem would be about the wrong game, so read Part 2 of the file critically.
- **`native_decide` trusts the compiler.** It relies on Lean's compiler as well as its core checker.
- **The check doesn't scale.** With 5 pieces there are far too many positions. You'd replace that one theorem with hand proofs of the geometric facts ("this queen move shrinks the box"). Layers 1 and 2 stay as they are.
