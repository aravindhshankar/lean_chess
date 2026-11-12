# Plan: formal proofs of king and pawn endgames, the human way

## Objective

Prove results about king and pawn endgames in Lean **the way a strong human player understands them**: through strategies and concepts such as key squares, opposition, the square of the pawn and the outside passed pawn. Lean's role is to make those human arguments fully rigorous.

Long-term goal: cover every king and pawn endgame. KPK is the first step.

## Guiding principle: no brute force

Endgame databases solve endings by searching every position. **That is explicitly not the goal here.** Rules for this project:

1. **Proofs follow human reasoning.** Every theorem comes with a strategy a player could follow (and for draws, a defence), and with a *reason* it works: a progress measure, an invariant, a geometric fact.
2. **No game-tree search in proofs.** Nothing computes "the value of this position" by exploring moves.
3. **Position-by-position checks are temporary scaffolding.** The current KQK proof checks one move ahead in every position with `native_decide`. That's acceptable as a stepping stone, but each such check is marked `-- SCAFFOLD:` in the code and tracked in the table below, with the goal of replacing it by a symbolic proof: lemmas about coordinates, proved by case analysis and tactics like `omega`.
4. **Computers may test conjectures, not prove them.** A Python endgame table may be used *outside* the proofs as a lie detector: to find the exact conditions under which a rule of thumb holds before trying to prove it. It never appears in a Lean proof.

## Decisions taken

| Question | Decision |
|---|---|
| Library | A Lean project built with Lake, using **Mathlib** (Lean's large shared mathematics library) |
| 50-move rule | **Ignored.** Endless play counts as a draw. |
| Ambition for KPK | **Full classification:** every KPK position shown to be a win or a draw, each case by a human strategy (wins) or a human defence (draws) |
| Reuse of KQK | Keep the existing proof as a **compiled, importable module** (see below) |

## Reusing KQK without recompiling it

Lean projects are split into modules (files). Lake, Lean's build tool, compiles each module once into a `.olean` file: a compiled record of all its definitions and proved theorems. Another file that writes `import Endgames.KQK.Original` just loads that record. **The proof isn't rerun**, including the slow `native_decide` check. A module is only recompiled when it, or a module it imports, changes.

To make KQK essentially "compile once, never again":

- **Freeze it.** Keep `KQKStrategy.lean` as its own module, `Endgames/KQK/Original.lean`, with its own small rules and no imports from the rest of the project. Since nothing it depends on ever changes, it never needs recompiling.
- **Bridge it.** A separate file, `Endgames/KQK/Bridge.lean`, proves that the KQK game sits exactly inside the new general chess rules (same moves, same checks). Then the general embedding lemma carries the theorem `white_always_wins` into the new setting. If the general rules change, only the bridge is rebuilt, not the KQK proof.
- **Caveat:** Mathlib requires a specific Lean version, newer than the 4.15 the file was tested on. When the project is set up, `Original.lean` may need small syntax fixes and **one** final compile under the new version. After that it's cached.
- KQK's `native_decide` check is itself scaffolding by the rules above. Replacing it with a symbolic proof is a later, optional task (see the table at the end). The frozen module can stay in use until then.

## Project layout

```
KPEndgames/
  lakefile.lean            -- build setup, Mathlib dependency
  Game/
    Basic.lean             -- games, positions, whose move
    Outcome.lean           -- win / draw / loss definitions
    Methods.lean           -- winning methods, holding sets (draws), chaining
    Embedding.lean         -- "a smaller game inside a bigger one" lemma
  Chess/
    Board.lean             -- squares, pieces, positions (kings, pawns, promoted pieces)
    Rules.lean             -- legal moves incl. en passant, double step, all promotions
    Symmetry.lean          -- left–right mirror, colour swap preserve results
    Geometry.lean          -- reusable facts: distances, the square of the pawn, ...
  Endgames/
    KQK/Original.lean      -- the existing proof, frozen
    KQK/Bridge.lean        -- embedding into the general rules
    KPK/...                -- concept theorems + classification
  test/                    -- move-generator tests against a chess library
  tools/                   -- Python conjecture tester (not used in proofs)
```

## The general framework (built once, reused everywhere)

- **Outcomes for both sides.** "White forces a win", "black forces a win", "draw". Wins are finite trees of moves, as in the KQK file.
- **Winning method.** Strategy + measure + promise (as in KQK), extended so a step may also land in a set of positions **already proved winning**. This lets theorems chain: distant opposition → opposition → key square → promotion → KQK.
- **Holding sets (draws).** A set of positions with a defence for black: from every position in the set, whatever white plays, black has a reply that stays in the set, and the set contains no position where black is mated or loses. Then white can't win from anywhere in the set. This is how human drawing techniques ("keep the king in front of the pawn", "take the opposition") become theorems.
- **Embedding lemma.** If game A sits faithfully inside game B, wins and draws in A are wins and draws in B.

## Roadmap

| Step | What | Done when |
|---|---|---|
| 0 | Lake project with Mathlib; folder layout as above | `lake build` succeeds on an empty skeleton |
| 1 | General framework: outcomes, winning methods with chaining, holding sets, embedding lemma | All proved, no chess involved |
| 2 | Chess rules for kings, pawns and promoted pieces | Move counts match a standard chess library on a test suite of positions |
| 3 | Symmetry theorems: mirroring files, swapping colours | Proved once, used to cut later case work |
| 4 | Freeze KQK as an importable module + bridge | `white_always_wins` available in the general setting |
| 5 | **KPK, the human way** (see below) | Every KPK position covered by a proved theorem |
| 6 | Queen-ending interface: KQ vs KP | Needed once both sides have pawns |
| 7 | KPKP, KPPK: races, the square of the pawn, outside passed pawn | First multi-pawn results |
| 8+ | General theorems for any number of pawns | Long-term goal |

## Step 5 in detail: KPK

Each rule becomes a theorem with exact conditions. The Python tester is used first to find conditions that are really true.

- **Promotion:** if the pawn can promote safely to a queen (not capturable, no stalemate), white wins, via KQK.
- **Square of the pawn:** if the black king is outside the pawn's square and can't catch it, the pawn promotes.
- **Key squares:** if the white king is on a key square of a non-rook pawn and the pawn is safe, white wins, whoever is to move.
- **Opposition:** white king in front of the pawn with the opposition wins.
- **Distant opposition:** the same, with the kings further apart.
- **Shouldering:** tested to see whether it states cleanly as a theorem, or belongs inside the strategies of the above.
- **Draws:** the defending king in front of the pawn with the opposition; rook pawns with the defending king in the corner region; stalemate defences. Each is proved with a holding set describing the human defence.
- **Classification:** every legal KPK position falls under at least one of these theorems. Ideally that's proved symbolically by case analysis. If that's not feasible at first, this coverage step is flagged as scaffolding.

Within KPK, the key-square theorem is the pilot for proving *without* position-by-position checks. It's done symbolically from the start, to learn the method before the others.

## Main risks

- **Finding progress measures and invariants** takes trial and error. That was most of the KQK effort.
- **Exact conditions near the edges** may be fiddly. An honest theorem with exceptions is still a correct theorem.
- **Symbolic proofs are much longer** than computed ones. The payoff is that they work for any amount of material.
- **Queen endings** are the boundary of the project: pawn races end in them, and some (KQ vs KQ) are very hard. Theorems claim only what the queen-ending library can support.

## Scaffolding tracker

Every place a proof relies on checking positions one by one rather than on a symbolic argument.

| Where | What it checks | Status |
|---|---|---|
| `Endgames/KQK/Original.lean`, `all_steps_ok` | Each strategy move lowers the measure, in all 262,144 KQK placements | Accepted for now; symbolic replacement optional |