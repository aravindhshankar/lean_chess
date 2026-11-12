/-
  ════════════════════════════════════════════════════════════════════════════
   King + Queen vs King: white ALWAYS wins.
   A Lean 4 formalization via "a winning method + a proof that it works".
  ════════════════════════════════════════════════════════════════════════════

  Lean 4, core library only (no Mathlib). Checked with Lean 4.15.

  The file has three parts:

    PART 1  Games in general (no chess here).
            What "white forces mate" means, and the KEY THEOREM:
              a strategy + a progress measure that always goes down
              ⟹ white forces mate.
            Proved by hand, by induction. This part is reusable: when you add
            pieces, you change the game, not this proof.

    PART 2  The rules of KQ-vs-K chess, as a concrete `Game`.

    PART 3  The winning method for KQ-vs-K (a strategy plus a measure), and the
            proof that it meets the conditions of the key theorem.

  ── What counts as the "human insight" ──────────────────────────────────────
  The insight is the MEASURE in Part 3: a formula saying how close white is to
  winning. The strategy is simply "play the move that guarantees the measure
  drops the most". The one-step check that the measure really drops is done by
  computation (see `all_steps_ok`). That check only looks ONE move ahead of
  each position. It does not search the game tree for a mate.
-/


/-══════════════════════════════════════════════════════════════════════════
  PART 1. Games, strategies, and the key theorem
══════════════════════════════════════════════════════════════════════════-/

/-- A two-player game, seen from white's side.
    `Pos` is the set of positions. Whose turn it is is implicit:
    `whiteMoves` is applied to positions with white to move, and
    `blackMoves` to positions with black to move. -/
structure Game where
  Pos          : Type
  whiteMoves   : Pos → List Pos   -- all legal white moves (resulting positions)
  blackMoves   : Pos → List Pos   -- all legal black moves (resulting positions)
  blackInCheck : Pos → Bool

namespace Game

variable (G : Game)

/-- Black (to move) is checkmated: in check, with no legal move. -/
def Mated (q : G.Pos) : Prop :=
  G.blackInCheck q = true ∧ G.blackMoves q = []

/-- `WhiteWins p`: from position `p` (white to move), white can FORCE mate.

    This is an INDUCTIVE definition. A proof of `WhiteWins p` is a finite tree,
    built from these two rules:

    * `mate`: white has a move to a position where black is mated.
    * `step`: white has a move `q` after which black is NOT stalemated
      (black has at least one move), and EVERY black reply `r` is again a
      `WhiteWins` position.

    Because a proof is a finite object, "white wins" automatically means
    "white wins in finitely many moves". Black wandering around forever
    doesn't count as a win for white.

    Stalemate (no black moves and not in check) fits neither rule, so it's
    correctly not a win. If black can capture the queen, then the resulting
    position must also be `WhiteWins`. That's impossible with a lone king (white
    has no mating material), so the definition forbids hanging the queen
    without saying so explicitly. -/
inductive WhiteWins : G.Pos → Prop
  | mate {p q : G.Pos} :
      q ∈ G.whiteMoves p → G.Mated q → WhiteWins p
  | step {p q : G.Pos} :
      q ∈ G.whiteMoves p →
      G.blackMoves q ≠ [] →
      (∀ r ∈ G.blackMoves q, WhiteWins r) →
      WhiteWins p

/-- A WINNING METHOD consists of
    * `Good`: the set of positions the method claims to win from;
    * `move`: which move to play in each position (the strategy);
    * `measure`: a natural number, "how far from done";
    together with two promises:
    * `move_legal`: the chosen move is legal;
    * `progress`: after the chosen move, either black is mated, or black
      has a move, and EVERY black reply lands in a `Good` position with a
      strictly SMALLER measure.

    A natural number can't decrease forever, so the game must end, and the
    only way it can end is in mate. That's the key theorem below. -/
structure WinningMethod where
  Good       : G.Pos → Prop
  move       : G.Pos → G.Pos
  measure    : G.Pos → Nat
  move_legal : ∀ p, Good p → move p ∈ G.whiteMoves p
  progress   : ∀ p, Good p →
                 G.Mated (move p) ∨
                 (G.blackMoves (move p) ≠ [] ∧
                  ∀ r ∈ G.blackMoves (move p), Good r ∧ measure r < measure p)

/-- THE KEY THEOREM: a winning method really wins.

    Proof idea: show, by induction on `n`, that white wins from every good
    position whose measure is below `n`.
    * n = 0: no natural number is below 0, so there's nothing to prove.
    * n+1: take a good position `p` with measure ≤ n. Play the method's move.
      If that's mate, done (`mate` rule). Otherwise every black reply `r`
      is good and has measure < measure p ≤ n, so the induction hypothesis
      says white wins from `r`. Then the `step` rule applies. -/
theorem WinningMethod.wins (S : WinningMethod G) :
    ∀ p, S.Good p → G.WhiteWins p := by
  have key : ∀ n p, S.measure p < n → S.Good p → G.WhiteWins p := by
    intro n
    induction n with
    | zero => intro p h; exact absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro p hlt hp
      rcases S.progress p hp with hmate | ⟨hne, hall⟩
      · exact .mate (S.move_legal p hp) hmate
      · refine .step (S.move_legal p hp) hne ?_
        intro r hr
        obtain ⟨hgood, hdec⟩ := hall r hr
        exact ih r (by omega) hgood     -- measure r < measure p ≤ n
  intro p hp
  exact key _ p (Nat.lt_succ_self _) hp

end Game


/-══════════════════════════════════════════════════════════════════════════
  PART 2. The rules of KQ vs K
══════════════════════════════════════════════════════════════════════════-/

namespace KQK

/-- A square is (file, rank), each 0..7. a1 = (0,0), h8 = (7,7). -/
abbrev Square := Fin 8 × Fin 8

def X (s : Square) : Int := s.1.val   -- file as an integer
def Y (s : Square) : Int := s.2.val   -- rank as an integer

/-- The square at integer coordinates (x, y), if that's on the board. -/
def mkSq (x y : Int) : Option Square :=
  if h : 0 ≤ x ∧ x < 8 ∧ 0 ≤ y ∧ y < 8 then
    some (⟨x.toNat, by omega⟩, ⟨y.toNat, by omega⟩)
  else none

/-- `sq 'e' 4` is e4 (for writing examples). -/
def sq (f : Char) (r : Nat) : Square :=
  (⟨(f.toNat - 'a'.toNat) % 8, Nat.mod_lt _ (by decide)⟩,
   ⟨(r - 1) % 8, Nat.mod_lt _ (by decide)⟩)

/-- All 64 squares. -/
def allSquares : List Square :=
  (List.finRange 8).flatMap fun f => (List.finRange 8).map fun r => (f, r)

/-- A position. The queen is an `Option`: `none` means black has captured it.
    Making the queen optional is what lets the rules talk about captures at
    all. (With more pieces you'd do the same for each piece.) -/
structure Pos where
  wK : Square
  wQ : Option Square
  bK : Square
  deriving DecidableEq, Repr

/-- The 8 king directions. -/
def dirs : List (Int × Int) :=
  [(1,0), (-1,0), (0,1), (0,-1), (1,1), (1,-1), (-1,1), (-1,-1)]

/-- The squares a king on `s` could step to (ignoring everything else). -/
def neighbors (s : Square) : List Square :=
  dirs.filterMap fun d => mkSq (X s + d.1) (Y s + d.2)

/-- Two distinct squares that touch (king distance 1). -/
def adjacent (a b : Square) : Bool :=
  a != b && (X a - X b).natAbs ≤ 1 && (Y a - Y b).natAbs ≤ 1

/-- Does a queen on `q` see square `t` along a rank, file or diagonal, with
    none of the `blockers` strictly in between? One definition is used both
    for "the queen attacks t" and for "the queen can move to t". -/
def sees (q t : Square) (blockers : List Square) : Bool :=
  let dx := X t - X q
  let dy := Y t - Y q
  let aligned := q != t && (dx == 0 || dy == 0 || dx.natAbs == dy.natAbs)
  let n := max dx.natAbs dy.natAbs
  let blocked := (List.range n).any fun k =>
    k != 0 && blockers.any fun b =>
      X q + k * dx.sign == X b && Y q + k * dy.sign == Y b
  aligned && !blocked

/-- Black is in check: the queen sees the black king (the white king can
    block). Without a queen, there's no check. -/
def blackInCheck (p : Pos) : Bool :=
  match p.wQ with
  | some q => sees q p.bK [p.wK]
  | none   => false

/-- White's legal moves.
    * King: one step, not onto the queen or the black king, and not next to the
      black king.
    * Queen: slide to any square it sees (both kings block), not onto either
      king.
    (In KQ vs K, white is never in check, so no other rules are needed.) -/
def whiteMoves (p : Pos) : List Pos :=
  let kingMoves :=
    ((neighbors p.wK).filter fun t =>
        some t != p.wQ && t != p.bK && !adjacent t p.bK)
      |>.map fun t => { p with wK := t }
  let queenMoves :=
    match p.wQ with
    | none   => []
    | some q =>
      (allSquares.filter fun t => t != p.wK && t != p.bK && sees q t [p.wK, p.bK])
        |>.map fun t => { p with wQ := some t }
  kingMoves ++ queenMoves

/-- Black's legal moves: one king step, not onto or next to the white king.
    * Stepping onto the queen captures it (the queen becomes `none`). That's
      legal exactly when the white king isn't defending it, which is already
      covered by "not next to the white king".
    * Otherwise the target must not be attacked by the queen. The black king
      is NOT used as a blocker here, so it can't escape a check by retreating
      along the queen's line. -/
def blackMoves (p : Pos) : List Pos :=
  (neighbors p.bK).filterMap fun t =>
    if t == p.wK || adjacent p.wK t then none
    else match p.wQ with
      | some q =>
        if t == q then some { p with bK := t, wQ := none }       -- capture
        else if sees q t [p.wK] then none                         -- attacked
        else some { p with bK := t }
      | none => some { p with bK := t }

/-- KQ vs K as an instance of the general `Game` from Part 1. -/
def game : Game where
  Pos          := Pos
  whiteMoves   := whiteMoves
  blackMoves   := blackMoves
  blackInCheck := blackInCheck

/-- A legal position with WHITE to move: the queen is on the board, all
    pieces are on different squares, the kings don't touch, and black is not in
    check (black just moved, so it can't have left its king in check). -/
def legalWhiteToMove (p : Pos) : Bool :=
  match p.wQ with
  | none   => false
  | some q => p.wK != q && p.wK != p.bK && q != p.bK &&
              !adjacent p.wK p.bK && !blackInCheck p


/-══════════════════════════════════════════════════════════════════════════
  PART 3. The winning method for KQ vs K
══════════════════════════════════════════════════════════════════════════-/

/-! ### The measure: how far is white from winning?

  The chess idea is the "box". The queen's rank and file cut the board into
  four rectangles, and the black king is trapped in one of them, because it
  can't cross a line the queen controls. Say that box is `w` files wide and `h`
  ranks tall. White's plan:

    (a) Shrink the box with the queen.
    (b) When the queen can't safely shrink it (the black king is guarding the
        next square), walk the white king toward a TARGET square next to the
        queen. From there it protects the queen's next step.
    (c) Never leave black with no legal move unless it's mate (stalemate).

  The measure combines these, most important first:

    1 000 000 · frozen      frozen = 1 if black would have NO legal move here.
                            White must never let that happen unless it's mate,
                            so it's the worst thing in the measure.
       20 000 · min(w, h)   First squeeze the black king against an edge.
        1 000 · (w + h)     Then shrink the box further.
           64 · cheb        Chebyshev (king-step) distance from the white king
                            to the target square,
            8 · manh        then Manhattan distance to it, then the distance
            1 · along       along the box's narrow side. These two tie-breakers
                            let a king that has to walk AROUND an obstacle
                            still count each step as progress.

  The weights are chosen so that each term outweighs the total of all the
  terms after it.

  Notice: the black king's moves don't change the box (it can't leave it) or
  the target (which depends only on the queen and which box). So in "king walk"
  phases, black can't undo white's progress. That's why these quantities, and
  not something like "distance between the kings", make a measure that strictly
  drops every move. Finding that was the actual work in designing this.
-/

/-- Box size (w, h) of the black king `b` relative to a queen on `q`.
    If they share a file (or rank), the box isn't closed in that direction: 8. -/
def box (q b : Square) : Nat × Nat :=
  let w := if b.1 < q.1 then q.1.val else if q.1 < b.1 then 7 - q.1.val else 8
  let h := if b.2 < q.2 then q.2.val else if q.2 < b.2 then 7 - q.2.val else 8
  (w, h)

def clamp (x : Int) : Int := max 0 (min 7 x)

/-- The measure described above. (With no queen it's 0. Such positions are
    never `Good`, so the value doesn't matter.) -/
def measure (p : Pos) : Nat :=
  match p.wQ with
  | none   => 0
  | some q =>
    let (w, h) := box q p.bK
    let frozen := if (blackMoves p).isEmpty then 1 else 0
    -- direction from the queen toward the box
    let sx := (X p.bK - X q).sign
    let sy := (Y p.bK - Y q).sign
    -- target: diagonally next to the queen, outside the box's narrow side,
    -- protecting the square the queen needs next
    let (tx, ty) :=
      if w ≤ h then (clamp (X q - sx), clamp (Y q + sy))
      else          (clamp (X q + sx), clamp (Y q - sy))
    let dx := (X p.wK - tx).natAbs
    let dy := (Y p.wK - ty).natAbs
    1000000 * frozen + 20000 * min w h + 1000 * (w + h)
      + 64 * max dx dy + 8 * (dx + dy) + (if w ≤ h then dx else dy)

/-! ### The strategy: play the move that guarantees the most progress -/

/-- How good is it for white to have reached `q` (black to move)?
    * `some 0`: black is checkmated. Best possible.
    * `none`: unacceptable (stalemate, or black can take the queen).
    * `some (1 + m)`: `m` is the largest measure black can reach in reply,
      so it's the worst case for white. -/
def score (q : Pos) : Option Nat :=
  let bm := blackMoves q
  if bm.isEmpty then (if blackInCheck q then some 0 else none)
  else if bm.any (fun r => r.wQ.isNone) then none
  else some (1 + (bm.map measure).foldl max 0)

/-- The strategy: among all legal white moves, take the first one with the
    lowest score. (If none were acceptable we'd return `p`, but Part 3 shows
    that never happens in a good position.) -/
def strategy (p : Pos) : Pos :=
  let best := (whiteMoves p).foldl
    (fun (acc : Option (Pos × Nat)) q =>
      match score q, acc with
      | none,   _            => acc
      | some s, none         => some (q, s)
      | some s, some (_, s') => if s < s' then some (q, s) else acc)
    none
  match best with
  | some (q, _) => q
  | none        => p

/-! ### The one-step check

  `stepOK p` tests, for ONE position, the two promises a winning method must
  keep: the strategy's move is legal, and afterwards it's mate, or every black
  reply is legal and has a smaller measure.

  ── Where computation comes in, and where hand proofs would go instead ──────
  `all_steps_ok` runs `stepOK` on every placement of the three pieces
  (64³ = 262 144 cases), using `native_decide`. Notes:
  * This is NOT solving chess by search. Each check looks one move ahead of
    one position. If the strategy or measure were wrong, it would fail. It
    can't discover a win on its own.
  * `native_decide` trusts Lean's compiler as well as its kernel. Proofs that
    avoid it are "more trusted".
  * This is the part that doesn't scale. With 4-5 pieces the case count
    explodes. There you'd replace this one theorem with hand proofs,
    e.g. "if the queen moves one square toward the black king, then w + h
    drops", proved by case analysis and `omega` (integer arithmetic).
    Parts 1-2 and the rest of Part 3 stay exactly as they are.
-/

def stepOK (p : Pos) : Bool :=
  !legalWhiteToMove p ||
    (let q := strategy p
     let bm := blackMoves q
     decide (q ∈ whiteMoves p) &&
     ((blackInCheck q && bm.isEmpty) ||
      (!bm.isEmpty && bm.all fun r => legalWhiteToMove r && decide (measure r < measure p))))

theorem all_steps_ok :
    ∀ k ∈ allSquares, ∀ q ∈ allSquares, ∀ b ∈ allSquares,
      stepOK ⟨k, some q, b⟩ = true := by
  native_decide

/-! ### Connecting the check to the abstract promises

  What's left is bookkeeping: turning the true/false (Bool) facts above into
  the logical statements (Prop) that `WinningMethod` asks for. -/

/-- Every square is in `allSquares` (Lean checks all 64 cases). -/
theorem mem_allSquares (s : Square) : s ∈ allSquares := by
  obtain ⟨a, b⟩ := s
  revert a b
  decide

/-- Every legal white-to-move position passes the one-step check. -/
theorem stepOK_of_legal (p : Pos) (h : legalWhiteToMove p = true) : stepOK p = true := by
  obtain ⟨k, oq, b⟩ := p
  cases oq with
  | none   => simp [legalWhiteToMove] at h
  | some q => exact all_steps_ok k (mem_allSquares k) q (mem_allSquares q) b (mem_allSquares b)

/-- Unpack `stepOK` into its parts, for a legal position. -/
theorem unpack (p : Pos) (h : legalWhiteToMove p = true) :
    strategy p ∈ whiteMoves p ∧
    ((blackInCheck (strategy p) = true ∧ blackMoves (strategy p) = []) ∨
     (blackMoves (strategy p) ≠ [] ∧
      ∀ r ∈ blackMoves (strategy p),
        legalWhiteToMove r = true ∧ measure r < measure p)) := by
  have hs := stepOK_of_legal p h
  simp only [stepOK, h, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff, Bool.not_eq_true',
    List.all_eq_true] at hs
  obtain ⟨hmem, hrest⟩ := hs
  refine ⟨hmem, ?_⟩
  rcases hrest with hm | ⟨hne, hall⟩
  · exact Or.inl hm
  · refine Or.inr ⟨?_, hall⟩
    intro he; simp [he] at hne

/-- THE WINNING METHOD for KQ vs K. -/
def method : game.WinningMethod where
  Good       := fun p => legalWhiteToMove p = true
  move       := strategy
  measure    := measure
  move_legal := fun p h => (unpack p h).1
  progress   := fun p h => (unpack p h).2

/-- ★ MAIN THEOREM ★
    In EVERY legal KQ-vs-K position with white to move, white can force
    checkmate. -/
theorem white_always_wins (p : Pos) (h : legalWhiteToMove p = true) :
    game.WhiteWins p :=
  Game.WinningMethod.wins game method p h

/-! ### A sanity check

  The theorem should say nothing for positions that AREN'T legal. For example,
  if black is in check with white to move, the position can't arise in a game.
  Lean confirms that such a position isn't covered. -/
example : legalWhiteToMove ⟨sq 'b' 6, some (sq 'a' 1), sq 'a' 8⟩ = false := by decide

end KQK
