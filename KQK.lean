/-
  King + Queen vs King, formalized in Lean 4 (core library only, no Mathlib).

  Structure of a formalization:
    1. DEFINITIONS  – turn the informal notions (board, attack, check, mate)
                      into precise mathematical objects.
    2. STATEMENTS   – write down claims about those objects as types.
    3. PROOFS       – terms of those types; Lean's kernel checks every one.
-/

/-! ## 1. Definitions -/

/-- A square is (file, rank), each 0..7.  a1 = (0,0), h8 = (7,7). -/
abbrev Square := Fin 8 × Fin 8

/-- Handy constructor: `sq 'e' 4` is e4. -/
def sq (f : Char) (r : Nat) : Square :=
  (⟨(f.toNat - 'a'.toNat) % 8, Nat.mod_lt _ (by decide)⟩,
   ⟨(r - 1) % 8, Nat.mod_lt _ (by decide)⟩)

inductive Color | white | black
  deriving DecidableEq, Repr

/-- The whole game state: three pieces and whose turn it is. -/
structure Position where
  wK : Square
  wQ : Square
  bK : Square
  toMove : Color

def fx (s : Square) : Int := s.1.val
def fy (s : Square) : Int := s.2.val

/-- King-adjacency (distinct squares at Chebyshev distance 1). -/
def adjacent (a b : Square) : Bool :=
  a != b && (fx a - fx b).natAbs ≤ 1 && (fy a - fy b).natAbs ≤ 1

/-- Does a queen on `q` attack square `t`, if the only possible blocker is
    on `blk`?  (Same rank, file or diagonal, and `blk` not strictly between.) -/
def queenAttacks (q t blk : Square) : Bool :=
  let dx := fx t - fx q
  let dy := fy t - fy q
  let aligned := q != t && (dx == 0 || dy == 0 || dx.natAbs == dy.natAbs)
  let n := max dx.natAbs dy.natAbs
  let sx := dx.sign
  let sy := dy.sign
  let blocked := (List.range n).any fun k =>
    k ≠ 0 && fx q + k * sx == fx blk && fy q + k * sy == fy blk
  aligned && !blocked

/-- All 64 squares. -/
def allSquares : List Square :=
  (List.finRange 8).flatMap fun f => (List.finRange 8).map fun r => (f, r)

/-- The black king is in check: the queen sees it (the white king can block).
    A king never gives check itself in a legal position. -/
def blackInCheck (p : Position) : Bool :=
  queenAttacks p.wQ p.bK p.wK

/-- Can the black king legally step to `t`?
    - one step away, not onto the white king, not next to the white king;
    - if it captures the queen, the queen is gone, so only the white king matters;
    - otherwise `t` must not be attacked by the queen.
    The black king is *not* a blocker here, so it can't "hide behind itself"
    by retreating along the queen's line. -/
def blackCanMoveTo (p : Position) (t : Square) : Bool :=
  adjacent p.bK t && t != p.wK && !adjacent p.wK t &&
  (t == p.wQ || !queenAttacks p.wQ t p.wK)

def blackHasMove (p : Position) : Bool :=
  allSquares.any (blackCanMoveTo p)

/-- A position is legal if the pieces are on distinct squares, the kings aren't
    touching, and the side NOT to move isn't in check. -/
def legal (p : Position) : Bool :=
  p.wK != p.wQ && p.wK != p.bK && p.wQ != p.bK && !adjacent p.wK p.bK &&
  (p.toMove == .black || !blackInCheck p)

def isCheckmate (p : Position) : Bool :=
  legal p && p.toMove == .black && blackInCheck p && !blackHasMove p

def isStalemate (p : Position) : Bool :=
  legal p && p.toMove == .black && !blackInCheck p && !blackHasMove p

/-- White queen moves (king moves omitted to keep this small). -/
def queenCanMoveTo (p : Position) (t : Square) : Bool :=
  t != p.wK && t != p.bK && queenAttacks p.wQ t p.wK

/-- White (to move) can mate in one with a queen move. -/
def mateInOneQ (p : Position) : Bool :=
  p.toMove == .white && legal p &&
  allSquares.any fun t =>
    queenCanMoveTo p t && isCheckmate { p with wQ := t, toMove := .black }

/-! ## 2 & 3. Statements and proofs -/

/-- Black: Ka8.  White: Kb6, Qb7.  Black to move. -/
def mate1 : Position := ⟨sq 'b' 6, sq 'b' 7, sq 'a' 8, .black⟩

/-- Proved by `decide`: Lean evaluates the definitions and checks the result. -/
theorem mate1_is_checkmate : isCheckmate mate1 = true := by decide

/-- Your original claim, stated literally: every legal position is checkmate. -/
def AlwaysMate : Prop := ∀ p : Position, legal p = true → isCheckmate p = true

/-- ...and it's false. One counterexample is enough: black king on e8,
    white king e1, queen d1, black to move: not even check. -/
theorem not_always_mate : ¬ AlwaysMate := by
  intro h
  have := h ⟨sq 'e' 1, sq 'd' 1, sq 'e' 8, .black⟩ (by decide)
  exact absurd this (by decide)

/-- A sharper counterexample: a stalemate. Ka8 / Kb6, Qc7, black to move. -/
theorem stalemate_exists :
    isStalemate ⟨sq 'b' 6, sq 'c' 7, sq 'a' 8, .black⟩ = true := by decide

/-- Same pieces but WHITE to move: Qb7 is mate in one. -/
theorem mate_in_one :
    mateInOneQ ⟨sq 'b' 6, sq 'c' 7, sq 'a' 8, .white⟩ = true := by decide

/-- A real universal theorem, over all 64³ placements:
    in every KQ-vs-K checkmate, the black king is on the edge of the board.
    `native_decide` compiles the check to machine code and runs it; that is
    faster than `decide` but it trusts the compiler, not only the kernel. -/
def onEdge (s : Square) : Bool :=
  s.1.val == 0 || s.1.val == 7 || s.2.val == 0 || s.2.val == 7

theorem mate_only_on_edge :
    ∀ k ∈ allSquares, ∀ q ∈ allSquares, ∀ b ∈ allSquares,
      isCheckmate ⟨k, q, b, .black⟩ = true → onEdge b = true := by
  native_decide
