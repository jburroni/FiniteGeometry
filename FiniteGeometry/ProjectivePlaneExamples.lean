import FiniteGeometry.IncidenceGeometry

/-!
# The Fano plane `PG(2,2)` as an `IncidenceGeometry`

We index both points and lines by `ZMod 7`.  The 7 lines are the cyclic translates of the
difference set `{0,1,3}`:
L(t) = {t, t + 1, t + 3}.
This already enforces the Steiner S(2,3,7) structure.
-/

open IncidenceGeometry
open Finset

namespace Fano

/-- Points and lines are both indexed by `ZMod 7`. -/
abbrev P := ZMod 7
abbrev L := ZMod 7

/-- The three points on the line indexed by `ℓ`. -/
@[simp] def linePoints (ℓ : L) : Finset P := {ℓ, ℓ + 1, ℓ + 3}

/-- Incidence for the Fano plane. -/
@[simp] def incid (A : P) (ℓ : L) : Prop := A ∈ linePoints ℓ

def G : IncidenceGeometry where
  Point := P
  Line  := L
  incidence := incid

notation:50 "PG22" => G

/-- Membership on a Fano line = being one of its three translates. -/
@[simp] lemma mem_linePoints {A ℓ : P} :
  A ∈ linePoints ℓ ↔ A = ℓ ∨ A = ℓ + 1 ∨ A = ℓ + 3 := by
  simp [linePoints]

@[simp] lemma incid_iff {A : P} {ℓ : L} :
  (A ∈ᵢ (ℓ : G.Line)) ↔ A = ℓ ∨ A = ℓ + 1 ∨ A = ℓ + 3 := by
  -- just unfold the geometry’s incidence
  change incid A ℓ ↔ _
  simp [incid, linePoints]

/-! ## Two tiny, very useful witnesses

* `three_points_on`: every line visibly has three distinct points.
* `three_lines_through`: every point lies on the three lines indexed
  by `A`, `A-1` and `A-3`.

These are the “P3/P4” parts of a projective plane.
-/

/-- Every line has three distinct points on it. -/
lemma three_points_on (ℓ : PG22.Line) :
    ∃ A B C : PG22.Point,
      A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      A ∈ᵢ ℓ ∧ B ∈ᵢ ℓ ∧ C ∈ᵢ ℓ := by
  -- take `A = ℓ`, `B = ℓ+1`, `C = ℓ+3`
  refine ⟨ℓ, ℓ + 1, ℓ + 3, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · -- `ℓ ≠ ℓ + 1`
    intro h; have : (0 : P) = 1 := by
      simpa using congrArg (fun x : P => x - ℓ) h
    exact (by decide : (0:P) ≠ 1) this
  · -- `ℓ ≠ ℓ + 3`
    intro h; have : (0 : P) = 3 := by
      simpa using congrArg (fun x : P => x - ℓ) h
    exact (by decide : (0:P) ≠ 3) this
  · -- `(ℓ + 1) ≠ (ℓ + 3)`
    intro h; have : (1 : P) = 3 := by
      simpa using congrArg (fun x : P => x - ℓ) h
    exact (by decide : (1:P) ≠ 3) this

/-- Three different lines through each point. -/
lemma three_lines_through (A : PG22.Point) :
    ∃ ℓ m n : PG22.Line,
      ℓ ≠ m ∧ ℓ ≠ n ∧ m ≠ n ∧
      A ∈ᵢ ℓ ∧ A ∈ᵢ m ∧ A ∈ᵢ n := by
  -- take `ℓ = A`, `m = A - 1`, `n = A - 3`
  refine ⟨A, A - 1, A - 3, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · intro h; have := congrArg (fun x : P => x - A) h; simpa using this
  · intro h; have := congrArg (fun x : P => x - A) h; simpa using this
  · intro h
    have : (2 : P) = 0 := by
      simpa using congrArg (fun x : P => x - A) h
    exact (by decide : (2:P) ≠ 0) this

/-!
### Optional (nice to have)

If you also want “unique line through two distinct points” and
“two lines meet in a unique point”, the following *computable*
helpers are a neat fit with this model:

* `through p q` — pick the unique index of the line containing `p` and `q`
  by case-splitting on the difference `q - p ∈ {±1,±2,±3}`.
* `meet ℓ m` — the unique intersection point, by a tiny split on `m - ℓ`.

They’re short, but the uniqueness proofs are a (routine) 6-case
check; add them if/when you want a full `[ProjectivePlane PG22]`
instance.
-/

/-- A concise “line through two points” chooser.
(It returns the right line even when `p=q`; uniqueness is the only
place you’ll need `p ≠ q`.) -/
def through (p q : PG22.Point) : PG22.Line :=
  let d : P := q - p
  p - if d = 1 ∨ d = 3 then (0:P)
      else if d = 2 ∨ d = 6 then 1
      else 3

/-- For convenience: membership on a line written as equalities. -/
lemma incid_cases {p ℓ : PG22.Point} (h : p ∈ᵢ ℓ) :
    p = ℓ ∨ p = ℓ + 1 ∨ p = ℓ + 3 := by
  simpa [incid, linePoints] using h

end Fano
