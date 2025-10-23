import FiniteGeometry.IncidenceGeometry

/-!
# The Fano plane `PG(2,2)` as an `IncidenceGeometry`

We index both points and lines by `ZMod 7`. The 7 lines are the cyclic translates of the
difference set `{0,1,3}`:
L(t) = {t, t + 1, t + 3}.
This enforces the Steiner S(2,3,7) structure.
-/

open Finset
open IncidenceGeometry
open scoped IncidenceGeometry

namespace Fano

/-- Points and lines are both indexed by `ZMod 7`. -/
abbrev P := ZMod 7
abbrev L := ZMod 7

@[simp] def incid (A : P) (ℓ : L) : Prop := A ∈ ({ℓ, ℓ + 1, ℓ + 3} : Finset P)

def PG22 : IncidenceGeometry where
  Point := P
  Line  := L
  incidence := incid

@[simp] lemma incid_iff {A : P} {ℓ : L} :
    PG22.incidence A ℓ ↔ A = ℓ ∨ A = ℓ + 1 ∨ A = ℓ + 3 := by
  change incid A ℓ ↔ _
  simp




lemma exists_three_distinct_points_on_line (ℓ : PG22.Line) :
  ∃ A B C, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ A ∈ᵢ ℓ ∧ B ∈ᵢ ℓ ∧ C ∈ᵢ ℓ := by
  let ℓp : P := ℓ
  refine ⟨ℓp, ℓp + 1, ℓp + 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (ℓp : ZMod 7) ≠ (ℓp : ZMod 7) + _; simp; decide
  · change (ℓp : ZMod 7) ≠ (ℓp : ZMod 7) + _; simp; decide
  · change (ℓp : ZMod 7) + _≠ (ℓp : ZMod 7) + _; simp; decide
  all_goals
  · change PG22.incidence _ _; subst ℓp; simp

lemma three_lines_through (A : PG22.Point) :
    ∃ ℓ m n : PG22.Line, ℓ ≠ m ∧ ℓ ≠ n ∧ m ≠ n ∧ A ∈ᵢ ℓ ∧ A ∈ᵢ m ∧ A ∈ᵢ n := by
  let Aℓ : L := A
  refine ⟨Aℓ, Aℓ + 6, Aℓ + 4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (Aℓ : ZMod 7) ≠ (Aℓ : ZMod 7) + _; simp; decide
  · change (Aℓ : ZMod 7) ≠ (Aℓ : ZMod 7) + _; simp; decide
  · change (Aℓ : ZMod 7) + _ ≠ (Aℓ : ZMod 7) + _; simp; decide
  all_goals
  · change PG22.incidence _ _
    subst Aℓ; simp [add_assoc]
    try ring_nf; decide





end Fano
