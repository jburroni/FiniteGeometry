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

@[simp] def linePoints (ℓ : L) : Finset P := {ℓ, ℓ + 1, ℓ + 3}

@[simp] def incid (A : P) (ℓ : L) : Prop := A ∈ linePoints ℓ

def PG22 : IncidenceGeometry where
  Point := P
  Line  := L
  incidence := incid

/-- Membership on a Fano line = being one of its three translates. -/
@[simp] lemma mem_linePoints {A ℓ : P} :
  A ∈ linePoints ℓ ↔ A = ℓ ∨ A = ℓ + 1 ∨ A = ℓ + 3 := by
  simp [linePoints]

@[simp] lemma incid_iff {A : P} {ℓ : L} :
  PG22.incidence A ℓ ↔ A = ℓ ∨ A = ℓ + 1 ∨ A = ℓ + 3 := by
  change incid A ℓ ↔ _
  simp [incid, linePoints]



private lemma add_left_cancel_ne {x a b : ZMod 7} (h : a ≠ b) :
    x + a ≠ x + b := (add_ne_add_right x).mpr h

private lemma add_right_cancel_ne {x a b : ZMod 7} (h : a ≠ b) :
    a + x ≠ b + x := (add_ne_add_left x).mpr h

@[simp] lemma incid_self  (ℓ : L) : PG22.incidence (ℓ : P) ℓ   := by simp
@[simp] lemma incid_add1 (ℓ : L) : PG22.incidence (ℓ + 1 : P) ℓ := by simp
@[simp] lemma incid_add3 (ℓ : L) : PG22.incidence (ℓ + 3 : P) ℓ := by simp

lemma exists_three_distinct_points_on_line (ℓ : PG22.Line) :
  ∃ A B C, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ A ∈ᵢ ℓ ∧ B ∈ᵢ ℓ ∧ C ∈ᵢ ℓ := by
  let ℓp : P := ℓ
  refine ⟨ℓp, ℓp + 1, ℓp + 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h01 : (0 : ZMod 7) ≠ 1 := by decide
    conv in (ℓp : P) => rw [←zero_add ℓp, add_comm]
    exact add_left_cancel_ne h01
  · have h03 : (0 : ZMod 7) ≠ 3 := by decide
    conv in (ℓp : P) => rw [←zero_add ℓp, add_comm]
    exact add_left_cancel_ne h03
  · have h13 : (1 : ZMod 7) ≠ 3 := by decide
    exact add_left_cancel_ne h13
  · change PG22.incidence ℓp ℓ
    subst ℓp; simp
  · change PG22.incidence (ℓp + 1) ℓ
    subst ℓp; simp
  · change PG22.incidence (ℓp + 3) ℓ
    subst ℓp; simp

lemma three_lines_through (A : PG22.Point) :
    ∃ ℓ m n : PG22.Line, ℓ ≠ m ∧ ℓ ≠ n ∧ m ≠ n ∧ A ∈ᵢ ℓ ∧ A ∈ᵢ m ∧ A ∈ᵢ n := by
  let Aℓ : L := A
  refine ⟨Aℓ, Aℓ - 1, Aℓ - 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    haveI : NeZero (1 : ZMod 7) := ⟨by decide⟩
    have h' : Aℓ + 1 = Aℓ := (eq_sub_iff_add_eq).mp h
    simp [add_eq_left] at *
  · intro h
    haveI : NeZero (3 : ZMod 7) := ⟨by decide⟩
    have h' : Aℓ + 3 = Aℓ := (eq_sub_iff_add_eq).mp h
    simp [add_eq_left, NeZero.ne] at *
  · simp; change (1 : ZMod 7) ≠ (3 : ZMod 7); decide
  all_goals
  · change PG22.incidence _ _
    subst Aℓ; simp


end Fano
