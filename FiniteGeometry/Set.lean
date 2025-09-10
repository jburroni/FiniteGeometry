import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

namespace Set
variable {α : Type*}

lemma subset_four_choose_three  {A B C D A' B' C' : α} {T : Set α} (h : T = {A', B', C'})
    (h₁ : A' ≠ B' ∧ A' ≠ C' ∧ B' ≠ C') : T ⊆ {A, B, C, D} → (T = {A, B, C}) ∨
    (T = {A, B, D}) ∨ (T = {A, C, D}) ∨ (T = {B, C, D}) := by
  subst T
  obtain ⟨_, _, _⟩ := h₁
  intro h₂
  have := Set.subset_def.mp h₂
  simp at this
  rcases this with ⟨(rfl | rfl | rfl | rfl), (rfl | rfl | rfl | rfl), (rfl | rfl | rfl | rfl)⟩
  any_goals
    first
    | contradiction
    | simp
  any_goals
    first
    | right; right; right; ext x; simp; tauto
    | right; right; left; ext x; simp; tauto
  · left; ext x; simp; tauto
  · right; left; ext x; simp; tauto
  · left; ext x; simp; tauto
  · right; left; ext x; simp; tauto
  · left; ext x; simp; tauto
  · right; left; ext x; simp; tauto
  · left; ext x; simp; tauto
  · left; ext x; simp; tauto
  · right; left; ext x; simp; tauto
  · right; left; ext x
    simp [or_left_comm, or_comm, or_assoc]



end Set
