import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

namespace Set
variable {α : Type*}

-- increase heartbeats in the following lemma
set_option maxHeartbeats 500000 in
lemma subset_four_choose_three  {A B C D A' B' C' : α} {T : Set α} (h : T = {A', B', C'})
    (h₁ : A' ≠ B' ∧ A' ≠ C' ∧ B' ≠ C') : T ⊆ {A, B, C, D} → (T = {A, B, C}) ∨
    (T = {A, B, D}) ∨ (T = {A, C, D}) ∨ (T = {B, C, D}) := by
  subst T
  intro h₂; simp [Set.subset_def] at h₂
  -- each of A', B', C' can take any of 4 values.
  -- we analyze each of the 64 combinations;
  rcases h₂ with ⟨(rfl | rfl | rfl | rfl), (rfl | rfl | rfl | rfl), (rfl | rfl | rfl | rfl)⟩
  any_goals
    first
    | tauto
    | right; right; right; ext x; simp; tauto
    | right; right; left; ext x; simp; tauto
    | right; left; ext x; simp; tauto
    | left; ext x; simp; tauto



end Set
