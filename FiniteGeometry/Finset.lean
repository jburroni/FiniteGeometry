import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic


namespace Finset
open Finset
variable {α : Type*} [DecidableEq α]
theorem mem_compl_singleton {a b : α} [Fintype α] : a ∈ ({b}ᶜ : Finset α) ↔ a ≠ b := by
  simp only [mem_compl, mem_singleton, ne_eq]

lemma card_finset_three {A B C : α} (hAB : A ≠ B) (hAC : A ≠ C)
    (hBC : B ≠ C) : #{A, B, C} = 3 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  repeat simp [hBC, hAB, hAC]


end Finset

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
  · left; ext x; simp; tauto
  · right; left; ext x; simp; tauto
  · right; right; left; ext x; simp; tauto
  · left; ext x; simp; tauto
  · right; left; ext y; simp; tauto
  · left; ext x; simp; tauto
  · right; left; ext x; simp; tauto
  · right; right; right; ext x; simp; tauto
  · left; ext x; simp; tauto
  · right; right; left; ext x; simp; tauto
  · left; ext x; simp; tauto
  · right; right; right; ext x; simp; tauto
  · right; right; left; ext y; simp; tauto
  · right; right; right; ext z; simp; tauto
  · right; left; ext x; simp; tauto
  · right; right; left; ext y; simp; tauto
  · right; left; ext z; simp; tauto
  · right; right; right; ext w; simp; tauto
  · right; right; left; ext y; simp; tauto
  · right; right; right; ext z; simp; tauto


end Set
