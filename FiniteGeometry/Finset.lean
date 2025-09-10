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
