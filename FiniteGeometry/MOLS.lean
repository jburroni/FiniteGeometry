import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open Finset

structure LatinSquare (n : ℕ) where
  L : Fin n → Fin n → Fin n
  row_latin {j k} : ∀ i , j ≠ k → L i j ≠ L i k
  col_latin {i k} : ∀ j, i ≠ k → L i j ≠ L k j

namespace LatinSquare

-- to support the A[(i, j)] notation
instance : GetElem (LatinSquare n) (Fin n × Fin n) (Fin n) (fun _ _ => True) where
  getElem L ij _ := L.L ij.1 ij.2

@[simp]
def pairMap {n : ℕ} (A B : LatinSquare n) : (Fin n × Fin n) → (Fin n × Fin n)
| ⟨i, j⟩ => (A[(i,j)], B[(i,j)])

@[simp]
def orthogonal {n : ℕ} (A B : LatinSquare n) : Prop :=
  Function.Injective (pairMap A B)

infix:50 " ⊥ " => orthogonal

@[simp] def orthogonal_bijective {n : ℕ} (A B : LatinSquare n) : Prop :=
  Function.Bijective (pairMap A B)

lemma orthogonal_iff_bijective {n : ℕ} (A B : LatinSquare n) :
    orthogonal A B ↔ orthogonal_bijective A B := Finite.injective_iff_bijective

end LatinSquare

section MOLS


def pairwise_orthogonal {n : ℕ} (_S : Finset (LatinSquare n)) : Prop :=
  Pairwise (fun A B ↦ (A : LatinSquare n) ⊥ (B: LatinSquare n))

lemma not_inj_of_no_zero {α : Type _} {n : ℕ} [NeZero n] {s : Finset α}
    (f : α → Fin n) (hs : s.card = n) (hf : ∀ x ∈ s, f x ≠ 0) : ¬Set.InjOn f s := by
  have img_subset : s.image f ⊆ univ \ {0} := by
    intros y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    simp [hf x hx]
  have h₀ : {0} ⊆ (univ : Finset (Fin n)) := subset_univ {0}
  intro h
  show False
  apply lt_irrefl n
  calc n = #s           := hs.symm
    _ = #(image f s)    := (Finset.card_image_of_injOn h).symm
    _ ≤ #(univ \ {0})   := Finset.card_le_card img_subset
    _ = #(univ) - #{0}  := Finset.card_sdiff h₀
    _ = n - 1           := by rw [Finset.card_singleton, Finset.card_fin n]
    _ < n               := Nat.sub_one_lt_of_lt NeZero.one_le


lemma card_MOLS_le (n : ℕ) (S : Finset (LatinSquare n)) (hS : pairwise_orthogonal S) :
    S.card ≤ n - 1 := by
  have h : S.card ≤ Fintype.card (Fin n) := by
    apply Finite.card_le_of_injective
    intro A B hAB
    simp at hAB
    exact hAB.orthogonal_iff_bijective.mp hAB
  rw [Fintype.card_fin] at h
  exact h


end MOLS

-- Fintype.equivOfCardEq requires noncomputable instances
noncomputable section KMOLS

variable {K : Type*} [Field K] [Fintype K]

def toFin : K ≃ Fin (Fintype.card K) :=
  (Fintype.equivOfCardEq (by simp)).symm


def ζ : Fin (Fintype.card K) ≃ K :=
  (toFin : K ≃ _).symm

omit [Field K] in
@[simp]
lemma fromFin_toFin (x : K) : ζ (toFin x) = x := by
  simp [ζ, toFin]

omit [Field K] in
@[simp]
lemma toFin_fromFin (i : Fin (Fintype.card K)) : toFin (ζ i) = i := by
  simp [ζ, toFin]


def L_square {m : K} (h : 0 ≠ m): LatinSquare (Fintype.card K) where
  L i j := toFin (ζ i + m * ζ j)
  row_latin {j k} := by
    intro i hneq hk
    simp at hk
    rcases hk with h₁| h₂
    · exact hneq h₁
    · exact h h₂.symm
  col_latin {i k} := by
    intro j hneq hk
    simp at hk
    exact hneq hk

lemma L_square_orth {m₁ m₂ : K} (h₀₁ : 0 ≠ m₁) (h₀₂ : 0 ≠ m₂) (h : m₁ ≠ m₂) :
    LatinSquare.orthogonal (L_square h₀₁) (L_square h₀₂) := by
  intro ⟨i, j⟩ ⟨k, l⟩ h₁
  simp at h₁
  rcases h₁ with ⟨h₁, h₂⟩
  have h₁' : ζ i + m₁ * ζ j = ζ k + m₁ * ζ l := by
    change toFin _ = toFin _ at h₁
    simpa using h₁
  have h₂' : ζ i + m₂ * ζ j = ζ k + m₂ * ζ l := by
    change toFin _ = toFin _ at h₂
    simpa using h₂
  have h_sub : (m₁ - m₂) * (ζ j - ζ l) = 0 := by
    linear_combination h₁' - h₂'

  have : m₁ - m₂ ≠ 0 := by simpa [sub_ne_zero] using h
  have h_coords : j = l := by
    have : m₁ - m₂ = 0 ∨ ζ j - ζ l = 0 := mul_eq_zero.mp h_sub
    rcases this with h_sub | h_sub
    · contradiction
    · simpa [sub_eq_zero] using h_sub
  simpa [h_coords] using h₁'


def complete_MOLS :
    {m // (0 : K) ≠ m } → LatinSquare (Fintype.card K) :=
  fun m => L_square m.property

lemma complete_MOLS_pairwise :
    Pairwise (fun m m' : {m // (0 : K) ≠ m } => (complete_MOLS m) ⊥ (complete_MOLS m')) := by
  intro m m' hneq
  apply L_square_orth
  exact fun h' => hneq (Subtype.ext h')

end KMOLS
