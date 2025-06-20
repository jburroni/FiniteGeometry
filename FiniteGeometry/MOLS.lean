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

def pairMap {n : ℕ} (A B : LatinSquare n) : (Fin n × Fin n) → (Fin n × Fin n)
| ⟨i, j⟩ => (A[(i,j)], B[(i,j)])

@[simp]
def orthogonal {n : ℕ} (A B : LatinSquare n) : Prop :=
  ∀ {i j k l : Fin n},
    A[(i, j)] = A[(k,l)] →
    B[(i, j)] = B[(k, l)] →
    i = k ∧ j = l

infix:50 " ⊥ " => orthogonal

@[simp] def orthogonal_bijective {n : ℕ} (A B : LatinSquare n) : Prop :=
  Function.Bijective (pairMap A B)

lemma orthogonal_iff_bijective {n : ℕ} (A B : LatinSquare n) :
    orthogonal A B ↔ orthogonal_bijective A B := by
  have card_eq : Fintype.card (Fin n × Fin n) = Fintype.card (Fin n × Fin n) := rfl
  refine ⟨?inj_to_bij, ?bij_to_inj⟩
  · intro h_inj
    have h_injective : Function.Injective (pairMap A B) := by
      intro p q h_eq
      rcases p with ⟨i,j⟩
      rcases q with ⟨k,l⟩
      simp [pairMap] at h_eq
      rcases h_eq with ⟨h₁, h₂⟩
      rcases h_inj h₁ h₂ with ⟨rfl, rfl⟩
      rfl
    -- An injective map between finite sets of the same cardinality is
    -- automatically bijective.
    have h_surj : Function.Surjective (pairMap A B) := Finite.injective_iff_surjective.1 h_injective
    exact ⟨h_injective, h_surj⟩
  · intro h_bij
    intro i j k l h₁ h₂
    have h_eq : (pairMap A B) (i, j) = (pairMap A B) (k, l) := by
      simpa [Prod.ext_iff] using And.intro h₁ h₂
    have h_coords : (i, j) = (k, l) := h_bij.injective h_eq
    show i = k ∧ j = l
    simpa using h_coords

end LatinSquare

-- Fintype.equivOfCardEq requires noncomputable instances
noncomputable section MOLS

variable {K : Type*} [Field K] [Fintype K]

def toFin : K ≃ Fin (Fintype.card K) :=
  (Fintype.equivOfCardEq (by simp)).symm


def fromFin : Fin (Fintype.card K) ≃ K :=
  (toFin : K ≃ _).symm

omit [Field K] in
@[simp]
lemma fromFin_toFin (x : K) : fromFin (toFin x) = x := by
  simp [fromFin, toFin]

omit [Field K] in
@[simp]
lemma toFin_fromFin (i : Fin (Fintype.card K)) : toFin (fromFin i) = i := by
  simp [fromFin, toFin]


def L_square {m : K} (h : 0 ≠ m): LatinSquare (Fintype.card K) where
  L i j := toFin (fromFin i + m * fromFin j)
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
  intro i j k l h₁ h₂
  have h₁' : fromFin i + m₁ * fromFin j = fromFin k + m₁ * fromFin l := by
    change toFin _ = toFin _ at h₁
    simpa using h₁
  have h₂' : fromFin i + m₂ * fromFin j = fromFin k + m₂ * fromFin l := by
    change toFin _ = toFin _ at h₂
    simpa using h₂
  have h_sub : (m₁ - m₂) * (fromFin j - fromFin l) = 0 := by
    linear_combination h₁' - h₂'

  have : m₁ - m₂ ≠ 0 := by simpa [sub_ne_zero] using h
  have h_coords : j = l := by
    have : m₁ - m₂ = 0 ∨ fromFin j - fromFin l = 0 := mul_eq_zero.mp h_sub
    rcases this with h_sub | h_sub
    · contradiction
    · simpa [sub_eq_zero] using h_sub
  simp [h_coords] at *
  exact h₁'


def complete_MOLS :
    {m // (0 : K) ≠ m } → LatinSquare (Fintype.card K) :=
  fun m => L_square m.property

lemma complete_MOLS_pairwise :
    Pairwise (fun m m' : {m // (0 : K) ≠ m } => (complete_MOLS m) ⊥ (complete_MOLS m')) := by
  intro m m' hneq
  apply L_square_orth
  exact fun h' => hneq (Subtype.ext h')

end MOLS
