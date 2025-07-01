import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open Finset

structure LatinSquare (n : ℕ) where
  L : Fin n → Fin n → Fin n
  row_latin : ∀ i, Function.Injective fun j ↦ L i j
  col_latin : ∀ j, Function.Injective fun i ↦ L i j

namespace LatinSquare

variable {n : ℕ}

@[simp]
def row (L : LatinSquare n) (i : Fin n) : Fin n → Fin n :=
  fun j => L.L i j

@[simp]
def col (L : LatinSquare n) (j : Fin n) : Fin n → Fin n :=
  fun i => L.L i j

-- to support the A[(i, j)] notation
instance : GetElem (LatinSquare n) (Fin n × Fin n) (Fin n) (fun _ _ => True) where
  getElem L ij _ := L.L ij.1 ij.2

@[simp]
def pairMap (A B : LatinSquare n) : (Fin n × Fin n) → (Fin n × Fin n)
| ⟨i, j⟩ => (A[(i,j)], B[(i,j)])

@[simp]
def orthogonal (A B : LatinSquare n) : Prop :=
  Function.Injective (pairMap A B)

infix:50 " ⊥ " => orthogonal

@[simp] def orthogonal_bijective (A B : LatinSquare n) : Prop :=
  Function.Bijective (pairMap A B)

lemma orthogonal_iff_bijective (A B : LatinSquare n) :
    orthogonal A B ↔ orthogonal_bijective A B := Finite.injective_iff_bijective

noncomputable def row_equiv (A : LatinSquare n) (i : Fin n) : Fin n ≃ Fin n :=
  let bij := Finite.injective_iff_bijective.mp (A.row_latin i)
  Equiv.ofBijective (A.row i) bij

noncomputable def col_equiv (A : LatinSquare n) (j : Fin n) : Fin n ≃ Fin n :=
  let bij := Finite.injective_iff_bijective.mp (A.col_latin j)
  Equiv.ofBijective (A.col j) bij

end LatinSquare

section MOLS


def pairwise_orthogonal {n : ℕ} (_S : Finset (LatinSquare n)) : Prop :=
  Pairwise (fun A B ↦ (A : LatinSquare n) ⊥ (B: LatinSquare n))


lemma not_inj_of_not_zero {n m : ℕ} [NeZero n]  (f : Fin m → Fin n)
    (hs : n ≤ m) (hf : ∀ x, f x ≠ 0) : ¬Function.Injective f := by
  rcases Nat.eq_or_lt_of_le hs with rfl | h_lt
  · simp [Finite.injective_iff_surjective]
    simpa [Function.Surjective] using ⟨0, hf⟩
  · apply mt (Finite.card_le_of_injective f); simpa

lemma not_inj_of_not_zero' {n : ℕ} [NeZero n] (S : Finset (LatinSquare n)) (hS : n ≤ S.card)
    (f: (LatinSquare n) → Fin n) (hf : ∀ A, f A ≠ 0) : ∃ A ∈ S, ∃ B ∈ S, A ≠ B ∧ f A = f B := by
  let to_S i : LatinSquare n := (Finset.equivFin S).symm i
  let g := f ∘ to_S
  have ⟨i, j, ⟨f_eq, ij_neq⟩⟩ : ∃ i j, g i = g j ∧ i ≠ j := by
    apply Function.not_injective_iff.mp
    exact not_inj_of_not_zero g hS (fun i => hf _)

  set A := to_S i; set B := to_S j
  have ⟨hA, hB⟩ : A ∈ S ∧ B ∈ S := by
    constructor <;> exact coe_mem (S.equivFin.symm _)
  have ab_neq : A ≠ B := fun h_neq => (Subtype.ext h_neq) |> S.equivFin.symm.injective |> ij_neq
  exact ⟨A, hA, B, hB, ab_neq, f_eq⟩

noncomputable def row_inv (A : LatinSquare n) (i : Fin n) : Fin n → Fin n :=
  (A.row_equiv i).symm


lemma row_inv_spec (A : LatinSquare n) (i : Fin n) (k : Fin n) :
    A.L i (row_inv A i k) = k := by
  change A.row_equiv i (row_inv A i k) = k
  simp [row_inv]


lemma card_MOLS_le (n : ℕ) (h : n ≥ 2) (S : Finset (LatinSquare n))
    (hS : pairwise_orthogonal S) : S.card ≤ n - 1 := by
  by_contra h_card
  push_neg at h_card
  have h_card : n ≤ S.card := by omega
  set one : Fin n := ⟨1, h⟩
  set zero : Fin n := ⟨0, (by linarith)⟩
  let k₀ := fun (A : LatinSquare n) ↦ A[(zero, zero)]
  have h_non_zero : ∀ (A : LatinSquare n), row_inv A one (k₀ A) ≠ zero := by
    intro A h_eq
    apply not_eq_of_beq_eq_false (a:= one) (b:=zero) rfl
    show one = zero
    have : A.L one zero = k₀ A := by rw [←h_eq, row_inv_spec]
    exact (A.col_latin zero) this
  haveI nz_n: NeZero n := NeZero.of_gt h
  let f := fun (A : LatinSquare n) ↦ row_inv A one (k₀ A)
  obtain ⟨A, hA, B, hB, ab_neq, f_eq⟩ := not_inj_of_not_zero' S h_card f h_non_zero
  set A' := row_inv A one (k₀ A) with hA'
  set B' := row_inv B one (k₀ B) with hB'
  have pair_eq : (k₀ A, k₀ B) = A.pairMap B (one, A') := by
    have : A' = B' := f_eq
    simp ; conv => enter [2,2]; rw [this]
    constructor <;> symm <;> exact row_inv_spec _ one (k₀ _)
  have pair_eq' : (k₀ A, k₀ B) = A.pairMap B (zero, zero) := by simp [k₀]
  have orthogonal : A ⊥ B := hS ab_neq
  have : (zero, zero) = (one, A') := by
    apply orthogonal.eq_iff.mp
    calc A.pairMap B (zero, zero)
      _ = (k₀ A, k₀ B)              := pair_eq'
      _ = A.pairMap B (one, A')     := pair_eq
  simp at this
  exact (not_eq_of_beq_eq_false rfl) this.1


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
  row_latin := by
    intro i j k heq
    simp at heq
    rcases heq with h₁| h₂
    · exact h₁
    · exfalso; exact h h₂.symm
  col_latin := by
    intro _ _ _ heq
    simpa using heq

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
