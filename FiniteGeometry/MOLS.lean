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

lemma row_surjective (A : LatinSquare n) (i : Fin n) : Function.Surjective (A.row i) :=
  Finite.surjective_of_injective (A.row_latin i)

lemma col_surjective (A : LatinSquare n) (j : Fin n) : Function.Surjective (A.col j) :=
  Finite.surjective_of_injective (A.col_latin j)

end LatinSquare

section MOLS


def pairwise_orthogonal {n : ℕ} (_S : Finset (LatinSquare n)) : Prop :=
  Pairwise (fun A B ↦ (A : LatinSquare n) ⊥ (B: LatinSquare n))

lemma not_inj_of_not_zero {α : Type*} {n : ℕ} [NeZero n] {s : Finset α} (f : α → Fin n)
    (hs : s.card = n) (hf : ∀ x ∈ s, f x ≠ 0) : ¬Set.InjOn f s := by
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


lemma not_inj_of_not_zero' {n m : ℕ} [NeZero n]  (f : Fin m → Fin n)
    (hs : n ≤ m) (hf : ∀ x, f x ≠ 0) : ¬Function.Injective f := by
  rcases Nat.eq_or_lt_of_le hs with rfl | h_lt
  · simp [Finite.injective_iff_surjective]
    simpa [Function.Surjective] using ⟨0, hf⟩
  · apply mt (Finite.card_le_of_injective f); simpa

noncomputable def row_inv (A : LatinSquare n) (i : Fin n) : Fin n → Fin n :=
  (A.row_equiv i).symm

lemma row_inv_spec' (A : LatinSquare n) (i : Fin n) (k : Fin n) :
    row_inv A i k = j ↔ A.L i j = k := by
  simp [row_inv, Equiv.symm_apply_eq]
  constructor
  · intro h_eq; rw [h_eq]; rfl
  · intro h_eq
    simpa [Equiv.symm_apply_eq] using h_eq.symm

lemma row_inv_spec (A : LatinSquare n) (i : Fin n) (k : Fin n) :
    A.L i (row_inv A i k) = k := by
  change A.row_equiv i (row_inv A i k) = k
  simp [row_inv]


lemma card_MOLS_le (n : ℕ) (h : n ≥ 2) (S : Finset (LatinSquare n))
    (hS : pairwise_orthogonal S) : S.card ≤ n - 1 := by
  -- Suppose S.card ≥ n
  -- Then, there are going to be two latin squares A and B in S such that
  -- A[(zero, zero)] = A[(one, zero)]
  -- and B[(zero, zero)] = B[(one, zero)]
  -- That is, ¬ Function.Injective (pairMap A B)
  by_contra h_card
  push_neg at h_card
  have h_card : n ≤ S.card := by omega
  set one : Fin n := ⟨1, h⟩
  set zero : Fin n := ⟨0, (by omega)⟩
  let k₀ := fun (A : LatinSquare n) ↦ A[(zero, zero)]
  have h_non_zero : ∀ (A : LatinSquare n), row_inv A one (k₀ A) ≠ zero := by
    intro A h
    simp [row_inv_spec' A one (k₀ A), k₀] at h
    have : one = zero := (A.col_latin zero) h
    have : zero ≠ one := not_eq_of_beq_eq_false rfl
    exact this (by omega)
  -- use the mapping between Fin m and S :  Finset (LatinSquare n)
  set m := S.card with s_card
  let index_to_latin (i : Fin m) : LatinSquare n := (Finset.equivFin S).symm i
  let f := fun (i : Fin m) ↦
    row_inv (index_to_latin i) one (k₀ (index_to_latin i))
  have : ∀ (i : Fin m), f i ≠ zero := by
    intro i
    simp [f]
    set A := index_to_latin i
    exact h_non_zero A
  haveI nz_n: NeZero n := NeZero.of_gt h
  have := not_inj_of_not_zero' f h_card this
  unfold Function.Injective at this
  push_neg at this
  rcases this with ⟨i, j, h_ij⟩
  simp [f] at h_ij
  set A := index_to_latin i
  set B := index_to_latin j
  have := row_inv_spec A one (k₀ A)
  have := row_inv_spec B one (k₀ B)

  let f := fun (A : LatinSquare n) ↦ (A[(one, zero)], k₀ A)
  have h_n₀ : ∀(A : LatinSquare n), A[(one, zero)] ≠ k₀ A := by
    intro A
    simp [k₀]
    intro h_eq
    have : one = zero := (A.col_latin zero) h_eq
    have : zero ≠ one := not_eq_of_beq_eq_false rfl
    exact this (by omega)

  set row_inv := fun (A : LatinSquare n) => by
    set f := fun j ↦ A.L one j
    have bij : Function.Bijective f :=
      Finite.surjective_iff_bijective.mp (A.row_surjective one)
    have := (Equiv.ofBijective _ bij).symm
    exact this (k₀ A)
  have : ∀ (A: LatinSquare n), row_inv A = zero → A.L one zero = k₀ A := by
    intro A h_eq
    simp [row_inv] at h_eq
    have : zero ≠ one := by omega
    have := A.row_latin one this
    simp [this] at h_eq
  have h_row_inv : ∀ (A : LatinSquare n), row_inv A ≠ zero := by
    intro A
    intro h_eq
    have : row_inv A = zero → A.L one zero = k₀ A := by
      intro h_eq
      simp [row_inv] at h_eq
      have : zero ≠ one := by omega
      have := A.row_latin one this
      simp [this] at h_eq
    have := h_n₀ A
    simp [row_inv] at h_eq
  have h_n₀ : ∀ (A : LatinSquare n), row_inv A ≠ zero := by
    intro A
    intro h_eq
    have := h_n₀ A
    simp [row_inv] at h_eq
    have : A.L one (row_inv A) = k₀ A := by
      simp [row_inv]
      let k := k₀ A
      rcases Fin.find (fun j => A.L one j = k) with - |
  have : ∀ A ∈ S, row_inv A ≠ zero := by
    intro A hA
    intro h
    have : A.L one (row_inv A) = k₀ A := by
      simp [row_inv]
      let k := k₀ A
      rcases Fin.find (fun j => A.L one j = k) with - | j
      | none =>
        exfalso
        simp [Fin.find_eq_none_iff] at *
        exact (A.row_surjective one k).elim
      | some j => rfl
    rw [h] at this  -- row_inv A = zero
    exact h_n₀ A this
    simp [row_inv, h_n₀, Fin.find_spec]
    intro h_eq
    have : zero ≠ one := by omega
    have := A.row_latin one this
    simp [this] at h_eq
  let row_inv := fun (A : LatinSquare n) i => by
    let k := k₀ A
    have j := Fin.find? (fun j => A.L one j = k)
    have : ∃ a, A.L one a = k := A.row_surjective one k
    have hj : j.isSome := by
      change ∃ a, ((A.L one a = k) = true) at this
      simp at this
      exact this
    match j with
    | some j' =>
    | Fin.succ i =>
    have := @Fin.find n (fun j => A.L i j = k) _ (A.row_surjective i k)
    let a := Fin.find this
    have : A.L i a = k := Fin.find_spec this
    obtain ⟨a, ha⟩ := this
    exact Fin.find (A.row_surjective i (k₀ A))
  let f := fun (A : LatinSquare n) =>  row_inv A one (A.L zero zero)
  have hf : ∀ A ∈ S, f A ≠ zero := by
    intro A hA
    simp [f, row_inv, Fin.find_spec]
    intro h_eq
    have : zero ≠ one := by omega
    have := A.row_latin zero this
    simp [this] at h_eq
  let f' := fun (A : LatinSquare n) =>  Fin.find (fun j => A.L one j = A.L zero zero)
  Fin.find (fun j => A.L i j = k)
  have := Fin.find (fun j => A.L i j = k)
  have hf : ∀ A ∈ S, f' A ≠ zero := by
    intro A hA
    simp [f', Fin.find_spec]
    intro h_eq
    have : zero ≠ one := by sorry
    have := A.col_latin zero this
    simp [this] at h_eq
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
