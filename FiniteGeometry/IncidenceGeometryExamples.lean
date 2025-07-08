import FiniteGeometry.IncidenceGeometry


namespace Finset
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
theorem mem_compl_singleton {a b : α} : a ∈ ({b}ᶜ : Finset α) ↔ a ≠ b := by
  simp only [mem_compl, mem_singleton, ne_eq]
end Finset

section Examples
-- To avoid linter warnings when simpa is applied to many goals
set_option linter.unnecessarySimpa false
open Finset

def steinerS335 : IncidenceGeometry where
  Point := Fin 5
  Line := { s : Finset (Fin 5) // #s = 3 }
  incidence := fun p b ↦ p ∈ b.val

def affineAG22 : IncidenceGeometry where
  Point := Fin 4
  Line := { s : Finset (Fin 4) // s.card = 2 }
  incidence := fun p b ↦ p ∈ b.val


namespace affineAG22Props

namespace affineAG22
def pencil (p : affineAG22.Point) : Finset affineAG22.Line := { l | p ∈ l.val }
def trace (ℓ : affineAG22.Line) : Finset affineAG22.Point := ℓ.val

lemma pencil_spec' {p : affineAG22.Point} {l : affineAG22.Line} :
  l ∈ pencil p ↔ ∃ q, q ≠ p ∧ l.val = {p, q} := by
  obtain ⟨a, b, hne, hab⟩ := Finset.card_eq_two.mp l.property
  simp [pencil]
  constructor
  · intro hp
    simp [hab] at hp
    rcases hp with rfl | rfl
    · use b; exact ⟨hne.symm, hab⟩
    · use a; exact ⟨hne, by simpa [Finset.pair_comm] using hab⟩
  · rintro ⟨q, hne, h_eq⟩
    simp [h_eq]

end affineAG22

open affineAG22
instance : DecidableEq affineAG22.Point := inferInstanceAs (DecidableEq (Fin 4))
instance : DecidableEq affineAG22.Line :=
  inferInstanceAs (DecidableEq { s : Finset (Fin 4) // #s = 2 })


lemma pair_unique_line {a b} (h : a ≠ b) :
    ∃! l, affineAG22.incidence a l ∧ affineAG22.incidence b l := by
  simp [affineAG22]
  set pair : Finset (Fin 4) := {a, b} with h_pair
  let l : affineAG22.Line := ⟨pair, card_pair h⟩
  use l
  constructor
  · simp [l, pair]
  rintro l' ⟨h_a, h_b⟩

  show l'= l
  apply Subtype.ext
  obtain ⟨x, y, _, l'.val⟩ := card_eq_two.mp l'.prop
  simp [l'.val] at *

  suffices h' : {x, y} = pair by rw [h']
  simp [pair]
  rcases h_a, h_b with ⟨rfl | rfl, rfl | rfl⟩
  <;> simpa [pair_comm] using h

lemma exists_unique_disjoint_line (p : affineAG22.Point) (b :affineAG22.Line) (h : p ∉ b.val) :
    ∃! ℓ, ℓ ∈ pencil p  ∧ Disjoint (trace ℓ) (trace b) := by
  obtain ⟨q₁, q₂, h_neq, hb⟩ := Finset.card_eq_two.mp b.property
  have p_ne_q₁ : p ≠ q₁ := by
    intro eq; subst eq; exact h (by simp [hb])
  have p_ne_q₂ : p ≠ q₂ := by
    intro eq; subst eq; exact h (by simp [hb])

  let known_points : Finset affineAG22.Point := {p, q₁, q₂}
  let remaining := (univ : Finset affineAG22.Point) \ known_points
  have h_remaining_card : #remaining = 1 := by
    have h_known_card : #known_points = 3 := by
      show #({p, q₁, q₂} : Finset affineAG22.Point) = 3
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [h_neq]
      · simp [p_ne_q₁, p_ne_q₂]
    have h_univ_card : #(Finset.univ : Finset affineAG22.Point) = 4 := by rfl
    simp [remaining, Finset.card_sdiff, h_univ_card, h_known_card]

  obtain ⟨q₃, hq₃⟩ := Finset.card_eq_one.mp h_remaining_card

  have q₃_comp : known_points = {q₃}ᶜ := eq_compl_comm.mp hq₃.symm
  have : ∀ q, q ∈ known_points → q₃ ≠ q := fun _ a
    ↦ Ne.symm (ne_of_mem_of_not_mem a (by simp[q₃_comp]))

  have hq₃_diff : q₃ ≠ p ∧ q₃ ≠ q₁ ∧ q₃ ≠ q₂ := by simp [this, known_points]
  let ℓ : affineAG22.Line := ⟨{p, q₃}, card_pair hq₃_diff.1.symm⟩

  have hℓ_pencil : ℓ ∈ pencil p := pencil_spec'.mpr ⟨q₃, hq₃_diff.1, rfl⟩
  have tr_ℓ: trace ℓ = {p, q₃} := by simp [ℓ, trace]
  have tr_b: trace b = {q₁, q₂} := by simp [hb, trace]
  have disjoint: Disjoint (trace ℓ) (trace b) := by
    simp [tr_ℓ, tr_b, Finset.disjoint_left, p_ne_q₁, p_ne_q₂, hq₃_diff]

  use ℓ
  constructor
  · exact ⟨hℓ_pencil, disjoint⟩
  simp [trace, h]
  intro ℓ' hℓ' h_disjoint
  have ⟨q, hq, h_eq⟩ : ∃ q, q ≠ p ∧ ℓ'.val = {p, q} := pencil_spec'.mp hℓ'

  suffices h_eq' : q = q₃ by
    apply Subtype.ext; rw [h_eq, h_eq']

  simp [hb, h_eq] at h_disjoint
  have hq₁' : q ≠ q₁ := Ne.symm h_disjoint.1.2
  have hq₂' : q ≠ q₂ := Ne.symm h_disjoint.2.2
  have : q ∈ known_pointsᶜ := by
    simp [known_points, hq, hq₁', hq₂']
  simpa [q₃_comp] using this


lemma every_line_has_two_points (l : affineAG22.Line) : #(affineAG22.trace l) = 2 := by
  simp [trace, l.property]

lemma every_point_in_three_lines (p : affineAG22.Point) : #(pencil p) = 3 := by
  let others : Finset affineAG22.Point := {p}ᶜ

  have h₁ : others.card = 3 := by
    simp [others, card_compl, affineAG22]

  let lines : Finset affineAG22.Line := others.attach.image (λ ⟨q, hq⟩ => ⟨{p, q}, by
      rw [Finset.card_insert_of_notMem]
      · simp [Finset.card_singleton q]
      · simp [Finset.mem_singleton]; simp [others] at hq
        exact Ne.symm hq⟩)

  have h_card : lines.card = 3 := by
    rw [card_image_of_injOn]
    · simp [h₁]
    · intros q₁ _ q₂ _ h
      simp at h
      rw [Subtype.mk.injEq] at h
      apply Subtype.eq
      have hq₁ : ↑q₁ ≠ p := mem_compl_singleton.mp q₁.property
      rw [Finset.ext_iff] at h
      specialize h q₁.val
      simpa [Finset.mem_insert, Finset.mem_singleton, hq₁] using h

  suffices h_lines : lines = pencil p by simp [h_lines.symm, h_card]
  refine Subset.antisymm_iff.mpr ⟨?hsub, ?hsup⟩
  · show lines ⊆ pencil p
    intro l hl
    simp [pencil]
    simp [lines, mem_image] at hl
    rcases hl with ⟨q, _, rfl⟩
    simp
  · show pencil p ⊆ lines
    intro ℓ hℓ
    have ⟨q, hq', h_eq⟩ := pencil_spec'.mp hℓ
    have hq : q ∈ others := by simp [others, hq']
    apply mem_image.mpr
    use ⟨q, hq⟩
    simp; congr; exact h_eq.symm


end affineAG22Props

end Examples
