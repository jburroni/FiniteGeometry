import Mathlib
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic


structure IncidenceGeometry where
  Point : Type*
  Line : Type*
  incidence : Point → Line → Prop
  [point_fintype : Fintype Point]
  [line_fintype : Fintype Line]
  [decidable_incidence : ∀ (p : Point) (ℓ : Line), Decidable (incidence p ℓ)]
namespace IncidenceGeometry

variable {G : IncidenceGeometry}
instance : Fintype G.Point := G.point_fintype
instance : Fintype G.Line := G.line_fintype
instance : ∀ (p : G.Point) (ℓ : G.Line), Decidable (G.incidence p ℓ) := G.decidable_incidence


@[simp]
def trace (ℓ : G.Line) : Finset G.Point :=  Finset.univ.filter (fun p => G.incidence p ℓ)

@[simp]
def pencil (p : G.Point) : Finset G.Line :=  Finset.univ.filter (fun ℓ => G.incidence p ℓ)

@[simp]
lemma trace_spec (ℓ : G.Line) (p : G.Point) :
  p ∈ G.trace ℓ ↔ G.incidence p ℓ := by simp

@[simp]
lemma pencil_spec (p : G.Point) (ℓ : G.Line) :
  ℓ ∈ G.pencil p ↔ G.incidence p ℓ := by simp

section Category
open CategoryTheory

@[ext]
structure IncidenceHom (G H : IncidenceGeometry.{u}) where
  pointMap : G.Point → H.Point
  lineMap : G.Line → H.Line
  preserves_incidence : ∀ {p : G.Point} {l : G.Line},
    G.incidence p l → H.incidence (pointMap p) (lineMap l)

namespace IncidenceHom

def id (G : IncidenceGeometry) : IncidenceHom G G where
  pointMap := fun p ↦ p
  lineMap := fun ℓ ↦ ℓ
  preserves_incidence := fun h ↦ h

def comp {G H K : IncidenceGeometry}
  (f : IncidenceHom G H) (g : IncidenceHom H K) : IncidenceHom G K where
    pointMap := g.pointMap ∘ f.pointMap
    lineMap := g.lineMap ∘ f.lineMap
    preserves_incidence := fun h ↦
      g.preserves_incidence (f.preserves_incidence h)

end IncidenceHom

instance : Category IncidenceGeometry.{u} where
  Hom := IncidenceHom
  id := IncidenceHom.id
  comp := IncidenceHom.comp

structure Iso (G H : IncidenceGeometry) extends IncidenceHom G H where
  inv : IncidenceHom H G
  left_inv : ∀ p : G.Point, inv.pointMap (pointMap p) = p
  right_inv : ∀ q : H.Point, pointMap (inv.pointMap q) = q
  left_inv_line : ∀ l : G.Line, inv.lineMap (lineMap l) = l
  right_inv_line : ∀ m : H.Line, lineMap (inv.lineMap m) = m

def dual (G : IncidenceGeometry) : IncidenceGeometry where
  Point := G.Line
  Line := G.Point
  incidence := fun l p ↦ G.incidence p l
  point_fintype := G.line_fintype
  line_fintype := G.point_fintype
  decidable_incidence := fun l p ↦ G.decidable_incidence p l

section Examples
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

def pencil (p : affineAG22.Point) : Finset affineAG22.Line := { l | p ∈ l.val }
def trace (ℓ : affineAG22.Line) : Finset affineAG22.Point := ℓ.val


instance : DecidableEq affineAG22.Point := inferInstanceAs (DecidableEq (Fin 4))
instance : DecidableEq affineAG22.Line :=
  inferInstanceAs (DecidableEq { s : Finset (Fin 4) // s.card = 2 })


lemma pair_unique_line {a b} (h : a ≠ b) :
    ∃! l, affineAG22.incidence a l ∧ affineAG22.incidence b l := by
  simp [affineAG22]
  set pair : Finset (Fin 4) := {a, b} with h_pair
  let l : affineAG22.Line := ⟨pair, card_pair h⟩
  use l
  constructor
  · simp [l, pair]

  rintro l' ⟨h_a, h_b⟩
  apply Subtype.ext
  obtain ⟨x, y, hxy, hx⟩ := Finset.card_eq_two.mp l'.prop
  rw [hx] at h_a h_b
  have h' : pair = {x, y} := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · have h_card : ({x, y} : Finset (Fin 4)).card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        simp [hxy]
      simp [h_card]
      have h_pair_card : pair.card = 2 := by
        rw [Finset.card_insert_of_notMem, Finset.card_singleton]
        simp [h]
      simp [h_pair_card]
  rw [hx, ←h']

lemma exists_unique_disjoint_line (p : affineAG22.Point) (b :affineAG22.Line) (h : p ∉ b.val) :
    ∃! ℓ, ℓ ∈ pencil p  ∧ Disjoint (trace ℓ) (trace b) := by
  obtain ⟨q₁, q₂, hq, hb⟩ := Finset.card_eq_two.mp b.property
  have p_ne_q₁ : p ≠ q₁ := by
    intro eq; subst eq; exact h (by simp [hb])
  have p_ne_q₂ : p ≠ q₂ := by
    intro eq; subst eq; exact h (by simp [hb])

  let known_points : Finset affineAG22.Point := {p, q₁, q₂}
  let remaining := (Finset.univ : Finset affineAG22.Point) \ known_points
  have h_remaining_card : #remaining = 1 := by
    have h_known_card : #known_points = 3 := by
      show #({p, q₁, q₂} : Finset affineAG22.Point) = 3
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hq]
      · simp [p_ne_q₁, p_ne_q₂]
    have h_univ_card : #(Finset.univ : Finset affineAG22.Point) = 4 := by rfl
    simp [remaining, Finset.card_sdiff, h_univ_card, h_known_card]

  obtain ⟨q₃, hq₃⟩ := Finset.card_eq_one.mp h_remaining_card

  have hq₃_not_in_known : q₃ ∉ known_points := by
    have h_q₃_in_remaining : q₃ ∈ remaining := by
      rw [hq₃]
      simp
    exact Finset.mem_sdiff.mp h_q₃_in_remaining |>.2

  have : ∀ q, q ∈ known_points → q₃ ≠ q := by
    intro q hq h_eq
    rw [h_eq] at hq₃_not_in_known
    contradiction

  have hq₃p : q₃ ≠ p := by simp [this, known_points]
  have hq₃q₁ : q₃ ≠ q₁ := by simp [this, known_points]
  have hq₃q₂ : q₃ ≠ q₂ := by simp [this, known_points]

  let ℓ : affineAG22.Line := ⟨{p, q₃}, card_pair hq₃p.symm⟩

  have hℓ_pencil : ℓ ∈ pencil p := by simp [pencil, ℓ, affineAG22]

  have tr_ℓ: trace ℓ = {p, q₃} := by simp [ℓ, trace]
  have tr_b: trace b = {q₁, q₂} := by simp [hb, trace]
  have disjoint: Disjoint (trace ℓ) (trace b) := by
    simp [tr_ℓ, tr_b, Finset.disjoint_left, p_ne_q₁, p_ne_q₂, hq₃q₁, hq₃q₂]

  use ℓ
  constructor
  · exact ⟨hℓ_pencil, disjoint⟩
  simp [trace, pencil, h]

  intro ℓ' hℓ'

  have : ∃ q, ℓ'.val = {p, q} := by

    obtain ⟨a, b, hne, hab⟩ := Finset.card_eq_two.mp ℓ'.property
    rw [hab] at hℓ'
    rw [Finset.mem_insert, Finset.mem_singleton] at hℓ'
    rcases hℓ' with rfl | rfl
    · use b
    · rw [Finset.pair_comm] at hab; use a
  intro h_disjoint
  simp [hb] at h_disjoint
  rcases this with ⟨q, h_eq⟩
  have hq : q ≠ p := by
    intro h_eq_qp
    subst h_eq_qp
    simp [pair_eq_singleton] at h_eq
    have := ℓ'.property
    rw [h_eq, card_singleton] at this
    simp at this
  have hq₁' : q ≠ q₁ := by
    intro h_eq_q₁q
    subst h_eq_q₁q
    have := h_disjoint.1
    rw [h_eq] at this
    simp at this
  have hq₂' : q ≠ q₂ := by
    intro h_eq_q₂q
    subst h_eq_q₂q
    have := h_disjoint.2
    rw [h_eq] at this
    simp at this
  have hq' : q₃ = q := by
    have hq_not_in_known : q ∉ known_points := by
      simp [known_points, mem_insert, mem_singleton, hq, hq₁', hq₂']

    have hq_in_remaining : q ∈ remaining := by
      rw [mem_sdiff]; simp [mem_univ, hq_not_in_known]
    rw [hq₃] at hq_in_remaining
    exact (mem_singleton.mp hq_in_remaining).symm
  subst hq'
  apply Subtype.ext
  rw [h_eq]


lemma every_line_has_two_points (l : affineAG22.Line) : #(affineAG22.trace l) = 2 := by
  simp [affineAG22, l.property]

lemma every_point_in_three_lines (p : affineAG22.Point) : #(affineAG22.pencil p) = 3 := by
  simp [affineAG22]
  let others := (univ.erase p)

  have h₁ : others.card = 3 := by
    simp [others, card_erase_of_mem (Finset.mem_univ p), card_univ, affineAG22]

  let lines : Finset affineAG22.Line := others.attach.image (λ ⟨q, hq⟩ =>
    ⟨{p, q}, by
      rw [Finset.card_insert_of_notMem]
      · simp [Finset.card_singleton q]
      · simp [Finset.mem_singleton]
        exact (Finset.mem_erase.mp hq).1.symm⟩)

  have h_sub : lines ⊆ pencil p := by
    intro l hl
    simp [pencil, affineAG22]
    simp [lines, mem_image] at hl
    rcases hl with ⟨q, _, rfl⟩
    simp

  have h_card : lines.card = 3 := by
    rw [card_image_of_injOn]
    · simp [h₁]
    · intros q₁ _ q₂ _ h
      simp at h
      rw [Subtype.mk.injEq] at h
      apply Subtype.eq
      have hq₁ : ↑q₁ ≠ p := by  dsimp [others] at q₁
                                have := q₁.property
                                rw [Finset.mem_erase] at this
                                exact this.1
      rw [Finset.ext_iff] at h
      specialize h q₁.val
      simpa [Finset.mem_insert, Finset.mem_singleton, hq₁] using h

  have h_sup : pencil p ⊆ lines := by
    intro ℓ hℓ
    simp [Finset.mem_filter, Finset.mem_univ] at hℓ
    have h₂ : ∃ q ∈ others, ℓ.val = {p, q} := by
      dsimp [others]
      simp
      obtain ⟨a, b, hne, h_ab⟩ := card_eq_two.mp ℓ.property
      simp [affineAG22, h_ab] at hℓ
      rcases hℓ with rfl | rfl
      · use b; exact ⟨Ne.symm hne, h_ab⟩
      · use a; exact ⟨hne, by simpa [Finset.pair_comm] using h_ab⟩
    rcases h₂ with ⟨q, hq, val_eq⟩
    apply mem_image.mpr
    use ⟨q, hq⟩
    simp
    congr; exact val_eq.symm

  have h_eq : pencil p = lines := Subset.antisymm_iff.mpr ⟨h_sup, h_sub⟩
  change #(pencil p) = 3
  rw [h_eq, h_card]

end affineAG22Props

end Examples

end Category

end IncidenceGeometry
