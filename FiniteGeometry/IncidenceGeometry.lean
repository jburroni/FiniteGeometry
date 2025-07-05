import Mathlib
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Finset
open Finset
variable {α : Type*}
variable [Fintype α]
variable [DecidableEq α] {a b : α}
theorem mem_compl_singleton {a b : α} : a ∈ ({b}ᶜ : Finset α) ↔ a ≠ b := by
  simp only [mem_compl, mem_singleton, ne_eq]

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

lemma pencil_spec' {p : affineAG22.Point} {l : affineAG22.Line} :
  l ∈ pencil p ↔ ∃ q, q ≠ p ∧ l.val = {p, q} := by
  obtain ⟨a, b, hne, hab⟩ := Finset.card_eq_two.mp l.property
  simp [affineAG22, hab] at l
  simp [pencil]
  constructor
  · intro hp
    simp [hab] at hp
    rcases hp with rfl | rfl
    · use b; exact ⟨hne.symm, hab⟩
    · use a; exact ⟨hne, by simpa [Finset.pair_comm] using hab⟩
  · rintro ⟨q, hne, h_eq⟩
    simp [h_eq]


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
  obtain ⟨q₁, q₂, hq, hb⟩ := Finset.card_eq_two.mp b.property
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
      · simp [hq]
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
  simp [hb, h_eq] at h_disjoint
  have hq₁' : q ≠ q₁ := Ne.symm h_disjoint.1.2
  have hq₂' : q ≠ q₂ := Ne.symm h_disjoint.2.2
  have hq' : q₃ = q := by
    symm
    have : q ∈ known_pointsᶜ := by
      simp [known_points, hq, hq₁', hq₂']
    simpa [q₃_comp] using this
  subst hq'
  apply Subtype.ext
  rw [h_eq]


lemma every_line_has_two_points (l : affineAG22.Line) : #(affineAG22.trace l) = 2 := by
  simp [affineAG22, l.property]

lemma every_point_in_three_lines (p : affineAG22.Point) : #(pencil p) = 3 := by
  simp [affineAG22]
  let others : Finset affineAG22.Point := {p}ᶜ

  have h₁ : others.card = 3 := by
    simp [others, card_compl, affineAG22]

  let lines : Finset affineAG22.Line := others.attach.image (λ ⟨q, hq⟩ =>
    ⟨{p, q}, by
      rw [Finset.card_insert_of_notMem]
      · simp [Finset.card_singleton q]
      · simp [Finset.mem_singleton]; simp [others] at hq
        exact Ne.symm hq⟩)

  have h_sub : lines ⊆ pencil p := by
    intro l hl
    simp [pencil]
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
      have hq₁ : ↑q₁ ≠ p := mem_compl_singleton.mp q₁.property
      rw [Finset.ext_iff] at h
      specialize h q₁.val
      simpa [Finset.mem_insert, Finset.mem_singleton, hq₁] using h

  have h_sup : pencil p ⊆ lines := by
    intro ℓ hℓ
    have ⟨q, hq', h_eq⟩ := pencil_spec'.mp hℓ
    have hq : q ∈ others := by simp [others, hq']
    apply mem_image.mpr
    use ⟨q, hq⟩
    simp; congr; exact h_eq.symm

  have h_eq : pencil p = lines := Subset.antisymm_iff.mpr ⟨h_sup, h_sub⟩
  change #(pencil p) = 3
  rw [h_eq, h_card]

end affineAG22Props

end Examples

end Category

end IncidenceGeometry
