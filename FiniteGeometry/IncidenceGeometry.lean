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

/-- Example: Steiner system S(3,3,5) with 5 points and all 3-element subsets as lines. -/
def steinerS335 : IncidenceGeometry where
  Point := Fin 5
  Line := { s : Finset (Fin 5) // #s = 3 }
  incidence := fun p b ↦ p ∈ b.val

/-- Example: Affine plane AG(2,2) with 4 points and all 2-element subsets as lines. -/
def affineAG22 : IncidenceGeometry where
  Point := Fin 4
  Line := { s : Finset (Fin 4) // s.card = 2 }
  incidence := fun p b ↦ p ∈ b.val


namespace affineAG22Props

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
