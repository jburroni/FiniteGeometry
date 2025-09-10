import Mathlib
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import FiniteGeometry.Finset
import FiniteGeometry.Set


structure IncidenceGeometry where
  Point : Type*
  Line : Type*
  incidence : Point → Line → Prop

namespace IncidenceGeometry

variable {G : IncidenceGeometry}

@[inline] def inc {G : IncidenceGeometry} : G.Point → G.Line → Prop :=
  G.incidence

scoped infix:50 " ∈ᵢ " => IncidenceGeometry.inc


@[simp]
def trace (ℓ : G.Line) : Set G.Point := { p | G.incidence p ℓ }

@[simp]
def pencil (p : G.Point) : Set G.Line :=  { ℓ : G.Line | G.incidence p ℓ }


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



end Category

section ExtraDefinitions

variable {G : IncidenceGeometry}

def collinear (S : Set G.Point) : Prop :=
  ∃ ℓ : G.Line, S ⊆ (trace ℓ : Set G.Point)

def triangle (T : Finset G.Point) : Prop :=
  T.card = 3 ∧ ¬ collinear (T : Set G.Point)

def generalPosition (S : Set G.Point) : Prop :=
  ∀ A B C : G.Point, {A, B, C} ⊆ S ∧ (A ≠ B ∧ A ≠ C ∧ B ≠ C) → ¬ collinear {A, B, C}
  -- ∀ T : Finset G.Point, (T : Set G.Point) ⊆ S → T.card = 3 → ¬ collinear (T : Set G.Point)

def concurrent (L : Set G.Line) : Prop :=
  ∃ p : G.Point, L ⊆ (pencil p : Set G.Line)

def quad (A B C D : G.Point) : Prop :=
  (A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D) ∧
  generalPosition {A, B, C, D}

structure Subgeometry (G : IncidenceGeometry) where
  PointSub : Set G.Point
  LineSub  : Set G.Line

namespace Subgeometry
variable {G: IncidenceGeometry}

def incidence (H : Subgeometry G)
    (p : { q : G.Point // q ∈ H.PointSub })
    (ℓ : { m : G.Line  // m ∈ H.LineSub }) : Prop :=
  p.val ∈ᵢ ℓ.val

def toIncidenceGeometry {G : IncidenceGeometry} (H : Subgeometry G) : IncidenceGeometry :=
{ Point          := { p : G.Point // p ∈ H.PointSub }
  Line           := { ℓ : G.Line  // ℓ ∈ H.LineSub }
  incidence      := H.incidence
}

end Subgeometry

end ExtraDefinitions

section BasicLemmas
open Finset
variable {G : IncidenceGeometry} {ℓ m : G.Line} {A B C : G.Point}


section DecidablePoint

lemma generalPosition_spec
    (S : Set G.Point) (A B C : G.Point) (hA : A ∈ S) (hB : B ∈ S)
    (hC : C ∈ S) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    generalPosition S → ¬ collinear ({A, B, C} : Set G.Point) := by
  intro hGP
  specialize hGP A B C
  apply hGP
  constructor
  · show {A, B, C} ⊆ S
    apply Set.insert_subset hA; apply Set.insert_subset hB; apply Set.singleton_subset_iff.mpr hC
  · show (A ≠ B ∧ A ≠ C ∧ B ≠ C)
    exact ⟨hAB, hAC, hBC⟩



lemma quad_rule {A B C D : G.Point} :
    quad A B C D ↔
    (A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D) ∧
    ¬collinear {A, B, C} ∧ ¬collinear {A, B, D} ∧ ¬collinear {A, C, D} ∧ ¬collinear {B, C, D} := by
  constructor
  · rintro ⟨h, H⟩
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
    refine ⟨h, ⟨?_, ?_, ?_, ?_⟩⟩
    all_goals
      apply generalPosition_spec (S := {A, B, C, D})
      <;> try simp
    all_goals
      assumption
  · rintro ⟨h, ⟨h₁, h₂, h₃, h₄⟩⟩
    constructor
    · show A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D
      exact h
    · show generalPosition {A, B, C, D}
      simp only [generalPosition]
      intro A' B' C'
      rintro ⟨hl, hr⟩
      set T := ({A', B', C'} : Set G.Point) with hT
      rcases (Set.subset_four_choose_three (h:=hT) hr hl) with (h|h|h|h)
      all_goals
      · rw [h] at *; assumption


end DecidablePoint

lemma line_ne_of_mem_not_mem (hAℓ : A ∈ᵢ ℓ) (hAnotm : ¬ A ∈ᵢ m) : ℓ ≠ m := by
  rintro rfl; contradiction

lemma point_ne_of_mem_not_mem (hAnot : ¬ A ∈ᵢ ℓ) (hB : B ∈ᵢ ℓ) : A ≠ B := by
  rintro rfl; contradiction
end BasicLemmas

end IncidenceGeometry
