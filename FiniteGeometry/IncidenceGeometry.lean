import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card


universe u

structure IncidenceGeometry where
  Point : Type u
  Line : Type u
  incidence : Point → Line → Prop

namespace IncidenceGeometry

def trace (G : IncidenceGeometry) (ℓ : G.Line) : Set G.Point :=
  { p | G.incidence p ℓ }

def pencil (G : IncidenceGeometry) (p : G.Point) : Set G.Line :=
  { ℓ | G.incidence p ℓ }

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

section Examples
open Finset
/-- Example: Steiner system S(3,3,5) with 5 points and all 3-element subsets as lines. -/
def steinerS335 : IncidenceGeometry where
  Point := Fin 5
  Line := { s : Finset (Fin 5) // s.card = 3 }
  incidence := fun p b ↦ p ∈ b.val

/-- Example: Affine plane AG(2,2) with 4 points and all 2-element subsets as lines. -/
def affineAG22 : IncidenceGeometry where
  Point := Fin 4
  Line := { s : Finset (Fin 4) // s.card = 2 }
  incidence := fun p b ↦ p ∈ b.val
end Examples

end Category

end IncidenceGeometry
