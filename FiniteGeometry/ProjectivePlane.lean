import FiniteGeometry.IncidenceGeometry

open IncidenceGeometry


class ProjectivePlane (G : IncidenceGeometry.{u}) : Prop where
  P1 : ∀ {p q : G.Point}, p ≠ q →
      ∃! ℓ : G.Line, G.incidence p ℓ ∧ G.incidence q ℓ
  P2 :
    ∀ {ℓ m : G.Line}, ℓ ≠ m →
      ∃! p : G.Point, G.incidence p ℓ ∧ G.incidence p m
  P3 :
    ∀ ℓ : G.Line,
      ∃ p q r : G.Point,
        p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
        G.incidence p ℓ ∧ G.incidence q ℓ ∧ G.incidence r ℓ
  P4 :
    ∀ p : G.Point,
      ∃ ℓ m n : G.Line,
        ℓ ≠ m ∧ ℓ ≠ n ∧ m ≠ n ∧
        G.incidence p ℓ ∧ G.incidence p m ∧ G.incidence p n

namespace ProjectivePlane

variable {G : IncidenceGeometry} [ProjectivePlane G]

noncomputable
def lineThrough {p q : G.Point} (h : p ≠ q) : G.Line :=
  (P1 h).choose

lemma lineThrough_incidence_left {p q : G.Point} (h : p ≠ q) : G.incidence p (lineThrough h) :=
  (P1 h).choose_spec.1.1

lemma lineThrough_incidence_right {p q : G.Point} (h : p ≠ q) : G.incidence q (lineThrough h) :=
  (P1 h).choose_spec.1.2

noncomputable
def meet {ℓ m : G.Line} (h : ℓ ≠ m) : G.Point :=
  (P2 h).choose

lemma meet_incidence_left {ℓ m : G.Line} (h : ℓ ≠ m) : G.incidence (meet h) ℓ :=
  (P2 h).choose_spec.1.1

lemma meet_incidence_right {ℓ m : G.Line} (h : ℓ ≠ m) : G.incidence (meet h) m :=
  (P2 h).choose_spec.1.2

end ProjectivePlane

instance dual_projective (G : IncidenceGeometry) [ProjectivePlane G] : ProjectivePlane G.dual where
  P1 := ProjectivePlane.P2
  P2 := ProjectivePlane.P1
  P3 := ProjectivePlane.P4
  P4 := ProjectivePlane.P3
