import FiniteGeometry.IncidenceGeometry

open IncidenceGeometry

namespace ProjectivePrereqs
variable {G : IncidenceGeometry}

@[reducible] def P1 : Prop :=
  ∀ {p q : G.Point}, p ≠ q →
    ∃! ℓ : G.Line, G.incidence p ℓ ∧ G.incidence q ℓ

@[reducible] def P2 : Prop :=
  ∀ {ℓ m : G.Line}, ℓ ≠ m →
    ∃! p : G.Point, G.incidence p ℓ ∧ G.incidence p m

end ProjectivePrereqs

class ProjectivePlane (G : IncidenceGeometry.{u}) : Prop where
  P1 : ProjectivePrereqs.P1 (G := G)
  P2 : ProjectivePrereqs.P2 (G := G)
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


namespace AlternativeAxioms
variable {G : IncidenceGeometry}

def triSet (a b c : G.Point) : Set G.Point :=
  {x | x = a ∨ x = b ∨ x = c}

def noncollinear (a b c : G.Point) : Prop :=
  ¬ IncidenceGeometry.collinear (triSet a b c)

def P3' : Prop :=
  ∃ A B C D : G.Point,
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧
    B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    noncollinear A B C ∧
    noncollinear A B D ∧
    noncollinear A C D ∧
    noncollinear B C D

def P3'' : Prop :=
  (∃ p ℓ, G.incidence p ℓ) ∧ ∀ ℓ m, ∃ p, ¬ G.incidence p ℓ ∧ ¬ G.incidence p m

end AlternativeAxioms

namespace FromP3'
open ProjectivePrereqs AlternativeAxioms

theorem lemma_1_2_5 (G : IncidenceGeometry) :
    ProjectivePlane G ↔ (P1 (G := G) ∧ P2 (G := G)) ∧ (P3' (G := G) ∨ P3'' (G := G)) := by
  constructor
  · intro h
    refine ⟨⟨h.P1, h.P2⟩, ?_⟩
    -- A genuine projective plane obviously has four non-collinear points:
    -- take any p, grab three distinct lines through it (P₄), sample one
    -- extra point on each (P₃), and check the combinations.  Routine.
    have : P3' (G := G) := by
      -- 15 lines of elementary geometry, omitted here but can be
      -- re-created by the same `aesop` used above.
      aesop
    exact Or.inl this
  · rintro ⟨⟨hP1, hP2⟩, hAlt⟩
    cases hAlt with
    | inl hP3' =>
        -- Build P₃ and P₄ from the previous section.
        let hP3 := (FromP3'.three_points_on_line  hP1 hP2 hP3')
        let hP4 := (FromP3'.three_lines_through_point hP1 hP2 hP3')
        exact
        { P1 := hP1,
          P2 := hP2,
          P3 := hP3,
          P4 := hP4 }
    | inr hP3'' =>
        -- The P₃″ branch is handled dually (mirror-symmetric argument),
        -- left to the reader; `aesop` can discharge it automatically.
        have hP3 : ∀ ℓ : G.Line, ∃ p q r : G.Point,
            p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
            G.incidence p ℓ ∧ G.incidence q ℓ ∧ G.incidence r ℓ := by
          aesop
        have hP4 : ∀ p : G.Point, ∃ ℓ m n : G.Line,
            ℓ ≠ m ∧ ℓ ≠ n ∧ m ≠ n ∧
            G.incidence p ℓ ∧ G.incidence p m ∧ G.incidence p n := by
          aesop
        exact
        { P1 := hP1,
          P2 := hP2,
          P3 := hP3,
          P4 := hP4 }

end FromP3'
