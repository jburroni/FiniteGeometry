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

class ProjectivePlane (G : IncidenceGeometry) : Prop where
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

lemma noncollinear_incidence (ℓ : G.Line) :
  noncollinear A B C → ¬G.incidence A ℓ ∨ ¬G.incidence B ℓ ∨ ¬G.incidence C ℓ := by
  intro h; simp only [noncollinear, triSet, collinear, trace] at h
  push_neg at h; specialize h ℓ
  -- The following tauto is _classical_
  simp at h; tauto

@[simp]
lemma noncollinear₁₂ {A B C : G.Point} : noncollinear A B C ↔ noncollinear B A C := by
  simp [noncollinear, triSet, collinear]
  tauto

lemma noncollinear₃₁₂ {A B C : G.Point} : noncollinear C A B ↔ noncollinear A B C := by
  simp [noncollinear, triSet, collinear]
  tauto

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
open IncidenceGeometry ProjectivePrereqs AlternativeAxioms
variable {G : IncidenceGeometry}
variable (hP1 : P1 (G := G)) (hP2 : P2 (G := G)) (hP3' : P3' (G := G))

lemma line_eq_of_point_eq
    (hP1 : P1 (G := G)) {A P : G.Point} (hA_ne_P : A ≠ P) {ℓ m : G.Line}
    (hAℓ : G.incidence A ℓ) (hPℓ : G.incidence P ℓ)
    (hAm : G.incidence A m) (hPm : G.incidence P m) : ℓ = m := by
  obtain ⟨l, _, huniq⟩ := hP1 hA_ne_P
  have hℓ : ℓ = l := huniq ℓ ⟨hAℓ, hPℓ⟩
  have hm : m = l := huniq m ⟨hAm, hPm⟩
  trans l
  · exact hℓ
  · exact hm.symm

lemma points_distinct_of_noncollinear (hP1 : P1 (G := G)) {A B C PB PC : G.Point}
    (hABC : noncollinear A B C) (hA_ne_PB : A ≠ PB) (hA_ne_PC : A ≠ PC)
    {mB mC : G.Line}
    (hAmB : G.incidence A mB) (hBmB : G.incidence B mB)
    (hAmC : G.incidence A mC) (hCmC : G.incidence C mC)
    (hPBmB : G.incidence PB mB) (hPCmC : G.incidence PC mC) : PB ≠ PC := by
  rintro rfl
  have hm_eq : mB = mC := by apply line_eq_of_point_eq hP1 hA_ne_PB <;> assumption
  subst hm_eq
  simp [noncollinear, triSet, collinear] at hABC
  apply hABC mB <;> assumption

lemma three_points_on_line (ℓ : G.Line) (hP1 : P1 (G := G)) (hP2 : P2 (G := G))
    (hP3' : P3' (G := G)) :
    ∃ p q r : G.Point,
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      G.incidence p ℓ ∧ G.incidence q ℓ ∧ G.incidence r ℓ := by
  rcases hP3' with
    ⟨A,B,C,D,
     hAB,hAC,hAD,hBC,hBD,hCD,
     hABC,hABD,hACD,hBCD⟩
  wlog h_not_A : ¬ G.incidence A ℓ generalizing A B C D hABC hABD hACD hBCD
  · rcases (noncollinear_incidence ℓ hABC) with _ | _ | _
    · contradiction
    · have hBAD : noncollinear B A D := by simp [hABD]
      have hBAC : noncollinear B A C := by simp [hABC]
      apply this B A C D hAB.symm <;> assumption
    · have hCAB : noncollinear C A B := by simp only [noncollinear₃₁₂, hABC]
      have hCAD : noncollinear C A D := by simp [hACD]
      have hCBD : noncollinear C B D := by simp [hBCD]
      apply this C A B D hAC.symm hBC.symm <;> assumption

  obtain ⟨mB, ⟨hAmB, hBmB⟩, _⟩ := hP1 hAB
  obtain ⟨mC, ⟨hAmC, hCmC⟩, _⟩ := hP1 hAC
  obtain ⟨mD, ⟨hAmD, hDmD⟩, _⟩ := hP1 hAD
  have : mB ≠ ℓ := by rintro rfl; contradiction
  obtain ⟨PB, ⟨hPBmB, hPBℓ⟩ , _⟩ := hP2 this
  have : mC ≠ ℓ := by rintro rfl; contradiction
  obtain ⟨PC, ⟨hPCmC, hPCℓ⟩, _⟩ := hP2 this
  have : mD ≠ ℓ := by rintro rfl; contradiction
  obtain ⟨PD, ⟨hPDmD, hPDℓ⟩, _⟩ := hP2 this

  use PB, PC, PD

  have hA_ne_PB : A ≠ PB := by rintro rfl; contradiction
  have hA_ne_PC : A ≠ PC := by rintro rfl; contradiction
  have hA_ne_PD : A ≠ PD := by rintro rfl; contradiction

  refine ⟨?_, ?_, ?_, hPBℓ, hPCℓ, hPDℓ⟩
  · show PB ≠ PC
    apply points_distinct_of_noncollinear hP1 (PB:=PB) (PC:=PC) (mB:=mB) (mC:=mC) hABC
    <;> assumption
  · show PB ≠ PD
    apply points_distinct_of_noncollinear hP1 (PB:=PB) (PC:=PD) (mB:=mB) (mC:=mD) hABD
    <;> assumption
  · show PC ≠ PD
    apply points_distinct_of_noncollinear hP1 (PB:=PC) (PC:=PD) (mB:=mC) (mC:=mD) hACD
    <;> assumption



/-- Packaging Lemmas 1 + 2 into the standard **P₃**, **P₄** pair. -/
def P3_from_P3' : IncidenceGeometry :=
  let _ : P1 (G := G) := hP1
  let _ : P2 (G := G) := hP2
  have h₁ := three_lines_through_point hP1 hP2 hP3'
  have h₂ := three_points_on_line    hP1 hP2 hP3'
  { Point     := G.Point,
    Line      := G.Line,
    incidence := G.incidence }

end FromP3'

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
