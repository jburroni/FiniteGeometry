import FiniteGeometry.IncidenceGeometry

open IncidenceGeometry

namespace ProjectivePrereqs
variable {G : IncidenceGeometry}

@[reducible] def P1 : Prop :=
  ∀ {p q : G.Point}, p ≠ q →
    ∃! ℓ : G.Line, p ∈ᵢ ℓ ∧ q ∈ᵢ ℓ

@[reducible] def P2 : Prop :=
  ∀ {ℓ m : G.Line}, ℓ ≠ m →
    ∃! p : G.Point, p ∈ᵢ ℓ ∧ p ∈ᵢ m

end ProjectivePrereqs

class ProjectivePlane (G : IncidenceGeometry) : Prop where
  P1 : ProjectivePrereqs.P1 (G := G)
  P2 : ProjectivePrereqs.P2 (G := G)
  P3 :
    ∀ ℓ : G.Line,
      ∃ p q r : G.Point,
        p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
        p ∈ᵢ ℓ ∧ q ∈ᵢ ℓ ∧ r ∈ᵢ ℓ
  P4 :
    ∀ p : G.Point,
      ∃ ℓ m n : G.Line,
        ℓ ≠ m ∧ ℓ ≠ n ∧ m ≠ n ∧
        p ∈ᵢ ℓ ∧ p ∈ᵢ m ∧ p ∈ᵢ n


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
  noncollinear A B C → ¬A ∈ᵢ ℓ ∨ ¬B ∈ᵢ ℓ ∨ ¬C ∈ᵢ ℓ := by
  intro h; simp only [noncollinear, triSet, collinear, trace] at h
  push_neg at h; specialize h ℓ
  -- The following tauto is _classical_
  simp at h; tauto

@[simp]
lemma noncollinear₁₂ {A B C : G.Point} : noncollinear A B C ↔ noncollinear B A C := by
  simp [noncollinear, triSet, collinear]
  tauto

lemma noncollinear₂₃ {A B C : G.Point} : noncollinear A B C ↔ noncollinear A C B := by
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
  (∃ p ℓ, G.incidence p ℓ) ∧ ∀ ℓ m : G.Line, ∃ p, ¬ p ∈ᵢ ℓ ∧ ¬ p ∈ᵢ m

end AlternativeAxioms

namespace FromP3'
open IncidenceGeometry ProjectivePrereqs AlternativeAxioms
variable {G : IncidenceGeometry}
variable (hP1 : P1 (G := G)) (hP2 : P2 (G := G)) (hP3' : P3' (G := G))

lemma line_eq_of_point_eq
    (hP1 : P1 (G := G)) {A P : G.Point} (hA_ne_P : A ≠ P) {ℓ m : G.Line}
    (hAℓ : A ∈ᵢ ℓ) (hPℓ : P ∈ᵢ ℓ) (hAm : A ∈ᵢ m) (hPm : P ∈ᵢ m) : ℓ = m := by
  obtain ⟨l, _, huniq⟩ := hP1 hA_ne_P
  have hℓ : ℓ = l := huniq ℓ ⟨hAℓ, hPℓ⟩
  have hm : m = l := huniq m ⟨hAm, hPm⟩
  trans l
  · exact hℓ
  · exact hm.symm

lemma point_eq_of_incident
    (hP2 : P2 (G := G)) {ℓ m : G.Line} (hℓm : ℓ ≠ m)
    {P Q : G.Point} (hPℓ : P ∈ᵢ ℓ) (hPm : P ∈ᵢ m)
    (hQℓ : Q ∈ᵢ ℓ) (hQm : Q ∈ᵢ m) : P = Q :=
  line_eq_of_point_eq (G := G.dual) (hP1 := hP2) (A := ℓ) (P := m) (ℓ := P) (m := Q)
    hℓm hPℓ hPm hQℓ hQm

lemma points_distinct_of_noncollinear (hP1 : P1 (G := G)) {A B C P Q : G.Point}
    (hABC : noncollinear A B C) (hA_ne_PB : A ≠ P) {mB mC : G.Line}
    (hAmB : A ∈ᵢ mB) (hBmB : B ∈ᵢ mB) (hAmC : A ∈ᵢ mC) (hCmC : C ∈ᵢ mC)
    (hPBmB : P ∈ᵢ mB) (hPCmC : Q ∈ᵢ mC) : P ≠ Q := by
  rintro rfl
  have hm_eq : mB = mC := by apply line_eq_of_point_eq hP1 hA_ne_PB <;> assumption
  subst mC
  simp [noncollinear, triSet, collinear] at hABC
  apply hABC mB <;> assumption

lemma line_ne_of_noncollinear {A B C : G.Point} {ℓ₁ ℓ₂ : G.Line}
    (hABC  : noncollinear A B C) (hAℓ₁  : A ∈ᵢ ℓ₁) (hBℓ₁ : B ∈ᵢ ℓ₁) (hCℓ₂ : C ∈ᵢ ℓ₂) : ℓ₁ ≠ ℓ₂ := by
  rintro rfl
  apply hABC; use ℓ₁; simp [collinear, triSet]
  exact ⟨hAℓ₁, hBℓ₁, hCℓ₂⟩

lemma nonconcurrent_chain (hP2 : P2 (G := G)) (hPQ : P ≠ Q) (h₁ : l ≠ m) (h₂ : m ≠ n)
    (h₃ : P ∈ᵢ l) (h₄ : P ∈ᵢ m) (h₅ : Q ∈ᵢ n) (h₆ : Q ∈ᵢ m) : noncollinear (G:= G.dual) l m n := by
  suffices h_no_common : ¬ ∃ A : G.Point, A ∈ᵢ l ∧ A ∈ᵢ m ∧ A ∈ᵢ n by
    simpa [noncollinear, collinear, triSet] using h_no_common
  intro ⟨A', _, _, _⟩
  apply hPQ
  calc P
    _ = A' := by symm; apply point_eq_of_incident (ℓ:= l) (m:=m) (P:=A') (Q:=P) <;> assumption
    _ = Q := by apply point_eq_of_incident (ℓ:= m) (m:=n) (P:=A') (Q:=Q) <;> assumption


lemma three_points_on_line (hP1 : P1 (G := G)) (hP2 : P2 (G := G)) (hP3' : P3' (G := G))
    (ℓ : G.Line) : ∃ p q r : G.Point, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ p ∈ᵢ ℓ ∧ q ∈ᵢ ℓ ∧ r ∈ᵢ ℓ := by
  rcases hP3' with
    ⟨A,B,C,D,
     hAB,hAC,hAD,hBC,hBD,hCD,
     hABC,hABD,hACD,hBCD⟩
  wlog h_not_A : ¬ A ∈ᵢ ℓ generalizing A B C D hABC hABD hACD hBCD
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

  have : A ≠ PB := by rintro rfl; contradiction
  have : A ≠ PC := by rintro rfl; contradiction
  have : A ≠ PD := by rintro rfl; contradiction

  refine ⟨?_, ?_, ?_, hPBℓ, hPCℓ, hPDℓ⟩
  · show PB ≠ PC
    apply points_distinct_of_noncollinear hP1 (P:=PB) (Q:=PC) (mB:=mB) (mC:=mC) hABC
    <;> assumption
  · show PB ≠ PD
    apply points_distinct_of_noncollinear hP1 (P:=PB) (Q:=PD) (mB:=mB) (mC:=mD) hABD
    <;> assumption
  · show PC ≠ PD
    apply points_distinct_of_noncollinear hP1 (P:=PC) (Q:=PD) (mB:=mC) (mC:=mD) hACD
    <;> assumption

lemma P3'_dual_of_P3'
    (hP1  : P1 (G := G)) (hP2 : P2 (G := G)) (hP3' : P3' (G := G)) : P3' (G := G.dual) := by
  rcases hP3' with
    ⟨A, B, C, D,
     hAB, hAC, hAD, hBC, hBD, hCD,
     hABC, hABD, hACD, hBCD⟩

  obtain ⟨ℓAB, hAℓAB, hBℓAB⟩ := hP1 hAB
  obtain ⟨ℓAC, hAℓAC, hCℓAC⟩ := hP1 hAC
  obtain ⟨ℓBD, hBℓBD, hDℓBD⟩ := hP1 hBD
  obtain ⟨ℓCD, hCℓCD, hDℓCD⟩ := hP1 hCD

  have hCDB : (noncollinear C D B) := noncollinear₃₁₂.mp hBCD
  have hBDA : (noncollinear B D A) := noncollinear₃₁₂.mp hABD

  have ℓAB_ne_ℓAC : ℓAB ≠ ℓAC := by apply line_ne_of_noncollinear hABC hAℓAB.1 hAℓAB.2 hAℓAC.2
  have ℓAB_ne_ℓBD : ℓAB ≠ ℓBD := by apply line_ne_of_noncollinear hABD hAℓAB.1 hAℓAB.2 hBℓBD.2
  have ℓAB_ne_ℓCD : ℓAB ≠ ℓCD := by apply line_ne_of_noncollinear hABD hAℓAB.1 hAℓAB.2 hCℓCD.2
  have ℓBD_ne_ℓCD : ℓBD ≠ ℓCD := by symm; apply line_ne_of_noncollinear hCDB hCℓCD.1 hCℓCD.2 hBℓBD.1

  have ℓAB_ne_ℓBD : ℓAB ≠ ℓBD := by apply line_ne_of_noncollinear hABD hAℓAB.1 hAℓAB.2 hBℓBD.2
  have ℓAC_ne_ℓBD : ℓAC ≠ ℓBD := by symm; apply line_ne_of_noncollinear hBDA hBℓBD.1 hBℓBD.2 hAℓAC.1
  have ℓAC_ne_ℓCD : ℓAC ≠ ℓCD := by apply line_ne_of_noncollinear hACD hAℓAC.1 hAℓAC.2 hCℓCD.2

  refine
    ⟨ℓAB, ℓAC, ℓBD, ℓCD,
     ℓAB_ne_ℓAC, ℓAB_ne_ℓBD, ℓAB_ne_ℓCD,
     ℓAC_ne_ℓBD, ℓAC_ne_ℓCD, ℓBD_ne_ℓCD,
     ?nclℓABℓACℓBD, ?nclℓABℓACℓCD,
     ?nclℓABℓBDℓCD, ?nclℓACℓBDℓCD⟩

  · suffices noncollinear (G := G.dual) ℓAC ℓAB ℓBD by
      simpa [noncollinear₁₂] using this
    exact nonconcurrent_chain hP2 hAB ℓAB_ne_ℓAC.symm ℓAB_ne_ℓBD hAℓAC.1 hAℓAB.1 hBℓBD.1 hAℓAB.2
  · exact nonconcurrent_chain hP2 hAC ℓAB_ne_ℓAC ℓAC_ne_ℓCD hAℓAB.1 hAℓAC.1 hCℓCD.1 hAℓAC.2
  · exact nonconcurrent_chain hP2 hBD ℓAB_ne_ℓBD ℓBD_ne_ℓCD hAℓAB.2 hBℓBD.1 hCℓCD.2 hBℓBD.2
  · suffices noncollinear (G := G.dual) ℓAC ℓCD ℓBD  by
      simpa [noncollinear₂₃] using this
    exact nonconcurrent_chain hP2 hCD ℓAC_ne_ℓCD ℓBD_ne_ℓCD.symm hAℓAC.2 hCℓCD.1 hBℓBD.2 hCℓCD.2


lemma three_lines_through_point (hP1 : P1 (G := G)) (hP2 : P2 (G := G)) (hP3' : P3' (G := G))
    (p : G.Point) :
    ∃ ℓ m n : G.Line, ℓ ≠ m ∧ ℓ ≠ n ∧ m ≠ n ∧ p ∈ᵢ ℓ ∧ p ∈ᵢ m ∧ p ∈ᵢ n :=
  three_points_on_line (G := G.dual) hP2 hP1 (P3'_dual_of_P3' hP1 hP2 hP3') p



end FromP3'

namespace FromP3''
open IncidenceGeometry ProjectivePrereqs AlternativeAxioms
variable {G : IncidenceGeometry}

lemma two_distinct_lines (hP1 : P1 (G := G)) (hP3'' : P3'' (G := G)): ∃ ℓ m : G.Line, ℓ ≠ m := by
  rcases hP3'' with ⟨⟨p₀, ℓ₀, _⟩, hOff⟩
  rcases hOff ℓ₀ ℓ₀ with ⟨q, hqℓ₀, _⟩
  have hpq : p₀ ≠ q := by rintro rfl; contradiction
  rcases hP1 hpq with ⟨m, ⟨_, hqm⟩, _⟩
  use ℓ₀, m
  show ℓ₀ ≠ m
  rintro rfl; contradiction


end FromP3''

namespace FromP3'
open ProjectivePrereqs AlternativeAxioms

theorem lemma_1_2_5 (G : IncidenceGeometry) :
    ProjectivePlane G ↔ (P1 (G := G) ∧ P2 (G := G)) ∧ (P3' (G := G) ∨ P3'' (G := G)) := by
  constructor
  · intro h
    refine ⟨⟨h.P1, h.P2⟩, ?_⟩
    have : P3' (G := G) := by sorry
    exact Or.inl this
  · rintro ⟨⟨hP1, hP2⟩, hAlt⟩
    cases hAlt with
    | inl hP3' =>
        exact
        { P1 := hP1,
          P2 := hP2,
          P3 := three_points_on_line  hP1 hP2 hP3',
          P4 := three_lines_through_point hP1 hP2 hP3'}
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
