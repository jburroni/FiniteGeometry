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
  P0 : Nonempty G.Point
  P0' : Nonempty G.Line
  P1 : ProjectivePrereqs.P1 (G := G)
  P2 : ProjectivePrereqs.P2 (G := G)
  P3 :
    ∀ ℓ : G.Line,
      ∃ A B C : G.Point,
        A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
        A ∈ᵢ ℓ ∧ B ∈ᵢ ℓ ∧ C ∈ᵢ ℓ
  P4 :
    ∀ A : G.Point,
      ∃ ℓ m n : G.Line,
        ℓ ≠ m ∧ ℓ ≠ n ∧ m ≠ n ∧
        A ∈ᵢ ℓ ∧ A ∈ᵢ m ∧ A ∈ᵢ n


instance dual_projective (G : IncidenceGeometry) [ProjectivePlane G] : ProjectivePlane G.dual where
  P0 := ProjectivePlane.P0'
  P0' := ProjectivePlane.P0
  P1 := ProjectivePlane.P2
  P2 := ProjectivePlane.P1
  P3 := ProjectivePlane.P4
  P4 := ProjectivePlane.P3

namespace ProjectivePrereqs
variable {G : IncidenceGeometry} {A B C : G.Point} {ℓ m: G.Line}

noncomputable
def line_through (hAB : A ≠ B) (hP1 : P1 (G:=G)) : G.Line :=
  Classical.choose (hP1 hAB)

lemma line_through_unique
    {p q : G.Point} (hpq : p ≠ q) (hP1 : P1 (G:=G)) {ℓ : G.Line} (hpℓ : p ∈ᵢ ℓ) (hqℓ : q ∈ᵢ ℓ) :
    ℓ = line_through hpq hP1 := by
  let huniq := (Classical.choose_spec (hP1 hpq)).2
  exact huniq ℓ ⟨hpℓ, hqℓ⟩

section noncollinear
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
end noncollinear

lemma noncollinear_of_witness' (hP1 : P1 (G := G)) (hAB : A ≠ B)
    (hAℓ : A ∈ᵢ ℓ) (hBℓ : B ∈ᵢ ℓ) (hCnotℓ : ¬ C ∈ᵢ ℓ) :
    (∀ x : G.Line, A ∈ᵢ x → B ∈ᵢ x → ¬ C ∈ᵢ x) := by
  intro x hAx hBx
  suffices x = ℓ by subst x; exact hCnotℓ
  have h₁ := line_through_unique hAB hP1 hAx hBx
  have h₂ := (line_through_unique hAB hP1 hAℓ hBℓ).symm
  exact h₁.trans h₂

lemma noncollinear_of_witness (hP1 : P1 (G := G)) (hAB : A ≠ B) :
    A ∈ᵢ ℓ ∧ B ∈ᵢ ℓ ∧ ¬C ∈ᵢ ℓ → noncollinear A B C := by
  rintro ⟨hAℓ, hBℓ, hC_not_ℓ⟩
  simp [noncollinear, triSet, collinear]
  exact noncollinear_of_witness' hP1 hAB hAℓ hBℓ hC_not_ℓ

lemma line_eq_of_point_eq
    (hP1 : P1 (G := G)) (hA_ne_B : A ≠ B)
    (hAℓ : A ∈ᵢ ℓ) (hBℓ : B ∈ᵢ ℓ) (hAm : A ∈ᵢ m) (hBm : B ∈ᵢ m) : ℓ = m := by
  obtain ⟨l, _, huniq⟩ := hP1 hA_ne_B
  have hℓ : ℓ = l := huniq ℓ ⟨hAℓ, hBℓ⟩
  have hm : m = l := huniq m ⟨hAm, hBm⟩
  trans l
  · exact hℓ
  · exact hm.symm

lemma not_mem_of_line_ne (hP1 : P1 (G := G)) (hAB : A ≠ B)
    (hAℓ : A ∈ᵢ ℓ) (hBℓ : B ∈ᵢ ℓ) (hAm : A ∈ᵢ m) (hne : ℓ ≠ m) :
    ¬ B ∈ᵢ m := by
  intro hBm
  have : ℓ = m := line_eq_of_point_eq (G := G) (hP1 := hP1) hAB hAℓ hBℓ hAm hBm
  exact hne this

end ProjectivePrereqs


namespace AlternativeAxioms
open ProjectivePrereqs
variable {G : IncidenceGeometry}


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


section FromP3'
open IncidenceGeometry ProjectivePrereqs AlternativeAxioms
variable {G : IncidenceGeometry}
variable {ℓ m : G.Line} {A B C : G.Point}
variable (hP1 : P1 (G := G)) (hP2 : P2 (G := G)) (hP3' : P3' (G := G))



lemma point_eq_of_incident
    (hP2 : P2 (G := G)) (hℓm : ℓ ≠ m) (hAℓ : A ∈ᵢ ℓ) (hAm : A ∈ᵢ m)
    (hBℓ : B ∈ᵢ ℓ) (hBm : B ∈ᵢ m) : A = B :=
  line_eq_of_point_eq (G := G.dual) (hP1 := hP2) hℓm hAℓ hAm hBℓ hBm

lemma line_ne_of_noncollinear
    (hABC  : noncollinear A B C) (hAℓ  : A ∈ᵢ ℓ) (hBℓ : B ∈ᵢ ℓ) (hCm : C ∈ᵢ m) : ℓ ≠ m := by
  rintro rfl
  apply hABC; use ℓ; simp [collinear, triSet]
  exact ⟨hAℓ, hBℓ, hCm⟩

lemma points_distinct_of_noncollinear (hP1 : P1 (G := G)) {P Q : G.Point}
    (hABC : noncollinear A B C) (hA_ne_P : A ≠ P) {mB mC : G.Line}
    (hAmB : A ∈ᵢ mB) (hBmB : B ∈ᵢ mB) (_ : A ∈ᵢ mC) (hCmC : C ∈ᵢ mC)
    (_ : P ∈ᵢ mB) (_ : Q ∈ᵢ mC) : P ≠ Q := by
  rintro rfl
  apply line_ne_of_noncollinear hABC hAmB hBmB hCmC
  show mB = mC
  apply line_eq_of_point_eq hP1 hA_ne_P <;> assumption



lemma nonconcurrent_chain (hP2 : P2 (G := G)) (hAB : A ≠ B) (h₁ : ℓ ≠ m) (h₂ : m ≠ n)
    (h₃ : A ∈ᵢ ℓ) (h₄ : A ∈ᵢ m) (h₅ : B ∈ᵢ n) (h₆ : B ∈ᵢ m) : noncollinear (G:= G.dual) ℓ m n := by
  suffices h_no_common : ¬ ∃ A' : G.Point, A' ∈ᵢ ℓ ∧ A' ∈ᵢ m ∧ A' ∈ᵢ n by
    simpa [noncollinear, collinear, triSet] using h_no_common
  intro ⟨A', _, _, _⟩
  apply hAB
  calc A
    _ = A' := by symm; apply point_eq_of_incident (ℓ:= ℓ) (m:=m) (A:=A') (B:=A) <;> assumption
    _ = B := by apply point_eq_of_incident (ℓ:= m) (m:=n) (A:=A') (B:=B) <;> assumption


lemma noncollinear_of_line_through_AB_not_C (hP1 : P1 (G := G)) (hAB : A ≠ B)
    (hAℓ : A ∈ᵢ ℓ) (hBℓ : B ∈ᵢ ℓ) (hC_not_ℓ : ¬ C ∈ᵢ ℓ) : noncollinear A B C := by
  intro hCol
  simp [triSet, collinear] at hCol
  rcases hCol with ⟨m, _, _, hCm⟩
  obtain ⟨_, ⟨_, _⟩, _⟩ := hP1 hAB
  have : ℓ = m := by apply line_eq_of_point_eq hP1 hAB <;> assumption
  subst m
  exact hC_not_ℓ hCm



lemma three_points_on_line (hP1 : P1 (G := G)) (hP2 : P2 (G := G)) (hP3' : P3' (G := G))
    (ℓ : G.Line) : ∃ P Q R : G.Point, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ P ∈ᵢ ℓ ∧ Q ∈ᵢ ℓ ∧ R ∈ᵢ ℓ := by
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


lemma three_lines_through_point (hP1 : P1 (G := G)) (hP2 : P2 (G := G)) (hP3' : P3' (G := G)) (A : G.Point) :
  ∃ ℓ m n : G.Line, ℓ ≠ m ∧ ℓ ≠ n ∧ m ≠ n ∧ A ∈ᵢ ℓ ∧ A ∈ᵢ m ∧ A ∈ᵢ n :=
  three_points_on_line (G := G.dual) hP2 hP1 (P3'_dual_of_P3' hP1 hP2 hP3') A


lemma point_from_P3' (hP3' : P3' (G := G)) : Nonempty G.Point := by
  obtain ⟨A, _⟩ := hP3'
  exact ⟨A⟩

lemma line_from_P1_P3' (hP1 : ProjectivePrereqs.P1 (G := G)) (hP3' : P3' (G := G)) :
    Nonempty G.Line := by
  rcases hP3' with ⟨_, _, _, _, hAB, _⟩
  rcases hP1 hAB with ⟨ℓ, _⟩
  exact ⟨ℓ⟩
end FromP3'

section FromP3''
open IncidenceGeometry ProjectivePrereqs AlternativeAxioms
variable {G : IncidenceGeometry} {A B C: G.Point} {ℓ m: G.Line}

lemma exists_line_with_point_and_nonpoint (hP3'' : P3'' (G := G)) : ∃ ℓ : G.Line, ∃ A B, A ∈ᵢ ℓ ∧ ¬B ∈ᵢ ℓ := by
  rcases hP3'' with ⟨⟨A, ℓ₀, hAℓ₀⟩, hOff⟩
  rcases hOff ℓ₀ ℓ₀ with ⟨B, hBℓ₀, _⟩
  exact ⟨ℓ₀, A, B, hAℓ₀, hBℓ₀⟩

lemma two_distinct_lines (hP1 : P1 (G := G)) (hP3'' : P3'' (G := G)): ∃ ℓ m : G.Line, ℓ ≠ m := by
  rcases exists_line_with_point_and_nonpoint hP3'' with ⟨ℓ, A, B, hAℓ, hBnotℓ⟩
  have hBA : B ≠ A := point_ne_of_mem_not_mem hBnotℓ hAℓ
  rcases hP1 hBA.symm with ⟨m, ⟨_, hBm : B ∈ᵢ m⟩, _⟩
  use m, ℓ
  show m ≠ ℓ
  exact line_ne_of_mem_not_mem hBm hBnotℓ

lemma exists_line_through_point_off (hP1 : P1 (G := G)) (hP3'' : P3'' (G := G))
    (hAℓ : A ∈ᵢ ℓ) : ∃ m : G.Line, A ∈ᵢ m ∧ m ≠ ℓ := by
  rcases hP3''.2 ℓ ℓ with ⟨Q, hQℓ, _⟩
  have hAQ : Q ≠ A := point_ne_of_mem_not_mem hQℓ hAℓ
  rcases hP1 hAQ.symm with ⟨r, ⟨hAr, hQr⟩, _⟩
  exact ⟨r, hAr, line_ne_of_mem_not_mem hQr hQℓ⟩

lemma exists_third_line_through_point_off_two
    (hP1 : P1 (G := G)) (hP3'' : P3'' (G := G))
    (hAℓ : A ∈ᵢ ℓ) : ∃ n : G.Line, A ∈ᵢ n ∧ n ≠ ℓ ∧ n ≠ m := by
  rcases hP3''.2 ℓ m with ⟨B, hBℓ, hBm⟩
  have hAQ : B ≠ A := point_ne_of_mem_not_mem hBℓ hAℓ
  rcases hP1 hAQ with ⟨n, ⟨hAn, hQn⟩, _⟩
  refine ⟨n, hQn, ?_, ?_⟩
  <;> apply line_ne_of_mem_not_mem hAn <;> assumption


lemma P3'_of_P3''
    (hP1 : P1 (G := G)) (hP2 : P2 (G := G)) (hP3'' : P3'' (G := G)) :
    P3' (G := G) := by
  obtain ⟨ℓ, m, hℓm⟩ := two_distinct_lines (G := G) hP1 hP3''
  obtain ⟨B, ⟨hBℓ, hBm⟩, hBuniq⟩ := hP2 hℓm
  rcases hP3''.2 ℓ m with ⟨A, hAℓ, hAm⟩
  have hAB : A ≠ B := point_ne_of_mem_not_mem hAℓ hBℓ

  obtain ⟨n, ⟨hAn, hBn⟩, huniq_n⟩ := hP1 hAB

  obtain ⟨r, hAr, hr_ne_n⟩ := exists_line_through_point_off (G := G) hP1 hP3'' hAn
  obtain ⟨s, hAs, hs_ne_n, hs_ne_r⟩ := exists_third_line_through_point_off_two hP1 hP3'' hAn (m:=r)

  have hr_ne_ℓ : r ≠ ℓ := line_ne_of_mem_not_mem hAr hAℓ
  obtain ⟨C, ⟨hCr, hCℓ⟩, _⟩ := hP2 hr_ne_ℓ

  have hs_ne_m : s ≠ m := line_ne_of_mem_not_mem hAs hAm
  obtain ⟨D, ⟨hDs, hDm⟩, _⟩ := hP2 hs_ne_m

  have hAC : A ≠ C := point_ne_of_mem_not_mem hAℓ hCℓ
  have hAD : A ≠ D := point_ne_of_mem_not_mem hAm hDm

  have hBr : ¬ B ∈ᵢ r := not_mem_of_line_ne hP1 hAB hAn hBn hAr hr_ne_n.symm
  have hBs : ¬ B ∈ᵢ s := not_mem_of_line_ne hP1 hAB hAn hBn hAs hs_ne_n.symm

  have hBC : B ≠ C := point_ne_of_mem_not_mem hBr hCr
  have hBD : B ≠ D := point_ne_of_mem_not_mem hBs hDs

  have hCD : C ≠ D := by
    rintro rfl
    have : C = B := hBuniq C ⟨hCℓ, hDm⟩
    exact hBC this.symm

  have hCnotn : ¬ C ∈ᵢ n := not_mem_of_line_ne hP1 hAC hAr hCr hAn hr_ne_n
  have hDnotn : ¬ D ∈ᵢ n := not_mem_of_line_ne hP1 hAD hAs hDs hAn hs_ne_n
  have hDnotr : ¬ D ∈ᵢ r := not_mem_of_line_ne hP1 hAD hAs hDs hAr hs_ne_r
  have hDnotℓ : ¬ D ∈ᵢ ℓ := not_mem_of_line_ne hP1 hBD hBm hDm hBℓ hℓm.symm

  -- assemble noncollinearities (as you already do)
  have hABC : noncollinear A B C := noncollinear_of_line_through_AB_not_C hP1 hAB hAn hBn hCnotn
  have hABD : noncollinear A B D := noncollinear_of_line_through_AB_not_C hP1 hAB hAn hBn hDnotn
  have hACD : noncollinear A C D := noncollinear_of_line_through_AB_not_C hP1 hAC hAr hCr hDnotr
  have hBCD : noncollinear B C D := noncollinear_of_line_through_AB_not_C hP1 hBC hBℓ hCℓ hDnotℓ

  exact
    ⟨A, B, C, D,
     hAB, hAC, hAD, hBC, hBD, hCD,
     hABC, hABD, hACD, hBCD⟩


end FromP3''

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
        { P0 := point_from_P3' hP3',
          P0' := line_from_P1_P3' hP1 hP3',
          P1 := hP1,
          P2 := hP2,
          P3 := three_points_on_line  hP1 hP2 hP3',
          P4 := three_lines_through_point hP1 hP2 hP3'}
    | inr hP3'' =>
        have hP3' : P3' := P3'_of_P3'' hP1 hP2 hP3''
        exact
        { P0 := point_from_P3' hP3',
          P0' := line_from_P1_P3' hP1 hP3',
          P1 := hP1,
          P2 := hP2,
          P3 := three_points_on_line hP1 hP2 hP3',
          P4 := three_lines_through_point hP1 hP2 hP3' }

end AlternativeAxioms
