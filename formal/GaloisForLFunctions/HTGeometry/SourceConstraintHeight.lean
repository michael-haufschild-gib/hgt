import GaloisForLFunctions.HTGeometry.NormalCrossingCriticalDerivedPhase

/-!
# Source-constraint height and the boundary-charge phase transition

The squarefree coface ideal in `r+1` structural directions first appears at coordinate width
`r`.  Consequently no fixed finite source-depth cutoff sees every normal-crossing constraint.
For the same hierarchy this exact source height is one more than the derived-critical amplitude.

The last two theorems isolate the finite algebra behind a second phase transition.  Two oriented
boundary directions may carry a common nonzero jump.  With three directions, four adjacent mixed-
orthant cancellations already force every jump to vanish.  The analytic input turning local
meromorphic finiteness into those cancellations is kept outside this algebraic file.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.VeroneseIdeal
open MvPolynomial Finset

noncomputable section

/-- A squarefree source ideal has exact constraint height `h` when it contains a coordinate
product of width `h`, but no coordinate product of smaller width. -/
def HasExactSquarefreeConstraintHeight
    {F : Type*} [Field F] {r : ℕ}
    (I : Ideal (MvPolynomial (Fin (r + 1)) F)) (h : ℕ) : Prop :=
  (∃ J : Finset (Fin (r + 1)), J.card = h ∧
      (∏ j ∈ J, (X j : MvPolynomial (Fin (r + 1)) F)) ∈ I) ∧
    ∀ J : Finset (Fin (r + 1)), J.card < h →
      (∏ j ∈ J, (X j : MvPolynomial (Fin (r + 1)) F)) ∉ I

/-- The squarefree coface ideal in `r+1` directions has exact source-constraint height `r`. -/
theorem veroneseIdeal_hasExactSquarefreeConstraintHeight
    {F : Type*} [Field F] (r : ℕ) :
    HasExactSquarefreeConstraintHeight
      (veroneseIdeal F (Fin (r + 1)) r) r := by
  constructor
  · refine ⟨Finset.univ.erase 0, by simp, ?_⟩
    apply Ideal.subset_span
    exact ⟨Finset.univ.erase 0, by simp, rfl⟩
  · intro J hJ
    exact prod_X_not_mem_veroneseIdeal_of_card_lt J hJ

/-- No nonzero polynomial of total augmentation degree below `r` belongs to the squarefree
coface ideal of height `r`. -/
theorem totalDegree_lt_constraintHeight_not_mem_veroneseIdeal
    {F : Type*} [Field F] {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) F) (hP : P ≠ 0)
    (hdegree : P.totalDegree < r) :
    P ∉ veroneseIdeal F (Fin (r + 1)) r := by
  intro hmem
  obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hP
  have hwide := (monoWide_of_mem_ideal hmem) d (mem_support_iff.mp hd)
  have hcard : d.support.card ≤ ∑ i ∈ d.support, d i := by
    calc
      d.support.card = ∑ i ∈ d.support, 1 := by simp
      _ ≤ ∑ i ∈ d.support, d i := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hsum : (∑ i ∈ d.support, d i) ≤ P.totalDegree := by
    simpa [Finsupp.sum] using le_totalDegree hd
  omega

/-- Every fixed source-depth cutoff misses the next normal-crossing constraint: no nonzero source
operator polynomial visible through the cutoff annihilates, while one of degree one level higher
does. -/
theorem boundedSourceDepth_misses_next_normalCrossingConstraint
    (F : Type*) [Field F] (bound : ℕ) :
    ∃ r : ℕ, bound < r ∧
      (∀ P : MvPolynomial (Fin (r + 1)) F, P ≠ 0 → P.totalDegree ≤ bound →
        P ∉ veroneseIdeal F (Fin (r + 1)) r) ∧
      ∃ J : Finset (Fin (r + 1)), J.card = r ∧
        (∏ j ∈ J, (X j : MvPolynomial (Fin (r + 1)) F)) ∈
          veroneseIdeal F (Fin (r + 1)) r := by
  let r := bound + 1
  have hheight := veroneseIdeal_hasExactSquarefreeConstraintHeight (F := F) r
  refine ⟨r, by omega, ?_, hheight.1⟩
  intro P hP hdegree
  exact totalDegree_lt_constraintHeight_not_mem_veroneseIdeal P hP (by omega)

/-- In the normal-crossing hierarchy, exact source height is one more than exact derived-critical
amplitude. -/
theorem normalCrossing_constraintHeight_eq_derivedAmplitude_succ
    {F : Type*} [Field F] {r : ℕ} (hr : 1 ≤ r)
    (input : NormalCrossingKoszulGradeInput r) :
    HasExactSquarefreeConstraintHeight
        (veroneseIdeal F (Fin (r + 1)) r) r ∧
      HasExactHomologicalAmplitude input.homologyNonzero (r - 1) ∧
      r = (r - 1) + 1 := by
  exact ⟨veroneseIdeal_hasExactSquarefreeConstraintHeight r,
    normalCrossing_exactDerivedAmplitude hr input, by omega⟩

/-- From source height two onward, the complete family of immediate coface multiplications detects
membership in the coface ideal.  Equivalently, immediate faces are jointly conservative on the
normal-crossing quotient. -/
theorem mem_veroneseIdeal_iff_all_X_mul_mem
    {F : Type*} [Field F] {r : ℕ} (hr : 2 ≤ r)
    (P : MvPolynomial (Fin (r + 1)) F) :
    P ∈ veroneseIdeal F (Fin (r + 1)) r ↔
      ∀ i, X i * P ∈ veroneseIdeal F (Fin (r + 1)) r := by
  constructor
  · intro hP i
    exact Ideal.mul_mem_left _ _ hP
  · intro hXP
    rw [mem_veroneseIdeal_iff]
    intro d hd
    by_cases hd0 : d = 0
    · subst d
      let i : Fin (r + 1) := 0
      have hwide := monoWide_of_mem_ideal (hXP i)
      have hcoeff :
          coeff (Finsupp.single i 1 + 0) (X i * P) ≠ 0 := by
        simpa only [coeff_X_mul] using hd
      have hwidth := hwide (Finsupp.single i 1 + 0) hcoeff
      simp at hwidth
      omega
    · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
      have hwide := monoWide_of_mem_ideal (hXP i)
      have hcoeff :
          coeff (Finsupp.single i 1 + d) (X i * P) ≠ 0 := by
        simpa only [coeff_X_mul] using hd
      have hwidth := hwide (Finsupp.single i 1 + d) hcoeff
      have hisupport : i ∈ d.support := hi
      have hsupport : (Finsupp.single i 1 + d).support = d.support := by
        ext j
        rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
        by_cases hji : i = j
        · subst j
          rw [Finsupp.add_apply]
          simp [Finsupp.mem_support_iff.mp hisupport]
        · rw [Finsupp.add_apply]
          simp [hji]
      rwa [hsupport] at hwidth

/-- The immediate-face detector fails exactly at source height one: the constant class survives,
but every coordinate multiple of it vanishes in the quotient. -/
theorem heightOne_all_X_mul_not_conservative
    (F : Type*) [Field F] :
    (1 : MvPolynomial (Fin 2) F) ∉ veroneseIdeal F (Fin 2) 1 ∧
      ∀ i, X i * (1 : MvPolynomial (Fin 2) F) ∈
        veroneseIdeal F (Fin 2) 1 := by
  constructor
  · simpa using
      (prod_X_not_mem_veroneseIdeal_of_card_lt (F := F) (r := 1) ∅ (by simp))
  · intro i
    apply Ideal.subset_span
    exact ⟨{i}, by simp, by simp⟩

section OrthantBoundary

variable {A : Type*} [AddCommGroup A]

/-- With two source directions, vanishing on the two mixed orthants permits a nonzero boundary
jump, but forces the two jumps to agree.  This is the algebraic core of triptic reciprocity. -/
theorem rankTwo_mixedOrthant_reciprocity
    (neg pos : Fin 2 → A)
    (hforward : pos 0 + neg 1 = 0)
    (hbackward : neg 0 + pos 1 = 0) :
    pos 0 - neg 0 = pos 1 - neg 1 := by
  have hp0 : pos 0 = -neg 1 := eq_neg_of_add_eq_zero_left hforward
  have hp1 : pos 1 = -neg 0 := eq_neg_of_add_eq_zero_right hbackward
  rw [hp0, hp1]
  abel

/-- With three source directions, four adjacent mixed-orthant cancellations force every boundary
jump to vanish.  Thus the rank-two reciprocity charge has no scalar rank-three continuation. -/
theorem rankThree_mixedOrthant_boundaryCollapse
    (neg pos : Fin 3 → A)
    (h0 : pos 0 + neg 1 + neg 2 = 0)
    (h1 : neg 0 + pos 1 + neg 2 = 0)
    (h01 : pos 0 + pos 1 + neg 2 = 0)
    (h02 : pos 0 + neg 1 + pos 2 = 0) :
    ∀ i, pos i = neg i := by
  intro i
  fin_cases i
  · calc
      pos 0 = (pos 0 + pos 1 + neg 2) - (neg 0 + pos 1 + neg 2) + neg 0 := by abel
      _ = neg 0 := by rw [h01, h1]; simp
  · calc
      pos 1 = (pos 0 + pos 1 + neg 2) - (pos 0 + neg 1 + neg 2) + neg 1 := by abel
      _ = neg 1 := by rw [h01, h0]; simp
  · calc
      pos 2 = (pos 0 + neg 1 + pos 2) - (pos 0 + neg 1 + neg 2) + neg 2 := by abel
      _ = neg 2 := by rw [h02, h0]; simp

end OrthantBoundary

end

end GaloisForLFunctions.HTGeometry
