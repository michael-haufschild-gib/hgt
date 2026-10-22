import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekScalarHistoryClassification

/-!
# Parikh--Wilczek positive matrix cross-grade classification

Every Borel-grade recoil phase contains the same reflection-wall factor.  This
file extracts it from an arbitrary finite matrix interaction across grades.
When the matrix is entrywise nonnegative and nonzero, the remaining quadratic
grade interaction is strictly positive throughout the open critical strip.

Consequently finite positive matrix mixing is still only an exact wall receiver:
its vanishing locus is the critical line, and universal vanishing on the Xi
divisor is exactly RH.  A viable PW-B producer must use signed/complex oriented
couplings, an infinite or singular interaction, or additional source dynamics;
finite positive cross-grade correlations cannot create flatness.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Common reflection-wall factor of every PW Borel-grade recoil phase. -/
def schwarzschildParikhWilczekBorelWallFactor (s : ℂ) : ℝ :=
  -2 * s.im * (2 * s.re - 1)

/-- Strictly positive grade-dependent residual after removing the common wall factor. -/
def schwarzschildParikhWilczekBorelGradeResidual (s : ℂ) (k : ℕ) : ℝ :=
  (2 * (k : ℝ) + s.re + 1 / 2) *
      (2 * (k : ℝ) + 3 / 2 - s.re) +
    s.im ^ (2 : ℕ) + 1 / 4

/-- Exact common-factor decomposition of each recoil phase. -/
theorem schwarzschildParikhWilczekBorelRecoilHolonomy_im_factorization
    (s : ℂ) (k : ℕ) :
    (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im =
      schwarzschildParikhWilczekBorelWallFactor s *
        schwarzschildParikhWilczekBorelGradeResidual s k := by
  rw [schwarzschildParikhWilczekBorelRecoilHolonomy_im]
  rfl

/-- The residual at every Borel grade is strictly positive in the open critical strip. -/
theorem schwarzschildParikhWilczekBorelGradeResidual_pos
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    0 < schwarzschildParikhWilczekBorelGradeResidual s k := by
  rw [schwarzschildParikhWilczekBorelGradeResidual]
  have hleft : 0 < 2 * (k : ℝ) + s.re + 1 / 2 := by positivity
  have hright : 0 < 2 * (k : ℝ) + 3 / 2 - s.re := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  positivity

/-- Finite matrix-valued interaction among recoil phases at different Borel grades. -/
def schwarzschildParikhWilczekMatrixCrossGradeEnergy
    {N : ℕ} (M : Fin N → Fin N → ℝ) (s : ℂ) : ℝ :=
  ∑ i, ∑ j,
    M i j *
      (schwarzschildParikhWilczekBorelRecoilHolonomy s (i : ℕ)).im *
        (schwarzschildParikhWilczekBorelRecoilHolonomy s (j : ℕ)).im

/-- Residual matrix interaction after removing the common wall factor. -/
def schwarzschildParikhWilczekMatrixResidualEnergy
    {N : ℕ} (M : Fin N → Fin N → ℝ) (s : ℂ) : ℝ :=
  ∑ i, ∑ j,
    M i j *
      schwarzschildParikhWilczekBorelGradeResidual s (i : ℕ) *
        schwarzschildParikhWilczekBorelGradeResidual s (j : ℕ)

/-- Every finite matrix cross-grade interaction factors through the squared wall coordinate. -/
theorem schwarzschildParikhWilczekMatrixCrossGradeEnergy_factorization
    {N : ℕ} (M : Fin N → Fin N → ℝ) (s : ℂ) :
    schwarzschildParikhWilczekMatrixCrossGradeEnergy M s =
      schwarzschildParikhWilczekBorelWallFactor s ^ (2 : ℕ) *
        schwarzschildParikhWilczekMatrixResidualEnergy M s := by
  rw [schwarzschildParikhWilczekMatrixCrossGradeEnergy,
    schwarzschildParikhWilczekMatrixResidualEnergy]
  simp_rw [schwarzschildParikhWilczekBorelRecoilHolonomy_im_factorization]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A nonzero entrywise-nonnegative cross-grade matrix has strictly positive residual energy. -/
theorem schwarzschildParikhWilczekMatrixResidualEnergy_pos
    {N : ℕ} {M : Fin N → Fin N → ℝ} (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hMnonneg : ∀ i j, 0 ≤ M i j)
    (hMpos : ∃ i j, 0 < M i j) :
    0 < schwarzschildParikhWilczekMatrixResidualEnergy M s := by
  rw [schwarzschildParikhWilczekMatrixResidualEnergy]
  obtain ⟨i0, j0, hMij⟩ := hMpos
  apply Finset.sum_pos'
  · intro i _
    apply Finset.sum_nonneg
    intro j _
    have hi := schwarzschildParikhWilczekBorelGradeResidual_pos s (i : ℕ) hs0 hs1
    have hj := schwarzschildParikhWilczekBorelGradeResidual_pos s (j : ℕ) hs0 hs1
    exact mul_nonneg (mul_nonneg (hMnonneg i j) hi.le) hj.le
  · refine ⟨i0, Finset.mem_univ i0, ?_⟩
    apply Finset.sum_pos'
    · intro j _
      have hi := schwarzschildParikhWilczekBorelGradeResidual_pos s (i0 : ℕ) hs0 hs1
      have hj := schwarzschildParikhWilczekBorelGradeResidual_pos s (j : ℕ) hs0 hs1
      exact mul_nonneg (mul_nonneg (hMnonneg i0 j) hi.le) hj.le
    · refine ⟨j0, Finset.mem_univ j0, ?_⟩
      have hi := schwarzschildParikhWilczekBorelGradeResidual_pos s (i0 : ℕ) hs0 hs1
      have hj := schwarzschildParikhWilczekBorelGradeResidual_pos s (j0 : ℕ) hs0 hs1
      positivity

/-- Positive finite matrix mixing vanishes exactly on the critical wall. -/
theorem schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff
    {N : ℕ} {M : Fin N → Fin N → ℝ} (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0)
    (hMnonneg : ∀ i j, 0 ≤ M i j)
    (hMpos : ∃ i j, 0 < M i j) :
    schwarzschildParikhWilczekMatrixCrossGradeEnergy M s = 0 ↔
      s.re = 1 / 2 := by
  rw [schwarzschildParikhWilczekMatrixCrossGradeEnergy_factorization]
  have hres := schwarzschildParikhWilczekMatrixResidualEnergy_pos
    s hs0 hs1 hMnonneg hMpos
  constructor
  · intro hzero
    have hwallSq : schwarzschildParikhWilczekBorelWallFactor s ^ (2 : ℕ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hres.ne'
    have hwall : schwarzschildParikhWilczekBorelWallFactor s = 0 :=
      (sq_eq_zero_iff).mp hwallSq
    rw [schwarzschildParikhWilczekBorelWallFactor] at hwall
    rcases mul_eq_zero.mp hwall with hfirst | hcenter
    · exact False.elim (hsim (by linarith))
    · linarith
  · intro hre
    rw [schwarzschildParikhWilczekBorelWallFactor, hre]
    norm_num

/-- Universal flatness of any nonzero positive finite cross-grade matrix is exactly RH. -/
theorem riemannHypothesis_iff_schwarzschildParikhWilczekMatrixCrossGradeEnergy_zero
    {N : ℕ} {M : Fin N → Fin N → ℝ}
    (hMnonneg : ∀ i j, 0 ≤ M i j)
    (hMpos : ∃ i j, 0 < M i j) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        schwarzschildParikhWilczekMatrixCrossGradeEnergy M (rho : ℂ) = 0 := by
  constructor
  · intro hRH rho
    obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit rho
    exact (schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff
      (rho : ℂ) h0 h1 (xi_divisor_support_im_ne_zero rho) hMnonneg hMpos).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho => by
      obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit rho
      exact (schwarzschildParikhWilczekMatrixCrossGradeEnergy_eq_zero_iff
        (rho : ℂ) h0 h1 (xi_divisor_support_im_ne_zero rho) hMnonneg hMpos).mp
        (h rho)

end

end RHTower
