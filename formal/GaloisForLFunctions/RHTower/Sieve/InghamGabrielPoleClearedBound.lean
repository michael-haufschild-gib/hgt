import GaloisForLFunctions.RHTower.Sieve.InghamGabrielPoleClearedError
import GaloisForLFunctions.RHTower.Sieve.InghamFixedGabrielIntegralInterpolation
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.HTGeometry.PolynomialExponentialDomination

/-!
# Global boundedness of the Gaussian pole-cleared Gabriel field

Polynomial vertical-strip growth of zeta and the finite mollifier is killed at large height by the
Gabriel Gaussian.  Compactness handles the remaining bounded-height region.  Together these give
the exact global closed-strip boundedness needed by Hadamard three-lines, and hence boundedness of
the concrete coefficient-three scalar family.
-/

open Complex Nat ArithmeticFunction Finset Set

namespace RHTower.Sieve

noncomputable section

/-- The finite Möbius mollifier is bounded by its length throughout the right half-plane. -/
theorem norm_inghamMollifier_le_nat (X : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖inghamMollifier X s‖ ≤ (X : ℝ) := by
  rw [inghamMollifier]
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ ≤
      ∑ n ∈ Finset.Icc 1 X,
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
      have hpow : ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num,
          Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
        apply Real.rpow_le_one_of_one_le_of_nonpos
        · exact_mod_cast hn1
        · simp
          exact hs
      nlinarith [norm_nonneg (((ArithmeticFunction.moebius n : ℤ) : ℂ)),
        norm_nonneg ((n : ℂ) ^ (-s))]
    _ = ((Finset.Icc 1 X).card : ℝ) := by simp
    _ ≤ (X : ℝ) := by
      rw [Nat.card_Icc]
      norm_cast

private theorem abs_re_le_two_of_mem_fixedGabrielClosedStrip {z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) inghamPowerSavingRightEdge) : |z.re| ≤ 2 := by
  rw [abs_of_nonneg (le_trans (by norm_num) hz.1)]
  exact hz.2.trans (by norm_num [inghamPowerSavingRightEdge])

private theorem norm_sub_one_le_two_mul_abs_im_of_mem_fixedGabrielClosedStrip
    {z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) inghamPowerSavingRightEdge) (ht : 1 ≤ |z.im|) :
    ‖z - 1‖ ≤ 2 * |z.im| := by
  have hbase := Complex.norm_le_abs_re_add_abs_im (z - 1)
  have hre : |(z - 1).re| ≤ 1 := by
    simp only [sub_re, one_re]
    rw [abs_le]
    have hzre2 : z.re ≤ 2 :=
      hz.2.trans (by norm_num [inghamPowerSavingRightEdge])
    constructor
    · linarith [hz.1]
    · linarith
  have him : |(z - 1).im| = |z.im| := by simp
  rw [him] at hbase
  linarith

/-- Gaussian decay dominates polynomial zeta growth above unit height. -/
theorem exists_norm_inghamGabrielPoleClearedError_le_of_large_im
    (X : ℕ) {kappa T : ℝ} (hkappa : 0 < kappa) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) inghamPowerSavingRightEdge,
      1 ≤ |z.im| → ‖inghamGabrielPoleClearedError X kappa T z‖ ≤ C := by
  obtain ⟨Cz, N, hCz, hzeta⟩ := RHTower.exists_bound_norm_riemannZeta_strip 2
  let c : ℝ := kappa / T ^ 2
  have hc : 0 < c := div_pos hkappa (sq_pos_of_pos hT)
  let D : ℝ := Real.exp (4 * kappa / T ^ 2) *
    (4 * Cz * (X : ℝ) + 4)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨D * (((N + 1).factorial : ℝ) / c ^ (N + 1)), by positivity, ?_⟩
  intro z hz ht
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    norm_num [Complex.HadamardThreeLines.verticalClosedStrip] at hz
  have hz1 : z ≠ 1 := by
    intro hone
    subst z
    norm_num at ht
  have hzetaBound : ‖riemannZeta z‖ ≤ Cz * |z.im| ^ N := by
    have hzrepr : (z.re : ℂ) + (z.im : ℂ) * I = z := by
      apply Complex.ext <;> simp
    simpa only [hzrepr]
      using hzeta z.re z.im (abs_re_le_two_of_mem_fixedGabrielClosedStrip hz) ht
  have hsub := norm_sub_one_le_two_mul_abs_im_of_mem_fixedGabrielClosedStrip hz ht
  have hG : ‖zetaResidueUnit z‖ ≤ 2 * Cz * |z.im| ^ (N + 1) := by
    rw [zetaResidueUnit, Function.update_of_ne hz1, norm_mul]
    calc
      ‖z - 1‖ * ‖riemannZeta z‖ ≤
          (2 * |z.im|) * (Cz * |z.im| ^ N) :=
        mul_le_mul hsub hzetaBound (norm_nonneg _) (by positivity)
      _ = 2 * Cz * |z.im| ^ (N + 1) := by rw [pow_succ]; ring
  have hM := norm_inghamMollifier_le_nat X (s := z) (le_trans (by norm_num) hz.1)
  have hpowone : |z.im| ≤ |z.im| ^ (N + 1) := by
    calc
      |z.im| = |z.im| ^ 1 := (pow_one _).symm
      _ ≤ |z.im| ^ (N + 1) := pow_le_pow_right₀ ht (by omega)
  have hnum : ‖zetaResidueUnit z * inghamMollifier X z - (z - 1)‖ ≤
      (2 * Cz * (X : ℝ) + 2) * |z.im| ^ (N + 1) := by
    calc
      ‖zetaResidueUnit z * inghamMollifier X z - (z - 1)‖ ≤
          ‖zetaResidueUnit z‖ * ‖inghamMollifier X z‖ + ‖z - 1‖ := by
        exact (norm_sub_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ (2 * Cz * |z.im| ^ (N + 1)) * (X : ℝ) + 2 * |z.im| := by
        gcongr
      _ ≤ (2 * Cz * |z.im| ^ (N + 1)) * (X : ℝ) +
          2 * |z.im| ^ (N + 1) := by gcongr
      _ = (2 * Cz * (X : ℝ) + 2) * |z.im| ^ (N + 1) := by ring
  have hdiv : ‖(zetaResidueUnit z * inghamMollifier X z - (z - 1)) / z‖ ≤
      (4 * Cz * (X : ℝ) + 4) * |z.im| ^ (N + 1) := by
    rw [norm_div]
    have hnormz : 1 / 2 ≤ ‖z‖ :=
      hz.1.trans ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
    apply (div_le_iff₀ (norm_pos_iff.mpr hz0)).mpr
    calc
      ‖zetaResidueUnit z * inghamMollifier X z - (z - 1)‖ ≤
          (2 * Cz * (X : ℝ) + 2) * |z.im| ^ (N + 1) := hnum
      _ ≤ ((4 * Cz * (X : ℝ) + 4) * |z.im| ^ (N + 1)) * ‖z‖ := by
        have hp : 0 ≤ |z.im| ^ (N + 1) := by positivity
        have hA : 0 ≤ (2 * Cz * (X : ℝ) + 2) * |z.im| ^ (N + 1) := by
          positivity
        have hscale : 1 ≤ 2 * ‖z‖ := by linarith
        have hmul := mul_le_mul_of_nonneg_left hscale hA
        nlinarith
  rw [inghamGabrielPoleClearedError, norm_mul]
  have hzrepr : (z.re : ℂ) + (z.im : ℂ) * I = z := by
    apply Complex.ext <;> simp
  have hgauss :
      ‖Complex.exp ((kappa : ℂ) * (z / (T : ℂ)) ^ 2)‖ =
        Real.exp (kappa * z.re ^ 2 / T ^ 2) *
          Real.exp (-kappa * z.im ^ 2 / T ^ 2) := by
    simpa only [hzrepr] using
      norm_inghamGabrielGaussian_vertical kappa T z.re z.im hT.ne'
  rw [hgauss]
  have hsigmaSq : z.re ^ 2 ≤ 4 := by
    have hre := abs_re_le_two_of_mem_fixedGabrielClosedStrip hz
    nlinarith [sq_abs z.re, abs_nonneg z.re]
  have habscissa : Real.exp (kappa * z.re ^ 2 / T ^ 2) ≤
      Real.exp (4 * kappa / T ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hsigmaSq hkappa.le
    apply div_le_div_of_nonneg_right _ (sq_nonneg T)
    simpa [mul_comm] using hmul
  have htSq : |z.im| ≤ z.im ^ 2 := by
    nlinarith [sq_abs z.im, abs_nonneg z.im, ht]
  have hdecay : Real.exp (-kappa * z.im ^ 2 / T ^ 2) ≤
      Real.exp (-(c * |z.im|)) := by
    apply Real.exp_le_exp.mpr
    dsimp only [c]
    have hc0 : 0 ≤ kappa / T ^ 2 := hc.le
    have hmul := mul_le_mul_of_nonneg_left htSq hc0
    calc
      -kappa * z.im ^ 2 / T ^ 2 = -(kappa / T ^ 2 * z.im ^ 2) := by ring
      _ ≤ -(kappa / T ^ 2 * |z.im|) := neg_le_neg hmul
  calc
    Real.exp (kappa * z.re ^ 2 / T ^ 2) *
          Real.exp (-kappa * z.im ^ 2 / T ^ 2) *
        ‖(zetaResidueUnit z * inghamMollifier X z - (z - 1)) / z‖ ≤
      Real.exp (4 * kappa / T ^ 2) * Real.exp (-(c * |z.im|)) *
        ((4 * Cz * (X : ℝ) + 4) * |z.im| ^ (N + 1)) := by gcongr
    _ = D * (|z.im| ^ (N + 1) * Real.exp (-(c * |z.im|))) := by
      dsimp only [D]
      ring
    _ ≤ D * (((N + 1).factorial : ℝ) / c ^ (N + 1)) := by
      exact mul_le_mul_of_nonneg_left
        (GaloisForLFunctions.HTGeometry.pow_mul_exp_neg_le hc (N + 1) (abs_nonneg z.im)) hD

/-- Compactness controls the bounded-height part of the closed Gabriel strip. -/
theorem exists_norm_inghamGabrielPoleClearedError_le_of_small_im
    (X : ℕ) (kappa T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) inghamPowerSavingRightEdge,
      |z.im| ≤ 1 → ‖inghamGabrielPoleClearedError X kappa T z‖ ≤ C := by
  let K : Set ℂ := Metric.closedBall 0 3 ∩
    Complex.HadamardThreeLines.verticalClosedStrip
      (1 / 2) inghamPowerSavingRightEdge
  have hstripClosed : IsClosed
      (Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) inghamPowerSavingRightEdge) := by
    exact isClosed_Icc.preimage continuous_re
  have hKcompact : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) 3).inter_right hstripClosed
  have hcontinuous : ContinuousOn
      (inghamGabrielPoleClearedError X kappa T) K := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      norm_num [K, Complex.HadamardThreeLines.verticalClosedStrip] at hz
    exact (analyticAt_inghamGabrielPoleClearedError X kappa T hz0).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (hKcompact.bddAbove_image hcontinuous.norm)
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro z hz ht
  have hzball : z ∈ Metric.closedBall (0 : ℂ) 3 := by
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hre := abs_re_le_two_of_mem_fixedGabrielClosedStrip hz
    have hnorm := Complex.norm_le_abs_re_add_abs_im z
    linarith
  have hzK : z ∈ K := ⟨hzball, hz⟩
  exact (hC _ (Set.mem_image_of_mem _ hzK)).trans (le_max_right _ _)

/-- The Gaussian pole-cleared error is globally bounded on the fixed closed Gabriel strip. -/
theorem exists_norm_inghamGabrielPoleClearedError_le_fixedStrip
    (X : ℕ) {kappa T : ℝ} (hkappa : 0 < kappa) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) inghamPowerSavingRightEdge,
      ‖inghamGabrielPoleClearedError X kappa T z‖ ≤ C := by
  obtain ⟨Clarge, hClarge, hlarge⟩ :=
    exists_norm_inghamGabrielPoleClearedError_le_of_large_im X hkappa hT
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    exists_norm_inghamGabrielPoleClearedError_le_of_small_im X kappa T
  refine ⟨max Clarge Csmall, le_max_of_le_left hClarge, ?_⟩
  intro z hz
  by_cases ht : 1 ≤ |z.im|
  · exact (hlarge z hz ht).trans (le_max_left _ _)
  · exact (hsmall z hz (le_of_not_ge ht)).trans (le_max_right _ _)

/-- The actual pole-cleared scalar family satisfies Hadamard's global boundedness premise. -/
theorem bddAbove_inghamFixedGabrielScalarFamily_poleCleared
    (X : ℕ) {kappa T : ℝ} (hkappa : 0 < kappa) (hT : 0 < T) :
    BddAbove ((norm ∘ inghamFixedGabrielScalarFamily
      (inghamGabrielPoleClearedError X kappa T) T) ''
      Complex.HadamardThreeLines.verticalClosedStrip
        (1 / 2) inghamPowerSavingRightEdge) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_inghamGabrielPoleClearedError_le_fixedStrip X hkappa hT
  exact bddAbove_inghamFixedGabrielScalarFamily_of_bound T C hC hbound

end

end RHTower.Sieve
