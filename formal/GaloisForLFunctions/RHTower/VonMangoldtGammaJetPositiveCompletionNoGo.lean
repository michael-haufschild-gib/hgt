import GaloisForLFunctions.RHTower.VonMangoldtGammaJetBoundaryConvergence
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion

/-!
# Depth-one positive-completion obstruction for the order-growing Gamma jet

The order-growing two-boundary packet is a genuine positive source Gram, but that alone does not
make it the completed prime--archimedean moment kernel.  Already at depth one and the central
Cauchy point, its first Euler atom is larger than the entire canonical zeroth moment.  Therefore
no completion obtained by adding a kernel with nonnegative central diagonal can satisfy the
proposed source-value identity.

This is an unconditional source-side no-go.  It forces any surviving completion to contain a
negative or genuinely off-diagonal Schur coupling between the Euler packet and the Gamma/polar
channel; an orthogonal positive direct sum is impossible.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Exact norm square of the depth-one, first-prime order-growing feature at the central Cauchy
point. -/
theorem depthOneOrderGrowingFeature_two_normSq_eq :
    ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        1 (0 : Fin 1) 1 0 2‖ ^ (2 : ℕ) =
      1 / (128 * Real.log 2 * (Real.log 2 ^ (2 : ℕ) - 1 / 4) ^ (2 : ℕ)) := by
  rw [finiteVonMangoldtAllDepthJetBalancedCauchyFeature,
    finiteExponentialAllDepthJetBalancedCauchyFeature,
    finiteVonMangoldtRealWeight, twoBoundaryCauchyJetResidual,
    twoBoundaryCauchyJetNormalizer, expNegOrientedRemainder]
  simp only [Fin.val_zero, pow_zero, Nat.reduceSubDiff, Nat.reduceAdd]
  rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num : Nat.Prime 2)]
  have hexp : Real.exp (-Real.log ((2 : ℕ) : ℝ)) = (1 / 2 : ℝ) := by
    have he : Real.exp (Real.log ((2 : ℕ) : ℝ)) = ((2 : ℕ) : ℝ) :=
      Real.exp_log (by norm_num)
    rw [Real.exp_neg, he]
    norm_num
  rw [hexp]
  norm_num [norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, expNegTruncPoly]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hquad : Real.log 2 ^ (2 : ℕ) - 1 / 4 ≠ 0 := by
    have hlo : (1 / 2 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    nlinarith
  have hnormlog : ‖((Real.log 2 : ℝ) : ℂ)‖ = |Real.log 2| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hnormquad :
      ‖((Real.log 2 : ℂ) ^ (2 : ℕ) - 1 / 4)‖ =
        |Real.log 2 ^ (2 : ℕ) - 1 / 4| := by
    have hcast : ((Real.log 2 : ℂ) ^ (2 : ℕ) - 1 / 4) =
        ((Real.log 2 ^ (2 : ℕ) - 1 / 4 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  have hclog : Complex.log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hclog]
  rw [hnormlog, hnormquad]
  rw [abs_of_pos (Real.log_pos (by norm_num))]
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [abs_of_pos (by
    have hlo : (1 / 2 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    nlinarith : 0 < Real.log 2 ^ (2 : ℕ) - 1 / 4)]
  rw [pow_two]
  field_simp [hlog, hquad]
  rw [Real.sq_sqrt (Real.log_nonneg (by norm_num)), Real.sq_sqrt (by norm_num)]
  ring

/-- The first Euler atom alone has norm square strictly larger than `1/5`. -/
theorem one_fifth_lt_depthOneOrderGrowingFeature_two_normSq :
    (1 / 5 : ℝ) <
      ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        1 (0 : Fin 1) 1 0 2‖ ^ (2 : ℕ) := by
  rw [depthOneOrderGrowingFeature_two_normSq_eq]
  let x : ℝ := Real.log 2
  let q : ℝ := 347 / 500
  let y : ℝ := x ^ (2 : ℕ) - 1 / 4
  let r : ℝ := q ^ (2 : ℕ) - 1 / 4
  have hxpos : 0 < x := Real.log_pos (by norm_num)
  have hxlt : x < q := by
    dsimp only [x, q]
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hypos : 0 < y := by
    dsimp only [y, x]
    have hxhalf : (1 / 2 : ℝ) < Real.log 2 := by
      nlinarith [Real.log_two_gt_d9]
    nlinarith
  have hrpos : 0 < r := by
    dsimp only [r, q]
    norm_num
  have hxSq : x ^ (2 : ℕ) < q ^ (2 : ℕ) :=
    (sq_lt_sq₀ hxpos.le (le_of_lt (hxpos.trans hxlt))).2 hxlt
  have hyr : y < r := by
    exact sub_lt_sub_right hxSq (1 / 4)
  have hySq : y ^ (2 : ℕ) < r ^ (2 : ℕ) :=
    (sq_lt_sq₀ hypos.le hrpos.le).2 hyr
  have hxy : x * y ^ (2 : ℕ) < q * r ^ (2 : ℕ) := by
    calc
      x * y ^ (2 : ℕ) ≤ q * y ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hxlt.le (sq_nonneg y)
      _ < q * r ^ (2 : ℕ) := mul_lt_mul_of_pos_left hySq (by
        dsimp only [q]
        norm_num)
  have hdenlt : 128 * x * y ^ (2 : ℕ) < 5 := by
    calc
      128 * x * y ^ (2 : ℕ) = 128 * (x * y ^ (2 : ℕ)) := by ring
      _ < 128 * (q * r ^ (2 : ℕ)) := mul_lt_mul_of_pos_left hxy (by norm_num)
      _ < 5 := by
        dsimp only [q, r]
        norm_num
  have hdenpos : 0 < 128 * x * y ^ (2 : ℕ) := by positivity
  have hinv := one_div_lt_one_div_of_lt hdenpos hdenlt
  simpa only [x, y] using hinv

/-- At depth one on the central diagonal, every kernel term is the real norm square of its source
feature. -/
theorem depthOneOrderGrowingKernelTerm_zero_zero_eq_normSq (n : ℕ) :
    vonMangoldtAllDepthOrderGrowingCauchyKernelTerm 1 0 0 n =
      (‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
          1 (0 : Fin 1) 1 0 (n + 2)‖ ^ (2 : ℕ) : ℝ) := by
  simp [vonMangoldtAllDepthOrderGrowingCauchyKernelTerm, Complex.mul_conj']

/-- Exact positive-series formula for the depth-one central diagonal. -/
theorem depthOneOrderGrowingKernel_zero_zero_eq_normSq_tsum :
    infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel 1 0 0 =
      ((∑' n : ℕ,
        ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
          1 (0 : Fin 1) 1 0 (n + 2)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel,
    Complex.ofReal_tsum]
  apply tsum_congr
  exact depthOneOrderGrowingKernelTerm_zero_zero_eq_normSq

/-- The whole depth-one central diagonal is larger than `1/5`, already because of its first
prime atom. -/
theorem one_fifth_lt_depthOneOrderGrowingKernel_zero_zero_re :
    (1 / 5 : ℝ) <
      (infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel 1 0 0).re := by
  rw [depthOneOrderGrowingKernel_zero_zero_eq_normSq_tsum]
  simp only [Complex.ofReal_re]
  have hsum : Summable (fun n : ℕ =>
      ‖finiteVonMangoldtAllDepthJetBalancedCauchyFeature
        1 (0 : Fin 1) 1 0 (n + 2)‖ ^ (2 : ℕ)) :=
    (summable_nat_add_iff 2).mpr
      (summable_normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyFeature
        1 (0 : Fin 1) 0)
  exact one_fifth_lt_depthOneOrderGrowingFeature_two_normSq.trans_le
    (hsum.le_tsum 0 (fun n _ => sq_nonneg _))

/-- The depth-one positive Euler kernel strictly exceeds the complete canonical zeroth
prime--archimedean moment. -/
theorem normalizedPrimeArchMoment_zero_lt_depthOneOrderGrowingKernel_zero_zero_re :
    normalizedPrimeArchMoment 0 <
      (infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel 1 0 0).re := by
  calc
    normalizedPrimeArchMoment 0 < 29 / 625 :=
      normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive
    _ < 1 / 5 := by norm_num
    _ < _ := one_fifth_lt_depthOneOrderGrowingKernel_zero_zero_re

/-- **Positive-completion no-go.** Adding any channel with nonnegative central diagonal cannot
turn the depth-one order-growing Euler Gram into the canonical zeroth completed moment. -/
theorem depthOneOrderGrowingKernel_no_nonnegativeDiagonalCompletion
    {C : ℂ} (hC : 0 ≤ C.re) :
    infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel 1 0 0 + C ≠
      (normalizedPrimeArchMoment 0 : ℝ) := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre
  have hstrict :=
    normalizedPrimeArchMoment_zero_lt_depthOneOrderGrowingKernel_zero_zero_re
  linarith

/-- Any correction which did produce the canonical completed zeroth moment would need a strictly
negative central real part below `-96/625`.  This is the quantitative Schur-coupling budget left by
the first Euler atom. -/
theorem depthOneOrderGrowingKernel_completion_forces_negativeBudget
    {C : ℂ}
    (hC : infiniteVonMangoldtAllDepthOrderGrowingCauchyKernel 1 0 0 + C =
      (normalizedPrimeArchMoment 0 : ℝ)) :
    C.re < -(96 / 625 : ℝ) := by
  have hre := congrArg Complex.re hC
  norm_num at hre
  have hkernel := one_fifth_lt_depthOneOrderGrowingKernel_zero_zero_re
  have hmoment :=
    normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive
  norm_num at hkernel hmoment ⊢
  linarith

end

end RHTower
