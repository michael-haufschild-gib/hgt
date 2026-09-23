import GaloisForLFunctions.RHTower.XiHeatCassiniWoldLowerHalfShiftConnectionKernel
import GaloisForLFunctions.RHTower.XiMassAdjacentPrimeMask
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

/-!
# Prime-log gap summability of the physical Route-T residual connection

The centered Wold primitive decays like `exp (-c sqrt(log p))`.  This does not beat the restored
`sqrt p` coefficient termwise.  After the physical half-shift is internalized, however, every
adjacent phase difference contributes one prime-log gap.

The decisive observation is elementary and does not use a prime-gap asymptotic.  Bertrand gives
`h_(n+1) <= 2 h_n` for `h_n = log p_n`; hence

`(h_(n+1)-h_n)/h_n^(2 : ℕ) <= 2 (1/h_n - 1/h_(n+1))`.

Square-root-exponential decay is eventually bounded by `C/h^(2 : ℕ)`, so the residual variation against
the logarithmic mesh is summable by a reciprocal-height telescope.  Therefore the physical
lower-half residual connection is absolutely convergent at every source coordinate.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Successor gap in the ordered prime-log mesh. -/
def xiHeatCassiniOrderedPrimeLogGap (N : ℕ) : ℝ :=
  xiMassNthPrimeLogHeight (N + 1) - xiMassNthPrimeLogHeight N

theorem xiHeatCassiniOrderedPrimeLogGap_nonneg (N : ℕ) :
    0 ≤ xiHeatCassiniOrderedPrimeLogGap N := by
  exact sub_nonneg.mpr
    (nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N))

theorem xiMassNthPrimeLogHeight_pos (N : ℕ) :
    0 < xiMassNthPrimeLogHeight N := by
  exact log_prime_pos (nthPrimeSubtype N)

/-- Bertrand's multiplicative gap bound becomes a factor-two bound on positive log heights. -/
theorem xiMassNthPrimeLogHeight_succ_le_two_mul (N : ℕ) :
    xiMassNthPrimeLogHeight (N + 1) ≤ 2 * xiMassNthPrimeLogHeight N := by
  let p : ℝ := nthPrimeSubtype N
  let q : ℝ := nthPrimeSubtype (N + 1)
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hq : 0 < q := nthPrimeSubtype_pos (N + 1)
  have hq2p : q ≤ 2 * p := by
    dsimp only [p, q]
    exact_mod_cast nthPrimeSubtype_succ_le_two_mul N
  have hlogq : Real.log q ≤ Real.log (2 * p) :=
    Real.strictMonoOn_log.monotoneOn hq (mul_pos (by norm_num) hp) hq2p
  have htwo : Real.log 2 ≤ Real.log p := by
    apply Real.strictMonoOn_log.monotoneOn (by norm_num) hp
    dsimp only [p]
    exact_mod_cast (nthPrimeSubtype N).prop.two_le
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp.ne'] at hlogq
  dsimp only [xiMassNthPrimeLogHeight, p, q]
  linarith

/-- One damped logarithmic cell is charged to a telescoping reciprocal-height drop. -/
theorem xiHeatCassiniOrderedPrimeLogGap_div_sq_le_reciprocal_drop (N : ℕ) :
    xiHeatCassiniOrderedPrimeLogGap N /
        xiMassNthPrimeLogHeight N ^ (2 : ℕ) ≤
      2 * (1 / xiMassNthPrimeLogHeight N -
        1 / xiMassNthPrimeLogHeight (N + 1)) := by
  let x : ℝ := xiMassNthPrimeLogHeight N
  let y : ℝ := xiMassNthPrimeLogHeight (N + 1)
  have hx : 0 < x := xiMassNthPrimeLogHeight_pos N
  have hy : 0 < y := xiMassNthPrimeLogHeight_pos (N + 1)
  have hxy : x ≤ y := nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
  have hy2x : y ≤ 2 * x := xiMassNthPrimeLogHeight_succ_le_two_mul N
  have hdrop : 1 / x - 1 / y = (y - x) / (x * y) := by
    field_simp [hx.ne', hy.ne']
  change (y - x) / x ^ (2 : ℕ) ≤ 2 * (1 / x - 1 / y)
  rw [hdrop]
  rw [show 2 * ((y - x) / (x * y)) = (2 * (y - x)) / (x * y) by ring]
  rw [div_le_div_iff₀ (sq_pos_of_pos hx) (mul_pos hx hy)]
  nlinarith [mul_le_mul_of_nonneg_left hy2x (sub_nonneg.mpr hxy)]

/-- Reciprocal-height telescope: all prime-log gaps weighted by `1/(log p)^(2 : ℕ)` are summable. -/
theorem summable_xiHeatCassiniOrderedPrimeLogGap_div_logHeight_sq :
    Summable (fun N : ℕ =>
      xiHeatCassiniOrderedPrimeLogGap N / xiMassNthPrimeLogHeight N ^ (2 : ℕ)) := by
  apply summable_of_sum_range_le
  · intro N
    exact div_nonneg (xiHeatCassiniOrderedPrimeLogGap_nonneg N) (sq_nonneg _)
  · intro M
    calc
      (∑ N ∈ Finset.range M,
          xiHeatCassiniOrderedPrimeLogGap N / xiMassNthPrimeLogHeight N ^ (2 : ℕ)) ≤
          ∑ N ∈ Finset.range M,
            2 * (1 / xiMassNthPrimeLogHeight N -
              1 / xiMassNthPrimeLogHeight (N + 1)) :=
        Finset.sum_le_sum fun N _ =>
          xiHeatCassiniOrderedPrimeLogGap_div_sq_le_reciprocal_drop N
      _ = 2 * (1 / xiMassNthPrimeLogHeight 0 -
            1 / xiMassNthPrimeLogHeight M) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub']
      _ ≤ 2 * (1 / xiMassNthPrimeLogHeight 0) := by
        have hM := xiMassNthPrimeLogHeight_pos M
        have hInv : 0 ≤ 1 / xiMassNthPrimeLogHeight M :=
          (one_div_pos.mpr hM).le
        linarith

/-- Every square-root-exponential residual rate is summable after multiplication by one
prime-log gap. -/
theorem summable_exp_neg_sqrt_primeLog_mul_successorGap
    {c : ℝ} (hc : 0 < c) :
    Summable (fun N : ℕ =>
      Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)) *
        xiHeatCassiniOrderedPrimeLogGap N) := by
  obtain ⟨C, hC, hrate⟩ :=
    burnolPow_mul_exp_neg_sqrt_le (y := c / 2) (by linarith) 0
  have hmajor :=
    summable_xiHeatCassiniOrderedPrimeLogGap_div_logHeight_sq.mul_left C
  refine Summable.of_nonneg_of_le (fun N => mul_nonneg (Real.exp_nonneg _)
      (xiHeatCassiniOrderedPrimeLogGap_nonneg N)) (fun N => ?_) hmajor
  have hheight := xiMassNthPrimeLogHeight_pos N
  have hrateN := hrate (xiMassNthPrimeLogHeight N) hheight
  have hrateN' :
      Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)) ≤
        C / xiMassNthPrimeLogHeight N ^ (2 : ℕ) := by
    simpa [show 2 * (c / 2) = c by ring] using hrateN
  calc
    Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)) *
        xiHeatCassiniOrderedPrimeLogGap N ≤
      (C / xiMassNthPrimeLogHeight N ^ (2 : ℕ)) *
        xiHeatCassiniOrderedPrimeLogGap N :=
      mul_le_mul_of_nonneg_right hrateN'
        (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
    _ = C * (xiHeatCassiniOrderedPrimeLogGap N /
        xiMassNthPrimeLogHeight N ^ (2 : ℕ)) := by ring

/-- **Finite physical variation of the centered Wold primitive.** -/
theorem summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap :
    Summable (fun N : ℕ =>
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N) := by
  obtain ⟨B, c, hc, hB, hrate⟩ :=
    exists_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate
  have hmajor :=
    (summable_exp_neg_sqrt_primeLog_mul_successorGap hc).mul_left B
  apply hmajor.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hrate] with N hN
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _)
    (xiHeatCassiniOrderedPrimeLogGap_nonneg N))]
  calc
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N ≤
      (B * Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N))) *
        xiHeatCassiniOrderedPrimeLogGap N :=
      mul_le_mul_of_nonneg_right (by simpa [xiMassNthPrimeLogHeight] using hN)
        (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
    _ = B * (Real.exp (-c * Real.sqrt (xiMassNthPrimeLogHeight N)) *
        xiHeatCassiniOrderedPrimeLogGap N) := by ring

/-- One primitive-form adjacent phase connection atom. -/
def xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom
    (x : ℝ) (N : ℕ) : ℂ :=
  (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
    (xiHeatCassiniOrderedPrimeNegativePhase N x -
      xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x)

theorem norm_xiHeatCassiniOrderedPrimeNegativePhase_sub_succ_le
    (x : ℝ) (N : ℕ) :
    ‖xiHeatCassiniOrderedPrimeNegativePhase N x -
        xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x‖ ≤
      xiHeatCassiniOrderedPrimeLogGap N * |x| := by
  have h := norm_xiMassFourierPhase_sub_le
    (xiMassNthPrimeLogHeight N) (xiMassNthPrimeLogHeight (N + 1)) x
  rw [abs_of_nonpos (by
    exact sub_nonpos.mpr
      (nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)))] at h
  simpa [xiHeatCassiniOrderedPrimeNegativePhase,
    xiHeatCassiniOrderedPrimeLogGap] using h

theorem norm_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom_le
    (x : ℝ) (N : ℕ) :
    ‖xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom x N‖ ≤
      (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N) * |x| := by
  rw [xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom, norm_mul,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        ‖xiHeatCassiniOrderedPrimeNegativePhase N x -
          xiHeatCassiniOrderedPrimeNegativePhase (N + 1) x‖ ≤
      |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        (xiHeatCassiniOrderedPrimeLogGap N * |x|) :=
      mul_le_mul_of_nonneg_left
        (norm_xiHeatCassiniOrderedPrimeNegativePhase_sub_succ_le x N)
        (abs_nonneg _)
    _ = (|xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| *
        xiHeatCassiniOrderedPrimeLogGap N) * |x| := by ring

/-- **Absolute convergence of the physical residual phase connection at every source point.** -/
theorem summable_norm_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom
    (x : ℝ) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom x N‖) := by
  have hmajor :=
    summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap.mul_right |x|
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom_le x) hmajor

theorem summable_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom
    (x : ℝ) :
    Summable (xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom x) :=
  (summable_norm_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom x).of_norm

/-- Infinite physical lower-half residual phase kernel. -/
def xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit (x : ℝ) : ℂ :=
  ∑' N : ℕ, xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom x N

/-- The exact finite primitive kernels converge after the terminal residual vanishes. -/
theorem tendsto_xiHeatCassiniWoldResidualLowerHalfPhaseKernel
    (x : ℝ) :
    Tendsto (fun N : ℕ => xiHeatCassiniWoldResidualLowerHalfPhaseKernel N x)
      atTop (𝓝 (xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit x)) := by
  have hterminal : Tendsto (fun N : ℕ =>
      (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) *
        xiHeatCassiniOrderedPrimeNegativePhase N x) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hres := tendsto_xiHeatCassiniOrderedWoldResidualLogDiscrepancy.norm
    simpa [norm_mul, xiHeatCassiniOrderedPrimeNegativePhase,
      Complex.norm_exp, Complex.mul_re] using hres
  have hsummable :=
    summable_xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom x
  have hpartial := hsummable.hasSum_iff_tendsto_nat.mp hsummable.hasSum
  have hadd := hterminal.add hpartial
  simpa only [zero_add, xiHeatCassiniWoldResidualLowerHalfPhaseKernel,
    xiHeatCassiniWoldResidualLowerHalfPhaseKernelLimit,
    xiHeatCassiniWoldResidualLowerHalfPhaseConnectionAtom] using hadd

end

end RHTower
