import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Interference
import GaloisForLFunctions.HTGeometry.SeparableBuresIncidenceLaw

/-! # Relative alignment of occupied levels from the magnitude of a return -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ReturnIntensity

open Filter Topology UniversalResponse
open scoped NNReal

def signal (A : Response) (P : ℕ+ → ℝ) (t : ℝ≥0) : ℂ :=
  ∑' n, survivalAmplitude A n t * (P n : ℂ)

private theorem dominated (A : Response) {P : ℕ+ → ℝ} (pos : ∀ n, 0 ≤ P n) (t : ℝ≥0) (n : ℕ+) :
    ‖survivalAmplitude A n t * (P n : ℂ)‖ ≤ P n := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pos n)]
  exact mul_le_of_le_one_left (pos n) (survival_bound A n t)

theorem terms_summable (A : Response) {P : ℕ+ → ℝ} (pos : ∀ n, 0 ≤ P n) (sum : Summable P) (t : ℝ≥0) :
    Summable (fun n => survivalAmplitude A n t * (P n : ℂ)) :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (dominated A pos t) sum)

theorem signal_zero (A : Response) (P : ℕ+ → ℝ) : signal A P 0 = ((∑' n, P n : ℝ) : ℂ) := by
  simp only [signal, survival_zero, one_mul, Complex.ofReal_tsum]

def aligned (A : Response) (P : ℕ+ → ℝ) (n : ℕ+) (t : ℝ≥0) : ℂ :=
  _root_.RHTower.overlapPhase (signal A P t) * survivalAmplitude A n t

private theorem aligned_norm (A : Response) (P : ℕ+ → ℝ) (n : ℕ+) (t : ℝ≥0) :
    ‖aligned A P n t‖ ≤ 1 := by
  rw [aligned, norm_mul, _root_.RHTower.overlapPhase_norm, one_mul]
  exact survival_bound A n t

/-- One rotation makes the sum real and nonnegative. Its deficit bounds
the squared distance of each rotated amplitude from one, with its own mass. -/
theorem aligned_defect (A : Response) {P : ℕ+ → ℝ} (pos : ∀ n, 0 ≤ P n) (sum : Summable P)
    (n : ℕ+) (t : ℝ≥0) :
    P n * ‖aligned A P n t - 1‖ ^ 2 ≤ 2 * ((∑' k, P k) - ‖signal A P t‖) := by
  let q := _root_.RHTower.overlapPhase (signal A P t)
  have rotation := ((terms_summable A pos sum t).hasSum.mul_left q)
  change HasSum _ (q * signal A P t) at rotation
  rw [show q * signal A P t = (‖signal A P t‖ : ℂ) from _root_.RHTower.overlapPhase_mul _] at rotation
  have rotated : HasSum (fun k => (aligned A P k t).re * P k) ‖signal A P t‖ := by
    apply (Complex.hasSum_re rotation).congr_fun
    intro k
    change (q * survivalAmplitude A k t).re * P k = (q * (survivalAmplitude A k t * (P k : ℂ))).re
    rw [← mul_assoc, Complex.mul_re (q * survivalAmplitude A k t) (P k : ℂ),
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have diff := sum.hasSum.sub rotated
  have term (k : ℕ+) : 0 ≤ P k - (aligned A P k t).re * P k :=
    sub_nonneg.mpr (mul_le_of_le_one_left (pos k) ((Complex.re_le_norm _).trans (aligned_norm A P k t)))
  have le := diff.summable.le_tsum n fun k _ => term k
  rw [diff.tsum_eq] at le
  let z := aligned A P n t
  have unit := (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr (aligned_norm A P n t)
  change ‖z‖^2 ≤ 1^2 at unit
  rw [Complex.sq_norm, Complex.normSq_apply, one_pow] at unit
  have disk : ‖z-1‖^2 ≤ 2*(1-z.re) := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, sub_zero]
    linarith only [unit]
  calc
    _ ≤ P n * (2*(1-z.re)) := mul_le_mul_of_nonneg_left disk (pos n)
    _ = 2 * (P n - z.re * P n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left le (by norm_num)

theorem aligned_limit (A : Response) {P : ℕ+ → ℝ} (pos : ∀ n, 0 ≤ P n) (sum : Summable P)
    (h : ContinuousAt (fun t => ‖signal A P t‖) 0) {n : ℕ+} (hn : 0 < P n) :
    Tendsto (aligned A P n) (𝓝 0) (𝓝 1) := by
  have lim := h.tendsto
  change Tendsto _ _ (𝓝 ‖signal A P 0‖) at lim
  rw [signal_zero, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg pos)] at lim
  have upper : Tendsto (fun t => 2*((∑' k, P k) - ‖signal A P t‖) / P n) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self, mul_zero, zero_div] using
      (((tendsto_const_nhds (x := ∑' k, P k)).sub lim).const_mul 2).div_const (P n)
  have sqr : Tendsto (fun t => ‖aligned A P n t - 1‖ ^ 2) (𝓝 0) (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun t => (le_div_iff₀ hn).mpr
      ((mul_comm _ _).trans_le (aligned_defect A pos sum n t))) upper
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp sqr

theorem continuous_signal (A : Response) (reg : ContinuousOn A.val Shares) {P : ℕ+ → ℝ}
    (pos : ∀ n, 0 ≤ P n) (sum : Summable P) : ContinuousAt (signal A P) 0 := by
  have amp (n : ℕ+) : Continuous (survivalAmplitude A n) := by
    apply reg.comp_continuous
    · exact Real.continuous_exp.comp (NNReal.continuous_coe.neg.mul continuous_const)
    · exact fun t => survival_share t.property n
  change Tendsto _ _ _
  rw [signal_zero, Complex.ofReal_tsum]
  apply tendsto_tsum_of_dominated_convergence sum
  · intro n
    simpa only [survival_zero, one_mul] using ((amp n).continuousAt (x := 0)).tendsto.mul_const (P n : ℂ)
  · exact Filter.Eventually.of_forall (dominated A pos)

#print axioms aligned_defect
#print axioms aligned_limit
#print axioms continuous_signal

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ReturnIntensity
