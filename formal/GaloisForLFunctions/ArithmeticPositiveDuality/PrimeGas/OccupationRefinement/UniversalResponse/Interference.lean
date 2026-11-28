import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Endpoint

/-! # One unresolved real return measurement forces a continuous response -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open Filter Topology ModeCapacities CoherentRay
open scoped NNReal

def weightedReturn (A : Response) (P : ℕ+ → ℝ) (t : ℝ≥0) :=
  ∑' n, (survivalAmplitude A n t).re * P n

theorem survival_bound (A : Response) (n : ℕ+) (t : ℝ≥0) : ‖survivalAmplitude A n t‖ ≤ 1 :=
  response_contracts A (survival_share t.property n)

private theorem term_bound (A : Response) {P : ℕ+ → ℝ} (pos : ∀ n, 0 ≤ P n) (n : ℕ+) (t : ℝ≥0) :
    ‖(survivalAmplitude A n t).re * P n‖ ≤ P n := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pos n)]
  exact mul_le_of_le_one_left (pos n) ((Complex.abs_re_le_norm _).trans (survival_bound A n t))

theorem weighted_zero (A : Response) (P : ℕ+ → ℝ) : weightedReturn A P 0 = ∑' n, P n := by
  simp only [weightedReturn, survival_zero, Complex.one_re, one_mul]

private theorem distance_bound {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖z-1‖ ^ 2 ≤ 2*(1-z.re) := by
  have sq := (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr hz
  rw [Complex.sq_norm, Complex.normSq_apply, one_pow] at sq
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero]
  linarith only [sq]

/-- Positive masses prevent cancellation. Each occupied mode pays its
own squared phase distance out of the measured return deficit. -/
theorem mode_defect (A : Response) {P : ℕ+ → ℝ} (pos : ∀ n, 0 ≤ P n) (sum : Summable P)
    (n : ℕ+) (t : ℝ≥0) :
    P n * ‖survivalAmplitude A n t - 1‖ ^ 2 ≤ 2 * ((∑' k, P k) - weightedReturn A P t) := by
  have sm : Summable (fun k => (survivalAmplitude A k t).re * P k) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => term_bound A pos k t) sum)
  have mass := sum.sub sm
  have term (k : ℕ+) : 0 ≤ P k - (survivalAmplitude A k t).re * P k := by
    apply sub_nonneg.mpr
    exact mul_le_of_le_one_left (pos k) ((Complex.re_le_norm _).trans (survival_bound A k t))
  have le := mass.le_tsum n fun k _ => term k
  rw [weightedReturn, ← sum.tsum_sub sm]
  calc
    _ ≤ P n * (2*(1-(survivalAmplitude A n t).re)) :=
      mul_le_mul_of_nonneg_left (distance_bound (survival_bound A n t)) (pos n)
    _ = 2 * (P n - (survivalAmplitude A n t).re * P n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left le (by norm_num)

private theorem mode_continuity (A : Response) {P : ℕ+ → ℝ} (pos : ∀ n, 0 ≤ P n)
    (sum : Summable P) (h : ContinuousAt (weightedReturn A P) 0) {n : ℕ+} (hn : 0 < P n) :
    ContinuousAt (survivalAmplitude A n) 0 := by
  have measured := h.tendsto
  rw [weighted_zero] at measured
  have upper : Tendsto (fun t => 2 * ((∑' k, P k) - weightedReturn A P t) / P n) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self, mul_zero, zero_div] using
      (((tendsto_const_nhds (x := ∑' k, P k)).sub measured).const_mul 2).div_const (P n)
  have lim : Tendsto (fun t => ‖survivalAmplitude A n t - 1‖ ^ 2) (𝓝 0) (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun t => (le_div_iff₀ hn).mpr
      ((mul_comm _ _).trans_le (mode_defect A pos sum n t))) upper
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  rw [survival_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp lim

private theorem return_continuity (A : Response) (reg : ContinuousOn A.val Shares)
    {P : ℕ+ → ℝ} (pos : ∀ n, 0 ≤ P n) (sum : Summable P) :
    ContinuousAt (weightedReturn A P) 0 := by
  have amp (n : ℕ+) : Continuous (survivalAmplitude A n) := by
    apply reg.comp_continuous
    · exact Real.continuous_exp.comp (NNReal.continuous_coe.neg.mul continuous_const)
    · exact fun t => survival_share t.property n
  change Tendsto _ _ _
  rw [weighted_zero]
  apply tendsto_tsum_of_dominated_convergence sum
  · intro n
    simpa only [Function.comp_def, survival_zero, Complex.one_re, one_mul] using
      ((Complex.continuous_re.comp (amp n)).continuousAt (x := 0)).tendsto.mul_const (P n)
  · exact Filter.Eventually.of_forall fun t n => term_bound A pos n t

/-- A single nonvacuum mass in an unlabelled positive mixture suffices
to determine whether the full response has a unique critical exponent. -/
theorem weighted_iff (A : Response) {P : ℕ+ → ℝ} (pos : ∀ n, 0 ≤ P n) (sum : Summable P)
    (excited : ∃ n, 0 < energy n ∧ 0 < P n) :
    ContinuousAt (weightedReturn A P) 0 ↔ ∃! s : Conserving, ∀ x ∈ Shares, A.val x = power s.val x := by
  rw [← classification]
  have law := (response_iff A.val).mp A.property
  constructor
  · intro h
    obtain ⟨n,E,p⟩ := excited
    exact ⟨continuous_from_mode A E (mode_continuity A pos sum h p),law⟩
  · exact fun h => return_continuity A h.1 pos sum

#print axioms mode_defect
#print axioms weighted_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
