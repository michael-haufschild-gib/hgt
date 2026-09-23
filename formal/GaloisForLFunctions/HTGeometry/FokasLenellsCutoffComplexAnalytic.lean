import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffComplexSymbols
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Entire complex-time evolution on the actual L-infinity and L2 carriers

A uniform quadratic scalar-exponential remainder proves differentiation in
the essential-supremum norm. The existing multiplier map transfers this
closed proof to operator norm, at every complex time and derivative order.
-/

open MeasureTheory Complex Filter Topology Set Asymptotics
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem complexSymbol_remainder_bound (a z : ℝ) (τ h : ℂ) (n : ℕ)
    (hh : ‖h‖ * cutoffPhaseBudget a ≤ 1) :
    ‖cutoffComplexSymbol a n (τ+h) z - cutoffComplexSymbol a n τ z -
      h * cutoffComplexSymbol a (n+1) τ z‖ ≤
      (cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a)) *
        cutoffPhaseBudget a ^ 2 * ‖h‖^(2 : ℕ) := by
  let c : ℂ := -(cutoffPhaseFrequency a z : ℂ) * I
  have hc : ‖c‖ ≤ cutoffPhaseBudget a := by
    simpa [c] using abs_cutoffPhaseFrequency_le a z
  have hhc : ‖h*c‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hc (norm_nonneg h)).trans hh
  have he : cutoffComplexSymbol a n (τ+h) z - cutoffComplexSymbol a n τ z -
      h * cutoffComplexSymbol a (n+1) τ z =
      cutoffComplexSymbol a n τ z * (Complex.exp (h*c) - 1 - h*c) := by
    have hh' : -(τ+h) * (cutoffPhaseFrequency a z : ℂ) * I =
        -τ * (cutoffPhaseFrequency a z : ℂ) * I + h*c := by dsimp [c]; ring
    simp only [cutoffComplexSymbol,hh',Complex.exp_add,pow_succ]
    dsimp [c]
    ring
  rw [he,norm_mul]
  calc
    _ ≤ (cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a)) * ‖h*c‖^(2 : ℕ) :=
      mul_le_mul (cutoffComplexSymbol_bound a z τ n) (Complex.norm_exp_sub_one_sub_id_le hhc)
        (norm_nonneg _) (mul_nonneg (pow_nonneg (cutoffPhaseBudget_pos a).le n) (Real.exp_pos _).le)
    _ ≤ (cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a)) * (‖h‖ * cutoffPhaseBudget a)^(2 : ℕ) := by
      apply mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (pow_nonneg (cutoffPhaseBudget_pos a).le n) (Real.exp_pos _).le)
      apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hc (norm_nonneg h)
    _ = _ := by ring

private theorem complexLinfty_remainder_bound (a : ℝ) (τ h : ℂ) (n : ℕ)
    (hh : ‖h‖ * cutoffPhaseBudget a ≤ 1) :
    ‖cutoffComplexLinfty a n (τ+h) - cutoffComplexLinfty a n τ -
      h • cutoffComplexLinfty a (n+1) τ‖ ≤
      (cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a)) *
        cutoffPhaseBudget a ^ 2 * ‖h‖^(2 : ℕ) := by
  rw [Lp.norm_def,eLpNorm_exponent_top]
  apply ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (cutoffPhaseBudget_pos a).le n) (Real.exp_pos _).le)
      (sq_nonneg _)) (sq_nonneg _))
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [Lp.coeFn_sub (cutoffComplexLinfty a n (τ+h) - cutoffComplexLinfty a n τ)
      (h • cutoffComplexLinfty a (n+1) τ),
    Lp.coeFn_sub (cutoffComplexLinfty a n (τ+h)) (cutoffComplexLinfty a n τ),
    Lp.coeFn_smul h (cutoffComplexLinfty a (n+1) τ),
    cutoffComplexLinfty_ae a n (τ+h),cutoffComplexLinfty_ae a n τ,
    cutoffComplexLinfty_ae a (n+1) τ] with z h0 h1 h2 h3 h4 h5
  rw [h0,Pi.sub_apply,h1,Pi.sub_apply,h2,Pi.smul_apply,h3,h4,h5,smul_eq_mul]
  exact complexSymbol_remainder_bound a z τ h n hh

/-- Every actual complex-time L-infinity symbol differentiates in essential-supremum norm. -/
theorem cutoffComplexLinfty_hasDerivAt (a : ℝ) (n : ℕ) (τ : ℂ) :
    HasDerivAt (cutoffComplexLinfty a n) (cutoffComplexLinfty a (n+1) τ) τ := by
  apply hasDerivAt_iff_isLittleO_nhds_zero.mpr
  have ho : (fun h : ℂ => cutoffComplexLinfty a n (τ+h) - cutoffComplexLinfty a n τ -
      h • cutoffComplexLinfty a (n+1) τ) =O[𝓝 0] fun h => ‖h‖^(2 : ℕ) := by
    apply IsBigO.of_bound ((cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a)) * cutoffPhaseBudget a ^ 2)
    have hc : Tendsto (fun h : ℂ => ‖h‖ * cutoffPhaseBudget a) (𝓝 0) (𝓝 0) := by
      have hb : Tendsto (fun h : ℂ => ‖h‖) (𝓝 0) (𝓝 0) := tendsto_norm_zero
      simpa using hb.mul_const (cutoffPhaseBudget a)
    filter_upwards [hc.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with h hh
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using
      complexLinfty_remainder_bound a τ h n hh.le
  exact ho.trans_isLittleO (isLittleO_norm_pow_id (by norm_num : 1 < (2:ℕ)))

/-- The actual symbol curve is entire, at every derivative order. -/
theorem cutoffComplexLinfty_analyticAt (a : ℝ) (n : ℕ) (τ : ℂ) :
    AnalyticAt ℂ (cutoffComplexLinfty a n) τ :=
  (show Differentiable ℂ (cutoffComplexLinfty a n) from fun t =>
    (cutoffComplexLinfty_hasDerivAt a n t).differentiableAt).analyticAt τ

/-- The actual complex-time derivative multiplier on the original Hilbert space. -/
def cutoffComplexOperator (a : ℝ) (n : ℕ) (τ : ℂ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  lineLinftyMultiplier (cutoffComplexLinfty a n τ)

/-- The operator acts by the literal complex-time derivative symbol almost everywhere. -/
theorem cutoffComplexOperator_ae (a : ℝ) (n : ℕ) (τ : ℂ) (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (cutoffComplexOperator a n τ u : ℝ → ℂ) =ᵐ[volume] fun z => cutoffComplexSymbol a n τ z * u z := by
  filter_upwards [lineLinftyMultiplier_ae (cutoffComplexLinfty a n τ) u,
    cutoffComplexLinfty_ae a n τ] with z hz he
  exact hz.trans (by rw [he])

/-- Exact operator norm at every complex time and derivative order. -/
theorem norm_cutoffComplexOperator (a : ℝ) (n : ℕ) (τ : ℂ) :
    ‖cutoffComplexOperator a n τ‖ =
      cutoffPhaseBudget a ^ n * Real.exp (|τ.im| * cutoffPhaseBudget a) := by
  rw [cutoffComplexOperator,norm_lineLinftyMultiplier,norm_cutoffComplexLinfty]

/-- Every complex operator derivative is the next actual multiplier, in operator norm. -/
theorem cutoffComplexOperator_hasDerivAt (a : ℝ) (n : ℕ) (τ : ℂ) :
    HasDerivAt (cutoffComplexOperator a n) (cutoffComplexOperator a (n+1) τ) τ :=
  lineLinftyMultiplier.hasFDerivAt.comp_hasDerivAt τ (cutoffComplexLinfty_hasDerivAt a n τ)

/-- The actual operator family is entire in operator norm at every derivative order. -/
theorem cutoffComplexOperator_analyticAt (a : ℝ) (n : ℕ) (τ : ℂ) :
    AnalyticAt ℂ (cutoffComplexOperator a n) τ :=
  (lineLinftyMultiplier.analyticAt _).comp (cutoffComplexLinfty_analyticAt a n τ)

/-- Restriction to real time recovers the audited original cutoff evolution. -/
theorem cutoffComplexOperator_zero_ofReal (a t : ℝ) :
    cutoffComplexOperator a 0 (t : ℂ) = cutoffEvolution a t := by
  rw [cutoffComplexOperator,cutoffComplexLinfty_zero_ofReal,cutoffEvolution_eq_lineLinftyMultiplier]

/-- Every iterated complex derivative is exactly the corresponding actual multiplier. -/
theorem iteratedDeriv_cutoffComplexOperator (a : ℝ) (n : ℕ) :
    iteratedDeriv n (cutoffComplexOperator a 0) = cutoffComplexOperator a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    exact funext fun τ => (cutoffComplexOperator_hasDerivAt a n τ).deriv

end
end GaloisForLFunctions.HTGeometry.FokasLenells
