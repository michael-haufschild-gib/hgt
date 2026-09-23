import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedUnitEigenchains

/-! Sharp complex-time growth of the genuine entire bounded derivative-chain evolution.
Actual unit rational eigenchains attain the left-half-plane bound and approach the imaginary endpoints. -/
open Complex ComplexConjugate MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance fokasLenellsCausalBoundedSharpGrowthInst1 : CompleteSpace (hardyL2ᗮ) := hardyL2.isClosed_orthogonal.completeSpace_coe
local instance fokasLenellsCausalBoundedSharpGrowthInst2 : CompleteSpace causalBoundedChain := causalBoundedChain_complete
local instance fokasLenellsCausalBoundedSharpGrowthInst3 : NormedAddCommGroup causalBoundedChain := causalBoundedChain.normedAddCommGroup
local instance fokasLenellsCausalBoundedSharpGrowthInst4 : NormedSpace ℂ causalBoundedChain := causalBoundedChain.normedSpace
local instance fokasLenellsCausalBoundedSharpGrowthInst5 : NormedRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  ContinuousLinearMap.toNormedRing
local instance fokasLenellsCausalBoundedSharpGrowthInst6 : TopologicalSpace (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  (inferInstance : NormedAddCommGroup
    (causalBoundedChain →L[ℂ] causalBoundedChain)).toUniformSpace.toTopologicalSpace
local instance fokasLenellsCausalBoundedSharpGrowthInst7 : IsTopologicalRing (causalBoundedChain →L[ℂ] causalBoundedChain) :=
  NonUnitalSeminormedRing.toIsTopologicalRing

private theorem lower_of_rate_limit (z : ℂ) (ω : ℝ) (w : ℂ)
    (hlim : Tendsto (fun b : ℝ => (causalUnitBoundaryRate b ω).val) atBot (𝓝 w)) :
    Real.exp ((z*w).re) ≤ ‖causalBoundedChainExponential z‖ := by
  have hp : Tendsto (fun b : ℝ => z*(causalUnitBoundaryRate b ω).val) atBot (𝓝 (z*w)) :=
    (tendsto_const_nhds (x := z)).mul hlim
  have hr := (Complex.continuous_re.tendsto (z*w)).comp hp
  have he := (Real.continuous_exp.tendsto ((z*w).re)).comp hr
  exact le_of_tendsto he (Filter.Eventually.of_forall (fun b =>
    causalBoundedChainExponential_unit_lower b ω z))

/-- Actual rational endpoint limits force growth at least exponential in imaginary time. -/
theorem causalBoundedChainExponential_imaginary_lower (z : ℂ) :
    Real.exp |z.im| ≤ ‖causalBoundedChainExponential z‖ := by
  have hp := lower_of_rate_limit z 1 I causalUnitBoundaryRate_tendsto_pos
  have hn := lower_of_rate_limit z (-1) (-I) causalUnitBoundaryRate_tendsto_neg
  have hp' : Real.exp (-z.im) ≤ ‖causalBoundedChainExponential z‖ := by
    simpa only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub] using hp
  have hn' : Real.exp z.im ≤ ‖causalBoundedChainExponential z‖ := by
    simpa only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      neg_zero, mul_zero, mul_neg_one, zero_sub, neg_neg] using hn
  by_cases hi : 0 ≤ z.im
  · simpa only [abs_of_nonneg hi] using hn'
  · simpa only [abs_of_neg (lt_of_not_ge hi)] using hp'

private theorem aligned_unit_rate (z : ℂ) (hz : z.re < 0) :
    (causalUnitBoundaryRate (Real.log (-z.re)) (-z.im)).val = conj z / (‖z‖ : ℂ) := by
  have he : (causalBoundaryRate (Real.log (-z.re)) (-z.im)).val = conj z := by
    apply Complex.ext <;>
      simp only [causalBoundaryRate, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero,
        zero_mul, sub_zero, add_zero, Complex.add_im, Complex.neg_im, neg_zero,
        Complex.mul_im, mul_one, zero_add, Complex.conj_re, Complex.conj_im,
        Real.exp_log (neg_pos.mpr hz), neg_neg]
  have hn : ‖(causalBoundaryRate (Real.log (-z.re)) (-z.im)).val‖ = ‖z‖ :=
    (congrArg (fun w : ℂ => ‖w‖) he).trans (Complex.norm_conj z)
  exact congrArg₂ (fun x y : ℂ => x/y) he (congrArg Complex.ofReal hn)

private theorem aligned_real_character (z : ℂ) (hz : z.re < 0) :
    (z*(causalUnitBoundaryRate (Real.log (-z.re)) (-z.im)).val).re = ‖z‖ := by
  have hne : z ≠ 0 := by
    intro h
    have he : z.re = 0 := congrArg Complex.re h
    exact (ne_of_lt hz) he
  have hn := norm_ne_zero_iff.mpr hne
  calc
    _ = (z*(conj z / (‖z‖ : ℂ))).re :=
      congrArg (fun w : ℂ => (z*w).re) (aligned_unit_rate z hz)
    _ = (z*conj z).re / ‖z‖ := by rw [← mul_div_assoc, Complex.div_ofReal_re]
    _ = ‖z‖^(2 : ℕ) / ‖z‖ := by rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    _ = ‖z‖ * (‖z‖/‖z‖) := by rw [pow_two, mul_div_assoc]
    _ = ‖z‖ := by rw [div_self hn, mul_one]

private theorem left_growth_lower (z : ℂ) (hz : z.re < 0) :
    Real.exp ‖z‖ ≤ ‖causalBoundedChainExponential z‖ :=
  (congrArg Real.exp (aligned_real_character z hz)).symm.trans_le
    (causalBoundedChainExponential_unit_lower (Real.log (-z.re)) (-z.im) z)

/-- Exact operator growth in every complex-time direction, proved by genuine rational tests. -/
theorem norm_causalBoundedChainExponential (z : ℂ) :
    ‖causalBoundedChainExponential z‖ = Real.exp (causalBoundedGrowthExponent z) := by
  apply le_antisymm (norm_causalBoundedChainExponential_le_growth z)
  by_cases hz : 0 ≤ z.re
  · simpa only [causalBoundedGrowthExponent, if_pos hz] using
      causalBoundedChainExponential_imaginary_lower z
  · simpa only [causalBoundedGrowthExponent, if_neg hz] using
      left_growth_lower z (lt_of_not_ge hz)

/-- The sharp exponent is the Euclidean length after clipping the positive real component. -/
theorem causalBoundedGrowthExponent_eq_sqrt (z : ℂ) :
    causalBoundedGrowthExponent z = Real.sqrt ((min z.re 0)^(2 : ℕ) + z.im^(2 : ℕ)) := by
  by_cases hz : 0 ≤ z.re
  · simp only [causalBoundedGrowthExponent, if_pos hz, min_eq_right hz,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, Real.sqrt_sq_eq_abs]
  · simp only [causalBoundedGrowthExponent, if_neg hz, min_eq_left (le_of_lt (lt_of_not_ge hz)),
      Complex.norm_def, Complex.normSq_apply, pow_two]

/-- Closed sharp complex-time norm formula in elementary real coordinates. -/
theorem norm_causalBoundedChainExponential_eq_sqrt (z : ℂ) :
    ‖causalBoundedChainExponential z‖ = Real.exp (Real.sqrt ((min z.re 0)^(2 : ℕ) + z.im^(2 : ℕ))) :=
  (norm_causalBoundedChainExponential z).trans (congrArg Real.exp (causalBoundedGrowthExponent_eq_sqrt z))

/-- Real time is contractive forward and has exact exponential norm growth backward. -/
theorem norm_causalBoundedChainExponential_ofReal (r : ℝ) :
    ‖causalBoundedChainExponential (r : ℂ)‖ = Real.exp (max (-r) 0) := by
  have he : causalBoundedGrowthExponent (r : ℂ) = max (-r) 0 := by
    change (if 0 ≤ (r : ℂ).re then |(r : ℂ).im| else ‖(r : ℂ)‖) = _
    simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero]
    by_cases hr : 0 ≤ r
    · rw [if_pos hr, max_eq_right (neg_nonpos.mpr hr)]
    · rw [if_neg hr, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge hr),
        max_eq_left (neg_nonneg.mpr (le_of_lt (lt_of_not_ge hr)))]
  exact (norm_causalBoundedChainExponential (r : ℂ)).trans (congrArg Real.exp he)

/-- Pure imaginary time has exact two-sided exponential growth. -/
theorem norm_causalBoundedChainExponential_imaginary (r : ℝ) :
    ‖causalBoundedChainExponential ((r : ℂ)*I)‖ = Real.exp |r| := by
  have he : causalBoundedGrowthExponent ((r : ℂ)*I) = |r| := by
    simp only [causalBoundedGrowthExponent, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero,
      add_zero, if_pos (le_refl (0 : ℝ))]
  exact (norm_causalBoundedChainExponential ((r : ℂ)*I)).trans (congrArg Real.exp he)

/-- No complex time is a strict contraction in the genuine bounded-chain operator norm. -/
theorem one_le_norm_causalBoundedChainExponential (z : ℂ) :
    1 ≤ ‖causalBoundedChainExponential z‖ :=
  (Real.one_le_exp (abs_nonneg z.im)).trans (causalBoundedChainExponential_imaginary_lower z)

end
end RHTower.FokasLenells
