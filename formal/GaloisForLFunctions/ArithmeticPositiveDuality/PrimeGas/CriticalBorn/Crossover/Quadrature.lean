import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.TiltDerivative
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover.Scale

/-! # Uniform comparison of a moving elementary tilt with its continuum correction -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover

open Filter Real
open GaloisForLFunctions.RestrictedFactorizationCalculus
open scoped Topology

/-- Uniform for both signs and all real tilts at a fixed cutoff. -/
theorem uniform_correction_error {N : ℕ} (hN : 2≤N) (hδ : coordinateRadius (log N)≤1) (w : ℝ) :
    |tiltCorrection w N-_root_.RHTower.logIntegralCompare w| ≤ coordinateRadius (log N)*
      (|w| * (2+3*|w|)*exp (2*|w|)) := by
  let f := fun q : ℝ => tiltCorrection q N - _root_.RHTower.logIntegralCompare q
  let δ := coordinateRadius (log N)
  have lN := log_pos (show (1:ℝ)<N by exact_mod_cast (by omega : 1<N))
  have h0 : 0≤δ := div_nonneg (add_nonneg _root_.RHTower.Sieve.mertensBlockGapConst_nonneg
    (log_nonneg (by norm_num))) lN.le
  have hd (q : ℝ) := (correction_deriv hN q).sub (_root_.RHTower.hasDerivAt_logIntegralCompare q)
  have B (q : ℝ) (h : q∈Set.Icc (-|w|) |w|) :
      ‖primeCoordinateSum (log N) (fun v => exp (q*v)) N-_root_.RHTower.logIntegralKernel q‖ ≤
      δ*((2+3*|w|)*exp (2*|w|)) := by
    rw [Real.norm_eq_abs]
    apply (derivative_error hN hδ q).trans
    have qle := abs_le.mpr h
    apply mul_le_mul_of_nonneg_left _ h0
    exact mul_le_mul (by linarith only [qle]) (exp_le_exp.mpr (by linarith only [qle]))
      (exp_pos _).le (by positivity)
  have est := (convex_Icc (-|w|) |w|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (fun q _ => (hd q).hasDerivWithinAt) B
    (show (0:ℝ)∈Set.Icc (-|w|) |w| from ⟨neg_nonpos.mpr (abs_nonneg _),abs_nonneg _⟩)
    (abs_le.mp (le_refl |w|))
  have zero : f 0 = 0 := by simp [f,tiltCorrection,_root_.RHTower.logIntegralCompare]
  rw [zero,sub_zero,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs] at est
  exact est.trans_eq (by dsimp [δ]; ring)

/-- Actual cutoff-dependent displacement in units of the maximum energy. -/
def drift (c : ℝ) (N : ℕ) := displacement c (log (log N))

theorem logEnergy_growth : Tendsto (fun N : ℕ => log (log N)) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem radius_small : Tendsto (fun N : ℕ => coordinateRadius (log N)) atTop (𝓝 0) :=
  (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop _

private theorem remainder_tends {c : ℝ} (q : ℕ → ℝ) (w : ∀ N, |q N|= |drift c N|) :
    Tendsto (fun N => tiltCorrection (q N) N - _root_.RHTower.logIntegralCompare (q N)) atTop (𝓝 0) := by
  have scale := (quadrature_scale c).comp logEnergy_growth
  let C := _root_.RHTower.Sieve.mertensBlockGapConst + log 2
  have upper := scale.const_mul C
  rw [mul_zero] at upper
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop 2,radius_small.eventually_le_const (by norm_num : (0:ℝ)<1)]
      with N hN hδ
    have h := uniform_correction_error hN hδ (q N)
    rw [w] at h
    rw [Real.norm_eq_abs]
    refine h.trans_eq ?_
    change C/log N*(|drift c N| * (2+3*|drift c N|)*exp (2*|drift c N|)) =
      C*(|drift c N| * (2+3*|drift c N|)*exp (2*|drift c N|)/exp (log (log N)))
    rw [exp_log (log_pos (by exact_mod_cast (by omega : 1<N)))]
    ring

theorem positive_remainder (c : ℝ) :
    Tendsto (fun N => tiltCorrection (drift c N) N - _root_.RHTower.logIntegralCompare (drift c N)) atTop
      (𝓝 0) := remainder_tends (drift c) (fun _ => rfl)

theorem negative_remainder (c : ℝ) :
    Tendsto (fun N => tiltCorrection (-(drift c N)) N - _root_.RHTower.logIntegralCompare (-(drift c N)))
      atTop (𝓝 0) := remainder_tends (fun N => -(drift c N)) (fun _ => abs_neg _)

#print axioms uniform_correction_error
#print axioms positive_remainder
#print axioms negative_remainder

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Crossover
