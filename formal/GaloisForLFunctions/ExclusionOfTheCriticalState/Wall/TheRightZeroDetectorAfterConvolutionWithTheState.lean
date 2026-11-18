import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.LogarithmicPrimeRowFactorization
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PositiveComparisonForThePrimeZeroDetector
import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheCriticalStateSeesALeftZero

/-!
# The right-zero detector after convolution with the state

The profile multiplies the leading exponential by its Laplace value at the
reflected zero. The remaining part stays bounded uniformly in the cutoff.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ExceptionalLayerTheory ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory

private theorem normalized_detector_error {a : ArithmeticFunction ℝ} {w : ℝ → ℂ} {ρ d : ℂ} {C : ℝ}
    (hb : ∀ x : ℝ, 1 ≤ x → ‖arithmeticKernel a w x - (x:ℂ)^ρ*d‖ ≤ C*Real.sqrt x)
    {v : ℝ} (hv : 0 ≤ v) :
    ‖logDilationKernel a w v-cexp ((ρ-1/2)*v)*d‖ ≤ C := by
  have hx := hb (Real.exp v) (Real.one_le_exp_iff.mpr hv)
  have hrt : Real.sqrt (Real.exp v) = Real.exp (v/2) := (Real.exp_half v).symm
  have hp : ((Real.exp v:ℝ):ℂ)^ρ = cexp ((v:ℂ)*ρ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
      ← Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
  have he : ((Real.exp (-v/2):ℝ):ℂ)*cexp ((v:ℂ)*ρ) = cexp ((ρ-1/2)*v) := by
    rw [Complex.ofReal_exp,← Complex.exp_add]; push_cast; congr 1; ring
  rw [logDilationKernel,← he,mul_assoc,← mul_sub,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [hp,hrt] at hx
  apply (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le).trans_eq
  rw [mul_left_comm,← Real.exp_add,show -v/2+v/2=0 by ring,Real.exp_zero,mul_one]

/-- Convolution with a negative-supported profile preserves a bounded
exponential remainder at every positive time, including its complex phase. -/
theorem confined_profile_preserves_detector_main_term {Φ : ℝ → ℝ} (hΦ : Integrable Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {z d : ℂ}
    (hz : Integrable fun u : ℝ => cexp (-z*u)*(Φ u:ℂ)) {K : ℝ → ℂ} {C T : ℝ}
    (hT : 0 ≤ T) (hK : Integrable fun u : ℝ => (Φ u:ℂ)*K (T-u))
    (hbound : ∀ v : ℝ, 0 ≤ v → ‖K v-cexp (z*v)*d‖ ≤ C) :
    ‖(∫ u, (Φ u:ℂ)*K (T-u)) - cexp (z*T)*d*negativeHalfLineLaplace (cx Φ) (-z)‖ ≤
      C*(∫ u, |Φ u|) := by
  let A := cexp (z*T)*d
  change ‖(∫ u, (Φ u:ℂ)*K (T-u)) - A*(∫ u : ℝ, cexp (-z*u)*(Φ u:ℂ))‖ ≤ _
  rw [← integral_const_mul,← integral_sub hK (hz.const_mul A),← integral_const_mul]
  apply norm_integral_le_integral_norm.trans
  apply integral_mono (hK.sub (hz.const_mul A)).norm (hΦ.abs.const_mul C)
  intro u
  by_cases hu : 0 ≤ u
  · simp [hs _ hu]
  have hmain : A*(cexp (-z*u)*(Φ u:ℂ)) = (Φ u:ℂ)*(cexp (z*((T-u:ℝ):ℂ))*d) := by
    dsimp only [A]
    rw [Complex.ofReal_sub,mul_sub,Complex.exp_sub]
    rw [neg_mul,Complex.exp_neg]
    ring
  rw [hmain,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_comm C]
  exact mul_le_mul_of_nonneg_left (hbound _ (sub_nonneg.2 ((le_of_not_ge hu).trans hT))) (abs_nonneg _)

#print axioms confined_profile_preserves_detector_main_term
end GaloisForLFunctions.ExclusionOfTheCriticalState
