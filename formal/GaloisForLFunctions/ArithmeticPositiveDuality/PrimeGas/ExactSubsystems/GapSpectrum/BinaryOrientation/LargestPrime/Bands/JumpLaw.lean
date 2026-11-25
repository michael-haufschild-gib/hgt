import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Exponent
import GaloisForLFunctions.HTGeometry.CharacteristicFunctionPositiveDefinite
import GaloisForLFunctions.RHTower.LiClockThetaSignedGammaCoupling

/-! # The limiting compound Poisson energy of one prime band -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace
open scoped ENNReal
open GaloisForLFunctions.HTGeometry

/-- The unnormalized jump intensity on the scaled prime interval. -/
def jumpMeasure (c d : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc c d)).withDensity fun v => ENNReal.ofReal (density v)

def jumpLaw (c d : ℝ) : Measure ℝ := (ENNReal.ofReal (rate c d))⁻¹ • jumpMeasure c d

theorem jump_mass {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    jumpMeasure c d univ = ENNReal.ofReal (rate c d) := by
  rw [jumpMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,rate_integral hc hcd]
  apply (ofReal_integral_eq_lintegral_ofReal
    ((integrableOn_exp_neg_div_Ioi hc).mono_set Ioc_subset_Ioi_self) ?_).symm
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioc (a := c) (b := d))] with v hv
  exact (div_pos (Real.exp_pos _) (hc.trans hv.1)).le

theorem jump_probability {c d : ℝ} (hc : 0 < c) (hcd : c < d) : IsProbabilityMeasure (jumpLaw c d) :=
  isProbabilityMeasure_inv_ofReal_smul _ (rate_pos hc hcd) (jump_mass hc hcd.le)

/-- The full probability law, including the possibility of zero occupied jumps. -/
def increment (c d : ℝ) (hc : 0 < c) (hcd : c < d) : ProbabilityMeasure ℝ := by
  letI := jump_probability hc hcd
  exact ⟨compoundPoisson (rate c d) (jumpLaw c d),isProbabilityMeasure_compoundPoisson _
    (rate_pos hc hcd).le _⟩

theorem jump_integral {c d : ℝ} (hc : 0 < c) (hcd : c < d) (f : ℝ → ℂ) :
    (∫ v, f v ∂jumpLaw c d) = (rate c d:ℂ)⁻¹*(∫ v in Ioc c d, (density v:ℂ)*f v) := by
  rw [jumpLaw,integral_smul_measure,ENNReal.toReal_inv,ENNReal.toReal_ofReal (rate_pos hc hcd).le,
    Complex.real_smul,Complex.ofReal_inv,jumpMeasure]
  have hm : Measurable density := (Real.measurable_exp.comp measurable_neg).div measurable_id
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal (by simp)]
  apply congrArg ((rate c d:ℂ)⁻¹*·)
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) (measurableSet_Ioc (a := c) (b := d))] with v hv
  rw [ENNReal.toReal_ofReal (show 0 ≤ density v from (div_pos (Real.exp_pos _) (hc.trans hv.1)).le),Complex.real_smul]

theorem charFun_increment {c d : ℝ} (hc : 0 < c) (hcd : c < d) (t : ℝ) :
    charFun (increment c d hc hcd : Measure ℝ) t = Complex.exp (bandExponent c d ((t:ℂ)*Complex.I)) := by
  letI := jump_probability hc hcd
  let e := fun v : ℝ => Complex.exp ((t:ℂ)*(v:ℂ)*Complex.I)
  have hi : Integrable e (jumpLaw c d) := by
    refine (integrable_const (1:ℝ)).mono' (by dsimp [e]; fun_prop) (ae_of_all _ fun v => ?_)
    rw [show e v = Complex.exp (((t*v:ℝ):ℂ)*Complex.I) by simp [e],Complex.norm_exp_ofReal_mul_I]
  have hchar : charFun (jumpLaw c d) t-1 = ∫ v, e v-1 ∂jumpLaw c d := by
    rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul,charFun_apply_real]
  change charFun (compoundPoisson _ _) t = _
  rw [charFun_compoundPoisson _ (rate_pos hc hcd).le,hchar,jump_integral hc hcd,← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (rate_pos hc hcd).ne'),one_mul,bandExponent,
    intervalIntegral.integral_of_le hcd.le]
  apply congrArg Complex.exp
  exact setIntegral_congr_fun measurableSet_Ioc fun v _ => by
    dsimp [e]
    rw [mul_right_comm (t:ℂ)]

/-- The band has precisely one atom. All positive jump counts have atomless energy laws. -/
theorem increment_atom {c d : ℝ} (hc : 0 < c) (hcd : c < d) (x : ℝ) :
    (increment c d hc hcd : Measure ℝ) {x} =
      if x = 0 then ENNReal.ofReal (Real.exp (expIntegralOne d-expIntegralOne c)) else 0 := by
  letI := jump_probability hc hcd
  haveI : NullSingletonClass (jumpMeasure c d) := by unfold jumpMeasure; infer_instance
  haveI : NullSingletonClass (jumpLaw c d) := ⟨fun a => by
    rw [jumpLaw,Measure.smul_apply,measure_singleton,smul_zero]⟩
  change compoundPoisson (rate c d) (jumpLaw c d) {x} = _
  rw [compoundPoisson,convPowMixture_singleton,tsum_eq_single 0]
  · simp only [pow_zero,mul_one,Nat.factorial_zero,Nat.cast_one,div_one,convPow,rate,neg_sub]
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx,Ne.symm hx]
  · intro n hn
    haveI := nullSingletonClass_convPow (jumpLaw c d) (Nat.pos_of_ne_zero hn)
    rw [measure_singleton,mul_zero]

/-- Widening the physical aperture convolves its law with independent compound Poisson energy. -/
theorem cutoff_convolution {c d : ℝ} (hc : 0 < c) (hcd : c < d) :
    (cutoffLaw d : Measure ℝ) = (cutoffLaw c : Measure ℝ) ∗ (increment c d hc hcd : Measure ℝ) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv,charFun_cutoffLaw,charFun_cutoffLaw,charFun_increment,factor_transform hc hcd.le]

#print axioms jump_mass
#print axioms jump_probability
#print axioms jump_integral
#print axioms charFun_increment
#print axioms increment_atom
#print axioms cutoff_convolution

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands
