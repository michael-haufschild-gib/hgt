import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Conditioning.Law

/-! # The characteristic exponent contributed by a band of marked primes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands

open Filter Topology Set MeasureTheory ProbabilityTheory _root_.RHTower _root_.RHTower.BAGTrace

/-- The intensity per unit of scaled prime energy. -/
def density (v : ℝ) := Real.exp (-v)/v

def rate (c d : ℝ) := expIntegralOne c-expIntegralOne d

def bandExponent (c d : ℝ) (z : ℂ) :=
  ∫ v in c..d, (density v:ℂ)*(Complex.exp (z*(v:ℂ))-1)

theorem rate_pos {c d : ℝ} (hc : 0 < c) (hcd : c < d) : 0 < rate c d :=
  sub_pos.mpr (expIntegralOne_strictAntiOn hc (hc.trans hcd) hcd)

theorem rate_integral {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    rate c d = ∫ v in Ioc c d, density v := expIntegralOne_sub hc hcd

/-- Changing scale turns the entire Euler exponent into an integral up to the physical cutoff. -/
private theorem scaled_primitive {c : ℝ} (hc : 0 < c) (u : ℂ) :
    criticalEulerExponent ((c:ℂ)*u) = ∫ v in (0:ℝ)..c, criticalEulerProfile u v := by
  have h (v : ℝ) : criticalEulerProfile ((c:ℂ)*u) v = c • criticalEulerProfile u (c*v) := by
    simp only [criticalEulerProfile,Complex.real_smul,Complex.ofReal_mul]
    ring_nf
  rw [criticalEulerExponent,funext h,intervalIntegral.integral_smul,
    intervalIntegral.integral_comp_mul_left (criticalEulerProfile u) hc.ne',mul_zero,mul_one,
    smul_smul,mul_inv_cancel₀ hc.ne',one_smul]

private def profileDifference (z : ℂ) (v : ℝ) :=
  criticalEulerProfile (z-1) v-criticalEulerProfile (-1) v

private theorem profile_continuous (z : ℂ) : Continuous (profileDifference z) :=
  (criticalEulerProfile_continuous _).sub (criticalEulerProfile_continuous _)

private theorem cutoff_exp {c : ℝ} (hc : 0 < c) (z : ℂ) :
    limitTransform c z = Complex.exp (∫ v in (0:ℝ)..c, profileDifference z v) := by
  change limitTransform c z = Complex.exp (∫ v in (0:ℝ)..c, criticalEulerProfile (z-1) v-criticalEulerProfile (-1) v)
  rw [limitTransform,criticalEulerCarrier,criticalEulerCarrier,← Complex.exp_sub,
    show -(c:ℂ) = (c:ℂ)*(-1) by ring,scaled_primitive hc,scaled_primitive hc,
    intervalIntegral.integral_sub ((criticalEulerProfile_continuous _).intervalIntegrable ..)
      ((criticalEulerProfile_continuous _).intervalIntegrable ..)]

private theorem difference_eq {v : ℝ} (hv : 0 < v) (z : ℂ) :
    profileDifference z v = (density v:ℂ)*(Complex.exp (z*(v:ℂ))-1) := by
  have h : Complex.exp ((z-1)*(v:ℂ)) = Complex.exp (-(v:ℂ))*Complex.exp (z*(v:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hv.ne')
  rw [profileDifference,mul_sub,criticalEulerProfile_mul,criticalEulerProfile_mul,h,neg_one_mul,
    density,Complex.ofReal_div,Complex.ofReal_exp,Complex.ofReal_neg]
  field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  ring

/-- Adding a disjoint prime band adds precisely its compensated exponential integral. -/
theorem factor_transform {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (z : ℂ) :
    limitTransform d z = limitTransform c z*Complex.exp (bandExponent c d z) := by
  have hband : (∫ v in c..d, profileDifference z v) = bandExponent c d z := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hcd] at hv
    exact difference_eq (hc.trans_le hv.1) z
  rw [cutoff_exp (hc.trans_le hcd),cutoff_exp hc,← hband,← Complex.exp_add,
    intervalIntegral.integral_add_adjacent_intervals ((profile_continuous z).intervalIntegrable ..)
      ((profile_continuous z).intervalIntegrable ..)]

theorem transform_ne_zero (c : ℝ) (z : ℂ) : limitTransform c z ≠ 0 :=
  div_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

#print axioms rate_pos
#print axioms rate_integral
#print axioms factor_transform
#print axioms transform_ne_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands
