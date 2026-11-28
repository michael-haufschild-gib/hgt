import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Readings

/-! # Measuring a complex exponent with uncalibrated coherent detectors -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay

open ModeCapacities SquareTest

/-- Known occupations and unknown capacities, complex channel gains and
per-particle output efficiencies. All observed gains are nonzero. -/
structure Detector where
  u : {g : ℕ → ℝ // positive g}
  v : {g : ℕ → ℝ // positive g}
  prime : Nat.Primes
  gain : ℕ → ℂˣ
  left : ℂˣ
  right : ℂˣ

def detected (D : Detector) (s : ℂ) (j k : ℕ) :=
  (D.gain (j+k):ℂ)*(D.left:ℂ)^j*(D.right:ℂ)^k*
    kernel s D.u.val D.v.val (rayState D.prime j) (rayState D.prime k)

def readings (r : ℕ → ℕ → ℂ) := ((r 1 1)^2/(r 2 0*r 0 2),(r 1 2)^2/(r 0 3*r 2 1))

private theorem four (z : ℂ) : power z 4=(power z 2)^2 := by
  simpa only [show (2:ℝ)^2=4 by norm_num] using power_nat z (by norm_num : 0<(2:ℝ)) 2

/-- The second and third shells retain only the binomial multiplicities
in their projective ratios. -/
theorem coherent_readings (D : Detector) (s : ℂ) : readings (detected D s)=(power s 4,power s 3) := by
  let a := (D.left:ℂ)*power s (share D.u.val D.v.val D.prime)
  let b := (D.right:ℂ)*power s (share D.v.val D.u.val D.prime)
  have nzA : a≠0 := mul_ne_zero D.left.ne_zero (power_ne _ _)
  have nzB : b≠0 := mul_ne_zero D.right.ne_zero (power_ne _ _)
  have raw (j k : ℕ) : detected D s j k=(D.gain (j+k):ℂ)*power s ((j+k).choose j:ℝ)*a^j*b^k := by
    rw [detected,amplitude_ray s D.u.property D.v.property]
    simp only [a,b,mul_pow]
    ring
  apply Prod.ext
  · change (detected D s 1 1)^2/(detected D s 2 0*detected D s 0 2)=power s 4
    simp only [raw,four]
    norm_num [Nat.choose_succ_succ,unit_power]
    field_simp [(D.gain 2).ne_zero,nzA,nzB]
  · change (detected D s 1 2)^2/(detected D s 0 3*detected D s 2 1)=power s 3
    simp only [raw]
    norm_num [Nat.choose_succ_succ,unit_power]
    field_simp [(D.gain 3).ne_zero,nzA,nzB,power_ne s 3]

private theorem signal_injective : Function.Injective (fun s : ℂ => (power s 4,power s 3)) := by
  intro z w H
  have h₂ : power z 4=power w 4 := congrArg Prod.fst H
  have h₃ : power z 3=power w 3 := congrArg Prod.snd H
  rw [four,four] at h₂
  have double (v : ℂ) (x : ℝ) : power (2*v) x=(power v x)^2 := by rw [two_mul,power_add,sq]
  apply mul_left_cancel₀ (by norm_num : (2:ℂ)≠0)
  apply power_refs_injective
  change (power (2*z) 2,power (2*z) 3)=(power (2*w) 2,power (2*w) 3)
  simp only [double,h₂,h₃]

/-- The complete complex exponent is identifiable even when both experiments
use different primes, capacities and uncalibrated detectors. -/
theorem same_readings_iff (D E : Detector) (s w : ℂ) :
    readings (detected D s)=readings (detected E w) ↔ s=w := by
  rw [coherent_readings,coherent_readings]
  exact signal_injective.eq_iff

#print axioms coherent_readings
#print axioms same_readings_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay
