import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Tomography

/-! # The ordinary symmetric tensor lift picks out the real square-root exponent -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay

open ModeCapacities SquareTest

theorem half_power {x : ℝ} (hx : 0<x) : power (1/2) x=(Real.sqrt x:ℂ) := by
  rw [power,Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx,Complex.ofReal_exp,Complex.ofReal_mul]
  congr 1
  push_cast
  ring

/-- The symmetric lift of the actual two elementary amplitudes includes
the square root of the number of labelled routings. -/
def symmetricLift (a b : ℂ) (j k : ℕ) :=
  (Real.sqrt ((j+k).choose j):ℂ)*a^j*b^k

def lifts (s : ℂ) (u v : ℕ → ℝ) (p : Nat.Primes) :=
  let entry (j k : ℕ) := kernel s u v (rayState p j) (rayState p k)
  ∀ j k, entry j k=symmetricLift (entry 1 0) (entry 0 1) j k

private theorem coefficients_iff (s : ℂ) :
    (∀ j k : ℕ, power s ((j+k).choose j:ℝ)=(Real.sqrt ((j+k).choose j):ℂ)) ↔ s=1/2 := by
  constructor
  · intro h
    apply power_refs_injective
    change (power s 2,power s 3)=(power (1/2) 2,power (1/2) 3)
    rw [half_power (by norm_num : 0<(2:ℝ)),half_power (by norm_num : 0<(3:ℝ))]
    exact Prod.ext (by simpa [Nat.choose_succ_succ] using h 1 1) (by simpa [Nat.choose_succ_succ] using h 1 2)
  · rintro rfl j k
    exact half_power (Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right j k)))

theorem lifts_iff (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    lifts s u v p ↔ s=1/2 := by
  have left := amplitude_ray s hu hv p 1 0
  have right := amplitude_ray s hu hv p 0 1
  norm_num [unit_power] at left right
  rw [←coefficients_iff]
  constructor
  · intro h j k
    have H := h j k
    dsimp only at H
    rw [left,right,symmetricLift,amplitude_ray s hu hv p j k] at H
    exact mul_right_cancel₀ (pow_ne_zero _ (power_ne s _)) (mul_right_cancel₀ (pow_ne_zero _ (power_ne s _)) H)
  · intro h j k
    dsimp only
    rw [left,right,symmetricLift,amplitude_ray s hu hv p j k,h]

/-- An uncalibrated coherent detector recognizes the symmetric lift
through two dimensionless intrashell readings. -/
theorem measured_lift (D : Detector) (s : ℂ) :
    readings (detected D s)=(2,(Real.sqrt 3:ℂ)) ↔ lifts s D.u.val D.v.val D.prime := by
  rw [lifts_iff s D.u.property D.v.property,←same_readings_iff D D s (1/2)]
  have ref := coherent_readings D (1/2)
  rw [half_power (by norm_num : 0<(4:ℝ)),half_power (by norm_num : 0<(3:ℝ))] at ref
  norm_num at ref
  rw [ref]

#print axioms lifts_iff
#print axioms measured_lift

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay
