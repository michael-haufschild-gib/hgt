import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Readings
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Isometry

/-! # Measuring the one-particle ladder coefficient on a prime ray -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators

open CoassociativeSplitting ModeCapacities SquareTest CoherentRay

/-- Divide the one-particle branch by the amplitudes for routing the same
particles individually. A state with no particles cannot be lowered. -/
def ladder (K : Kernel) (p : Nat.Primes) : ℕ → ℂ
  | 0 => 0
  | k+1 => K (rayState p 1) (rayState p k) /
      (K (rayState p 1) (rayState p 0) * K (rayState p 0) (rayState p 1) ^ k)

theorem measured (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) (k : ℕ) :
    ladder (kernel s u v) p (k+1) = power s ((k+1:ℕ):ℝ) := by
  have left := amplitude_ray s hu hv p 1 0
  have right := amplitude_ray s hu hv p 0 1
  norm_num [unit_power] at left right
  rw [ladder, left, right, amplitude_ray s hu hv p 1 k, Nat.choose_one_right, Nat.add_comm 1 k, pow_one]
  apply (div_eq_iff (mul_ne_zero (power_ne _ _) (pow_ne_zero _ (power_ne _ _)))).mpr
  rw [mul_assoc]

theorem measured_mass (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v)
    (p : Nat.Primes) (k : ℕ) :
    ‖ladder (kernel s u v) p (k+1)‖ ^ 2 = ((k+1:ℕ):ℝ) ^ (2*s.re) := by
  rw [measured s hu hv, power, Complex.norm_exp, sq, ← Real.exp_add,
    Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.succ_pos k))]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  congr 1
  ring

/-- One increment of the measured number eigenvalue, on the singly
occupied input, already determines the critical exponent condition. -/
theorem first_increment_iff (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    ‖ladder (kernel s u v) p 2‖ ^ 2 - ‖ladder (kernel s u v) p 1‖ ^ 2 = 1 ↔ s.re=1/2 := by
  have second : ‖ladder (kernel s u v) p 2‖ ^ 2 = (2:ℝ)^(2*s.re) := measured_mass s hu hv p 1
  have first : ‖ladder (kernel s u v) p 1‖ ^ 2 = 1 := by
    simpa only [Nat.zero_add, Nat.cast_one, Real.one_rpow] using measured_mass s hu hv p 0
  rw [first,second]
  have inj := (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1:ℝ)<2)).injective
  constructor
  · intro h
    have eqn : (2:ℝ)^(2*s.re) = (2:ℝ)^(1:ℝ) := by rw [Real.rpow_one]; linarith only [h]
    have E := inj eqn
    linarith only [E]
  · intro h
    rw [h, show (2:ℝ)*(1/2)=1 by norm_num, Real.rpow_one]
    norm_num

theorem counts_on_line (s : ℂ) {u v : ℕ → ℝ} (hu : positive u) (hv : positive v)
    (p : Nat.Primes) (line : s.re=1/2) (k : ℕ) : ‖ladder (kernel s u v) p k‖ ^ 2 = (k:ℝ) := by
  cases k with
  | zero => simp [ladder]
  | succ k => rw [measured_mass s hu hv, line, show (2:ℝ)*(1/2)=1 by norm_num, Real.rpow_one]

#print axioms measured
#print axioms first_increment_iff
#print axioms counts_on_line

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators
