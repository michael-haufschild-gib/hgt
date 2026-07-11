import GaloisForLFunctions.PrimeSuperspaceWickAnisotropy
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Finite prime-boundary Dickman/Wick cumulant

The radial and vertical finite-prime energies are the real and imaginary-axis restrictions of one
entire cumulant.  Exponentiating its imaginary-axis restriction gives a strictly positive,
therefore zero-free, characteristic function.  On paper this is the characteristic function of
the symmetric Poisson prime-jump field whose Lévy measures converge to `du / |u|`.
-/

noncomputable section

namespace RHTower

/-- The finite symmetric prime-jump cumulant. -/
def primeBoundaryWickCumulant (N : ℕ) (z : ℂ) : ℂ :=
  ∑ p ∈ Nat.primesLE N,
    2 * (Complex.cosh (z * (Real.log p : ℂ)) - 1) / p

/-- Hyperbolic/cosh form of radial reflected energy in the symmetric coordinate `r=2ε`. -/
theorem primeClockCutoffEnergy_half_eq_cosh (N : ℕ) (r : ℝ) :
    primeClockCutoffEnergy N (r / 2) =
      ∑ p ∈ Nat.primesLE N, 2 * (Real.cosh (r * Real.log p) - 1) / p := by
  rw [primeClockCutoffEnergy_eq_sinh]
  apply Finset.sum_congr rfl
  intro p hp
  let x : ℝ := r * Real.log p / 2
  have hx : r * Real.log p = 2 * x := by dsimp [x]; ring
  have hxhalf : r / 2 * Real.log p = x := by dsimp [x]; ring
  have htrig : 4 * Real.sinh x ^ 2 = 2 * (Real.cosh (2 * x) - 1) := by
    rw [Real.cosh_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  rw [hxhalf, hx, htrig]

/-- The real axis of the Wick cumulant is radial reflected energy. -/
theorem primeBoundaryWickCumulant_ofReal (N : ℕ) (r : ℝ) :
    primeBoundaryWickCumulant N (r : ℂ) =
      (primeClockCutoffEnergy N (r / 2) : ℂ) := by
  rw [primeClockCutoffEnergy_half_eq_cosh, primeBoundaryWickCumulant]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  rfl

/-- The imaginary axis of the Wick cumulant is minus vertical clock energy. -/
theorem primeBoundaryWickCumulant_mul_I (N : ℕ) (h : ℝ) :
    primeBoundaryWickCumulant N ((h : ℂ) * Complex.I) =
      -(primeClockVerticalEnergy N h : ℂ) := by
  rw [primeClockVerticalEnergy_eq_cos, primeBoundaryWickCumulant]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show ((h : ℂ) * Complex.I) * Complex.log p =
      ((h : ℂ) * Complex.log p) * Complex.I by ring,
    Complex.cosh_mul_I]
  ring

/-- The finite characteristic function of the symmetric prime-jump field. -/
def primeBoundaryCharacteristic (N : ℕ) (h : ℝ) : ℂ :=
  Complex.exp (primeBoundaryWickCumulant N ((h : ℂ) * Complex.I))

theorem primeBoundaryCharacteristic_eq_exp_neg_verticalEnergy (N : ℕ) (h : ℝ) :
    primeBoundaryCharacteristic N h =
      Complex.exp (-(primeClockVerticalEnergy N h : ℂ)) := by
  rw [primeBoundaryCharacteristic, primeBoundaryWickCumulant_mul_I]

/-- The finite characteristic function is a positive real number. -/
theorem primeBoundaryCharacteristic_eq_ofReal_exp (N : ℕ) (h : ℝ) :
    primeBoundaryCharacteristic N h =
      (Real.exp (-primeClockVerticalEnergy N h) : ℂ) := by
  rw [primeBoundaryCharacteristic_eq_exp_neg_verticalEnergy, Complex.ofReal_exp]
  congr 1
  push_cast

theorem primeBoundaryCharacteristic_re_pos (N : ℕ) (h : ℝ) :
    0 < (primeBoundaryCharacteristic N h).re := by
  rw [primeBoundaryCharacteristic_eq_ofReal_exp]
  exact Real.exp_pos _

/-- No finite prime-boundary Poisson field can create an interference node. -/
theorem primeBoundaryCharacteristic_ne_zero (N : ℕ) (h : ℝ) :
    primeBoundaryCharacteristic N h ≠ 0 := by
  rw [primeBoundaryCharacteristic_eq_exp_neg_verticalEnergy]
  exact Complex.exp_ne_zero _

end RHTower
