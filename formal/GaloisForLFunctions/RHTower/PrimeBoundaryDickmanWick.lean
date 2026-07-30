import GaloisForLFunctions.RHTower.PrimeSuperspaceWickAnisotropy
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

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

/-- The `k`th finite prime-log moment, with the symmetric-Wick normalization. -/
def primeBoundaryLogMoment (N k : ℕ) : ℂ :=
  ∑ p ∈ Nat.primesLE N, 2 * (Real.log p : ℂ) ^ k / p

private theorem iteratedDeriv_cosh_mul_even (a : ℂ) (m : ℕ) :
    iteratedDeriv (2 * m) (fun z : ℂ => Complex.cosh (z * a)) 0 = a ^ (2 * m) := by
  have hfun : (fun z : ℂ => Complex.cosh (z * a)) =
      (fun z : ℂ => Complex.cosh (a * z)) := by
    funext z
    congr 1
    ring
  rw [hfun, iteratedDeriv_comp_const_mul Complex.contDiff_cosh a]
  simp

private theorem iteratedDeriv_cosh_mul_odd (a : ℂ) (m : ℕ) :
    iteratedDeriv (2 * m + 1) (fun z : ℂ => Complex.cosh (z * a)) 0 = 0 := by
  have hfun : (fun z : ℂ => Complex.cosh (z * a)) =
      (fun z : ℂ => Complex.cosh (a * z)) := by
    funext z
    congr 1
    ring
  rw [hfun, iteratedDeriv_comp_const_mul Complex.contDiff_cosh a,
    Complex.iteratedDeriv_odd_cosh]
  simp

private theorem iteratedDeriv_wickTerm_even (a p : ℂ) (m : ℕ) (hm : 0 < m) :
    iteratedDeriv (2 * m)
      (fun z : ℂ => 2 * (Complex.cosh (z * a) - 1) / p) 0 =
      2 * a ^ (2 * m) / p := by
  have hsub :
      iteratedDeriv (2 * m) (fun z : ℂ => Complex.cosh (z * a) - 1) 0 =
        iteratedDeriv (2 * m) (fun z : ℂ => Complex.cosh (z * a)) 0 -
          iteratedDeriv (2 * m) (fun _z : ℂ => (1 : ℂ)) 0 := by
    simpa only [Pi.sub_apply] using!
      iteratedDeriv_sub (n := 2 * m) (x := (0 : ℂ))
        (f := fun z : ℂ => Complex.cosh (z * a))
        (g := fun _z : ℂ => (1 : ℂ)) (by fun_prop) (by fun_prop)
  have hn : 2 * m ≠ 0 := Nat.mul_ne_zero (by norm_num) hm.ne'
  have hconst : iteratedDeriv (2 * m) (fun _z : ℂ => (1 : ℂ)) 0 = 0 := by
    rw [iteratedDeriv_const]
    simp [hn]
  rw [iteratedDeriv_div_const, iteratedDeriv_const_mul_field, hsub,
    iteratedDeriv_cosh_mul_even, hconst, sub_zero]

private theorem iteratedDeriv_wickTerm_odd (a p : ℂ) (m : ℕ) :
    iteratedDeriv (2 * m + 1)
      (fun z : ℂ => 2 * (Complex.cosh (z * a) - 1) / p) 0 = 0 := by
  have hsub :
      iteratedDeriv (2 * m + 1) (fun z : ℂ => Complex.cosh (z * a) - 1) 0 =
        iteratedDeriv (2 * m + 1) (fun z : ℂ => Complex.cosh (z * a)) 0 -
          iteratedDeriv (2 * m + 1) (fun _z : ℂ => (1 : ℂ)) 0 := by
    simpa only [Pi.sub_apply] using!
      iteratedDeriv_sub (n := 2 * m + 1) (x := (0 : ℂ))
        (f := fun z : ℂ => Complex.cosh (z * a))
        (g := fun _z : ℂ => (1 : ℂ)) (by fun_prop) (by fun_prop)
  have hconst : iteratedDeriv (2 * m + 1) (fun _z : ℂ => (1 : ℂ)) 0 = 0 := by
    rw [iteratedDeriv_const]
    simp
  rw [iteratedDeriv_div_const, iteratedDeriv_const_mul_field, hsub,
    iteratedDeriv_cosh_mul_odd, hconst]
  ring

/-- Every positive even cumulant is exactly the corresponding finite prime-log moment. -/
theorem iteratedDeriv_primeBoundaryWickCumulant_even (N m : ℕ) (hm : 0 < m) :
    iteratedDeriv (2 * m) (primeBoundaryWickCumulant N) 0 =
      primeBoundaryLogMoment N (2 * m) := by
  change iteratedDeriv (2 * m)
    (fun z : ℂ => ∑ p ∈ Nat.primesLE N,
      2 * (Complex.cosh (z * (Real.log p : ℂ)) - 1) / p) 0 = _
  rw [primeBoundaryLogMoment]
  rw [iteratedDeriv_fun_sum (fun p hp => by fun_prop)]
  apply Finset.sum_congr rfl
  intro p hp
  exact iteratedDeriv_wickTerm_even (Real.log p : ℂ) p m hm

/-- Every odd cumulant of the symmetric finite prime-jump field vanishes. -/
theorem iteratedDeriv_primeBoundaryWickCumulant_odd (N m : ℕ) :
    iteratedDeriv (2 * m + 1) (primeBoundaryWickCumulant N) 0 = 0 := by
  change iteratedDeriv (2 * m + 1)
    (fun z : ℂ => ∑ p ∈ Nat.primesLE N,
      2 * (Complex.cosh (z * (Real.log p : ℂ)) - 1) / p) 0 = 0
  rw [iteratedDeriv_fun_sum (fun p hp => by fun_prop)]
  apply Finset.sum_eq_zero
  intro p hp
  exact iteratedDeriv_wickTerm_odd (Real.log p : ℂ) p m

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
  exact (Complex.ofReal_neg _).symm

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
