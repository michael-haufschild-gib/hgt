import GaloisForLFunctions.RHTower.GammaCoPoissonIntervalFactorialBridge
import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse

/-!
# Burnol prime dilation and co-Poisson divided quotient

Exact half-density prime character, its removable finite-log divided difference, the zeta-zero
resolvent identity valid on and off confluence, and its FE--Schwarz seam normalization.  The
finite-log cell is the existing Gamma/co-Poisson interval source, including all confluent jets.
-/

open Complex

namespace RHTower

noncomputable section

def burnolPrimeCharacter (p : ℝ) (s : ℂ) : ℂ := (p : ℂ) ^ (s - 1 / 2)

theorem burnolPrimeCharacter_eq_exp (p : ℝ) (hp : 0 < p) (s : ℂ) :
    burnolPrimeCharacter p s = Complex.exp ((s - 1 / 2) * Real.log p) := by
  rw [burnolPrimeCharacter, Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne')]
  rw [Complex.ofReal_log hp.le]
  congr 1
  ring

theorem burnolPrimeCharacter_sub_mul_dslope
    (zeta : ℂ → ℂ) (rho s : ℂ) (hzeta : zeta rho = 0) :
    (burnolPrimeCharacter p s - burnolPrimeCharacter p rho) * dslope zeta rho s =
      zeta s * dslope (burnolPrimeCharacter p) rho s := by
  rcases eq_or_ne s rho with rfl | hsr
  · simp [hzeta]
  · rw [dslope_of_ne _ hsr, dslope_of_ne _ hsr, slope_def_module,
      slope_def_module, hzeta]
    simp only [sub_zero, smul_eq_mul]
    field_simp [sub_ne_zero.mpr hsr]

theorem dslope_burnolPrimeCharacter_eq_gammaCoPoissonIntervalCell
    (p : ℝ) (hp : 0 < p) (rho s : ℂ) :
    dslope (burnolPrimeCharacter p) rho s =
      gammaCoPoissonIntervalCell (Real.log p) s rho := by
  have hfun : burnolPrimeCharacter p = fun u : ℂ =>
      Complex.exp (((Real.log p : ℝ) : ℂ) * (u - 1 / 2)) := by
    funext u
    rw [burnolPrimeCharacter_eq_exp p hp]
    congr 1
    ring
  rw [hfun]
  by_cases hsr : s = rho
  · subst s
    rw [dslope_same, gammaCoPoissonIntervalCell_self]
    rw [← iteratedDeriv_one,
      show (fun u : ℂ => Complex.exp ((Real.log p : ℂ) * (u - 1 / 2))) =
        fun u : ℂ => Complex.exp (-(Real.log p / 2)) *
          Complex.exp ((Real.log p : ℂ) * u) by
        funext u
        rw [← Complex.exp_add]
        congr 1
        ring,
      iteratedDeriv_const_mul_field,
      GaloisForLFunctions.iteratedDeriv_exp_linear]
    simp only [pow_one]
    rw [show Complex.exp ((rho - 1 / 2) * (Real.log p : ℂ)) =
      Complex.exp (-(Real.log p / 2)) *
        Complex.exp ((Real.log p : ℂ) * rho) by
          rw [← Complex.exp_add]
          congr 1
          ring]
    ring
  · rw [dslope_of_ne _ hsr, slope_def_module,
      gammaCoPoissonIntervalCell_eq_dividedDifference _ _ _ hsr]
    simp only [smul_eq_mul]
    rw [show (rho - 1 / 2) * (Real.log p : ℂ) =
      (Real.log p : ℂ) * (rho - 1 / 2) by ring,
      show (s - 1 / 2) * (Real.log p : ℂ) =
      (Real.log p : ℂ) * (s - 1 / 2) by ring]
    rw [div_eq_mul_inv]
    ring

theorem burnolPrime_resolvent_quotient_identity
    (zeta : ℂ → ℂ) (p : ℝ) (hp : 0 < p) (rho s : ℂ)
    (hzeta : zeta rho = 0) :
    (burnolPrimeCharacter p s - burnolPrimeCharacter p rho) * dslope zeta rho s =
      zeta s * gammaCoPoissonIntervalCell (Real.log p) s rho := by
  rw [burnolPrimeCharacter_sub_mul_dslope zeta rho s hzeta,
    dslope_burnolPrimeCharacter_eq_gammaCoPoissonIntervalCell p hp rho s]

theorem orbitwiseScaleSeamCharge_eq_cpow_burnolPrimeCharacter_reflection
    (p : ℝ) (hp : 0 < p) (rho : ℂ) :
    orbitwiseScaleSeamCharge p rho =
      (Real.log p : ℂ) * (p : ℂ) ^ (-(1 / 2 : ℂ)) *
        (burnolPrimeCharacter p (1 - star rho) - burnolPrimeCharacter p rho) := by
  rw [orbitwiseScaleSeamCharge, burnolPrimeCharacter, burnolPrimeCharacter]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  calc
    (Real.log p : ℂ) *
        ((p : ℂ) ^ (-(starRingEnd ℂ) rho) - (p : ℂ) ^ (-(1 - rho))) =
      (Real.log p : ℂ) *
        ((p : ℂ) ^ (-(1 / 2 : ℂ)) * (p : ℂ) ^ (1 - star rho - 1 / 2) -
          (p : ℂ) ^ (-(1 / 2 : ℂ)) * (p : ℂ) ^ (rho - 1 / 2)) := by
            rw [← Complex.cpow_add _ _ hpC, ← Complex.cpow_add _ _ hpC]
            simp only [Complex.star_def]
            ring
    _ = (Real.log p : ℂ) * (p : ℂ) ^ (-(1 / 2 : ℂ)) *
        ((p : ℂ) ^ (1 - star rho - 1 / 2) - (p : ℂ) ^ (rho - 1 / 2)) := by ring

theorem cpow_neg_half_eq_inv_sqrt (p : ℝ) (hp : 0 < p) :
    (p : ℂ) ^ (-(1 / 2 : ℂ)) = (Real.sqrt p : ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hp.le]
  norm_num

theorem orbitwiseScaleSeamCharge_eq_burnolPrimeCharacter_reflection
    (p : ℝ) (hp : 0 < p) (rho : ℂ) :
    orbitwiseScaleSeamCharge p rho =
      (Real.log p / Real.sqrt p : ℂ) *
        (burnolPrimeCharacter p (1 - star rho) - burnolPrimeCharacter p rho) := by
  rw [orbitwiseScaleSeamCharge_eq_cpow_burnolPrimeCharacter_reflection p hp rho,
    cpow_neg_half_eq_inv_sqrt p hp]
  ring

end
end RHTower
