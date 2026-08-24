import GaloisForLFunctions.RHTower.SymmetricShiftFiniteEuler
import GaloisForLFunctions.HTGeometry.CayleyGeneralizedSchurCongruence

/-!
# Shifted-Xi Euler prime factors at the real anchor

This leaf formalizes each scalar prime factor in the Euler-region quotient.
At a purely imaginary sampling node its value is real and strictly greater
than one, so its literal upper-half-plane Schur diagonal is strictly negative.
-/

open Complex Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Prime-local quotient `(1-p^(-s₊))/(1-p^(-s₋))` in the upper-half-plane
sampling coordinate. -/
def eulerXiPrimeShiftFactor (p : Nat.Primes) (omega : ℝ) (z : ℂ) : ℂ :=
  finiteEulerLocalFactor p (1 / 2 + (omega : ℂ) - z * I) /
    finiteEulerLocalFactor p (1 / 2 - (omega : ℂ) - z * I)

/-- Real form of a prime-local quotient at the anchor `z = i y`. -/
def eulerXiPrimeAnchorFactor (p : Nat.Primes) (omega y : ℝ) : ℝ :=
  (1 - Real.exp (-(1 / 2 + omega + y) * Real.log p)) /
    (1 - Real.exp (-(1 / 2 - omega + y) * Real.log p))

/-- The complex prime-local quotient at `i y` is exactly its real avatar. -/
theorem eulerXiPrimeShiftFactor_mul_I
    (p : Nat.Primes) (omega y : ℝ) :
    eulerXiPrimeShiftFactor p omega ((y : ℂ) * I) =
      (eulerXiPrimeAnchorFactor p omega y : ℝ) := by
  rw [eulerXiPrimeShiftFactor, eulerXiPrimeAnchorFactor,
    finiteEulerLocalFactor, finiteEulerLocalFactor]
  have hyI : (y : ℂ) * I * I = -(y : ℂ) := by
    rw [mul_assoc, I_mul_I]
    ring
  rw [hyI]
  rw [show -(1 / 2 + (omega : ℂ) - -(y : ℂ)) * Real.log p =
      ((-(1 / 2 + omega + y) * Real.log p : ℝ) : ℂ) by
        push_cast
        ring,
    show -(1 / 2 - (omega : ℂ) - -(y : ℂ)) * Real.log p =
      ((-(1 / 2 - omega + y) * Real.log p : ℝ) : ℂ) by
        push_cast
        ring,
    ← Complex.ofReal_exp, ← Complex.ofReal_exp]
  push_cast
  rfl

/-- Every prime-local factor is strictly larger than one at every real anchor
in the Euler sampling region. -/
theorem one_lt_eulerXiPrimeAnchorFactor
    (p : Nat.Primes) {omega y : ℝ}
    (homega : 0 < omega) (hy : 1 / 2 + omega < y) :
    1 < eulerXiPrimeAnchorFactor p omega y := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hlog : 0 < Real.log p := Real.log_pos hp
  let ap := Real.exp (-(1 / 2 + omega + y) * Real.log p)
  let am := Real.exp (-(1 / 2 - omega + y) * Real.log p)
  have hminus_exp_lt_one : am < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    apply Real.exp_lt_exp.mpr
    have : 0 < 1 / 2 - omega + y := by linarith
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr this) hlog
  have haplus_lt_hminus : ap < am := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  change 1 < (1 - ap) / (1 - am)
  rw [one_lt_div₀ (sub_pos.mpr hminus_exp_lt_one)]
  linarith

/-- Complex-coordinate form of prime-local real-anchor expansion. -/
theorem one_lt_re_eulerXiPrimeShiftFactor_mul_I
    (p : Nat.Primes) {omega y : ℝ}
    (homega : 0 < omega) (hy : 1 / 2 + omega < y) :
    1 < (eulerXiPrimeShiftFactor p omega ((y : ℂ) * I)).re := by
  rw [eulerXiPrimeShiftFactor_mul_I]
  exact one_lt_eulerXiPrimeAnchorFactor p homega hy

/-- Every prime-local Schur carrier has a strictly negative diagonal at every
real anchor in the Euler sampling region. -/
theorem re_upperHalfPlaneSchurKernel_eulerXiPrimeShiftFactor_mul_I_neg
    (p : Nat.Primes) {omega y : ℝ}
    (homega : 0 < omega) (hy : 1 / 2 + omega < y) :
    (upperHalfPlaneSchurKernel (eulerXiPrimeShiftFactor p omega)
      ((y : ℂ) * I) ((y : ℂ) * I)).re < 0 := by
  have hypos : 0 < y := by linarith
  have htheta := one_lt_eulerXiPrimeAnchorFactor p homega hy
  rw [upperHalfPlaneSchurKernel, eulerXiPrimeShiftFactor_mul_I]
  simp only [Complex.conj_ofReal]
  have hden : (y : ℂ) * I - conj ((y : ℂ) * I) =
      (2 * y : ℝ) * I := by
    apply Complex.ext <;> simp
    ring
  rw [hden]
  have h2yr : (2 * y : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) hypos.ne'
  have hIdiv : I / ((2 * y : ℝ) * I) = ((2 * y : ℝ)⁻¹ : ℝ) := by
    have hinvCast : (((2 * y : ℝ)⁻¹ : ℝ) : ℂ) =
        (((2 * y : ℝ) : ℂ))⁻¹ := by norm_cast
    rw [hinvCast]
    field_simp [h2yr]
  rw [hIdiv]
  norm_num [Complex.mul_re]
  have hsquare : 1 < (eulerXiPrimeAnchorFactor p omega y) ^ 2 := by
    nlinarith [sq_nonneg (eulerXiPrimeAnchorFactor p omega y - 1)]
  exact mul_neg_of_pos_of_neg
    (mul_pos (inv_pos.mpr hypos) (by norm_num)) (by nlinarith)

end
end RHTower
