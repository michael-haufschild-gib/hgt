import GaloisForLFunctions.RepresentationLifting.Differential.DividedPowerCoefficients
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.SplitIfs

/-!
# Indexed logarithmic calculus in prime characteristic

The logarithmic derivative on divided-power coefficient lists splits by
exponent residue. Its residue projectors are explicit polynomials in the
operator, and division by nonzero residues gives an exact inverse modulo
horizontal sections. Thus the inhomogeneous equation has a solution exactly
when its exponent-zero component vanishes.

This is the one-coordinate logarithmic model of the indexed splitting in
Fersi, *Lifting the local logarithmic Cartier transform modulo p^n*, §4.4.
The statements here concern the constructed coefficient operators over
`ZMod p`; they do not assert the general geometric Cartier equivalence.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.DividedPower

variable (p : ℕ) [Fact p.Prime]

private def coefficientMultiplier (a : ℕ → ZMod p) : Module.End (ZMod p) (ℕ →₀ ZMod p) where
  toFun f := Finsupp.onFinset f.support (fun n => a n * f n) (fun n hn =>
    Finsupp.mem_support_iff.mpr (fun h => hn (by rw [h, mul_zero])))
  map_add' f g := by ext n; exact mul_add _ _ _
  map_smul' c f := by ext n; exact mul_left_comm _ _ _

private theorem coefficientMultiplier_apply (a : ℕ → ZMod p) (f : ℕ →₀ ZMod p) (n : ℕ) :
    coefficientMultiplier p a f n = a n * f n := rfl

/-- The logarithmic derivative acts diagonally on divided-power degree. -/
def logarithmicEuler : Module.End (ZMod p) (ℕ →₀ ZMod p) :=
  coefficientMultiplier p (fun n => n)

@[simp] theorem logarithmicEuler_apply (f : ℕ →₀ ZMod p) (n : ℕ) :
    logarithmicEuler p f n = n * f n := rfl

/-- The residue-class projector for the logarithmic exponent. -/
def cartierResidue (a : ZMod p) : Module.End (ZMod p) (ℕ →₀ ZMod p) :=
  coefficientMultiplier p (fun n => if (n : ZMod p) = a then 1 else 0)

@[simp] theorem cartierResidue_apply (a : ZMod p) (f : ℕ →₀ ZMod p) (n : ℕ) :
    cartierResidue p a f n = if (n : ZMod p) = a then f n else 0 := by
  change (if (n : ZMod p) = a then 1 else 0) * f n = _
  split_ifs <;> simp

/-- Powers of the Euler operator multiply each degree by the corresponding scalar power. -/
theorem logarithmicEuler_pow_apply (k : ℕ) (f : ℕ →₀ ZMod p) (n : ℕ) :
    (logarithmicEuler p ^ k) f n = (n : ZMod p) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, logarithmicEuler_apply, ih, pow_succ']
    exact (mul_assoc _ _ _).symm

/-- The logarithmic derivative has zero restricted p-curvature. -/
theorem logarithmicEuler_pow_char : logarithmicEuler p ^ p = logarithmicEuler p := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  rw [logarithmicEuler_pow_apply, ZMod.pow_card, logarithmicEuler_apply]

/-- All exponent classes are recovered, including the horizontal class. -/
theorem sum_cartierResidue : ∑ a : ZMod p, cartierResidue p a = 1 := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  simp only [LinearMap.sum_apply]
  simp

/-- Distinct exponent projectors annihilate one another. -/
theorem cartierResidue_mul (a b : ZMod p) :
    cartierResidue p a * cartierResidue p b =
      if a = b then cartierResidue p a else 0 := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  by_cases ha : (n : ZMod p) = a <;> by_cases hb : (n : ZMod p) = b <;>
    by_cases hab : a = b <;> simp_all

/-- Each exponent component is an eigenspace of the actual logarithmic operator. -/
theorem logarithmicEuler_cartierResidue (a : ZMod p) :
    logarithmicEuler p * cartierResidue p a = a • cartierResidue p a := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change (n : ZMod p) * cartierResidue p a f n = a * cartierResidue p a f n
  rw [cartierResidue_apply]
  split_ifs with h
  · rw [h]
  · simp

/-- The inverse away from exponent zero, extended by zero on horizontal coefficients. -/
def cartierGreen : Module.End (ZMod p) (ℕ →₀ ZMod p) :=
  coefficientMultiplier p (fun n => (n : ZMod p)⁻¹)

/-- Exact homotopy identity for the logarithmic connection. -/
theorem logarithmicEuler_cartierGreen :
    logarithmicEuler p * cartierGreen p = 1 - cartierResidue p 0 := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change (n : ZMod p) * ((n : ZMod p)⁻¹ * f n) = f n - cartierResidue p 0 f n
  rw [cartierResidue_apply, ← mul_assoc]
  by_cases hn : (n : ZMod p) = 0
  · simp [hn]
  · simp [hn]

#print axioms logarithmicEuler_pow_char
#print axioms sum_cartierResidue
#print axioms cartierResidue_mul
#print axioms logarithmicEuler_cartierGreen

/-- Only exponent-zero coefficients obstruct solving the logarithmic equation. -/
theorem logarithmicEuler_range (g : ℕ →₀ ZMod p) :
    (∃ f, logarithmicEuler p f = g) ↔ cartierResidue p 0 g = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    ext n
    rw [cartierResidue_apply, logarithmicEuler_apply]
    split_ifs with h
    · simp only [h, zero_mul, Finsupp.zero_apply]
    · rfl
  · intro hg
    refine ⟨cartierGreen p g, ?_⟩
    have h := congrArg (fun T : Module.End (ZMod p) (ℕ →₀ ZMod p) => T g)
      (logarithmicEuler_cartierGreen p)
    change logarithmicEuler p (cartierGreen p g) = g - cartierResidue p 0 g at h
    simpa only [hg, sub_zero] using h

/-- Horizontal sections are precisely their exponent-zero component. -/
theorem logarithmicEuler_kernel (f : ℕ →₀ ZMod p) :
    logarithmicEuler p f = 0 ↔ cartierResidue p 0 f = f := by
  constructor
  · intro hf
    ext n
    rw [cartierResidue_apply]
    split_ifs with hn
    · rfl
    · have h := congrArg (fun g : ℕ →₀ ZMod p => g n) hf
      change (n : ZMod p) * f n = 0 at h
      exact ((mul_eq_zero.mp h).resolve_left hn).symm
  · intro hf
    rw [← hf]
    have h := congrArg (fun T : Module.End (ZMod p) (ℕ →₀ ZMod p) => T f)
      (logarithmicEuler_cartierResidue p 0)
    simpa using h

/-- Differentiation lowers logarithmic exponent by one. -/
theorem derivative_logarithmicEuler :
    derivative (ZMod p) (ZMod p) * logarithmicEuler p =
      logarithmicEuler p * derivative (ZMod p) (ZMod p) +
        derivative (ZMod p) (ZMod p) := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change ((n + 1 : ℕ) : ZMod p) * f (n + 1) =
    (n : ZMod p) * f (n + 1) + f (n + 1)
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- No new horizontal sections appear after any positive power of the Euler operator. -/
theorem logarithmicEuler_pow_kernel (k : ℕ) (f : ℕ →₀ ZMod p) :
    (logarithmicEuler p ^ (k + 1)) f = 0 ↔ logarithmicEuler p f = 0 := by
  constructor
  · intro h
    ext n
    have hn := congrArg (fun g : ℕ →₀ ZMod p => g n) h
    rw [logarithmicEuler_pow_apply] at hn
    change (n : ZMod p) ^ (k + 1) * f n = 0 at hn
    change (n : ZMod p) * f n = 0
    rcases mul_eq_zero.mp hn with ha | hf
    · rw [eq_zero_of_pow_eq_zero ha, zero_mul]
    · rw [hf, mul_zero]
  · intro h
    rw [pow_succ, Module.End.mul_apply, h, map_zero]

#print axioms logarithmicEuler_range
#print axioms logarithmicEuler_kernel
#print axioms derivative_logarithmicEuler
#print axioms logarithmicEuler_pow_kernel

private theorem shiftedEuler_pow_apply (a : ZMod p) (k : ℕ)
    (f : ℕ →₀ ZMod p) (n : ℕ) :
    ((logarithmicEuler p - a • 1) ^ k) f n = ((n : ZMod p) - a) ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (n : ZMod p) * (((logarithmicEuler p - a • 1) ^ k) f n) -
      a * (((logarithmicEuler p - a • 1) ^ k) f n) = _
    rw [ih, ← sub_mul, ← mul_assoc, ← pow_succ']

/-- The indexed Cartier projector is a polynomial in the logarithmic connection. -/
theorem cartierResidue_eq_polynomial (a : ZMod p) :
    cartierResidue p a = 1 - (logarithmicEuler p - a • 1) ^ (p - 1) := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change cartierResidue p a f n = f n - ((logarithmicEuler p - a • 1) ^ (p - 1)) f n
  rw [cartierResidue_apply, shiftedEuler_pow_apply, ZMod.pow_card_sub_one]
  by_cases h : (n : ZMod p) = a
  · simp [h]
  · simp [h, sub_ne_zero.mpr h]

#print axioms cartierResidue_eq_polynomial
end GaloisForLFunctions.RepresentationLifting.DividedPower
