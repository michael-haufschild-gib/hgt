import GaloisForLFunctions.RHTower.Sieve.TotientMoebiusNormalisation
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Signed-totient inversion in the moving-cusp theta source

The cofinal reflected Euler-deletion source has arithmetic coefficient
`A(n) = ∑_{d∣n} μ(d)d`.  This module proves that `A` is the Dirichlet-convolution
inverse of Euler's positive totient `φ`.  Their pointwise source-level
reconstruction and the resulting one-unit spectral shear are established
on paper in `theta-prime-deletion-moving-cusp-dual-source.md`.

The convolution identity is unconditional; it does not assert that the
totient operator is bounded on the cofinal theta history carrier.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace RHTower

/-- Pointwise multiplication by the arithmetic identity commutes with
Dirichlet convolution, because the identity is completely multiplicative. -/
theorem pmul_id_mul (f g : ArithmeticFunction ℝ) :
    (f.pmul ArithmeticFunction.id) * (g.pmul ArithmeticFunction.id) =
      (f * g).pmul ArithmeticFunction.id := by
  ext n
  simp only [mul_apply, pmul_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ab hab
  have hprod : ab.1 * ab.2 = n := (Nat.mem_divisorsAntidiagonal.mp hab).1
  simp only [ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
  have hcast : (ab.1 : ℝ) * (ab.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast hprod
  calc
    f ab.1 * (ab.1 : ℝ) * (g ab.2 * (ab.2 : ℝ)) =
        f ab.1 * g ab.2 * ((ab.1 : ℝ) * (ab.2 : ℝ)) := by ring
    _ = _ := by rw [hcast]

/-- The Möbius coefficient weighted by its index. -/
def weightedMobiusAF : ArithmeticFunction ℝ :=
  (μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.id

/-- Signed-totient coefficient of the cofinal moving-cusp source. -/
def signedTotientAF : ArithmeticFunction ℝ :=
  weightedMobiusAF * (ζ : ArithmeticFunction ℝ)

/-- The signed coefficient is exactly `A(n)=∑_{d∣n} μ(d)d`. -/
theorem signedTotientAF_apply (n : ℕ) :
    signedTotientAF n =
      ∑ a ∈ n.divisors, ((μ a : ℤ) : ℝ) * (a : ℝ) := by
  simp only [signedTotientAF, ArithmeticFunction.coe_mul_zeta_apply,
    weightedMobiusAF, ArithmeticFunction.pmul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply]

/-- Euler's totient, expressed as Möbius convolution with the identity. -/
def eulerTotientAF : ArithmeticFunction ℝ :=
  (μ : ArithmeticFunction ℝ) * ArithmeticFunction.id

/-- Weighted Möbius is the Dirichlet inverse of the identity. -/
theorem weightedMobiusAF_mul_id :
    weightedMobiusAF * (ArithmeticFunction.id : ArithmeticFunction ℝ) = 1 := by
  calc
    weightedMobiusAF * (ArithmeticFunction.id : ArithmeticFunction ℝ) =
        ((μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)).pmul
          ArithmeticFunction.id := by
            simpa [weightedMobiusAF, ArithmeticFunction.pmul_zeta] using
              pmul_id_mul (μ : ArithmeticFunction ℝ) (ζ : ArithmeticFunction ℝ)
    _ = 1 := by
      ext n
      by_cases hn : n = 1
      · subst n
        simp [pmul_apply]
      · simp [pmul_apply, hn]

/-- Signed totient and positive totient are exact Dirichlet-convolution inverses. -/
theorem signedTotientAF_mul_eulerTotientAF :
    signedTotientAF * eulerTotientAF = 1 := by
  rw [signedTotientAF, eulerTotientAF]
  calc
    (weightedMobiusAF * (ζ : ArithmeticFunction ℝ)) *
        ((μ : ArithmeticFunction ℝ) * ArithmeticFunction.id) =
        (weightedMobiusAF * ArithmeticFunction.id) *
          ((ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) := by
            ac_rfl
    _ = 1 := by simp [weightedMobiusAF_mul_id]

/-- The inverse coefficient is Euler's ordinary nonnegative totient. -/
theorem eulerTotientAF_apply (n : ℕ) (hn : 0 < n) :
    eulerTotientAF n = (Nat.totient n : ℝ) := by
  rw [eulerTotientAF, ArithmeticFunction.mul_apply]
  simp only [ArithmeticFunction.intCoe_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply]
  rw [Nat.sum_divisorsAntidiagonal (f := fun a b =>
    ((μ a : ℤ) : ℝ) * (b : ℝ))]
  exact (Sieve.totient_eq_sum_moebius_mul n hn).symm

end RHTower
