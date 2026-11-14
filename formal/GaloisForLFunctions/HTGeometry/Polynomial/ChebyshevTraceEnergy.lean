import GaloisForLFunctions.HTGeometry.Polynomial.ChebyshevDifferential
import GaloisForLFunctions.HTGeometry.ChebyshevMomentTrace
import GaloisForLFunctions.HTGeometry.ChebyshevSpectralPacketTrace

/-!
# Differential energy of moment and spectral trace kernels

Multiplying a shifted Chebyshev polynomial by `X` introduces a removable
singularity in its logarithmic derivative. The expression `X P' - P`
removes it polynomially and yields an identity valid even at `X = 0`.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

/-- Exact energy of the kernel on the unit interval, valid on the whole field. -/
theorem chebyshev_unitInterval_energy {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    X * (1 - X) * ((Chebyshev.T K (n : ℤ)).comp (1 - 2 * X)).derivative ^ 2 +
      (n : K[X]) ^ 2 * (Chebyshev.T K (n : ℤ)).comp (1 - 2 * X) ^ 2 =
        (n : K[X]) ^ 2 := by
  have h := chebyshev_affine_differential_energy (n : ℤ) (-2 : K) 1
  have ha : C (-2 : K) * X + C 1 = (1 - 2 * X : K[X]) := by
    simp only [C_neg, C_ofNat, C_1]
    ring
  rw [ha] at h
  simp only [C_neg, C_ofNat, Int.cast_natCast] at h
  apply mul_left_cancel₀ (show (4 : K[X]) ≠ 0 by norm_num)
  linear_combination -h

/-- The trace factor `X` can be absorbed without dividing at the origin. -/
theorem chebyshev_weightedTrace_energy {K : Type*} [Field K] [CharZero K] (n : ℕ) :
    (1 - X) * (X * (X * (Chebyshev.T K (n : ℤ)).comp (1 - 2 * X)).derivative -
      X * (Chebyshev.T K (n : ℤ)).comp (1 - 2 * X)) ^ 2 +
      (n : K[X]) ^ 2 * X * (X * (Chebyshev.T K (n : ℤ)).comp (1 - 2 * X)) ^ 2 =
        (n : K[X]) ^ 2 * X ^ 3 := by
  simp only [derivative_mul, derivative_X, one_mul]
  linear_combination X ^ 3 * chebyshev_unitInterval_energy (K := K) n

/-- Complex spectral trace polynomials obey the same polynomial energy identity. -/
theorem complexChebyshevTracePolynomial_energy (n : ℕ) :
    (1 - X) * (X * (complexChebyshevTracePolynomial n).derivative -
      complexChebyshevTracePolynomial n) ^ 2 +
      (n : ℂ[X]) ^ 2 * X * complexChebyshevTracePolynomial n ^ 2 =
        (n : ℂ[X]) ^ 2 * X ^ 3 :=
  chebyshev_weightedTrace_energy n

/-- Arbitrary complex spectral packets inherit the exact energy balance by summing nodes. -/
theorem packetChebyshevTrace_differential_energy {r : ℕ}
    (lam w : Fin r → ℂ) (n : ℕ) :
    (∑ j, w j * ((1 - lam j) *
      (lam j * (complexChebyshevTracePolynomial n).derivative.eval (lam j) -
        (complexChebyshevTracePolynomial n).eval (lam j)) ^ 2 +
      (n : ℂ) ^ 2 * lam j * (complexChebyshevTracePolynomial n).eval (lam j) ^ 2)) =
        (n : ℂ) ^ 2 * packetMoment lam w 3 := by
  rw [packetMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h := congrArg (Polynomial.eval (lam j)) (complexChebyshevTracePolynomial_energy n)
  simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_one, eval_X, eval_natCast] at h
  rw [h]
  ring

end GaloisForLFunctions.HTGeometry

namespace HTGeometry

/-- The real moment kernel satisfies the exact first-derivative energy law. -/
theorem chebyshevTraceKernelPolynomial_energy (n : ℕ) :
    X * (1 - X) * (chebyshevTraceKernelPolynomial n).derivative ^ 2 +
      (n : ℝ[X]) ^ 2 * chebyshevTraceKernelPolynomial n ^ 2 = (n : ℝ[X]) ^ 2 :=
  GaloisForLFunctions.HTGeometry.chebyshev_unitInterval_energy n

/-- The real trace polynomial has a nonsingular weighted energy at the origin. -/
theorem chebyshevTracePolynomial_energy (n : ℕ) :
    (1 - X) * (X * (chebyshevTracePolynomial n).derivative - chebyshevTracePolynomial n) ^ 2 +
      (n : ℝ[X]) ^ 2 * X * chebyshevTracePolynomial n ^ 2 = (n : ℝ[X]) ^ 2 * X ^ 3 :=
  GaloisForLFunctions.HTGeometry.chebyshev_weightedTrace_energy n

end HTGeometry
