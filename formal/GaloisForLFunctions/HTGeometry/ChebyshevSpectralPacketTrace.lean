import GaloisForLFunctions.HTGeometry.ConstitutiveThreeRealizationPacket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

open Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- First-kind Chebyshev probe, shifted to the node interval `[0,1]`. -/
def complexChebyshevTracePolynomial (n : ℕ) : Polynomial ℂ :=
  X * (Chebyshev.T ℂ (n : ℤ)).comp (1 - 2 * X)

/-- Polynomial trace of a finite complex spectral packet. -/
def packetChebyshevTrace {r : ℕ} (lam w : Fin r → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ (complexChebyshevTracePolynomial n).support,
    (complexChebyshevTracePolynomial n).coeff k * packetMoment lam w k

theorem packetChebyshevTrace_eq_nodes {r : ℕ}
    (lam w : Fin r → ℂ) (n : ℕ) :
    packetChebyshevTrace lam w n =
      ∑ j : Fin r, w j * lam j *
        (Chebyshev.T ℂ (n : ℤ)).eval (1 - 2 * lam j) := by
  classical
  rw [packetChebyshevTrace]
  simp only [packetMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    ∑ k ∈ (complexChebyshevTracePolynomial n).support,
        (complexChebyshevTracePolynomial n).coeff k * (w j * lam j ^ k) =
      w j * ∑ k ∈ (complexChebyshevTracePolynomial n).support,
        (complexChebyshevTracePolynomial n).coeff k * lam j ^ k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
    _ = w j * (complexChebyshevTracePolynomial n).eval (lam j) := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    _ = _ := by simp [complexChebyshevTracePolynomial]; ring

end

end GaloisForLFunctions.HTGeometry
