import GaloisForLFunctions.HTGeometry.FiniteResponseForce
import GaloisForLFunctions.HTGeometry.AtomicMomentHankelSection

/-!
# Polynomial response observables of atomic Hankel data

The moment-sufficiency mechanism of Araújo, arXiv:2609.05560, section 4.1 applies directly
to the corpus's CCM atomic moments and Hankel sections. No positivity or normalization is
needed for these identities: signed source packets satisfy the same response laws.
-/
open scoped BigOperators
open Polynomial Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Every polynomial response is a finite linear combination of existing atomic moments. -/
theorem finiteResponseForce_polynomial_moments {n : ℕ}
    (w z : Fin n → ℝ) (P : ℝ[X]) (x : ℝ) :
    finiteResponseForce (fun u => P.eval u) w z x =
      (P.comp (X - C x)).sum (fun k a => a * RHTower.ccmAtomicMixedMoment w z k) := by
  let Q : ℝ[X] := P.comp (X - C x)
  have heval (i : Fin n) : P.eval (z i - x) = Q.eval (z i) := by
    simp [Q]
  unfold finiteResponseForce
  simp_rw [heval, Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [RHTower.ccmAtomicMixedMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- At the origin, a monomial response reads the corresponding existing atomic moment. -/
theorem finiteResponseForce_power_zero {n : ℕ} (w z : Fin n → ℝ) (k : ℕ) :
    finiteResponseForce (fun u => u ^ k) w z 0 = RHTower.ccmAtomicMixedMoment w z k := by
  simp [finiteResponseForce, RHTower.ccmAtomicMixedMoment]

/-- Affine response sees only mass and the first moment. -/
theorem finiteResponseForce_affine_moments {n : ℕ} (w z : Fin n → ℝ) (a b x : ℝ) :
    finiteResponseForce (fun u => a * u + b) w z x =
      a * RHTower.ccmAtomicMixedMoment w z 1 +
        (b - a * x) * RHTower.ccmAtomicMixedMoment w z 0 := by
  simp only [finiteResponseForce, RHTower.ccmAtomicMixedMoment, pow_one, pow_zero, mul_one,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Quadratic response detects variance information discarded by mean-only compression. -/
theorem finiteResponseForce_quadratic_moments {n : ℕ} (w z : Fin n → ℝ) (x : ℝ) :
    finiteResponseForce (fun u => u ^ 2) w z x =
      RHTower.ccmAtomicMixedMoment w z 2 - 2 * x * RHTower.ccmAtomicMixedMoment w z 1 +
        x ^ 2 * RHTower.ccmAtomicMixedMoment w z 0 := by
  simp only [finiteResponseForce, RHTower.ccmAtomicMixedMoment, pow_one, pow_zero, mul_one,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Cubic response additionally reads the third moment, with an exact triangular expansion. -/
theorem finiteResponseForce_cubic_moments {n : ℕ} (w z : Fin n → ℝ) (x : ℝ) :
    finiteResponseForce (fun u => u ^ 3) w z x =
      RHTower.ccmAtomicMixedMoment w z 3 - 3 * x * RHTower.ccmAtomicMixedMoment w z 2 +
        3 * x ^ 2 * RHTower.ccmAtomicMixedMoment w z 1 -
          x ^ 3 * RHTower.ccmAtomicMixedMoment w z 0 := by
  simp only [finiteResponseForce, RHTower.ccmAtomicMixedMoment, pow_one, pow_zero, mul_one,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- All translated polynomial probes carry exactly the atomic moment sequence. -/
theorem polynomial_response_equivalence_iff_moments {n m : ℕ}
    (w z : Fin n → ℝ) (v t : Fin m → ℝ) :
    (∀ (P : ℝ[X]) (x : ℝ), finiteResponseForce (fun u => P.eval u) w z x =
      finiteResponseForce (fun u => P.eval u) v t x) ↔
      ∀ k, RHTower.ccmAtomicMixedMoment w z k = RHTower.ccmAtomicMixedMoment v t k := by
  constructor
  · intro h k
    simpa [finiteResponseForce, RHTower.ccmAtomicMixedMoment] using h (X ^ k) 0
  · intro h P x
    rw [finiteResponseForce_polynomial_moments, finiteResponseForce_polynomial_moments]
    simp_rw [h]

/-- Squared-polynomial response is exactly the corpus's Hankel quadratic form. -/
theorem finiteResponseForce_squaredPolynomial_hankel {n J : ℕ}
    (w z : Fin n → ℝ) (a : Fin J → ℝ) :
    finiteResponseForce (fun u => (Polynomial.ofFn J a).eval u ^ 2) w z 0 =
      a ⬝ᵥ (atomicHankel w z J *ᵥ a) := by
  rw [dotProduct_mulVec_atomicHankel]
  simp [finiteResponseForce]

/-- Translating the probe translates the polynomial in the same Hankel energy identity. -/
theorem finiteResponseForce_squaredPolynomial_translate {n : ℕ}
    (w z : Fin n → ℝ) (P : ℝ[X]) (x : ℝ) :
    finiteResponseForce (fun u => P.eval u ^ 2) w z x =
      ∑ i, w i * ((P.comp (X - C x)).eval (z i)) ^ 2 := by
  simp [finiteResponseForce]

end
end GaloisForLFunctions.HTGeometry
