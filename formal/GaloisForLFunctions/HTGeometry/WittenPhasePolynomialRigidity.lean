import GaloisForLFunctions.HTGeometry.WittenAsymptoticExpansion
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare

/-!
# Leading-packet rigidity for exact Witten phase polynomials

Equal Chern--Simons phases must be aggregated before reading an asymptotic degree.  This file
proves the degree-one case: if every aggregated leading coefficient vanishes, the exact formula
collapses to degree zero.  It is the finite algebraic part of the phase-uniqueness mechanism in
the finite-order mapping-torus formulas.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open RHTower

/-- If all equal-phase fibers have zero aggregate linear coefficient, a degree-one exact phase
polynomial is already a degree-zero phase polynomial. -/
theorem finitePhasePolynomial_degreeOne_eq_degreeZero_of_leadingFiberZero
    {ι : Type*} (s : Finset ι) (phase : ι → ℂ) (coefficient : ι → ℕ → ℂ)
    (hfiber : ∀ u ∈ s.image phase,
      finiteExponentialFiberCoefficient s (fun i => coefficient i 1) phase u = 0) :
    finitePhasePolynomial s phase coefficient 1 =
      finitePhasePolynomial s phase coefficient 0 := by
  funext n
  have htop : finiteExponentialPencil s (fun i => coefficient i 1) phase n = 0 := by
    rw [← finiteExponentialPencil_image_eq s (fun i => coefficient i 1) phase n]
    simp only [finiteExponentialPencil]
    apply Finset.sum_eq_zero
    intro u hu
    rw [hfiber u hu, zero_mul]
  simp only [finitePhasePolynomial]
  rw [show (∑ i ∈ s, phase i ^ n *
      ∑ j ∈ Finset.range (1 + 1), coefficient i j * (n : ℂ) ^ j) =
      (∑ i ∈ s, phase i ^ n * coefficient i 0) +
        (n : ℂ) * finiteExponentialPencil s (fun i => coefficient i 1) phase n by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, mul_one, pow_one]
    rw [finiteExponentialPencil, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  rw [htop, mul_zero, add_zero]
  simp

end GaloisForLFunctions.HTGeometry
