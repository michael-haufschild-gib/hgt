import GaloisForLFunctions.HTGeometry.QuadraticResponseHierarchy
import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum
/-!
# Hankel memory of the cavity coefficient hierarchy

The quadratic recurrence extracted from arXiv:2608.14343 has at most two
independent Hankel columns at every window size. Its adjacent minors equal
`-b^(n+1)`. In particular, a positive quadratic coefficient gives a negative
moment minor; finite recurrence memory is not positive moment geometry.
-/

open scoped BigOperators Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section
/-- Every coefficient window has Hankel rank at most two, uniformly in its size. -/
theorem quadraticResponseCoeff_hankel_rank_le_two (a b : ℂ) (N : ℕ) :
    (seqHankel (quadraticResponseCoeff a b) N).rank ≤ 2 := by
  let p : Polynomial ℂ := Polynomial.C 1 * Polynomial.X ^ (2 : ℕ) +
    Polynomial.C a * Polynomial.X + Polynomial.C b
  have hd : p.natDegree = 2 := Polynomial.natDegree_quadratic (by simp)
  have hp : p ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hd
    contradiction
  have hr : ∀ n, ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k * quadraticResponseCoeff a b (n + k) = 0 := by
    intro n
    rw [hd]
    simp [p, Finset.sum_range_succ, quadraticResponseCoeff_add_two, Polynomial.coeff_X]
    ring
  simpa only [hd] using rank_seqHankel_le_of_recurrence hp hr N
/-- The adjacent real Hankel determinant has an exact sign, independent of the linear coefficient. -/
theorem quadraticResponseCoeff_real_hankel_minor (a b : ℝ) (n : ℕ) :
    Matrix.det !![quadraticResponseCoeff a b n, quadraticResponseCoeff a b (n + 1);
      quadraticResponseCoeff a b (n + 1), quadraticResponseCoeff a b (n + 2)] =
      -b ^ (n + 1) := by
  rw [Matrix.det_fin_two]
  change quadraticResponseCoeff a b n * quadraticResponseCoeff a b (n + 2) -
    quadraticResponseCoeff a b (n + 1) * quadraticResponseCoeff a b (n + 1) = _
  linear_combination -quadraticResponseCoeff_cassini a b n
/-- Positive quadratic response gives strictly negative adjacent moment minors at every depth. -/
theorem quadraticResponseCoeff_positive_quadratic_negative_minor (a r : ℝ) (n : ℕ) :
    Matrix.det !![quadraticResponseCoeff a (r ^ (2 : ℕ) + 1) n,
      quadraticResponseCoeff a (r ^ (2 : ℕ) + 1) (n + 1);
      quadraticResponseCoeff a (r ^ (2 : ℕ) + 1) (n + 1),
      quadraticResponseCoeff a (r ^ (2 : ℕ) + 1) (n + 2)] < 0 := by
  rw [quadraticResponseCoeff_real_hankel_minor]
  have h : 0 < (r ^ (2 : ℕ) + 1) ^ (n + 1) := by positivity
  linarith
end
end GaloisForLFunctions.HTGeometry
