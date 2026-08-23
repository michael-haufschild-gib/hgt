import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Rank-one algebra of the polarized additive-heat finite part

Once the analytic finite-part calculation supplies the kernel
`ζ(s) * conj (ζ(w))`, its finite-dimensional polarization is exactly the
Gram form of one scalar value functional.  This file formalizes that
unconditional finite algebra only; it does not assume or encode the missing
polylogarithmic boundary expansion.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open scoped BigOperators

/-- A finite outer-product Gram form is the squared norm of its scalar
feature sum. -/
theorem finite_complex_rankOne_gram
    {ι : Type*} (S : Finset ι) (c z : ι → ℂ) :
    (∑ i ∈ S, ∑ j ∈ S, star (c i) * c j * z j * star (z i)) =
      ((‖∑ i ∈ S, c i * z i‖ ^ 2 : ℝ) : ℂ) := by
  calc
    ∑ i ∈ S, ∑ j ∈ S, star (c i) * c j * z j * star (z i) =
        ∑ i ∈ S, star (c i * z i) * ∑ j ∈ S, c j * z j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [star_mul]
          ring
    _ = (∑ i ∈ S, star (c i * z i)) * ∑ j ∈ S, c j * z j := by
          rw [Finset.sum_mul]
    _ = star (∑ i ∈ S, c i * z i) * ∑ j ∈ S, c j * z j := by
          change (∑ i ∈ S, (starRingEnd ℂ) (c i * z i)) * ∑ j ∈ S, c j * z j =
            (starRingEnd ℂ) (∑ i ∈ S, c i * z i) * ∑ j ∈ S, c j * z j
          rw [← map_sum]
    _ = ((‖∑ i ∈ S, c i * z i‖ ^ 2 : ℝ) : ℂ) := by
          rw [mul_comm]
          change (∑ i ∈ S, c i * z i) *
            (starRingEnd ℂ) (∑ i ∈ S, c i * z i) = _
          rw [Complex.mul_conj, ← Complex.sq_norm]

/-- The zeta-value finite-part kernel is a rank-one Gram form on every finite
test family. -/
theorem finite_riemannZeta_value_rankOne_gram
    {ι : Type*} (S : Finset ι) (c s : ι → ℂ) :
    (∑ i ∈ S, ∑ j ∈ S,
      star (c i) * c j * riemannZeta (s j) * star (riemannZeta (s i))) =
      ((‖∑ i ∈ S, c i * riemannZeta (s i)‖ ^ 2 : ℝ) : ℂ) := by
  simpa using finite_complex_rankOne_gram S c (fun i => riemannZeta (s i))

end GaloisForLFunctions.RHTower

end
