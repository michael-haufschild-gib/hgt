/-
# Zeros of the entire determinant are limits of reciprocal block eigenvalues

The entire regularized determinant of a Hilbert–Schmidt kernel is the uniform-on-discs limit of the
regularized determinants of its finite blocks, and those vanish exactly at the reciprocals of the
block eigenvalues.  Hurwitz's theorem therefore turns a zero of the limit into eigenvalues of all
but finitely many blocks, converging to its reciprocal.

Main result: `eventually_exists_blockEigenvalue_near`.
-/
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantLimit
import GaloisForLFunctions.HTGeometry.FiniteDeterminantZeros
import GaloisForLFunctions.HTGeometry.HurwitzZeroLimit

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Metric Filter Matrix

variable {ι : Type*} [DecidableEq ι]

/-- **A zero of the entire determinant is a limit of reciprocal block eigenvalues.**  For every
punctured disc around a zero `z₀` on whose boundary the determinant does not vanish, all but
finitely many finite blocks have an eigenvalue `z⁻¹` with `z` in that disc. -/
theorem eventually_exists_blockEigenvalue_near {K : ι × ι → ℂ} (hK : IsHS K) {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hrz : r < ‖z₀‖) (hz₀ : entireDet2 K z₀ = 0)
    (hne : ∀ z ∈ sphere z₀ r, entireDet2 K z ≠ 0) :
    ∀ᶠ s : Finset ι in atTop, ∃ z ∈ ball z₀ r, ∃ v : ↥s → ℂ, v ≠ 0 ∧
      (blockMatrix K s) *ᵥ v = z⁻¹ • v := by
  have hsub : closedBall z₀ r ⊆ closedBall (0 : ℂ) (‖z₀‖ + r) := by
    refine closedBall_subset_closedBall' ?_
    rw [Complex.dist_eq, sub_zero]
    linarith
  have hρ : 0 < ‖z₀‖ + r := by
    have : (0 : ℝ) ≤ ‖z₀‖ := norm_nonneg z₀
    linarith
  have huniform : TendstoUniformlyOn
      (fun (s : Finset ι) (z : ℂ) => finiteDet2 (-(blockMatrix K s)) z)
      (entireDet2 K) atTop (closedBall z₀ r) :=
    (tendstoUniformlyOn_finiteDet2_entireDet2 hK hρ).mono hsub
  have hF : ∀ s : Finset ι,
      DiffContOnCl ℂ (fun z => finiteDet2 (-(blockMatrix K s)) z) (ball z₀ r) :=
    fun s => (differentiable_finiteDet2 (-(blockMatrix K s))).diffContOnCl
  have hcont : ContinuousOn (entireDet2 K) (sphere z₀ r) :=
    (differentiable_entireDet2 hK).continuous.continuousOn
  filter_upwards [eventually_exists_zero_of_tendstoUniformlyOn hr hF hcont huniform hz₀ hne]
    with s hs
  obtain ⟨z, hzmem, hzero⟩ := hs
  have hz0 : z ≠ 0 := by
    intro h
    have hd : ‖z - z₀‖ < r := by
      rw [← Complex.dist_eq]; exact mem_ball.mp hzmem
    rw [h] at hd
    rw [zero_sub, norm_neg] at hd
    linarith
  refine ⟨z, hzmem, ?_⟩
  obtain ⟨v, hv0, hv⟩ := (finiteDet2_eq_zero_iff_exists_eigenvector _ hz0).mp hzero
  refine ⟨v, hv0, ?_⟩
  have hneg : (-(blockMatrix K s)) *ᵥ v = -((blockMatrix K s) *ᵥ v) := by
    ext i; simp [Matrix.neg_mulVec]
  rw [hneg] at hv
  have : (blockMatrix K s) *ᵥ v = z⁻¹ • v := by
    have hh : -((blockMatrix K s) *ᵥ v) = (-z⁻¹) • v := hv
    have := congrArg (fun w : ↥s → ℂ => -w) hh
    simpa [neg_smul] using this
  exact this

end GaloisForLFunctions.HTGeometry
