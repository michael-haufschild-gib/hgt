/-
# The order of vanishing of the entire determinant is the eventual block eigenvalue count

Putting the chain together.  The block determinants converge to the entire determinant uniformly on
every closed disc; the contour integral of a block determinant's logarithmic derivative counts its
Schur eigenvalues with `−1/tᵢ` inside the circle; and counting Hurwitz says that eventual count is
the order of vanishing of the limit.

Main results:
* `eventually_zeroCount_finiteDet2_eq_analyticOrder` — the abstract instantiation.
* `eventually_schurCount_eq_analyticOrder` — with the count supplied by a Schur triangulation of
  each block.
-/
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantLimit
import GaloisForLFunctions.HTGeometry.FiniteDeterminantArgumentPrinciple
import GaloisForLFunctions.HTGeometry.LogDerivUniformLimit

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Metric Filter Matrix

variable {ι : Type*} [DecidableEq ι]

/-- **The eventual zero count of the block determinants is the order of vanishing of the entire
determinant.** -/
theorem eventually_zeroCount_finiteDet2_eq_analyticOrder {K : ι × ι → ℂ} (hK : IsHS K)
    {z₀ : ℂ} {d : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hord : analyticOrderAt (entireDet2 K) z₀ = (d : ℕ∞))
    (hne : ∀ z ∈ closedBall z₀ R, z ≠ z₀ → entireDet2 K z ≠ 0)
    {n : Finset ι → ℕ}
    (hn : ∀ s, (∮ z in C(z₀, r), logDeriv (finiteDet2 (-(blockMatrix K s))) z)
        = 2 * Real.pi * Complex.I * (n s : ℂ)) :
    ∀ᶠ s : Finset ι in atTop, n s = d := by
  have hRpos : 0 < R := lt_trans hr hrR
  have hρ : 0 < ‖z₀‖ + R := by
    have : (0 : ℝ) ≤ ‖z₀‖ := norm_nonneg z₀
    linarith
  have hsub : closedBall z₀ R ⊆ closedBall (0 : ℂ) (‖z₀‖ + R) := by
    refine closedBall_subset_closedBall' ?_
    rw [Complex.dist_eq, sub_zero]
    linarith
  have huniform := (tendstoUniformlyOn_finiteDet2_entireDet2 hK hρ).mono hsub
  exact eventually_zeroCount_eq_analyticOrder
    (fun s => differentiable_finiteDet2 (-(blockMatrix K s))) (differentiable_entireDet2 hK)
    hr hrR huniform (hrR' := hrR) hord hne hn

/-- The block matrix reindexed to `Fin`, where the Schur decomposition is available. -/
noncomputable def blockFin (K : ι × ι → ℂ) (s : Finset ι) :
    Matrix (Fin (Fintype.card ↥s)) (Fin (Fintype.card ↥s)) ℂ :=
  (blockMatrix K s).submatrix (Fintype.equivFin ↥s).symm (Fintype.equivFin ↥s).symm

theorem finiteDet2_neg_blockFin (K : ι × ι → ℂ) (s : Finset ι) (z : ℂ) :
    finiteDet2 (-(blockFin K s)) z = finiteDet2 (-(blockMatrix K s)) z := by
  have hneg : -(blockFin K s)
      = (-(blockMatrix K s)).submatrix (Fintype.equivFin ↥s).symm
        (Fintype.equivFin ↥s).symm := by
    ext i j; simp [blockFin]
  rw [hneg, finiteDet2_submatrix]

open scoped Classical in
/-- **The order of vanishing of the entire determinant is the eventual Schur eigenvalue count.**
For any choice of Schur triangulation of each reindexed block, the number of Schur eigenvalues `t`
with `−1/t` inside the circle is eventually the order of vanishing of `entireDet2 K` at the
centre. -/
theorem eventually_schurCount_eq_analyticOrder {K : ι × ι → ℂ} (hK : IsHS K)
    {z₀ : ℂ} {d : ℕ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hord : analyticOrderAt (entireDet2 K) z₀ = (d : ℕ∞))
    (hne : ∀ z ∈ closedBall z₀ R, z ≠ z₀ → entireDet2 K z ≠ 0)
    (U T : ∀ s : Finset ι, Matrix (Fin (Fintype.card ↥s)) (Fin (Fintype.card ↥s)) ℂ)
    (hU1 : ∀ s, (U s)ᴴ * U s = 1) (hU2 : ∀ s, U s * (U s)ᴴ = 1)
    (hT : ∀ s, (T s).BlockTriangular id)
    (hMT : ∀ s, (U s)ᴴ * (-(blockFin K s)) * U s = T s)
    (hsph : ∀ s, ∀ z ∈ sphere z₀ r, ∀ i, 1 + z * T s i i ≠ 0) :
    ∀ᶠ s : Finset ι in atTop,
      (Finset.univ.filter fun i => T s i i ≠ 0 ∧ -(T s i i)⁻¹ ∈ ball z₀ r).card = d := by
  refine eventually_zeroCount_finiteDet2_eq_analyticOrder hK hr hrR hord hne ?_
  intro s
  have h := circleIntegral_logDeriv_finiteDet2 (hU1 s) (hU2 s) (hT s) (hMT s) hr (hsph s)
  have hfun : finiteDet2 (-(blockFin K s)) = finiteDet2 (-(blockMatrix K s)) :=
    funext (finiteDet2_neg_blockFin K s)
  rw [hfun] at h
  exact h

end GaloisForLFunctions.HTGeometry
