import Mathlib

/-!
# Scalar submicroscopic diagonal covariance cannot be a universal minorant

The source-only centered shifts in `XiCenteredRealShiftDiagonalExtractor` recover exact analytic
multiplicity after the displacement tends to zero.  At a finite displacement, however, a scalar
extractor contains off-diagonal pair covariance.  This module isolates the obstruction without
using a zero enumeration.

Any continuous normalized symmetric pair kernel is positive at some nonzero arbitrarily close
separation.  A two-point packet then has extracted mass strictly larger than its exact diagonal
mass.  The canonical transverse and real-height shift kernels exhibit the same obstruction
explicitly.  Thus a finite-displacement scalar source extractor cannot by itself give the
minorant needed to majorize the corrected critical-feature budget.  A viable successor must keep
signed matrix covariance or use additional pair-repulsion information.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Scalar diagonal approximation for two distinct unit-multiplicity points when the symmetric
off-diagonal pair kernel has value `K d`. -/
def twoPointSymmetricScalarDiagonalBudget (K : ℝ → ℝ) (d : ℝ) : ℝ :=
  2 + 2 * K d

/-- **Continuous scalar-selector no-go.**  Every continuous kernel normalized to one on the
diagonal overcounts the diagonal mass of some arbitrarily close two-point packet. -/
theorem exists_twoPointSymmetricScalarDiagonalBudget_gt_diagonal
    {K : ℝ → ℝ} (hK : ContinuousAt K 0) (hzero : K 0 = 1) :
    ∃ d : ℝ, 0 < d ∧
      2 < twoPointSymmetricScalarDiagonalBudget K d := by
  have hKzero : 0 < K 0 := by rw [hzero]; norm_num
  have hevent : ∀ᶠ d in 𝓝 (0 : ℝ), 0 < K d :=
    hK.eventually_const_lt hKzero
  rw [Metric.eventually_nhds_iff] at hevent
  obtain ⟨eta, heta, hall⟩ := hevent
  refine ⟨eta / 2, by linarith, ?_⟩
  have hdist : dist (eta / 2) (0 : ℝ) < eta := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  have hpos := hall hdist
  rw [twoPointSymmetricScalarDiagonalBudget]
  linarith

/-- Pair covariance produced by a transverse displacement, equivalently a positive-real
displacement in the ordinary `s` coordinate. -/
def submicroscopicTransversePairKernel (eps d : ℝ) : ℝ :=
  eps ^ (2 : ℕ) / (d ^ (2 : ℕ) + eps ^ (2 : ℕ))

theorem submicroscopicTransversePairKernel_zero
    {eps : ℝ} (heps : eps ≠ 0) :
    submicroscopicTransversePairKernel eps 0 = 1 := by
  simp [submicroscopicTransversePairKernel, heps]

/-- Every distinct pair contributes with the wrong strict sign to the transverse scalar
diagonal extractor. -/
theorem submicroscopicTransversePairKernel_pos
    {eps d : ℝ} (heps : eps ≠ 0) :
    0 < submicroscopicTransversePairKernel eps d := by
  rw [submicroscopicTransversePairKernel]
  positivity

theorem two_lt_twoPoint_transverseScalarDiagonalBudget
    {eps d : ℝ} (heps : eps ≠ 0) :
    2 < twoPointSymmetricScalarDiagonalBudget
      (submicroscopicTransversePairKernel eps) d := by
  rw [twoPointSymmetricScalarDiagonalBudget]
  have hpos := submicroscopicTransversePairKernel_pos (d := d) heps
  linarith

/-- Pair covariance produced by the centered real-height shift used by the existing source-only
diagonal extractor. -/
def submicroscopicRealPairKernel (eps d : ℝ) : ℝ :=
  eps ^ (2 : ℕ) / (eps ^ (2 : ℕ) - d ^ (2 : ℕ))

theorem submicroscopicRealPairKernel_zero
    {eps : ℝ} (heps : eps ≠ 0) :
    submicroscopicRealPairKernel eps 0 = 1 := by
  simp [submicroscopicRealPairKernel, heps]

/-- A real-height shift also has the wrong sign on every pair closer than its displacement. -/
theorem submicroscopicRealPairKernel_pos_of_abs_lt
    {eps d : ℝ} (heps : 0 < eps) (hd : |d| < eps) :
    0 < submicroscopicRealPairKernel eps d := by
  have hdsq : d ^ (2 : ℕ) < eps ^ (2 : ℕ) := by
    have hsq := (sq_lt_sq₀ (abs_nonneg d) heps.le).2 hd
    rwa [sq_abs] at hsq
  rw [submicroscopicRealPairKernel]
  exact div_pos (sq_pos_of_pos heps) (sub_pos.mpr hdsq)

theorem two_lt_twoPoint_realScalarDiagonalBudget_of_close
    {eps d : ℝ} (heps : 0 < eps) (hd : |d| < eps) :
    2 < twoPointSymmetricScalarDiagonalBudget
      (submicroscopicRealPairKernel eps) d := by
  rw [twoPointSymmetricScalarDiagonalBudget]
  have hpos := submicroscopicRealPairKernel_pos_of_abs_lt heps hd
  linarith

end

end RHTower
