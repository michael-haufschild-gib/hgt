import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureBoundaryPhaseSelection
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeaturePoleGammaVerticalFTC

/-!
# First-order winding reduction of the HCF height-cell budget

The height-cell average of the source-only pole--Gamma covariance contains a second logarithmic
derivative.  On the canonical lattice, its cell endpoint increments telescope exactly.  The two
surviving endpoints are `o(N)` by the zero-independent archimedean vertical bound and
Riemann--von Mangoldt.  Consequently the only possible leading source budget is first-order
archimedean winding minus the compact Plemelj boundary average.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Forward differences telescope on the asymmetric canonical integer window. -/
theorem sum_criticalFeatureCanonicalLatticeWindow_increment
    (d : ℤ → ℝ) (n : ℕ) :
    (∑ k ∈ criticalFeatureCanonicalLatticeWindow n, (d k - d (k - 1))) =
      d ((n : ℤ) + 1) - d (-((n : ℤ) + 2)) := by
  classical
  have h := Finset.sum_range_sub
    (fun j : ℕ => d ((j : ℤ) - (n : ℤ) - 2)) (2 * n + 3)
  have hreindex :
      (∑ k ∈ criticalFeatureCanonicalLatticeWindow n, (d k - d (k - 1))) =
        ∑ j ∈ Finset.range (2 * n + 3),
          ((fun j : ℕ => d ((j : ℤ) - (n : ℤ) - 2)) (j + 1) -
            (fun j : ℕ => d ((j : ℤ) - (n : ℤ) - 2)) j) := by
    unfold criticalFeatureCanonicalLatticeWindow
    refine Finset.sum_nbij'
      (i := fun k => (k + (n : ℤ) + 1).toNat)
      (j := fun j => (j : ℤ) - (n : ℤ) - 1) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Icc]
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    · intro j hj
      simp only [Finset.mem_range] at hj
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have h1 : ((((k + (n : ℤ) + 1).toNat + 1 : ℕ) : ℤ) -
          (n : ℤ) - 2) = k := by
        push_cast
        omega
      have h2 : (((k + (n : ℤ) + 1).toNat : ℤ) - (n : ℤ) - 2) = k - 1 := by
        omega
      simp only [h1, h2]
  rw [hreindex, h]
  congr 1 <;> push_cast <;> congr 1 <;> omega

/-- Twice the first-order archimedean winding over all canonical height cells. -/
def criticalFeatureCanonicalFirstOrderPoleGammaWinding (n : ℕ) : ℝ :=
  2 * ∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
    ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ),
      (logDeriv archFactor (criticalFeatureEulerVMArchPoint t)).re

/-- Exact canonical-cell reduction: the second jet is only the two endpoint values. -/
theorem sum_integral_criticalFeaturePoleGammaArchJet_eq_firstOrder_sub_endpoint
    (n : ℕ) :
    (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
      ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ),
        2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
          deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re) =
      criticalFeatureCanonicalFirstOrderPoleGammaWinding n -
        2 * criticalFeatureCanonicalPoleGammaEndpointIncrement n := by
  let L : ℝ → ℂ := fun t =>
    logDeriv archFactor (criticalFeatureEulerVMArchPoint t)
  have htelescope := sum_criticalFeatureCanonicalLatticeWindow_increment
    (fun k : ℤ => (L (k : ℝ)).im) n
  have htelescope' :
      (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
        ((L (k : ℝ)).im - (L ((k : ℝ) - 1)).im)) =
        criticalFeatureCanonicalPoleGammaEndpointIncrement n := by
    push_cast at htelescope
    simpa only [Int.cast_sub, Int.cast_one,
      criticalFeatureCanonicalPoleGammaEndpointIncrement, L] using htelescope
  calc
    (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
      ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ),
        2 * (logDeriv archFactor (criticalFeatureEulerVMArchPoint t) -
          deriv (logDeriv archFactor) (criticalFeatureEulerVMArchPoint t)).re) =
      ∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
        (2 * (∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ), (L t).re) -
          2 * ((L (k : ℝ)).im - (L ((k : ℝ) - 1)).im)) := by
            apply Finset.sum_congr rfl
            intro k hk
            simpa only [L] using
              (integral_criticalFeaturePoleGammaArchJet_eq_firstOrder_sub_endpoints
                ((k : ℝ) - 1) (k : ℝ))
    _ = 2 * (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
          ∫ t : ℝ in ((k : ℝ) - 1)..(k : ℝ), (L t).re) -
        2 * (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
          ((L (k : ℝ)).im - (L ((k : ℝ) - 1)).im)) := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = criticalFeatureCanonicalFirstOrderPoleGammaWinding n -
        2 * criticalFeatureCanonicalPoleGammaEndpointIncrement n := by
      rw [htelescope']
      rfl

/-- Exact source-only covariance formula after height-cell tiling and vertical FTC. -/
theorem criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage_eq_firstOrder_sub_endpoint_boundary
    (n : ℕ) :
    criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n =
      criticalFeatureCanonicalFirstOrderPoleGammaWinding n -
        2 * criticalFeatureCanonicalPoleGammaEndpointIncrement n -
        criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n := by
  rw [criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage_eq_heightCells,
    sum_integral_criticalFeaturePoleGammaArchJet_eq_firstOrder_sub_endpoint]

/-- At `N(T)` scale, phase-averaged source covariance is exactly first-order safe-line winding
minus compact source boundary.  No second-jet budget remains. -/
theorem tendsto_criticalFeaturePhaseCovariance_sub_firstOrderWindingBoundary_div :
    Tendsto
      (fun n : ℕ =>
        (criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage n -
          (criticalFeatureCanonicalFirstOrderPoleGammaWinding n -
            criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n)) /
          criticalFeatureCanonicalZeroCount n)
      atTop (𝓝 0) := by
  have h : Tendsto
      (fun n : ℕ => (-2 : ℝ) *
        (criticalFeatureCanonicalPoleGammaEndpointIncrement n /
          criticalFeatureCanonicalZeroCount n))
      atTop (𝓝 ((-2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul
      tendsto_criticalFeatureCanonicalPoleGammaEndpointIncrement_div
  convert h using 1
  · funext n
    rw [
      criticalFeatureCompactFiniteLatticeSourceCovariancePhaseAverage_eq_firstOrder_sub_endpoint_boundary]
    ring
  · ring

end

end RHTower
