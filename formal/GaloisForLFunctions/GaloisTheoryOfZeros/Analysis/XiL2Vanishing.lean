import GaloisForLFunctions.HTGeometry.ComplexAnalysis.HolomorphicL2Flatness
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Local squared mass of the completed Riemann function

At every complex point, the rotated completed Riemann function has a positive polynomial
lower bound for its disk mass. In particular no point, including any zero of any multiplicity,
has infinite-order local L² vanishing. This requires neither a zero-location assertion nor a
simplicity assertion.
-/

open Complex MeasureTheory Metric Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Every point admits a positive power-law lower bound for the local mass of `XiC`. -/
theorem XiC_exists_power_lower_mass (a : ℂ) :
    ∃ (k : ℕ) (c δ : ℝ), 0 < c ∧ 0 < δ ∧
      ∀ r : ℝ, 0 < r → r < δ →
        c * r ^ k ≤ ∫ z in ball (0 : ℂ) r, ‖XiC (a + z)‖ ^ 2 := by
  have hshift : AnalyticOnNhd ℂ (fun z => XiC (a + z)) univ := by
    intro z _
    exact (XiC_analytic (a + z) (mem_univ _)).comp
      (analyticAt_const.add analyticAt_id)
  apply exists_power_lower_mass_of_entire hshift
  exact ⟨-a, by simpa only [add_neg_cancel] using XiC_zero_ne⟩

/-- The completed Riemann function has no point of infinite-order local L² vanishing. -/
theorem XiC_not_l2FlatAt (a : ℂ) : ¬ L2FlatAt XiC a := by
  intro hflat
  exact XiC_zero_ne (congrFun (eq_zero_of_entire_l2FlatAt XiC_analytic hflat) 0)

end RHTower
