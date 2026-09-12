import GaloisForLFunctions.HTGeometry.AnalyticSlopeFactor
import Mathlib.Analysis.Analytic.Order

/-!
# Analytic factors retained by compensated division

Normalize a correction by `U(rho) = 1` and subtract `G(rho) U` from a seed
multiplier `G`. Dividing the corrected product `F (G - G(rho) U)` by `s-rho`
leaves the entire factor `F` intact. The divided difference gives its analytic
extension, the exact order sum, and the first-jet condition for equality of
orders. Thus source compensation cannot lower the multiplicity carried by `F`.
-/

open Complex Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The seed multiplier after subtraction of its normalized correction. -/
def compensatedSeedGerm (rho : ℂ) (G U : ℂ → ℂ) (s : ℂ) : ℂ :=
  G s - G rho * U s

/-- Analytic extension of the compensated quotient, retaining its original factor. -/
def compensatedAnalyticDivision (rho : ℂ) (F G U : ℂ → ℂ) : ℂ → ℂ :=
  F * analyticSlope (compensatedSeedGerm rho G U) rho

theorem compensatedSeedGerm_analyticAt {rho : ℂ} {G U : ℂ → ℂ}
    (hG : AnalyticAt ℂ G rho) (hU : AnalyticAt ℂ U rho) :
    AnalyticAt ℂ (compensatedSeedGerm rho G U) rho :=
  hG.sub (analyticAt_const.mul hU)

/-- Exact quotient identity, including the division point. -/
theorem compensatedAnalyticDivision_factor (rho : ℂ) (F G U : ℂ → ℂ)
    (hU : U rho = 1) (s : ℂ) :
    (s - rho) * compensatedAnalyticDivision rho F G U s =
      F s * (G s - G rho * U s) := by
  have h := sub_eq_mul_analyticSlope (compensatedSeedGerm rho G U) rho s
  have hzero : compensatedSeedGerm rho G U rho = 0 := by
    simp [compensatedSeedGerm, hU]
  rw [hzero, sub_zero] at h
  change (s - rho) * (F s * analyticSlope (compensatedSeedGerm rho G U) rho s) = _
  rw [mul_left_comm, ← h]
  rfl

theorem compensatedAnalyticDivision_analyticAt {rho : ℂ} {F G U : ℂ → ℂ}
    (hF : AnalyticAt ℂ F rho) (hG : AnalyticAt ℂ G rho) (hU : AnalyticAt ℂ U rho) :
    AnalyticAt ℂ (compensatedAnalyticDivision rho F G U) rho :=
  hF.mul (analyticAt_analyticSlope (compensatedSeedGerm_analyticAt hG hU))

/-- The original zero order survives as an exact summand. -/
theorem compensatedAnalyticDivision_order {rho : ℂ} {F G U : ℂ → ℂ}
    (hF : AnalyticAt ℂ F rho) (hG : AnalyticAt ℂ G rho) (hU : AnalyticAt ℂ U rho) :
    analyticOrderAt (compensatedAnalyticDivision rho F G U) rho =
      analyticOrderAt F rho +
        analyticOrderAt (analyticSlope (compensatedSeedGerm rho G U) rho) rho :=
  analyticOrderAt_mul hF (analyticAt_analyticSlope (compensatedSeedGerm_analyticAt hG hU))

/-- Compensation followed by division cannot lower the original factor multiplicity. -/
theorem compensatedAnalyticDivision_order_not_lowered {rho : ℂ} {F G U : ℂ → ℂ}
    (hF : AnalyticAt ℂ F rho) (hG : AnalyticAt ℂ G rho) (hU : AnalyticAt ℂ U rho) :
    analyticOrderAt F rho ≤ analyticOrderAt (compensatedAnalyticDivision rho F G U) rho := by
  rw [compensatedAnalyticDivision_order hF hG hU]
  exact le_self_add

/-- The surviving multiplier is fixed by the original and correction first jets. -/
theorem compensatedSeedGerm_slope_self {rho : ℂ} {G U : ℂ → ℂ}
    (hG : AnalyticAt ℂ G rho) (hU : AnalyticAt ℂ U rho) :
    analyticSlope (compensatedSeedGerm rho G U) rho rho =
      deriv G rho - G rho * deriv U rho := by
  rw [analyticSlope_self]
  exact (hG.differentiableAt.hasDerivAt.sub
    (hU.differentiableAt.hasDerivAt.const_mul (G rho))).deriv

/-- A nonzero compensated first jet preserves the original multiplicity exactly. -/
theorem compensatedAnalyticDivision_order_preserved {rho : ℂ} {F G U : ℂ → ℂ}
    (hF : AnalyticAt ℂ F rho) (hG : AnalyticAt ℂ G rho) (hU : AnalyticAt ℂ U rho)
    (hjet : deriv G rho - G rho * deriv U rho ≠ 0) :
    analyticOrderAt (compensatedAnalyticDivision rho F G U) rho = analyticOrderAt F rho := by
  have hs : analyticOrderAt (analyticSlope (compensatedSeedGerm rho G U) rho) rho = 0 := by
    apply (analyticAt_analyticSlope
      (compensatedSeedGerm_analyticAt hG hU)).analyticOrderAt_eq_zero.mpr
    rwa [compensatedSeedGerm_slope_self hG hU]
  rw [compensatedAnalyticDivision_order hF hG hU, hs, add_zero]

end
end GaloisForLFunctions.HTGeometry
