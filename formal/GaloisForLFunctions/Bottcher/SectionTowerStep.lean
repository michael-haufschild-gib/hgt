/-
# The Böttcher section tower: extension step (helpers)

Helpers for the sqrt-descent: circle membership, the bridge from a `TowerSection`'s raw winding
field to `windInt` of its section loop, and the transported point-winding (any point strictly
below the circle's level has winding `2πi` — sublevel transport to `0`).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.SectionTower

open Complex Set Filter Metric

namespace Bottcher

theorem norm_circleMap_zero {r : ℝ} (hr : 0 < r) (θ : ℝ) : ‖circleMap 0 r θ‖ = r := by
  simp [circleMap, Complex.norm_exp, abs_of_pos hr]

theorem circleMap_mem_annulusSet {r rlo rhi : ℝ} (hr : 0 < r) (h1 : rlo < r) (h2 : r < rhi)
    (θ : ℝ) : circleMap 0 r θ ∈ annulusSet rlo rhi := by
  constructor
  · rw [norm_circleMap_zero hr]; exact h1
  · rw [norm_circleMap_zero hr]; exact h2

/-- The section loop of a tower section at an interior radius. -/
noncomputable def TowerSection.loop {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {r : ℝ} (hr : 0 < r) (h1 : rlo < r) (h2 : r < rhi) : C1Loop :=
  sectionLoop S.an (circleMap_mem_annulusSet hr h1 h2)

/-- The raw winding field is `windInt` of the section loop about `0`. -/
theorem TowerSection.windInt_loop_zero {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {r : ℝ} (hr : 0 < r) (h1 : rlo < r) (h2 : r < rhi) :
    windInt (S.loop hr h1 h2) 0 = 2 * (Real.pi : ℂ) * Complex.I := by
  have hraw := S.wind r h1 h2
  rw [← hraw]
  apply intervalIntegral.integral_congr
  intro θ _
  show ((S.loop hr h1 h2).γ θ - 0)⁻¹ * (S.loop hr h1 h2).γ' θ = _
  rw [sub_zero]
  rfl

/-- The loop of a tower section runs at constant level `log r`. -/
theorem TowerSection.loop_level {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {r : ℝ} (hr : 0 < r) (h1 : rlo < r) (h2 : r < rhi) (θ : ℝ) :
    greenFunctionDyn c ((S.loop hr h1 h2).γ θ) = Real.log r := by
  show greenFunctionDyn c (S.T (circleMap 0 r θ)) = Real.log r
  rw [S.level _ (circleMap_mem_annulusSet hr h1 h2 θ), norm_circleMap_zero hr]

/-- **Transported point winding.**  Any point strictly below the circle's level has winding `2πi`
about the section loop (sublevel transport to `0` + the tower's winding invariant). -/
theorem TowerSection.windInt_loop_point {c : ℂ} {rlo rhi : ℝ} (S : TowerSection c rlo rhi)
    {r : ℝ} (hr : 0 < r) (h1 : rlo < r) (h2 : r < rhi)
    (h0 : greenFunctionDyn c 0 < Real.log r)
    {p : ℂ} (hp : greenFunctionDyn c p < Real.log r) :
    windInt (S.loop hr h1 h2) p = 2 * (Real.pi : ℂ) * Complex.I := by
  rw [windInt_eq_windInt_zero_of_level (S.loop hr h1 h2) h0 (S.loop_level hr h1 h2) hp]
  exact S.windInt_loop_zero hr h1 h2

/-- The critical value's level: `G_c(c) = 2·G_c(0)`. -/
theorem greenFunctionDyn_critical_value (c : ℂ) :
    greenFunctionDyn c c = 2 * greenFunctionDyn c 0 := by
  have := greenFunctionDyn_quadratic c 0
  rw [show quadratic c 0 = c from by unfold quadratic; ring] at this
  exact this

/-- `logDeriv` respects eventual equality. -/
theorem logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {w : ℂ} (h : f =ᶠ[nhds w] g) :
    logDeriv f w = logDeriv g w := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.self_of_nhds]

end Bottcher

namespace Bottcher
open Complex Set Filter Metric
