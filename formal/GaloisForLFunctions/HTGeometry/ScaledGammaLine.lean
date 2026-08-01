import GaloisForLFunctions.HTGeometry.GammaLineBoundaryCases
import GaloisForLFunctions.HTGeometry.NormalizedRatioLaw

/-!
# Scaled archimedean factors on a vertical line

The archimedean factor of an `L`-function is `Γ((s+μ)/2)` rather than `Γ(s)`.  On a vertical line
this is the *same* object after an affine change of variable: `Γ((σ+μ+it)/2)` is the value of
`Γ` on the line `Re s = (σ+μ)/2` at the parameter `t/2`.  Since `t/2 → ∞` with `t`, every vertical
statement transfers — decay faster than every power, and dominance of a higher Gamma power.

Simultaneous *incommensurable* Gamma scales are a different question and are not treated here: the
transfer below is a single affine substitution.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {μ σ : ℝ}

/-- The scaled archimedean factor `Γ((s+μ)/2)` on the vertical line `Re s = σ`. -/
noncomputable def scaledGammaLine (μ σ t : ℝ) : ℂ :=
  Complex.Gamma (((σ : ℂ) + (μ : ℂ) + (t : ℂ) * Complex.I) / 2)

/-- The scaled factor is the unscaled one after an affine substitution. -/
theorem scaledGammaLine_eq (μ σ t : ℝ) :
    scaledGammaLine μ σ t = gammaLine ((σ + μ) / 2) (t / 2) := by
  rw [scaledGammaLine, gammaLine]
  congr 1
  push_cast
  ring

theorem scaledGammaLine_ne_zero (h : 0 < σ + μ) (t : ℝ) : scaledGammaLine μ σ t ≠ 0 := by
  rw [scaledGammaLine_eq]
  exact gammaLine_ne_zero (by linarith) _

/-- Polynomial growth survives an affine substitution of the line parameter. -/
theorem HasPolyGrowthLine.comp_mul_two {f : ℝ → ℂ} (hf : HasPolyGrowthLine f) :
    HasPolyGrowthLine (fun u : ℝ => f (2 * u)) := by
  obtain ⟨M, C, hC, hb⟩ := hf
  refine ⟨M, C * 2 ^ M, by positivity, ?_⟩
  have hmap : Tendsto (fun u : ℝ => 2 * u) atTop atTop :=
    Filter.Tendsto.const_mul_atTop two_pos tendsto_id
  filter_upwards [hmap.eventually hb, eventually_ge_atTop (0 : ℝ)] with u hu hu0
  calc ‖f (2 * u)‖ ≤ C * (2 * u) ^ M := hu
    _ = C * 2 ^ M * u ^ M := by rw [mul_pow]; ring

/-- **The scaled archimedean factor also kills polynomial growth.**  A positive power of
`Γ((s+μ)/2)` times a coefficient of polynomial growth tends to zero along the line. -/
theorem tendsto_scaledGammaLine_pow_mul (h : 0 < σ + μ) {f : ℝ → ℂ}
    (hf : HasPolyGrowthLine f) (k : ℕ) :
    Tendsto (fun t : ℝ => scaledGammaLine μ σ t ^ (k + 1) * f t) atTop (nhds 0) := by
  have hhalf : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun t ht => by linarith⟩
  have hbase := tendsto_gammaLine_pow_mul (σ := (σ + μ) / 2) (by linarith)
    hf.comp_mul_two k
  have hcomp := hbase.comp hhalf
  refine hcomp.congr fun t => ?_
  simp only [Function.comp_apply]
  rw [scaledGammaLine_eq]
  congr 2
  ring

/-- The scaled factor decays on the line. -/
theorem tendsto_scaledGammaLine_zero (h : 0 < σ + μ) :
    Tendsto (fun t : ℝ => scaledGammaLine μ σ t) atTop (nhds 0) := by
  have hhalf : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun t ht => by linarith⟩
  have hbase := tendsto_gammaLine_zero (σ := (σ + μ) / 2) (by linarith)
  refine (hbase.comp hhalf).congr fun t => ?_
  simp only [Function.comp_apply]
  rw [scaledGammaLine_eq]

/-- A strictly larger power of the scaled factor dominates. -/
theorem tendsto_scaledGammaLine_pow_ratio (h : 0 < σ + μ) {u v : ℕ} (huv : v < u) :
    Tendsto (fun t : ℝ => scaledGammaLine μ σ t ^ u / scaledGammaLine μ σ t ^ v)
      atTop (nhds 0) := by
  have hhalf : Tendsto (fun t : ℝ => t / 2) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun t ht => by linarith⟩
  have hbase := tendsto_gammaLine_pow_ratio (σ := (σ + μ) / 2) (by linarith) huv
  refine (hbase.comp hhalf).congr fun t => ?_
  simp only [Function.comp_apply]
  rw [scaledGammaLine_eq]

end GaloisForLFunctions
