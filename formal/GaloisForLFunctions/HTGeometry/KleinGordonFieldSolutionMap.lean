import GaloisForLFunctions.HTGeometry.KleinGordonFieldReversible

/-!
# The solution operator

The field-level Duhamel formula is linear in its data, so for each time the map sending the Cauchy
data to the state of the solution is linear — and bounded, by the exponential estimate. This file
makes it a first-class object: a continuous linear map on `L² × L²`, with an explicit bound on its
operator norm.

Linearity is proved the way every structural property of the mild solution is proved: the candidate
curve is continuous and satisfies the Duhamel formula with the corresponding data, and uniqueness
identifies it.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Linear

variable {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}

theorem kgFieldFree_add (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldFree (f₁ + f₂) (h₁ + h₂) t = kgFieldFree f₁ h₁ t + kgFieldFree f₂ h₂ t := by
  rw [kgFieldFree, kgFieldFree, kgFieldFree, map_add, map_add]
  abel

theorem kgFieldFree_smul (c : ℂ) (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldFree (c • f) (c • h) t = c • kgFieldFree f h t := by
  rw [kgFieldFree, kgFieldFree, map_smul, map_smul, smul_add]

/-- **The solution is additive in the Cauchy data.** -/
theorem kgFieldMild_add (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b)
    (f₁ h₁ f₂ h₂ : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMild W (f₁ + f₂) (h₁ + h₂) t
      = kgFieldMild W f₁ h₁ t + kgFieldMild W f₂ h₂ t := by
  have hc1 := continuous_kgFieldMild hb0 hW f₁ h₁
  have hc2 := continuous_kgFieldMild hb0 hW f₂ h₂
  have hduh : ∀ τ : ℝ, kgFieldMild W f₁ h₁ τ + kgFieldMild W f₂ h₂ τ
      = kgFieldFree (f₁ + f₂) (h₁ + h₂) τ
        + ∫ s in (0 : ℝ)..τ, kgFieldKernel W τ s
            (kgFieldMild W f₁ h₁ s + kgFieldMild W f₂ h₂ s) := by
    intro τ
    have hI1 := intervalIntegrable_kgFieldKernel hc1 W τ
    have hI2 := intervalIntegrable_kgFieldKernel hc2 W τ
    have hint : (∫ s in (0 : ℝ)..τ, kgFieldKernel W τ s
          (kgFieldMild W f₁ h₁ s + kgFieldMild W f₂ h₂ s))
        = (∫ s in (0 : ℝ)..τ, kgFieldKernel W τ s (kgFieldMild W f₁ h₁ s))
          + ∫ s in (0 : ℝ)..τ, kgFieldKernel W τ s (kgFieldMild W f₂ h₂ s) := by
      rw [← intervalIntegral.integral_add hI1 hI2]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [map_add]
    rw [hint, kgFieldFree_add, kgFieldMild_eq hb0 hW f₁ h₁ τ, kgFieldMild_eq hb0 hW f₂ h₂ τ]
    abel
  have hfin := eq_kgFieldMild_of_duhamel hb0 hW (f₁ + f₂) (h₁ + h₂) (hc1.add hc2) hduh
  exact (congrFun hfin t).symm

/-- **The solution is homogeneous in the Cauchy data.** -/
theorem kgFieldMild_smul (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (c : ℂ)
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    kgFieldMild W (c • f) (c • h) t = c • kgFieldMild W f h t := by
  have hc1 := continuous_kgFieldMild hb0 hW f h
  have hduh : ∀ τ : ℝ, c • kgFieldMild W f h τ
      = kgFieldFree (c • f) (c • h) τ
        + ∫ s in (0 : ℝ)..τ, kgFieldKernel W τ s (c • kgFieldMild W f h s) := by
    intro τ
    have hI1 := intervalIntegrable_kgFieldKernel hc1 W τ
    have hint : (∫ s in (0 : ℝ)..τ, kgFieldKernel W τ s (c • kgFieldMild W f h s))
        = c • ∫ s in (0 : ℝ)..τ, kgFieldKernel W τ s (kgFieldMild W f h s) := by
      rw [← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [kgFieldKernel_apply, kgFieldKernel_apply, map_smul, map_smul]
    rw [hint, kgFieldFree_smul, kgFieldMild_eq hb0 hW f h τ, smul_add]
  have hfin := eq_kgFieldMild_of_duhamel hb0 hW (c • f) (c • h)
    (continuous_const_smul c |>.comp hc1) hduh
  exact (congrFun hfin t).symm

/-! ## The solution operator -/

variable (W b)

/-- The solution operator, as a linear map from the Cauchy data to the state at time `t`. -/
def kgSolutionLM (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (t : ℝ) :
    (Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E)) →ₗ[ℂ]
      Lp ℂ 2 (volume : Measure E) where
  toFun w := kgFieldMild W w.1 w.2 t
  map_add' w₁ w₂ := kgFieldMild_add hb0 hW w₁.1 w₁.2 w₂.1 w₂.2 t
  map_smul' c w := kgFieldMild_smul hb0 hW c w.1 w.2 t

/-- **The solution operator**, as a continuous linear map with an explicit bound. -/
def kgSolutionCLM (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (t : ℝ) :
    (Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E)) →L[ℂ]
      Lp ℂ 2 (volume : Measure E) :=
  LinearMap.mkContinuous (kgSolutionLM W b hb0 hW t) (2 * Real.exp (b * |t|)) (by
    intro w
    have hle := norm_kgFieldMild_le hb0 hW w.1 w.2 t
    have h1 : ‖w.1‖ ≤ ‖w‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have h2 : ‖w.2‖ ≤ ‖w‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have hexp : (0 : ℝ) < Real.exp (b * |t|) := Real.exp_pos _
    calc ‖kgFieldMild W w.1 w.2 t‖ ≤ (‖w.1‖ + ‖w.2‖) * Real.exp (b * |t|) := hle
      _ ≤ (2 * ‖w‖) * Real.exp (b * |t|) :=
          mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hexp)
      _ = 2 * Real.exp (b * |t|) * ‖w‖ := by ring)

theorem kgSolutionCLM_apply (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (t : ℝ)
    (w : Lp ℂ 2 (volume : Measure E) × Lp ℂ 2 (volume : Measure E)) :
    kgSolutionCLM W b hb0 hW t w = kgFieldMild W w.1 w.2 t := rfl

theorem norm_kgSolutionCLM_le (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (t : ℝ) :
    ‖kgSolutionCLM W b hb0 hW t‖ ≤ 2 * Real.exp (b * |t|) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end Linear

end GaloisForLFunctions.HTGeometry
