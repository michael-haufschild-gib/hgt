import GaloisForLFunctions.HTGeometry.HerglotzControlMap

/-!
# The weighted Cauchy-jet control map

The genericity argument perturbs the *parameter* `u`, so its control map must be defined on the
parameter space `L^∞(μ)` of the base measure, not on `L^∞` of the reweighted measure.  Writing the
Radon–Nikodym density explicitly keeps everything over `μ`:

```text
L f = fun s ↦ ∫ f t * w t * (t - x s.1)⁻¹ ^ (s.2 + 1) dμ t.
```

Here `w` is the density of the reweighted measure, integrable against `μ` exactly under the
Nevanlinna growth condition.  Boundedness now comes from integrability of `w` rather than
finiteness of `μ`, so the base measure may have infinite mass — which is the case of interest.

This also removes any need to identify `L^∞(μ)` with `L^∞` of the reweighted measure: both the
parameter and the gauge live over `μ` throughout.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A bounded reweighting against an integrable density and a bounded kernel is integrable, with no
finiteness hypothesis on the base measure. -/
theorem integrable_Lp_top_mul_weight {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℝ ⊤ μ) (w : α → ℝ) (hw : Integrable w μ)
    (g : α → ℂ) (hg : AEStronglyMeasurable g μ) {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    Integrable (fun t => ((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * g t) μ := by
  have hmeas : AEStronglyMeasurable
      (fun t => ((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * g t) μ := by
    refine AEStronglyMeasurable.mul ?_ hg
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f)).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable)
  refine Integrable.mono' (((hw.abs).const_mul (‖f‖ * B))) hmeas ?_
  filter_upwards [ae_norm_le_norm_Lp_top μ f] with t ht
  calc ‖((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * g t‖
      = ‖f t‖ * ‖w t‖ * ‖g t‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
    _ ≤ ‖f‖ * |w t| * B := by
        have h1 : ‖f t‖ * ‖w t‖ ≤ ‖f‖ * |w t| := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
        exact mul_le_mul h1 (hB t) (norm_nonneg _)
          (mul_nonneg (norm_nonneg f) (abs_nonneg _))
    _ = ‖f‖ * B * |w t| := by ring

/-- The explicit operator bound of one weighted jet coordinate. -/
theorem norm_integral_Lp_top_mul_weight_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : Lp ℝ ⊤ μ) (w : α → ℝ) (hw : Integrable w μ)
    (g : α → ℂ) {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) :
    ‖∫ t, ((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * g t ∂μ‖ ≤
      (B * ∫ t, |w t| ∂μ) * ‖f‖ := by
  have hbound : ∀ᵐ t ∂μ,
      ‖((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * g t‖ ≤ ‖f‖ * B * |w t| := by
    filter_upwards [ae_norm_le_norm_Lp_top μ f] with t ht
    calc ‖((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * g t‖
        = ‖f t‖ * ‖w t‖ * ‖g t‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
      _ ≤ ‖f‖ * |w t| * B := by
          have h1 : ‖f t‖ * ‖w t‖ ≤ ‖f‖ * |w t| := by
            rw [Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
          exact mul_le_mul h1 (hB t) (norm_nonneg _)
            (mul_nonneg (norm_nonneg f) (abs_nonneg _))
      _ = ‖f‖ * B * |w t| := by ring
  have hint := norm_integral_le_integral_norm
    (f := fun t => ((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * g t) (μ := μ)
  refine le_trans hint ?_
  have hmono := integral_mono_of_nonneg
    (f := fun t => ‖((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * g t‖)
    (g := fun t => ‖f‖ * B * |w t|)
    (Filter.Eventually.of_forall fun t => norm_nonneg _)
    ((hw.abs).const_mul (‖f‖ * B)) hbound
  refine le_trans hmono ?_
  rw [integral_const_mul]
  ring_nf
  exact le_refl _

omit [Fintype ι] [DecidableEq ι] in
/-- Integrability of a bounded reweighting against the weighted Cauchy kernel. -/
theorem integrable_weighted_cauchyJetKernel (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (f : Lp ℝ ⊤ μ) (s : jetIndex n) :
    Integrable
      (fun t => ((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s) μ :=
  integrable_Lp_top_mul_weight μ f w hw _
    (aestronglyMeasurable_cauchyJetKernel μ x n s)
    (norm_cauchyJetKernel_le x hne n s)

/-- The weighted Cauchy-jet control map on bounded reweightings, as a linear map. -/
def weightedJetControlLinear (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ) :
    Lp ℝ ⊤ μ →ₗ[ℝ] (jetIndex n → ℂ) where
  toFun f := fun s =>
    ∫ t, ((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ
  map_add' f g := by
    funext s
    have hae : ∀ᵐ t ∂μ,
        (((f + g) t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s =
          ((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s +
            ((g t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s := by
      filter_upwards [Lp.coeFn_add f g] with t ht
      rw [ht]
      simp only [Pi.add_apply]
      push_cast
      ring
    rw [integral_congr_ae hae,
      integral_add (integrable_weighted_cauchyJetKernel μ w hw x hne n f s)
        (integrable_weighted_cauchyJetKernel μ w hw x hne n g s)]
    rfl
  map_smul' r f := by
    funext s
    have hae : ∀ᵐ t ∂μ,
        (((r • f) t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s =
          (r : ℂ) * (((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) *
            cauchyJetKernel x n t s) := by
      filter_upwards [Lp.coeFn_smul r f] with t ht
      rw [ht]
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [integral_congr_ae hae, integral_const_mul]
    rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem weightedJetControlLinear_apply (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (f : Lp ℝ ⊤ μ) (s : jetIndex n) :
    weightedJetControlLinear μ w hw x hne n f s =
      ∫ t, ((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ :=
  rfl

/-- The total operator bound of the weighted control map. -/
def weightedJetControlBound (μ : Measure ℝ) (w : ℝ → ℝ)
    (x : ι → ℂ) (n : ι → ℕ) : ℝ :=
  (∑ s : jetIndex n, cauchyJetKernelBound x n s) * ∫ t, |w t| ∂μ

set_option linter.unusedSectionVars false in
/-- **The weighted control map is bounded.** -/
theorem norm_weightedJetControlLinear_le (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ) (f : Lp ℝ ⊤ μ) :
    ‖weightedJetControlLinear μ w hw x hne n f‖ ≤
      weightedJetControlBound μ w x n * ‖f‖ := by
  have hmass : 0 ≤ ∫ t, |w t| ∂μ :=
    integral_nonneg fun t => abs_nonneg _
  have hCnonneg : 0 ≤ weightedJetControlBound μ w x n := by
    apply mul_nonneg _ hmass
    exact Finset.sum_nonneg fun s _ => cauchyJetKernelBound_nonneg x n s
  apply pi_norm_le_iff_of_nonneg (mul_nonneg hCnonneg (norm_nonneg f)) |>.mpr
  intro s
  have hcoord := norm_integral_Lp_top_mul_weight_le μ f w hw
    (fun t => cauchyJetKernel x n t s) (norm_cauchyJetKernel_le x hne n s)
  refine le_trans hcoord ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  rw [weightedJetControlBound]
  apply mul_le_mul_of_nonneg_right _ hmass
  exact Finset.single_le_sum
    (fun s' _ => cauchyJetKernelBound_nonneg x n s') (Finset.mem_univ s)

/-- The weighted Cauchy-jet control map as a continuous linear map. -/
def weightedJetControl (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ) :
    Lp ℝ ⊤ μ →L[ℝ] (jetIndex n → ℂ) :=
  LinearMap.mkContinuous (weightedJetControlLinear μ w hw x hne n)
    (weightedJetControlBound μ w x n)
    (norm_weightedJetControlLinear_le μ w hw x hne n)

set_option linter.unusedSectionVars false in
@[simp]
theorem weightedJetControl_apply (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ)
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (f : Lp ℝ ⊤ μ) (s : jetIndex n) :
    weightedJetControl μ w hw x hne n f s =
      ∫ t, ((f t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ :=
  rfl

end

end GaloisForLFunctions.HTGeometry
