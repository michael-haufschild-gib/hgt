import GaloisForLFunctions.HTGeometry.BoundedReweightingControl

/-!
# The bounded-reweighting Cauchy-jet control map

This module assembles the control map used by the genericity argument: a bounded reweighting of a
finite measure is sent to the finite vector of its Cauchy jets at prescribed nodes,

```text
L f = fun s ↦ ∫ f t * (t - x s.1)⁻¹ ^ (s.2 + 1) dμ t.
```

Each kernel coordinate is uniformly bounded off the real axis, so every component is a bounded
linear functional of the reweighting, with operator bound linear in the reweighting norm.  The
resulting continuous linear map is the object the Baire pullback consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The uniform bound on one Cauchy kernel coordinate. -/
def cauchyJetKernelBound (x : ι → ℂ) (n : ι → ℕ) (s : jetIndex n) : ℝ :=
  (|(x s.1).im|⁻¹) ^ (s.2.1 + 1)

omit [Fintype ι] [DecidableEq ι] in
theorem cauchyJetKernelBound_nonneg (x : ι → ℂ) (n : ι → ℕ) (s : jetIndex n) :
    0 ≤ cauchyJetKernelBound x n s := by
  rw [cauchyJetKernelBound]
  positivity

omit [Fintype ι] [DecidableEq ι] in
/-- Off the real axis each Cauchy kernel coordinate is uniformly bounded. -/
theorem norm_cauchyJetKernel_le (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0)
    (n : ι → ℕ) (s : jetIndex n) (t : ℝ) :
    ‖cauchyJetKernel x n t s‖ ≤ cauchyJetKernelBound x n s := by
  rw [cauchyJetKernel, cauchyJetKernelBound, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inv_real_sub_le (hne s.1) t) _

omit [Fintype ι] [DecidableEq ι] in
theorem aestronglyMeasurable_cauchyJetKernel (μ : Measure ℝ)
    (x : ι → ℂ) (n : ι → ℕ) (s : jetIndex n) :
    AEStronglyMeasurable (fun t : ℝ => cauchyJetKernel x n t s) μ := by
  apply Measurable.aestronglyMeasurable
  unfold cauchyJetKernel
  fun_prop

omit [Fintype ι] [DecidableEq ι] in
/-- Integrability of a bounded reweighting against one Cauchy kernel coordinate. -/
theorem integrable_reweighted_cauchyJetKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (f : Lp ℝ ⊤ μ) (s : jetIndex n) :
    Integrable (fun t => ((f t : ℝ) : ℂ) * cauchyJetKernel x n t s) μ :=
  integrable_Lp_top_mul μ f _ (aestronglyMeasurable_cauchyJetKernel μ x n s)
    (norm_cauchyJetKernel_le x hne n s)

/-- The Cauchy-jet control map on bounded reweightings, as a linear map. -/
def herglotzControlLinear (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ) :
    Lp ℝ ⊤ μ →ₗ[ℝ] (jetIndex n → ℂ) where
  toFun f := fun s => ∫ t, ((f t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ
  map_add' f g := by
    funext s
    have hae : ∀ᵐ t ∂μ,
        (((f + g) t : ℝ) : ℂ) * cauchyJetKernel x n t s =
          ((f t : ℝ) : ℂ) * cauchyJetKernel x n t s +
            ((g t : ℝ) : ℂ) * cauchyJetKernel x n t s := by
      filter_upwards [Lp.coeFn_add f g] with t ht
      rw [ht]
      simp only [Pi.add_apply]
      push_cast
      ring
    rw [integral_congr_ae hae,
      integral_add (integrable_reweighted_cauchyJetKernel μ x hne n f s)
        (integrable_reweighted_cauchyJetKernel μ x hne n g s)]
    rfl
  map_smul' r f := by
    funext s
    have hae : ∀ᵐ t ∂μ,
        (((r • f) t : ℝ) : ℂ) * cauchyJetKernel x n t s =
          (r : ℂ) * (((f t : ℝ) : ℂ) * cauchyJetKernel x n t s) := by
      filter_upwards [Lp.coeFn_smul r f] with t ht
      rw [ht]
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [integral_congr_ae hae, integral_const_mul]
    rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem herglotzControlLinear_apply (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (f : Lp ℝ ⊤ μ) (s : jetIndex n) :
    herglotzControlLinear μ x hne n f s =
      ∫ t, ((f t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ :=
  rfl

/-- The total operator bound of the control map. -/
def herglotzControlBound (μ : Measure ℝ) (x : ι → ℂ) (n : ι → ℕ) : ℝ :=
  (∑ s : jetIndex n, cauchyJetKernelBound x n s) * μ.real Set.univ

omit [DecidableEq ι] in
/-- **The Cauchy-jet control map is bounded.**  Each component is dominated by the uniform kernel
bound times the measure mass, uniformly in the reweighting. -/
theorem norm_herglotzControlLinear_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ) (f : Lp ℝ ⊤ μ) :
    ‖herglotzControlLinear μ x hne n f‖ ≤ herglotzControlBound μ x n * ‖f‖ := by
  have hmass : 0 ≤ μ.real Set.univ := measureReal_nonneg
  have hCnonneg : 0 ≤ herglotzControlBound μ x n := by
    apply mul_nonneg _ hmass
    exact Finset.sum_nonneg fun s _ => cauchyJetKernelBound_nonneg x n s
  apply pi_norm_le_iff_of_nonneg (mul_nonneg hCnonneg (norm_nonneg f)) |>.mpr
  intro s
  have hcoord := norm_integral_Lp_top_mul_le μ f
    (fun t => cauchyJetKernel x n t s) (norm_cauchyJetKernel_le x hne n s)
  refine le_trans hcoord ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
  rw [herglotzControlBound]
  apply mul_le_mul_of_nonneg_right _ hmass
  exact Finset.single_le_sum
    (fun s' _ => cauchyJetKernelBound_nonneg x n s') (Finset.mem_univ s)

/-- The Cauchy-jet control map as a continuous linear map on bounded reweightings. -/
def herglotzControl (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ) :
    Lp ℝ ⊤ μ →L[ℝ] (jetIndex n → ℂ) :=
  LinearMap.mkContinuous (herglotzControlLinear μ x hne n)
    (herglotzControlBound μ x n)
    (norm_herglotzControlLinear_le μ x hne n)

omit [DecidableEq ι] in
@[simp]
theorem herglotzControl_apply (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0) (n : ι → ℕ)
    (f : Lp ℝ ⊤ μ) (s : jetIndex n) :
    herglotzControl μ x hne n f s =
      ∫ t, ((f t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ :=
  rfl

end

end GaloisForLFunctions.HTGeometry
