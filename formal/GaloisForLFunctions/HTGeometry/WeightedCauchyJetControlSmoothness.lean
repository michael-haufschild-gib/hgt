import GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaRowEvaluationSmoothness
import GaloisForLFunctions.HTGeometry.WeightedJetControl

/-!
# Smooth weighted Cauchy-jet control on an arbitrary base measure

The compact-patch transversality argument needs the bounded-density Cauchy control to vary smoothly
with its finite upper-half-plane node packet.  The base Herglotz measure need not be finite: an
integrable positive Nevanlinna density supplies all required `L¹` bounds.

We reuse the smooth compactified Cauchy kernel, multiply it by the integrable density, embed it in
`L¹(μ)`, and pair it against the original `L∞(μ)` parameter space.  Thus no identification of
`L∞` spaces for equivalent measures is needed.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set
open scoped ENNReal OnePoint

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Multiplying a compactified continuous kernel by an integrable real density produces an
integrable kernel over the original base measure. -/
theorem integrable_weight_smul_projectiveContinuousMap
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (f : C(OnePoint ℝ, V)) :
    Integrable (fun t : ℝ => w t • f (t : OnePoint ℝ)) μ := by
  apply Integrable.mono' (hw.norm.const_mul ‖f‖)
  · exact hw.aestronglyMeasurable.smul
      (f.continuous.comp continuous_coe).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (abs_nonneg _)

/-- Continuous real-linear weighted embedding of compactified continuous kernels into `L¹(μ)`. -/
def weightedProjectiveContinuousMapToLp
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ) :
    C(OnePoint ℝ, V) →L[ℝ] Lp V 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        (integrable_weight_smul_projectiveContinuousMap μ w hw f).toLp
          (fun t : ℝ => w t • f (t : OnePoint ℝ))
      map_add' := by
        intro f g
        apply Lp.ext fun_prop
        filter_upwards
          [(integrable_weight_smul_projectiveContinuousMap μ w hw (f + g)).coeFn_toLp,
           (integrable_weight_smul_projectiveContinuousMap μ w hw f).coeFn_toLp,
           (integrable_weight_smul_projectiveContinuousMap μ w hw g).coeFn_toLp]
            with t ht htf htg
        rw [ht, htf, htg]
        simp [smul_add]
      map_smul' := by
        intro c f
        apply Lp.ext fun_prop
        filter_upwards
          [(integrable_weight_smul_projectiveContinuousMap μ w hw (c • f)).coeFn_toLp,
           (integrable_weight_smul_projectiveContinuousMap μ w hw f).coeFn_toLp]
            with t ht htf
        rw [ht, htf]
        simp [smul_smul] }
    (∫ t, |w t| ∂μ)
    (fun f => by
      rw [L1.norm_eq_integral_norm]
      have hdom : ∀ᵐ t ∂μ,
          ‖w t • f (t : OnePoint ℝ)‖ ≤ |w t| * ‖f‖ := by
        filter_upwards [] with t
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (abs_nonneg _)
      calc
        ∫ t, ‖w t • f (t : OnePoint ℝ)‖ ∂μ
            ≤ ∫ t, |w t| * ‖f‖ ∂μ := by
              exact integral_mono_ae
                (integrable_weight_smul_projectiveContinuousMap μ w hw f).norm
                (hw.abs.mul_const ‖f‖) hdom
        _ = (∫ t, |w t| ∂μ) * ‖f‖ := by rw [integral_mul_const])

/-- The complete Cauchy-jet kernel as a continuous function on the compactified real line. -/
def projectiveCauchyJetBanachMap
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (z : ι → ℂ) :
    C(OnePoint ℝ, (Σ i, Fin (n i)) → ℂ) :=
  projectiveContinuousMapPiCLM fun s =>
    (projectiveResolventBanach (z s.1)) ^ (s.2.1 + 1)

/-- On a strict upper packet, the continuous Banach kernel is the literal projective Cauchy-jet
column. -/
theorem projectiveCauchyJetBanachMap_apply
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (z : ι → ℂ)
    (hz : ∀ i, 0 < (z i).im) (t : OnePoint ℝ) :
    projectiveCauchyJetBanachMap n z t = projectiveCauchyJetColumn z n t := by
  funext s
  simp only [projectiveCauchyJetBanachMap, projectiveContinuousMapPiCLM_apply,
    ContinuousMap.pow_apply, projectiveCauchyJetColumn]
  rw [projectiveResolventBanach_apply (z s.1) (hz s.1)]

/-- The compactified Cauchy-jet kernel varies smoothly in sup norm on the strict upper packet
locus. -/
theorem contDiffOn_projectiveCauchyJetBanachMap
    {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    ContDiffOn ℝ ⊤ (projectiveCauchyJetBanachMap n)
      (nevanlinnaUpperPacketSet id) := by
  have hpi : ContDiffOn ℝ ⊤
      (fun z : ι → ℂ => fun s : Σ i, Fin (n i) =>
        (projectiveResolventBanach (z s.1)) ^ (s.2.1 + 1))
      (nevanlinnaUpperPacketSet id) := by
    apply contDiffOn_pi'
    intro s
    have hz : ContDiff ℝ ⊤ (fun z : ι → ℂ => z s.1) :=
      contDiff_apply ℝ ℂ s.1
    exact (contDiffOn_projectiveCauchyPowerBanach s.2.1).comp hz.contDiffOn
      (fun z hz => by simpa [nevanlinnaUpperPacketSet] using hz s.1)
  simpa only [projectiveCauchyJetBanachMap, Function.comp_apply] using!
    (projectiveContinuousMapPiCLM.restrictScalars ℝ).contDiff.comp_contDiffOn hpi

/-- Smooth weighted Cauchy control on the original base-measure `L∞` space. -/
def weightedCauchyJetSmoothControl
    {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (n : ι → ℕ) (z : ι → ℂ) :
    Lp ℝ ⊤ μ →L[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  linftyLpKernelControl μ
    (weightedProjectiveContinuousMapToLp μ w hw (projectiveCauchyJetBanachMap n z))

/-- The weighted Cauchy control varies smoothly in operator norm. -/
theorem contDiffOn_weightedCauchyJetSmoothControl
    {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ) (n : ι → ℕ) :
    ContDiffOn ℝ ⊤ (weightedCauchyJetSmoothControl μ w hw n)
      (nevanlinnaUpperPacketSet id) := by
  exact (linftyLpKernelControl μ).contDiff.comp_contDiffOn
    ((weightedProjectiveContinuousMapToLp μ w hw).contDiff.comp_contDiffOn
      (contDiffOn_projectiveCauchyJetBanachMap n))

/-- Pointwise representative of the weighted compactified-kernel embedding. -/
theorem weightedProjectiveContinuousMapToLp_coeFn
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (f : C(OnePoint ℝ, V)) :
    weightedProjectiveContinuousMapToLp μ w hw f =ᵐ[μ]
      fun t : ℝ => w t • f (t : OnePoint ℝ) := by
  exact (integrable_weight_smul_projectiveContinuousMap μ w hw f).coeFn_toLp

/-- On strict upper packets, the smooth control is exactly the existing weighted Cauchy-jet
control, not an abstract surrogate. -/
theorem weightedCauchyJetSmoothControl_eq_weightedJetControl
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (n : ι → ℕ) (z : ι → ℂ) (hz : ∀ i, 0 < (z i).im) :
    weightedCauchyJetSmoothControl μ w hw n z =
      weightedJetControl μ w hw z (fun i => ne_of_gt (hz i)) n := by
  apply ContinuousLinearMap.ext
  intro u
  funext s
  rw [weightedCauchyJetSmoothControl, linftyLpKernelControl_apply,
    linftyLpPairingRight_apply, weightedJetControl_apply]
  apply integral_congr_ae
  filter_upwards
    [weightedProjectiveContinuousMapToLp_coeFn μ w hw
      (projectiveCauchyJetBanachMap n z)] with t ht
  rw [ht, projectiveCauchyJetBanachMap_apply n z hz]
  simp [projectiveCauchyJetColumn, projectiveCauchyPower, cauchyJetKernel,
    smul_eq_mul]

end

end GaloisForLFunctions.HTGeometry
