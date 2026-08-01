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

omit [CompleteSpace V] in
/-- Multiplying a compactified continuous kernel by an integrable real density produces an
integrable kernel over the original base measure. -/
theorem integrable_weight_smul_projectiveContinuousMap
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (f : C(OnePoint ℝ, V)) :
    Integrable (fun t : ℝ => w t • f (t : OnePoint ℝ)) μ := by
  apply Integrable.mono' (hw.norm.const_mul ‖f‖)
  · exact hw.aestronglyMeasurable.smul
      (f.continuous.comp OnePoint.continuous_coe).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |w t| * ‖f (t : OnePoint ℝ)‖ ≤ |w t| * ‖f‖ :=
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (abs_nonneg _)
      _ = ‖f‖ * |w t| := mul_comm _ _

omit [CompleteSpace V] in
/-- `L¹` packaging of the weighted compactified continuous kernel. -/
theorem memLp_one_weight_smul_projectiveContinuousMap
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (f : C(OnePoint ℝ, V)) :
    MemLp (fun t : ℝ => w t • f (t : OnePoint ℝ)) 1 μ :=
  memLp_one_iff_integrable.mpr
    (integrable_weight_smul_projectiveContinuousMap μ w hw f)

/-- Continuous real-linear weighted embedding of compactified continuous kernels into `L¹(μ)`. -/
def weightedProjectiveContinuousMapToLp
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ) :
    C(OnePoint ℝ, V) →L[ℝ] Lp V 1 μ :=
  LinearMap.mkContinuous
    { toFun := fun f =>
        (memLp_one_weight_smul_projectiveContinuousMap μ w hw f).toLp
          (fun t : ℝ => w t • f (t : OnePoint ℝ))
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards
          [(memLp_one_weight_smul_projectiveContinuousMap μ w hw (f + g)).coeFn_toLp,
           (memLp_one_weight_smul_projectiveContinuousMap μ w hw f).coeFn_toLp,
           (memLp_one_weight_smul_projectiveContinuousMap μ w hw g).coeFn_toLp,
           Lp.coeFn_add
             ((memLp_one_weight_smul_projectiveContinuousMap μ w hw f).toLp
               (fun t : ℝ => w t • f (t : OnePoint ℝ)))
             ((memLp_one_weight_smul_projectiveContinuousMap μ w hw g).toLp
               (fun t : ℝ => w t • g (t : OnePoint ℝ)))]
            with t ht htf htg hadd
        rw [ht, hadd]
        simp only [Pi.add_apply]
        rw [htf, htg]
        simp [smul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards
          [(memLp_one_weight_smul_projectiveContinuousMap μ w hw (c • f)).coeFn_toLp,
           (memLp_one_weight_smul_projectiveContinuousMap μ w hw f).coeFn_toLp,
           Lp.coeFn_smul c
             ((memLp_one_weight_smul_projectiveContinuousMap μ w hw f).toLp
               (fun t : ℝ => w t • f (t : OnePoint ℝ)))]
            with t ht htf hsmul
        rw [ht]
        have hsmul' :
            ⇑(c • (memLp_one_weight_smul_projectiveContinuousMap μ w hw f).toLp
                (fun t : ℝ => w t • f (t : OnePoint ℝ))) t =
              (c • ⇑((memLp_one_weight_smul_projectiveContinuousMap μ w hw f).toLp
                (fun t : ℝ => w t • f (t : OnePoint ℝ)))) t := by
          simpa only [RingHom.id_apply] using hsmul
        change w t • (c • f) (t : OnePoint ℝ) =
          ⇑(c • (memLp_one_weight_smul_projectiveContinuousMap μ w hw f).toLp
            (fun t : ℝ => w t • f (t : OnePoint ℝ))) t
        rw [hsmul']
        simp only [Pi.smul_apply]
        rw [htf]
        simp [smul_smul, mul_comm] }
    (∫ t, |w t| ∂μ)
    (fun f => by
      change ‖(memLp_one_weight_smul_projectiveContinuousMap μ w hw f).toLp
        (fun t : ℝ => w t • f (t : OnePoint ℝ))‖ ≤ _
      rw [L1.norm_eq_integral_norm]
      have hcoe :
          ⇑((memLp_one_weight_smul_projectiveContinuousMap μ w hw f).toLp
            (fun t : ℝ => w t • f (t : OnePoint ℝ))) =ᵐ[μ]
            fun t : ℝ => w t • f (t : OnePoint ℝ) :=
        (memLp_one_weight_smul_projectiveContinuousMap μ w hw f).coeFn_toLp
      have hnorm : ∀ᵐ t ∂μ,
          ‖((memLp_one_weight_smul_projectiveContinuousMap μ w hw f).toLp
            (fun t : ℝ => w t • f (t : OnePoint ℝ))) t‖ =
            ‖w t • f (t : OnePoint ℝ)‖ := by
        filter_upwards [hcoe] with t ht
        rw [ht]
      rw [integral_congr_ae hnorm]
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
    {ι : Type} [Fintype ι] (n : ι → ℕ) (z : ι → ℂ) :
    C(OnePoint ℝ, (Σ i, Fin (n i)) → ℂ) :=
  projectiveContinuousMapPiCLM fun s : Σ i, Fin (n i) =>
    (projectiveResolventBanach (z s.1)) ^ (s.2.1 + 1)

/-- On a strict upper packet, the continuous Banach kernel is the literal projective Cauchy-jet
column. -/
theorem projectiveCauchyJetBanachMap_apply
    {ι : Type} [Fintype ι] (n : ι → ℕ) (z : ι → ℂ)
    (hz : ∀ i, 0 < (z i).im) (t : OnePoint ℝ) :
    projectiveCauchyJetBanachMap n z t = projectiveCauchyJetColumn z n t := by
  funext s
  induction t using OnePoint.rec with
  | infty =>
      simp only [projectiveCauchyJetBanachMap, projectiveContinuousMapPiCLM_apply,
        ContinuousMap.pow_apply, projectiveCauchyJetColumn, projectiveCauchyPower_infty]
      rw [projectiveResolventBanach_apply (z s.1) (hz s.1)]
      simp
  | coe t =>
      simp [projectiveCauchyJetBanachMap, projectiveCauchyJetColumn,
        projectiveCauchyPower, projectiveResolventBanach_apply (z s.1) (hz s.1)]

/-- The compactified Cauchy-jet kernel varies smoothly in sup norm on the strict upper packet
locus. -/
theorem contDiffOn_projectiveCauchyJetBanachMap
    {ι : Type} [Fintype ι] (n : ι → ℕ) :
    ContDiffOn ℝ ⊤ (projectiveCauchyJetBanachMap n)
      (nevanlinnaUpperPacketSet (ι := ι) (fun z : ℂ => z)) := by
  have hpi : ContDiffOn ℝ ⊤
      (fun z : ι → ℂ => fun s : Σ i, Fin (n i) =>
        (projectiveResolventBanach (z s.1)) ^ (s.2.1 + 1))
      (nevanlinnaUpperPacketSet (ι := ι) (fun z : ℂ => z)) := by
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
    {ι : Type} [Fintype ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (n : ι → ℕ) (z : ι → ℂ) :
    Lp ℝ ⊤ μ →L[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  linftyLpKernelControl μ
    (weightedProjectiveContinuousMapToLp μ w hw (projectiveCauchyJetBanachMap n z))

/-- The weighted Cauchy control varies smoothly in operator norm. -/
theorem contDiffOn_weightedCauchyJetSmoothControl
    {ι : Type} [Fintype ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ) (n : ι → ℕ) :
    ContDiffOn ℝ ⊤ (weightedCauchyJetSmoothControl μ w hw n)
      (nevanlinnaUpperPacketSet (ι := ι) (fun z : ℂ => z)) := by
  exact (linftyLpKernelControl μ).contDiff.comp_contDiffOn
    ((weightedProjectiveContinuousMapToLp μ w hw).contDiff.comp_contDiffOn
      (contDiffOn_projectiveCauchyJetBanachMap n))

omit [CompleteSpace V] in
/-- Pointwise representative of the weighted compactified-kernel embedding. -/
theorem weightedProjectiveContinuousMapToLp_coeFn
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (f : C(OnePoint ℝ, V)) :
    weightedProjectiveContinuousMapToLp μ w hw f =ᵐ[μ]
      fun t : ℝ => w t • f (t : OnePoint ℝ) := by
  exact (memLp_one_weight_smul_projectiveContinuousMap μ w hw f).coeFn_toLp

/-- On strict upper packets, the smooth control is exactly the existing weighted Cauchy-jet
control, not an abstract surrogate. -/
theorem weightedCauchyJetSmoothControl_eq_weightedJetControl
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) (w : ℝ → ℝ) (hw : Integrable w μ)
    (n : ι → ℕ) (z : ι → ℂ) (hz : ∀ i, 0 < (z i).im) :
    weightedCauchyJetSmoothControl μ w hw n z =
      weightedJetControl μ w hw z (fun i => ne_of_gt (hz i)) n := by
  apply ContinuousLinearMap.ext
  intro u
  funext s
  rw [weightedCauchyJetSmoothControl, linftyLpKernelControl_apply,
    linftyLpPairingRight_apply, weightedJetControl_apply]
  have hint :
      (∫ t, (u t) •
        (weightedProjectiveContinuousMapToLp μ w hw
          (projectiveCauchyJetBanachMap n z)) t ∂μ) =
      ∫ t, fun s => ((u t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) *
        cauchyJetKernel z n t s ∂μ := by
    apply integral_congr_ae
    filter_upwards
      [weightedProjectiveContinuousMapToLp_coeFn μ w hw
        (projectiveCauchyJetBanachMap n z)] with t ht
    rw [ht, projectiveCauchyJetBanachMap_apply n z hz]
    funext s
    simp [cauchyJetColumn, cauchyJetKernel, inv_pow, mul_assoc]
  have hrhs : Integrable
      (fun t => fun s => ((u t : ℝ) : ℂ) * ((w t : ℝ) : ℂ) *
        cauchyJetKernel z n t s) μ := by
    rw [integrable_pi_iff]
    intro j
    exact integrable_weighted_cauchyJetKernel μ w hw z
      (fun i => ne_of_gt (hz i)) n u j
  have hcomm :=
    (ContinuousLinearMap.proj s :
      ((Σ i, Fin (n i)) → ℂ) →L[ℝ] ℂ).integral_comp_comm hrhs
  exact (congrFun hint s).trans hcomm.symm

end

end GaloisForLFunctions.HTGeometry
