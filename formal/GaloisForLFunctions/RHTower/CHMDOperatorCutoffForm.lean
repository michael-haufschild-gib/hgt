import GaloisForLFunctions.RHTower.CHMDArchMomentPullback

/-!
# Spatial cutoff multipliers on the complete archimedean form graph

First-moment endpoint admission removes the bounded-source restriction from
cutoff admission. The same moment space supplies the bounded commutator.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

theorem integral_archMoment (f : ℝ × ℝ → ℝ) :
    (∫ e, f e ∂archMomentMeasure) = ∫ e, e.1 * f e ∂archMeasure := by
  rw [archMomentMeasure, integral_weighted archBase measurable_archMomentWeight
    archMomentWeight_nonneg, archMeasure,
    integral_weighted archBase measurable_archWeight archWeight_nonneg_ae]
  apply integral_congr_ae
  filter_upwards [] with e
  unfold archMomentWeight
  ring

theorem integrable_archMoment_iff (f : ℝ × ℝ → ℝ) :
    Integrable f archMomentMeasure ↔ Integrable (fun e => e.1 * f e) archMeasure := by
  rw [archMomentMeasure, integrable_weighted_iff archBase measurable_archMomentWeight
    archMomentWeight_nonneg, archMeasure,
    integrable_weighted_iff archBase measurable_archWeight archWeight_nonneg_ae]
  apply integrable_congr
  filter_upwards [] with e
  unfold archMomentWeight
  ring

theorem cutoff_norm_le_one (n : ℕ) (x : ℝ) : ‖cutoff n x‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (cutoff_nonneg n x)]
  exact cutoff_le_one n x

def massCutoff (n : ℕ) : MassSpace →L[ℝ] MassSpace :=
  lpBoundedMulCLM (cutoff_contDiff n).continuous.measurable (by norm_num) (cutoff_norm_le_one n)

theorem massCutoff_ae (n : ℕ) (u : MassSpace) :
    massCutoff n u =ᵐ[massMeasure] fun x => cutoff n x * u x :=
  lpBoundedMulCLM_coeFn _ _ _ u

theorem massCutoff_symmetric (n : ℕ) (u v : MassSpace) :
    ⟪massCutoff n u, v⟫_ℝ = ⟪u, massCutoff n v⟫_ℝ :=
  lpBoundedMulCLM_inner_real _ _ _ (fun _ => rfl) u v

theorem massCutoff_tendsto (u : MassSpace) :
    Tendsto (fun n => massCutoff n u) atTop (𝓝 u) := by
  have h := tendsto_lpBoundedMulCLM_apply (μ := massMeasure)
    (fun n => (cutoff_contDiff n).continuous.measurable) measurable_const
    (by norm_num : (0 : ℝ) ≤ 1) cutoff_norm_le_one
    (fun _ : ℝ => by norm_num : ∀ _ : ℝ, ‖(1 : ℝ)‖ ≤ 1) cutoff_tendsto u
  have he : lpBoundedMulCLM (μ := massMeasure) (p := 2)
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ)))
      (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by norm_num) u = u := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (μ := massMeasure) (p := 2)
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ)))
      (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by norm_num) u] with x hx
    simpa using hx
  rw [he] at h
  exact h

def cutoffSlope (n : ℕ) (e : ℝ × ℝ) : ℝ :=
  (cutoff n (left e) - cutoff n (right e)) / e.1

theorem measurable_cutoffSlope (n : ℕ) : Measurable (cutoffSlope n) := by
  unfold cutoffSlope left right
  exact (((cutoff_contDiff n).continuous.measurable.comp measurable_snd).sub
    ((cutoff_contDiff n).continuous.measurable.comp
      (measurable_snd.add measurable_fst))).div measurable_fst

theorem cutoffSlope_bound (n : ℕ) (e : ℝ × ℝ) : ‖cutoffSlope n e‖ ≤ cutoffLipschitz := by
  by_cases ht : e.1 = 0
  · simp [cutoffSlope, ht]
  rw [cutoffSlope, Real.norm_eq_abs, abs_div, div_le_iff₀ (abs_pos.mpr ht)]
  have h := cutoff_difference_le n (left e) (right e)
  simpa only [left, right, sub_add_cancel_left, abs_neg] using h

theorem cutoffSlope_tendsto (e : ℝ × ℝ) : Tendsto (fun n => cutoffSlope n e) atTop (𝓝 0) := by
  simpa only [cutoffSlope, sub_self, zero_div] using
    ((cutoff_tendsto (left e)).sub (cutoff_tendsto (right e))).div_const e.1

def cutoffSlopeOperator (n : ℕ) : Lp ℝ 2 archMomentMeasure →L[ℝ] Lp ℝ 2 archMomentMeasure :=
  lpBoundedMulCLM (measurable_cutoffSlope n) cutoffLipschitz.coe_nonneg (cutoffSlope_bound n)

theorem cutoffSlopeOperator_ae (n : ℕ) (u : Lp ℝ 2 archMomentMeasure) :
    cutoffSlopeOperator n u =ᵐ[archMomentMeasure] fun e => cutoffSlope n e * u e :=
  lpBoundedMulCLM_coeFn _ _ _ u

theorem cutoffSlopeOperator_tendsto (u : Lp ℝ 2 archMomentMeasure) :
    Tendsto (fun n => cutoffSlopeOperator n u) atTop (𝓝 0) := by
  have h := tendsto_lpBoundedMulCLM_apply (μ := archMomentMeasure)
    measurable_cutoffSlope measurable_const cutoffLipschitz.coe_nonneg cutoffSlope_bound
    (fun _ : ℝ × ℝ => by simp : ∀ _ : ℝ × ℝ, ‖(0 : ℝ)‖ ≤ cutoffLipschitz)
    cutoffSlope_tendsto u
  have he : lpBoundedMulCLM (μ := archMomentMeasure) (p := 2)
      (measurable_const : Measurable (fun _ : ℝ × ℝ => (0 : ℝ)))
      cutoffLipschitz.coe_nonneg (fun _ => by simp) u = 0 := by
    apply Lp.ext
    filter_upwards [lpBoundedMulCLM_coeFn (μ := archMomentMeasure) (p := 2)
      (measurable_const : Measurable (fun _ : ℝ × ℝ => (0 : ℝ)))
      cutoffLipschitz.coe_nonneg (fun _ => by simp) u,
      Lp.coeFn_zero ℝ 2 archMomentMeasure] with e he hz
    simp only [he, hz, Pi.zero_apply, zero_mul]
  exact he ▸ h

theorem cutoff_difference_sq_le (n : ℕ) {e : ℝ × ℝ} (ht : 0 < e.1) :
    (cutoff n (left e) - cutoff n (right e)) ^ 2 ≤ (cutoffLipschitz : ℝ) * e.1 := by
  have h1 : |cutoff n (left e) - cutoff n (right e)| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [cutoff_nonneg n (left e), cutoff_nonneg n (right e),
      cutoff_le_one n (left e), cutoff_le_one n (right e)]
  have h2 := cutoff_difference_le n (left e) (right e)
  simp only [left, right, sub_add_cancel_left, abs_neg, abs_of_pos ht] at h2
  change |cutoff n (left e) - cutoff n (right e)| ≤ (cutoffLipschitz : ℝ) * e.1 at h2
  nlinarith [abs_nonneg (cutoff n (left e) - cutoff n (right e)),
    sq_abs (cutoff n (left e) - cutoff n (right e))]

theorem memLp_cutoff_correction (n : ℕ) (u : MassSpace) :
    MemLp (fun e => (cutoff n (left e) - cutoff n (right e)) * u (right e)) 2 archMeasure := by
  have hu := (Lp.stronglyMeasurable u).measurable
  have hc := (cutoff_contDiff n).continuous.measurable
  have hm : Measurable (fun e : ℝ × ℝ =>
      (cutoff n (left e) - cutoff n (right e)) * u (right e)) :=
    ((hc.comp measurable_snd).sub (hc.comp (measurable_snd.add measurable_fst))).mul
      (hu.comp (measurable_snd.add measurable_fst))
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hi := (integrable_archMoment_iff _).mp (memLp_archMoment_right u).integrable_sq
  refine (hi.const_mul (cutoffLipschitz : ℝ)).mono'
    (hm.pow_const 2).aestronglyMeasurable ?_
  have ht : ∀ᵐ e ∂archMeasure, 0 < e.1 :=
    (withDensity_absolutelyContinuous archBase _).ae_le archBase_fst_pos
  filter_upwards [ht] with e he
  rw [Real.norm_of_nonneg (sq_nonneg _), mul_pow]
  exact (mul_le_mul_of_nonneg_right (cutoff_difference_sq_le n he) (sq_nonneg (u (right e)))).trans_eq
    (by dsimp; ring)

theorem memLp_cutoff_arch (n : ℕ) (p : ArchGraph) :
    MemLp (difference (fun x => cutoff n x * p.val.fst x)) 2 archMeasure := by
  have h0 := memLp_mul_of_bound (μ := archMeasure) (p := 2)
    ((cutoff_contDiff n).continuous.measurable.comp measurable_snd)
    (by norm_num : (0 : ℝ) ≤ 1) (fun e => cutoff_norm_le_one n (left e)) p.val.snd
  have hp : p.val.snd =ᵐ[archMeasure] difference p.val.fst := p.property
  have h1 := h0.ae_eq (hp.mono fun e he => congrArg (fun y => cutoff n (left e) * y) he)
  refine (h1.add (memLp_cutoff_correction n p.val.fst)).ae_eq ?_
  filter_upwards [] with e
  simp only [Pi.add_apply, difference]
  ring

def archCutoff (n : ℕ) (p : ArchGraph) : ArchGraph :=
  ofFunction massMeasure archMeasure left right nonsingular_arch_left nonsingular_arch_right
    (fun x => cutoff n x * p.val.fst x)
    (memLp_mul_of_bound (cutoff_contDiff n).continuous.measurable
      (by norm_num) (cutoff_norm_le_one n) p.val.fst) (memLp_cutoff_arch n p)

theorem archCutoff_source (n : ℕ) (p : ArchGraph) :
    archSourceMap (archCutoff n p) = massCutoff n (archSourceMap p) := rfl

def archCutoffCommutator (n : ℕ) : MassSpace →L[ℝ] MassSpace :=
  archMomentLeft.adjoint.comp ((cutoffSlopeOperator n).comp archMomentRight) -
    archMomentRight.adjoint.comp ((cutoffSlopeOperator n).comp archMomentLeft)

theorem archCutoffCommutator_tendsto (u : MassSpace) :
    Tendsto (fun n => archCutoffCommutator n u) atTop (𝓝 0) := by
  have hl := (archMomentLeft.adjoint.continuous.tendsto 0).comp
    (cutoffSlopeOperator_tendsto (archMomentRight u))
  have hr := (archMomentRight.adjoint.continuous.tendsto 0).comp
    (cutoffSlopeOperator_tendsto (archMomentLeft u))
  change Tendsto (fun n => archMomentLeft.adjoint (cutoffSlopeOperator n (archMomentRight u)) -
    archMomentRight.adjoint (cutoffSlopeOperator n (archMomentLeft u))) atTop (𝓝 0)
  simpa only [Function.comp_def, map_zero, sub_zero] using hl.sub hr

end RHTower.CHMDDoobGraph
