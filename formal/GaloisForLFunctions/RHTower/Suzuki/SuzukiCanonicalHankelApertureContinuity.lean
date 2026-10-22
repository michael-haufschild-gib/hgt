import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma46
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Strong continuity of Suzuki's sharp aperture

This module supplies the fixed-window infrastructure needed for Suzuki's Appendix Lemma `ad2`.
On `L²(0,B)`, multiplication by `1_{x ≤ a}` is a contraction and depends strongly continuously
on the aperture `a`.  Operator-norm continuity is false, so the proof works at the application
level and uses finite-measure Vitali convergence.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-- The part of the fixed carrier `(0,B)` lying below aperture `a`. -/
def suzukiApertureSet (a B : ℝ) : Set (ClosedInterval 0 B) :=
  {x | (x : ℝ) ≤ a}

theorem measurableSet_suzukiApertureSet (a B : ℝ) :
    MeasurableSet (suzukiApertureSet a B) := by
  exact measurableSet_Iic.preimage measurable_subtype_coe

/-- Sharp aperture projection on the fixed carrier `L²(0,B)`. -/
def suzukiApertureCutoff (a B : ℝ) :
    IntervalL2 0 B →L[ℂ] IntervalL2 0 B :=
  lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ)
    (volume : Measure (ClosedInterval 0 B)) 2
    (suzukiApertureSet a B) (measurableSet_suzukiApertureSet a B)

theorem suzukiApertureCutoff_ae (a B : ℝ) (f : IntervalL2 0 B) :
    suzukiApertureCutoff a B f =ᵐ[volume]
      (suzukiApertureSet a B).indicator f := by
  exact lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ)
    (volume : Measure (ClosedInterval 0 B)) 2
    (suzukiApertureSet a B) (measurableSet_suzukiApertureSet a B) f

theorem norm_suzukiApertureCutoff_apply_le (a B : ℝ) (f : IntervalL2 0 B) :
    ‖suzukiApertureCutoff a B f‖ ≤ ‖f‖ := by
  change ‖lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ)
      (volume : Measure (ClosedInterval 0 B)) 2
      (suzukiApertureSet a B) (measurableSet_suzukiApertureSet a B)
      (LpToLpRestrictCLM (ClosedInterval 0 B) ℂ ℂ
        (volume : Measure (ClosedInterval 0 B)) 2
        (suzukiApertureSet a B) f)‖ ≤ ‖f‖
  rw [show lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ)
      (volume : Measure (ClosedInterval 0 B)) 2
      (suzukiApertureSet a B) (measurableSet_suzukiApertureSet a B)
      (LpToLpRestrictCLM (ClosedInterval 0 B) ℂ ℂ
        (volume : Measure (ClosedInterval 0 B)) 2
        (suzukiApertureSet a B) f) =
      lpExtendByZero (F := ℂ) (volume : Measure (ClosedInterval 0 B)) 2
        (suzukiApertureSet a B) (measurableSet_suzukiApertureSet a B)
        (LpToLpRestrictCLM (ClosedInterval 0 B) ℂ ℂ
          (volume : Measure (ClosedInterval 0 B)) 2
          (suzukiApertureSet a B) f) by rfl,
    norm_lpExtendByZero]
  exact norm_Lp_toLp_restrict_le (suzukiApertureSet a B) f

theorem norm_suzukiApertureCutoff_le_one (a B : ℝ) :
    ‖suzukiApertureCutoff a B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_suzukiApertureCutoff_apply_le a B f

/-- Sharp aperture projections are strongly continuous.  This deliberately does not assert the
false operator-norm continuity of the projection family. -/
theorem continuous_suzukiApertureCutoff_apply (B : ℝ) (f : IntervalL2 0 B) :
    Continuous fun a : ℝ => suzukiApertureCutoff a B f := by
  rw [continuous_iff_seqContinuous]
  intro u a hu
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  let F : ℕ → ClosedInterval 0 B → ℂ := fun n =>
    (suzukiApertureSet (u n) B).indicator f
  let G : ClosedInterval 0 B → ℂ :=
    (suzukiApertureSet a B).indicator f
  have hF (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    (Lp.memLp f).1.indicator (measurableSet_suzukiApertureSet (u n) B)
  have hG : MemLp G 2 volume :=
    (Lp.memLp f).indicator (measurableSet_suzukiApertureSet a B)
  have hui : UnifIntegrable F 2 volume := by
    intro epsilon hepsilon
    obtain ⟨delta, hdelta, hbound⟩ :=
      (unifIntegrable_const (ι := ℕ) (p := (2 : ℝ≥0∞)) (by norm_num)
        (by norm_num) (Lp.memLp f)) hepsilon
    refine ⟨delta, hdelta, fun n s hs hmeasure => ?_⟩
    calc
      eLpNorm (s.indicator (F n)) 2 volume =
          eLpNorm ((s ∩ suzukiApertureSet (u n) B).indicator f) 2 volume := by
        change eLpNorm (s.indicator ((suzukiApertureSet (u n) B).indicator f))
          2 volume = _
        rw [Set.indicator_indicator]
      _ ≤ eLpNorm (s.indicator f) 2 volume := by
        apply eLpNorm_mono
        intro x
        by_cases hxs : x ∈ s
        · by_cases hxa : x ∈ suzukiApertureSet (u n) B <;> simp [hxs, hxa]
        · simp [hxs]
      _ ≤ ENNReal.ofReal epsilon := hbound n s hs hmeasure
  have hmp : MeasurePreserving ((↑) : ClosedInterval 0 B → ℝ)
      (volume : Measure (ClosedInterval 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hne : ∀ᵐ x : ClosedInterval 0 B ∂volume, (x : ℝ) ≠ a :=
    hmp.quasiMeasurePreserving.ae
      (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne a))
  have hpoint : ∀ᵐ x : ClosedInterval 0 B ∂volume,
      Tendsto (fun n => F n x) atTop (𝓝 (G x)) := by
    filter_upwards [hne] with x hx
    rcases lt_or_gt_of_ne hx with hxa | hax
    · have hevent : ∀ᶠ n in atTop, (x : ℝ) < u n :=
        (tendsto_order.mp hu).1 (x : ℝ) hxa
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      filter_upwards [hevent] with n hn
      simp [F, G, suzukiApertureSet, hn.le, hxa.le]
    · have hevent : ∀ᶠ n in atTop, u n < (x : ℝ) :=
        (tendsto_order.mp hu).2 (x : ℝ) hax
      refine (tendsto_congr' ?_).mpr tendsto_const_nhds
      filter_upwards [hevent] with n hn
      simp [F, G, suzukiApertureSet, not_le.mpr hn, not_le.mpr hax]
  have hLp : Tendsto (fun n => eLpNorm (F n - G) 2 volume) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) hF hG hui hpoint
  have hnorm : (fun n => eLpNorm
      ((suzukiApertureCutoff (u n) B f : ClosedInterval 0 B → ℂ) -
        (suzukiApertureCutoff a B f : ClosedInterval 0 B → ℂ)) 2 volume) =
      (fun n => eLpNorm (F n - G) 2 volume) := by
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [suzukiApertureCutoff_ae (u n) B f,
      suzukiApertureCutoff_ae a B f] with x hleft hright
    simp only [Pi.sub_apply]
    rw [hleft, hright]
  change Tendsto (fun n => eLpNorm
      ((suzukiApertureCutoff (u n) B f : ClosedInterval 0 B → ℂ) -
        (suzukiApertureCutoff a B f : ClosedInterval 0 B → ℂ)) 2 volume) atTop (𝓝 0)
  rw [hnorm]
  exact hLp

/-- Strong continuity persists when both aperture and input vary continuously. -/
theorem continuous_suzukiApertureCutoff_apply₂
    (B : ℝ) {u : ℝ → IntervalL2 0 B} (hu : Continuous u) :
    Continuous fun a : ℝ => suzukiApertureCutoff a B (u a) := by
  rw [continuous_iff_seqContinuous]
  intro v a hv
  have huT : Tendsto (fun n => u (v n)) atTop (𝓝 (u a)) :=
    hu.seqContinuous hv
  have hdiff : Tendsto (fun n => u (v n) - u a) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => u a) atTop (𝓝 (u a)) :=
      tendsto_const_nhds
    simpa only [sub_self] using huT.sub hconst
  have hfirstNorm : Tendsto (fun n =>
      ‖suzukiApertureCutoff (v n) B (u (v n) - u a)‖) atTop (𝓝 0) := by
    apply squeeze_zero
    · exact fun _ => norm_nonneg _
    · exact fun n => norm_suzukiApertureCutoff_apply_le (v n) B (u (v n) - u a)
    · simpa only [norm_zero] using hdiff.norm
  have hfirst : Tendsto (fun n =>
      suzukiApertureCutoff (v n) B (u (v n) - u a)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hfirstNorm
  have hsecond : Tendsto (fun n => suzukiApertureCutoff (v n) B (u a))
      atTop (𝓝 (suzukiApertureCutoff a B (u a))) :=
    (continuous_suzukiApertureCutoff_apply B (u a)).seqContinuous hv
  have hsum := hfirst.add hsecond
  have hsum' : Tendsto (fun n =>
      suzukiApertureCutoff (v n) B (u (v n) - u a) +
        suzukiApertureCutoff (v n) B (u a)) atTop
      (𝓝 (suzukiApertureCutoff a B (u a))) := by
    simpa only [zero_add] using hsum
  change Tendsto (fun n => suzukiApertureCutoff (v n) B (u (v n)))
    atTop (𝓝 (suzukiApertureCutoff a B (u a)))
  convert hsum' using 1
  ext n
  rw [← map_add]
  simp

theorem continuousAt_suzukiApertureCutoff_apply₂
    (B a : ℝ) {u : ℝ → IntervalL2 0 B} (hu : ContinuousAt u a) :
    ContinuousAt (fun b : ℝ => suzukiApertureCutoff b B (u b)) a := by
  have hconst : ContinuousAt (fun _ : ℝ => u a) a := continuousAt_const
  have hdiff : Tendsto (fun b => u b - u a) (𝓝 a) (𝓝 0) := by
    have hdiff' := hu.sub hconst
    change Tendsto (fun b => u b - u a) (𝓝 a) (𝓝 (u a - u a)) at hdiff'
    simpa only [sub_self] using hdiff'
  have hfirstNorm : Tendsto (fun b =>
      ‖suzukiApertureCutoff b B (u b - u a)‖) (𝓝 a) (𝓝 0) := by
    apply squeeze_zero
    · exact fun _ => norm_nonneg _
    · exact fun b => norm_suzukiApertureCutoff_apply_le b B (u b - u a)
    · simpa only [norm_zero] using hdiff.norm
  have hfirst : Tendsto (fun b =>
      suzukiApertureCutoff b B (u b - u a)) (𝓝 a) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hfirstNorm
  have hsecond : Tendsto (fun b => suzukiApertureCutoff b B (u a))
      (𝓝 a) (𝓝 (suzukiApertureCutoff a B (u a))) :=
    (continuous_suzukiApertureCutoff_apply B (u a)).continuousAt
  have hsum := hfirst.add hsecond
  have hsum' : Tendsto (fun b =>
      suzukiApertureCutoff b B (u b - u a) +
        suzukiApertureCutoff b B (u a)) (𝓝 a)
      (𝓝 (suzukiApertureCutoff a B (u a))) := by
    simpa only [zero_add] using hsum
  change Tendsto (fun b => suzukiApertureCutoff b B (u b))
    (𝓝 a) (𝓝 (suzukiApertureCutoff a B (u a)))
  convert hsum' using 1
  ext b
  rw [← map_add]
  simp

end RHTower
