import GaloisForLFunctions.RHTower.PaperThetaCutParametrix
import GaloisForLFunctions.RHTower.PaperThetaQuantileDerivative
import GaloisForLFunctions.RHTower.HedenmalmQuantileSliceMoment

/-! # Actual integrable derivatives on both compact theta branches

No spectral-domain hypothesis is needed on either closed half interval.
These are the literal quantile branches, including their endpoint traces.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

def leftClosedQuantileMode (z : ℂ) (t : ℝ) : ℂ :=
  closedQuantileMode (-z) (1-t)

theorem continuousOn_closedQuantileMode_right (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    ContinuousOn (closedQuantileMode z) (Icc c.val 1) := by
  have hi : ContinuousOn (flatModePullback z) (Ioo c.val 1) := by
    intro t ht
    exact (differentiableAt_pullback z ⟨t, c.property.1.trans ht.1, ht.2⟩).continuousAt.continuousWithinAt
  have hl := (differentiableAt_pullback z c).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] c.val ≤ 𝓝 c.val)
  have hc := continuousOn_Icc_extendFrom_Ioo hi hl (tendsto_pullback_at_one z)
  apply hc.congr
  intro t ht
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc ht with rfl | rfl | ht
  · rw [closedQuantileMode_interior z c,
      eq_lim_at_left_extendFrom_Ioo c.property.2 hl]
  · rw [(closedQuantileMode_endpoints z).2,
      eq_lim_at_right_extendFrom_Ioo c.property.2 (tendsto_pullback_at_one z)]
  · rw [closedQuantileMode_interior z ⟨t, c.property.1.trans ht.1, ht.2⟩,
      extendFrom_extends hi t ht]

theorem boundedVariationOn_closedQuantileMode_right (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    BoundedVariationOn (closedQuantileMode z) (Icc c.val 1) := by
  have hvar : eVariationOn (closedQuantileMode z) (Ico c.val 1) ≤
      eVariationOn (flatQuotient z) (Ici (thetaSource.quantileFun c.val)) := by
    rw [eVariationOn.congr (fun t ht =>
      closedQuantileMode_interior z ⟨t, c.property.1.trans_le ht.1, ht.2⟩)]
    apply eVariationOn.comp_le_of_monotoneOn (flatQuotient z)
      (s := Ici (thetaSource.quantileFun c.val)) thetaSource.quantileFun
    · exact thetaSource.strictMonoOn_quantileFun.monotoneOn.mono
        (fun t ht => ⟨c.property.1.trans_le ht.1, ht.2⟩)
    · intro t ht
      exact thetaSource.strictMonoOn_quantileFun.monotoneOn c.property
        ⟨c.property.1.trans_le ht.1, ht.2⟩ ht.1
  have hne : (𝓝[Ici c.val ∩ Iio (1 : ℝ)] (1 : ℝ)).NeBot := by
    rw [Ici_inter_Iio, nhdsWithin_Ico_eq_nhdsLT c.property.2]
    infer_instance
  have hc : ContinuousWithinAt (closedQuantileMode z) (Ici c.val ∩ Iic 1) 1 := by
    simpa only [Ici_inter_Iic] using
      continuousOn_closedQuantileMode_right z c 1 ⟨c.property.2.le, le_rfl⟩
  have he := eVariationOn.eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt hne hc
  rw [Ici_inter_Iio, Ici_inter_Iic] at he
  change eVariationOn (closedQuantileMode z) (Icc c.val 1) ≠ ⊤
  rw [← he]
  exact ne_top_of_le_ne_top
    (boundedVariationOn_flatQuotient_Ici z (thetaSource.quantileFun c.val)) hvar

theorem continuousOn_leftClosedQuantileMode (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    ContinuousOn (leftClosedQuantileMode z) (Icc (0 : ℝ) c.val) := by
  let d : Ioo (0 : ℝ) 1 := ⟨1-c.val, by constructor <;> linarith [c.property.1, c.property.2]⟩
  exact (continuousOn_closedQuantileMode_right (-z) d).comp
    (by fun_prop) (fun t ht => ⟨by dsimp [d]; linarith [ht.2], by linarith [ht.1]⟩)

theorem boundedVariationOn_leftClosedQuantileMode (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    BoundedVariationOn (leftClosedQuantileMode z) (Icc (0 : ℝ) c.val) := by
  let d : Ioo (0 : ℝ) 1 := ⟨1-c.val, by constructor <;> linarith [c.property.1, c.property.2]⟩
  apply ne_top_of_le_ne_top (boundedVariationOn_closedQuantileMode_right (-z) d)
  apply eVariationOn.comp_le_of_antitoneOn (closedQuantileMode (-z))
    (s := Icc d.val 1) (fun t : ℝ => 1-t)
    (fun _ _ _ _ h => sub_le_sub_left h 1)
  intro t ht
  exact ⟨by dsimp [d]; linarith [ht.2], by linarith [ht.1]⟩

theorem differentiableAt_leftClosedQuantileMode (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (leftClosedQuantileMode z) t.val := by
  have ht : 1-t.val ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [t.property.1, t.property.2]
  exact (differentiableAt_closedQuantileMode (-z) ⟨1-t.val, ht⟩).comp t.val (by fun_prop)

/-- A complex BV branch with an actual interior derivative has an L1 derivative. -/
theorem intervalIntegrable_complex_deriv_of_bv
    {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hb : BoundedVariationOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t) :
    IntervalIntegrable (deriv f) volume a b := by
  have hb' : BoundedVariationOn f (uIcc a b) := by rwa [uIcc_of_le hab]
  have hr := (Complex.reCLM.lipschitz.comp_boundedVariationOn hb').intervalIntegrable_deriv
  have hi := (Complex.imCLM.lipschitz.comp_boundedVariationOn hb').intervalIntegrable_deriv
  have hrc : IntervalIntegrable
      (fun t : ℝ => ((deriv (fun x => (f x).re) t : ℝ) : ℂ)) volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp hr.1, Complex.ofRealCLM.integrable_comp hr.2⟩
  have hic : IntervalIntegrable
      (fun t : ℝ => ((deriv (fun x => (f x).im) t : ℝ) : ℂ)) volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp hi.1, Complex.ofRealCLM.integrable_comp hi.2⟩
  apply (hrc.add (hic.mul_const Complex.I)).congr_uIoo
  intro t ht
  rw [uIoo_of_le hab] at ht
  have h := (hd t ht).hasDerivAt
  have hr' : deriv (fun x => (f x).re) t = (deriv f t).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h).deriv
  have hi' : deriv (fun x => (f x).im) t = (deriv f t).im :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h).deriv
  change ((deriv (fun x => (f x).re) t : ℝ) : ℂ) +
    ((deriv (fun x => (f x).im) t : ℝ) : ℂ)*Complex.I = _
  rw [hr', hi', Complex.re_add_im]

theorem intervalIntegrable_deriv_closedQuantileMode_right
    (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (deriv (closedQuantileMode z)) volume c.val 1 :=
  intervalIntegrable_complex_deriv_of_bv c.property.2.le
    (boundedVariationOn_closedQuantileMode_right z c)
    (fun t ht => differentiableAt_closedQuantileMode z
      ⟨t, c.property.1.trans ht.1, ht.2⟩)

theorem intervalIntegrable_deriv_leftClosedQuantileMode
    (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    IntervalIntegrable (deriv (leftClosedQuantileMode z)) volume 0 c.val :=
  intervalIntegrable_complex_deriv_of_bv c.property.1.le
    (boundedVariationOn_leftClosedQuantileMode z c)
    (fun t ht => differentiableAt_leftClosedQuantileMode z
      ⟨t, ht.1, ht.2.trans c.property.2⟩)

theorem leftClosedQuantileMode_zero (z : ℂ) : leftClosedQuantileMode z 0 = -1 := by
  simpa only [leftClosedQuantileMode, sub_zero] using (closedQuantileMode_endpoints (-z)).2

theorem leftClosedQuantileMode_interior (z : ℂ) (t : Ioo (0 : ℝ) 1) :
    leftClosedQuantileMode z t.val = leftQuotient z (thetaSource.quantileFun t.val) := by
  have ht : 1-t.val ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [t.property.1, t.property.2]
  rw [leftClosedQuantileMode, closedQuantileMode_interior (-z) ⟨_, ht⟩,
    flatModePullback_eq_flatQuotient, quantileFun_one_sub t.property]
  rfl

theorem closedQuantileMode_sub_left (z : ℂ) (c : Ioo (0 : ℝ) 1) :
    closedQuantileMode z c.val - leftClosedQuantileMode z c.val =
      cutCharge z (thetaSource.quantileFun c.val) := by
  rw [closedQuantileMode_interior z c, leftClosedQuantileMode_interior z c,
    flatModePullback_eq_flatQuotient]
  rfl

end RHTower.PaperThetaEndpoint
