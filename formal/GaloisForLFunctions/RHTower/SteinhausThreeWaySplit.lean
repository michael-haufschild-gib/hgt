import GaloisForLFunctions.RHTower.SteinhausChernoff

/-!
# The three-way split of the exponential moment

The Cramér lower bound without constructing the tilted measure.  Splitting

`∫ e^{tW} dμ = ∫_{W<q} + ∫_{q≤W≤q+δ} + ∫_{W>q+δ}`

and comparing the two outer pieces with the SAME product formula at a smaller tilt `s < t` and a
larger tilt `u > t` bounds the middle piece from below; since `e^{tW} ≤ e^{t(q+δ)}` there, the
measure of the middle band is bounded below too.
-/

open MeasureTheory Filter Topology HTGeometry

namespace RHTower

local instance phaseCirclePositiveSplit : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The real projection functional of the model. -/
theorem continuous_weightedSteinhausProjection (a : ι → ℝ) :
    Continuous (weightedSteinhausProjection a) := by
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_const.mul (continuous_steinhausProjection.comp (continuous_apply i))

theorem integrable_exp_weighted (a : ι → ℝ) (t : ℝ) :
    Integrable (fun x : ι → PhaseCircle => Real.exp (t * weightedSteinhausProjection a x))
      (Measure.pi fun _ : ι => AddCircle.haarAddCircle) := by
  have hbd : ∀ x : ι → PhaseCircle,
      ‖Real.exp (t * weightedSteinhausProjection a x)‖ ≤ Real.exp (|t| * ∑ i, |a i|) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have habs : |weightedSteinhausProjection a x| ≤ ∑ i, |a i| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      have := abs_steinhausProjection_le_one (x i)
      nlinarith only [this, abs_nonneg (a i)]
    have h1 : t * weightedSteinhausProjection a x ≤ |t| * |weightedSteinhausProjection a x| := by
      have h2 := le_abs_self (t * weightedSteinhausProjection a x)
      rw [abs_mul] at h2
      exact h2
    have h3 : |t| * |weightedSteinhausProjection a x| ≤ |t| * ∑ i, |a i| :=
      mul_le_mul_of_nonneg_left habs (abs_nonneg t)
    linarith
  refine Integrable.mono' (integrable_const (Real.exp (|t| * ∑ i, |a i|)))
    ((Real.continuous_exp.comp (continuous_const.mul
      (continuous_weightedSteinhausProjection a))).aestronglyMeasurable) ?_
  filter_upwards with x
  exact hbd x

/-- **The lower tail piece.** -/
theorem integral_low_le (a : ι → ℝ) {s t q : ℝ} (hst : s ≤ t) :
    ∫ x in {x : ι → PhaseCircle | weightedSteinhausProjection a x < q},
        Real.exp (t * weightedSteinhausProjection a x)
        ∂(Measure.pi fun _ : ι => AddCircle.haarAddCircle)
      ≤ Real.exp ((t - s) * q) * ∏ i, steinhausLaplace (s * a i) := by
  set μ : Measure (ι → PhaseCircle) := Measure.pi fun _ : ι => AddCircle.haarAddCircle with hμ
  set A : Set (ι → PhaseCircle) := {x | weightedSteinhausProjection a x < q} with hA
  have hAm : MeasurableSet A :=
    measurableSet_lt (continuous_weightedSteinhausProjection a).measurable measurable_const
  have hpt : ∀ x ∈ A, Real.exp (t * weightedSteinhausProjection a x)
      ≤ Real.exp ((t - s) * q) * Real.exp (s * weightedSteinhausProjection a x) := by
    intro x hx
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hxq : weightedSteinhausProjection a x < q := hx
    nlinarith only [hst, hxq]
  have hle : ∫ x in A, Real.exp (t * weightedSteinhausProjection a x) ∂μ
      ≤ ∫ x in A, Real.exp ((t - s) * q) * Real.exp (s * weightedSteinhausProjection a x) ∂μ :=
    setIntegral_mono_on (integrable_exp_weighted a t).integrableOn
      ((integrable_exp_weighted a s).const_mul _).integrableOn hAm hpt
  have hfull : ∫ x in A, Real.exp ((t - s) * q) * Real.exp (s * weightedSteinhausProjection a x) ∂μ
      ≤ Real.exp ((t - s) * q) * ∏ i, steinhausLaplace (s * a i) := by
    rw [integral_const_mul]
    have hsub : ∫ x in A, Real.exp (s * weightedSteinhausProjection a x) ∂μ
        ≤ ∫ x, Real.exp (s * weightedSteinhausProjection a x) ∂μ :=
      setIntegral_le_integral (integrable_exp_weighted a s)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    have hprod : ∫ x, Real.exp (s * weightedSteinhausProjection a x) ∂μ
        = ∏ i, steinhausLaplace (s * a i) := by
      rw [hμ]
      exact integral_exp_weightedSteinhausProjection a s
    rw [← hprod]
    exact mul_le_mul_of_nonneg_left hsub (Real.exp_pos _).le
  linarith

/-- **The upper tail piece.** -/
theorem integral_high_le (a : ι → ℝ) {t u r : ℝ} (htu : t ≤ u) :
    ∫ x in {x : ι → PhaseCircle | r < weightedSteinhausProjection a x},
        Real.exp (t * weightedSteinhausProjection a x)
        ∂(Measure.pi fun _ : ι => AddCircle.haarAddCircle)
      ≤ Real.exp ((t - u) * r) * ∏ i, steinhausLaplace (u * a i) := by
  set μ : Measure (ι → PhaseCircle) := Measure.pi fun _ : ι => AddCircle.haarAddCircle with hμ
  set C : Set (ι → PhaseCircle) := {x | r < weightedSteinhausProjection a x} with hC
  have hCm : MeasurableSet C :=
    measurableSet_lt measurable_const (continuous_weightedSteinhausProjection a).measurable
  have hpt : ∀ x ∈ C, Real.exp (t * weightedSteinhausProjection a x)
      ≤ Real.exp ((t - u) * r) * Real.exp (u * weightedSteinhausProjection a x) := by
    intro x hx
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hxr : r < weightedSteinhausProjection a x := hx
    nlinarith only [htu, hxr]
  have hle : ∫ x in C, Real.exp (t * weightedSteinhausProjection a x) ∂μ
      ≤ ∫ x in C, Real.exp ((t - u) * r) * Real.exp (u * weightedSteinhausProjection a x) ∂μ :=
    setIntegral_mono_on (integrable_exp_weighted a t).integrableOn
      ((integrable_exp_weighted a u).const_mul _).integrableOn hCm hpt
  have hfull : ∫ x in C, Real.exp ((t - u) * r) * Real.exp (u * weightedSteinhausProjection a x) ∂μ
      ≤ Real.exp ((t - u) * r) * ∏ i, steinhausLaplace (u * a i) := by
    rw [integral_const_mul]
    have hsub : ∫ x in C, Real.exp (u * weightedSteinhausProjection a x) ∂μ
        ≤ ∫ x, Real.exp (u * weightedSteinhausProjection a x) ∂μ :=
      setIntegral_le_integral (integrable_exp_weighted a u)
        (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    have hprod : ∫ x, Real.exp (u * weightedSteinhausProjection a x) ∂μ
        = ∏ i, steinhausLaplace (u * a i) := by
      rw [hμ]
      exact integral_exp_weightedSteinhausProjection a u
    rw [← hprod]
    exact mul_le_mul_of_nonneg_left hsub (Real.exp_pos _).le
  linarith


theorem steinhausSum_re (a : ι → ℝ) (x : ι → PhaseCircle) :
    (steinhausSum a x).re = weightedSteinhausProjection a x := by
  rw [steinhausSum, weightedSteinhausProjection, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re, steinhausProjection]

/-- **The band lower bound.** -/
theorem le_meas_band (a : ι → ℝ) {s t u q δ : ℝ} (hst : s ≤ t) (htu : t ≤ u) (ht : 0 ≤ t)
    (hδ : 0 ≤ δ) :
    Real.exp (-(t * (q + δ))) * ((∏ i, steinhausLaplace (t * a i))
        - Real.exp ((t - s) * q) * ∏ i, steinhausLaplace (s * a i)
        - Real.exp ((t - u) * (q + δ)) * ∏ i, steinhausLaplace (u * a i))
      ≤ ((Measure.pi fun _ : ι => AddCircle.haarAddCircle)
          {x : ι → PhaseCircle | q ≤ weightedSteinhausProjection a x}).toReal := by
  set μ : Measure (ι → PhaseCircle) := Measure.pi fun _ : ι => AddCircle.haarAddCircle with hμ
  set f : (ι → PhaseCircle) → ℝ :=
    fun x => Real.exp (t * weightedSteinhausProjection a x) with hf
  set A : Set (ι → PhaseCircle) := {x | weightedSteinhausProjection a x < q} with hA
  set C : Set (ι → PhaseCircle) := {x | q + δ < weightedSteinhausProjection a x} with hC
  have hAm : MeasurableSet A :=
    measurableSet_lt (continuous_weightedSteinhausProjection a).measurable measurable_const
  have hCm : MeasurableSet C :=
    measurableSet_lt measurable_const (continuous_weightedSteinhausProjection a).measurable
  have hint : Integrable f μ := integrable_exp_weighted a t
  have hAc : Aᶜ = {x : ι → PhaseCircle | q ≤ weightedSteinhausProjection a x} := by
    ext x
    simp [hA, not_lt]
  have hsplit1 : (∫ x in A, f x ∂μ) + ∫ x in Aᶜ, f x ∂μ = ∫ x, f x ∂μ :=
    integral_add_compl hAm hint
  have hCsub : Aᶜ ∩ C = C := by
    rw [Set.inter_eq_right]
    intro x hx
    rw [hAc, Set.mem_setOf_eq]
    have : q + δ < weightedSteinhausProjection a x := hx
    linarith
  have hsplit2 : (∫ x in Aᶜ ∩ C, f x ∂μ) + ∫ x in Aᶜ \ C, f x ∂μ = ∫ x in Aᶜ, f x ∂μ :=
    integral_inter_add_sdiff hCm hint.integrableOn
  rw [hCsub] at hsplit2
  set B : Set (ι → PhaseCircle) := Aᶜ \ C with hB
  have hBm : MeasurableSet B := hAm.compl.diff hCm
  have hlow := integral_low_le a (s := s) (t := t) (q := q) hst
  have hhigh := integral_high_le a (t := t) (u := u) (r := q + δ) htu
  have hprod : ∫ x, f x ∂μ = ∏ i, steinhausLaplace (t * a i) := by
    rw [hf, hμ]
    exact integral_exp_weightedSteinhausProjection a t
  have hBlow : (∏ i, steinhausLaplace (t * a i))
      - Real.exp ((t - s) * q) * ∏ i, steinhausLaplace (s * a i)
      - Real.exp ((t - u) * (q + δ)) * ∏ i, steinhausLaplace (u * a i)
      ≤ ∫ x in B, f x ∂μ := by
    rw [← hprod]
    linarith [hsplit1, hsplit2, hlow, hhigh]
  have hBub : ∫ x in B, f x ∂μ ≤ Real.exp (t * (q + δ)) * (μ B).toReal := by
    have hpt : ∀ x ∈ B, f x ≤ Real.exp (t * (q + δ)) := by
      intro x hx
      rw [hf]
      refine Real.exp_le_exp.2 ?_
      have h1 : ¬ (q + δ < weightedSteinhausProjection a x) := hx.2
      rw [not_lt] at h1
      nlinarith only [h1, ht]
    have hmono := setIntegral_mono_on hint.integrableOn
      ((integrable_const (Real.exp (t * (q + δ)))).integrableOn) hBm hpt
    rw [setIntegral_const, measureReal_def, smul_eq_mul] at hmono
    linarith [hmono]
  have hBsub : B ⊆ Aᶜ := Set.sdiff_subset
  have hmeasle : (μ B).toReal ≤ (μ Aᶜ).toReal := by
    have hprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
    exact ENNReal.toReal_le_toReal (measure_ne_top μ B) (measure_ne_top μ Aᶜ) |>.2
      (measure_mono hBsub)
  rw [← hAc]
  have hexp : (0 : ℝ) < Real.exp (-(t * (q + δ))) := Real.exp_pos _
  have hcancel : Real.exp (-(t * (q + δ))) * (Real.exp (t * (q + δ)) * (μ B).toReal)
      = (μ B).toReal := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  calc Real.exp (-(t * (q + δ))) * ((∏ i, steinhausLaplace (t * a i))
        - Real.exp ((t - s) * q) * ∏ i, steinhausLaplace (s * a i)
        - Real.exp ((t - u) * (q + δ)) * ∏ i, steinhausLaplace (u * a i))
      ≤ Real.exp (-(t * (q + δ))) * ∫ x in B, f x ∂μ :=
        mul_le_mul_of_nonneg_left hBlow hexp.le
    _ ≤ Real.exp (-(t * (q + δ))) * (Real.exp (t * (q + δ)) * (μ B).toReal) :=
        mul_le_mul_of_nonneg_left hBub hexp.le
    _ = (μ B).toReal := hcancel
    _ ≤ (μ Aᶜ).toReal := hmeasle

/-- The modulus dominates the projection. -/
theorem meas_proj_le_meas_norm (a : ι → ℝ) (q : ℝ) :
    ((Measure.pi fun _ : ι => AddCircle.haarAddCircle)
        {x : ι → PhaseCircle | q ≤ weightedSteinhausProjection a x})
      ≤ (Measure.pi fun _ : ι => AddCircle.haarAddCircle)
        {x : ι → PhaseCircle | q ≤ ‖steinhausSum a x‖} := by
  refine measure_mono fun x hx => ?_
  rw [Set.mem_setOf_eq] at hx ⊢
  have := Complex.re_le_norm (steinhausSum a x)
  rw [steinhausSum_re] at this
  linarith

end

end RHTower
