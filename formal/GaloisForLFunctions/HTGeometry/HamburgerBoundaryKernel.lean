import GaloisForLFunctions.HTGeometry.LabeledBoundarySimplex

/-!
# Hamburger moments of boundary-kernel barycenters

This module proves the unbounded integration step used by the canonical Nevanlinna boundary
simplex. It first derives a real-valued bind-integral theorem from the positive and negative
Lebesgue integrals. It then proves that a measurable probability kernel whose leaves represent one
complete Hamburger moment sequence has a barycenter representing exactly the same sequence.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Fubini for a real-valued integrable function over a measurable measure kernel. This is proved
from `lintegral_bind`; no signed-integral interchange is assumed. -/
theorem integral_bind_real
    (m : Measure A) (nu : A → Measure B) (f : B → ℝ)
    (hnu : Measurable nu) (hf : Measurable f)
    (hint : Integrable f (m.bind nu)) :
    (∫ x, f x ∂m.bind nu) = ∫ a, (∫ x, f x ∂nu a) ∂m := by
  let p : A → ℝ≥0∞ := fun a => ∫⁻ x, ENNReal.ofReal (f x) ∂nu a
  let q : A → ℝ≥0∞ := fun a => ∫⁻ x, ENNReal.ofReal (-f x) ∂nu a
  have hpmeas : Measurable p :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf)).comp hnu
  have hqmeas : Measurable q :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf.neg)).comp hnu
  have hnormTop : (∫⁻ x, ‖f x‖ₑ ∂m.bind nu) < ∞ :=
    hasFiniteIntegral_iff_enorm.mp hint.hasFiniteIntegral
  have hpTopBind : (∫⁻ x, ENNReal.ofReal (f x) ∂m.bind nu) < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hnormTop
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self (f x))
  have hqTopBind : (∫⁻ x, ENNReal.ofReal (-f x) ∂m.bind nu) < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hnormTop
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (neg_le_abs (f x))
  have hpBind : (∫⁻ x, ENNReal.ofReal (f x) ∂m.bind nu) = ∫⁻ a, p a ∂m :=
    Measure.lintegral_bind hnu.aemeasurable
      (ENNReal.measurable_ofReal.comp hf).aemeasurable
  have hqBind : (∫⁻ x, ENNReal.ofReal (-f x) ∂m.bind nu) = ∫⁻ a, q a ∂m :=
    Measure.lintegral_bind hnu.aemeasurable
      (ENNReal.measurable_ofReal.comp hf.neg).aemeasurable
  have hpTop : (∫⁻ a, p a ∂m) < ∞ := hpBind ▸ hpTopBind
  have hqTop : (∫⁻ a, q a ∂m) < ∞ := hqBind ▸ hqTopBind
  have hpAe : ∀ᵐ a ∂m, p a ≠ ∞ := (ae_lt_top hpmeas hpTop.ne).mono fun _ h => h.ne
  have hqAe : ∀ᵐ a ∂m, q a ≠ ∞ := (ae_lt_top hqmeas hqTop.ne).mono fun _ h => h.ne
  have hpInt : Integrable (fun a => (p a).toReal) m := by
    refine ⟨hpmeas.ennreal_toReal.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ a, ‖(p a).toReal‖ₑ ∂m) = ∫⁻ a, p a ∂m := by
        apply lintegral_congr_ae
        filter_upwards [hpAe] with a ha
        simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal ha]
      _ < ∞ := hpTop
  have hqInt : Integrable (fun a => (q a).toReal) m := by
    refine ⟨hqmeas.ennreal_toReal.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ a, ‖(q a).toReal‖ₑ ∂m) = ∫⁻ a, q a ∂m := by
        apply lintegral_congr_ae
        filter_upwards [hqAe] with a ha
        simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal ha]
      _ < ∞ := hqTop
  have hpIntegral : (∫ a, (p a).toReal ∂m) = (∫⁻ a, p a ∂m).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hpInt.1]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hpAe] with a ha
    exact ENNReal.ofReal_toReal ha
  have hqIntegral : (∫ a, (q a).toReal ∂m) = (∫⁻ a, q a ∂m).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hqInt.1]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hqAe] with a ha
    exact ENNReal.ofReal_toReal ha
  have hinner : ∀ᵐ a ∂m, (∫ x, f x ∂nu a) = (p a).toReal - (q a).toReal := by
    filter_upwards [hpAe, hqAe] with a hpa hqa
    have hfa : Integrable f (nu a) := by
      refine ⟨hf.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      calc
        (∫⁻ x, ‖f x‖ₑ ∂nu a) =
            ∫⁻ x, ENNReal.ofReal (f x) + ENNReal.ofReal (-f x) ∂nu a := by
          apply lintegral_congr
          intro x
          rw [Real.enorm_eq_ofReal_abs]
          by_cases hx : 0 ≤ f x
          · simp [abs_of_nonneg hx, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hx)]
          · have hx' : f x < 0 := lt_of_not_ge hx
            simp [abs_of_neg hx', ENNReal.ofReal_eq_zero.mpr (le_of_lt hx')]
        _ = p a + q a := by
          simpa only [Function.comp_apply] using
            (lintegral_add_left (μ := nu a) (ENNReal.measurable_ofReal.comp hf)
              (fun x => ENNReal.ofReal (-f x)))
        _ < ∞ := ENNReal.add_lt_top.2
          ⟨lt_top_iff_ne_top.2 hpa, lt_top_iff_ne_top.2 hqa⟩
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfa
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint, hpBind, hqBind]
  calc
    (∫⁻ a, p a ∂m).toReal - (∫⁻ a, q a ∂m).toReal =
        (∫ a, (p a).toReal ∂m) - ∫ a, (q a).toReal ∂m := by
          rw [hpIntegral, hqIntegral]
    _ = ∫ a, ((p a).toReal - (q a).toReal) ∂m := (integral_sub hpInt hqInt).symm
    _ = ∫ a, (∫ x, f x ∂nu a) ∂m :=
      integral_congr_ae (Filter.EventuallyEq.symm hinner)

/-- A finite real measure represents the complete Hamburger moment sequence `s`. -/
def HasHamburgerMoments (s : ℕ → ℝ) (mu : Measure ℝ) : Prop :=
  ∀ n, Integrable (fun x : ℝ => x ^ n) mu ∧ (∫ x, x ^ n ∂mu) = s n

/-- A measurable probability kernel whose leaves represent one Hamburger moment sequence has a
barycenter representing exactly the same complete sequence. -/
theorem boundaryBarycenter_hasHamburgerMoments
    {T : Type*} [MeasurableSpace T]
    (eta : Measure T) [IsProbabilityMeasure eta]
    (nu : T → Measure ℝ) [∀ t, IsProbabilityMeasure (nu t)]
    (hnu : Measurable nu) (s : ℕ → ℝ)
    (hleaf : ∀ t, HasHamburgerMoments s (nu t)) :
    HasHamburgerMoments s (boundaryBarycenter eta nu) := by
  letI : IsProbabilityMeasure (boundaryBarycenter eta nu) :=
    boundaryBarycenter_isProbabilityMeasure eta nu hnu (fun t => inferInstance)
  intro n
  let e : ℕ := 2 * n
  have heven_nonneg : ∀ x : ℝ, 0 ≤ x ^ e := by
    intro x
    dsimp [e]
    rw [pow_mul]
    positivity
  have hlinEven : (∫⁻ x, ENNReal.ofReal (x ^ e) ∂boundaryBarycenter eta nu) =
      ENNReal.ofReal (s e) := by
    change (∫⁻ x, ENNReal.ofReal (x ^ e) ∂eta.bind nu) = _
    calc
      (∫⁻ x, ENNReal.ofReal (x ^ e) ∂eta.bind nu) =
          ∫⁻ t, ∫⁻ x, ENNReal.ofReal (x ^ e) ∂nu t ∂eta := by
        have hmeas :
            AEMeasurable (fun x : ℝ => ENNReal.ofReal (x ^ e)) (eta.bind nu) :=
          (ENNReal.measurable_ofReal.comp (measurable_id.pow_const e)).aemeasurable
        exact Measure.lintegral_bind hnu.aemeasurable hmeas
      _ = ∫⁻ _t, ENNReal.ofReal (s e) ∂eta := by
        apply lintegral_congr
        intro t
        rw [← (hleaf t e).2]
        exact (ofReal_integral_eq_lintegral_ofReal (hleaf t e).1
          (Filter.Eventually.of_forall heven_nonneg)).symm
      _ = ENNReal.ofReal (s e) := by simp
  have hevenInt : Integrable (fun x : ℝ => x ^ e) (boundaryBarycenter eta nu) := by
    refine ⟨(measurable_id.pow_const e).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc
      (∫⁻ x, ‖x ^ e‖ₑ ∂boundaryBarycenter eta nu) =
          ∫⁻ x, ENNReal.ofReal (x ^ e) ∂boundaryBarycenter eta nu := by
        apply lintegral_congr
        intro x
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (heven_nonneg x)]
      _ = ENNReal.ofReal (s e) := hlinEven
      _ < ∞ := ENNReal.ofReal_lt_top
  have hdom : ∀ x : ℝ, ‖x ^ n‖ ≤ 1 + x ^ e := by
    intro x
    rw [Real.norm_eq_abs]
    have hsq : |x ^ n| ^ 2 = x ^ e := by
      rw [sq_abs, ← pow_mul]
      congr 1
      dsimp [e]
      omega
    rw [← hsq]
    nlinarith [sq_nonneg (|x ^ n| - (1 / 2 : ℝ))]
  have hnInt : Integrable (fun x : ℝ => x ^ n) (boundaryBarycenter eta nu) := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hevenInt)
      (measurable_id.pow_const n).aestronglyMeasurable
    exact Filter.Eventually.of_forall hdom
  refine ⟨hnInt, ?_⟩
  change (∫ x, x ^ n ∂eta.bind nu) = s n
  rw [integral_bind_real eta nu (fun x : ℝ => x ^ n) hnu (measurable_id.pow_const n) hnInt]
  simp_rw [(hleaf _ n).2]
  simp

end

end GaloisForLFunctions.HTGeometry
