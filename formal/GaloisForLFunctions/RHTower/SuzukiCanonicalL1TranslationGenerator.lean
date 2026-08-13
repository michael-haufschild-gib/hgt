import GaloisForLFunctions.RHTower.SuzukiCanonicalL1Translation
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Strong `L¹` differentiation of translation orbits

An integrable representative satisfying an exact fundamental-theorem identity with an
integrable derivative has the expected strong derivative under real translation.  The proof does
not exchange point evaluation with a Bochner integral.  It identifies the translated increment
with the `L¹`-valued primitive by Fubini and the separating family of finite set integrals.

This is the strong Sobolev translation theorem needed for Suzuki's moving arithmetic cusps.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

/-- Canonical `L¹` class of an integrable complex-valued real function. -/
def integrableToL1 (f : ℝ → ℂ) (hf : Integrable f) :
    Lp ℂ 1 (volume : Measure ℝ) :=
  (memLp_one_iff_integrable.mpr hf).toLp f

theorem integrableToL1_ae (f : ℝ → ℂ) (hf : Integrable f) :
    (integrableToL1 f hf : ℝ → ℂ) =ᵐ[volume] f :=
  MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)

/-- Exact norm formula for a translated integrable representative. -/
theorem norm_realL1Translate_integrableToL1_sub_eq
    (f : ℝ → ℂ) (hf : Integrable f) (t : ℝ) :
    ‖realL1Translate t (integrableToL1 f hf) - integrableToL1 f hf‖ =
      ∫ x : ℝ, ‖f (t + x) - f x‖ := by
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub
      (realL1Translate t (integrableToL1 f hf)) (integrableToL1 f hf),
    realL1Translate_ae t (integrableToL1 f hf),
    integrableToL1_ae f hf,
    (measurePreserving_realAddTranslationFamily t).quasiMeasurePreserving.ae
      (integrableToL1_ae f hf)] with x hsub htrans hcoe hcoeShift
  change (integrableToL1 f hf : ℝ → ℂ) (t + x) = f (t + x) at hcoeShift
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [htrans, hcoe, hcoeShift]

/-- Continuous linear functional integrating an `L¹` class over a measurable set. -/
def realL1SetIntegralCLM (s : Set ℝ) :
    Lp ℂ 1 (volume : Measure ℝ) →L[ℝ] ℂ :=
  L1.integralCLM ∘L
    LpToLpRestrictCLM ℝ ℂ ℝ (volume : Measure ℝ) 1 s

theorem realL1SetIntegralCLM_apply (s : Set ℝ)
    (f : Lp ℂ 1 (volume : Measure ℝ)) :
    realL1SetIntegralCLM s f = ∫ x in s, f x := by
  rw [realL1SetIntegralCLM, ContinuousLinearMap.comp_apply,
    ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s f)

/-- A translated `L¹` function remains integrable on a bounded translation strip. -/
theorem integrable_prod_add_on_interval
    (g : ℝ → ℂ) (hg : Integrable g) (a b : ℝ) :
    Integrable (fun z : ℝ × ℝ => g (z.1 + z.2))
      ((volume.restrict (uIoc a b)).prod volume) := by
  let w : ℝ → ℂ := (uIoc a b).indicator fun _ => 1
  have hw : Integrable w := by
    exact (integrableOn_const (C := (1 : ℂ))
      (by simp [Real.volume_uIoc])).integrable_indicator measurableSet_uIoc
  have hbase : Integrable (fun z : ℝ × ℝ => w z.1 * g z.2)
      (volume.prod volume) := hw.mul_prod hg
  have hshear : Integrable
      ((fun z : ℝ × ℝ => w z.1 * g z.2) ∘
        fun z : ℝ × ℝ => (z.1, z.1 + z.2))
      (volume.prod volume) :=
    (measurePreserving_prod_add volume volume).integrable_comp_of_integrable hbase
  have hrestrict : Integrable
      ((fun z : ℝ × ℝ => w z.1 * g z.2) ∘
        fun z : ℝ × ℝ => (z.1, z.1 + z.2))
      ((volume.restrict (uIoc a b)).prod volume) :=
    hshear.mono_measure
      (Measure.prod_mono (Measure.restrict_le_self (μ := volume)
        (s := uIoc a b)) le_rfl)
  refine hrestrict.congr ?_
  have ht : ∀ᵐ z : ℝ × ℝ ∂((volume.restrict (uIoc a b)).prod volume),
      z.1 ∈ uIoc a b :=
    Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem measurableSet_uIoc)
  filter_upwards [ht] with z hz
  change w z.1 * g (z.1 + z.2) = g (z.1 + z.2)
  rw [show w z.1 = 1 by exact Set.indicator_of_mem hz _]
  simp

/-- `L¹`-valued primitive of the strong translation orbit. -/
def realL1TranslationPrimitive
    (g : Lp ℂ 1 (volume : Measure ℝ)) (h : ℝ) :
    Lp ℂ 1 (volume : Measure ℝ) :=
  ∫ t in 0..h, realL1Translate t g

theorem realL1SetIntegralCLM_translationPrimitive
    (s : Set ℝ) (g : Lp ℂ 1 (volume : Measure ℝ)) (h : ℝ) :
    realL1SetIntegralCLM s (realL1TranslationPrimitive g h) =
      ∫ t in 0..h, ∫ x in s, (realL1Translate t g) x := by
  have hint : IntervalIntegrable (fun t => realL1Translate t g) volume 0 h :=
    (continuous_realL1Translate g).intervalIntegrable 0 h
  rw [realL1TranslationPrimitive,
    ← (realL1SetIntegralCLM s).intervalIntegral_comp_comm hint]
  apply intervalIntegral.integral_congr
  intro t _
  exact realL1SetIntegralCLM_apply s (realL1Translate t g)

/-- Exact strong increment identity: translation of a `W^{1,1}` representative is the
`L¹`-valued primitive of translations of its derivative. -/
theorem realL1Translate_sub_eq_translationPrimitive
    (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (hFTC : ∀ x y : ℝ, (∫ r in x..y, g r) = f y - f x)
    (h : ℝ) :
    realL1Translate h (integrableToL1 f hf) - integrableToL1 f hf =
      realL1TranslationPrimitive (integrableToL1 g hg) h := by
  apply Lp.ext
  apply Lp.ae_eq_of_forall_setIntegral_eq _ _ (by norm_num) (by norm_num)
  · intro s _ _
    exact (L1.integrable_coeFn _).integrableOn
  · intro s _ _
    exact (L1.integrable_coeFn _).integrableOn
  · intro s _hs _hsm
    have hprod : Integrable (fun z : ℝ × ℝ => g (z.1 + z.2))
        ((volume.restrict (uIoc 0 h)).prod (volume.restrict s)) :=
      (integrable_prod_add_on_interval g hg 0 h).mono_measure
        (Measure.prod_mono le_rfl Measure.restrict_le_self)
    calc
      (∫ x in s,
          (realL1Translate h (integrableToL1 f hf) -
            integrableToL1 f hf) x) =
          ∫ x in s, (f (h + x) - f x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub
            (realL1Translate h (integrableToL1 f hf))
              (integrableToL1 f hf)),
          ae_restrict_of_ae (realL1Translate_ae h (integrableToL1 f hf)),
          ae_restrict_of_ae (integrableToL1_ae f hf),
          ae_restrict_of_ae
            ((measurePreserving_realAddTranslationFamily h).quasiMeasurePreserving.ae
              (integrableToL1_ae f hf))] with x hsub htrans hcoe hcoeShift
        change (integrableToL1 f hf : ℝ → ℂ) (h + x) = f (h + x) at hcoeShift
        rw [hsub]
        simp only [Pi.sub_apply]
        rw [htrans, hcoe, hcoeShift]
      _ = ∫ x in s, ∫ t in 0..h, g (t + x) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [intervalIntegral.integral_comp_add_right, zero_add,
          add_comm h x, hFTC]
      _ = ∫ t in 0..h, ∫ x in s, g (t + x) := by
        exact (MeasureTheory.intervalIntegral_integral_swap hprod).symm
      _ = ∫ t in 0..h, ∫ x in s,
          (realL1Translate t (integrableToL1 g hg)) x := by
        apply intervalIntegral.integral_congr
        intro t _
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae
            (realL1Translate_ae t (integrableToL1 g hg)),
          ae_restrict_of_ae
            ((measurePreserving_realAddTranslationFamily t).quasiMeasurePreserving.ae
              (integrableToL1_ae g hg))] with x htrans hcoeShift
        change (integrableToL1 g hg : ℝ → ℂ) (t + x) = g (t + x) at hcoeShift
        rw [htrans, hcoeShift]
      _ = realL1SetIntegralCLM s
          (realL1TranslationPrimitive (integrableToL1 g hg) h) :=
        (realL1SetIntegralCLM_translationPrimitive s
          (integrableToL1 g hg) h).symm
      _ = ∫ x in s,
          (realL1TranslationPrimitive (integrableToL1 g hg) h) x :=
        realL1SetIntegralCLM_apply s _

@[simp] theorem realL1Translate_zero
    (f : Lp ℂ 1 (volume : Measure ℝ)) :
    realL1Translate 0 f = f := by
  apply Lp.ext
  filter_upwards [realL1Translate_ae 0 f] with x hx
  simpa using hx

/-- Strong derivative at the identity of the translation group. -/
theorem hasDerivAt_realL1Translate_zero_of_integral_eq_sub
    (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (hFTC : ∀ x y : ℝ, (∫ r in x..y, g r) = f y - f x) :
    HasDerivAt (fun h : ℝ => realL1Translate h (integrableToL1 f hf))
      (integrableToL1 g hg) 0 := by
  have hcont : Continuous fun t : ℝ =>
      realL1Translate t (integrableToL1 g hg) :=
    continuous_realL1Translate _
  have hprim : HasDerivAt
      (fun h : ℝ => realL1TranslationPrimitive (integrableToL1 g hg) h)
      (integrableToL1 g hg) 0 := by
    have hraw := intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable 0 0)
      (hcont.stronglyMeasurableAtFilter volume (nhds 0)) hcont.continuousAt
    simpa only [realL1TranslationPrimitive, realL1Translate_zero] using hraw
  have hsum := hprim.const_add (integrableToL1 f hf)
  apply hsum.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro h
  dsimp only
  rw [← realL1Translate_sub_eq_translationPrimitive f g hf hg hFTC h]
  abel

theorem integrableToL1_comp_add_left
    (f : ℝ → ℂ) (hf : Integrable f) (s : ℝ) :
    integrableToL1 (fun x => f (s + x)) (hf.comp_add_left s) =
      realL1Translate s (integrableToL1 f hf) := by
  apply Lp.ext
  filter_upwards [integrableToL1_ae (fun x => f (s + x)) (hf.comp_add_left s),
    realL1Translate_ae s (integrableToL1 f hf),
    (measurePreserving_realAddTranslationFamily s).quasiMeasurePreserving.ae
      (integrableToL1_ae f hf)] with x hleft hright hshift
  change (integrableToL1 f hf : ℝ → ℂ) (s + x) = f (s + x) at hshift
  rw [hleft, hright, hshift]

/-- Group law for the chosen orientation of real `L¹` translations. -/
theorem realL1Translate_add
    (s t : ℝ) (f : Lp ℂ 1 (volume : Measure ℝ)) :
    realL1Translate t (realL1Translate s f) =
      realL1Translate (s + t) f := by
  apply Lp.ext
  filter_upwards [realL1Translate_ae t (realL1Translate s f),
    (measurePreserving_realAddTranslationFamily t).quasiMeasurePreserving.ae
      (realL1Translate_ae s f),
    realL1Translate_ae (s + t) f] with x hout hinner hdirect
  change (realL1Translate s f : ℝ → ℂ) (t + x) =
    f (s + (t + x)) at hinner
  rw [hout, hinner, hdirect]
  simp only [add_assoc]

/-- Strong `L¹` translation-generator theorem at every real parameter. -/
theorem hasDerivAt_realL1Translate_of_integral_eq_sub
    (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (hFTC : ∀ x y : ℝ, (∫ r in x..y, g r) = f y - f x)
    (s : ℝ) :
    HasDerivAt (fun t : ℝ => realL1Translate t (integrableToL1 f hf))
      (realL1Translate s (integrableToL1 g hg)) s := by
  let fs : ℝ → ℂ := fun x => f (s + x)
  let gs : ℝ → ℂ := fun x => g (s + x)
  have hfs : Integrable fs := hf.comp_add_left s
  have hgs : Integrable gs := hg.comp_add_left s
  have hFTCshift : ∀ x y : ℝ, (∫ r in x..y, gs r) = fs y - fs x := by
    intro x y
    dsimp only [fs, gs]
    rw [intervalIntegral.integral_comp_add_left, hFTC]
  have hzero := hasDerivAt_realL1Translate_zero_of_integral_eq_sub
    fs gs hfs hgs hFTCshift
  have hshift : HasDerivAt
      (fun t : ℝ => realL1Translate (s + t) (integrableToL1 f hf))
      (realL1Translate s (integrableToL1 g hg)) 0 := by
    convert hzero using 1
    · funext t
      rw [integrableToL1_comp_add_left f hf s,
        realL1Translate_add]
    · rw [integrableToL1_comp_add_left g hg s]
  have hshift' : HasDerivAt
      (fun t : ℝ => realL1Translate (s + t) (integrableToL1 f hf))
      (realL1Translate s (integrableToL1 g hg)) (s - s) := by
    simpa using hshift
  have hback := hshift'.hasFDerivAt.comp_hasDerivAt_of_eq s
    ((hasDerivAt_id' (𝕜 := ℝ) s).sub_const s) (by simp)
  simpa [Function.comp_def] using hback

end RHTower
