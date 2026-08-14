import GaloisForLFunctions.RHTower.SuzukiScrewNondegeneracy
import GaloisForLFunctions.RHTower.SuzukiHlogDenseFormCore

/-!
# The exact interval/zero-extension unitary for Suzuki apertures

Suzuki's 2026 operator paper uses ordinary `L²(-a,a)`; the restricted-Weil construction in this
corpus uses the closed subspace of whole-line `L²` fixed by zero extension.  This file proves
that the literal representative-based zero extension already used for the screw kernel is linear,
preserves the complex inner product, and is onto that physical aperture subspace.  It therefore
upgrades the previously injective bridge to a genuine unitary equivalence.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem suzukiApertureZeroExtend_ae_add {a : ℝ}
    (f g : SuzukiApertureIntervalL2 a) :
    suzukiApertureZeroExtend (f + g) =ᵐ[volume]
      suzukiApertureZeroExtend f + suzukiApertureZeroExtend g := by
  apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-a) a)
  · rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [suzukiApertureRepresentative_ae (f + g),
      suzukiApertureRepresentative_ae f, suzukiApertureRepresentative_ae g,
      Lp.coeFn_add f g] with x hfg hf hg hadd
    rw [suzukiApertureZeroExtend_apply]
    change suzukiApertureRepresentative (f + g) x =
      suzukiApertureZeroExtend f x + suzukiApertureZeroExtend g x
    rw [suzukiApertureZeroExtend_apply, suzukiApertureZeroExtend_apply,
      hfg, hf, hg, hadd]
    rfl
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hx
    have hx' : x ∉ Icc (-a) a := hx
    change suzukiApertureZeroExtend (f + g) x =
      suzukiApertureZeroExtend f x + suzukiApertureZeroExtend g x
    rw [suzukiApertureZeroExtend_eq_zero_of_notMem (f + g) hx',
      suzukiApertureZeroExtend_eq_zero_of_notMem f hx',
      suzukiApertureZeroExtend_eq_zero_of_notMem g hx']
    simp

theorem suzukiApertureZeroExtend_ae_smul {a : ℝ}
    (c : ℂ) (f : SuzukiApertureIntervalL2 a) :
    suzukiApertureZeroExtend (c • f) =ᵐ[volume]
      c • suzukiApertureZeroExtend f := by
  apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-a) a)
  · rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [suzukiApertureRepresentative_ae (c • f),
      suzukiApertureRepresentative_ae f, Lp.coeFn_smul c f] with x hcf hf hsmul
    rw [suzukiApertureZeroExtend_apply]
    change suzukiApertureRepresentative (c • f) x =
      c * suzukiApertureZeroExtend f x
    rw [suzukiApertureZeroExtend_apply, hcf, hf, hsmul]
    rfl
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hx
    have hx' : x ∉ Icc (-a) a := hx
    change suzukiApertureZeroExtend (c • f) x = c * suzukiApertureZeroExtend f x
    rw [suzukiApertureZeroExtend_eq_zero_of_notMem (c • f) hx',
      suzukiApertureZeroExtend_eq_zero_of_notMem f hx']
    simp

theorem suzukiApertureZeroExtendL2_add {a : ℝ}
    (f g : SuzukiApertureIntervalL2 a) :
    suzukiApertureZeroExtendL2 (f + g) =
      suzukiApertureZeroExtendL2 f + suzukiApertureZeroExtendL2 g := by
  apply Lp.ext
  filter_upwards [suzukiApertureZeroExtendL2_coeFn (f + g),
    suzukiApertureZeroExtend_ae_add f g,
    Lp.coeFn_add (suzukiApertureZeroExtendL2 f) (suzukiApertureZeroExtendL2 g),
    suzukiApertureZeroExtendL2_coeFn f,
    suzukiApertureZeroExtendL2_coeFn g] with x hleft hfun hadd hf hg
  rw [hleft, hfun]
  change suzukiApertureZeroExtend f x + suzukiApertureZeroExtend g x =
    (suzukiApertureZeroExtendL2 f + suzukiApertureZeroExtendL2 g : SoninL2) x
  rw [hadd]
  change suzukiApertureZeroExtend f x + suzukiApertureZeroExtend g x =
    suzukiApertureZeroExtendL2 f x + suzukiApertureZeroExtendL2 g x
  rw [hf, hg]

theorem suzukiApertureZeroExtendL2_smul {a : ℝ}
    (c : ℂ) (f : SuzukiApertureIntervalL2 a) :
    suzukiApertureZeroExtendL2 (c • f) =
      c • suzukiApertureZeroExtendL2 f := by
  apply Lp.ext
  filter_upwards [suzukiApertureZeroExtendL2_coeFn (c • f),
    suzukiApertureZeroExtend_ae_smul c f,
    Lp.coeFn_smul c (suzukiApertureZeroExtendL2 f),
    suzukiApertureZeroExtendL2_coeFn f] with x hleft hfun hsmul hf
  rw [hleft, hfun, hsmul]
  change c * suzukiApertureZeroExtend f x = c * suzukiApertureZeroExtendL2 f x
  rw [hf]

theorem inner_suzukiApertureZeroExtendL2 {a : ℝ}
    (f g : SuzukiApertureIntervalL2 a) :
    inner ℂ (suzukiApertureZeroExtendL2 f) (suzukiApertureZeroExtendL2 g) =
      inner ℂ f g := by
  rw [MeasureTheory.L2.inner_def, inner_suzukiApertureL2_eq_integral]
  have hf := suzukiApertureZeroExtendL2_coeFn f
  have hg := suzukiApertureZeroExtendL2_coeFn g
  calc
    (∫ x : ℝ, inner ℂ (suzukiApertureZeroExtendL2 f x)
        (suzukiApertureZeroExtendL2 g x)) =
      ∫ x : ℝ, inner ℂ (suzukiApertureZeroExtend f x)
        (suzukiApertureZeroExtend g x) := by
          apply integral_congr_ae
          filter_upwards [hf, hg] with x hfx hgx
          rw [hfx, hgx]
    _ = ∫ x : SuzukiApertureInterval a,
        inner ℂ (suzukiApertureRepresentative f x)
          (suzukiApertureRepresentative g x) := by
          rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
          · rw [← integral_subtype measurableSet_Icc]
            apply integral_congr_ae
            filter_upwards with x
            rw [suzukiApertureZeroExtend_apply, suzukiApertureZeroExtend_apply]
          · intro x hx
            rw [suzukiApertureZeroExtend_eq_zero_of_notMem f hx]
            simp
    _ = ∫ x : SuzukiApertureInterval a,
        (starRingEnd ℂ) (f x) * g x := by
          apply integral_congr_ae
          filter_upwards [suzukiApertureRepresentative_ae f,
            suzukiApertureRepresentative_ae g] with x hfx hgx
          rw [hfx, hgx]
          exact RCLike.inner_apply' (f x) (g x)

theorem norm_suzukiApertureZeroExtendL2 {a : ℝ}
    (f : SuzukiApertureIntervalL2 a) :
    ‖suzukiApertureZeroExtendL2 f‖ = ‖f‖ := by
  have hinner := inner_suzukiApertureZeroExtendL2 f f
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
  have hsquares : ‖suzukiApertureZeroExtendL2 f‖ ^ 2 = ‖f‖ ^ 2 := by
    exact_mod_cast hinner
  nlinarith [norm_nonneg f, norm_nonneg (suzukiApertureZeroExtendL2 f)]

def suzukiApertureRestrictRepresentative (a : ℝ) (f : SoninL2) :
    SuzukiApertureInterval a → ℂ :=
  fun x => (Lp.aestronglyMeasurable f).aemeasurable.mk f x

theorem measurable_suzukiApertureRestrictRepresentative (a : ℝ) (f : SoninL2) :
    Measurable (suzukiApertureRestrictRepresentative a f) := by
  exact (Lp.aestronglyMeasurable f).aemeasurable.measurable_mk.comp measurable_subtype_coe

theorem suzukiApertureRestrictRepresentative_ae (a : ℝ) (f : SoninL2) :
    suzukiApertureRestrictRepresentative a f =ᵐ[volume]
      fun x : SuzukiApertureInterval a => f x := by
  exact (ae_restrict_iff_subtype measurableSet_Icc).mp
    (ae_restrict_of_ae (Lp.aestronglyMeasurable f).aemeasurable.ae_eq_mk.symm)

theorem memLp_suzukiApertureRestrictRepresentative (a : ℝ) (f : SoninL2) :
    MemLp (suzukiApertureRestrictRepresentative a f) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_suzukiApertureRestrictRepresentative a f).aestronglyMeasurable).2
  have hfull : Integrable (fun x : ℝ =>
      ‖(Lp.aestronglyMeasurable f).aemeasurable.mk f x‖ ^ 2) := by
    have horig : Integrable (fun x : ℝ => ‖f x‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
    apply horig.congr
    filter_upwards [(Lp.aestronglyMeasurable f).aemeasurable.ae_eq_mk] with x hx
    rw [← hx]
  have hon : IntegrableOn (fun x : ℝ =>
      ‖(Lp.aestronglyMeasurable f).aemeasurable.mk f x‖ ^ 2)
      (Icc (-a) a) := hfull.integrableOn
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Icc] at hon
  rw [Measure.Subtype.volume_def]
  apply hon.congr
  filter_upwards with x
  rfl

def suzukiApertureRestrictL2 (a : ℝ) (f : SoninL2) :
    SuzukiApertureIntervalL2 a :=
  (memLp_suzukiApertureRestrictRepresentative a f).toLp
    (suzukiApertureRestrictRepresentative a f)

theorem suzukiApertureRestrictL2_coeFn (a : ℝ) (f : SoninL2) :
    suzukiApertureRestrictL2 a f =ᵐ[volume]
      suzukiApertureRestrictRepresentative a f :=
  (memLp_suzukiApertureRestrictRepresentative a f).coeFn_toLp

theorem suzukiApertureZeroExtendL2_restrict_eq
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    suzukiApertureZeroExtendL2 (suzukiApertureRestrictL2 a.1 (f : SoninL2)) =
      (f : SoninL2) := by
  apply Lp.ext
  have hsupport : ((f : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (Icc (-a.1) a.1).indicator fun x => (f : SoninL2) x := by
    have hcut := indicatorCutoff_ae (Icc (-a.1) a.1) measurableSet_Icc (f : SoninL2)
    have hfix : indicatorCutoff (Icc (-a.1) a.1) measurableSet_Icc
        (f : SoninL2) = (f : SoninL2) := by
      exact indicatorCutoff_suzukiApertureHilbert a f
    rw [hfix] at hcut
    exact hcut
  apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-a.1) a.1)
  · rw [ae_restrict_iff_subtype measurableSet_Icc]
    have hzeroRestrict :
        ((suzukiApertureZeroExtendL2
          (suzukiApertureRestrictL2 a.1 (f : SoninL2)) : SoninL2) : ℝ → ℂ) =ᵐ[
            volume.restrict (Icc (-a.1) a.1)]
          suzukiApertureZeroExtend (suzukiApertureRestrictL2 a.1 (f : SoninL2)) :=
      ae_restrict_of_ae (suzukiApertureZeroExtendL2_coeFn
        (suzukiApertureRestrictL2 a.1 (f : SoninL2)))
    have hzeroSub :
        (fun x : SuzukiApertureInterval a.1 =>
          (suzukiApertureZeroExtendL2
            (suzukiApertureRestrictL2 a.1 (f : SoninL2)) : SoninL2) x) =ᵐ[volume]
          fun x => suzukiApertureZeroExtend
            (suzukiApertureRestrictL2 a.1 (f : SoninL2)) x :=
      (ae_restrict_iff_subtype measurableSet_Icc).mp hzeroRestrict
    filter_upwards [hzeroSub,
      suzukiApertureRepresentative_ae
        (suzukiApertureRestrictL2 a.1 (f : SoninL2)),
      suzukiApertureRestrictL2_coeFn a.1 (f : SoninL2),
      suzukiApertureRestrictRepresentative_ae a.1 (f : SoninL2)] with x hzero hrep hres hsource
    rw [hzero, suzukiApertureZeroExtend_apply, hrep, hres, hsource]
  · filter_upwards [
      (suzukiApertureZeroExtendL2_coeFn
        (suzukiApertureRestrictL2 a.1 (f : SoninL2))).filter_mono
          (ae_mono Measure.restrict_le_self),
      hsupport.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hzero hsource hx
    have hx' : x ∉ Icc (-a.1) a.1 := hx
    rw [hzero, suzukiApertureZeroExtend_eq_zero_of_notMem _ hx']
    simpa [hx'] using hsource.symm

def suzukiApertureZeroExtendLinearIsometry (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →ₗᵢ[ℂ] suzukiApertureHilbert a where
  toFun f := ⟨suzukiApertureZeroExtendL2 f, by
    rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
    exact ⟨suzukiApertureZeroExtendL2 f, suzukiApertureZeroExtendL2_cutoff f⟩⟩
  map_add' f g := Subtype.ext (suzukiApertureZeroExtendL2_add f g)
  map_smul' c f := Subtype.ext (suzukiApertureZeroExtendL2_smul c f)
  norm_map' f := norm_suzukiApertureZeroExtendL2 f

theorem suzukiApertureZeroExtendLinearIsometry_surjective
    (a : SuzukiPositiveAperture) :
    Function.Surjective (suzukiApertureZeroExtendLinearIsometry a) := by
  intro f
  refine ⟨suzukiApertureRestrictL2 a.1 (f : SoninL2), ?_⟩
  apply Subtype.ext
  exact suzukiApertureZeroExtendL2_restrict_eq a f

def suzukiApertureL2Equiv (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 ≃ₗᵢ[ℂ] suzukiApertureHilbert a :=
  LinearIsometryEquiv.ofSurjective (suzukiApertureZeroExtendLinearIsometry a)
    (suzukiApertureZeroExtendLinearIsometry_surjective a)

end RHTower

