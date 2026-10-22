import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelPhysicalKernel
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalCompressedHankelOperator
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma43

/-!
# Suzuki's canonical Hankel unitary: finite compression bridge

This file identifies Suzuki's literal Hilbert--Schmidt operator with kernel `h_omega(xy)` on
`L²(0,a)` with the finite compression of the canonical unitary on `L²((0,∞),dx)`.  Endpoint
classes are handled inside `Lp`; no pointwise value at zero enters the identification.

The bridge is the missing operator-theoretic step between Suzuki (2012), Lemmas 4.1--4.3 and the
strict finite-section theorem of Lemma 4.4.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

/-! ## Isometric zero extension from `L²(0,a)` to the positive ray -/

/-- A measurable representative of an interval `L²` class. -/
def suzukiPhysicalIntervalRepresentative {a : ℝ} (f : IntervalL2 0 a) :
    ClosedInterval 0 a → ℂ :=
  (Lp.aestronglyMeasurable f).aemeasurable.mk f

theorem measurable_suzukiPhysicalIntervalRepresentative {a : ℝ}
    (f : IntervalL2 0 a) :
    Measurable (suzukiPhysicalIntervalRepresentative f) :=
  (Lp.aestronglyMeasurable f).aemeasurable.measurable_mk

theorem suzukiPhysicalIntervalRepresentative_ae {a : ℝ}
    (f : IntervalL2 0 a) :
    suzukiPhysicalIntervalRepresentative f =ᵐ[volume] f :=
  (Lp.aestronglyMeasurable f).aemeasurable.ae_eq_mk.symm

/-- Literal zero extension of an interval representative to `ℝ`. -/
def suzukiPhysicalIntervalZeroExtendFun {a : ℝ} (f : IntervalL2 0 a) : ℝ → ℂ :=
  Function.extend Subtype.val (suzukiPhysicalIntervalRepresentative f) 0

theorem suzukiPhysicalIntervalZeroExtendFun_apply {a : ℝ}
    (f : IntervalL2 0 a) (x : ClosedInterval 0 a) :
    suzukiPhysicalIntervalZeroExtendFun f x =
      suzukiPhysicalIntervalRepresentative f x :=
  Function.Injective.extend_apply Subtype.val_injective _ _ x

theorem suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem {a : ℝ}
    (f : IntervalL2 0 a) {x : ℝ} (hx : x ∉ Icc 0 a) :
    suzukiPhysicalIntervalZeroExtendFun f x = 0 := by
  have hnot : ¬ ∃ y : ClosedInterval 0 a, (y : ℝ) = x := by
    rintro ⟨y, rfl⟩
    exact hx y.property
  rw [suzukiPhysicalIntervalZeroExtendFun, Function.extend_apply' _ _ _ hnot]
  rfl

theorem suzukiPhysicalIntervalZeroExtendFun_aestronglyMeasurable {a : ℝ}
    (f : IntervalL2 0 a) :
    AEStronglyMeasurable (suzukiPhysicalIntervalZeroExtendFun f) := by
  rw [aestronglyMeasurable_iff_aemeasurable]
  exact ((MeasurableEmbedding.subtype_coe measurableSet_Icc).measurable_extend
    (measurable_suzukiPhysicalIntervalRepresentative f) measurable_const).aemeasurable

theorem suzukiPhysicalIntervalZeroExtendFun_memLp {a : ℝ}
    (f : IntervalL2 0 a) :
    MemLp (suzukiPhysicalIntervalZeroExtendFun f) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (suzukiPhysicalIntervalZeroExtendFun_aestronglyMeasurable f)).2
  have hsub : Integrable
      (fun x : ClosedInterval 0 a =>
        ‖suzukiPhysicalIntervalRepresentative f x‖ ^ 2) := by
    refine ((Lp.memLp f).integrable_norm_pow (by norm_num)).congr ?_
    filter_upwards [suzukiPhysicalIntervalRepresentative_ae f] with x hx
    rw [hx]
  have hon : IntegrableOn
      (fun x : ℝ => ‖suzukiPhysicalIntervalZeroExtendFun f x‖ ^ 2) (Icc 0 a) := by
    rw [integrableOn_iff_comap_subtypeVal measurableSet_Icc]
    refine hsub.congr (ae_of_all _ fun x => ?_)
    dsimp only [Function.comp_apply]
    rw [suzukiPhysicalIntervalZeroExtendFun_apply]
  exact hon.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem f hx, norm_zero]
    norm_num

/-- Whole-line `L²` zero extension of an interval class. -/
def suzukiPhysicalIntervalWholeL2 {a : ℝ} (f : IntervalL2 0 a) : SoninL2 :=
  (suzukiPhysicalIntervalZeroExtendFun_memLp f).toLp
    (suzukiPhysicalIntervalZeroExtendFun f)

theorem suzukiPhysicalIntervalWholeL2_ae {a : ℝ} (f : IntervalL2 0 a) :
    suzukiPhysicalIntervalWholeL2 f =ᵐ[volume]
      suzukiPhysicalIntervalZeroExtendFun f :=
  (suzukiPhysicalIntervalZeroExtendFun_memLp f).coeFn_toLp

theorem norm_suzukiPhysicalIntervalWholeL2 {a : ℝ} (f : IntervalL2 0 a) :
    ‖suzukiPhysicalIntervalWholeL2 f‖ = ‖f‖ := by
  have hsqWhole := norm_sq_toLp_eq_integral_norm_sq
    (suzukiPhysicalIntervalZeroExtendFun_memLp f)
  have hsqSub := norm_sq_lp_eq_integral_norm_sq f
  have hint :
      (∫ x : ℝ, ‖suzukiPhysicalIntervalZeroExtendFun f x‖ ^ 2) =
        ∫ x : ClosedInterval 0 a, ‖f x‖ ^ 2 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rw [← integral_subtype measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [suzukiPhysicalIntervalRepresentative_ae f] with x hx
      rw [suzukiPhysicalIntervalZeroExtendFun_apply, hx]
    · intro x hx
      rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem f hx, norm_zero]
      norm_num
  rw [hint, ← hsqSub] at hsqWhole
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsqWhole

/-- Zero extension, now regarded as an element of Suzuki's positive-half-line carrier. -/
def suzukiPhysicalIntervalPositiveL2 {a : ℝ} (f : IntervalL2 0 a) : SuzukiPositiveL2 :=
  soninHalfLine (suzukiPhysicalIntervalWholeL2 f)

theorem suzukiPhysicalIntervalPositiveL2_ae {a : ℝ} (f : IntervalL2 0 a) :
    suzukiPhysicalIntervalPositiveL2 f =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      suzukiPhysicalIntervalZeroExtendFun f :=
  (coeFn_soninHalfLine (suzukiPhysicalIntervalWholeL2 f)).trans
    (ae_restrict_of_ae (suzukiPhysicalIntervalWholeL2_ae f))

theorem norm_suzukiPhysicalIntervalPositiveL2 {a : ℝ} (f : IntervalL2 0 a) :
    ‖suzukiPhysicalIntervalPositiveL2 f‖ = ‖f‖ := by
  have hmem := memLp_restrict_Ioi (suzukiPhysicalIntervalWholeL2 f)
  have hsqPos := norm_sq_toLp_eq_integral_norm_sq hmem
  have hsqSub := norm_sq_lp_eq_integral_norm_sq f
  have hint :
      (∫ x : ℝ in Ioi (0 : ℝ),
          ‖(suzukiPhysicalIntervalWholeL2 f : ℝ → ℂ) x‖ ^ 2) =
        ∫ x : ClosedInterval 0 a, ‖f x‖ ^ 2 := by
    have hnorm :
        (∫ x : ℝ in Ioi (0 : ℝ),
            ‖(suzukiPhysicalIntervalWholeL2 f : ℝ → ℂ) x‖ ^ 2) =
          ∫ x : ℝ in Ioi (0 : ℝ),
            ‖suzukiPhysicalIntervalZeroExtendFun f x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (suzukiPhysicalIntervalWholeL2_ae f)] with x hx
      rw [hx]
    rw [hnorm]
    calc
      (∫ x : ℝ in Ioi (0 : ℝ),
          ‖suzukiPhysicalIntervalZeroExtendFun f x‖ ^ 2) =
          ∫ x : ℝ in Ioc 0 a,
            ‖suzukiPhysicalIntervalZeroExtendFun f x‖ ^ 2 := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (fun x hx => hx.1)
        intro x hx
        rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem]
        · norm_num
        · exact fun hIcc => hx.2 ⟨hx.1, hIcc.2⟩
      _ = ∫ x : ℝ in Icc 0 a,
            ‖suzukiPhysicalIntervalZeroExtendFun f x‖ ^ 2 := by
        exact integral_Icc_eq_integral_Ioc.symm
      _ = ∫ x : ClosedInterval 0 a, ‖f x‖ ^ 2 := by
        rw [← integral_subtype measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards [suzukiPhysicalIntervalRepresentative_ae f] with x hx
        rw [suzukiPhysicalIntervalZeroExtendFun_apply, hx]
  change ‖soninHalfLine (suzukiPhysicalIntervalWholeL2 f)‖ ^ 2 = _ at hsqPos
  rw [hint, ← hsqSub] at hsqPos
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsqPos

theorem suzukiPhysicalIntervalZeroExtendFun_add_ae {a : ℝ}
    (f g : IntervalL2 0 a) :
    suzukiPhysicalIntervalZeroExtendFun (f + g) =ᵐ[volume]
      fun x => suzukiPhysicalIntervalZeroExtendFun f x +
        suzukiPhysicalIntervalZeroExtendFun g x := by
  have hsub : suzukiPhysicalIntervalRepresentative (f + g) =ᵐ[volume]
      fun x => suzukiPhysicalIntervalRepresentative f x +
        suzukiPhysicalIntervalRepresentative g x := by
    filter_upwards [suzukiPhysicalIntervalRepresentative_ae (f + g),
      suzukiPhysicalIntervalRepresentative_ae f,
      suzukiPhysicalIntervalRepresentative_ae g,
      Lp.coeFn_add f g] with x hout hf hg hadd
    rw [hout, hf, hg, hadd]
    rfl
  have hIcc : ∀ᵐ x ∂volume.restrict (Icc 0 a),
      suzukiPhysicalIntervalZeroExtendFun (f + g) x =
        suzukiPhysicalIntervalZeroExtendFun f x +
          suzukiPhysicalIntervalZeroExtendFun g x := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [hsub] with x hx
    rw [suzukiPhysicalIntervalZeroExtendFun_apply,
      suzukiPhysicalIntervalZeroExtendFun_apply,
      suzukiPhysicalIntervalZeroExtendFun_apply]
    exact hx
  have hIccWhole := (ae_restrict_iff' measurableSet_Icc).mp hIcc
  filter_upwards [hIccWhole] with x hx
  by_cases hmem : x ∈ Icc 0 a
  · exact hx hmem
  · rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem (f + g) hmem,
      suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem f hmem,
      suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem g hmem, zero_add]

theorem suzukiPhysicalIntervalZeroExtendFun_smul_ae {a : ℝ}
    (c : ℂ) (f : IntervalL2 0 a) :
    suzukiPhysicalIntervalZeroExtendFun (c • f) =ᵐ[volume]
      fun x => c * suzukiPhysicalIntervalZeroExtendFun f x := by
  have hsub : suzukiPhysicalIntervalRepresentative (c • f) =ᵐ[volume]
      fun x => c * suzukiPhysicalIntervalRepresentative f x := by
    filter_upwards [suzukiPhysicalIntervalRepresentative_ae (c • f),
      suzukiPhysicalIntervalRepresentative_ae f,
      Lp.coeFn_smul c f] with x hout hf hsmul
    rw [hout, hf, hsmul]
    rfl
  have hIcc : ∀ᵐ x ∂volume.restrict (Icc 0 a),
      suzukiPhysicalIntervalZeroExtendFun (c • f) x =
        c * suzukiPhysicalIntervalZeroExtendFun f x := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [hsub] with x hx
    rw [suzukiPhysicalIntervalZeroExtendFun_apply,
      suzukiPhysicalIntervalZeroExtendFun_apply]
    exact hx
  have hIccWhole := (ae_restrict_iff' measurableSet_Icc).mp hIcc
  filter_upwards [hIccWhole] with x hx
  by_cases hmem : x ∈ Icc 0 a
  · exact hx hmem
  · rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem (c • f) hmem,
      suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem f hmem, mul_zero]

def suzukiPhysicalIntervalPositiveLinear (a : ℝ) :
    IntervalL2 0 a →ₗ[ℂ] SuzukiPositiveL2 where
  toFun := suzukiPhysicalIntervalPositiveL2
  map_add' f g := by
    apply Lp.ext
    filter_upwards [suzukiPhysicalIntervalPositiveL2_ae (f + g),
      suzukiPhysicalIntervalPositiveL2_ae f,
      suzukiPhysicalIntervalPositiveL2_ae g,
      Lp.coeFn_add (suzukiPhysicalIntervalPositiveL2 f)
        (suzukiPhysicalIntervalPositiveL2 g),
      ae_restrict_of_ae (suzukiPhysicalIntervalZeroExtendFun_add_ae f g)] with
        x hout hf hg hsum hzero
    rw [hout, hsum]
    change suzukiPhysicalIntervalZeroExtendFun (f + g) x =
      suzukiPhysicalIntervalPositiveL2 f x +
        suzukiPhysicalIntervalPositiveL2 g x
    rw [hzero, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [suzukiPhysicalIntervalPositiveL2_ae (c • f),
      suzukiPhysicalIntervalPositiveL2_ae f,
      Lp.coeFn_smul c (suzukiPhysicalIntervalPositiveL2 f),
      ae_restrict_of_ae (suzukiPhysicalIntervalZeroExtendFun_smul_ae c f)] with
        x hout hf hsum hzero
    simp only [RingHom.id_apply]
    rw [hout, hsum]
    change suzukiPhysicalIntervalZeroExtendFun (c • f) x =
      c * suzukiPhysicalIntervalPositiveL2 f x
    rw [hzero, hf]

/-- Canonical isometric embedding `L²(0,a) → L²((0,∞),dx)` by zero extension. -/
def suzukiPhysicalIntervalPositiveIsometry (a : ℝ) :
    IntervalL2 0 a →ₗᵢ[ℂ] SuzukiPositiveL2 where
  __ := suzukiPhysicalIntervalPositiveLinear a
  norm_map' := norm_suzukiPhysicalIntervalPositiveL2

/-! ## Restriction back to the finite interval -/

/-- Zero extension from Suzuki's positive carrier to whole-line `L²` is itself an isometry. -/
def suzukiPositiveZeroExtensionIsometry : SuzukiPositiveL2 →ₗᵢ[ℂ] SoninL2 where
  __ := suzukiPositiveZeroExtensionLinear
  norm_map' := norm_suzukiPositiveZeroExtension

/-- Restriction from the positive ray to Suzuki's literal interval carrier. -/
def suzukiPositiveIntervalRestriction (a : ℝ) :
    SuzukiPositiveL2 →L[ℂ] IntervalL2 0 a :=
  restrictToClosedInterval 0 a ∘L
    suzukiPositiveZeroExtensionIsometry.toContinuousLinearMap

theorem suzukiPositiveIntervalRestriction_ae (a : ℝ) (g : SuzukiPositiveL2) :
    suzukiPositiveIntervalRestriction a g =ᵐ[volume]
      fun x : ClosedInterval 0 a => suzukiPositiveZeroExtension g (x : ℝ) := by
  exact restrictToClosedInterval_coeFn 0 a (suzukiPositiveZeroExtension g)

/-- Restriction is a left inverse to physical zero extension. -/
@[simp] theorem suzukiPositiveIntervalRestriction_extension
    (a : ℝ) (f : IntervalL2 0 a) :
    suzukiPositiveIntervalRestriction a
        (suzukiPhysicalIntervalPositiveIsometry a f) = f := by
  apply Lp.ext
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hzero := hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae
    (suzukiPositiveZeroExtension_ae
      (suzukiPhysicalIntervalPositiveL2 f)))
  have hposWhole := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae f)
  have hpos := hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae hposWhole)
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  filter_upwards [suzukiPositiveIntervalRestriction_ae a
      (suzukiPhysicalIntervalPositiveL2 f),
    hzero, hpos, hne, suzukiPhysicalIntervalRepresentative_ae f] with
      x hres hzero hpos hne hrep
  change suzukiPositiveIntervalRestriction a
      (suzukiPhysicalIntervalPositiveL2 f) x = f x
  rw [hres]
  change suzukiPositiveZeroExtension
      (suzukiPhysicalIntervalPositiveL2 f) (x : ℝ) = f x
  have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hne)
  rw [show suzukiPositiveZeroExtension
      (suzukiPhysicalIntervalPositiveL2 f) (x : ℝ) =
      suzukiPositiveZeroExtensionFun
        (suzukiPhysicalIntervalPositiveL2 f) (x : ℝ) by
        simpa only [Function.comp_apply] using hzero]
  rw [suzukiPositiveZeroExtensionFun,
    indicator_of_mem (show (x : ℝ) ∈ Ioi (0 : ℝ) from hxpos)]
  rw [hpos hxpos, suzukiPhysicalIntervalZeroExtendFun_apply, hrep]

theorem norm_suzukiPositiveIntervalRestriction_le (a : ℝ)
    (g : SuzukiPositiveL2) :
    ‖suzukiPositiveIntervalRestriction a g‖ ≤ ‖g‖ := by
  calc
    ‖suzukiPositiveIntervalRestriction a g‖ ≤
        ‖suzukiPositiveZeroExtension g‖ := by
      rw [suzukiPositiveIntervalRestriction, ContinuousLinearMap.coe_comp,
        Function.comp_apply, restrictToClosedInterval,
        ContinuousLinearMap.coe_comp, Function.comp_apply]
      change ‖(Lp.compMeasurePreservingₗᵢ ℂ
          ((↑) : ClosedInterval 0 a → ℝ)
          (measurePreserving_subtype_coe measurableSet_Icc))
            (LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (Icc 0 a)
              (suzukiPositiveZeroExtension g))‖ ≤ _
      rw [(Lp.compMeasurePreservingₗᵢ ℂ
        ((↑) : ClosedInterval 0 a → ℝ)
        (measurePreserving_subtype_coe measurableSet_Icc)).norm_map]
      exact norm_Lp_toLp_restrict_le (Icc 0 a)
        (suzukiPositiveZeroExtension g)
    _ = ‖g‖ := norm_suzukiPositiveZeroExtension g

/-! ## Exact logarithmic support of an interval source -/

/-- Unitary logarithmic half-density coordinate on Suzuki's positive carrier. -/
def suzukiPositiveLogUnitary : SuzukiPositiveL2 ≃ₗᵢ[ℂ] SoninL2 :=
  suzukiPositiveHalfLineUnitary.symm.trans logEvenUnitary

@[simp] theorem suzukiPositiveLogUnitary_apply (g : SuzukiPositiveL2) :
    suzukiPositiveLogUnitary g =
      logEvenUnitary (suzukiPositiveHalfLineUnitary.symm g) := rfl

/-- A zero-extended source from `L²(0,a)` becomes a sharp left-half-line source in logarithmic
coordinates.  This is the exact physical-to-log support bridge used in Suzuki's Lemma 4.4. -/
theorem logHalflineCutoff_suzukiPhysicalIntervalPositive
    {a : ℝ} (ha : 0 < a) (f : IntervalL2 0 a) :
    logHalflineCutoff (Real.log a)
        (suzukiPositiveLogUnitary
          (suzukiPhysicalIntervalPositiveIsometry a f)) =
      suzukiPositiveLogUnitary
        (suzukiPhysicalIntervalPositiveIsometry a f) := by
  let u : SuzukiPositiveL2 := suzukiPhysicalIntervalPositiveL2 f
  let q : SoninL2 := suzukiPositiveLogUnitary u
  have hcarrier :
      suzukiPositiveHalfLineUnitary (logEvenUnitary.symm q) = u := by
    change suzukiPositiveHalfLineUnitary
      (logEvenUnitary.symm
        (logEvenUnitary (suzukiPositiveHalfLineUnitary.symm u))) = u
    rw [logEvenUnitary.symm_apply_apply,
      suzukiPositiveHalfLineUnitary.apply_symm_apply]
  have hcoord := suzukiPositiveHalfLineUnitary_logEven_symm_ae q
  rw [hcarrier] at hcoord
  have hcoordWhole := (ae_restrict_iff' measurableSet_Ioi).mp hcoord
  have hcoordExp := realExp_quasiMeasurePreserving.ae hcoordWhole
  have hinputWhole := (ae_restrict_iff' measurableSet_Ioi).mp
    (suzukiPhysicalIntervalPositiveL2_ae f)
  have hinputExp := realExp_quasiMeasurePreserving.ae hinputWhole
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (Iic (Real.log a)) measurableSet_Iic q,
    l2MeasurableRep_ae q, hcoordExp, hinputExp] with t hcut hrep hcoord hinput
  change logHalflineCutoff (Real.log a) q t = q t
  rw [show logHalflineCutoff (Real.log a) q t =
      (Iic (Real.log a)).indicator (fun s => q s) t by
        simpa [logHalflineCutoff] using hcut]
  by_cases ht : t ≤ Real.log a
  · rw [indicator_of_mem (show t ∈ Iic (Real.log a) from ht)]
  · rw [indicator_of_notMem (show t ∉ Iic (Real.log a) from ht)]
    have hexp : a < Real.exp t := by
      rw [← Real.exp_log ha]
      exact Real.exp_lt_exp.mpr (lt_of_not_ge ht)
    have hnotIcc : Real.exp t ∉ Icc 0 a := fun hx => (not_le_of_gt hexp) hx.2
    have huZero : u (Real.exp t) = 0 := by
      rw [hinput (Real.exp_pos t),
        suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem f hnotIcc]
    have hcoord' : u (Real.exp t) =
        (Real.exp (-t / 2) : ℂ) * l2MeasurableRep q t := by
      simpa only [Real.log_exp] using hcoord (Real.exp_pos t)
    have hweight : (Real.exp (-t / 2) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.exp_ne_zero (-t / 2))
    have hrepZero : l2MeasurableRep q t = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left hweight
      rw [← hcoord', huZero]
    rw [← hrep, hrepZero]

/-! ## Restriction is the Hilbert adjoint of extension -/

theorem inner_suzukiPhysicalIntervalPositive_extension
    {a : ℝ} (f : IntervalL2 0 a) (g : SuzukiPositiveL2) :
    inner ℂ (suzukiPhysicalIntervalPositiveIsometry a f) g =
      inner ℂ f (suzukiPositiveIntervalRestriction a g) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hleft :
      (∫ x : ℝ in Ioi (0 : ℝ),
          inner ℂ (suzukiPhysicalIntervalPositiveL2 f x) (g x)) =
        ∫ x : ℝ in Ioi (0 : ℝ),
          inner ℂ (suzukiPhysicalIntervalZeroExtendFun f x) (g x) := by
    apply integral_congr_ae
    filter_upwards [suzukiPhysicalIntervalPositiveL2_ae f] with x hx
    rw [hx]
  change (∫ x : ℝ in Ioi (0 : ℝ),
      inner ℂ (suzukiPhysicalIntervalPositiveL2 f x) (g x)) = _
  rw [hleft]
  calc
    (∫ x : ℝ in Ioi (0 : ℝ),
        inner ℂ (suzukiPhysicalIntervalZeroExtendFun f x) (g x)) =
        ∫ x : ℝ in Ioc 0 a,
          inner ℂ (suzukiPhysicalIntervalZeroExtendFun f x) (g x) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (fun x hx => hx.1)
      intro x hx
      rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem]
      · simp
      · exact fun hIcc => hx.2 ⟨hx.1, hIcc.2⟩
    _ = ∫ x : ℝ in Icc 0 a,
          inner ℂ (suzukiPhysicalIntervalZeroExtendFun f x) (g x) := by
      exact integral_Icc_eq_integral_Ioc.symm
    _ = ∫ x : ClosedInterval 0 a,
          inner ℂ (f x) (suzukiPositiveIntervalRestriction a g x) := by
      rw [← integral_subtype measurableSet_Icc]
      let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
          (volume : Measure (ClosedInterval 0 a))
          ((volume : Measure ℝ).restrict (Icc 0 a)) :=
        measurePreserving_subtype_coe measurableSet_Icc
      have hzero := hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae
        (suzukiPositiveZeroExtension_ae g))
      have hne := hmp.quasiMeasurePreserving.ae
        (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
      apply integral_congr_ae
      filter_upwards [suzukiPhysicalIntervalRepresentative_ae f,
        suzukiPositiveIntervalRestriction_ae a g, hzero, hne] with
          x hf hres hzero hne
      have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hne)
      rw [suzukiPhysicalIntervalZeroExtendFun_apply, hf, hres]
      rw [show suzukiPositiveZeroExtension g (x : ℝ) =
          suzukiPositiveZeroExtensionFun g (x : ℝ) by
            simpa only [Function.comp_apply] using hzero,
        suzukiPositiveZeroExtensionFun,
        indicator_of_mem (show (x : ℝ) ∈ Ioi (0 : ℝ) from hxpos)]

/-- Exact adjoint identity for the finite-extension isometry. -/
theorem adjoint_suzukiPhysicalIntervalPositiveIsometry (a : ℝ) :
    (suzukiPhysicalIntervalPositiveIsometry a).toContinuousLinearMap.adjoint =
      suzukiPositiveIntervalRestriction a := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc
    inner ℂ g ((suzukiPhysicalIntervalPositiveIsometry a) f) =
        (starRingEnd ℂ)
          (inner ℂ ((suzukiPhysicalIntervalPositiveIsometry a) f) g) :=
      (inner_conj_symm (𝕜 := ℂ) g
        ((suzukiPhysicalIntervalPositiveIsometry a) f)).symm
    _ = (starRingEnd ℂ)
          (inner ℂ f (suzukiPositiveIntervalRestriction a g)) := by
      rw [inner_suzukiPhysicalIntervalPositive_extension]
    _ = inner ℂ (suzukiPositiveIntervalRestriction a g) f :=
      inner_conj_symm (𝕜 := ℂ) (suzukiPositiveIntervalRestriction a g) f

/-! ## Range characterization and compact-smooth core -/

theorem suzukiPhysicalInterval_extension_restriction_of_ae_zero
    {a : ℝ} (ha : 0 < a) (g : SuzukiPositiveL2)
    (hzero : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), a < x → g x = 0) :
    suzukiPhysicalIntervalPositiveIsometry a
        (suzukiPositiveIntervalRestriction a g) = g := by
  let f := suzukiPositiveIntervalRestriction a g
  have hresSub := suzukiPositiveIntervalRestriction_ae a g
  have hzeroExtSub := (suzukiPositiveZeroExtension_ae g)
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hzeroExtOnSub := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hzeroExtSub)
  have hresPointSub : ∀ᵐ x : ClosedInterval 0 a ∂volume, f x = g (x : ℝ) := by
    filter_upwards [hresSub, hzeroExtOnSub,
      hmp.quasiMeasurePreserving.ae
        (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))] with x hres hzeroExt hne
    rw [hres]
    have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hne)
    rw [show suzukiPositiveZeroExtension g (x : ℝ) =
        suzukiPositiveZeroExtensionFun g (x : ℝ) by
          simpa only [Function.comp_apply] using hzeroExt,
      suzukiPositiveZeroExtensionFun,
      indicator_of_mem (show (x : ℝ) ∈ Ioi (0 : ℝ) from hxpos)]
  have hrepSub : suzukiPhysicalIntervalRepresentative f =ᵐ[volume]
      fun x : ClosedInterval 0 a => g (x : ℝ) :=
    (suzukiPhysicalIntervalRepresentative_ae f).trans hresPointSub
  have hrepIcc : ∀ᵐ x ∂volume.restrict (Icc 0 a),
      suzukiPhysicalIntervalZeroExtendFun f x = g x := by
    apply (ae_restrict_iff_subtype measurableSet_Icc).2
    filter_upwards [hrepSub] with x hx
    rw [suzukiPhysicalIntervalZeroExtendFun_apply, hx]
  have hrepWhole := (ae_restrict_iff' measurableSet_Icc).mp hrepIcc
  apply Lp.ext
  filter_upwards [suzukiPhysicalIntervalPositiveL2_ae f, hzero,
    ae_restrict_of_ae hrepWhole, ae_restrict_mem measurableSet_Ioi] with
      x hext hzero hrep hxpos
  change suzukiPhysicalIntervalPositiveL2 f x = g x
  rw [hext]
  by_cases hxa : x ≤ a
  · exact hrep ⟨hxpos.le, hxa⟩
  · rw [suzukiPhysicalIntervalZeroExtendFun_eq_zero_of_notMem,
      hzero (lt_of_not_ge hxa)]
    exact fun hx => hxa hx.2

theorem suzukiCompactSmoothPositiveL2_ae_zero_above
    {a : ℝ} (ha : 0 < a)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g)
    (hg : ∀ t, Real.log a ≤ t → g t = 0) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), a < x →
      suzukiCompactSmoothPositiveL2 g hsmooth hcompact x = 0 := by
  filter_upwards [suzukiCompactSmoothPositiveL2_ae g hsmooth hcompact,
    ae_restrict_mem measurableSet_Ioi] with x hx hxpos hax
  rw [hx, hg]
  · ring
  · exact (Real.strictMonoOn_log ha hxpos hax).le

theorem suzukiPhysicalInterval_extension_restriction_compactSmooth
    {a : ℝ} (ha : 0 < a)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g)
    (hg : ∀ t, Real.log a ≤ t → g t = 0) :
    suzukiPhysicalIntervalPositiveIsometry a
        (suzukiPositiveIntervalRestriction a
          (suzukiCompactSmoothPositiveL2 g hsmooth hcompact)) =
      suzukiCompactSmoothPositiveL2 g hsmooth hcompact :=
  suzukiPhysicalInterval_extension_restriction_of_ae_zero ha _
    (suzukiCompactSmoothPositiveL2_ae_zero_above ha g hsmooth hcompact hg)

theorem suzukiPositiveIntervalRestriction_value_ae
    {a : ℝ} (g : SuzukiPositiveL2) :
    suzukiPositiveIntervalRestriction a g =ᵐ[volume]
      fun x : ClosedInterval 0 a => g (x : ℝ) := by
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hzero := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (suzukiPositiveZeroExtension_ae g))
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  filter_upwards [suzukiPositiveIntervalRestriction_ae a g, hzero, hne] with
      x hres hzero hne
  rw [hres]
  have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hne)
  rw [show suzukiPositiveZeroExtension g (x : ℝ) =
      suzukiPositiveZeroExtensionFun g (x : ℝ) by
        simpa only [Function.comp_apply] using hzero,
    suzukiPositiveZeroExtensionFun,
    indicator_of_mem (show (x : ℝ) ∈ Ioi (0 : ℝ) from hxpos)]

/-- A positive-ray integral against an interval-supported `L²` vector is exactly its subtype
integral over `L²(0,a)`. -/
theorem integral_Ioi_kernel_eq_interval_of_ae_zero
    {a : ℝ} (u : SuzukiPositiveL2)
    (hzero : ∀ᵐ y ∂volume.restrict (Ioi (0 : ℝ)), a < y → u y = 0)
    (K : ℝ → ℂ) :
    (∫ y : ℝ in Ioi (0 : ℝ), K y * u y) =
      ∫ y : ClosedInterval 0 a,
        K (y : ℝ) * suzukiPositiveIntervalRestriction a u y := by
  calc
    (∫ y : ℝ in Ioi (0 : ℝ), K y * u y) =
        ∫ y : ℝ in Ioc 0 a, K y * u y := by
      apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
        measurableSet_Ioi.nullMeasurableSet (fun y hy => hy.1)
      filter_upwards [(ae_restrict_iff' measurableSet_Ioi).mp hzero] with y hy hdiff
      have hya : a < y := by
        by_contra hnot
        exact hdiff.2 ⟨hdiff.1, le_of_not_gt hnot⟩
      rw [hy hdiff.1 hya, mul_zero]
    _ = ∫ y : ℝ in Icc 0 a, K y * u y := by
      exact integral_Icc_eq_integral_Ioc.symm
    _ = ∫ y : ClosedInterval 0 a,
          K (y : ℝ) * suzukiPositiveIntervalRestriction a u y := by
      rw [← integral_subtype measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [suzukiPositiveIntervalRestriction_value_ae u] with y hy
      rw [hy]

/-! ## The exact finite compression -/

/-- Compression of Suzuki's global canonical Hankel unitary to `L²(0,a)`. -/
def suzukiCanonicalPositiveHankelCompression
    (omega a : ℝ) (homega : 1 / 2 < omega) :
    IntervalL2 0 a →L[ℂ] IntervalL2 0 a :=
  suzukiPositiveIntervalRestriction a ∘L
    (suzukiCanonicalPositiveHankelUnitary omega
      (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)).toLinearIsometry.toContinuousLinearMap
      ∘L (suzukiPhysicalIntervalPositiveIsometry a).toContinuousLinearMap

theorem suzukiCanonicalPositiveHankelCompression_eq_on_compactSmooth
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 0 < a)
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g)
    (hg : ∀ t, Real.log a ≤ t → g t = 0) :
    suzukiCanonicalPositiveHankelCompression omega a homega
        (suzukiPositiveIntervalRestriction a
          (suzukiCompactSmoothPositiveL2 g hsmooth hcompact)) =
      suzukiCompressedHankelOperator omega a homega
        (suzukiPositiveIntervalRestriction a
          (suzukiCompactSmoothPositiveL2 g hsmooth hcompact)) := by
  let u := suzukiCompactSmoothPositiveL2 g hsmooth hcompact
  let f := suzukiPositiveIntervalRestriction a u
  let H := suzukiCanonicalPositiveHankelUnitary omega
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
  have hfixed : suzukiPhysicalIntervalPositiveIsometry a f = u :=
    suzukiPhysicalInterval_extension_restriction_compactSmooth
      ha g hsmooth hcompact hg
  have huZero := suzukiCompactSmoothPositiveL2_ae_zero_above
    ha g hsmooth hcompact hg
  have hphysical := suzuki2012_lemma_four_one_positive_half_line_ae_kernel
    (show 0 < omega by linarith) (c := omega + 1) (by linarith)
    (suzukiCanonicalTheta_meromorphicInner_of_half_lt homega)
    g hsmooth hcompact
  have hphysicalWhole := (ae_restrict_iff' measurableSet_Ioi).mp hphysical
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hphysicalSub := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae hphysicalWhole)
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae (volume.ae_ne (0 : ℝ)))
  apply Lp.ext
  filter_upwards [suzukiPositiveIntervalRestriction_value_ae (H u),
    suzukiCompressedHankelOperator_coeFn omega a homega ha f,
    hphysicalSub, hne] with x hleft hright hphysical hne
  change suzukiPositiveIntervalRestriction a
      (H (suzukiPhysicalIntervalPositiveIsometry a f)) x = _
  rw [hfixed, hleft, hright]
  have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hne)
  rw [hphysical hxpos]
  exact integral_Ioi_kernel_eq_interval_of_ae_zero u huZero
    (fun y => suzukiSourceHFinite omega ((x : ℝ) * y))

theorem suzukiPositiveLogUnitary_compactSmooth
    (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hcompact : HasCompactSupport g) :
    suzukiPositiveLogUnitary
        (suzukiCompactSmoothPositiveL2 g hsmooth hcompact) =
      suzukiCompactSmoothLogL2 g hsmooth hcompact := by
  change logEvenUnitary
      (suzukiPositiveHalfLineUnitary.symm
        (suzukiPositiveHalfLineUnitary
          (logEvenUnitary.symm
            (suzukiCompactSmoothLogL2 g hsmooth hcompact)))) = _
  rw [suzukiPositiveHalfLineUnitary.symm_apply_apply,
    logEvenUnitary.apply_symm_apply]

/-- Compact-smooth logarithmic sources supported in `(-∞, log a]`, restricted back to
`L²(0,a)`. -/
def suzukiIntervalCompactSmoothCore (a : ℝ) : Set (IntervalL2 0 a) :=
  {f | ∃ (g : ℝ → ℂ) (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
      (hcompact : HasCompactSupport g),
      (∀ t, Real.log a ≤ t → g t = 0) ∧
        f = suzukiPositiveIntervalRestriction a
          (suzukiCompactSmoothPositiveL2 g hsmooth hcompact)}

/-- The source-faithful compact-smooth core is dense in the literal finite interval space. -/
theorem dense_suzukiIntervalCompactSmoothCore {a : ℝ} (ha : 0 < a) :
    Dense (suzukiIntervalCompactSmoothCore a) := by
  rw [Metric.dense_iff]
  intro f ε hε
  let u := suzukiPhysicalIntervalPositiveIsometry a f
  let q := suzukiPositiveLogUnitary u
  have hq : logHalflineCutoff (Real.log a) q = q :=
    logHalflineCutoff_suzukiPhysicalIntervalPositive ha f
  obtain ⟨g, hcompact, hsmooth, hg, hdist⟩ :=
    exists_suzukiOneSidedCompactSmoothL2_dist_lt hq hε
  let u' := suzukiCompactSmoothPositiveL2 g hsmooth hcompact
  let f' := suzukiPositiveIntervalRestriction a u'
  refine ⟨f', ?_, ?_⟩
  · rw [Metric.mem_ball]
    have hfu : suzukiPositiveIntervalRestriction a u = f :=
      suzukiPositiveIntervalRestriction_extension a f
    have hfu' : suzukiPositiveIntervalRestriction a u' = f' := rfl
    have hcontract : dist f' f ≤ dist u u' := by
      calc
        dist f' f = ‖suzukiPositiveIntervalRestriction a u' -
            suzukiPositiveIntervalRestriction a u‖ := by
          rw [hfu', hfu, dist_eq_norm]
        _ = ‖suzukiPositiveIntervalRestriction a (u' - u)‖ := by
          rw [map_sub]
        _ ≤ ‖u' - u‖ := norm_suzukiPositiveIntervalRestriction_le a (u' - u)
        _ = dist u' u := (dist_eq_norm u' u).symm
        _ = dist u u' := dist_comm _ _
    have hiso : dist u u' = dist q
        (suzukiOneSidedCompactSmoothL2 g hcompact hsmooth) := by
      calc
        dist u u' = dist (suzukiPositiveLogUnitary u)
            (suzukiPositiveLogUnitary u') :=
          (suzukiPositiveLogUnitary.dist_map u u').symm
        _ = dist q (suzukiOneSidedCompactSmoothL2 g hcompact hsmooth) := by
          rw [suzukiPositiveLogUnitary_compactSmooth,
            suzukiOneSidedCompactSmoothL2_eq_suzukiCompactSmoothLogL2]
    exact lt_of_le_of_lt hcontract (hiso.trans_lt hdist)
  · exact ⟨g, hsmooth, hcompact, hg, rfl⟩

/-- **Exact compression identity.**  Suzuki's literal kernel operator on `L²(0,a)` is the
finite compression of the global canonical spectral unitary. -/
theorem suzukiCanonicalPositiveHankelCompression_eq_compressedHankel
    {omega a : ℝ} (homega : 1 / 2 < omega) (ha : 0 < a) :
    suzukiCanonicalPositiveHankelCompression omega a homega =
      suzukiCompressedHankelOperator omega a homega := by
  let D := suzukiIntervalCompactSmoothCore a
  have hD : Dense D := dense_suzukiIntervalCompactSmoothCore ha
  apply ContinuousLinearMap.ext
  intro f
  have heq : Set.EqOn
      (suzukiCanonicalPositiveHankelCompression omega a homega)
      (suzukiCompressedHankelOperator omega a homega) D := by
    intro v hv
    obtain ⟨g, hsmooth, hcompact, hg, rfl⟩ := hv
    exact suzukiCanonicalPositiveHankelCompression_eq_on_compactSmooth
      homega ha g hsmooth hcompact hg
  have hfun := Continuous.ext_on hD
    (suzukiCanonicalPositiveHankelCompression omega a homega).continuous
    (suzukiCompressedHankelOperator omega a homega).continuous heq
  exact congrFun hfun f

/-! ## Norm-equality rigidity for the finite projection -/

theorem suzukiPhysicalInterval_extension_restriction_eq_of_norm_eq
    (a : ℝ) (v : SuzukiPositiveL2)
    (hnorm : ‖suzukiPositiveIntervalRestriction a v‖ = ‖v‖) :
    suzukiPhysicalIntervalPositiveIsometry a
        (suzukiPositiveIntervalRestriction a v) = v := by
  let p := suzukiPhysicalIntervalPositiveIsometry a
    (suzukiPositiveIntervalRestriction a v)
  let d := v - p
  have hRd : suzukiPositiveIntervalRestriction a d = 0 := by
    dsimp only [d, p]
    rw [map_sub, suzukiPositiveIntervalRestriction_extension, sub_self]
  have horth : inner ℂ p d = 0 := by
    dsimp only [p]
    rw [inner_suzukiPhysicalIntervalPositive_extension, hRd, inner_zero_right]
  have hdecomp : p + d = v := by
    dsimp only [d]
    abel
  have hpNorm : ‖p‖ = ‖v‖ := by
    dsimp only [p]
    rw [(suzukiPhysicalIntervalPositiveIsometry a).norm_map, hnorm]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p d horth
  rw [hdecomp, hpNorm] at hpyth
  have hd : d = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖d‖]
  dsimp only [d] at hd
  exact sub_eq_zero.mp hd |>.symm

theorem suzukiPositiveLogUnitary_canonicalHankel
    (omega : ℝ) (hinner : SuzukiCanonicalThetaMeromorphicInner omega)
    (u : SuzukiPositiveL2) :
    suzukiPositiveLogUnitary
        (suzukiCanonicalPositiveHankelUnitary omega hinner u) =
      suzukiCanonicalLogHankelUnitary omega hinner
        (suzukiPositiveLogUnitary u) := by
  have hcarrier :=
    suzukiCanonicalPositiveHankelUnitary_positiveHalfLineUnitary
      omega hinner (suzukiPositiveHalfLineUnitary.symm u)
  rw [suzukiPositiveHalfLineUnitary.apply_symm_apply] at hcarrier
  rw [suzukiPositiveLogUnitary_apply, hcarrier,
    suzukiPositiveHalfLineUnitary.symm_apply_apply]
  change logEvenUnitary
      (suzukiCanonicalHankelUnitary omega hinner
        (suzukiPositiveHalfLineUnitary.symm u)) =
    logEvenUnitary
      (suzukiCanonicalHankelUnitary omega hinner
        (logEvenUnitary.symm (suzukiPositiveLogUnitary u)))
  rw [show logEvenUnitary.symm (suzukiPositiveLogUnitary u) =
      suzukiPositiveHalfLineUnitary.symm u by
        change logEvenUnitary.symm
            (logEvenUnitary (suzukiPositiveHalfLineUnitary.symm u)) = _
        rw [logEvenUnitary.symm_apply_apply]]

/-- Upper and reflected-lower sharp support laws combine to exact compact support. -/
theorem suzukiCutoff_eq_self_of_logHalfline_fixed
    {A : ℝ} {p : SoninL2}
    (hupper : logHalflineCutoff A p = p)
    (hlower : logLowerHalflineCutoff (-A) p = p) :
    suzukiCutoff A p = p := by
  apply Lp.ext
  have hupperPoint : (logHalflineCutoff A p : ℝ → ℂ) = (p : ℝ → ℂ) :=
    congrArg (fun q : SoninL2 => (q : ℝ → ℂ)) hupper
  have hlowerPoint : (logLowerHalflineCutoff (-A) p : ℝ → ℂ) =
      (p : ℝ → ℂ) :=
    congrArg (fun q : SoninL2 => (q : ℝ → ℂ)) hlower
  filter_upwards [indicatorCutoff_ae (Icc (-A) A) measurableSet_Icc p,
    indicatorCutoff_ae (Iic A) measurableSet_Iic p,
    indicatorCutoff_ae (Ici (-A)) measurableSet_Ici p] with
      t hcompact hupperAe hlowerAe
  rw [show suzukiCutoff A p t =
      (Icc (-A) A).indicator (fun s => p s) t by
        simpa only [Function.comp_apply] using hcompact]
  by_cases ht : t ∈ Icc (-A) A
  · rw [indicator_of_mem ht]
  · rw [indicator_of_notMem ht]
    by_cases hta : t ≤ A
    · have htneg : t < -A := lt_of_not_ge (fun h => ht ⟨h, hta⟩)
      have hnotLower : t ∉ Ici (-A) := not_le_of_gt htneg
      have hlowerZero : p t = 0 := by
        rw [← hlowerPoint]
        simpa [logLowerHalflineCutoff, hnotLower] using hlowerAe
      exact hlowerZero.symm
    · have hnotUpper : t ∉ Iic A := hta
      have hupperZero : p t = 0 := by
        rw [← hupperPoint]
        simpa [logHalflineCutoff, hnotUpper] using hupperAe
      exact hupperZero.symm

end RHTower
