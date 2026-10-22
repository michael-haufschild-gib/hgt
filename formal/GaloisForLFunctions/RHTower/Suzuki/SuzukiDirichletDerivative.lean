import GaloisForLFunctions.RHTower.Suzuki.SuzukiZeroMeanScrewCompression
import GaloisForLFunctions.HTGeometry.ClosedHyperplaneInverse
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

def suzukiApertureL2ToL1Bound (a : ℝ) : ℝ :=
  ((volume : Measure (SuzukiApertureInterval a)) Set.univ ^
    (1 / (1 : ℝ) - 1 / (2 : ℝ))).toReal

theorem integral_norm_suzukiAperture_le
    (a : ℝ) (f : SuzukiApertureIntervalL2 a) :
    ∫ t : SuzukiApertureInterval a, ‖f t‖ ∂volume ≤
      suzukiApertureL2ToL1Bound a * ‖f‖ := by
  have hfint : Integrable (fun t : SuzukiApertureInterval a => f t) :=
    (Lp.memLp f).integrable (by norm_num)
  have hcoe : (fun t => (hfint.toL1 _) t) =ᵐ[volume]
      fun t : SuzukiApertureInterval a => f t := hfint.coeFn_toL1
  have h1 : ‖hfint.toL1 (fun t => f t)‖ =
      ∫ t : SuzukiApertureInterval a, ‖f t‖ ∂volume := by
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae (by filter_upwards [hcoe] with t ht; rw [ht])
  have h2 : ‖hfint.toL1 (fun t => f t)‖ =
      (eLpNorm (fun t : SuzukiApertureInterval a => f t) 1 volume).toReal := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hcoe)
  have hle := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := (volume : Measure (SuzukiApertureInterval a)))
    (p := (1 : ENNReal)) (q := (2 : ENNReal))
    (by norm_num : (1 : ENNReal) ≤ 2) (Lp.aestronglyMeasurable f)
  have hrightTop :
      eLpNorm (fun t : SuzukiApertureInterval a => f t) 2 volume *
          (volume : Measure (SuzukiApertureInterval a)) Set.univ ^
            (1 / (1 : ℝ) - 1 / (2 : ℝ)) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact (Lp.memLp f).eLpNorm_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness)
  have hreal := ENNReal.toReal_mono hrightTop hle
  rw [ENNReal.toReal_mul] at hreal
  rw [← h1, h2, suzukiApertureL2ToL1Bound, Lp.norm_def]
  simpa [mul_comm] using hreal

def suzukiAperturePrefix (a : ℝ) (f : SuzukiApertureIntervalL2 a)
    (t : SuzukiApertureInterval a) : ℂ :=
  ∫ u : SuzukiApertureInterval a, (Iic t).indicator (fun u => f u) u ∂volume

def suzukiApertureLowerKernel (a : ℝ) :
    Set (SuzukiApertureInterval a × SuzukiApertureInterval a) :=
  {p | p.2 ≤ p.1}

theorem measurableSet_suzukiApertureLowerKernel (a : ℝ) :
    MeasurableSet (suzukiApertureLowerKernel a) := by
  exact measurableSet_le measurable_snd measurable_fst

theorem aestronglyMeasurable_suzukiAperturePrefix
    (a : ℝ) (f : SuzukiApertureIntervalL2 a) :
    AEStronglyMeasurable (suzukiAperturePrefix a f) volume := by
  have hfint : Integrable (fun u : SuzukiApertureInterval a => f u) :=
    (Lp.memLp f).integrable (by norm_num)
  have hkernel : AEStronglyMeasurable
      ((suzukiApertureLowerKernel a).indicator
        (fun p : SuzukiApertureInterval a × SuzukiApertureInterval a => f p.2))
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) :=
    (hfint.comp_snd (volume : Measure (SuzukiApertureInterval a))
      |>.indicator (measurableSet_suzukiApertureLowerKernel a)).aestronglyMeasurable
  have h := hkernel.integral_prod_right'
  change AEStronglyMeasurable
    (fun t => ∫ u, if u ≤ t then f u else 0 ∂volume) volume
  simpa only [suzukiAperturePrefix, suzukiApertureLowerKernel,
    Set.indicator_apply, mem_setOf_eq] using h

theorem norm_suzukiAperturePrefix_le
    (a : ℝ) (f : SuzukiApertureIntervalL2 a)
    (t : SuzukiApertureInterval a) :
    ‖suzukiAperturePrefix a f t‖ ≤ suzukiApertureL2ToL1Bound a * ‖f‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    (∫ u : SuzukiApertureInterval a,
        ‖(Iic t).indicator (fun u => f u) u‖ ∂volume) ≤
      ∫ u : SuzukiApertureInterval a, ‖f u‖ ∂volume := by
        apply integral_mono_ae
        · exact (((Lp.memLp f).integrable (by norm_num)).indicator measurableSet_Iic).norm
        · exact ((Lp.memLp f).integrable (by norm_num)).norm
        · filter_upwards with u
          simp only [indicator_apply, mem_Iic]
          split_ifs <;> simp
    _ ≤ _ := integral_norm_suzukiAperture_le a f

theorem memLp_suzukiAperturePrefix (a : ℝ)
    (f : SuzukiApertureIntervalL2 a) :
    MemLp (suzukiAperturePrefix a f) 2 volume :=
  MemLp.of_bound (aestronglyMeasurable_suzukiAperturePrefix a f)
    (suzukiApertureL2ToL1Bound a * ‖f‖)
    (Filter.Eventually.of_forall (norm_suzukiAperturePrefix_le a f))

def suzukiAperturePrimitive (a : ℝ)
    (f : SuzukiApertureIntervalL2 a) : SuzukiApertureIntervalL2 a :=
  (memLp_suzukiAperturePrefix a f).toLp (suzukiAperturePrefix a f)

theorem suzukiAperturePrimitive_coeFn (a : ℝ)
    (f : SuzukiApertureIntervalL2 a) :
    (suzukiAperturePrimitive a f : SuzukiApertureInterval a → ℂ)
      =ᵐ[volume] suzukiAperturePrefix a f :=
  (memLp_suzukiAperturePrefix a f).coeFn_toLp

theorem volume_suzukiApertureInterval_univ (a : SuzukiPositiveAperture) :
    (volume : Measure (SuzukiApertureInterval a.1)) Set.univ = ENNReal.ofReal (2 * a.1) := by
  change (volume : Measure (Set.Icc (-a.1) a.1)) Set.univ = _
  rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc]
  congr 1
  ring

def suzukiAperturePrimitiveBound (a : SuzukiPositiveAperture) : ℝ :=
  suzukiApertureL2ToL1Bound a.1 * Real.sqrt (2 * a.1)

theorem norm_suzukiAperturePrimitive_le (a : SuzukiPositiveAperture)
    (f : SuzukiApertureIntervalL2 a.1) :
    ‖suzukiAperturePrimitive a.1 f‖ ≤
      suzukiAperturePrimitiveBound a * ‖f‖ := by
  rw [suzukiAperturePrimitive, Lp.norm_toLp]
  let C : ℝ := suzukiApertureL2ToL1Bound a.1 * ‖f‖
  have hCnonneg : 0 ≤ C :=
    mul_nonneg ENNReal.toReal_nonneg (norm_nonneg f)
  have hmono : eLpNorm (suzukiAperturePrefix a.1 f) 2 volume ≤
      eLpNorm (fun _ : SuzukiApertureInterval a.1 => (C : ℂ)) 2 volume :=
    eLpNorm_mono_ae (Filter.Eventually.of_forall fun t => by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hCnonneg]
        using norm_suzukiAperturePrefix_le a.1 f t)
  have htop : eLpNorm
      (fun _ : SuzukiApertureInterval a.1 => (C : ℂ)) 2 volume ≠ ⊤ :=
    (memLp_const (C : ℂ)).eLpNorm_ne_top
  calc
    (eLpNorm (suzukiAperturePrefix a.1 f) 2 volume).toReal ≤
        (eLpNorm (fun _ : SuzukiApertureInterval a.1 => (C : ℂ)) 2 volume).toReal :=
      ENNReal.toReal_mono htop hmono
    _ = C * Real.sqrt (2 * a.1) := by
      have hμ : (volume : Measure (SuzukiApertureInterval a.1)) ≠ 0 := by
        intro hzero
        have hu : (volume : Measure (SuzukiApertureInterval a.1)) Set.univ = 0 := by
          simp [hzero]
        rw [volume_suzukiApertureInterval_univ a] at hu
        exact (ENNReal.ofReal_pos.mpr (by linarith [a.2])).ne' hu
      rw [eLpNorm_const (C : ℂ) (by norm_num)
        hμ]
      rw [volume_suzukiApertureInterval_univ a]
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
      rw [toReal_enorm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hCnonneg,
        ENNReal.toReal_ofReal (show 0 ≤ 2 * a.1 by linarith [a.2])]
      norm_num [Real.sqrt_eq_rpow]
    _ = suzukiAperturePrimitiveBound a * ‖f‖ := by
      simp only [C, suzukiAperturePrimitiveBound]
      ring

theorem suzukiAperturePrefix_add (a : ℝ)
    (f g : SuzukiApertureIntervalL2 a) (t : SuzukiApertureInterval a) :
    suzukiAperturePrefix a (f + g) t =
      suzukiAperturePrefix a f t + suzukiAperturePrefix a g t := by
  have hcoe : (fun u => (f + g) u) =ᵐ[volume]
      fun u : SuzukiApertureInterval a => f u + g u := Lp.coeFn_add f g
  rw [suzukiAperturePrefix, suzukiAperturePrefix, suzukiAperturePrefix]
  calc
    (∫ u, (Iic t).indicator (fun u => (f + g) u) u ∂volume) =
        ∫ u, (Iic t).indicator (fun u => f u + g u) u ∂volume := by
      apply integral_congr_ae
      filter_upwards [hcoe] with u hu
      simp only [indicator_apply]
      split_ifs
      · exact hu
      · rfl
    _ = _ := by
      rw [← integral_add]
      · apply integral_congr_ae
        filter_upwards with u
        simp only [indicator_apply]
        split_ifs <;> simp
      · exact (((Lp.memLp f).integrable (by norm_num)).indicator measurableSet_Iic)
      · exact (((Lp.memLp g).integrable (by norm_num)).indicator measurableSet_Iic)

theorem suzukiAperturePrimitive_add (a : ℝ)
    (f g : SuzukiApertureIntervalL2 a) :
    suzukiAperturePrimitive a (f + g) =
      suzukiAperturePrimitive a f + suzukiAperturePrimitive a g := by
  unfold suzukiAperturePrimitive
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_suzukiAperturePrefix a (f + g)),
    MemLp.coeFn_toLp (memLp_suzukiAperturePrefix a f),
    MemLp.coeFn_toLp (memLp_suzukiAperturePrefix a g),
    Lp.coeFn_add (suzukiAperturePrimitive a f) (suzukiAperturePrimitive a g)]
      with t hfg hf hg hadd
  simp only [suzukiAperturePrimitive] at hadd
  rw [hfg, hadd]
  simp only [Pi.add_apply, hf, hg, suzukiAperturePrefix_add]

theorem suzukiAperturePrefix_smul (a : ℝ) (c : ℂ)
    (f : SuzukiApertureIntervalL2 a) (t : SuzukiApertureInterval a) :
    suzukiAperturePrefix a (c • f) t = c * suzukiAperturePrefix a f t := by
  have hcoe : (fun u => (c • f) u) =ᵐ[volume]
      fun u : SuzukiApertureInterval a => c * f u := by
    filter_upwards [Lp.coeFn_smul c f] with u hu
    simpa [smul_eq_mul] using hu
  rw [suzukiAperturePrefix, suzukiAperturePrefix]
  calc
    (∫ u, (Iic t).indicator (fun u => (c • f) u) u ∂volume) =
        ∫ u, c * (Iic t).indicator (fun u => f u) u ∂volume := by
      apply integral_congr_ae
      filter_upwards [hcoe] with u hu
      simp only [indicator_apply]
      split_ifs <;> simp [hu]
    _ = _ := by rw [integral_const_mul]

theorem suzukiAperturePrimitive_smul (a : ℝ) (c : ℂ)
    (f : SuzukiApertureIntervalL2 a) :
    suzukiAperturePrimitive a (c • f) = c • suzukiAperturePrimitive a f := by
  unfold suzukiAperturePrimitive
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_suzukiAperturePrefix a (c • f)),
    MemLp.coeFn_toLp (memLp_suzukiAperturePrefix a f),
    Lp.coeFn_smul c (suzukiAperturePrimitive a f)] with t hcf hf hsmul
  simp only [suzukiAperturePrimitive] at hsmul
  rw [hcf, hsmul]
  simp only [Pi.smul_apply, hf, suzukiAperturePrefix_smul, smul_eq_mul]

def suzukiAperturePrimitiveCLM (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  LinearMap.mkContinuous
    { toFun := suzukiAperturePrimitive a.1
      map_add' := suzukiAperturePrimitive_add a.1
      map_smul' := suzukiAperturePrimitive_smul a.1 }
    (suzukiAperturePrimitiveBound a) (norm_suzukiAperturePrimitive_le a)

theorem suzukiAperturePrefix_eq_intervalIntegral
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1)
    (t : SuzukiApertureInterval a.1) :
    suzukiAperturePrefix a.1 f t =
      ∫ x in (-a.1)..(t : ℝ), suzukiApertureZeroExtend f x := by
  have hset : Iic (t : ℝ) ∩ Icc (-a.1) a.1 = Icc (-a.1) (t : ℝ) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hxt, hxa, -⟩
      exact ⟨hxa, hxt⟩
    · rintro ⟨hxa, hxt⟩
      exact ⟨hxt, hxa, le_trans hxt t.property.2⟩
  rw [suzukiAperturePrefix]
  calc
    (∫ u : SuzukiApertureInterval a.1,
        (Iic t).indicator (fun u => f u) u ∂volume) =
      ∫ u : SuzukiApertureInterval a.1,
        (Iic (t : ℝ)).indicator (suzukiApertureZeroExtend f) (u : ℝ) ∂volume := by
          apply integral_congr_ae
          filter_upwards [suzukiApertureRepresentative_ae f] with u hu
          simp only [indicator_apply, mem_Iic]
          by_cases hut : u ≤ t
          · have hutR : (u : ℝ) ≤ (t : ℝ) := hut
            rw [if_pos hut, if_pos hutR, suzukiApertureZeroExtend_apply, hu]
          · have hutR : ¬(u : ℝ) ≤ (t : ℝ) := hut
            rw [if_neg hut, if_neg hutR]
    _ = ∫ x in Icc (-a.1) a.1,
        (Iic (t : ℝ)).indicator (suzukiApertureZeroExtend f) x := by
          rw [← integral_subtype measurableSet_Icc]
    _ = ∫ x in Icc (-a.1) (t : ℝ), suzukiApertureZeroExtend f x := by
          rw [integral_indicator measurableSet_Iic,
            Measure.restrict_restrict measurableSet_Iic, hset]
    _ = ∫ x in (-a.1)..(t : ℝ), suzukiApertureZeroExtend f x := by
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le t.property.1]

theorem integrableOn_suzukiApertureZeroExtend
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1) :
    IntegrableOn (suzukiApertureZeroExtend f) (Icc (-a.1) a.1) volume := by
  have hfinite : volume (Icc (-a.1) a.1) ≠ ∞ := by
    rw [Real.volume_Icc]
    finiteness
  have hL2 := integrableOn_Lp_of_measure_ne_top
    (suzukiApertureZeroExtendL2 f) (by norm_num : (1 : ENNReal) ≤ 2) hfinite
  exact hL2.congr_fun_ae
    (ae_restrict_of_ae (suzukiApertureZeroExtendL2_coeFn f))

/-- The indefinite-integral injection is genuinely injective on the full interval `L²` space. -/
theorem suzukiAperturePrimitiveCLM_injective (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiAperturePrimitiveCLM a) := by
  suffices hker : ∀ f : SuzukiApertureIntervalL2 a.1,
      suzukiAperturePrimitiveCLM a f = 0 → f = 0 by
    intro f g hfg
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hfg, sub_self]
  intro f hf
  have hzero : suzukiAperturePrimitive a.1 f = 0 := hf
  have hprimitiveCoe :
      (fun t => (suzukiAperturePrimitive a.1 f) t) =ᵐ[volume]
        fun _ : SuzukiApertureInterval a.1 => (0 : ℂ) := by
    rw [hzero]
    change ((0 : SuzukiApertureIntervalL2 a.1) :
      SuzukiApertureInterval a.1 → ℂ) =ᵐ[volume] 0
    exact Lp.coeFn_zero ℂ (2 : ENNReal)
      (volume : Measure (SuzukiApertureInterval a.1))
  have hprefixZero : suzukiAperturePrefix a.1 f =ᵐ[volume]
      fun _ : SuzukiApertureInterval a.1 => (0 : ℂ) :=
    (suzukiAperturePrimitive_coeFn a.1 f).symm.trans hprimitiveCoe
  let F : ℝ → ℂ := fun t =>
    ∫ u in (-a.1)..t, suzukiApertureZeroExtend f u
  have hIntOn : IntegrableOn (suzukiApertureZeroExtend f)
      (Icc (-a.1) a.1) volume := integrableOn_suzukiApertureZeroExtend a f
  have hIntOnU : IntegrableOn (suzukiApertureZeroExtend f)
      (uIcc (-a.1) a.1) volume := by
    rw [uIcc_of_le (by linarith [a.2])]
    exact hIntOn
  have hFcontinuous : ContinuousOn F (Icc (-a.1) a.1) := by
    have h := intervalIntegral.continuousOn_primitive_interval hIntOnU
    rw [uIcc_of_le (by linarith [a.2])] at h
    exact h
  have hFae : F =ᵐ[volume.restrict (Icc (-a.1) a.1)]
      fun _ : ℝ => (0 : ℂ) := by
    change ∀ᵐ x ∂volume.restrict (Icc (-a.1) a.1), F x = 0
    rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [hprefixZero] with t ht
    change (∫ u in (-a.1)..(t : ℝ), suzukiApertureZeroExtend f u) = 0
    rw [← suzukiAperturePrefix_eq_intervalIntegral a f t]
    exact ht
  have hclosure : Icc (-a.1) a.1 ⊆
      closure (interior (Icc (-a.1) a.1)) := by
    rw [interior_Icc, closure_Ioo (by linarith [a.2] : -a.1 ≠ a.1)]
  have hFzero : Set.EqOn F (fun _ : ℝ => (0 : ℂ)) (Icc (-a.1) a.1) :=
    (volume : Measure ℝ).eqOn_of_ae_eq hFae hFcontinuous continuousOn_const hclosure
  have hldt := hIntOnU.intervalIntegrable.ae_hasDerivAt_integral
  have hldtRestrict :
      ∀ᵐ x ∂volume.restrict (Icc (-a.1) a.1),
        x ∈ uIcc (-a.1) a.1 → ∀ c ∈ uIcc (-a.1) a.1,
          HasDerivAt (fun y => ∫ t in c..y, suzukiApertureZeroExtend f t)
            (suzukiApertureZeroExtend f x) x :=
    ae_restrict_of_ae hldt
  have hfzero : suzukiApertureZeroExtend f =ᵐ[
      volume.restrict (Icc (-a.1) a.1)] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [hldtRestrict,
      (volume.restrict (Icc (-a.1) a.1)).ae_ne (-a.1),
      (volume.restrict (Icc (-a.1) a.1)).ae_ne a.1,
      ae_restrict_mem (μ := volume) measurableSet_Icc]
        with x hxderiv hxleft hxright hx
    have hxoo : x ∈ Ioo (-a.1) a.1 :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxleft),
        lt_of_le_of_ne hx.2 hxright⟩
    have hord : -a.1 ≤ a.1 := by linarith [a.2]
    have hxu : x ∈ uIcc (-a.1) a.1 := by
      rw [uIcc_of_le hord]
      exact hx
    have hleftmem : -a.1 ∈ uIcc (-a.1) a.1 := by
      rw [uIcc_of_le hord]
      exact left_mem_Icc.mpr hord
    have hprimitive : HasDerivAt F (suzukiApertureZeroExtend f x) x := by
      exact hxderiv hxu (-a.1) hleftmem
    have hlocal : Filter.EventuallyEq (nhds x) F (fun _ : ℝ => (0 : ℂ)) := by
      filter_upwards [Ioo_mem_nhds hxoo.1 hxoo.2] with y hy
      exact hFzero (Ioo_subset_Icc_self hy)
    have hzeroDeriv : HasDerivAt F 0 x :=
      (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hlocal
    exact hprimitive.unique hzeroDeriv
  have hExtZero : suzukiApertureZeroExtend f =ᵐ[volume]
      fun _ : ℝ => (0 : ℂ) := by
    apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-a.1) a.1)
    · exact hfzero
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl]
        with x hx
      exact suzukiApertureZeroExtend_eq_zero_of_notMem f hx
  have hL2zero : suzukiApertureZeroExtendL2 f = 0 := by
    apply Lp.ext
    filter_upwards [suzukiApertureZeroExtendL2_coeFn f, hExtZero,
      Lp.coeFn_zero ℂ (2 : ENNReal) volume] with x hcoe hfun hzeroCoe
    rw [hcoe, hfun, hzeroCoe]
    simp
  have hzeroMap : suzukiApertureZeroExtendL2
      (0 : SuzukiApertureIntervalL2 a.1) = 0 := by
    have hz := map_zero (suzukiApertureZeroExtendLinearIsometry a)
    exact congrArg Subtype.val hz
  exact suzukiApertureZeroExtendL2_injective (hL2zero.trans hzeroMap.symm)

/-! ## Reverse primitive and the exact adjoint identity -/

def suzukiApertureUpperPrefix (a : ℝ) (f : SuzukiApertureIntervalL2 a)
    (t : SuzukiApertureInterval a) : ℂ :=
  ∫ u : SuzukiApertureInterval a, (Ici t).indicator (fun u => f u) u ∂volume

def suzukiApertureUpperKernel (a : ℝ) :
    Set (SuzukiApertureInterval a × SuzukiApertureInterval a) :=
  {p | p.1 ≤ p.2}

theorem measurableSet_suzukiApertureUpperKernel (a : ℝ) :
    MeasurableSet (suzukiApertureUpperKernel a) := by
  exact measurableSet_le measurable_fst measurable_snd

theorem aestronglyMeasurable_suzukiApertureUpperPrefix
    (a : ℝ) (f : SuzukiApertureIntervalL2 a) :
    AEStronglyMeasurable (suzukiApertureUpperPrefix a f) volume := by
  have hfint : Integrable (fun u : SuzukiApertureInterval a => f u) :=
    (Lp.memLp f).integrable (by norm_num)
  have hkernel : AEStronglyMeasurable
      ((suzukiApertureUpperKernel a).indicator
        (fun p : SuzukiApertureInterval a × SuzukiApertureInterval a => f p.2))
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) :=
    (hfint.comp_snd (volume : Measure (SuzukiApertureInterval a))
      |>.indicator (measurableSet_suzukiApertureUpperKernel a)).aestronglyMeasurable
  have h := hkernel.integral_prod_right'
  change AEStronglyMeasurable
    (fun t => ∫ u, if t ≤ u then f u else 0 ∂volume) volume
  simpa only [suzukiApertureUpperPrefix, suzukiApertureUpperKernel,
    Set.indicator_apply, mem_setOf_eq] using h

theorem norm_suzukiApertureUpperPrefix_le
    (a : ℝ) (f : SuzukiApertureIntervalL2 a)
    (t : SuzukiApertureInterval a) :
    ‖suzukiApertureUpperPrefix a f t‖ ≤
      suzukiApertureL2ToL1Bound a * ‖f‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    (∫ u : SuzukiApertureInterval a,
        ‖(Ici t).indicator (fun u => f u) u‖ ∂volume) ≤
      ∫ u : SuzukiApertureInterval a, ‖f u‖ ∂volume := by
        apply integral_mono_ae
        · exact (((Lp.memLp f).integrable (by norm_num)).indicator measurableSet_Ici).norm
        · exact ((Lp.memLp f).integrable (by norm_num)).norm
        · filter_upwards with u
          simp only [indicator_apply]
          split_ifs <;> simp
    _ ≤ _ := integral_norm_suzukiAperture_le a f

theorem memLp_suzukiApertureUpperPrefix (a : ℝ)
    (f : SuzukiApertureIntervalL2 a) :
    MemLp (suzukiApertureUpperPrefix a f) 2 volume :=
  MemLp.of_bound (aestronglyMeasurable_suzukiApertureUpperPrefix a f)
    (suzukiApertureL2ToL1Bound a * ‖f‖)
    (Filter.Eventually.of_forall (norm_suzukiApertureUpperPrefix_le a f))

def suzukiApertureUpperPrimitive (a : ℝ)
    (f : SuzukiApertureIntervalL2 a) : SuzukiApertureIntervalL2 a :=
  (memLp_suzukiApertureUpperPrefix a f).toLp (suzukiApertureUpperPrefix a f)

theorem suzukiApertureUpperPrimitive_coeFn (a : ℝ)
    (f : SuzukiApertureIntervalL2 a) :
    (suzukiApertureUpperPrimitive a f : SuzukiApertureInterval a → ℂ)
      =ᵐ[volume] suzukiApertureUpperPrefix a f :=
  (memLp_suzukiApertureUpperPrefix a f).coeFn_toLp

theorem suzukiApertureUpperPrefix_add (a : ℝ)
    (f g : SuzukiApertureIntervalL2 a) (t : SuzukiApertureInterval a) :
    suzukiApertureUpperPrefix a (f + g) t =
      suzukiApertureUpperPrefix a f t + suzukiApertureUpperPrefix a g t := by
  have hcoe : (fun u => (f + g) u) =ᵐ[volume]
      fun u : SuzukiApertureInterval a => f u + g u := Lp.coeFn_add f g
  rw [suzukiApertureUpperPrefix, suzukiApertureUpperPrefix,
    suzukiApertureUpperPrefix]
  calc
    (∫ u, (Ici t).indicator (fun u => (f + g) u) u ∂volume) =
        ∫ u, (Ici t).indicator (fun u => f u + g u) u ∂volume := by
      apply integral_congr_ae
      filter_upwards [hcoe] with u hu
      simp only [indicator_apply]
      split_ifs
      · exact hu
      · rfl
    _ = _ := by
      rw [← integral_add]
      · apply integral_congr_ae
        filter_upwards with u
        simp only [indicator_apply]
        split_ifs <;> simp
      · exact (((Lp.memLp f).integrable (by norm_num)).indicator measurableSet_Ici)
      · exact (((Lp.memLp g).integrable (by norm_num)).indicator measurableSet_Ici)

theorem suzukiApertureUpperPrimitive_add (a : ℝ)
    (f g : SuzukiApertureIntervalL2 a) :
    suzukiApertureUpperPrimitive a (f + g) =
      suzukiApertureUpperPrimitive a f + suzukiApertureUpperPrimitive a g := by
  unfold suzukiApertureUpperPrimitive
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_suzukiApertureUpperPrefix a (f + g)),
    MemLp.coeFn_toLp (memLp_suzukiApertureUpperPrefix a f),
    MemLp.coeFn_toLp (memLp_suzukiApertureUpperPrefix a g),
    Lp.coeFn_add (suzukiApertureUpperPrimitive a f)
      (suzukiApertureUpperPrimitive a g)] with t hfg hf hg hadd
  simp only [suzukiApertureUpperPrimitive] at hadd
  rw [hfg, hadd]
  simp only [Pi.add_apply, hf, hg, suzukiApertureUpperPrefix_add]

theorem suzukiApertureUpperPrefix_smul (a : ℝ) (c : ℂ)
    (f : SuzukiApertureIntervalL2 a) (t : SuzukiApertureInterval a) :
    suzukiApertureUpperPrefix a (c • f) t =
      c * suzukiApertureUpperPrefix a f t := by
  have hcoe : (fun u => (c • f) u) =ᵐ[volume]
      fun u : SuzukiApertureInterval a => c * f u := by
    filter_upwards [Lp.coeFn_smul c f] with u hu
    simpa [smul_eq_mul] using hu
  rw [suzukiApertureUpperPrefix, suzukiApertureUpperPrefix]
  calc
    (∫ u, (Ici t).indicator (fun u => (c • f) u) u ∂volume) =
        ∫ u, c * (Ici t).indicator (fun u => f u) u ∂volume := by
      apply integral_congr_ae
      filter_upwards [hcoe] with u hu
      simp only [indicator_apply]
      split_ifs <;> simp [hu]
    _ = _ := by rw [integral_const_mul]

theorem suzukiApertureUpperPrimitive_smul (a : ℝ) (c : ℂ)
    (f : SuzukiApertureIntervalL2 a) :
    suzukiApertureUpperPrimitive a (c • f) =
      c • suzukiApertureUpperPrimitive a f := by
  unfold suzukiApertureUpperPrimitive
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_suzukiApertureUpperPrefix a (c • f)),
    MemLp.coeFn_toLp (memLp_suzukiApertureUpperPrefix a f),
    Lp.coeFn_smul c (suzukiApertureUpperPrimitive a f)] with t hcf hf hsmul
  simp only [suzukiApertureUpperPrimitive] at hsmul
  rw [hcf, hsmul]
  simp only [Pi.smul_apply, hf, suzukiApertureUpperPrefix_smul, smul_eq_mul]

theorem norm_suzukiApertureUpperPrimitive_le (a : SuzukiPositiveAperture)
    (f : SuzukiApertureIntervalL2 a.1) :
    ‖suzukiApertureUpperPrimitive a.1 f‖ ≤
      suzukiAperturePrimitiveBound a * ‖f‖ := by
  rw [suzukiApertureUpperPrimitive, Lp.norm_toLp]
  let C : ℝ := suzukiApertureL2ToL1Bound a.1 * ‖f‖
  have hCnonneg : 0 ≤ C :=
    mul_nonneg ENNReal.toReal_nonneg (norm_nonneg f)
  have hmono : eLpNorm (suzukiApertureUpperPrefix a.1 f) 2 volume ≤
      eLpNorm (fun _ : SuzukiApertureInterval a.1 => (C : ℂ)) 2 volume :=
    eLpNorm_mono_ae (Filter.Eventually.of_forall fun t => by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hCnonneg]
        using norm_suzukiApertureUpperPrefix_le a.1 f t)
  have htop : eLpNorm
      (fun _ : SuzukiApertureInterval a.1 => (C : ℂ)) 2 volume ≠ ⊤ :=
    (memLp_const (C : ℂ)).eLpNorm_ne_top
  calc
    (eLpNorm (suzukiApertureUpperPrefix a.1 f) 2 volume).toReal ≤
        (eLpNorm (fun _ : SuzukiApertureInterval a.1 => (C : ℂ)) 2 volume).toReal :=
      ENNReal.toReal_mono htop hmono
    _ = C * Real.sqrt (2 * a.1) := by
      have hμ : (volume : Measure (SuzukiApertureInterval a.1)) ≠ 0 := by
        intro hzero
        have hu : (volume : Measure (SuzukiApertureInterval a.1)) Set.univ = 0 := by
          simp [hzero]
        rw [volume_suzukiApertureInterval_univ a] at hu
        exact (ENNReal.ofReal_pos.mpr (by linarith [a.2])).ne' hu
      rw [eLpNorm_const (C : ℂ) (by norm_num) hμ,
        volume_suzukiApertureInterval_univ a, ENNReal.toReal_mul,
        ← ENNReal.toReal_rpow, toReal_enorm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hCnonneg,
        ENNReal.toReal_ofReal (show 0 ≤ 2 * a.1 by linarith [a.2])]
      norm_num [Real.sqrt_eq_rpow]
    _ = suzukiAperturePrimitiveBound a * ‖f‖ := by
      simp only [C, suzukiAperturePrimitiveBound]
      ring

def suzukiApertureUpperPrimitiveCLM (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  LinearMap.mkContinuous
    { toFun := suzukiApertureUpperPrimitive a.1
      map_add' := suzukiApertureUpperPrimitive_add a.1
      map_smul' := suzukiApertureUpperPrimitive_smul a.1 }
    (suzukiAperturePrimitiveBound a) (norm_suzukiApertureUpperPrimitive_le a)

theorem integrable_conj_suzukiApertureCoe (a : ℝ)
    (f : SuzukiApertureIntervalL2 a) :
    Integrable (fun t : SuzukiApertureInterval a => (starRingEnd ℂ) (f t)) := by
  exact ((Lp.memLp f).integrable (by norm_num)).norm.mono'
    (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun t => by rw [RCLike.norm_conj])

def suzukiApertureTriangleKernel (a : ℝ)
    (f g : SuzukiApertureIntervalL2 a)
    (p : SuzukiApertureInterval a × SuzukiApertureInterval a) : ℂ :=
  (suzukiApertureUpperKernel a).indicator
    (fun p => (starRingEnd ℂ) (f p.1) * g p.2) p

theorem integrable_suzukiApertureTriangleKernel (a : ℝ)
    (f g : SuzukiApertureIntervalL2 a) :
    Integrable (suzukiApertureTriangleKernel a f g)
      ((volume : Measure (SuzukiApertureInterval a)).prod volume) := by
  exact ((integrable_conj_suzukiApertureCoe a f).mul_prod
    ((Lp.memLp g).integrable (by norm_num))).indicator
      (measurableSet_suzukiApertureUpperKernel a)

theorem conj_suzukiAperturePrefix_mul_eq_integral_triangle
    (a : ℝ) (f g : SuzukiApertureIntervalL2 a)
    (t : SuzukiApertureInterval a) :
    (starRingEnd ℂ) (suzukiAperturePrefix a f t) * g t =
      ∫ u, suzukiApertureTriangleKernel a f g (u, t) ∂volume := by
  rw [suzukiAperturePrefix, ← integral_conj, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with u
  simp only [suzukiApertureTriangleKernel, suzukiApertureUpperKernel,
    indicator_apply, mem_setOf_eq, mem_Iic]
  split_ifs <;> simp

theorem conj_mul_suzukiApertureUpperPrefix_eq_integral_triangle
    (a : ℝ) (f g : SuzukiApertureIntervalL2 a)
    (u : SuzukiApertureInterval a) :
    (starRingEnd ℂ) (f u) * suzukiApertureUpperPrefix a g u =
      ∫ t, suzukiApertureTriangleKernel a f g (u, t) ∂volume := by
  rw [suzukiApertureUpperPrefix, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [suzukiApertureTriangleKernel, suzukiApertureUpperKernel,
    indicator_apply, mem_setOf_eq, mem_Ici]
  split_ifs <;> simp

theorem integral_conj_suzukiAperturePrefix_mul_eq_upperPrefix
    (a : ℝ) (f g : SuzukiApertureIntervalL2 a) :
    (∫ t, (starRingEnd ℂ) (suzukiAperturePrefix a f t) * g t ∂volume) =
      ∫ u, (starRingEnd ℂ) (f u) * suzukiApertureUpperPrefix a g u ∂volume := by
  have htri := integrable_suzukiApertureTriangleKernel a f g
  calc
    (∫ t, (starRingEnd ℂ) (suzukiAperturePrefix a f t) * g t ∂volume) =
      ∫ t, ∫ u, suzukiApertureTriangleKernel a f g (u, t) ∂volume ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (conj_suzukiAperturePrefix_mul_eq_integral_triangle a f g)
    _ = ∫ u, ∫ t, suzukiApertureTriangleKernel a f g (u, t) ∂volume ∂volume := by
      exact (integral_integral_swap
        (f := fun u t => suzukiApertureTriangleKernel a f g (u, t)) htri).symm
    _ = ∫ u, (starRingEnd ℂ) (f u) *
        suzukiApertureUpperPrefix a g u ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun u => (conj_mul_suzukiApertureUpperPrefix_eq_integral_triangle a f g u).symm)

/-- The reverse primitive is exactly the Hilbert adjoint of the forward primitive. -/
theorem inner_suzukiAperturePrimitive_eq_upperPrimitive
    (a : SuzukiPositiveAperture) (f g : SuzukiApertureIntervalL2 a.1) :
    inner ℂ (suzukiAperturePrimitiveCLM a f) g =
      inner ℂ f (suzukiApertureUpperPrimitiveCLM a g) := by
  rw [inner_suzukiApertureL2_eq_integral,
    inner_suzukiApertureL2_eq_integral]
  calc
    (∫ t, (starRingEnd ℂ) (suzukiAperturePrimitiveCLM a f t) * g t ∂volume) =
      ∫ t, (starRingEnd ℂ) (suzukiAperturePrefix a.1 f t) * g t ∂volume := by
        apply integral_congr_ae
        filter_upwards [suzukiAperturePrimitive_coeFn a.1 f] with t ht
        change (starRingEnd ℂ) ((suzukiAperturePrimitive a.1 f) t) * g t = _
        rw [ht]
    _ = ∫ u, (starRingEnd ℂ) (f u) *
        suzukiApertureUpperPrefix a.1 g u ∂volume :=
      integral_conj_suzukiAperturePrefix_mul_eq_upperPrefix a.1 f g
    _ = ∫ u, (starRingEnd ℂ) (f u) *
        suzukiApertureUpperPrimitiveCLM a g u ∂volume := by
      apply integral_congr_ae
      filter_upwards [suzukiApertureUpperPrimitive_coeFn a.1 g] with u hu
      change _ = (starRingEnd ℂ) (f u) * (suzukiApertureUpperPrimitive a.1 g) u
      rw [hu]

theorem suzukiApertureUpperPrimitiveCLM_eq_adjoint
    (a : SuzukiPositiveAperture) :
    suzukiApertureUpperPrimitiveCLM a =
      (suzukiAperturePrimitiveCLM a).adjoint := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_suzukiAperturePrimitive_eq_upperPrimitive a f g).symm

theorem suzukiApertureUpperPrefix_eq_intervalIntegral
    (a : SuzukiPositiveAperture) (f : SuzukiApertureIntervalL2 a.1)
    (t : SuzukiApertureInterval a.1) :
    suzukiApertureUpperPrefix a.1 f t =
      ∫ x in (t : ℝ)..a.1, suzukiApertureZeroExtend f x := by
  have hset : Ici (t : ℝ) ∩ Icc (-a.1) a.1 = Icc (t : ℝ) a.1 := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨htx, -, hxa⟩
      exact ⟨htx, hxa⟩
    · rintro ⟨htx, hxa⟩
      exact ⟨htx, le_trans t.property.1 htx, hxa⟩
  rw [suzukiApertureUpperPrefix]
  calc
    (∫ u : SuzukiApertureInterval a.1,
        (Ici t).indicator (fun u => f u) u ∂volume) =
      ∫ u : SuzukiApertureInterval a.1,
        (Ici (t : ℝ)).indicator (suzukiApertureZeroExtend f) (u : ℝ) ∂volume := by
          apply integral_congr_ae
          filter_upwards [suzukiApertureRepresentative_ae f] with u hu
          simp only [indicator_apply, mem_Ici]
          by_cases htu : t ≤ u
          · have htuR : (t : ℝ) ≤ (u : ℝ) := htu
            rw [if_pos htu, if_pos htuR, suzukiApertureZeroExtend_apply, hu]
          · have htuR : ¬(t : ℝ) ≤ (u : ℝ) := htu
            rw [if_neg htu, if_neg htuR]
    _ = ∫ x in Icc (-a.1) a.1,
        (Ici (t : ℝ)).indicator (suzukiApertureZeroExtend f) x := by
          rw [← integral_subtype measurableSet_Icc]
    _ = ∫ x in Icc (t : ℝ) a.1, suzukiApertureZeroExtend f x := by
          rw [integral_indicator measurableSet_Ici,
            Measure.restrict_restrict measurableSet_Ici, hset]
    _ = ∫ x in (t : ℝ)..a.1, suzukiApertureZeroExtend f x := by
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le t.property.2]

/-- Projection of the reverse primitive to the zero-mean hyperplane has trivial kernel. -/
theorem suzukiApertureProjectedUpperPrimitiveCLM_injective
    (a : SuzukiPositiveAperture) :
    Function.Injective
      ((suzukiApertureZeroMeanProjection a).comp
        (suzukiApertureUpperPrimitiveCLM a)) := by
  letI : CompleteSpace (SuzukiApertureZeroMean a) :=
    (suzukiApertureZeroMean_isClosed a).completeSpace_coe
  suffices hker : ∀ f : SuzukiApertureIntervalL2 a.1,
      (suzukiApertureZeroMeanProjection a).comp
          (suzukiApertureUpperPrimitiveCLM a) f = 0 → f = 0 by
    intro f g hfg
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hfg, sub_self]
  intro f hf
  have horth : suzukiApertureUpperPrimitiveCLM a f ∈
      (SuzukiApertureZeroMean a)ᗮ :=
    (SuzukiApertureZeroMean a).orthogonalProjectionOnto_eq_zero_iff.mp hf
  let S : Submodule ℂ (SuzukiApertureIntervalL2 a.1) :=
    ℂ ∙ suzukiApertureIntervalOne a
  letI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton _)
  have hspan : Sᗮᗮ = S := by
    rw [S.orthogonal_orthogonal_eq_closure, S.topologicalClosure_eq_self]
  have hmemSpan : suzukiApertureUpperPrimitiveCLM a f ∈ S := by
    change suzukiApertureUpperPrimitiveCLM a f ∈ Sᗮᗮ at horth
    rwa [hspan] at horth
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmemSpan
  have hupperEq : suzukiApertureUpperPrimitive a.1 f =
      c • suzukiApertureIntervalOne a := hc.symm
  have hupperLpEq :
      (fun t => (suzukiApertureUpperPrimitive a.1 f) t) =ᵐ[volume]
        fun t => (c • suzukiApertureIntervalOne a) t := by
    rw [hupperEq]
  have hupperConst : suzukiApertureUpperPrefix a.1 f =ᵐ[volume]
      fun _ : SuzukiApertureInterval a.1 => c := by
    filter_upwards [suzukiApertureUpperPrimitive_coeFn a.1 f,
      hupperLpEq, Lp.coeFn_smul c (suzukiApertureIntervalOne a),
      suzukiApertureIntervalOne_coeFn a] with t hu heq hsmul hone
    calc
      suzukiApertureUpperPrefix a.1 f t =
          (suzukiApertureUpperPrimitive a.1 f) t := hu.symm
      _ = (c • suzukiApertureIntervalOne a) t := heq
      _ = c • (suzukiApertureIntervalOne a) t := hsmul
      _ = c := by rw [hone]; simp
  let F : ℝ → ℂ := fun t =>
    ∫ u in t..a.1, suzukiApertureZeroExtend f u
  have hIntOn : IntegrableOn (suzukiApertureZeroExtend f)
      (Icc (-a.1) a.1) volume := integrableOn_suzukiApertureZeroExtend a f
  have hIntOnU : IntegrableOn (suzukiApertureZeroExtend f)
      (uIcc (-a.1) a.1) volume := by
    rw [uIcc_of_le (by linarith [a.2])]
    exact hIntOn
  have hFcontinuous : ContinuousOn F (Icc (-a.1) a.1) := by
    have h := intervalIntegral.continuousOn_primitive_interval_left hIntOnU
    rw [uIcc_of_le (by linarith [a.2])] at h
    exact h
  have hFae : F =ᵐ[volume.restrict (Icc (-a.1) a.1)]
      fun _ : ℝ => c := by
    change ∀ᵐ x ∂volume.restrict (Icc (-a.1) a.1), F x = c
    rw [ae_restrict_iff_subtype measurableSet_Icc]
    filter_upwards [hupperConst] with t ht
    change (∫ u in (t : ℝ)..a.1, suzukiApertureZeroExtend f u) = c
    rw [← suzukiApertureUpperPrefix_eq_intervalIntegral a f t]
    exact ht
  have hclosure : Icc (-a.1) a.1 ⊆
      closure (interior (Icc (-a.1) a.1)) := by
    rw [interior_Icc, closure_Ioo (by linarith [a.2] : -a.1 ≠ a.1)]
  have hFconst : Set.EqOn F (fun _ : ℝ => c) (Icc (-a.1) a.1) :=
    (volume : Measure ℝ).eqOn_of_ae_eq hFae hFcontinuous continuousOn_const hclosure
  have hldt := hIntOnU.intervalIntegrable.ae_hasDerivAt_integral
  have hldtRestrict :
      ∀ᵐ x ∂volume.restrict (Icc (-a.1) a.1),
        x ∈ uIcc (-a.1) a.1 → ∀ d ∈ uIcc (-a.1) a.1,
          HasDerivAt (fun y => ∫ t in d..y, suzukiApertureZeroExtend f t)
            (suzukiApertureZeroExtend f x) x :=
    ae_restrict_of_ae hldt
  have hfzero : suzukiApertureZeroExtend f =ᵐ[
      volume.restrict (Icc (-a.1) a.1)] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [hldtRestrict,
      (volume.restrict (Icc (-a.1) a.1)).ae_ne (-a.1),
      (volume.restrict (Icc (-a.1) a.1)).ae_ne a.1,
      ae_restrict_mem (μ := volume) measurableSet_Icc]
        with x hxderiv hxleft hxright hx
    have hxoo : x ∈ Ioo (-a.1) a.1 :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxleft),
        lt_of_le_of_ne hx.2 hxright⟩
    have hord : -a.1 ≤ a.1 := by linarith [a.2]
    have hxu : x ∈ uIcc (-a.1) a.1 := by
      rw [uIcc_of_le hord]
      exact hx
    have hrightmem : a.1 ∈ uIcc (-a.1) a.1 := by
      rw [uIcc_of_le hord]
      exact right_mem_Icc.mpr hord
    have hprimitive : HasDerivAt
        (fun y => ∫ t in a.1..y, suzukiApertureZeroExtend f t)
        (suzukiApertureZeroExtend f x) x := hxderiv hxu a.1 hrightmem
    have hFderiv : HasDerivAt F (-suzukiApertureZeroExtend f x) x := by
      have hneg := hprimitive.neg
      apply hneg.congr_of_eventuallyEq
      filter_upwards with y
      change (∫ t in y..a.1, suzukiApertureZeroExtend f t) =
        -(∫ t in a.1..y, suzukiApertureZeroExtend f t)
      rw [intervalIntegral.integral_symm]
    have hlocal : Filter.EventuallyEq (nhds x) F (fun _ : ℝ => c) := by
      filter_upwards [Ioo_mem_nhds hxoo.1 hxoo.2] with y hy
      exact hFconst (Ioo_subset_Icc_self hy)
    have hzeroDeriv : HasDerivAt F 0 x :=
      (hasDerivAt_const x c).congr_of_eventuallyEq hlocal
    exact neg_eq_zero.mp (hFderiv.unique hzeroDeriv)
  have hExtZero : suzukiApertureZeroExtend f =ᵐ[volume]
      fun _ : ℝ => (0 : ℂ) := by
    apply ae_of_ae_restrict_of_ae_restrict_compl (Icc (-a.1) a.1)
    · exact hfzero
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl]
        with x hx
      exact suzukiApertureZeroExtend_eq_zero_of_notMem f hx
  have hL2zero : suzukiApertureZeroExtendL2 f = 0 := by
    apply Lp.ext
    filter_upwards [suzukiApertureZeroExtendL2_coeFn f, hExtZero,
      Lp.coeFn_zero ℂ (2 : ENNReal) volume] with x hcoe hfun hzeroCoe
    rw [hcoe, hfun, hzeroCoe]
    simp
  have hzeroMap : suzukiApertureZeroExtendL2
      (0 : SuzukiApertureIntervalL2 a.1) = 0 := by
    have hz := map_zero (suzukiApertureZeroExtendLinearIsometry a)
    exact congrArg Subtype.val hz
  exact suzukiApertureZeroExtendL2_injective (hL2zero.trans hzeroMap.symm)

/-! ## The bounded inverse coordinate for `D = i d/dx` -/

/-- The primitive restricted to zero-mean derivatives.  Its range is the exact one-dimensional
Dirichlet Sobolev domain: primitives vanish at both endpoints. -/
def suzukiDirichletInverseCLM (a : SuzukiPositiveAperture) :
    SuzukiApertureZeroMean a →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  (suzukiAperturePrimitiveCLM a).comp (SuzukiApertureZeroMean a).subtypeL

theorem suzukiDirichletInverseCLM_injective (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiDirichletInverseCLM a) := by
  intro f g hfg
  apply Subtype.ext
  exact suzukiAperturePrimitiveCLM_injective a hfg

/-- Exact Hilbert adjoint of the zero-mean primitive: reverse primitive followed by mean-zero
projection. -/
def suzukiDirichletInverseAdjointCLM (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →L[ℂ] SuzukiApertureZeroMean a :=
  (suzukiApertureZeroMeanProjection a).comp
    (suzukiApertureUpperPrimitiveCLM a)

theorem inner_suzukiDirichletInverse_eq_adjoint
    (a : SuzukiPositiveAperture) (f : SuzukiApertureZeroMean a)
    (g : SuzukiApertureIntervalL2 a.1) :
    inner ℂ (suzukiDirichletInverseCLM a f) g =
      inner ℂ f (suzukiDirichletInverseAdjointCLM a g) := by
  change inner ℂ (suzukiAperturePrimitiveCLM a
      (f : SuzukiApertureIntervalL2 a.1)) g =
    inner ℂ f (suzukiApertureZeroMeanProjection a
      (suzukiApertureUpperPrimitiveCLM a g))
  rw [inner_suzukiAperturePrimitive_eq_upperPrimitive]
  exact ((SuzukiApertureZeroMean a).inner_orthogonalProjectionOnto_eq_of_mem_left
    f (suzukiApertureUpperPrimitiveCLM a g)).symm

theorem suzukiDirichletInverseAdjointCLM_eq_adjoint
    (a : SuzukiPositiveAperture) :
    suzukiDirichletInverseAdjointCLM a =
      (suzukiDirichletInverseCLM a).adjoint := by
  letI : CompleteSpace (SuzukiApertureZeroMean a) :=
    (suzukiApertureZeroMean_isClosed a).completeSpace_coe
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_suzukiDirichletInverse_eq_adjoint a f g).symm

theorem suzukiDirichletInverseAdjointCLM_injective
    (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiDirichletInverseAdjointCLM a) :=
  suzukiApertureProjectedUpperPrimitiveCLM_injective a

/-- Zero-endpoint primitives are dense in literal interval `L²`; equivalently the Dirichlet
derivative is densely defined. -/
theorem dense_suzukiDirichletInverseCLM_range (a : SuzukiPositiveAperture) :
    Dense ((suzukiDirichletInverseCLM a).range :
      Set (SuzukiApertureIntervalL2 a.1)) := by
  letI : CompleteSpace (SuzukiApertureZeroMean a) :=
    (suzukiApertureZeroMean_isClosed a).completeSpace_coe
  let B := suzukiDirichletInverseCLM a
  have hadjInj : Function.Injective B.adjoint := by
    rw [← suzukiDirichletInverseAdjointCLM_eq_adjoint a]
    exact suzukiDirichletInverseAdjointCLM_injective a
  have hker : B.adjoint.ker = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun v hv => hadjInj (by simpa using hv)
  have horth : B.rangeᗮ = ⊥ := by
    rw [B.orthogonal_range, hker]
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  calc
    B.range.topologicalClosure = B.rangeᗮᗮ :=
      B.range.orthogonal_orthogonal_eq_closure.symm
    _ = (⊥ : Submodule ℂ (SuzukiApertureIntervalL2 a.1))ᗮ := by rw [horth]
    _ = ⊤ := Submodule.bot_orthogonal_eq_top

/-! ## Literal closed Dirichlet derivative -/

def suzukiDirichletOutputCLM (a : SuzukiPositiveAperture) :
    SuzukiApertureZeroMean a →L[ℂ] SuzukiApertureIntervalL2 a.1 :=
  Complex.I • (SuzukiApertureZeroMean a).subtypeL

theorem suzukiDirichletOutputCLM_injective (a : SuzukiPositiveAperture) :
    Function.Injective (suzukiDirichletOutputCLM a) := by
  intro f g hfg
  apply Subtype.ext
  have hcancel := congrArg
    (fun z : SuzukiApertureIntervalL2 a.1 => Complex.I⁻¹ • z) hfg
  simpa [suzukiDirichletOutputCLM, smul_smul, Complex.I_ne_zero] using hcancel

/-- Literal `D = i d/dx` on the zero-endpoint primitive domain.  Defining it as the closed graph
inverse of integration makes domain and closure data structural rather than postulated. -/
def suzukiDirichletDerivative (a : SuzukiPositiveAperture) :
    SuzukiApertureIntervalL2 a.1 →ₗ.[ℂ] SuzukiApertureIntervalL2 a.1 :=
  closedGraphTransform (SuzukiApertureZeroMean a)
    (suzukiDirichletInverseCLM a) (suzukiDirichletOutputCLM a)

/-- Exact one-dimensional realization of `H₀¹(-a,a)` as zero-mean primitives. -/
def SuzukiApertureH01 (a : SuzukiPositiveAperture) :
    Submodule ℂ (SuzukiApertureIntervalL2 a.1) :=
  (suzukiDirichletInverseCLM a).range

theorem suzukiDirichletDerivative_domain (a : SuzukiPositiveAperture) :
    (suzukiDirichletDerivative a).domain = SuzukiApertureH01 a := by
  exact closedGraphTransform_domain _ _ _

theorem suzukiDirichletDerivative_dense_domain (a : SuzukiPositiveAperture) :
    Dense ((suzukiDirichletDerivative a).domain :
      Set (SuzukiApertureIntervalL2 a.1)) := by
  rw [suzukiDirichletDerivative_domain]
  exact dense_suzukiDirichletInverseCLM_range a

theorem suzukiDirichletDerivative_apply_inverse
    (a : SuzukiPositiveAperture) (f : SuzukiApertureZeroMean a) :
    ∃ hmem : suzukiDirichletInverseCLM a f ∈
        (suzukiDirichletDerivative a).domain,
      suzukiDirichletDerivative a
        ⟨suzukiDirichletInverseCLM a f, hmem⟩ =
          Complex.I • (f : SuzukiApertureIntervalL2 a.1) := by
  have h := closedGraphTransform_apply_B (SuzukiApertureZeroMean a)
    (suzukiDirichletInverseCLM a) (suzukiDirichletOutputCLM a)
    (suzukiDirichletInverseCLM_injective a) f
  refine ⟨h.1, ?_⟩
  exact h.2

theorem suzukiDirichletOutputCLM_antilipschitz
    (a : SuzukiPositiveAperture) :
    AntilipschitzWith 1
      ((suzukiDirichletInverseCLM a).prod (suzukiDirichletOutputCLM a)) := by
  apply ((suzukiDirichletInverseCLM a).prod
    (suzukiDirichletOutputCLM a)).antilipschitz_of_bound
  intro f
  simp only [NNReal.coe_one, one_mul]
  change ‖f‖ ≤ max ‖suzukiDirichletInverseCLM a f‖
    ‖suzukiDirichletOutputCLM a f‖
  calc
    ‖f‖ = ‖suzukiDirichletOutputCLM a f‖ := by
      rw [suzukiDirichletOutputCLM, smul_apply,
        Submodule.coe_subtypeL, norm_smul, Complex.norm_I, one_mul]
      rfl
    _ ≤ max ‖suzukiDirichletInverseCLM a f‖
        ‖suzukiDirichletOutputCLM a f‖ := le_max_right _ _

theorem suzukiDirichletDerivative_isClosed (a : SuzukiPositiveAperture) :
    (suzukiDirichletDerivative a).IsClosed := by
  exact closedGraphTransform_isClosed (SuzukiApertureZeroMean a)
    (suzukiDirichletInverseCLM a) (suzukiDirichletOutputCLM a)
    (suzukiDirichletInverseCLM_injective a)
    (suzukiDirichletOutputCLM_antilipschitz a)

theorem suzukiDirichletOutputCLM_range (a : SuzukiPositiveAperture) :
    (suzukiDirichletOutputCLM a).range = SuzukiApertureZeroMean a := by
  apply le_antisymm
  · rintro y ⟨f, rfl⟩
    exact (SuzukiApertureZeroMean a).smul_mem Complex.I f.property
  · intro y hy
    let f : SuzukiApertureZeroMean a :=
      ⟨(-Complex.I) • y, (SuzukiApertureZeroMean a).smul_mem (-Complex.I) hy⟩
    refine ⟨f, ?_⟩
    change Complex.I • ((-Complex.I) • y) = y
    simp [smul_smul, Complex.I_mul_I]

theorem suzukiDirichletDerivative_range (a : SuzukiPositiveAperture) :
    (suzukiDirichletDerivative a).rangeSubmodule = SuzukiApertureZeroMean a := by
  rw [suzukiDirichletDerivative,
    closedGraphTransform_range (SuzukiApertureZeroMean a)
      (suzukiDirichletInverseCLM a) (suzukiDirichletOutputCLM a)
      (suzukiDirichletInverseCLM_injective a),
    suzukiDirichletOutputCLM_range]

theorem suzukiDirichletDerivative_kernel_eq_bot (a : SuzukiPositiveAperture) :
    (suzukiDirichletDerivative a).kernel = ⊥ := by
  exact closedGraphTransform_kernel_eq_bot (SuzukiApertureZeroMean a)
    (suzukiDirichletInverseCLM a) (suzukiDirichletOutputCLM a)
    (suzukiDirichletInverseCLM_injective a)
    (suzukiDirichletOutputCLM_injective a)

end RHTower
