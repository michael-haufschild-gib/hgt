import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelL1Resolvent

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem integral_subtype_apertureSet_eq_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B a : ℝ) (ha0 : 0 ≤ a) (haB : a ≤ B) (F : ℝ → E) :
    (∫ y : ClosedInterval 0 B,
      (suzukiApertureSet a B).indicator (fun y => F (y : ℝ)) y ∂volume) =
      ∫ y in (0 : ℝ)..a, F y := by
  rw [integral_indicator (measurableSet_suzukiApertureSet a B)]
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 B → ℝ)
      (volume : Measure (ClosedInterval 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have himage : ((↑) : ClosedInterval 0 B → ℝ) '' suzukiApertureSet a B = Icc 0 a := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property.1, hy⟩
    · intro hx
      exact ⟨⟨x, ⟨hx.1, hx.2.trans haB⟩⟩, hx.2, rfl⟩
  rw [← hmp.setIntegral_image_emb (MeasurableEmbedding.subtype_coe measurableSet_Icc) F
    (suzukiApertureSet a B), himage]
  rw [Measure.restrict_restrict measurableSet_Icc]
  have hinter : Icc 0 a ∩ Icc 0 B = Icc 0 a := by
    ext x
    simp only [mem_inter_iff, mem_Icc]
    constructor
    · intro h
      exact h.1
    · intro h
      exact ⟨h, ⟨h.1, h.2.trans haB⟩⟩
  rw [hinter]
  rw [intervalIntegral.integral_of_le ha0,
    ← integral_Icc_eq_integral_Ioc]

def suzukiHankelKernelContinuousRow
    (omega B : ℝ) (homega : 1 < omega) (y : ClosedInterval 0 B) :
    C(ClosedInterval 0 B, ℂ) :=
  (suzukiHankelKernelContinuous omega B homega).curry y

@[simp] theorem suzukiHankelKernelContinuousRow_apply
    (omega B : ℝ) (homega : 1 < omega)
    (y x : ClosedInterval 0 B) :
    suzukiHankelKernelContinuousRow omega B homega y x =
      suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) := by
  rw [suzukiHankelKernelContinuousRow, ContinuousMap.curry_apply]
  simp only [suzukiHankelKernelContinuous_apply, mul_comm]

def suzukiHankelKernelContinuousRowOnReal
    (omega B : ℝ) (homega : 1 < omega) (hB0 : 0 ≤ B) (y : ℝ) :
    C(ClosedInterval 0 B, ℂ) :=
  suzukiHankelKernelContinuousRow omega B homega
    (Set.projIcc 0 B hB0 y)

theorem continuous_suzukiHankelKernelContinuousRowOnReal
    (omega B : ℝ) (homega : 1 < omega) (hB0 : 0 ≤ B) :
    Continuous (suzukiHankelKernelContinuousRowOnReal omega B homega hB0) := by
  have hrows : Continuous (suzukiHankelKernelContinuousRow omega B homega) := by
    change Continuous fun y =>
      (suzukiHankelKernelContinuous omega B homega).curry y
    exact (suzukiHankelKernelContinuous omega B homega).curry.continuous
  exact hrows.comp continuous_projIcc

def suzukiSmoothedAperturePrimitive
    (omega B : ℝ) (homega : 1 < omega) (hB0 : 0 ≤ B) (a : ℝ) :
    C(ClosedInterval 0 B, ℂ) :=
  ∫ y in (0 : ℝ)..a,
    suzukiHankelKernelContinuousRowOnReal omega B homega hB0 y

theorem hasDerivAt_suzukiSmoothedAperturePrimitive
    (omega B : ℝ) (homega : 1 < omega) (hB0 : 0 ≤ B) (a : ℝ) :
    HasDerivAt (suzukiSmoothedAperturePrimitive omega B homega hB0)
      (suzukiHankelKernelContinuousRowOnReal omega B homega hB0 a) a := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (continuous_suzukiHankelKernelContinuousRowOnReal omega B homega hB0).intervalIntegrable _ _
  · exact (continuous_suzukiHankelKernelContinuousRowOnReal omega B homega hB0).aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact (continuous_suzukiHankelKernelContinuousRowOnReal omega B homega hB0).continuousAt

def suzukiSmoothedApertureProfileIntegrand
    (omega B : ℝ) (homega : 1 < omega) (hB0 : 0 ≤ B)
    (f : C(ClosedInterval 0 B, ℂ)) (y : ℝ) : C(ClosedInterval 0 B, ℂ) :=
  f (Set.projIcc 0 B hB0 y) •
    suzukiHankelKernelContinuousRowOnReal omega B homega hB0 y

theorem continuous_suzukiSmoothedApertureProfileIntegrand
    (omega B : ℝ) (homega : 1 < omega) (hB0 : 0 ≤ B)
    (f : C(ClosedInterval 0 B, ℂ)) :
    Continuous (suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f) := by
  exact (f.continuous.comp continuous_projIcc).smul
    (continuous_suzukiHankelKernelContinuousRowOnReal omega B homega hB0)

def suzukiSmoothedApertureProfilePrimitive
    (omega B : ℝ) (homega : 1 < omega) (hB0 : 0 ≤ B)
    (f : C(ClosedInterval 0 B, ℂ)) (a : ℝ) : C(ClosedInterval 0 B, ℂ) :=
  ∫ y in (0 : ℝ)..a,
    suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f y

theorem hasDerivAt_suzukiSmoothedApertureProfilePrimitive
    (omega B : ℝ) (homega : 1 < omega) (hB0 : 0 ≤ B)
    (f : C(ClosedInterval 0 B, ℂ)) (a : ℝ) :
    HasDerivAt (suzukiSmoothedApertureProfilePrimitive omega B homega hB0 f)
      (suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f a) a := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (continuous_suzukiSmoothedApertureProfileIntegrand
      omega B homega hB0 f).intervalIntegrable _ _
  · exact (continuous_suzukiSmoothedApertureProfileIntegrand
      omega B homega hB0 f).aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact (continuous_suzukiSmoothedApertureProfileIntegrand
      omega B homega hB0 f).continuousAt

theorem suzukiCompressedHankelL1ToL2_cutoff_continuousMap
    (omega B : ℝ) (homega : 1 < omega) (hB0 : 0 ≤ B)
    (a : ℝ) (ha0 : 0 ≤ a) (haB : a ≤ B)
    (f : C(ClosedInterval 0 B, ℂ)) :
    suzukiCompressedHankelL1ToL2 omega B homega
        (suzukiApertureCutoffL1 a B
          (ContinuousMap.toLp 1 volume ℂ f)) =
      ContinuousMap.toLp 2 volume ℂ
        (suzukiSmoothedApertureProfilePrimitive omega B homega hB0 f a) := by
  have hcutAe := suzukiApertureCutoffL1_ae a B
    (ContinuousMap.toLp 1 volume ℂ f)
  have hfAe := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (1 : ENNReal))
    (μ := (volume : Measure (ClosedInterval 0 B))) f
  apply Lp.ext
  filter_upwards [suzukiCompressedHankelL1ToL2_coeFn omega B homega
      (suzukiApertureCutoffL1 a B (ContinuousMap.toLp 1 volume ℂ f)),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (ClosedInterval 0 B)))
      (suzukiSmoothedApertureProfilePrimitive omega B homega hB0 f a)] with x hH hprim
  rw [hH, hprim]
  let F : ℝ → ℂ := fun y =>
    suzukiSourceHFinite omega ((x : ℝ) * y) *
      f (Set.projIcc 0 B hB0 y)
  calc
    (∫ y : ClosedInterval 0 B,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
          suzukiApertureCutoffL1 a B (ContinuousMap.toLp 1 volume ℂ f) y
          ∂volume) =
        ∫ y : ClosedInterval 0 B,
          (suzukiApertureSet a B).indicator (fun y => F (y : ℝ)) y ∂volume := by
      apply integral_congr_ae
      filter_upwards [hcutAe, hfAe] with y hcut hf
      rw [hcut]
      by_cases hy : y ∈ suzukiApertureSet a B
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        rw [hf]
        change suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y =
          suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) *
            f (Set.projIcc 0 B hB0 (y : ℝ))
        rw [Set.projIcc_of_mem hB0 y.property]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
    _ = ∫ y in (0 : ℝ)..a, F y :=
      integral_subtype_apertureSet_eq_intervalIntegral B a ha0 haB F
    _ = suzukiSmoothedApertureProfilePrimitive omega B homega hB0 f a x := by
      have hint : IntervalIntegrable
          (suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f)
          volume 0 a :=
        (continuous_suzukiSmoothedApertureProfileIntegrand
          omega B homega hB0 f).intervalIntegrable _ _
      have hintSet : IntegrableOn
          (suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f) (Ioc 0 a) := by
        have hu := (intervalIntegrable_iff.mp hint)
        simpa only [Set.uIoc_of_le ha0] using hu
      calc
        (∫ y in (0 : ℝ)..a, F y) = ∫ y in Ioc 0 a, F y :=
          intervalIntegral.integral_of_le ha0
        _ = ∫ y in Ioc 0 a,
            (ContinuousMap.evalCLM ℂ x)
              (suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f y) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
          change suzukiSourceHFinite omega ((x : ℝ) * y) *
              f (Set.projIcc 0 B hB0 y) =
            (ContinuousMap.evalCLM ℂ x)
              (suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f y)
          rw [suzukiSmoothedApertureProfileIntegrand,
            ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
            suzukiHankelKernelContinuousRowOnReal,
            suzukiHankelKernelContinuousRow_apply]
          simp only [smul_eq_mul]
          have hyB : y ∈ Icc 0 B := ⟨hy.1.le, hy.2.trans haB⟩
          rw [Set.projIcc_of_mem hB0 hyB]
          exact mul_comm _ _
        _ = (ContinuousMap.evalCLM ℂ x)
            (∫ y in Ioc 0 a,
              suzukiSmoothedApertureProfileIntegrand omega B homega hB0 f y) :=
          (ContinuousMap.evalCLM ℂ x).integral_comp_comm hintSet
        _ = suzukiSmoothedApertureProfilePrimitive omega B homega hB0 f a x := by
          rw [ContinuousMap.evalCLM_apply,
            suzukiSmoothedApertureProfilePrimitive,
            intervalIntegral.integral_of_le ha0]

/-- Exact endpoint rank-one law: after Suzuki's Hankel smoothing, differentiating the sharp
aperture of a continuous profile produces its endpoint value times the kernel row.  The unsmoothed
cutoff has no `L¹` derivative; this theorem is the correct Banach-space statement. -/
theorem hasDerivAt_suzukiCompressedHankelL1ToL2_aperture_continuousMap
    (omega B : ℝ) (homega : 1 < omega)
    (a : ℝ) (ha0 : 0 < a) (haB : a < B)
    (f : C(ClosedInterval 0 B, ℂ)) :
    HasDerivAt (fun b =>
      suzukiCompressedHankelL1ToL2 omega B homega
        (suzukiApertureCutoffL1 b B
          (ContinuousMap.toLp 1 volume ℂ f)))
      (ContinuousMap.toLp 2 volume ℂ
        (suzukiSmoothedApertureProfileIntegrand omega B homega
          (le_of_lt (ha0.trans haB)) f a)) a := by
  have hB0 : 0 ≤ B := le_of_lt (ha0.trans haB)
  have hprimitive :=
    hasDerivAt_suzukiSmoothedApertureProfilePrimitive
      omega B homega hB0 f a
  have hmapped :=
    ((ContinuousMap.toLp 2 volume ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      a hprimitive
  have heq : (fun b =>
      suzukiCompressedHankelL1ToL2 omega B homega
        (suzukiApertureCutoffL1 b B
          (ContinuousMap.toLp 1 volume ℂ f))) =ᶠ[𝓝 a]
      fun b => ContinuousMap.toLp 2 volume ℂ
        (suzukiSmoothedApertureProfilePrimitive omega B homega hB0 f b) := by
    filter_upwards [Icc_mem_nhds ha0 haB] with b hb
    exact suzukiCompressedHankelL1ToL2_cutoff_continuousMap
      omega B homega hB0 b hb.1 hb.2 f
  exact hmapped.congr_of_eventuallyEq heq

end RHTower
