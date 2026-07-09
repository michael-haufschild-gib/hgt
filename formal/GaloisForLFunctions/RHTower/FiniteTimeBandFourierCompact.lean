/-
BRIDGE (classical harmonic-analysis infrastructure).

Compactness of finite time-band Fourier integral operators, with no analytic compactness
hypothesis.  Mathlib supplies `L²`, Holder pairings, simple-function density, and compact
operators, but not Hilbert--Schmidt integral operators.  The first half of this file builds the
needed theorem: an `L²` field of continuous functionals induces a compact operator.  Simple
functional fields give finite-rank operators, and arbitrary fields follow by `L²` density and
norm-closedness of the compact operators.

The second half constructs the actual Fourier kernel `exp (-2 * pi * i * x * y)` on a finite
rectangle, records its pointwise integral formula, and specializes compactness to both one interval
and the two-sided Sonin shell.
-/
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.CompactOpen
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge

noncomputable section

open MeasureTheory
open FourierTransform
open scoped ENNReal BoundedContinuousFunction SchwartzMap

namespace RHTower

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (μ : Measure α) [IsFiniteMeasure μ]

/-- Pointwise evaluation, bilinear in a continuous functional and a vector. -/
def evalBilinear : (E →L[ℂ] ℂ) →L[ℂ] E →L[ℂ] ℂ :=
  ContinuousLinearMap.flip (ContinuousLinearMap.apply ℂ ℂ)

/-- The continuous map taking an `L²` field of functionals to its associated kernel operator. -/
def kernelOperatorMap :
    Lp (E →L[ℂ] ℂ) 2 μ →L[ℂ] E →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.flip
      (ContinuousLinearMap.compL ℂ E (Lp E ∞ μ) (Lp ℂ 2 μ))
      (Lp.constL ∞ μ ℂ)) ∘L
    ((evalBilinear (E := E)).holderL μ 2 ∞ 2)

/-- The operator induced by a square-integrable field of continuous functionals. -/
def kernelOperator (K : Lp (E →L[ℂ] ℂ) 2 μ) : E →L[ℂ] Lp ℂ 2 μ :=
  kernelOperatorMap (E := E) μ K

@[simp] theorem kernelOperatorMap_apply
    (K : Lp (E →L[ℂ] ℂ) 2 μ) (f : E) :
    kernelOperatorMap (E := E) μ K f =
      (evalBilinear (E := E)).holder 2 K (Lp.const ∞ μ f) := rfl

/-- An indicator-constant functional field induces a rank-one operator. -/
theorem kernelOperator_indicatorConst
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s < ∞)
    (ell : E →L[ℂ] ℂ) :
    kernelOperator (E := E) μ (indicatorConstLp 2 hs hμs.ne ell) =
      (ContinuousLinearMap.toSpanSingleton ℂ
        (indicatorConstLp 2 hs hμs.ne (1 : ℂ))) ∘L ell := by
  ext f
  filter_upwards [
    (evalBilinear (E := E)).coeFn_holder (r := (2 : ENNReal))
      (indicatorConstLp 2 hs hμs.ne ell) (Lp.const ∞ μ f),
    indicatorConstLp_coeFn (p := 2) (μ := μ) (c := ell),
    Lp.coeFn_const (p := ∞) μ f,
    indicatorConstLp_coeFn (s := s) (p := 2) (μ := μ) (c := (1 : ℂ)),
    Lp.coeFn_smul (ell f) (indicatorConstLp 2 hs hμs.ne (1 : ℂ))
  ] with x hholder hK hconst hone hsmul
  rw [kernelOperator, kernelOperatorMap_apply]
  rw [hholder, hK, hconst, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, hsmul, Pi.smul_apply, hone]
  by_cases hx : x ∈ s <;> simp [hx, evalBilinear]

/-- Indicator-constant functional fields induce compact operators. -/
theorem isCompactOperator_kernelOperator_indicatorConst
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s < ∞)
    (ell : E →L[ℂ] ℂ) :
    IsCompactOperator
      (kernelOperator (E := E) μ (indicatorConstLp 2 hs hμs.ne ell)) := by
  rw [kernelOperator_indicatorConst (E := E) μ s hs hμs ell]
  have hell : IsCompactOperator ell := isCompactOperator_of_locallyCompactSpace_dom ell
  exact hell.clm_comp
    (ContinuousLinearMap.toSpanSingleton ℂ
      (indicatorConstLp 2 hs hμs.ne (1 : ℂ)))

/-- The construction is additive in the functional field. -/
theorem kernelOperator_add
    (K L : Lp (E →L[ℂ] ℂ) 2 μ) :
    kernelOperator (E := E) μ (K + L) =
      kernelOperator (E := E) μ K + kernelOperator (E := E) μ L := by
  exact map_add (kernelOperatorMap (E := E) μ) K L

/-- **Hilbert--Schmidt kernel theorem in field form.** Every square-integrable field of continuous
functionals induces a compact operator into scalar `L²`. -/
theorem isCompactOperator_kernelOperator (K : Lp (E →L[ℂ] ℂ) 2 μ) :
    IsCompactOperator (kernelOperator (E := E) μ K) := by
  apply Lp.induction (p := (2 : ENNReal)) (by norm_num)
    (motive := fun L => IsCompactOperator (kernelOperator (E := E) μ L))
  · intro ell s hs hμs
    simpa only [Lp.simpleFunc.coe_indicatorConst] using
      isCompactOperator_kernelOperator_indicatorConst (E := E) μ s hs hμs ell
  · intro f g hf hg hdisj ihf ihg
    rw [kernelOperator_add]
    exact ihf.add ihg
  · exact isClosed_setOf_isCompactOperator.preimage (kernelOperatorMap (E := E) μ).continuous

open Set
open scoped Real

attribute [local instance] Measure.Subtype.measureSpace

/-- A closed real interval, used with its subtype Lebesgue measure. -/
abbrev ClosedInterval (a b : ℝ) := Set.Icc a b

noncomputable instance intervalVolumeFinite (a b : ℝ) :
    IsFiniteMeasure (volume : Measure (ClosedInterval a b)) := by
  constructor
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- The Fourier phase on a closed time-frequency rectangle. -/
def fourierPhaseContinuous (a b c d : ℝ) :
    C(ClosedInterval a b × ClosedInterval c d, ℂ) where
  toFun z := Complex.exp ((-(2 * Real.pi * (z.1 : ℝ) * (z.2 : ℝ)) : ℝ) * Complex.I)
  continuous_toFun := by fun_prop

/-- The Fourier phase, curried as a continuous family of continuous frequency functions. -/
def fourierPhaseCurried (a b c d : ℝ) :
    C(ClosedInterval a b, C(ClosedInterval c d, ℂ)) :=
  (fourierPhaseContinuous a b c d).curry

/-- The Fourier phase, curried as a continuous family of frequency `L²` vectors. -/
def fourierSectionContinuous (a b c d : ℝ) :
    C(ClosedInterval a b, Lp ℂ 2 (volume : Measure (ClosedInterval c d))) where
  toFun x := ContinuousMap.toLp 2 volume ℂ (fourierPhaseCurried a b c d x)
  continuous_toFun :=
    (ContinuousMap.toLp 2 volume ℂ).continuous.comp
      (fourierPhaseCurried a b c d).continuous

/-- Complex multiplication as a continuous bilinear map. -/
def complexMulBilinear : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.lsmul ℂ ℂ

/-- The Fourier phase section as a continuous functional on frequency `L²`. -/
def fourierFunctionalContinuous (a b c d : ℝ) :
    C(ClosedInterval a b,
      Lp ℂ 2 (volume : Measure (ClosedInterval c d)) →L[ℂ] ℂ) where
  toFun x := (complexMulBilinear.lpPairing volume 2 2)
    (fourierSectionContinuous a b c d x)
  continuous_toFun :=
    (complexMulBilinear.lpPairing volume 2 2).continuous.comp
      (fourierSectionContinuous a b c d).continuous

/-- The square-integrable field of Fourier functionals on a finite rectangle. -/
def fourierFunctionalField (a b c d : ℝ) :
    Lp (Lp ℂ 2 (volume : Measure (ClosedInterval c d)) →L[ℂ] ℂ) 2
      (volume : Measure (ClosedInterval a b)) :=
  ContinuousMap.toLp 2 volume ℂ (fourierFunctionalContinuous a b c d)

/-- The finite time-band Fourier integral operator between two interval `L²` spaces. -/
def finiteTimeBandFourier (a b c d : ℝ) :
    Lp ℂ 2 (volume : Measure (ClosedInterval c d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (ClosedInterval a b)) :=
  kernelOperator (volume : Measure (ClosedInterval a b))
    (fourierFunctionalField a b c d)

/-- The preceding definition is the integral operator with kernel `exp (-2*pi*i*x*y)`. -/
theorem finiteTimeBandFourier_coeFn (a b c d : ℝ)
    (f : Lp ℂ 2 (volume : Measure (ClosedInterval c d))) :
    (finiteTimeBandFourier a b c d f : ClosedInterval a b → ℂ) =ᵐ[volume]
      fun x => ∫ y : ClosedInterval c d,
        fourierPhaseContinuous a b c d (x, y) * f y ∂volume := by
  filter_upwards [
    (evalBilinear (E := Lp ℂ 2 (volume : Measure (ClosedInterval c d)))).coeFn_holder
      (r := (2 : ENNReal)) (fourierFunctionalField a b c d)
      (Lp.const ∞ (volume : Measure (ClosedInterval a b)) f),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (ClosedInterval a b)))
      (fourierFunctionalContinuous a b c d),
    Lp.coeFn_const (p := ∞) (volume : Measure (ClosedInterval a b)) f
  ] with x hholder hfield hconst
  rw [finiteTimeBandFourier, kernelOperator, kernelOperatorMap_apply,
    hholder, fourierFunctionalField, hfield, hconst]
  change (complexMulBilinear.lpPairing volume 2 2
    (fourierSectionContinuous a b c d x)) f = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
    (μ := (volume : Measure (ClosedInterval c d)))
    (fourierPhaseCurried a b c d x)] with y hy
  change complexMulBilinear
    ((ContinuousMap.toLp 2 volume ℂ (fourierPhaseCurried a b c d x)) y)
    (f y) = _
  rw [hy]
  simp [evalBilinear, complexMulBilinear, fourierSectionContinuous,
    fourierPhaseCurried]

/-- **Finite-rectangle time-band compactness.** The Fourier integral operator between any two
closed finite intervals is compact. -/
theorem isCompactOperator_finiteTimeBandFourier (a b c d : ℝ) :
    IsCompactOperator (finiteTimeBandFourier a b c d) :=
  isCompactOperator_kernelOperator (volume : Measure (ClosedInterval a b))
    (fourierFunctionalField a b c d)

abbrev IntervalL2 (a b : ℝ) :=
  Lp ℂ 2 (volume : Measure (ClosedInterval a b))

/-- The `L²` space on the two components of the finite shell `λ ≤ |y| ≤ ρλ`. -/
abbrev FourierShellL2 (ρ lam : ℝ) :=
  IntervalL2 (-ρ * lam) (-lam) × IntervalL2 lam (ρ * lam)

/-- The two-component Fourier block from `λ ≤ |y| ≤ ρλ` into `[-λ, λ]`. -/
def finiteShellTimeBandFourier (ρ lam : ℝ) :
    FourierShellL2 ρ lam →L[ℂ] IntervalL2 (-lam) lam :=
  (finiteTimeBandFourier (-lam) lam (-ρ * lam) (-lam)) ∘L
      ContinuousLinearMap.fst ℂ (IntervalL2 (-ρ * lam) (-lam))
        (IntervalL2 lam (ρ * lam)) +
    (finiteTimeBandFourier (-lam) lam lam (ρ * lam)) ∘L
      ContinuousLinearMap.snd ℂ (IntervalL2 (-ρ * lam) (-lam))
        (IntervalL2 lam (ρ * lam))

/-- **Sonin-shell time-band compactness.** The Fourier block from a finite two-sided shell into the
central time interval is compact. -/
theorem isCompactOperator_finiteShellTimeBandFourier (ρ lam : ℝ) :
    IsCompactOperator (finiteShellTimeBandFourier ρ lam) := by
  apply IsCompactOperator.add
  · exact (isCompactOperator_finiteTimeBandFourier
      (-lam) lam (-ρ * lam) (-lam)).comp_clm _
  · exact (isCompactOperator_finiteTimeBandFourier
      (-lam) lam lam (ρ * lam)).comp_clm _

/-! ### Restriction and extension by zero on full `L²` -/

section ExtendByZero

variable {X F 𝕜 : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup F] [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F]
variable (ν : Measure X) (q : ENNReal) [Fact (1 ≤ q)]

/-- Extend an `Lᵖ` class for a restricted measure by zero outside the restricting set. -/
def lpExtendByZero (s : Set X) (hs : MeasurableSet s)
    (f : Lp F q (ν.restrict s)) : Lp F q ν :=
  MemLp.toLp (s.indicator f)
    ((memLp_indicator_iff_restrict hs).2 (Lp.memLp f))

theorem lpExtendByZero_add (s : Set X) (hs : MeasurableSet s)
    (f g : Lp F q (ν.restrict s)) :
    lpExtendByZero ν q s hs (f + g) =
      lpExtendByZero ν q s hs f + lpExtendByZero ν q s hs g := by
  let hf : MemLp (s.indicator (f : X → F)) q ν :=
    (memLp_indicator_iff_restrict hs).2 (Lp.memLp f)
  let hg : MemLp (s.indicator (g : X → F)) q ν :=
    (memLp_indicator_iff_restrict hs).2 (Lp.memLp g)
  rw [lpExtendByZero, lpExtendByZero, lpExtendByZero, ← hf.toLp_add hg]
  apply MemLp.toLp_congr
  filter_upwards [ae_restrict_iff' hs |>.mp (Lp.coeFn_add f g)] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs, Pi.add_apply]
    exact hx hxs
  · simp [hxs]

theorem lpExtendByZero_smul (s : Set X) (hs : MeasurableSet s)
    (c : 𝕜) (f : Lp F q (ν.restrict s)) :
    lpExtendByZero ν q s hs (c • f) = c • lpExtendByZero ν q s hs f := by
  let hf : MemLp (s.indicator (f : X → F)) q ν :=
    (memLp_indicator_iff_restrict hs).2 (Lp.memLp f)
  rw [lpExtendByZero, lpExtendByZero, ← hf.toLp_const_smul c]
  apply MemLp.toLp_congr
  filter_upwards [ae_restrict_iff' hs |>.mp (Lp.coeFn_smul c f)] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs, Pi.smul_apply]
    exact hx hxs
  · simp [hxs]

theorem norm_lpExtendByZero (s : Set X) (hs : MeasurableSet s)
    (f : Lp F q (ν.restrict s)) :
    ‖lpExtendByZero ν q s hs f‖ = ‖f‖ := by
  rw [lpExtendByZero, Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (MemLp.coeFn_toLp _),
    eLpNorm_indicator_eq_eLpNorm_restrict hs]

/-- Extension by zero as a norm-one continuous linear map. -/
def lpExtendByZeroCLM (s : Set X) (hs : MeasurableSet s) :
    Lp F q (ν.restrict s) →L[𝕜] Lp F q ν :=
  LinearMap.mkContinuous
    { toFun := lpExtendByZero ν q s hs
      map_add' := lpExtendByZero_add ν q s hs
      map_smul' := lpExtendByZero_smul ν q s hs }
    1 (fun f => by
      change ‖lpExtendByZero ν q s hs f‖ ≤ 1 * ‖f‖
      rw [norm_lpExtendByZero ν q s hs f, one_mul])

theorem lpExtendByZeroCLM_coeFn (s : Set X) (hs : MeasurableSet s)
    (f : Lp F q (ν.restrict s)) :
    lpExtendByZeroCLM (F := F) (𝕜 := 𝕜) ν q s hs f =ᵐ[ν]
      s.indicator f := by
  change lpExtendByZero ν q s hs f =ᵐ[ν] s.indicator f
  exact AEEqFun.coeFn_mk _ _

/-- Multiplication by the indicator of a measurable set on a full `Lᵖ` space. -/
def lpSetCutoffCLM (s : Set X) (hs : MeasurableSet s) :
    Lp F q ν →L[𝕜] Lp F q ν :=
  lpExtendByZeroCLM (F := F) (𝕜 := 𝕜) ν q s hs ∘L
    LpToLpRestrictCLM X F 𝕜 ν q s

theorem lpSetCutoffCLM_coeFn (s : Set X) (hs : MeasurableSet s)
    (f : Lp F q ν) :
    lpSetCutoffCLM (F := F) (𝕜 := 𝕜) ν q s hs f =ᵐ[ν]
      s.indicator f := by
  filter_upwards [
    lpExtendByZeroCLM_coeFn (F := F) (𝕜 := 𝕜) ν q s hs
      (LpToLpRestrictCLM X F 𝕜 ν q s f),
    ae_restrict_iff' hs |>.mp (LpToLpRestrictCLM_coeFn (μ := ν) (p := q) 𝕜 s f)
  ] with x hext hres
  rw [lpSetCutoffCLM, ContinuousLinearMap.coe_comp', Function.comp_apply, hext]
  by_cases hx : x ∈ s
  · simp [hx, hres hx]
  · simp [hx]

end ExtendByZero

/-! ### Compact Fourier blocks on full `L²(ℝ)` -/

/-- The ambient complex `L²(ℝ)` used by the Sonin model. -/
abbrev RealL2 := Lp ℂ 2 (volume : Measure ℝ)

/-- Sharp multiplication by the indicator of a closed interval on full `L²(ℝ)`. -/
def intervalCutoff (a b : ℝ) : RealL2 →L[ℂ] RealL2 :=
  lpSetCutoffCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2 (Icc a b) measurableSet_Icc

/-- Restrict full `L²(ℝ)` to an interval and pull it back to the interval subtype. -/
def restrictToClosedInterval (c d : ℝ) : RealL2 →L[ℂ] IntervalL2 c d :=
  (Lp.compMeasurePreservingₗᵢ ℂ ((↑) : ClosedInterval c d → ℝ)
      (measurePreserving_subtype_coe measurableSet_Icc)).toContinuousLinearMap ∘L
    LpToLpRestrictCLM ℝ ℂ ℂ (volume : Measure ℝ) 2 (Icc c d)

theorem restrictToClosedInterval_coeFn (c d : ℝ) (f : RealL2) :
    restrictToClosedInterval c d f =ᵐ[(volume : Measure (ClosedInterval c d))]
      fun y => f (y : ℝ) := by
  let g : Lp ℂ 2 ((volume : Measure ℝ).restrict (Icc c d)) :=
    LpToLpRestrictCLM ℝ ℂ ℂ (volume : Measure ℝ) 2 (Icc c d) f
  let hmp : MeasurePreserving ((↑) : ClosedInterval c d → ℝ)
      (volume : Measure (ClosedInterval c d))
      ((volume : Measure ℝ).restrict (Icc c d)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  filter_upwards [
    Lp.coeFn_compMeasurePreserving g hmp,
    hmp.quasiMeasurePreserving.ae
      (LpToLpRestrictCLM_coeFn (μ := (volume : Measure ℝ)) (p := (2 : ENNReal))
        ℂ (Icc c d) f)
  ] with y hcomp hres
  rw [restrictToClosedInterval, ContinuousLinearMap.coe_comp', Function.comp_apply]
  change (Lp.compMeasurePreserving ((↑) : ClosedInterval c d → ℝ) hmp g) y = f (y : ℝ)
  rw [hcomp]
  exact hres

/-- On a finite output interval, the Fourier integral over a finite input interval is a continuous
family of functionals on the ambient full `L²(ℝ)`. -/
def fullFourierFunctionalContinuous (a b c d : ℝ) :
    C(ClosedInterval a b, RealL2 →L[ℂ] ℂ) where
  toFun x := fourierFunctionalContinuous a b c d x ∘L restrictToClosedInterval c d
  continuous_toFun :=
    (fourierFunctionalContinuous a b c d).continuous.clm_comp_const
      (restrictToClosedInterval c d)

/-- Evaluation of the full-input functional is the Fourier integral over the source interval. -/
theorem fullFourierFunctionalContinuous_apply (a b c d : ℝ)
    (x : ClosedInterval a b) (f : RealL2) :
    fullFourierFunctionalContinuous a b c d x f =
      ∫ y : ℝ in Icc c d,
        Complex.exp ((-(2 * Real.pi * (x : ℝ) * y) : ℝ) * Complex.I) * f y := by
  change (complexMulBilinear.lpPairing volume 2 2
    (fourierSectionContinuous a b c d x)) (restrictToClosedInterval c d f) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  let hmp : MeasurePreserving ((↑) : ClosedInterval c d → ℝ)
      (volume : Measure (ClosedInterval c d))
      ((volume : Measure ℝ).restrict (Icc c d)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  calc
    (∫ y : ClosedInterval c d,
        complexMulBilinear (fourierSectionContinuous a b c d x y)
          (restrictToClosedInterval c d f y) ∂volume) =
        ∫ y : ClosedInterval c d,
          Complex.exp ((-(2 * Real.pi * (x : ℝ) * (y : ℝ)) : ℝ) * Complex.I) *
            f (y : ℝ) ∂volume := by
      apply integral_congr_ae
      filter_upwards [
        ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
          (μ := (volume : Measure (ClosedInterval c d)))
          (fourierPhaseCurried a b c d x),
        restrictToClosedInterval_coeFn c d f
      ] with y hphase hf
      change complexMulBilinear
        ((ContinuousMap.toLp 2 volume ℂ (fourierPhaseCurried a b c d x)) y)
        (restrictToClosedInterval c d f y) = _
      rw [hphase, hf]
      simp [complexMulBilinear, fourierPhaseCurried, fourierPhaseContinuous]
    _ = ∫ y : ℝ,
          Complex.exp ((-(2 * Real.pi * (x : ℝ) * y) : ℝ) * Complex.I) * f y
            ∂((volume : Measure ℝ).restrict (Icc c d)) := by
      simpa only [Function.comp_apply] using
        (hmp.integral_comp (MeasurableEmbedding.subtype_coe measurableSet_Icc)
          (fun y : ℝ =>
            Complex.exp ((-(2 * Real.pi * (x : ℝ) * y) : ℝ) * Complex.I) * f y))

/-- Extend the preceding functional family continuously and boundedly from `[a,b]` to `ℝ` by
projection onto the interval. -/
def fullFourierFunctionalBCF (a b c d : ℝ) (hab : a ≤ b) :
    ℝ →ᵇ (RealL2 →L[ℂ] ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => fullFourierFunctionalContinuous a b c d (projIcc a b hab x))
    ((fullFourierFunctionalContinuous a b c d).continuous.comp continuous_projIcc)
    ‖fullFourierFunctionalContinuous a b c d‖
    (fun x => (fullFourierFunctionalContinuous a b c d).norm_coe_le_norm _)

/-- The full-input Fourier functional field, square-integrable for the output measure restricted
to `[a,b]`. -/
def fullFourierFunctionalField (a b c d : ℝ) (hab : a ≤ b) :
    Lp (RealL2 →L[ℂ] ℂ) 2 ((volume : Measure ℝ).restrict (Icc a b)) :=
  BoundedContinuousFunction.toLp 2 ((volume : Measure ℝ).restrict (Icc a b)) ℂ
    (fullFourierFunctionalBCF a b c d hab)

/-- The Fourier integral over `[c,d]`, observed on `[a,b]`, as an operator from full `L²(ℝ)` to
the restricted-measure output `L²`. -/
def fullToRestrictedTimeBandFourier (a b c d : ℝ) (hab : a ≤ b) :
    RealL2 →L[ℂ] Lp ℂ 2 ((volume : Measure ℝ).restrict (Icc a b)) :=
  kernelOperator ((volume : Measure ℝ).restrict (Icc a b))
    (fullFourierFunctionalField a b c d hab)

/-- The same finite-rectangle Fourier integral, extended by zero to full output `L²(ℝ)`. -/
def fullTimeBandFourier (a b c d : ℝ) (hab : a ≤ b) : RealL2 →L[ℂ] RealL2 :=
  lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
      (Icc a b) measurableSet_Icc ∘L
    fullToRestrictedTimeBandFourier a b c d hab

/-- The full-space finite time-band Fourier integral is compact. -/
theorem isCompactOperator_fullTimeBandFourier
    (a b c d : ℝ) (hab : a ≤ b) :
    IsCompactOperator (fullTimeBandFourier a b c d hab) := by
  simpa only [fullTimeBandFourier, ContinuousLinearMap.coe_comp'] using
    (isCompactOperator_kernelOperator ((volume : Measure ℝ).restrict (Icc a b))
      (fullFourierFunctionalField a b c d hab)).clm_comp
        (lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
          (Icc a b) measurableSet_Icc)

end RHTower
