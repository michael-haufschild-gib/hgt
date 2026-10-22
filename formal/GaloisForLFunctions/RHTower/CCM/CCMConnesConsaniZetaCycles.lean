import GaloisForLFunctions.RHTower.Deninger.DeningerFloquetParseval
import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonZeroDivisor
import GaloisForLFunctions.RHTower.MeyerPoissonTest
import GaloisForLFunctions.RHTower.Deninger.DeningerRadialNuclear
import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge
import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonSource
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelKernelInversion
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPoissonMellinFactorization
import GaloisForLFunctions.RHTower.Deninger.DeningerFourierBridge
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerDilationFlow
import GaloisForLFunctions.HTGeometry.FourierCircleTranslation
import GaloisForLFunctions.HTGeometry.CompactAbelianTranslation
import Mathlib.Analysis.Convex.Integral
import Mathlib.Topology.CompactOpen

open Complex Filter Topology MeasureTheory Set
open scoped FourierTransform SchwartzMap
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem mellin_deningerPoissonValue_eq_zeta_mul_of_re_pos
    {f : 𝓢(ℝ, ℂ)} (hf : f ∈ DeningerMeyerCap)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    mellin (deningerPoissonValue f) s =
      riemannZeta s * mellin (f : ℝ → ℂ) s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re} \ {1}
  let F : ℂ → ℂ := fun z => mellin (deningerPoissonValue f) z
  let G : ℂ → ℂ := fun z => riemannZeta z * mellin (f : ℝ → ℂ) z
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hFan : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact (differentiableAt_mellin_deningerPoissonValue hf z).differentiableWithinAt
  have hGan : AnalyticOnNhd ℂ G U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact ((differentiableAt_riemannZeta hz.2).mul
      (differentiableAt_mellin_schwartz f hz.1)).differentiableWithinAt
  have h2mem : (2 : ℂ) ∈ U := by
    exact ⟨by norm_num, by norm_num⟩
  have hevent : F =ᶠ[𝓝 (2 : ℂ)] G := by
    have hhalf : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hhalf] with z hz
    exact mellin_deningerPoissonValue f hz
  have hEqOn : Set.EqOn F G U :=
    hFan.eqOn_of_preconnected_of_eventuallyEq hGan
      isPreconnected_halfplane_punctured h2mem hevent
  exact hEqOn ⟨hs0, hs1⟩

theorem fourier_halfDensityPoisson_eq_mellin
    (f : DeningerMeyerCap) (xi : ℝ) :
    𝓕 ((((deningerHalfDensityLift (deningerPoissonSource f) :
        DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) xi =
      mellin (deningerPoissonValue (f : 𝓢(ℝ, ℂ)))
        ((1 / 2 : ℂ) - ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I) := by
  rw [mellin_eq_integral_exp_mul_log, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  rw [deningerHalfDensityLift_apply, deningerPoissonSource_apply,
    deningerPoissonLog_eq, smul_eq_mul, Complex.ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring_nf

/-- Connes--Consani Lemma `scalingact` (i): Meyer's source is invariant under
multiplicative scaling, and the half-density Poisson boundary intertwines it
with translation in logarithmic radius. -/
theorem deningerHalfDensityPoisson_capFlow
    (c : ℝ) (f : DeningerMeyerCap) :
    deningerHalfDensityLift
        (deningerPoissonSource (deningerMeyerCapFlow c f)) =
      ((Real.exp (c / 2) : ℝ) : ℂ) •
        deningerEscapeFamily 0 c
          (deningerHalfDensityLift (deningerPoissonSource f)) := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerHalfDensityLift_apply, Submodule.coe_smul]
  change
    ((Real.exp (t / 2) : ℝ) : ℂ) *
        (((deningerPoissonSource (deningerMeyerCapFlow c f) :
          DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t) = _
  rw [deningerPoissonSource_apply, deningerPoissonLog_eq]
  change _ = ((Real.exp (c / 2) : ℝ) : ℂ) *
    (((deningerEscapeFamily 0 c
      (deningerHalfDensityLift (deningerPoissonSource f)) :
        DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) t)
  rw [deningerEscapeFamily_apply, deningerHalfDensityLift_apply,
    deningerPoissonSource_apply, deningerPoissonLog_eq]
  norm_num
  have hscale :
      deningerPoissonValue
          ((deningerMeyerCapFlow c f : DeningerMeyerCap) : 𝓢(ℝ, ℂ))
          (Real.exp t) =
        deningerPoissonValue (f : 𝓢(ℝ, ℂ)) (Real.exp (t - c)) := by
    rw [deningerPoissonValue, deningerPoissonValue]
    apply tsum_congr
    intro n
    rw [deningerMeyerCapFlow_apply]
    congr 1
    rw [Real.exp_sub, Real.exp_neg]
    field_simp [Real.exp_ne_zero c]
  rw [hscale, ← mul_assoc, ← Complex.exp_add]
  congr 1
  ring

def meyerPoissonTestPolynomial : Polynomial ℝ :=
  Polynomial.X ^ (2 : ℕ) *
    (Polynomial.X ^ (2 : ℕ) - Polynomial.C (3 / (2 * Real.pi)))

def meyerPoissonTestSchwartz : 𝓢(ℝ, ℂ) :=
  polyGaussSchwartz meyerPoissonTestPolynomial

theorem meyerPoissonTestSchwartz_apply (x : ℝ) :
    meyerPoissonTestSchwartz x = ((meyerPoissonTest x : ℝ) : ℂ) := by
  rw [meyerPoissonTestSchwartz, polyGaussSchwartz_apply,
    meyerPoissonTestPolynomial, meyerPoissonTest]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_C, gaussReal]
  push_cast
  ring_nf

theorem meyerPoissonTestSchwartz_mem :
    meyerPoissonTestSchwartz ∈ DeningerMeyerCap := by
  rw [deningerMeyerCap_mem_iff]
  refine ⟨fun x => ?_, ?_, ?_⟩
  · rw [meyerPoissonTestSchwartz_apply, meyerPoissonTestSchwartz_apply]
    exact_mod_cast meyerPoissonTest_even x
  · rw [meyerPoissonTestSchwartz_apply]
    exact_mod_cast meyerPoissonTest_zero
  · have hcoe :
        (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) meyerPoissonTestSchwartz) =
          fourierSCLM meyerPoissonTestSchwartz := by
      rw [FourierTransform.fourierCLE_apply, fourierSCLM_eq]
    rw [hcoe]
    change 𝓕 (meyerPoissonTestSchwartz : ℝ → ℂ) 0 = 0
    rw [Real.fourier_real_eq_integral_exp_smul]
    have hfun : (meyerPoissonTestSchwartz : ℝ → ℂ) =
        fun x : ℝ => ((meyerPoissonTest x : ℝ) : ℂ) :=
      funext meyerPoissonTestSchwartz_apply
    rw [hfun]
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    calc
      (∫ v : ℝ, ((meyerPoissonTest v : ℝ) : ℂ)) =
          (((∫ v : ℝ, meyerPoissonTest v) : ℝ) : ℂ) := integral_ofReal
      _ = 0 := by rw [integral_meyerPoissonTest]; simp

def meyerPoissonTestSource : DeningerMeyerCap :=
  ⟨meyerPoissonTestSchwartz, meyerPoissonTestSchwartz_mem⟩

theorem mellin_meyerPoissonTestSource_ne_zero {s : ℂ}
    (hs : -2 < s.re) (hs1 : s ≠ 1) :
    mellin ((meyerPoissonTestSource : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) s ≠ 0 := by
  have hfun : (((meyerPoissonTestSource : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
      fun x : ℝ => ((meyerPoissonTest x : ℝ) : ℂ) :=
    funext meyerPoissonTestSchwartz_apply
  rw [hfun]
  exact mellin_meyerPoissonTest_ne_zero hs hs1

abbrev CCMZetaCircleLength := {L : ℝ // 0 < L}

instance factZetaCircleLengthPos (L : CCMZetaCircleLength) :
    Fact (0 < (L : ℝ)) := ⟨L.property⟩

theorem liftIoc_eq_periodic_lift {B : Type*} (L : CCMZetaCircleLength)
    (g : ℝ → B) (hg : Function.Periodic g (L : ℝ)) :
    AddCircle.liftIoc (L : ℝ) 0 g = hg.lift := by
  ext x
  obtain ⟨t, ht, rfl⟩ := AddCircle.eq_coe_Ioc x
  rw [AddCircle.liftIoc_coe_apply (by simpa using ht),
    Function.Periodic.lift_coe]

def ccmZetaCircleCriticalPoint (L : CCMZetaCircleLength) (m : ℤ) : ℂ :=
  (1 / 2 : ℂ) - (((2 * Real.pi * (m : ℝ) / (L : ℝ) : ℝ) : ℂ) * Complex.I)

theorem ccmZetaCircleCriticalPoint_re (L : CCMZetaCircleLength) (m : ℤ) :
    (ccmZetaCircleCriticalPoint L m).re = 1 / 2 := by
  simp [ccmZetaCircleCriticalPoint]

theorem ccmZetaCircleCriticalPoint_ne_one (L : CCMZetaCircleLength) (m : ℤ) :
    ccmZetaCircleCriticalPoint L m ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  rw [ccmZetaCircleCriticalPoint_re] at hre
  norm_num at hre

theorem deningerFourierCoeffOn_halfDensityPoisson_eq_zeta_mul_mellin
    (L : CCMZetaCircleLength) (f : DeningerMeyerCap) (m : ℤ) :
    fourierCoeffOn L.property
        (deningerPeriodizationSum
          (((deningerHalfDensityLift (deningerPoissonSource f) :
            DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) (L : ℝ)) m =
      (1 / (L : ℝ)) •
        (riemannZeta (ccmZetaCircleCriticalPoint L m) *
          mellin ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ))
            (ccmZetaCircleCriticalPoint L m)) := by
  let h : DeningerExpSchwartz :=
    deningerHalfDensityLift (deningerPoissonSource f)
  rw [deningerFourierCoeffOn_periodization
    (SchwartzMap.integrable ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) L.property m]
  change (1 / (L : ℝ)) • 𝓕 (((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      ((1 / (L : ℝ)) * (m : ℝ)) = _
  rw [fourier_halfDensityPoisson_eq_mellin]
  have hp :
      ((1 / 2 : ℂ) -
          ↑(2 * Real.pi * ((1 / (L : ℝ)) * (m : ℝ))) * Complex.I) =
        ccmZetaCircleCriticalPoint L m := by
    rw [ccmZetaCircleCriticalPoint]
    push_cast
    congr 2
    field_simp
  rw [hp, mellin_deningerPoissonValue_eq_zeta_mul_of_re_pos f.property
    (by rw [ccmZetaCircleCriticalPoint_re]; norm_num)
    (ccmZetaCircleCriticalPoint_ne_one L m)]

def ccmZetaCycleTrace (L : CCMZetaCircleLength) (f : DeningerMeyerCap) :
    AddCircle (L : ℝ) → ℂ :=
  AddCircle.liftIoc (L : ℝ) 0
    (deningerPeriodizationSum
      (((deningerHalfDensityLift (deningerPoissonSource f) :
        DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) (L : ℝ))

theorem deningerPeriodizationSum_halfDensityPoisson_capFlow
    (L : CCMZetaCircleLength) (c : ℝ) (f : DeningerMeyerCap) (t : ℝ) :
    deningerPeriodizationSum
        (((deningerHalfDensityLift
          (deningerPoissonSource (deningerMeyerCapFlow c f)) :
            DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) (L : ℝ) t =
      ((Real.exp (c / 2) : ℝ) : ℂ) *
        deningerPeriodizationSum
          (((deningerHalfDensityLift (deningerPoissonSource f) :
            DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) (L : ℝ) (t - c) := by
  rw [deningerHalfDensityPoisson_capFlow]
  let a : ℂ := ((Real.exp (c / 2) : ℝ) : ℂ)
  let h : DeningerExpSchwartz :=
    deningerEscapeFamily 0 c
      (deningerHalfDensityLift (deningerPoissonSource f))
  change deningerPeriodizationSum (((a • h : DeningerExpSchwartz) :
    𝓢(ℝ, ℂ))) (L : ℝ) t = _
  have hcoe :
      (((a • h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) =
        a • ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) := rfl
  rw [hcoe]
  dsimp only [a, h]
  rw [deningerPeriodizationSum_smul,
    deningerEscapeFamily_periodizationSum]
  norm_num

/-- Connes--Consani Lemma `scalingact` (ii): source scaling descends to
circle translation on the periodized half-density boundary. -/
theorem ccmZetaCycleTrace_capFlow
    (L : CCMZetaCircleLength) (c : ℝ) (f : DeningerMeyerCap)
    (x : AddCircle (L : ℝ)) :
    ccmZetaCycleTrace L (deningerMeyerCapFlow c f) x =
      ((Real.exp (c / 2) : ℝ) : ℂ) *
        ccmZetaCycleTrace L f (x - (c : AddCircle (L : ℝ))) := by
  induction x using QuotientAddGroup.induction_on with
  | _ t =>
      rw [ccmZetaCycleTrace, ccmZetaCycleTrace,
        liftIoc_eq_periodic_lift L _
          (deningerPeriodizationSum_periodic _ (L : ℝ)),
        liftIoc_eq_periodic_lift L _
          (deningerPeriodizationSum_periodic _ (L : ℝ))]
      rw [Function.Periodic.lift_coe]
      rw [show (t : AddCircle (L : ℝ)) - (c : AddCircle (L : ℝ)) =
          ((t - c : ℝ) : AddCircle (L : ℝ)) by
        rw [sub_eq_add_neg, sub_eq_add_neg, AddCircle.coe_add,
          AddCircle.coe_neg]]
      rw [Function.Periodic.lift_coe]
      exact deningerPeriodizationSum_halfDensityPoisson_capFlow L c f t

theorem continuous_ccmZetaCycleTrace (L : CCMZetaCircleLength)
    (f : DeningerMeyerCap) : Continuous (ccmZetaCycleTrace L f) := by
  apply AddCircle.liftIoc_continuous
  · exact (deningerPeriodizationSum_periodic
      (((deningerHalfDensityLift (deningerPoissonSource f) :
        DeningerExpSchwartz) : 𝓢(ℝ, ℂ))) (L : ℝ) 0).symm
  · exact (deningerPeriodizationSum_contDiff
      (deningerHalfDensityLift (deningerPoissonSource f)).property L.property).continuous.continuousOn

theorem fourierCoeff_ccmZetaCycleTrace_eq_zeta_mul_mellin
    (L : CCMZetaCircleLength) (f : DeningerMeyerCap) (m : ℤ) :
    fourierCoeff (ccmZetaCycleTrace L f) m =
      (1 / (L : ℝ)) •
        (riemannZeta (ccmZetaCircleCriticalPoint L m) *
          mellin ((f : DeningerMeyerCap) : 𝓢(ℝ, ℂ))
            (ccmZetaCircleCriticalPoint L m)) := by
  rw [ccmZetaCycleTrace, fourierCoeff_liftIoc_eq]
  convert deningerFourierCoeffOn_halfDensityPoisson_eq_zeta_mul_mellin L f m using 1 <;> simp

def ccmZetaCycleCharacterSurvives (L : CCMZetaCircleLength) (m : ℤ) : Prop :=
  ∀ f : DeningerMeyerCap, fourierCoeff (ccmZetaCycleTrace L f) m = 0

theorem ccmZetaCycleCharacterSurvives_iff
    (L : CCMZetaCircleLength) (m : ℤ) :
    ccmZetaCycleCharacterSurvives L m ↔
      riemannZeta (ccmZetaCircleCriticalPoint L m) = 0 := by
  constructor
  · intro h
    have htest := h meyerPoissonTestSource
    rw [fourierCoeff_ccmZetaCycleTrace_eq_zeta_mul_mellin] at htest
    have hscale : ((1 / (L : ℝ) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast one_div_ne_zero (ne_of_gt L.property)
    have hmel : mellin
        ((meyerPoissonTestSource : DeningerMeyerCap) : 𝓢(ℝ, ℂ))
          (ccmZetaCircleCriticalPoint L m) ≠ 0 := by
      apply mellin_meyerPoissonTestSource_ne_zero
      · rw [ccmZetaCircleCriticalPoint_re]
        norm_num
      · exact ccmZetaCircleCriticalPoint_ne_one L m
    rw [Complex.real_smul] at htest
    have hprod : riemannZeta (ccmZetaCircleCriticalPoint L m) *
        mellin ((meyerPoissonTestSource : DeningerMeyerCap) : 𝓢(ℝ, ℂ))
          (ccmZetaCircleCriticalPoint L m) = 0 :=
      (mul_eq_zero.mp htest).resolve_left hscale
    exact (mul_eq_zero.mp hprod).resolve_right hmel
  · intro hz f
    rw [fourierCoeff_ccmZetaCycleTrace_eq_zeta_mul_mellin, hz, zero_mul, smul_zero]

/-- Connes--Consani Theorem `spectralreal`, character-spectrum form. -/
theorem connesConsani_spectralreal_character
    (L : CCMZetaCircleLength) (m : ℤ) :
    ccmZetaCycleCharacterSurvives L m ↔
      riemannZeta (ccmZetaCircleCriticalPoint L m) = 0 :=
  ccmZetaCycleCharacterSurvives_iff L m

def ccmZetaCycleTraceContinuous (L : CCMZetaCircleLength)
    (f : DeningerMeyerCap) : C(AddCircle (L : ℝ), ℂ) :=
  ⟨ccmZetaCycleTrace L f, continuous_ccmZetaCycleTrace L f⟩

def ccmZetaCycleTraceL2 (L : CCMZetaCircleLength)
    (f : DeningerMeyerCap) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    (ccmZetaCycleTraceContinuous L f)

theorem ccmZetaCircleMeasurePreservingTranslate (L : CCMZetaCircleLength)
    (a : AddCircle (L : ℝ)) :
    MeasurePreserving (fun x : AddCircle (L : ℝ) => x + a)
      AddCircle.haarAddCircle AddCircle.haarAddCircle :=
  measurePreserving_add_right AddCircle.haarAddCircle a

def ccmZetaCircleTransLM (L : CCMZetaCircleLength)
    (a : AddCircle (L : ℝ)) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) →ₗ[ℂ]
      Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) where
  toFun := Lp.compMeasurePreserving (fun x : AddCircle (L : ℝ) => x + a)
    (ccmZetaCircleMeasurePreservingTranslate L a)
  map_add' u v := map_add _ u v
  map_smul' z u := by
    refine Lp.ext ?_
    have h1 := Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) (z • u)
      (ccmZetaCircleMeasurePreservingTranslate L a)
    have h2 := Lp.coeFn_compMeasurePreserving (E := ℂ) (p := 2) u
      (ccmZetaCircleMeasurePreservingTranslate L a)
    have h3 : (fun x : AddCircle (L : ℝ) => (z • u) x)
        =ᵐ[AddCircle.haarAddCircle] fun x => z • u x := Lp.coeFn_smul z u
    have h4 := (ccmZetaCircleMeasurePreservingTranslate L a).quasiMeasurePreserving.ae_eq_comp h3
    have h5 := Lp.coeFn_smul z
      (Lp.compMeasurePreserving (fun x : AddCircle (L : ℝ) => x + a)
        (ccmZetaCircleMeasurePreservingTranslate L a) u)
    filter_upwards [h1, h2, h4, h5] with x hx1 hx2 hx4 hx5
    simp only [Function.comp_apply, RingHom.id_apply, Pi.smul_apply] at hx1 hx2 hx4 hx5 ⊢
    rw [hx1, hx4, hx5, hx2]

theorem ccmZetaCircleTransLM_coeFn (L : CCMZetaCircleLength)
    (a : AddCircle (L : ℝ))
    (u : Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) :
    (fun x => (ccmZetaCircleTransLM L a u) x) =ᵐ[AddCircle.haarAddCircle]
      fun x => u (x + a) :=
  Lp.coeFn_compMeasurePreserving u (ccmZetaCircleMeasurePreservingTranslate L a)

theorem norm_ccmZetaCircleTransLM (L : CCMZetaCircleLength)
    (a : AddCircle (L : ℝ))
    (u : Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) :
    ‖ccmZetaCircleTransLM L a u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u (ccmZetaCircleMeasurePreservingTranslate L a)

def ccmZetaCircleTransOp (L : CCMZetaCircleLength)
    (a : AddCircle (L : ℝ)) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) →L[ℂ]
      Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) :=
  LinearMap.mkContinuous (ccmZetaCircleTransLM L a) 1 fun u => by
    simpa using (norm_ccmZetaCircleTransLM L a u).le

@[simp]
theorem ccmZetaCircleTransOp_apply (L : CCMZetaCircleLength)
    (a : AddCircle (L : ℝ))
    (u : Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) :
    ccmZetaCircleTransOp L a u = ccmZetaCircleTransLM L a u := rfl

theorem ccmZetaCircleTransOp_coeFn (L : CCMZetaCircleLength)
    (a : AddCircle (L : ℝ))
    (u : Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) :
    (fun x => (ccmZetaCircleTransOp L a u) x) =ᵐ[AddCircle.haarAddCircle]
      fun x => u (x + a) :=
  ccmZetaCircleTransLM_coeFn L a u

theorem ccmZetaCycleTraceL2_capFlow
    (L : CCMZetaCircleLength) (c : ℝ) (f : DeningerMeyerCap) :
    ccmZetaCycleTraceL2 L (deningerMeyerCapFlow c f) =
      ((Real.exp (c / 2) : ℝ) : ℂ) •
        ccmZetaCircleTransOp L (-(c : AddCircle (L : ℝ)))
          (ccmZetaCycleTraceL2 L f) := by
  refine Lp.ext ?_
  have hleft :
      (ccmZetaCycleTraceL2 L (deningerMeyerCapFlow c f) :
        AddCircle (L : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
          ccmZetaCycleTrace L (deningerMeyerCapFlow c f) :=
    ContinuousMap.coeFn_toLp AddCircle.haarAddCircle
      (ccmZetaCycleTraceContinuous L (deningerMeyerCapFlow c f))
  have htrans :
      (fun x => (ccmZetaCircleTransOp L (-(c : AddCircle (L : ℝ)))
        (ccmZetaCycleTraceL2 L f) : AddCircle (L : ℝ) → ℂ) x)
        =ᵐ[AddCircle.haarAddCircle]
      fun x => (ccmZetaCycleTraceL2 L f : AddCircle (L : ℝ) → ℂ)
        (x + -(c : AddCircle (L : ℝ))) := by
    exact ccmZetaCircleTransOp_coeFn L
      (-(c : AddCircle (L : ℝ))) (ccmZetaCycleTraceL2 L f)
  have hbase :
      (ccmZetaCycleTraceL2 L f : AddCircle (L : ℝ) → ℂ)
        =ᵐ[AddCircle.haarAddCircle] ccmZetaCycleTrace L f :=
    ContinuousMap.coeFn_toLp AddCircle.haarAddCircle
      (ccmZetaCycleTraceContinuous L f)
  have hbaseTrans :=
    (ccmZetaCircleMeasurePreservingTranslate L
      (-(c : AddCircle (L : ℝ)))).quasiMeasurePreserving.ae_eq_comp
        hbase
  have hsmul := Lp.coeFn_smul (((Real.exp (c / 2) : ℝ) : ℂ))
    (ccmZetaCircleTransOp L (-(c : AddCircle (L : ℝ)))
      (ccmZetaCycleTraceL2 L f))
  filter_upwards [hleft, htrans, hbaseTrans, hsmul] with x hxleft hxtrans hxbase hxsmul
  simp only [Function.comp_apply] at hxbase
  rw [hxleft]
  calc
    ccmZetaCycleTrace L (deningerMeyerCapFlow c f) x =
        ((Real.exp (c / 2) : ℝ) : ℂ) *
          ccmZetaCycleTrace L f (x - (c : AddCircle (L : ℝ))) :=
      ccmZetaCycleTrace_capFlow L c f x
    _ = ((Real.exp (c / 2) : ℝ) : ℂ) *
          ccmZetaCycleTrace L f (x + -(c : AddCircle (L : ℝ))) := by
      rfl
    _ = ((Real.exp (c / 2) : ℝ) : ℂ) *
          (ccmZetaCycleTraceL2 L f : AddCircle (L : ℝ) → ℂ)
            (x + -(c : AddCircle (L : ℝ))) := by rw [hxbase]
    _ = ((Real.exp (c / 2) : ℝ) : ℂ) *
          (ccmZetaCircleTransOp L
            (-(c : AddCircle (L : ℝ))) (ccmZetaCycleTraceL2 L f) :
              AddCircle (L : ℝ) → ℂ) x := by
      rw [hxtrans]
    _ = (((((Real.exp (c / 2) : ℝ) : ℂ) •
          ccmZetaCircleTransOp L
            (-(c : AddCircle (L : ℝ))) (ccmZetaCycleTraceL2 L f)) :
              Lp ℂ 2 AddCircle.haarAddCircle) : AddCircle (L : ℝ) → ℂ) x :=
      by simpa [Pi.smul_apply, smul_eq_mul] using hxsmul.symm

theorem fourierBasis_repr_ccmZetaCycleTraceL2
    (L : CCMZetaCircleLength) (f : DeningerMeyerCap) (m : ℤ) :
    fourierBasis.repr (ccmZetaCycleTraceL2 L f) m =
      fourierCoeff (ccmZetaCycleTrace L f) m := by
  rw [fourierBasis_repr]
  have hae :
      (ccmZetaCycleTraceL2 L f : AddCircle (L : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
        ccmZetaCycleTrace L f := by
    exact ContinuousMap.coeFn_toLp AddCircle.haarAddCircle
      (ccmZetaCycleTraceContinuous L f)
  exact congrFun (fourierCoeff_congr_ae hae) m

def ccmZetaCycleSourceSubmodule (L : CCMZetaCircleLength) :
    Submodule ℂ (Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) :=
  (Submodule.span ℂ (Set.range (ccmZetaCycleTraceL2 L))).topologicalClosure

theorem ccmZetaCycleTraceL2_mem_sourceSpan
    (L : CCMZetaCircleLength) (f : DeningerMeyerCap) :
    ccmZetaCycleTraceL2 L f ∈
      Submodule.span ℂ (Set.range (ccmZetaCycleTraceL2 L)) :=
  Submodule.subset_span ⟨f, rfl⟩

theorem transOp_ccmZetaCycleTraceL2_mem_sourceSpan
    (L : CCMZetaCircleLength) (a : AddCircle (L : ℝ))
    (f : DeningerMeyerCap) :
    ccmZetaCircleTransOp L a (ccmZetaCycleTraceL2 L f) ∈
      Submodule.span ℂ (Set.range (ccmZetaCycleTraceL2 L)) := by
  obtain ⟨c, -, hc⟩ := AddCircle.eq_coe_Ioc (-a)
  have hca : -(c : AddCircle (L : ℝ)) = a := by
    rw [hc, neg_neg]
  have hflow := ccmZetaCycleTraceL2_capFlow L c f
  rw [hca] at hflow
  have hmem := ccmZetaCycleTraceL2_mem_sourceSpan L
    (deningerMeyerCapFlow c f)
  rw [hflow] at hmem
  have hscale : (((Real.exp (c / 2) : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.2 (Real.exp_ne_zero _)
  have hinv := (Submodule.span ℂ (Set.range (ccmZetaCycleTraceL2 L))).smul_mem
    (((Real.exp (c / 2) : ℝ) : ℂ)⁻¹) hmem
  rw [inv_smul_smul₀ hscale] at hinv
  exact hinv

theorem ccmZetaCycleSourceSubmodule_translation_invariant
    (L : CCMZetaCircleLength) (a : AddCircle (L : ℝ))
    {u : Lp ℂ 2 AddCircle.haarAddCircle}
    (hu : u ∈ ccmZetaCycleSourceSubmodule L) :
    ccmZetaCircleTransOp L a u ∈
      ccmZetaCycleSourceSubmodule L := by
  let T := ccmZetaCircleTransOp L a
  let S := Submodule.span ℂ (Set.range (ccmZetaCycleTraceL2 L))
  have hSinv : S ∈ Module.End.invtSubmodule T.toLinearMap := by
    rw [Module.End.mem_invtSubmodule_iff_map_le]
    rintro _ ⟨u, hu, rfl⟩
    refine Submodule.span_induction (p := fun v _ => T v ∈ S) ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨f, rfl⟩
      exact transOp_ccmZetaCycleTraceL2_mem_sourceSpan L a f
    · exact T.map_zero ▸ Submodule.zero_mem S
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem S hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem S c hx
  have hclosure := Submodule.topologicalClosure_mem_invtSubmodule hSinv
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hclosure
  exact hclosure ⟨u, hu, rfl⟩

def ccmZetaCircleTranslateContinuous (L : CCMZetaCircleLength)
    (v : C(AddCircle (L : ℝ), ℂ)) (a : AddCircle (L : ℝ)) :
    C(AddCircle (L : ℝ), ℂ) :=
  ⟨fun x => v (x + a), v.continuous.comp (continuous_id.add continuous_const)⟩

theorem continuous_ccmZetaCircleTranslateContinuous (L : CCMZetaCircleLength)
    (v : C(AddCircle (L : ℝ), ℂ)) :
    Continuous (ccmZetaCircleTranslateContinuous L v) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact v.continuous.comp (continuous_snd.add continuous_fst)

theorem ccmZetaCircleTranslateContinuous_toLp (L : CCMZetaCircleLength)
    (v : C(AddCircle (L : ℝ), ℂ)) (a : AddCircle (L : ℝ)) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
        (ccmZetaCircleTranslateContinuous L v a) =
      ccmZetaCircleTransOp L a
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ v) := by
  refine Lp.ext ?_
  have hleft := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    AddCircle.haarAddCircle (ccmZetaCircleTranslateContinuous L v a)
  have hright := ccmZetaCircleTransOp_coeFn L a
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ v)
  have hbase := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ)
    AddCircle.haarAddCircle v
  have hbaseTrans := (ccmZetaCircleMeasurePreservingTranslate L a).quasiMeasurePreserving.ae_eq_comp
    hbase
  filter_upwards [hleft, hright, hbaseTrans] with x hxleft hxright hxbase
  simp only [Function.comp_apply] at hxbase
  rw [hxleft, hxright, hxbase]
  rfl

theorem fourierBasis_repr_ccmZetaCircleTransOp
    (L : CCMZetaCircleLength) (a : AddCircle (L : ℝ))
    (u : Lp ℂ 2 AddCircle.haarAddCircle) (k : ℤ) :
    fourierBasis.repr (ccmZetaCircleTransOp L a u) k =
      fourier k a * fourierBasis.repr u k := by
  rw [fourierBasis_repr, fourierBasis_repr]
  have hae := ccmZetaCircleTransOp_coeFn L a u
  rw [congrFun (fourierCoeff_congr_ae hae) k]
  exact fourierCoeff_comp_add (fun x => u x) k a

theorem integral_fourier_haarAddCircle (L : CCMZetaCircleLength) (q : ℤ) :
    (∫ a : AddCircle (L : ℝ), fourier q a ∂AddCircle.haarAddCircle) =
      if q = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (L : ℝ)) q) 0
  simpa [fourierCoeff, fourier_zero, Pi.single_apply, eq_comm] using h

def ccmZetaCircleFourierProjectionIntegrand (L : CCMZetaCircleLength) (m : ℤ)
    (v : C(AddCircle (L : ℝ), ℂ)) (a : AddCircle (L : ℝ)) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) :=
  fourier (T := (L : ℝ)) (-m) a •
    ContinuousMap.toLp 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) ℂ
      (ccmZetaCircleTranslateContinuous L v a)

theorem continuous_ccmZetaCircleFourierProjectionIntegrand
    (L : CCMZetaCircleLength) (m : ℤ) (v : C(AddCircle (L : ℝ), ℂ)) :
    Continuous (ccmZetaCircleFourierProjectionIntegrand L m v) := by
  exact (map_continuous (fourier (T := (L : ℝ)) (-m))).smul
    ((ContinuousMap.toLp 2
      (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) ℂ).continuous.comp
        (continuous_ccmZetaCircleTranslateContinuous L v))

theorem integrable_ccmZetaCircleFourierProjectionIntegrand
    (L : CCMZetaCircleLength) (m : ℤ) (v : C(AddCircle (L : ℝ), ℂ)) :
    Integrable (ccmZetaCircleFourierProjectionIntegrand L m v)
      (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) := by
  apply (continuous_ccmZetaCircleFourierProjectionIntegrand L m v).integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)

def ccmZetaCircleFourierProjection (L : CCMZetaCircleLength) (m : ℤ)
    (v : C(AddCircle (L : ℝ), ℂ)) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) :=
  ∫ a, ccmZetaCircleFourierProjectionIntegrand L m v a
    ∂(@AddCircle.haarAddCircle (L : ℝ) (inferInstance))

theorem ccmZetaCircleFourierProjection_mem_source
    (L : CCMZetaCircleLength) (m : ℤ) (f : DeningerMeyerCap) :
    ccmZetaCircleFourierProjection L m (ccmZetaCycleTraceContinuous L f) ∈
      ccmZetaCycleSourceSubmodule L := by
  let S := ccmZetaCycleSourceSubmodule L
  have hclosed : IsClosed (S : Set
      (Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)))) := by
    exact (Submodule.span ℂ (Set.range
      (ccmZetaCycleTraceL2 L))).isClosed_topologicalClosure
  have hmem : ∀ a, ccmZetaCircleFourierProjectionIntegrand L m
      (ccmZetaCycleTraceContinuous L f) a ∈ S := by
    intro a
    rw [ccmZetaCircleFourierProjectionIntegrand,
      ccmZetaCircleTranslateContinuous_toLp]
    apply S.smul_mem
    exact ccmZetaCycleSourceSubmodule_translation_invariant L a
      (Submodule.le_topologicalClosure _
        (ccmZetaCycleTraceL2_mem_sourceSpan L f))
  exact (S.restrictScalars ℝ).convex.integral_mem hclosed
    (Filter.Eventually.of_forall hmem)
    (integrable_ccmZetaCircleFourierProjectionIntegrand L m _)

def ccmZetaCircleFourierCoordinate (L : CCMZetaCircleLength) (k : ℤ) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) →L[ℂ] ℂ :=
  innerSL ℂ (fourierBasis k)

@[simp]
theorem ccmZetaCircleFourierCoordinate_apply (L : CCMZetaCircleLength) (k : ℤ)
    (u : Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) :
    ccmZetaCircleFourierCoordinate L k u = fourierBasis.repr u k := by
  exact (HilbertBasis.repr_apply_apply fourierBasis u k).symm

theorem fourierBasis_repr_ccmZetaCircleFourierProjection
    (L : CCMZetaCircleLength) (m k : ℤ) (v : C(AddCircle (L : ℝ), ℂ)) :
    fourierBasis.repr (ccmZetaCircleFourierProjection L m v) k =
      if k = m then fourierBasis.repr
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ v) m else 0 := by
  let base := ContinuousMap.toLp 2
    (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) ℂ v
  let c := fourierBasis.repr base k
  have hint := integrable_ccmZetaCircleFourierProjectionIntegrand L m v
  calc
    fourierBasis.repr (ccmZetaCircleFourierProjection L m v) k =
        ccmZetaCircleFourierCoordinate L k
          (∫ a, ccmZetaCircleFourierProjectionIntegrand L m v a
            ∂(@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) := by
      rw [ccmZetaCircleFourierCoordinate_apply, ccmZetaCircleFourierProjection]
    _ = ∫ a, ccmZetaCircleFourierCoordinate L k
          (ccmZetaCircleFourierProjectionIntegrand L m v a)
          ∂(@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) :=
      (ContinuousLinearMap.integral_comp_comm
        (ccmZetaCircleFourierCoordinate L k) hint).symm
    _ = ∫ a, fourier (k - m) a * c
          ∂(@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) := by
      apply integral_congr_ae
      filter_upwards with a
      rw [ccmZetaCircleFourierProjectionIntegrand, map_smul,
        ccmZetaCircleFourierCoordinate_apply,
        ccmZetaCircleTranslateContinuous_toLp,
        fourierBasis_repr_ccmZetaCircleTransOp]
      change fourier (-m) a * (fourier k a * c) = _
      rw [show k - m = -m + k by ring, fourier_add]
      ring
    _ = (∫ a, fourier (k - m) a
          ∂(@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) * c := by
      rw [integral_mul_const]
    _ = (if k - m = 0 then 1 else 0) * c := by
      rw [integral_fourier_haarAddCircle]
    _ = if k = m then fourierBasis.repr base m else 0 := by
      by_cases hkm : k = m
      · subst k
        simp [c]
      · have hsub : k - m ≠ 0 := sub_ne_zero.mpr hkm
        simp [hkm, hsub]

theorem ccmZetaCircleFourierProjection_eq_coeff_smul_fourierLp
    (L : CCMZetaCircleLength) (m : ℤ) (v : C(AddCircle (L : ℝ), ℂ)) :
    ccmZetaCircleFourierProjection L m v =
      fourierBasis.repr
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ v) m • fourierLp 2 m := by
  apply fourierBasis.repr.injective
  ext k
  rw [fourierBasis_repr_ccmZetaCircleFourierProjection, map_smul,
    ← coe_fourierBasis, HilbertBasis.repr_self]
  change (if k = m then fourierBasis.repr
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ v) m else 0) =
    fourierBasis.repr (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ v) m *
      (Pi.single m (1 : ℂ) : ℤ → ℂ) k
  by_cases hkm : k = m
  · subst k
    simp
  · simp [hkm]

def ccmZetaCycleCohomology (L : CCMZetaCircleLength) :
    Submodule ℂ (Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) :=
  (ccmZetaCycleSourceSubmodule L)ᗮ

theorem fourierLp_mem_ccmZetaCycleCohomology_iff
    (L : CCMZetaCircleLength) (m : ℤ) :
    fourierLp 2 m ∈ ccmZetaCycleCohomology L ↔
      ccmZetaCycleCharacterSurvives L m := by
  rw [ccmZetaCycleCohomology, ccmZetaCycleSourceSubmodule,
    Submodule.orthogonal_closure, Submodule.mem_orthogonal]
  constructor
  · intro h f
    have hgen : ccmZetaCycleTraceL2 L f ∈
        Submodule.span ℂ (Set.range (ccmZetaCycleTraceL2 L)) :=
      Submodule.subset_span ⟨f, rfl⟩
    have hinner : inner ℂ (ccmZetaCycleTraceL2 L f) (fourierLp 2 m) = 0 :=
      h _ hgen
    have hswap : inner ℂ (fourierLp 2 m) (ccmZetaCycleTraceL2 L f) = 0 := by
      rw [← inner_conj_symm, hinner]
      simp
    calc
      fourierCoeff (ccmZetaCycleTrace L f) m =
          fourierBasis.repr (ccmZetaCycleTraceL2 L f) m :=
        (fourierBasis_repr_ccmZetaCycleTraceL2 L f m).symm
      _ = inner ℂ (fourierBasis m) (ccmZetaCycleTraceL2 L f) :=
        HilbertBasis.repr_apply_apply fourierBasis _ _
      _ = inner ℂ (fourierLp 2 m) (ccmZetaCycleTraceL2 L f) := by
        rw [coe_fourierBasis]
      _ = 0 := hswap
  · intro h u hu
    refine Submodule.span_induction (p := fun v _ => inner ℂ v (fourierLp 2 m) = 0)
      ?_ (by simp) ?_ ?_ hu
    · intro x hx
      obtain ⟨f, rfl⟩ := hx
      have hcoeff := h f
      have hbasis : inner ℂ (fourierLp 2 m) (ccmZetaCycleTraceL2 L f) = 0 := by
        calc
          inner ℂ (fourierLp 2 m) (ccmZetaCycleTraceL2 L f) =
              inner ℂ (fourierBasis m) (ccmZetaCycleTraceL2 L f) := by
            rw [coe_fourierBasis]
          _ = fourierBasis.repr (ccmZetaCycleTraceL2 L f) m :=
            (HilbertBasis.repr_apply_apply fourierBasis _ _).symm
          _ = fourierCoeff (ccmZetaCycleTrace L f) m :=
            fourierBasis_repr_ccmZetaCycleTraceL2 L f m
          _ = 0 := hcoeff
      rw [← inner_conj_symm, hbasis]
      simp
    · intro x y hx hy hx0 hy0
      rw [inner_add_left, hx0, hy0, add_zero]
    · intro c x hx hx0
      rw [inner_smul_left, hx0, mul_zero]

theorem fourierLp_mem_ccmZetaCycleCohomology_iff_zeta_zero
    (L : CCMZetaCircleLength) (m : ℤ) :
    fourierLp 2 m ∈ ccmZetaCycleCohomology L ↔
      riemannZeta (ccmZetaCircleCriticalPoint L m) = 0 := by
  rw [fourierLp_mem_ccmZetaCycleCohomology_iff,
    ccmZetaCycleCharacterSurvives_iff]

theorem ccmZetaCircleTransOp_fourierLp
    (L : CCMZetaCircleLength) (a : AddCircle (L : ℝ)) (m : ℤ) :
    ccmZetaCircleTransOp L a (fourierLp 2 m) =
      fourier m a • fourierLp 2 m := by
  refine Lp.ext ?_
  have htrans := ccmZetaCircleTransOp_coeFn L a (fourierLp 2 m)
  have hbase := coeFn_fourierLp (T := (L : ℝ)) 2 m
  have hbaseTrans := (ccmZetaCircleMeasurePreservingTranslate L a).quasiMeasurePreserving.ae_eq_comp
    hbase
  have hsmul := Lp.coeFn_smul (fourier (T := (L : ℝ)) m a)
    (fourierLp (T := (L : ℝ)) 2 m)
  filter_upwards [htrans, hbaseTrans, hsmul, hbase] with x
      hxtrans hxbaseTrans hxsmul hxbase
  simp only [Function.comp_apply] at hxbaseTrans
  rw [hxtrans, hxbaseTrans, hxsmul]
  simp only [Pi.smul_apply, hxbase, smul_eq_mul, fourier_add_arg]
  ring

/-- Literal eigenmode form of Connes--Consani Theorem `spectralreal` (i):
the `m`-th translation character occurs in zeta-cycle cohomology exactly
when zeta vanishes at its associated critical-line frequency. -/
theorem connesConsani_spectralreal_mode
    (L : CCMZetaCircleLength) (m : ℤ) :
    (fourierLp 2 m ∈ ccmZetaCycleCohomology L ∧
      ∀ a : AddCircle (L : ℝ),
        ccmZetaCircleTransOp L a (fourierLp 2 m) =
          fourier m a • fourierLp 2 m) ↔
      riemannZeta (ccmZetaCircleCriticalPoint L m) = 0 := by
  constructor
  · rintro ⟨hmem, -⟩
    exact (fourierLp_mem_ccmZetaCycleCohomology_iff_zeta_zero L m).1 hmem
  · intro hz
    exact ⟨(fourierLp_mem_ccmZetaCycleCohomology_iff_zeta_zero L m).2 hz,
      fun a => ccmZetaCircleTransOp_fourierLp L a m⟩

def CCMIsZetaCycle (L : CCMZetaCircleLength) : Prop :=
  ccmZetaCycleSourceSubmodule L ≠ ⊤

theorem ccmIsZetaCycle_of_character_survives
    (L : CCMZetaCircleLength) (m : ℤ)
    (hm : ccmZetaCycleCharacterSurvives L m) : CCMIsZetaCycle L := by
  intro htop
  have hb : fourierLp 2 m ∈ ccmZetaCycleCohomology L :=
    (fourierLp_mem_ccmZetaCycleCohomology_iff L m).2 hm
  have hb0 :
      (fourierLp (T := (L : ℝ)) 2 m :
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (L : ℝ)))) = 0 := by
    rw [ccmZetaCycleCohomology, htop, Submodule.top_orthogonal_eq_bot] at hb
    exact (Submodule.mem_bot ℂ).mp hb
  exact ((orthonormal_fourier (T := (L : ℝ))).ne_zero m) hb0

theorem fourierBasis_repr_meyerPoissonTestSource_ne_zero_of_zeta_ne_zero
    (L : CCMZetaCircleLength) (m : ℤ)
    (hz : riemannZeta (ccmZetaCircleCriticalPoint L m) ≠ 0) :
    fourierBasis.repr
      (ccmZetaCycleTraceL2 L meyerPoissonTestSource) m ≠ 0 := by
  rw [fourierBasis_repr_ccmZetaCycleTraceL2,
    fourierCoeff_ccmZetaCycleTrace_eq_zeta_mul_mellin]
  rw [Complex.real_smul]
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr
      (one_div_ne_zero (ne_of_gt L.property))
  · apply mul_ne_zero hz
    apply mellin_meyerPoissonTestSource_ne_zero
    · rw [ccmZetaCircleCriticalPoint_re]
      norm_num
    · exact ccmZetaCircleCriticalPoint_ne_one L m

theorem fourierLp_mem_ccmZetaCycleSourceSubmodule_of_zeta_ne_zero
    (L : CCMZetaCircleLength) (m : ℤ)
    (hz : riemannZeta (ccmZetaCircleCriticalPoint L m) ≠ 0) :
    fourierLp 2 m ∈ ccmZetaCycleSourceSubmodule L := by
  let c := fourierBasis.repr
    (ccmZetaCycleTraceL2 L meyerPoissonTestSource) m
  have hc : c ≠ 0 :=
    fourierBasis_repr_meyerPoissonTestSource_ne_zero_of_zeta_ne_zero L m hz
  have hproj := ccmZetaCircleFourierProjection_mem_source
    L m meyerPoissonTestSource
  rw [ccmZetaCircleFourierProjection_eq_coeff_smul_fourierLp] at hproj
  change c • fourierLp 2 m ∈ ccmZetaCycleSourceSubmodule L at hproj
  have hinv := (ccmZetaCycleSourceSubmodule L).smul_mem c⁻¹ hproj
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hinv

theorem ccmZetaCycleSourceSubmodule_eq_top_of_all_zeta_ne_zero
    (L : CCMZetaCircleLength)
    (hz : ∀ m : ℤ, riemannZeta (ccmZetaCircleCriticalPoint L m) ≠ 0) :
    ccmZetaCycleSourceSubmodule L = ⊤ := by
  have hspan : Submodule.span ℂ (Set.range
      (fourierBasis : ℤ → Lp ℂ 2 AddCircle.haarAddCircle)) ≤
      ccmZetaCycleSourceSubmodule L := by
    apply Submodule.span_le.mpr
    intro u hu
    obtain ⟨m, rfl⟩ := hu
    rw [coe_fourierBasis]
    exact fourierLp_mem_ccmZetaCycleSourceSubmodule_of_zeta_ne_zero
      L m (hz m)
  have hclosure : (Submodule.span ℂ (Set.range
      (fourierBasis : ℤ → Lp ℂ 2 AddCircle.haarAddCircle))).topologicalClosure ≤
      ccmZetaCycleSourceSubmodule L := by
    apply Submodule.topologicalClosure_minimal _ hspan
    exact (Submodule.span ℂ (Set.range
      (ccmZetaCycleTraceL2 L))).isClosed_topologicalClosure
  rw [HilbertBasis.dense_span] at hclosure
  exact top_unique hclosure

/-- Connes--Consani Theorem `spectralreal` (i): a circle is a zeta cycle
exactly when one of its Fourier frequencies is the imaginary part of a
critical-line zeta zero. -/
theorem connesConsani_spectralreal (L : CCMZetaCircleLength) :
    CCMIsZetaCycle L ↔
      ∃ m : ℤ, riemannZeta (ccmZetaCircleCriticalPoint L m) = 0 := by
  constructor
  · intro hcycle
    by_contra hnone
    push Not at hnone
    exact hcycle
      (ccmZetaCycleSourceSubmodule_eq_top_of_all_zeta_ne_zero L hnone)
  · rintro ⟨m, hm⟩
    exact ccmIsZetaCycle_of_character_survives L m
      ((ccmZetaCycleCharacterSurvives_iff L m).2 hm)

def ccmZetaCircleCoverLength (L : CCMZetaCircleLength)
    (n : ℕ+) : CCMZetaCircleLength :=
  ⟨(n : ℕ) * (L : ℝ),
    mul_pos (by exact_mod_cast n.property) L.property⟩

theorem ccmZetaCircleCriticalPoint_cover (L : CCMZetaCircleLength)
    (n : ℕ+) (m : ℤ) :
    ccmZetaCircleCriticalPoint (ccmZetaCircleCoverLength L n) ((n : ℤ) * m) =
      ccmZetaCircleCriticalPoint L m := by
  rw [ccmZetaCircleCriticalPoint, ccmZetaCircleCriticalPoint,
    ccmZetaCircleCoverLength]
  have hn : (0 : ℝ) < (n : ℕ) := by positivity
  push_cast
  field_simp

/-- Connes--Consani Proposition `traversals`: every positive finite cover
of a zeta cycle is again a zeta cycle. -/
theorem connesConsani_traversals (L : CCMZetaCircleLength) (n : ℕ+)
    (hL : CCMIsZetaCycle L) :
    CCMIsZetaCycle (ccmZetaCircleCoverLength L n) := by
  obtain ⟨m, hm⟩ := (connesConsani_spectralreal L).1 hL
  apply (connesConsani_spectralreal (ccmZetaCircleCoverLength L n)).2
  refine ⟨(n : ℤ) * m, ?_⟩
  rw [ccmZetaCircleCriticalPoint_cover]
  exact hm

def CCMCriticalZetaOrdinateSet : Set ℝ :=
  {s | riemannZeta ((1 / 2 : ℂ) + (s : ℂ) * Complex.I) = 0}

theorem ccmZetaCircleCriticalPoint_as_ordinate
    (L : CCMZetaCircleLength) (m : ℤ) :
    ccmZetaCircleCriticalPoint L m =
      (1 / 2 : ℂ) +
        ((-2 * Real.pi * (m : ℝ) / (L : ℝ) : ℝ) : ℂ) * Complex.I := by
  rw [ccmZetaCircleCriticalPoint]
  push_cast
  ring

theorem ccmZetaCircle_resonance_from_index
    (L : CCMZetaCircleLength) (m : ℤ) :
    (-2 * Real.pi * (m : ℝ) / (L : ℝ)) * (L : ℝ) =
      2 * Real.pi * (-(m : ℤ) : ℤ) := by
  have hL : (L : ℝ) ≠ 0 := ne_of_gt L.property
  push_cast
  field_simp

theorem ccmZetaCircleCriticalPoint_eq_of_resonance
    (L : CCMZetaCircleLength) (s : ℝ) (n : ℤ)
    (h : s * (L : ℝ) = 2 * Real.pi * n) :
    ccmZetaCircleCriticalPoint L (-n) =
      (1 / 2 : ℂ) + (s : ℂ) * Complex.I := by
  rw [ccmZetaCircleCriticalPoint]
  have hL : (L : ℝ) ≠ 0 := ne_of_gt L.property
  have hs : s = 2 * Real.pi * (n : ℝ) / (L : ℝ) :=
    (eq_div_iff hL).2 h
  rw [hs]
  push_cast
  ring

theorem ccmZetaCycleCohomology_ne_bot_iff (L : CCMZetaCircleLength) :
    ccmZetaCycleCohomology L ≠ ⊥ ↔ CCMIsZetaCycle L := by
  constructor
  · intro hcoh htop
    apply hcoh
    rw [ccmZetaCycleCohomology, htop, Submodule.top_orthogonal_eq_bot]
  · intro hcycle hbot
    obtain ⟨m, hm⟩ := (connesConsani_spectralreal L).1 hcycle
    have hb : fourierLp 2 m ∈ ccmZetaCycleCohomology L :=
      (fourierLp_mem_ccmZetaCycleCohomology_iff_zeta_zero L m).2 hm
    rw [hbot] at hb
    have hb0 : (fourierLp (T := (L : ℝ)) 2 m :
        Lp ℂ 2 AddCircle.haarAddCircle) = 0 :=
      (Submodule.mem_bot ℂ).mp hb
    exact ((orthonormal_fourier (T := (L : ℝ))).ne_zero m) hb0

/-- Connes--Consani Corollary `repetitions`: the zeta-cycle cohomology is
nonzero exactly at resonant lengths `sL = 2πn` for critical-line zeta
ordinates `s`. -/
theorem connesConsani_repetitions (L : CCMZetaCircleLength) :
    ccmZetaCycleCohomology L ≠ ⊥ ↔
      ∃ s ∈ CCMCriticalZetaOrdinateSet,
        ∃ n : ℤ, s * (L : ℝ) = 2 * Real.pi * n := by
  rw [ccmZetaCycleCohomology_ne_bot_iff, connesConsani_spectralreal]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨-2 * Real.pi * (m : ℝ) / (L : ℝ), ?_, -(m : ℤ), ?_⟩
    · change riemannZeta ((1 / 2 : ℂ) +
          ((-2 * Real.pi * (m : ℝ) / (L : ℝ) : ℝ) : ℂ) * Complex.I) = 0
      rw [← ccmZetaCircleCriticalPoint_as_ordinate]
      exact hm
    · exact ccmZetaCircle_resonance_from_index L m
  · rintro ⟨s, hs, n, hres⟩
    refine ⟨-n, ?_⟩
    rw [ccmZetaCircleCriticalPoint_eq_of_resonance L s n hres]
    exact hs

structure CCMCriticalLineZetaZero where
  ordinate : ℝ
  ordinate_pos : 0 < ordinate
  vanishing : riemannZeta ((1 / 2 : ℂ) + (ordinate : ℂ) * Complex.I) = 0

def ccmCriticalZetaCircleLength (z : CCMCriticalLineZetaZero)
    (n : ℕ+) : CCMZetaCircleLength :=
  ⟨2 * Real.pi * (n : ℕ) / z.ordinate,
    div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (by exact_mod_cast n.property)) z.ordinate_pos⟩

theorem ccmZetaCircleCriticalPoint_neg_n_eq
    (z : CCMCriticalLineZetaZero) (n : ℕ+) :
    ccmZetaCircleCriticalPoint (ccmCriticalZetaCircleLength z n) (-(n : ℤ)) =
      (1 / 2 : ℂ) + (z.ordinate : ℂ) * Complex.I := by
  rw [ccmZetaCircleCriticalPoint, ccmCriticalZetaCircleLength]
  have hn : (0 : ℝ) < (n : ℕ) := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hz : z.ordinate ≠ 0 := z.ordinate_pos.ne'
  push_cast
  field_simp
  ring

/-- Connes--Consani Theorem `spectralreal` (ii), with zero data intrinsic. -/
theorem connesConsani_spectralreal_converse
    (z : CCMCriticalLineZetaZero) (n : ℕ+) :
    CCMIsZetaCycle (ccmCriticalZetaCircleLength z n) ∧
      ccmZetaCycleCharacterSurvives
        (ccmCriticalZetaCircleLength z n) (-(n : ℤ)) := by
  have hz : riemannZeta
      (ccmZetaCircleCriticalPoint (ccmCriticalZetaCircleLength z n) (-(n : ℤ))) = 0 := by
    rw [ccmZetaCircleCriticalPoint_neg_n_eq]
    exact z.vanishing
  have hsurv := (ccmZetaCycleCharacterSurvives_iff
    (ccmCriticalZetaCircleLength z n) (-(n : ℤ))).2 hz
  exact ⟨ccmIsZetaCycle_of_character_survives _ _ hsurv, hsurv⟩

end

end RHTower
