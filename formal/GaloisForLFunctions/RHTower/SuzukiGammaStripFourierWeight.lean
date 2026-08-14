import GaloisForLFunctions.RHTower.SuzukiGammaStripContourPairing
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The transform of the glued seam carries a single exponential weight

The boundary datum of the glued strip solution on the line of height `σ` is square integrable, so
it has an `L²` inverse Fourier transform.  Pairing that transform with an exponentially weighted
test function turns, by the multiplication formula for tempered distributions, into the pairing of
the boundary datum with the entire Fourier extension of the test function; the contour shift makes
that pairing independent of `σ`.  Hence the transforms of the different lines differ exactly by the
exponential weights `e^{2πσL}`, and one single frequency profile `F` satisfies
`e^{2πσL}F ∈ L²(ℝ;X)` for every `0 < σ < 1`.
-/

open Set Complex MeasureTheory Filter SchwartzMap

open scoped ContDiff FourierTransform

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

omit [CompleteSpace X] [Nontrivial X] in
/-- A continuous scalar factor preserves local integrability. -/
theorem locallyIntegrable_real_continuous_smul {f : ℝ → X}
    (hf : LocallyIntegrable f (volume : Measure ℝ)) {h : ℝ → ℝ} (hh : Continuous h) :
    LocallyIntegrable (fun x : ℝ => h x • f x) (volume : Measure ℝ) := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (hf.integrableOn_isCompact hK).continuousOn_smul hh.continuousOn hK

/-- The boundary datum of the strip solution on the interior line of height `σ`. -/
def stripLine (E : ℂ → ℂ) (T : X →L[ℂ] X) (c : X) (σ : ℝ) : ℝ → X :=
  fun x => stripSolution E T c ((x : ℂ) + (σ : ℂ) * Complex.I)

omit [Nontrivial X] in
theorem continuous_stripLine {E : ℂ → ℂ} (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (T : X →L[ℂ] X) (c : X) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    Continuous (stripLine E T c σ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hline : ContinuousAt (fun x : ℝ => ((x : ℂ) + (σ : ℂ) * Complex.I)) x := by fun_prop
  have hmem : ((x : ℂ) + (σ : ℂ) * Complex.I) ∈ imStrip 0 1 := by
    constructor <;> simp [hσ.1, hσ.2]
  have hdiff : DifferentiableAt ℂ (stripSolution E T c) ((x : ℂ) + (σ : ℂ) * Complex.I) :=
    (differentiableOn_stripSolution hEd T c).differentiableAt
      ((isOpen_imStrip 0 1).mem_nhds hmem)
  have hcomp : ContinuousAt ((stripSolution E T c)
      ∘ (fun x : ℝ => ((x : ℂ) + (σ : ℂ) * Complex.I))) x :=
    ContinuousAt.comp hdiff.continuousAt hline
  exact hcomp

/-- The boundary datum is square integrable. -/
theorem memLp_stripLine {E : ℂ → ℂ} {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) (c : X) {σ : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    MemLp (stripLine E T c σ) 2 (volume : Measure ℝ) := by
  refine (memLp_two_iff_integrable_sq_norm
    (continuous_stripLine hEd T c hσ).aestronglyMeasurable).mpr ?_
  exact integrable_norm_sq_stripSolution hT hEd.continuousOn hE c hσ.1 hσ.2

/-- The boundary datum as an `L²` class. -/
def stripLineLp {E : ℂ → ℂ} {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) (c : X) {σ : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) : Lp X 2 (volume : Measure ℝ) :=
  (memLp_stripLine hT hEd hE c hσ).toLp _

/-- The exponentially weighted test function on the frequency line. -/
def weightedTest (ψ : ℝ → ℂ) (σ : ℝ) : ℝ → ℂ :=
  fun L => ψ L * Complex.exp (-(((2 * Real.pi * σ * L : ℝ)) : ℂ))

theorem contDiff_weightedTest {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (σ : ℝ) :
    ContDiff ℝ ∞ (weightedTest ψ σ) := by
  have h0 : ContDiff ℝ ∞ (fun L : ℝ => (2 * Real.pi * σ * L : ℝ)) := by fun_prop
  have hlin : ContDiff ℝ ∞ (fun L : ℝ => (((2 * Real.pi * σ * L : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h0
  exact hψ.mul (Complex.contDiff_exp.comp hlin.neg)

theorem hasCompactSupport_weightedTest {ψ : ℝ → ℂ} (hψs : HasCompactSupport ψ) (σ : ℝ) :
    HasCompactSupport (weightedTest ψ σ) := hψs.mul_right

/-- The inverse Fourier transform of the weighted test function is the rescaled test transform on
the shifted line. -/
theorem fourierInv_weightedTest (ψ : ℝ → ℂ) (σ x : ℝ) :
    𝓕⁻ (weightedTest ψ σ) x = testTransformTwoPi ψ ((x : ℂ) + (σ : ℂ) * Complex.I) := by
  rw [Real.fourierInv_eq', testTransformTwoPi_ofReal_line]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
  simp only [weightedTest, smul_eq_mul]
  congr 2
  push_cast [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  ring

set_option maxHeartbeats 1000000 in
/-- **The multiplication formula for the boundary pairing.**  Testing the `L²` transform of the
boundary datum against a weighted test function is the same as testing the boundary datum against
the entire Fourier extension. -/
theorem integral_weightedTest_smul_fourierInv {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : HasCompactSupport ψ) {E : ℂ → ℂ} {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) (c : X) {σ : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    (∫ L : ℝ, weightedTest ψ σ L •
        ((𝓕⁻ (stripLineLp hT hEd hE c hσ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L)
      = ∫ x : ℝ, pairedIntegrand ψ E T c ((x : ℂ) + (σ : ℂ) * Complex.I) := by
  set u : Lp X 2 (volume : Measure ℝ) := stripLineLp hT hEd hE c hσ with hu
  set φ : 𝓢(ℝ, ℂ) :=
    (hasCompactSupport_weightedTest hψs σ).toSchwartzMap (contDiff_weightedTest hψ σ) with hφ
  set φinv : 𝓢(ℝ, ℂ) := 𝓕⁻ φ with hφinv
  have hφcoe : ⇑φ = weightedTest ψ σ := rfl
  have hstep1 : (∫ L : ℝ, weightedTest ψ σ L •
      ((𝓕⁻ u : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L)
      = (((𝓕⁻ u : Lp X 2 (volume : Measure ℝ)) : 𝓢'(ℝ, X))) φ := by
    rw [MeasureTheory.Lp.toTemperedDistribution_apply, hφcoe]
  have hstep2 : (((𝓕⁻ u : Lp X 2 (volume : Measure ℝ)) : 𝓢'(ℝ, X))) φ
      = ((u : 𝓢'(ℝ, X))) φinv := by
    rw [← MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq u, hφinv]
    exact TemperedDistribution.fourierInv_apply _ _
  have hstep3 : ((u : 𝓢'(ℝ, X))) φinv = ∫ x : ℝ, φinv x • (u : ℝ → X) x :=
    MeasureTheory.Lp.toTemperedDistribution_apply u φinv
  have hcoeinv : ∀ x : ℝ, φinv x = testTransformTwoPi ψ ((x : ℂ) + (σ : ℂ) * Complex.I) := by
    intro x
    have h1 : ⇑φinv = 𝓕⁻ (weightedTest ψ σ) := by
      rw [hφinv, SchwartzMap.fourierInv_coe, hφcoe]
    rw [h1]
    exact fourierInv_weightedTest ψ σ x
  have hucoe : (u : ℝ → X) =ᵐ[volume] stripLine E T c σ := by
    rw [hu, stripLineLp]
    exact (memLp_stripLine hT hEd hE c hσ).coeFn_toLp
  have hstep4 : (∫ x : ℝ, φinv x • (u : ℝ → X) x)
      = ∫ x : ℝ, pairedIntegrand ψ E T c ((x : ℂ) + (σ : ℂ) * Complex.I) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hucoe] with x hx
    rw [hcoeinv x, hx, pairedIntegrand, stripLine]
  rw [hstep1, hstep2, hstep3, hstep4]

set_option maxHeartbeats 1000000 in
/-- **`(32)`: the exponentially damped transforms of the different lines agree.** -/
theorem stripFourier_weight_eq {E : ℂ → ℂ} {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) (c : X) {σ σ' : ℝ}
    (hσ : σ ∈ Ioo (0 : ℝ) 1) (hσ' : σ' ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ L : ℝ, Real.exp (-(2 * Real.pi * σ * L)) •
        ((𝓕⁻ (stripLineLp hT hEd hE c hσ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L
      = Real.exp (-(2 * Real.pi * σ' * L)) •
        ((𝓕⁻ (stripLineLp hT hEd hE c hσ') : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L := by
  have hloc : ∀ {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1),
      LocallyIntegrable (fun L : ℝ => Real.exp (-(2 * Real.pi * τ * L)) •
        ((𝓕⁻ (stripLineLp hT hEd hE c hτ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L)
        (volume : Measure ℝ) := by
    intro τ hτ
    refine locallyIntegrable_real_continuous_smul ((Lp.memLp _).locallyIntegrable (by norm_num)) ?_
    exact Real.continuous_exp.comp (by fun_prop)
  refine ae_eq_of_integral_contDiff_smul_eq (hloc hσ) (hloc hσ') ?_
  intro g hg hgs
  set ψ : ℝ → ℂ := (fun r : ℝ => ((r : ℝ) : ℂ)) ∘ g with hψdef
  have hψ : ContDiff ℝ ∞ ψ := Complex.ofRealCLM.contDiff.comp hg
  have hψs : HasCompactSupport ψ := hgs.comp_left rfl
  have hrewrite : ∀ {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1),
      (∫ L : ℝ, g L • (Real.exp (-(2 * Real.pi * τ * L)) •
        ((𝓕⁻ (stripLineLp hT hEd hE c hτ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L))
      = ∫ x : ℝ, pairedIntegrand ψ E T c ((x : ℂ) + (τ : ℂ) * Complex.I) := by
    intro τ hτ
    rw [← integral_weightedTest_smul_fourierInv hψ hψs hT hEd hE c hτ]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
    have hcast : weightedTest ψ τ L = (((g L * Real.exp (-(2 * Real.pi * τ * L)) : ℝ)) : ℂ) := by
      simp only [weightedTest, hψdef, Function.comp_apply, Complex.ofReal_mul,
        Complex.ofReal_exp, Complex.ofReal_neg]
    simp only [hcast, Complex.coe_smul, mul_smul]
  rw [hrewrite hσ, hrewrite hσ']
  exact pairedIntegrand_line_shift hψ hψs hT hEd hE c hσ hσ'

set_option maxHeartbeats 1000000 in
/-- **`(25)`: one frequency profile carries every interior line.**  There is a measurable `F` whose
exponential weights `e^{2πσL}F(L)` are exactly the `L²` transforms of the interior lines, hence are
square integrable for every `0 < σ < 1`. -/
theorem exists_memLp_exp_smul_stripFourier {E : ℂ → ℂ} {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (hEd : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) (c : X) :
    ∃ F : ℝ → X, ∀ σ : ℝ, ∀ hσ : σ ∈ Ioo (0 : ℝ) 1,
      (∀ᵐ L : ℝ, ((𝓕⁻ (stripLineLp hT hEd hE c hσ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L
          = Real.exp (2 * Real.pi * σ * L) • F L)
        ∧ MemLp (fun L : ℝ => Real.exp (2 * Real.pi * σ * L) • F L) 2 (volume : Measure ℝ) := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨fun L => Real.exp (-(2 * Real.pi * (1 / 2 : ℝ) * L)) •
    ((𝓕⁻ (stripLineLp hT hEd hE c hhalf) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L, ?_⟩
  intro σ hσ
  have hkey : ∀ᵐ L : ℝ,
      ((𝓕⁻ (stripLineLp hT hEd hE c hσ) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L
        = Real.exp (2 * Real.pi * σ * L) •
          (Real.exp (-(2 * Real.pi * (1 / 2 : ℝ) * L)) •
            ((𝓕⁻ (stripLineLp hT hEd hE c hhalf) : Lp X 2 (volume : Measure ℝ)) : ℝ → X) L) := by
    filter_upwards [stripFourier_weight_eq hT hEd hE c hσ hhalf] with L hL
    rw [← hL, smul_smul, ← Real.exp_add]
    have hzero : 2 * Real.pi * σ * L + -(2 * Real.pi * σ * L) = 0 := by ring
    rw [hzero, Real.exp_zero, one_smul]
  exact ⟨hkey, (Lp.memLp _).ae_eq hkey⟩

end

end GaloisForLFunctions.RHTower
