import GaloisForLFunctions.HTGeometry.HardyLineIndependence
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceFourier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The boundary datum of a Hardy function

The inverse Fourier transform of the boundary values of a Hardy function on the line `Re w = σ`,
weighted back by `e^{σx}`, does not depend on `σ`.  This is the contour-shift statement transported
through Plancherel: testing against a smooth compactly supported function turns the weighted datum
into the line integral of the Hardy function against the exponential transform of the test function,
which is line-independent.

## Main results

* `hardyPreimage`
* `hardyPreimage_weight_ae_eq`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology FourierTransform SchwartzMap

open scoped ContDiff SchwartzMap

noncomputable section

/-- The inverse `L²` Fourier transform of the boundary datum on the line `Re w = σ`. -/
def hardyPreimage (F : ℂ → ℂ) (σ : ℝ)
    (h : MemLp (fun ξ : ℝ => F (rayLine σ ξ)) 2 (volume : Measure ℝ)) :
    Lp ℂ 2 (volume : Measure ℝ) := 𝓕⁻ (h.toLp _)

theorem fourier_hardyPreimage (F : ℂ → ℂ) (σ : ℝ)
    (h : MemLp (fun ξ : ℝ => F (rayLine σ ξ)) 2 (volume : Measure ℝ)) :
    (𝓕 (hardyPreimage F σ h) : Lp ℂ 2 (volume : Measure ℝ)) = h.toLp _ :=
  fourier_fourierInv_eq _

/-! ### The Schwartz test function attached to a real test function and a line -/

/-- A real test function damped by `e^{σx}`, as a complex-valued function. -/
def dampedTest (θ : ℝ → ℝ) (σ : ℝ) : ℝ → ℂ := fun x => ((θ x * Real.exp (σ * x) : ℝ) : ℂ)

theorem contDiff_dampedTest {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (σ : ℝ) :
    ContDiff ℝ ∞ (dampedTest θ σ) := by
  have h1 : ContDiff ℝ ∞ fun x : ℝ => θ x * Real.exp (σ * x) :=
    hθ.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact Complex.ofRealCLM.contDiff.comp h1

theorem hasCompactSupport_dampedTest {θ : ℝ → ℝ} (hs : HasCompactSupport θ) (σ : ℝ) :
    HasCompactSupport (dampedTest θ σ) := by
  refine HasCompactSupport.intro hs.isCompact (fun x hx => ?_)
  have hθx : θ x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp [dampedTest, hθx]

/-- The Schwartz function whose Fourier transform is the damped test function. -/
def testSchwartz (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ) (hs : HasCompactSupport θ) (σ : ℝ) :
    SchwartzMap ℝ ℂ :=
  𝓕⁻ ((hasCompactSupport_dampedTest hs σ).toSchwartzMap (contDiff_dampedTest hθ σ))

theorem fourier_testSchwartz {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hs : HasCompactSupport θ)
    (σ : ℝ) :
    ((𝓕 (testSchwartz θ hθ hs σ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = dampedTest θ σ := by
  rw [testSchwartz, fourier_fourierInv_eq]
  rfl

theorem fourierInv_eq_integral (g : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ g x = ∫ v : ℝ, Complex.exp (((2 * Real.pi * v * x : ℝ)) * Complex.I) • g v := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have harg : (-2 * Real.pi * v * (-x) : ℝ) = (2 * Real.pi * v * x : ℝ) := by ring
  simp only [smul_eq_mul]
  rw [harg]

/-- The Schwartz test function is the exponential transform of the test function on the line. -/
theorem testSchwartz_apply {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hs : HasCompactSupport θ)
    (σ x : ℝ) :
    ((testSchwartz θ hθ hs σ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = expTestTransform (fun t : ℝ => ((θ t : ℝ) : ℂ)) (rayLine σ x) := by
  rw [testSchwartz, fourierInv_coe, fourierInv_eq_integral, expTestTransform_eq]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have hcoe : (((hasCompactSupport_dampedTest hs σ).toSchwartzMap
      (contDiff_dampedTest hθ σ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) v = dampedTest θ σ v := rfl
  simp only [smul_eq_mul]
  rw [hcoe, dampedTest]
  have hsplit : ((θ v * Real.exp (σ * v) : ℝ) : ℂ)
      = ((θ v : ℝ) : ℂ) * Complex.exp (((σ * v : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hsplit]
  have hexp : Complex.exp (((2 * Real.pi * v * x : ℝ)) * Complex.I)
      * Complex.exp (((σ * v : ℝ)) : ℂ) = Complex.exp (rayLine σ x * (v : ℝ)) := by
    rw [← Complex.exp_add, rayLine]
    congr 1
    push_cast
    ring
  calc Complex.exp (((2 * Real.pi * v * x : ℝ)) * Complex.I)
        * (((θ v : ℝ) : ℂ) * Complex.exp (((σ * v : ℝ)) : ℂ))
      = ((θ v : ℝ) : ℂ) * (Complex.exp (((2 * Real.pi * v * x : ℝ)) * Complex.I)
          * Complex.exp (((σ * v : ℝ)) : ℂ)) := by ring
    _ = ((θ v : ℝ) : ℂ) * Complex.exp (rayLine σ x * (v : ℝ)) := by rw [hexp]

/-! ### The line integral against a test function -/

/-- The multiplication formula against a Schwartz function. -/
theorem integral_schwartz_mul_fourier (f : Lp ℂ 2 (volume : Measure ℝ)) (η : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, (η : ℝ → ℂ) x * ((𝓕 f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)
      = ∫ x : ℝ, ((𝓕 η : SchwartzMap ℝ ℂ) : ℝ → ℂ) x * (f : ℝ → ℂ) x := by
  have hdist := Lp.fourier_toTemperedDistribution_eq f
  have hdist_apply := congrArg (fun T : 𝓢'(ℝ, ℂ) => T η) hdist
  simpa [mul_comm] using hdist_apply.symm

/-- **Testing the weighted datum against a test function is a line integral.** -/
theorem integral_test_hardyPreimage {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {σ : ℝ}
    (hσ : 0 < σ) {θ : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hs : HasCompactSupport θ) :
    (∫ x : ℝ, ((θ x * Real.exp (σ * x) : ℝ) : ℂ)
        * (hardyPreimage F σ (hF.memLp σ hσ) : ℝ → ℂ) x)
      = ((2 * Real.pi)⁻¹ : ℝ) • ∫ y : ℝ, F ((σ : ℂ) + (y : ℝ) * Complex.I)
          * expTestTransform (fun t : ℝ => ((θ t : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * Complex.I) := by
  set f : Lp ℂ 2 (volume : Measure ℝ) := hardyPreimage F σ (hF.memLp σ hσ) with hf
  have hmul := integral_schwartz_mul_fourier f (testSchwartz θ hθ hs σ)
  rw [hf, fourier_hardyPreimage] at hmul
  -- the right-hand side of the multiplication formula is the tested weighted datum
  have hrhs : (∫ x : ℝ, ((𝓕 (testSchwartz θ hθ hs σ) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      * (f : ℝ → ℂ) x)
      = ∫ x : ℝ, ((θ x * Real.exp (σ * x) : ℝ) : ℂ) * (f : ℝ → ℂ) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [fourier_testSchwartz hθ hs σ]
    rfl
  -- the left-hand side is the line integral, in the Fourier parametrisation
  have hlhs : (∫ x : ℝ, ((testSchwartz θ hθ hs σ : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      * (((hF.memLp σ hσ).toLp _ : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)
      = ∫ x : ℝ, (fun y : ℝ => F ((σ : ℂ) + (y : ℝ) * Complex.I)
          * expTestTransform (fun t : ℝ => ((θ t : ℝ) : ℂ))
            ((σ : ℂ) + (y : ℝ) * Complex.I)) (2 * Real.pi * x) := by
    refine integral_congr_ae ?_
    filter_upwards [(hF.memLp σ hσ).coeFn_toLp] with x hx
    rw [hx, testSchwartz_apply hθ hs σ x]
    have hline : rayLine σ x = (σ : ℂ) + ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := rfl
    rw [hline]
    ring
  rw [hrhs] at hmul
  rw [hlhs] at hmul
  have hscale := Measure.integral_comp_mul_left
    (fun y : ℝ => F ((σ : ℂ) + (y : ℝ) * Complex.I)
      * expTestTransform (fun t : ℝ => ((θ t : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * Complex.I))
    (2 * Real.pi)
  rw [← hmul, hscale, abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]

/-! ### The weighted datum does not depend on the line -/

theorem locallyIntegrable_exp_mul_lp (σ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    LocallyIntegrable (fun x : ℝ => ((Real.exp (σ * x) : ℝ) : ℂ) * (f : ℝ → ℂ) x) volume := by
  have hloc : LocallyIntegrable (f : ℝ → ℂ) volume := (Lp.memLp f).locallyIntegrable (by norm_num)
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  have hint : IntegrableOn (f : ℝ → ℂ) K volume := hloc.integrableOn_isCompact hK
  have hcont : ContinuousOn (fun x : ℝ => ((Real.exp (σ * x) : ℝ) : ℂ)) K := by fun_prop
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine hint.bdd_mul (c := C) (hcont.aestronglyMeasurable hK.measurableSet) ?_
  exact (ae_restrict_iff' hK.measurableSet).2 (Filter.Eventually.of_forall hC)

set_option maxHeartbeats 1000000 in
/-- **The weighted boundary datum of a Hardy function does not depend on the line.** -/
theorem hardyPreimage_weight_ae_eq {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    (fun x : ℝ => ((Real.exp (α * x) : ℝ) : ℂ)
        * (hardyPreimage F α (hF.memLp α hα) : ℝ → ℂ) x)
      =ᵐ[volume] fun x : ℝ => ((Real.exp (β * x) : ℝ) : ℂ)
          * (hardyPreimage F β (hF.memLp β hβ) : ℝ → ℂ) x := by
  refine ae_eq_of_integral_contDiff_smul_eq (locallyIntegrable_exp_mul_lp α _)
    (locallyIntegrable_exp_mul_lp β _) (fun g hg hsupp => ?_)
  have hconv : ∀ (γ : ℝ) (hγ : 0 < γ),
      (∫ x : ℝ, g x • (((Real.exp (γ * x) : ℝ) : ℂ)
          * (hardyPreimage F γ (hF.memLp γ hγ) : ℝ → ℂ) x))
        = ∫ x : ℝ, ((g x * Real.exp (γ * x) : ℝ) : ℂ)
            * (hardyPreimage F γ (hF.memLp γ hγ) : ℝ → ℂ) x := by
    intro γ hγ
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Complex.real_smul]
    push_cast
    ring
  have hgcsupp : HasCompactSupport fun t : ℝ => ((g t : ℝ) : ℂ) := by
    have h := hsupp.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)
    simpa [Function.comp_def] using h
  rw [hconv α hα, hconv β hβ, integral_test_hardyPreimage hF hα hg hsupp,
    integral_test_hardyPreimage hF hβ hg hsupp,
    integral_hardyMulTest_line_indep hF
      (ψ := fun t : ℝ => ((g t : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp hg) hgcsupp hα hβ]

end

end GaloisForLFunctions.HTGeometry
