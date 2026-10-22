import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseWeilBridge
import GaloisForLFunctions.RHTower.CCM.CCMPolarPrimeStieltjesAutocorrelation
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFriedrichsOperator
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewOperatorEquationTwoFive

/-!
# Exact Suzuki--CCM source-form bridge

Suzuki's restricted Weil form and Connes--Consani--Moscovici's Friedrichs form use the same
compact autocorrelation source, but the literature presents their archimedean terms in different
coordinates.  This module constructs that source on Suzuki's literal real smooth core and proves
the normalization-sensitive phase--Weil identity.  In particular, the factor `2π`, the sign of
the archimedean distribution, and compact support of the autocorrelation are all theorems rather
than conventions hidden in an abstract form hypothesis.

All declarations are unconditional on the intrinsic Suzuki source core.
-/

open Complex MeasureTheory Set
open scoped FourierTransform SchwartzMap

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

/-- Suzuki's real compact smooth source, regarded as a complex Schwartz function. -/
def suzukiRestrictedWeilCoreSchwartz {a : ℝ}
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    SchwartzMap ℝ ℂ :=
  suzukiComplexTestSchwartz (fun x => (u x : ℂ))
    (suzukiRestrictedWeilCore_contDiff_ofReal u)
    (suzukiRestrictedWeilCore_hasCompactSupport_ofReal u)

@[simp] theorem suzukiRestrictedWeilCoreSchwartz_apply {a : ℝ}
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) (x : ℝ) :
    suzukiRestrictedWeilCoreSchwartz u x = (u x : ℂ) := by
  rfl

theorem suzukiRestrictedWeilCore_tsupport_subset_aperture
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    tsupport (u : ℝ → ℝ) ⊆ Ioo (-a.1) a.1 := by
  intro x hx
  have hxr := GaloisForLFunctions.RHTower.core_tsupport_subset_radius u hx
  constructor <;> linarith [hxr.1, hxr.2, u.supportRadius_lt_aperture]

/-- Canonical exact CCM form-domain realization of Suzuki's real smooth source. -/
def suzukiRestrictedWeilCoreCCMFormVector
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    CCMArchimedeanFormDomain a :=
  Classical.choose (exists_ccmArchimedeanFormDomain_eq_smoothRealTest
    a u u.smooth u.hasCompactSupport
      (suzukiRestrictedWeilCore_tsupport_subset_aperture a u))

theorem ccmArchimedeanFormEmbedding_suzukiRestrictedWeilCoreCCMFormVector
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    ccmArchimedeanFormEmbedding a
        (suzukiRestrictedWeilCoreCCMFormVector a u) =
      suzukiRealTestL2 u u.smooth u.hasCompactSupport :=
  Classical.choose_spec (exists_ccmArchimedeanFormDomain_eq_smoothRealTest
    a u u.smooth u.hasCompactSupport
      (suzukiRestrictedWeilCore_tsupport_subset_aperture a u))

/-- The physical representative of the canonical CCM vector is Suzuki's source almost
everywhere on the full line. -/
theorem ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    ((ccmArchimedeanFormToAperture a
      (suzukiRestrictedWeilCoreCCMFormVector a u) : SoninL2) : ℝ → ℂ)
        =ᵐ[volume] fun x => (u x : ℂ) := by
  rw [ccmArchimedeanFormToAperture_coe,
    ccmArchimedeanFormEmbedding_suzukiRestrictedWeilCoreCCMFormVector]
  change ((suzukiRealTestL2 u u.smooth u.hasCompactSupport : SoninL2) : ℝ → ℂ)
    =ᵐ[volume] suzukiRealTestComplex u
  exact suzukiRealTestL2_coeFn u u.smooth u.hasCompactSupport

theorem suzukiRestrictedWeilCoreSchwartz_eq_realTestSchwartz
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    suzukiRestrictedWeilCoreSchwartz u =
      suzukiRealTestSchwartz u u.smooth u.hasCompactSupport := by
  ext x
  rfl

/-- The Fourier coordinate stored in the canonical CCM form vector is the classical Fourier
transform of Suzuki's source almost everywhere. -/
theorem suzukiRestrictedWeilCoreCCMFormVector_coeFn
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    ((suzukiRestrictedWeilCoreCCMFormVector a u).1 : ℝ → ℂ) =ᵐ[volume]
      𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) := by
  let q := suzukiRestrictedWeilCoreCCMFormVector a u
  let U := suzukiRestrictedWeilCoreSchwartz u
  have hphysical :=
    ccmArchimedeanFormEmbedding_suzukiRestrictedWeilCoreCCMFormVector a u
  have hweighted : ccmArchimedeanWeightedToL2 q.1 =
      (𝓕 U : SchwartzMap ℝ ℂ).toLp 2 volume := by
    calc
      ccmArchimedeanWeightedToL2 q.1 =
          fourierUnitary (ccmArchimedeanFormEmbedding a q) :=
        (fourierUnitary_ccmArchimedeanFourierToTime q.1).symm
      _ = fourierUnitary (suzukiRealTestL2 u u.smooth u.hasCompactSupport) := by
        rw [hphysical]
      _ = fourierUnitary (U.toLp 2 volume) := by
        unfold U suzukiRealTestL2
        rw [suzukiRestrictedWeilCoreSchwartz_eq_realTestSchwartz]
      _ = (𝓕 U : SchwartzMap ℝ ℂ).toLp 2 volume :=
        SchwartzMap.toLp_fourier_eq U
  have hw := ccmArchimedeanWeightedToL2_coeFn q.1
  rw [hweighted] at hw
  exact hw.symm.trans ((𝓕 U : SchwartzMap ℝ ℂ).coeFn_toLp 2 volume)

/-- Every logarithmic translation matrix coefficient of the canonical CCM source vector is the
literal Suzuki aperture autocorrelation at that lag. -/
theorem inner_logTranslationCLM_suzukiRestrictedWeilCoreCCMFormVector
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) (h : ℝ) :
    inner ℂ
        (logTranslationCLM h
          (ccmArchimedeanFormToAperture a
            (suzukiRestrictedWeilCoreCCMFormVector a u)).1)
        (ccmArchimedeanFormToAperture a
          (suzukiRestrictedWeilCoreCCMFormVector a u)).1 =
      apertureAutocorrelation (fun x => (u x : ℂ)) h := by
  let f : SoninL2 := (ccmArchimedeanFormToAperture a
    (suzukiRestrictedWeilCoreCCMFormVector a u)).1
  have hf : (f : ℝ → ℂ) =ᵐ[volume] fun x => (u x : ℂ) :=
    ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a u
  have hfshift := hf.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have htrans := Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving h)
  rw [MeasureTheory.L2.inner_def]
  unfold apertureAutocorrelation
  apply integral_congr_ae
  filter_upwards [htrans, hf, hfshift] with x htx hx hxs
  change inner ℂ ((logTranslationCLM h f : SoninL2) x) (f x) = _
  change inner ℂ
      (Lp.compMeasurePreserving (MellinL2.realTranslationEquiv h)
        (MellinL2.realTranslation_measurePreserving h) f x) (f x) = _
  rw [htx, hx, hxs]
  simp [RCLike.inner_apply, MellinL2.realTranslationEquiv,
    Function.comp_apply, mul_comm]

/-- The critical-Mellin atom and Suzuki's prime-pair coefficient are the same normalization. -/
theorem criticalMellinAtomWeight_eq_primePairWeight
    {n : ℕ} (hn : 0 < n) :
    criticalMellinAtomWeight n =
      GaloisForLFunctions.HTGeometry.primePairWeight n := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  unfold criticalMellinAtomWeight
    GaloisForLFunctions.HTGeometry.primePairWeight
  have hexp : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
  rw [hexp, Real.rpow_neg hn0, Real.sqrt_eq_rpow, div_eq_mul_inv]
  ring

/-- Compact Schwartz autocorrelation attached to Suzuki's source core.  The explicit radius
`2r+2` is deliberately strict; the actual support is contained in `[-2r,2r]`. -/
def suzukiRestrictedWeilCoreAutocorrelationTest {a : ℝ}
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    CCMCompactSchwartzLogTest where
  toSchwartzMap :=
    SchwartzMap.autocorrelationSchwartz (suzukiRestrictedWeilCoreSchwartz u)
  radius := 2 * u.supportRadius + 2
  one_lt_radius := by linarith [u.supportRadius_nonneg]
  eq_zero_of_radius_le_abs := by
    intro x hx
    rw [SchwartzMap.autocorrelationSchwartz_apply]
    unfold SchwartzMap.autocorrelation
    rw [convolution_def]
    apply integral_eq_zero_of_ae
    filter_upwards with y
    simp only [Pi.zero_apply, SchwartzMap.conjugateReflection, neg_sub]
    by_cases hy : u y = 0
    · simp [suzukiRestrictedWeilCoreSchwartz_apply, hy]
    by_cases hyx : u (y - x) = 0
    · simp [suzukiRestrictedWeilCoreSchwartz_apply, hyx]
    have hyr : y ∈ Icc (-u.supportRadius) u.supportRadius :=
      u.support_subset hy
    have hyxr : y - x ∈ Icc (-u.supportRadius) u.supportRadius :=
      u.support_subset hyx
    have habsy : |y| ≤ u.supportRadius := (abs_le).2 hyr
    have habsyx : |y - x| ≤ u.supportRadius := (abs_le).2 hyxr
    have htri : |x| ≤ |y| + |y - x| := by
      calc
        |x| = |y - (y - x)| := by ring_nf
        _ ≤ |y| + |y - x| := abs_sub y (y - x)
    exfalso
    linarith

/-- Fourier transform of Suzuki's compact autocorrelation is the exact spectral density
`|Fourier u|²`. -/
@[simp] theorem fourier_suzukiRestrictedWeilCoreAutocorrelationTest {a : ℝ}
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) (ξ : ℝ) :
    𝓕 ((suzukiRestrictedWeilCoreAutocorrelationTest u).toSchwartzMap : ℝ → ℂ) ξ =
      ((‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := by
  change 𝓕 (SchwartzMap.autocorrelationSchwartz
      (suzukiRestrictedWeilCoreSchwartz u) : ℝ → ℂ) ξ = _
  rw [← SchwartzMap.fourier_coe,
    SchwartzMap.fourier_autocorrelationSchwartz,
    Complex.mul_conj, Complex.normSq_eq_norm_sq,
    SchwartzMap.fourier_coe]

/-- The bundled Schwartz autocorrelation is the literal aperture autocorrelation used in the
polar--prime Stieltjes source. -/
theorem suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_apertureAutocorrelation
    {a h : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    suzukiRestrictedWeilCoreAutocorrelationTest u h =
      apertureAutocorrelation (fun x => (u x : ℂ)) h := by
  change SchwartzMap.autocorrelationSchwartz
      (suzukiRestrictedWeilCoreSchwartz u) h = _
  rw [SchwartzMap.autocorrelationSchwartz_apply]
  unfold SchwartzMap.autocorrelation apertureAutocorrelation
  rw [convolution_def]
  simp only [SchwartzMap.conjugateReflection, neg_sub,
    suzukiRestrictedWeilCoreSchwartz_apply]
  change (∫ y : ℝ, (u y : ℂ) * (starRingEnd ℂ) (u (y - h) : ℂ)) = _
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun y : ℝ => (u y : ℂ) * (starRingEnd ℂ) (u (y - h) : ℂ)) h
  simpa only [add_sub_cancel_right] using hshift.symm

/-- On the real core, the complex aperture autocorrelation is exactly Suzuki's real screw
cross-correlation. -/
theorem apertureAutocorrelation_suzukiRestrictedWeilCore_eq
    {a h : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    apertureAutocorrelation (fun x => (u x : ℂ)) h =
      (GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u h : ℂ) := by
  unfold apertureAutocorrelation
    GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation
    GaloisForLFunctions.RHTower.screwCrossCorr
  calc
    (∫ x : ℝ, (u (x + h) : ℂ) * (starRingEnd ℂ) (u x : ℂ)) =
        ∫ x : ℝ, ((u x * u (h + x) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Complex.conj_ofReal]
      push_cast
      ring
    _ = ((∫ x : ℝ, u x * u (h + x) : ℝ) : ℂ) := integral_ofReal

theorem apertureAutocorrelation_suzukiRestrictedWeilCore_neg
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) (h : ℝ) :
    apertureAutocorrelation (fun x => (u x : ℂ)) (-h) =
      apertureAutocorrelation (fun x => (u x : ℂ)) h := by
  rw [apertureAutocorrelation_suzukiRestrictedWeilCore_eq,
    apertureAutocorrelation_suzukiRestrictedWeilCore_eq,
    GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation_neg]

/-- The finite-prime matrix-coefficient block in the CCM source formula is twice the atomic
autocorrelation carrier, with exactly Suzuki's visible index set. -/
theorem ccmFinitePrimeSource_suzukiRestrictedWeilCore_eq
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n)
              (ccmArchimedeanFormToAperture a
                (suzukiRestrictedWeilCoreCCMFormVector a u)).1)
              (ccmArchimedeanFormToAperture a
                (suzukiRestrictedWeilCoreCCMFormVector a u)).1 +
            inner ℂ (logTranslationCLM (-Real.log n)
              (ccmArchimedeanFormToAperture a
                (suzukiRestrictedWeilCoreCCMFormVector a u)).1)
              (ccmArchimedeanFormToAperture a
                (suzukiRestrictedWeilCoreCCMFormVector a u)).1).re) =
      2 * ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        criticalMellinAtomWeight n *
          (apertureAutocorrelation (fun x => (u x : ℂ)) (Real.log n)).re := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [inner_logTranslationCLM_suzukiRestrictedWeilCoreCCMFormVector,
    inner_logTranslationCLM_suzukiRestrictedWeilCoreCCMFormVector,
    apertureAutocorrelation_suzukiRestrictedWeilCore_neg]
  have hnpos : 0 < n := by
    have hnmem := Finset.mem_Icc.mp hn
    omega
  rw [criticalMellinAtomWeight_eq_primePairWeight hnpos]
  unfold GaloisForLFunctions.HTGeometry.primePairWeight
  simp
  ring

/-- Each polar Riesz coefficient of the canonical CCM source vector is the literal exponential
moment of Suzuki's source. -/
theorem inner_ccmPolarApertureVector_suzukiRestrictedWeilCoreCCMFormVector
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a
          (suzukiRestrictedWeilCoreCCMFormVector a u)) =
      ∫ x : ℝ, (Real.exp (s * x) : ℂ) * (u x : ℂ) := by
  let f : SoninL2 := (ccmArchimedeanFormToAperture a
    (suzukiRestrictedWeilCoreCCMFormVector a u)).1
  have hf : (f : ℝ → ℂ) =ᵐ[volume] fun x => (u x : ℂ) :=
    ccmArchimedeanFormToAperture_suzukiRestrictedWeilCoreCCMFormVector_coeFn a u
  have hp := ccmPolarL2Vector_coeFn a s
  change inner ℂ (ccmPolarL2Vector a s) f = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hp, hf] with x hpx hfx
  change inner ℂ ((ccmPolarApertureVector a s : suzukiApertureHilbert a).1 x)
      ((ccmArchimedeanFormToAperture a
        (suzukiRestrictedWeilCoreCCMFormVector a u) :
          suzukiApertureHilbert a).1 x) = _
  change inner ℂ (ccmPolarL2Vector a s x) (f x) = _
  rw [hpx, hfx]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx]
    simp [ccmPolarProfile, RCLike.inner_apply]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.conj_ofReal]
    ring
  · rw [indicator_of_notMem hx]
    have hux : u x = 0 := by
      apply Function.notMem_support.mp
      intro hmem
      apply hx
      exact Ioo_subset_Icc_self (u.support_subset_aperture hmem)
    simp [hux]

/-- Exponentially weighted autocorrelation factors into Suzuki's two polar moments. -/
theorem integral_exp_half_mul_suzukiCoreAutocorrelation
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    (∫ h : ℝ, Real.exp (h / 2) *
        GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u h) =
      (∫ x : ℝ, Real.exp (x / 2) * u x) *
        ∫ x : ℝ, Real.exp (-(x / 2)) * u x := by
  let f : ℝ → ℝ := fun x => Real.exp (x / 2) * u x
  let g : ℝ → ℝ := fun x => Real.exp (x / 2) * u (-x)
  have hfcont : Continuous f := by
    dsimp only [f]
    exact (Real.continuous_exp.comp (continuous_id.div_const 2)).mul u.continuous
  have hgcont : Continuous g := by
    dsimp only [g]
    exact (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
      (u.continuous.comp continuous_neg)
  have hfsupp : HasCompactSupport f := u.hasCompactSupport.mul_left
  have hgsupp : HasCompactSupport g :=
    (u.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)).mul_left
  have hfint : Integrable f := hfcont.integrable_of_hasCompactSupport hfsupp
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hgsupp
  have hconv := MeasureTheory.integral_convolution
    (ContinuousLinearMap.mul ℝ ℝ) hfint hgint
  have hpoint : ∀ h : ℝ,
      convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume h =
        Real.exp (h / 2) *
          GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u h := by
    intro h
    calc
      convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume h =
          Real.exp (h / 2) *
            GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u (-h) := by
        rw [convolution_def]
        change (∫ y : ℝ, f y * g (h - y)) = _
        unfold f g GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation
          GaloisForLFunctions.RHTower.screwCrossCorr
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        rw [show -(h - y) = -h + y by ring,
          show h / 2 = y / 2 + (h - y) / 2 by ring, Real.exp_add]
        ring
      _ = _ := by
        rw [GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation_neg]
  have hg : (∫ x : ℝ, g x) =
      ∫ x : ℝ, Real.exp (-(x / 2)) * u x := by
    calc
      (∫ x : ℝ, g x) = ∫ x : ℝ, g (-x) :=
        (MeasureTheory.integral_neg_eq_self (μ := volume) g).symm
      _ = ∫ x : ℝ, Real.exp (-(x / 2)) * u x := by
        apply integral_congr_ae
        filter_upwards with x
        unfold g
        congr 2 <;> ring
  calc
    (∫ h : ℝ, Real.exp (h / 2) *
        GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u h) =
        ∫ h : ℝ, convolution f g (ContinuousLinearMap.mul ℝ ℝ) volume h := by
      apply integral_congr_ae
      filter_upwards with h
      exact (hpoint h).symm
    _ = (∫ x : ℝ, f x) * ∫ x : ℝ, g x := by
      simpa using hconv
    _ = _ := by
      rw [hg]

/-- Suzuki's real core autocorrelation is continuous on the whole line. -/
theorem continuous_suzukiCoreAutocorrelation_bridge
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    Continuous (GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u) := by
  rw [continuous_iff_continuousAt]
  intro h
  exact (GaloisForLFunctions.RHTower.hasDerivAt_suzukiCoreAutocorrelation u h).continuousAt

/-- Suzuki's autocorrelation has its sharp elementary support bound `[-2r,2r]`. -/
theorem hasCompactSupport_suzukiCoreAutocorrelation
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    HasCompactSupport
      (GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-(2 * u.supportRadius)) (2 * u.supportRadius)) isCompact_Icc ?_
  intro h hh
  show -(2 * u.supportRadius) ≤ h ∧ h ≤ 2 * u.supportRadius
  constructor
  · by_contra hleft
    exact hh (GaloisForLFunctions.RHTower.screwCrossCorr_eq_zero_of_support_radius_neg
      u.support_subset u.support_subset (by linarith))
  · by_contra hright
    exact hh (GaloisForLFunctions.RHTower.screwCrossCorr_eq_zero_of_support_radius_pos
      u.support_subset u.support_subset (by linarith))

/-- The whole-line half-density autocorrelation moment is exactly its finite positive-aperture
hyperbolic moment.  Strict interior support is what removes every endpoint and tail term. -/
theorem integral_exp_half_mul_suzukiCoreAutocorrelation_eq_Ioc_cosh
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    (∫ h : ℝ, Real.exp (h / 2) *
        GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u h) =
      ∫ h in Ioc (0 : ℝ) (2 * a.1),
        2 * Real.cosh (h / 2) *
          GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u h := by
  let c : ℝ → ℝ := GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u
  let f : ℝ → ℝ := fun h => Real.exp (h / 2) * c h
  have hccont : Continuous c := continuous_suzukiCoreAutocorrelation_bridge u
  have hccompact : HasCompactSupport c :=
    hasCompactSupport_suzukiCoreAutocorrelation u
  have hfcont : Continuous f := by
    dsimp only [f]
    exact (Real.continuous_exp.comp (continuous_id.div_const 2)).mul hccont
  have hfcompact : HasCompactSupport f := hccompact.mul_left
  have hfint : Integrable f := hfcont.integrable_of_hasCompactSupport hfcompact
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := (0 : ℝ)) hfint.integrableOn hfint.integrableOn
  have hreflect := integral_comp_neg_Ioi (0 : ℝ) f
  simp only [neg_zero] at hreflect
  have hfneg : Integrable (fun h => f (-h)) := hfint.comp_neg
  have hwhole : (∫ h : ℝ, f h) =
      ∫ h in Ioi (0 : ℝ),
        2 * Real.cosh (h / 2) * c h := by
    calc
      (∫ h : ℝ, f h) =
          (∫ h in Iic (0 : ℝ), f h) + ∫ h in Ioi (0 : ℝ), f h := hsplit.symm
      _ = (∫ h in Ioi (0 : ℝ), f (-h)) + ∫ h in Ioi (0 : ℝ), f h := by
        rw [hreflect]
      _ = ∫ h in Ioi (0 : ℝ), f (-h) + f h := by
        rw [integral_add hfneg.integrableOn hfint.integrableOn]
      _ = ∫ h in Ioi (0 : ℝ), 2 * Real.cosh (h / 2) * c h := by
        apply integral_congr_ae
        filter_upwards with h
        dsimp only [f, c]
        rw [GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation_neg,
          Real.cosh_eq]
        ring_nf
  have htruncate :
      (∫ h in Ioi (0 : ℝ), 2 * Real.cosh (h / 2) * c h) =
        ∫ h in Ioc (0 : ℝ) (2 * a.1), 2 * Real.cosh (h / 2) * c h := by
    rw [← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with h
    by_cases hshort : h ∈ Ioc (0 : ℝ) (2 * a.1)
    · rw [indicator_of_mem hshort,
        indicator_of_mem (show h ∈ Ioi (0 : ℝ) from hshort.1)]
    · rw [indicator_of_notMem hshort]
      by_cases hpos : h ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hpos]
        have hlarge : 2 * u.supportRadius < h := by
          have htop : 2 * a.1 < h := by
            simp only [mem_Ioc, not_and_or, not_lt, not_le] at hshort
            rcases hshort with hnonpos | htop
            · exact False.elim ((not_lt_of_ge hnonpos) hpos)
            · exact htop
          linarith [u.supportRadius_lt_aperture]
        rw [show c h = 0 by
          exact GaloisForLFunctions.RHTower.screwCrossCorr_eq_zero_of_support_radius_pos
            u.support_subset u.support_subset hlarge]
        ring
      · rw [indicator_of_notMem hpos]
  dsimp only [f, c] at hwhole htruncate ⊢
  rw [hwhole, htruncate]

/-- A literal CCM polar Riesz coefficient is the real exponential moment, embedded in `ℂ`. -/
theorem inner_ccmPolarApertureVector_suzukiRestrictedWeilCoreCCMFormVector_eq_ofReal
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a
          (suzukiRestrictedWeilCoreCCMFormVector a u)) =
      ((∫ x : ℝ, Real.exp (s * x) * u x : ℝ) : ℂ) := by
  rw [inner_ccmPolarApertureVector_suzukiRestrictedWeilCoreCCMFormVector]
  calc
    (∫ x : ℝ, (Real.exp (s * x) : ℂ) * (u x : ℂ)) =
        ∫ x : ℝ, ((Real.exp (s * x) * u x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      push_cast
      ring
    _ = ((∫ x : ℝ, Real.exp (s * x) * u x : ℝ) : ℂ) := integral_ofReal

/-- The two literal CCM polar matrix coefficients give exactly the positive-lag hyperbolic
autocorrelation carrier on Suzuki's source core. -/
theorem ccmPolarSource_suzukiRestrictedWeilCore_eq
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    let q := suzukiRestrictedWeilCoreCCMFormVector a u
    let f := ccmArchimedeanFormToAperture a q
    ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (1 / 2)) f +
        (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (-1 / 2)) f).re =
      2 * ∫ h in Ioc (0 : ℝ) (2 * a.1),
        2 * Real.cosh (h / 2) *
          GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u h := by
  dsimp only
  rw [inner_ccmPolarApertureVector_suzukiRestrictedWeilCoreCCMFormVector_eq_ofReal,
    inner_ccmPolarApertureVector_suzukiRestrictedWeilCoreCCMFormVector_eq_ofReal]
  have hfactor := integral_exp_half_mul_suzukiCoreAutocorrelation u
  have hhalf := integral_exp_half_mul_suzukiCoreAutocorrelation_eq_Ioc_cosh a u
  let Mneg : ℝ := ∫ x : ℝ, Real.exp ((-1 / 2 : ℝ) * x) * u x
  let Mpos : ℝ := ∫ x : ℝ, Real.exp ((1 / 2 : ℝ) * x) * u x
  simp only [Complex.conj_ofReal]
  change (((Mneg : ℂ) * (Mpos : ℂ) + (Mpos : ℂ) * (Mneg : ℂ))).re = _
  have hreal : (((Mneg : ℂ) * (Mpos : ℂ) +
      (Mpos : ℂ) * (Mneg : ℂ))).re = 2 * Mneg * Mpos := by
    simp [Complex.mul_re]
    ring
  rw [hreal]
  have hMneg : Mneg = ∫ x : ℝ, Real.exp (-(x / 2)) * u x := by
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    ring
  have hMpos : Mpos = ∫ x : ℝ, Real.exp (x / 2) * u x := by
    apply integral_congr_ae
    filter_upwards with x
    congr 2
    ring
  rw [hMneg, hMpos]
  calc
    2 * (∫ x : ℝ, Real.exp (-(x / 2)) * u x) *
        (∫ x : ℝ, Real.exp (x / 2) * u x) =
      2 * ((∫ x : ℝ, Real.exp (x / 2) * u x) *
        ∫ x : ℝ, Real.exp (-(x / 2)) * u x) := by ring
    _ = 2 * (∫ h : ℝ, Real.exp (h / 2) *
        GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u h) := by rw [hfactor]
    _ = _ := by rw [hhalf]

/-- The literal polar term minus the literal finite-prime matrix-coefficient term in CCM's source
formula is exactly the signed critical-Mellin autocorrelation quadratic. -/
theorem ccmPolarPrimeSource_suzukiRestrictedWeilCore_eq
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    let q := suzukiRestrictedWeilCoreCCMFormVector a u
    let f := ccmArchimedeanFormToAperture a q
    ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (1 / 2)) f +
        (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (-1 / 2)) f).re -
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
            inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re =
      polarPrimeAutocorrelationQuadratic a.1 (fun x => (u x : ℂ)) := by
  dsimp only
  have hcont : Continuous (fun h : ℝ =>
      apertureAutocorrelation (fun x => (u x : ℂ)) h *
        (2 * Real.cosh (h / 2) : ℂ)) := by
    have hcorr : apertureAutocorrelation (fun x => (u x : ℂ)) =
        suzukiRestrictedWeilCoreAutocorrelationTest u := by
      funext h
      exact (suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_apertureAutocorrelation
        u).symm
    rw [hcorr]
    exact (suzukiRestrictedWeilCoreAutocorrelationTest u).toSchwartzMap.continuous.mul
      (by fun_prop)
  have hint : Integrable
      (fun h => apertureAutocorrelation (fun x => (u x : ℂ)) h *
        (2 * Real.cosh (h / 2) : ℂ))
      (volume.restrict (Ioc (0 : ℝ) (2 * a.1))) :=
    hcont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [ccmPolarSource_suzukiRestrictedWeilCore_eq,
    ccmFinitePrimeSource_suzukiRestrictedWeilCore_eq,
    polarPrimeAutocorrelationQuadratic_eq_integral_sub_sum hint]
  have hcorrRe : ∀ h : ℝ,
      (apertureAutocorrelation (fun x => (u x : ℂ)) h).re =
        GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation u h := by
    intro h
    rw [apertureAutocorrelation_suzukiRestrictedWeilCore_eq]
    simp
  simp_rw [hcorrRe]
  congr 3
  funext h
  ring

/-- Suzuki's bundled autocorrelation is even. -/
theorem suzukiRestrictedWeilCoreAutocorrelationTest_neg
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) (h : ℝ) :
    suzukiRestrictedWeilCoreAutocorrelationTest u (-h) =
      suzukiRestrictedWeilCoreAutocorrelationTest u h := by
  rw [suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_apertureAutocorrelation,
    suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_apertureAutocorrelation,
    apertureAutocorrelation_suzukiRestrictedWeilCore_eq,
    apertureAutocorrelation_suzukiRestrictedWeilCore_eq,
    GaloisForLFunctions.RHTower.suzukiCoreAutocorrelation_neg]

/-- Suzuki's bundled autocorrelation is real-valued. -/
@[simp] theorem suzukiRestrictedWeilCoreAutocorrelationTest_im
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) (h : ℝ) :
    (suzukiRestrictedWeilCoreAutocorrelationTest u h).im = 0 := by
  rw [suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_apertureAutocorrelation,
    apertureAutocorrelation_suzukiRestrictedWeilCore_eq]
  simp

/-- The critical-Mellin Stieltjes carrier of Suzuki's real autocorrelation is itself real. -/
@[simp] theorem criticalMellinStieltjesPairing_suzukiRestrictedWeilCore_im
    {a₀ a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a₀) :
    (criticalMellinStieltjesPairing a
      (suzukiRestrictedWeilCoreAutocorrelationTest u)).im = 0 := by
  unfold criticalMellinStieltjesPairing
  rw [Complex.sub_im]
  have hint :
      (∫ h in Ioc (0 : ℝ) (2 * a),
        suzukiRestrictedWeilCoreAutocorrelationTest u h *
          (2 * Real.cosh (h / 2) : ℂ)).im = 0 := by
    have hcast :
        (∫ h in Ioc (0 : ℝ) (2 * a),
          suzukiRestrictedWeilCoreAutocorrelationTest u h *
            (2 * Real.cosh (h / 2) : ℂ)) =
          ((∫ h in Ioc (0 : ℝ) (2 * a),
            (suzukiRestrictedWeilCoreAutocorrelationTest u h).re *
              (2 * Real.cosh (h / 2)) : ℝ) : ℂ) := by
      calc
        _ = ∫ h in Ioc (0 : ℝ) (2 * a),
            (((suzukiRestrictedWeilCoreAutocorrelationTest u h).re *
              (2 * Real.cosh (h / 2)) : ℝ) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with h
          apply Complex.ext <;>
            simp [suzukiRestrictedWeilCoreAutocorrelationTest_im]
        _ = _ := integral_ofReal
    rw [hcast]
    simp
  have hsum :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (criticalMellinAtomWeight k : ℂ) *
          suzukiRestrictedWeilCoreAutocorrelationTest u (Real.log k)).im = 0 := by
    rw [Complex.im_sum]
    apply Finset.sum_eq_zero
    intro k hk
    simp [suzukiRestrictedWeilCoreAutocorrelationTest_im]
  rw [hint, hsum, sub_zero]

/-- CCM's two-sided polar--prime source is exactly the real Stieltjes autocorrelation quadratic
on Suzuki's core. -/
theorem ccmRestrictedPolarPrimeFull_suzukiRestrictedWeilCore_eq
    {a₀ a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a₀) :
    ccmRestrictedPolarPrimeFull a
        (suzukiRestrictedWeilCoreAutocorrelationTest u) =
      (polarPrimeAutocorrelationQuadratic a (fun x => (u x : ℂ)) : ℂ) := by
  let H : ℝ → ℂ := suzukiRestrictedWeilCoreAutocorrelationTest u
  let P : ℂ := criticalMellinStieltjesPairing a H
  have heven : (fun h => H h + H (-h)) = fun h => 2 * H h := by
    funext h
    rw [show H (-h) = H h by
      exact suzukiRestrictedWeilCoreAutocorrelationTest_neg u h]
    ring
  have hscale : criticalMellinStieltjesPairing a (fun h => 2 * H h) = 2 * P := by
    unfold P
    unfold criticalMellinStieltjesPairing
    have hint :
        (∫ h in Ioc (0 : ℝ) (2 * a),
          (2 * H h) * (2 * Real.cosh (h / 2) : ℂ)) =
            2 * ∫ h in Ioc (0 : ℝ) (2 * a),
              H h * (2 * Real.cosh (h / 2) : ℂ) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with h
      ring
    have hsum :
        (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
          (criticalMellinAtomWeight k : ℂ) * (2 * H (Real.log k))) =
            2 * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
              (criticalMellinAtomWeight k : ℂ) * H (Real.log k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hint, hsum]
    ring
  have hreal : P = (P.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [P, Complex.ofReal_im] using
        criticalMellinStieltjesPairing_suzukiRestrictedWeilCore_im
          (a := a) u
  have hcorr :
      apertureAutocorrelation (fun x => (u x : ℂ)) = H := by
    funext h
    exact (suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_apertureAutocorrelation
      u).symm
  rw [ccmRestrictedPolarPrimeFull_eq_sharp_evenization, heven, hscale]
  unfold polarPrimeAutocorrelationQuadratic
  rw [hcorr]
  change 2 * P = ((2 * P.re : ℝ) : ℂ)
  rw [hreal]
  simp

/-- Generic phase--Weil bridge for a compact Schwartz autocorrelation.  This is the precise
archimedean equality needed to compare the CCM source quadratic with Suzuki's source form. -/
theorem integral_two_gammaHardyPhaseRate_mul_fourier_norm_sq_eq_neg_weilDistribution
    (H : CCMCompactSchwartzLogTest) (U : SchwartzMap ℝ ℂ)
    (hFourier : ∀ ξ : ℝ,
      (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ =
        ((‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ)) :
    ((∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
        ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) =
      -ccmArchimedeanWeilDistribution H := by
  have hWeil :=
    integral_fourier_mul_logPi_sub_re_quarterDigamma_eq_weilDistribution H
  calc
    ((∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
        ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) =
        ∫ ξ : ℝ, ((2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
          ‖𝓕 (U : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := integral_ofReal.symm
    _ = -∫ ξ : ℝ,
        (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ *
          ((Real.log Real.pi -
            (Complex.digamma (ccmQuarterPiDigammaPoint ξ)).re : ℝ) : ℂ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hFourier]
      have hpoint : linePt ((2 * Real.pi) * ξ) / 2 =
          ccmQuarterPiDigammaPoint ξ := by
        unfold linePt ccmQuarterPiDigammaPoint
        push_cast
        ring
      unfold gammaHardyPhaseRate
      rw [hpoint]
      push_cast
      ring
    _ = -ccmArchimedeanWeilDistribution H := congrArg Neg.neg hWeil

/-- Exact archimedean phase identity on Suzuki's literal restricted Weil core. -/
theorem suzukiRestrictedWeilCore_phaseQuadratic_eq_neg_weilDistribution
    {a : ℝ} (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a) :
    ((∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
        ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) =
      -ccmArchimedeanWeilDistribution
        (suzukiRestrictedWeilCoreAutocorrelationTest u) := by
  exact integral_two_gammaHardyPhaseRate_mul_fourier_norm_sq_eq_neg_weilDistribution
    (suzukiRestrictedWeilCoreAutocorrelationTest u)
    (suzukiRestrictedWeilCoreSchwartz u)
    (fourier_suzukiRestrictedWeilCoreAutocorrelationTest u)

/-- The literal phase term occurring inside `ccmRestrictedWeilSourceQuadratic`, evaluated on the
canonical Suzuki source vector, is the negative global archimedean Weil distribution. -/
theorem suzukiRestrictedWeilCoreCCMFormVector_phaseQuadratic_eq_neg_weilDistribution
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    ((∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
        ‖((suzukiRestrictedWeilCoreCCMFormVector a u).1 : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) =
      -ccmArchimedeanWeilDistribution
        (suzukiRestrictedWeilCoreAutocorrelationTest u) := by
  have hcoord := suzukiRestrictedWeilCoreCCMFormVector_coeFn a u
  calc
    ((∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
        ‖((suzukiRestrictedWeilCoreCCMFormVector a u).1 : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) =
        ((∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
          ‖𝓕 (suzukiRestrictedWeilCoreSchwartz u : ℝ → ℂ) ξ‖ ^ 2 : ℝ) : ℂ) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hcoord] with ξ hξ
      rw [hξ]
    _ = -ccmArchimedeanWeilDistribution
        (suzukiRestrictedWeilCoreAutocorrelationTest u) :=
      suzukiRestrictedWeilCore_phaseQuadratic_eq_neg_weilDistribution u

/-- Exact source-coordinate decomposition of CCM's restricted Weil quadratic on Suzuki's
canonical core vector: finite polar--prime carrier minus the global archimedean Weil
distribution. -/
theorem ccmRestrictedWeilSourceQuadratic_suzukiRestrictedWeilCore_eq
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    ccmRestrictedWeilSourceQuadratic a
        (suzukiRestrictedWeilCoreCCMFormVector a u) =
      polarPrimeAutocorrelationQuadratic a.1 (fun x => (u x : ℂ)) -
        (ccmArchimedeanWeilDistribution
          (suzukiRestrictedWeilCoreAutocorrelationTest u)).re := by
  have hphaseC :=
    suzukiRestrictedWeilCoreCCMFormVector_phaseQuadratic_eq_neg_weilDistribution a u
  have hphase :
      (∫ ξ : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * ξ) *
          ‖((suzukiRestrictedWeilCoreCCMFormVector a u).1 : ℝ → ℂ) ξ‖ ^ 2 : ℝ) =
        -(ccmArchimedeanWeilDistribution
          (suzukiRestrictedWeilCoreAutocorrelationTest u)).re := by
    have hre := congrArg Complex.re hphaseC
    simpa using hre
  have hpolarPrime := ccmPolarPrimeSource_suzukiRestrictedWeilCore_eq a u
  unfold ccmRestrictedWeilSourceQuadratic
  dsimp only
  rw [hphase]
  linarith only [hpolarPrime]

/-- Complex form of the exact CCM source decomposition.  Reality of the archimedean
distribution is derived from the real phase integral, not assumed. -/
theorem ccmRestrictedWeilSourceQuadratic_suzukiRestrictedWeilCore_eq_complex
    (a : SuzukiPositiveAperture)
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1) :
    (ccmRestrictedWeilSourceQuadratic a
      (suzukiRestrictedWeilCoreCCMFormVector a u) : ℂ) =
      (polarPrimeAutocorrelationQuadratic a.1 (fun x => (u x : ℂ)) : ℂ) -
        ccmArchimedeanWeilDistribution
          (suzukiRestrictedWeilCoreAutocorrelationTest u) := by
  let W : ℂ := ccmArchimedeanWeilDistribution
    (suzukiRestrictedWeilCoreAutocorrelationTest u)
  have hphaseC :=
    suzukiRestrictedWeilCoreCCMFormVector_phaseQuadratic_eq_neg_weilDistribution a u
  have hWim : W.im = 0 := by
    have him := congrArg Complex.im hphaseC
    have hzero : 0 = W.im := by
      dsimp only [W]
      simpa using congrArg Neg.neg him
    exact hzero.symm
  have hWreal : W = (W.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [hWim]
  have hreal := ccmRestrictedWeilSourceQuadratic_suzukiRestrictedWeilCore_eq a u
  dsimp only [W] at hWreal
  rw [hreal, hWreal]
  push_cast
  simp

end RHTower
