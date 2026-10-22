import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilEvenStrictDomain
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowSpectralIdentity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMMixedScrewWeilBridge

/-!
# The completed even ground and literal heat-window sources

Reflection symmetrization preserves the pole-constrained smooth core. A negative
even ground therefore has a smooth even witness; real--imaginary splitting of
the complete source produces a real witness without losing either pole zero.

This closes the gap between the completed even form domain and HCF's real test
cone. Positive even grounds feed the sharp lower window transfer, while negative
ones feed the sharp Hermite witness at every sufficiently large degree.
-/

open Complex MeasureTheory Set Filter Topology Polynomial
open scoped InnerProduct BigOperators
noncomputable section
namespace RHTower.CCMEvenSector

def reflectedSource {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a) :
    CCMComplexSmoothInteriorSource a where
  toFun x := g (-x)
  smooth := g.smooth.comp contDiff_neg
  hasCompactSupport := g.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)
  tsupport_subset := by
    intro x hx
    have hn := g.tsupport_subset (tsupport_comp_subset_preimage (g : ℝ → ℂ) continuous_neg hx)
    change -a.1 < -x ∧ -x < a.1 at hn
    constructor <;> linarith [hn.1, hn.2]

theorem reflectedSource_vector {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a) :
    (reflectedSource g).toCCMFormVector = ccmArchimedeanFormReflection a g.toCCMFormVector := by
  apply ccmArchimedeanFormEmbedding_injective a
  change (ccmArchimedeanFormToAperture a (reflectedSource g).toCCMFormVector : SoninL2) =
    (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a g.toCCMFormVector) : SoninL2)
  rw [ccmArchimedeanFormToAperture_reflection]
  apply Lp.ext
  have hn := g.toCCMFormVector_physical_coeFn.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [(reflectedSource g).toCCMFormVector_physical_coeFn,
    l2Reflection_ae (ccmArchimedeanFormToAperture a g.toCCMFormVector : SoninL2), hn]
    with x hx hr hn
  dsimp only [Function.comp_apply] at hn
  rw [hx, hr, hn]
  rfl

def evenSmoothSource {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a) :
    CCMComplexSmoothInteriorSource a := g.combo g (reflectedSource g) (-1 / 2) (1 / 2)

theorem evenSmoothSource_even {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a)
    (x : ℝ) : evenSmoothSource g (-x) = evenSmoothSource g x := by
  simp only [evenSmoothSource, CCMComplexSmoothInteriorSource.combo_apply, reflectedSource, neg_neg]
  ring

theorem evenSmoothSource_vector {a : SuzukiPositiveAperture} (g : CCMComplexSmoothInteriorSource a) :
    (evenSmoothSource g).toCCMFormVector = ccmRestrictedWeilEvenPart a g.toCCMFormVector := by
  rw [evenSmoothSource, CCMComplexSmoothInteriorSource.combo_toCCMFormVector, reflectedSource_vector,
    ccmRestrictedWeilEvenPart]
  module

/-- A negative even ground has an even smooth strict-interior witness with both poles removed. -/
theorem exists_even_smooth_negative {a : SuzukiPositiveAperture} (hneg : evenGroundEnergy a < 0) :
    ∃ g : CCMComplexSmoothInteriorSource a, (∀ x, g (-x) = g x) ∧
      IsPolarConstrained a g.toCCMFormVector ∧ ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector < 0 := by
  obtain ⟨u, hp, he, hn, hQ⟩ := exists_evenGround a
  have heu : ccmRestrictedWeilEvenPart a u = u := by
    unfold ccmRestrictedWeilEvenPart
    rw [he]
    module
  have hc : Continuous (fun v : CCMArchimedeanFormDomain a =>
      ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilEvenPart a v)) := by
    apply (continuous_ccmRestrictedWeilSourceQuadratic a).comp
    exact (continuous_id.add (ccmArchimedeanFormReflection a).continuous).const_smul (2 : ℂ)⁻¹
  have hU : ∀ᶠ v : CCMArchimedeanFormDomain a in 𝓝 u,
      ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilEvenPart a v) < 0 :=
    hc.continuousAt.eventually (Iio_mem_nhds (by
      change ccmRestrictedWeilSourceQuadratic a (ccmRestrictedWeilEvenPart a u) < 0
      rw [heu, hQ]
      exact hneg))
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hU
  obtain ⟨g, hgp, hdist⟩ := exists_polarConstrained_smooth_close a u hp hδ
  refine ⟨evenSmoothSource g, evenSmoothSource_even g, ?_, ?_⟩
  · rw [evenSmoothSource_vector]
    exact hgp.evenPart
  · rw [evenSmoothSource_vector]
    exact hnear (by simpa only [dist_eq_norm] using hdist)

private theorem smooth_realImag_energy (a : SuzukiPositiveAperture)
    (g : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a g.toCCMFormVector =
      ccmRestrictedWeilSourceQuadratic a (suzukiRestrictedWeilCoreCCMFormVector a g.realCore) +
      ccmRestrictedWeilSourceQuadratic a (suzukiRestrictedWeilCoreCCMFormVector a g.imagCore) := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source, g.toCCMFormVector_eq_real_add_I_imag,
    ccmRestrictedWeilForm_realImag_expansion]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    zero_mul, one_mul, ccmRestrictedWeilForm_realCore_mixed_im_eq_zero,
    ccmRestrictedWeilForm_self_re_eq_source, sub_zero, add_zero]

private theorem smooth_pole_realImag {a : SuzukiPositiveAperture}
    (g : CCMComplexSmoothInteriorSource a) (hp : IsPolarConstrained a g.toCCMFormVector) :
    (∫ x, g.realCore x * Real.exp (x / 2) = 0) ∧
      (∫ x, g.imagCore x * Real.exp (x / 2) = 0) := by
  have hi : Integrable (fun x : ℝ => (Real.exp ((1 / 2) * x) : ℂ) * g x) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).mul g.continuous).integrable_of_hasCompactSupport
      g.hasCompactSupport.mul_left
  have hz := hp.1
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector] at hz
  constructor
  · calc
      (∫ x, g.realCore x * Real.exp (x / 2)) =
          ∫ x, ((Real.exp ((1 / 2) * x) : ℂ) * g x).re := by
        apply integral_congr_ae
        filter_upwards with x
        rw [show x / 2 = (1 / 2) * x by ring]
        simp only [CCMComplexSmoothInteriorSource.realCore_apply, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_comm]
      _ = (∫ x, (Real.exp ((1 / 2) * x) : ℂ) * g x).re := integral_re hi
      _ = 0 := congrArg Complex.re hz
  · calc
      (∫ x, g.imagCore x * Real.exp (x / 2)) =
          ∫ x, ((Real.exp ((1 / 2) * x) : ℂ) * g x).im := by
        apply integral_congr_ae
        filter_upwards with x
        rw [show x / 2 = (1 / 2) * x by ring]
        simp only [CCMComplexSmoothInteriorSource.imagCore_apply, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, mul_comm]
      _ = (∫ x, (Real.exp ((1 / 2) * x) : ℂ) * g x).im := integral_im hi
      _ = 0 := congrArg Complex.im hz

/-- Negative energy in the completed even sector is detected by a literal real smooth source. -/
theorem exists_real_even_negative_of_ground_neg {a : SuzukiPositiveAperture}
    (hneg : evenGroundEnergy a < 0) : ¬ EvenPoleWeilNonneg a.1 := by
  obtain ⟨g, he, hp, hQ⟩ := exists_even_smooth_negative hneg
  have hsplit := smooth_realImag_energy a g
  obtain ⟨hr, hi⟩ := smooth_pole_realImag g hp
  have hcomponent : ∃ r : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore a.1,
      (∀ x, r (-x) = r x) ∧ (∫ x, r x * Real.exp (x / 2) = 0) ∧
        ccmRestrictedWeilSourceQuadratic a (suzukiRestrictedWeilCoreCCMFormVector a r) < 0 := by
    by_cases hreal : ccmRestrictedWeilSourceQuadratic a
        (suzukiRestrictedWeilCoreCCMFormVector a g.realCore) < 0
    · exact ⟨g.realCore, fun x => congrArg Complex.re (he x), hr, hreal⟩
    · exact ⟨g.imagCore, fun x => congrArg Complex.im (he x), hi, by linarith⟩
  obtain ⟨r, hre, hrp, hrQ⟩ := hcomponent
  intro hpos
  have hs : tsupport (r : ℝ → ℝ) ⊆ Ioo (-a.1) a.1 := by
    exact (closure_minimal r.support_subset isClosed_Icc).trans
      (fun x hx => ⟨by linarith [hx.1, r.supportRadius_lt_aperture],
        by linarith [hx.2, r.supportRadius_lt_aperture]⟩)
  have hv : (realEvenSource a r r.smooth r.hasCompactSupport hs).toCCMFormVector =
      suzukiRestrictedWeilCoreCCMFormVector a r := by
    exact ccmComplexSmoothInteriorSourceOfRealCore_toCCMFormVector a r
  have hz := hpos r r.smooth r.hasCompactSupport (fun x hx => by
    by_contra hne
    have hmem := r.support_subset_aperture hne
    have hlt : |x| < a.1 := abs_lt.mpr hmem
    linarith) hre hrp
  rw [← ccmRestrictedWeilSourceQuadratic_realEven (A := a) (hsmooth := r.smooth)
    (hcpt := r.hasCompactSupport) (hsupp := hs) hre, hv] at hz
  linarith

/-- The smooth real even test cone determines the sign on its complete form domain. -/
theorem evenGroundEnergy_nonneg_of_evenPoleWeilNonneg {a : SuzukiPositiveAperture}
    (h : EvenPoleWeilNonneg a.1) : 0 ≤ evenGroundEnergy a := by
  by_contra hn
  exact exists_real_even_negative_of_ground_neg (lt_of_not_ge hn) h

end RHTower.CCMEvenSector

namespace RHTower.CCMEvenSector

theorem realEvenSource_isEven {a : SuzukiPositiveAperture} {u : ℝ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u)
    (hs : tsupport u ⊆ Ioo (-a.1) a.1) (he : ∀ x, u (-x) = u x) :
    IsEven a (realEvenSource a u hu hc hs).toCCMFormVector := by
  apply ccmArchimedeanFormEmbedding_injective a
  change (ccmArchimedeanFormToAperture a (ccmArchimedeanFormReflection a
    (realEvenSource a u hu hc hs).toCCMFormVector) : SoninL2) = _
  rw [ccmArchimedeanFormToAperture_reflection]
  change l2Reflection (ccmArchimedeanFormToAperture a
    (realEvenSource a u hu hc hs).toCCMFormVector : SoninL2) =
      (ccmArchimedeanFormToAperture a (realEvenSource a u hu hc hs).toCCMFormVector : SoninL2)
  apply Lp.ext
  let g := realEvenSource a u hu hc hs
  have hn := g.toCCMFormVector_physical_coeFn.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [g.toCCMFormVector_physical_coeFn,
    l2Reflection_ae (ccmArchimedeanFormToAperture a g.toCCMFormVector : SoninL2), hn]
    with x hx hr hn
  dsimp only [Function.comp_apply] at hn
  rw [hr, hn, hx]
  exact congrArg Complex.ofReal (he x)

/-- Every completed even ground is a floor for all strictly smaller real smooth apertures. -/
theorem evenWeilFloor_of_evenGroundEnergy (b : SuzukiPositiveAperture)
    {A : ℝ} (hAb : A < b.1) : EvenWeilFloor A (evenGroundEnergy b) := by
  intro u hu hc hs he hp
  have hs' : tsupport u ⊆ Ioo (-b.1) b.1 := by
    have hclosed : tsupport u ⊆ Icc (-A) A := by
      apply closure_minimal ?_ isClosed_Icc
      intro x hx
      apply abs_le.mp
      by_contra hn
      exact hx (hs x (lt_of_not_ge hn))
    exact hclosed.trans (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hpol : IsPolarConstrained b (realEvenSource b u hu hc hs').toCCMFormVector :=
    isPolarConstrained_realEven he (by simpa only [mul_comm] using hp)
  have hf := evenGroundEnergy_mul_le b _ hpol (realEvenSource_isEven hu hc hs' he)
  rw [sq_norm_ccmArchimedeanFormToAperture_realSource,
    ccmRestrictedWeilSourceQuadratic_realEven he] at hf
  exact hf

/-- The exact even ground, without a full-ground parity choice, controls heat windows. -/
theorem heatWindowNonneg_of_evenGroundEnergy_pos {b : SuzukiPositiveAperture}
    (hb : 0 < evenGroundEnergy b) {K : ℝ} (hK : 0 < K) (hKb : 4 * K < b.1 ^ 2) :
    HeatWindowNonneg K := by
  have hs := Real.sqrt_nonneg (4 * K)
  have hs2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * K)
  have hsb : Real.sqrt (4 * K) < b.1 := by nlinarith [b.2]
  let A := (Real.sqrt (4 * K) + b.1) / 2
  have hA : 0 < A := by dsimp [A]; linarith [b.2]
  have hAb : A < b.1 := by dsimp [A]; linarith
  have hKA : 4 * K < A ^ 2 := by
    have hsA : Real.sqrt (4 * K) < A := by dsimp [A]; linarith
    nlinarith
  have hfloor := evenWeilFloor_of_evenGroundEnergy b hAb
  filter_upwards [eventually_le_re_heatHankel_of_evenWeilFloor hA hfloor hK hKA
    (half_pos hb), eventually_gt_atTop 0] with n hn hn0 P hPd hPe
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hh := hn (K / n) (div_pos hK hn') le_rfl P hPd hPe
  have hmass : 0 ≤ ∫ x, heatTest (K / n) P x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact (mul_nonneg (by linarith : 0 ≤ evenGroundEnergy b - evenGroundEnergy b / 2) hmass).trans hh

/-- On the other side, a negative completed even ground gives negative sections at every large rank. -/
theorem eventually_heatWindow_negative_of_evenGroundEnergy_neg {a : SuzukiPositiveAperture}
    (ha : evenGroundEnergy a < 0) {K : ℝ} (hK : 0 < K) (haK : a.1 ^ 2 < 4 * K) :
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
      (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re < 0 := by
  have hnot := exists_real_even_negative_of_ground_neg ha
  unfold EvenPoleWeilNonneg at hnot
  push Not at hnot
  obtain ⟨u, hu, hc, hs, he, hp, hneg⟩ := hnot
  exact eventually_exists_poleHyperplane_heatHankel_neg_of_source hu hc hs he hp hneg hK haK

theorem polarGroundEnergy_le_evenGroundEnergy (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilPolarGroundEnergy a ≤ evenGroundEnergy a := by
  obtain ⟨u, hp, _, hn, hQ⟩ := exists_evenGround a
  have hf := ccmRestrictedWeilPolarGroundEnergy_mul_le a u hp
  simpa only [hn, one_pow, mul_one, hQ] using hf

end RHTower.CCMEvenSector
