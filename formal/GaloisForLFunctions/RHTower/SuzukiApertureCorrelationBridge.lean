import GaloisForLFunctions.RHTower.SuzukiEquationTwoFour

/-!
# Compact-aperture double-integral/correlation bridge

Suzuki repeatedly passes from a double integral on `(-a,a)^(2 : ℕ)` to a one-variable correlation on
the difference interval `(-2a,2a)`. This module proves that passage once for every continuous
kernel and every continuous function supported in a strictly smaller compact aperture. Strict
interior support is the source-locked smooth core used for the distributional calculations; no
integrability or Fubini premise remains on the public theorem.
-/

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.RHTower

private theorem integrable_uncurry_compactDiffForm
    {r : ℝ} {K f : ℝ → ℝ}
    (hK : Continuous K) (hf : Continuous f)
    (hfsupp : Function.support f ⊆ Icc (-r) r) :
    Integrable (Function.uncurry (diffFormIntegrand K f f))
      (volume.prod volume) := by
  have hsupp : Function.support (Function.uncurry (diffFormIntegrand K f f)) ⊆
      Icc (-r) r ×ˢ Icc (-r) r := by
    intro p hp
    have hy : f p.2 ≠ 0 := by
      intro hz
      apply hp
      dsimp only [Function.uncurry, diffFormIntegrand]
      rw [hz]
      ring
    have hx : f p.1 ≠ 0 := by
      intro hz
      apply hp
      dsimp only [Function.uncurry, diffFormIntegrand]
      rw [hz]
      ring
    exact ⟨hfsupp hx, hfsupp hy⟩
  have hcont : Continuous (Function.uncurry (diffFormIntegrand K f f)) := by
    change Continuous (fun p : ℝ × ℝ => K (p.1 - p.2) * f p.2 * f p.1)
    fun_prop
  rw [← Measure.volume_eq_prod]
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc) hsupp)

private theorem integrable_uncurry_compactDiffShear
    {r : ℝ} {K f : ℝ → ℝ}
    (hK : Continuous K) (hf : Continuous f)
    (hfsupp : Function.support f ⊆ Icc (-r) r) :
    Integrable (Function.uncurry (diffShearIntegrand K f f))
      (volume.prod volume) := by
  have hsupp : Function.support (Function.uncurry (diffShearIntegrand K f f)) ⊆
      Icc (-r) r ×ˢ Icc (-(2 * r)) (2 * r) := by
    intro p hp
    have hy : f p.1 ≠ 0 := by
      intro hz
      apply hp
      dsimp only [Function.uncurry, diffShearIntegrand]
      rw [hz]
      ring
    have hty : f (p.2 + p.1) ≠ 0 := by
      intro hz
      apply hp
      dsimp only [Function.uncurry, diffShearIntegrand]
      rw [hz]
      ring
    have hyr := hfsupp hy
    have htyr := hfsupp hty
    exact ⟨hyr, by constructor <;> linarith [hyr.1, hyr.2, htyr.1, htyr.2]⟩
  have hcont : Continuous (Function.uncurry (diffShearIntegrand K f f)) := by
    change Continuous (fun p : ℝ × ℝ => K p.2 * f p.1 * f (p.2 + p.1))
    fun_prop
  rw [← Measure.volume_eq_prod]
  exact hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc) hsupp)

/-- Exact compact-aperture shear identity. Both iterated interval integrals and the whole-line
correlation are proved integrable from continuity and compact support. -/
theorem compactApertureDoubleIntegral_eq_correlation
    {a r : ℝ} (hr : r < a) {K f : ℝ → ℝ}
    (hK : Continuous K) (hf : Continuous f)
    (hfsupp : Function.support f ⊆ Icc (-r) r) :
    (∫ x in (-a)..a, ∫ y in (-a)..a, K (x - y) * f y * f x) =
      ∫ t in (-(2 * a))..(2 * a), K t * screwCrossCorr f f t := by
  have hfsuppA : Function.support f ⊆ Ioc (-a) a := by
    intro x hx
    have hxr := hfsupp hx
    constructor <;> linarith [hxr.1, hxr.2, hr]
  have hinner (x : ℝ) :
      (∫ y in (-a)..a, K (x - y) * f y * f x) =
        ∫ y : ℝ, K (x - y) * f y * f x := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro y hy
    have hfy : f y ≠ 0 := by
      intro hz
      exact hy (by simp [hz])
    exact hfsuppA hfy
  rw [intervalIntegral.integral_congr (fun x _ => hinner x)]
  have houter :
      (∫ x in (-a)..a, ∫ y : ℝ, K (x - y) * f y * f x) =
        ∫ x : ℝ, ∫ y : ℝ, K (x - y) * f y * f x := by
    apply intervalIntegral.integral_eq_integral_of_support_subset
    intro x hx
    have hfx : f x ≠ 0 := by
      intro hz
      exact hx (by simp [hz])
    exact hfsuppA hfx
  rw [houter]
  have hdiff :
      (∫ x : ℝ, ∫ y : ℝ, K (x - y) * f y * f x) = diffBilinForm K f f := by
    rw [diffBilinForm_eq_integral_uncurry, Measure.volume_eq_prod ℝ ℝ]
    exact integral_integral (integrable_uncurry_compactDiffForm hK hf hfsupp)
  rw [hdiff, diffBilinForm_eq_correlation_pairing K f f
    (integrable_uncurry_compactDiffForm hK hf hfsupp)
    (integrable_uncurry_compactDiffShear hK hf hfsupp)]
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have hcorr : screwCrossCorr f f t ≠ 0 := by
    intro hz
    exact ht (by simp [hz])
  constructor
  · by_contra hneg
    have hz := screwCrossCorr_eq_zero_of_support_radius_neg hfsupp hfsupp
      (show t < -(2 * r) by linarith [hneg, hr])
    exact hcorr hz
  · by_contra hpos
    have hz := screwCrossCorr_eq_zero_of_support_radius_pos hfsupp hfsupp
      (show 2 * r < t by linarith [hpos, hr])
    exact hcorr hz

/-- Derivative specialization used in Suzuki's equations (2.4) and (2.5). -/
theorem suzukiCoreDerivativeDoubleIntegral_eq_correlation
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) {K : ℝ → ℝ} (hK : Continuous K) :
    (∫ x in (-A.1)..A.1, ∫ y in (-A.1)..A.1,
      K (x - y) * deriv u y * deriv u x) =
      ∫ t in (-(2 * A.1))..(2 * A.1),
        K t * screwCrossCorr (deriv u) (deriv u) t := by
  exact compactApertureDoubleIntegral_eq_correlation u.supportRadius_lt_aperture hK
    (u.smooth.continuous_deriv (by simp)) (core_deriv_support_subset_radius u)

/-- Undifferentiated specialization used by the smooth remainder block. -/
theorem suzukiCoreDoubleIntegral_eq_correlation
    (A : _root_.RHTower.SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) {K : ℝ → ℝ} (hK : Continuous K) :
    (∫ x in (-A.1)..A.1, ∫ y in (-A.1)..A.1,
      K (x - y) * u y * u x) =
      ∫ t in (-(2 * A.1))..(2 * A.1), K t * suzukiCoreAutocorrelation u t := by
  exact compactApertureDoubleIntegral_eq_correlation u.supportRadius_lt_aperture hK
    u.continuous u.support_subset

end GaloisForLFunctions.RHTower
