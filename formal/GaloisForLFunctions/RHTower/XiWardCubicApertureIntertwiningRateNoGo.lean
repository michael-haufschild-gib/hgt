import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolConstantChannelLandingNoGo

/-!
# Cubic Ward aperture-intertwining rate no-go (W-H194)

P-G195 excludes fixed fibrewise mixtures of the three Burnol colligation channels.  This module
excludes a much larger class: every linear radius-nonlocal landing that intertwines the aperture
translation semigroup.

The cubic conormal `r * exp (-z r)` is a length-two generalized translation eigenvector.  Its
second translation difference vanishes at multiplier `exp (-z c)`.  A linear translation
intertwiner preserves that exact annihilating relation.  Two modes with distinct real decay rates
have multipliers with different norms, so the target relation is nonzero already at radius zero.

Every primitive Euler mode has real centered rate at least `log 2`, while every strict-right Xi
mode has rate below `1/2`.  Hence no aperture-intertwining linear operator—even an unbounded,
radius-nonlocal one—can map one primitive Burnol conormal to a strict-right completed-Xi conormal.
The missing contraction must break aperture covariance through a polar--Gamma boundary defect;
stationary convolution, multiplier, or functional calculus cannot be the landing mechanism.
-/

open Complex

namespace RHTower

noncomputable section

/-- Translation in the radial aperture coordinate. -/
def xiWardCubicRadialTranslate (c : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun r => f (r + c)

/-- Universal length-two generalized exponential mode underlying the cubic conormal. -/
def xiWardCubicRadialGeneralizedMode (z : ℂ) : ℝ → ℂ :=
  fun r => (r : ℂ) * Complex.exp (-(z * (r : ℂ)))

/-- Second translation difference at multiplier `mu`. -/
def xiWardCubicRadialSecondDifference
    (c : ℝ) (mu : ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun r => f (r + 2 * c) - 2 * mu * f (r + c) + mu ^ (2 : ℕ) * f r

/-- A cubic conormal mode is killed by the square of its exact translation character. -/
theorem xiWardCubicRadialSecondDifference_mode (z : ℂ) (c : ℝ) :
    xiWardCubicRadialSecondDifference c (Complex.exp (-(z * (c : ℂ))))
        (xiWardCubicRadialGeneralizedMode z) = 0 := by
  funext r
  rw [xiWardCubicRadialSecondDifference, xiWardCubicRadialGeneralizedMode,
    xiWardCubicRadialGeneralizedMode, xiWardCubicRadialGeneralizedMode]
  have h1 : Complex.exp (-(z * ((r + c : ℝ) : ℂ))) =
      Complex.exp (-(z * (r : ℂ))) * Complex.exp (-(z * (c : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (-(z * ((r + 2 * c : ℝ) : ℂ))) =
      Complex.exp (-(z * (r : ℂ))) * Complex.exp (-(z * (c : ℂ))) ^ (2 : ℕ) := by
    rw [pow_two, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  push_cast
  ring_nf
  rfl

theorem xiWardCubicRadialSecondDifference_eq_translates
    (c : ℝ) (mu : ℂ) (f : ℝ → ℂ) :
    xiWardCubicRadialSecondDifference c mu f =
      xiWardCubicRadialTranslate (2 * c) f -
        (2 * mu) • xiWardCubicRadialTranslate c f + mu ^ (2 : ℕ) • f := by
  rfl

/-- At a wrong nonzero translation multiplier, the second difference of a cubic conormal is
already nonzero at the radial boundary. -/
theorem xiWardCubicRadialSecondDifference_mode_apply_zero
    (z : ℂ) {c : ℝ} (hc : c ≠ 0) {mu : ℂ}
    (hmu : mu ≠ Complex.exp (-(z * (c : ℂ)))) :
    xiWardCubicRadialSecondDifference c mu
        (xiWardCubicRadialGeneralizedMode z) 0 ≠ 0 := by
  rw [xiWardCubicRadialSecondDifference, xiWardCubicRadialGeneralizedMode,
    xiWardCubicRadialGeneralizedMode, xiWardCubicRadialGeneralizedMode]
  simp only [ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, zero_mul,
    zero_add]
  have he : Complex.exp (-(z * (((2 * c : ℝ) : ℂ)))) =
      Complex.exp (-(z * (c : ℂ))) ^ (2 : ℕ) := by
    rw [pow_two, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  have hexp : Complex.exp (-(z * (c : ℂ))) ≠ 0 := Complex.exp_ne_zero _
  push_cast
  intro h
  have hfactor :
      (2 * (c : ℂ)) * Complex.exp (-(z * (c : ℂ))) *
          (Complex.exp (-(z * (c : ℂ))) - mu) = 0 := by
    linear_combination h
  have hleft :
      (2 * (c : ℂ)) * Complex.exp (-(z * (c : ℂ))) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr hc)
    · exact hexp
  have hdiff := (mul_eq_zero.mp hfactor).resolve_left hleft
  exact hmu (sub_eq_zero.mp hdiff).symm

/-- Distinct real decay rates give distinct translation characters at every positive aperture. -/
theorem exp_neg_mul_ne_of_re_ne
    {z w : ℂ} {c : ℝ} (hc : 0 < c) (hre : z.re ≠ w.re) :
    Complex.exp (-(z * (c : ℂ))) ≠ Complex.exp (-(w * (c : ℂ))) := by
  intro h
  have hn := congrArg norm h
  rw [Complex.norm_exp, Complex.norm_exp] at hn
  have hrexp := Real.exp_injective hn
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hrexp
  apply hre
  nlinarith

/-- No linear aperture-translation intertwiner can change the real decay rate of a cubic
generalized mode.  No continuity or boundedness premise is needed. -/
theorem not_exists_linear_apertureIntertwiner_changes_radialMode_rate
    {z w : ℂ} (hre : z.re ≠ w.re) :
    ¬ ∃ T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ),
      (∀ c f,
        T (xiWardCubicRadialTranslate c f) =
          xiWardCubicRadialTranslate c (T f)) ∧
      T (xiWardCubicRadialGeneralizedMode z) =
        xiWardCubicRadialGeneralizedMode w := by
  rintro ⟨T, hcomm, hland⟩
  let c : ℝ := 1
  let mu : ℂ := Complex.exp (-(z * (c : ℂ)))
  have hsource := xiWardCubicRadialSecondDifference_mode z c
  have htransport :
      T (xiWardCubicRadialSecondDifference c mu
          (xiWardCubicRadialGeneralizedMode z)) =
        xiWardCubicRadialSecondDifference c mu
          (T (xiWardCubicRadialGeneralizedMode z)) := by
    rw [xiWardCubicRadialSecondDifference_eq_translates,
      xiWardCubicRadialSecondDifference_eq_translates,
      map_add, map_sub, map_smul, map_smul, hcomm, hcomm]
  have hzero :
      xiWardCubicRadialSecondDifference c mu
          (xiWardCubicRadialGeneralizedMode w) = 0 := by
    rw [← hland, ← htransport, hsource, map_zero]
  have hmu : mu ≠ Complex.exp (-(w * (c : ℂ))) := by
    exact exp_neg_mul_ne_of_re_ne (by norm_num : 0 < c) hre
  exact (xiWardCubicRadialSecondDifference_mode_apply_zero w
    (by norm_num : c ≠ 0) hmu) (by
      have hz := congrFun hzero 0
      simpa using hz)

theorem xiWardCubicRadialGeneralizedMode_eq_routePXiBaseConormalResidueFeature
    (rho : ℂ) :
    xiWardCubicRadialGeneralizedMode (rho - 1 / 2) =
      routePXiBaseConormalResidueFeature rho := by
  rfl

/-- **W-H194 aperture-covariance obstruction.** No linear radius-nonlocal operator commuting with
all aperture translations maps one literal primitive Burnol conormal to any strict-right
completed-Xi conormal. -/
theorem not_exists_apertureIntertwiner_primitive_to_strictRight
    (q : XiRightZeroCopy) (pe : Nat.Primes × ℕ) (kappa : ℝ) :
    ¬ ∃ T : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ),
      (∀ c f,
        T (xiWardCubicRadialTranslate c f) =
          xiWardCubicRadialTranslate c (T f)) ∧
      T (xiWardCubicBurnolWindowConormalFeature ·
          (routePPrimitiveBurnolSpectralPoint pe kappa)) =
        routePXiBaseConormalResidueFeature (q.1.1 : ℂ) := by
  have hre :
      (routePPrimitiveBurnolSpectralPoint pe kappa - 1 / 2).re ≠
        ((q.1.1 : ℂ) - 1 / 2).re := by
    have hgap := xiRightCenteredZero_re_lt_primitiveBurnolLogFrequency pe q
    rw [xiRightCenteredZero_eq_support_sub_half] at hgap
    norm_num [Complex.sub_re] at hgap ⊢
    rw [routePPrimitiveBurnolSpectralPoint_re]
    linarith
  rintro ⟨T, hcomm, hland⟩
  apply not_exists_linear_apertureIntertwiner_changes_radialMode_rate hre
  refine ⟨T, hcomm, ?_⟩
  rw [xiWardCubicRadialGeneralizedMode_eq_routePXiBaseConormalResidueFeature,
    xiWardCubicRadialGeneralizedMode_eq_routePXiBaseConormalResidueFeature]
  simpa only [xiWardCubicBurnolWindowConormalFeature_eq] using hland

end

end RHTower
