import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnXiMassTimelikeBoostBridge
import GaloisForLFunctions.HTGeometry.PrincipalSquareRoot

/-!
# Optimal spacelike contour for the Xi mass kernel

For the damped mass phase with spectral parameter `sigma + I*u` and Fourier frequency `h`,
the complex propagation argument is `(sigma + I*u)^(2 : ℕ) + h^(2 : ℕ)`.  This module proves that the
square of its principal-root real part is exactly the maximum damping quadratic available to a
hyperbolically curved contour.  The optimizer is constructed as an actual nonnegative contour
angle, not merely as an abstract eigenvector.

In the strict spacelike chamber `0 < u < h`, the optimal rate strictly exceeds both the null gap
`h-u` and the undamped Lorentz gap `sqrt (h^(2 : ℕ)-u^(2 : ℕ))`.  The coefficient-critical cone therefore has
sharp limiting slope `a / sqrt (a^(2 : ℕ)-1/4)`, strictly below the best horizontal-strip slope
`a / (a-1/2)`.  This identifies a real quantitative loss in the existing Route T cone and isolates
the curved-contour/Bessel estimate needed to recover it.
-/

open Complex Real

namespace RHTower

noncomputable section

def xiMassSpacelikePropagationArgument (sigma u h : ℝ) : ℂ :=
  ((sigma : ℂ) + (u : ℂ) * I) ^ (2 : ℕ) + ((h ^ (2 : ℕ) : ℝ) : ℂ)

def xiMassSpacelikeTrace (sigma u h : ℝ) : ℝ := sigma ^ (2 : ℕ) + h ^ (2 : ℕ) - u ^ (2 : ℕ)

def xiMassSpacelikeAnisotropy (sigma u h : ℝ) : ℝ :=
  (sigma ^ (2 : ℕ) - h ^ (2 : ℕ) + u ^ (2 : ℕ)) / 2

def xiMassSpacelikeCoupling (sigma h : ℝ) : ℝ := sigma * h

def xiMassSpacelikeContourRadius (sigma u h : ℝ) : ℝ :=
  Real.sqrt
    (xiMassSpacelikeAnisotropy sigma u h ^ (2 : ℕ) +
      xiMassSpacelikeCoupling sigma h ^ (2 : ℕ))

def xiMassSpacelikePropagationRateSq (sigma u h : ℝ) : ℝ :=
  xiMassSpacelikeTrace sigma u h / 2 +
    xiMassSpacelikeContourRadius sigma u h

def xiMassSpacelikeContourQuadratic
    (sigma u h X Y : ℝ) : ℝ :=
  xiMassSpacelikeTrace sigma u h / 2 +
    xiMassSpacelikeAnisotropy sigma u h * X +
    xiMassSpacelikeCoupling sigma h * Y

def xiMassSpacelikeContourRateSq
    (sigma u h c s : ℝ) : ℝ :=
  (sigma * c + h * s) ^ (2 : ℕ) - (u * s) ^ (2 : ℕ)

def xiMassSpacelikeSharpSlope (a : ℝ) : ℝ :=
  a / Real.sqrt (a ^ (2 : ℕ) - 1 / 4)

def xiMassHorizontalStripLimitingSlope (a : ℝ) : ℝ :=
  a / (a - 1 / 2)

theorem xiMassSpacelikePropagationArgument_re (sigma u h : ℝ) :
    (xiMassSpacelikePropagationArgument sigma u h).re =
      xiMassSpacelikeTrace sigma u h := by
  rw [xiMassSpacelikePropagationArgument, xiMassSpacelikeTrace]
  simp [pow_two, Complex.mul_re]
  ring

theorem xiMassSpacelikePropagationArgument_im (sigma u h : ℝ) :
    (xiMassSpacelikePropagationArgument sigma u h).im = 2 * sigma * u := by
  rw [xiMassSpacelikePropagationArgument]
  simp [pow_two, Complex.mul_im]
  ring

theorem xiMassSpacelikeContourRadius_nonneg (sigma u h : ℝ) :
    0 ≤ xiMassSpacelikeContourRadius sigma u h := by
  exact Real.sqrt_nonneg _

theorem sq_xiMassSpacelikeContourRadius (sigma u h : ℝ) :
    xiMassSpacelikeContourRadius sigma u h ^ (2 : ℕ) =
      xiMassSpacelikeAnisotropy sigma u h ^ (2 : ℕ) +
        xiMassSpacelikeCoupling sigma h ^ (2 : ℕ) := by
  rw [xiMassSpacelikeContourRadius, Real.sq_sqrt]
  positivity

theorem norm_xiMassSpacelikePropagationArgument_eq_two_mul_radius
    (sigma u h : ℝ) :
    ‖xiMassSpacelikePropagationArgument sigma u h‖ =
      2 * xiMassSpacelikeContourRadius sigma u h := by
  have hr := sq_xiMassSpacelikeContourRadius sigma u h
  have hn : 0 ≤ ‖xiMassSpacelikePropagationArgument sigma u h‖ := norm_nonneg _
  have hR := xiMassSpacelikeContourRadius_nonneg sigma u h
  have hnormsq :
      ‖xiMassSpacelikePropagationArgument sigma u h‖ ^ (2 : ℕ) =
        xiMassSpacelikeTrace sigma u h ^ (2 : ℕ) + (2 * sigma * u) ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply,
      xiMassSpacelikePropagationArgument_re,
      xiMassSpacelikePropagationArgument_im]
    ring
  have halg :
      xiMassSpacelikeTrace sigma u h ^ (2 : ℕ) + (2 * sigma * u) ^ (2 : ℕ) =
        4 * (xiMassSpacelikeAnisotropy sigma u h ^ (2 : ℕ) +
          xiMassSpacelikeCoupling sigma h ^ (2 : ℕ)) := by
    unfold xiMassSpacelikeTrace xiMassSpacelikeAnisotropy
      xiMassSpacelikeCoupling
    ring
  nlinarith

theorem sq_csqrtRe_xiMassSpacelikePropagationArgument
    {sigma u h : ℝ} (htrace : 0 < xiMassSpacelikeTrace sigma u h) :
    HTGeometry.csqrtRe
        (xiMassSpacelikePropagationArgument sigma u h) ^ (2 : ℕ) =
      xiMassSpacelikePropagationRateSq sigma u h := by
  rw [HTGeometry.sq_csqrtRe]
  · rw [norm_xiMassSpacelikePropagationArgument_eq_two_mul_radius,
      xiMassSpacelikePropagationArgument_re]
    unfold xiMassSpacelikePropagationRateSq
    ring
  · rwa [xiMassSpacelikePropagationArgument_re]

theorem xiMassSpacelikeContourQuadratic_le_rateSq
    {sigma u h X Y : ℝ} (hunit : X ^ (2 : ℕ) + Y ^ (2 : ℕ) = 1) :
    xiMassSpacelikeContourQuadratic sigma u h X Y ≤
      xiMassSpacelikePropagationRateSq sigma u h := by
  let A := xiMassSpacelikeAnisotropy sigma u h
  let B := xiMassSpacelikeCoupling sigma h
  let R := xiMassSpacelikeContourRadius sigma u h
  have hR : 0 ≤ R := xiMassSpacelikeContourRadius_nonneg sigma u h
  have hR2 : R ^ (2 : ℕ) = A ^ (2 : ℕ) + B ^ (2 : ℕ) := by
    simpa only [A, B, R] using sq_xiMassSpacelikeContourRadius sigma u h
  have hdot : A * X + B * Y ≤ R := by
    by_cases hnonpos : A * X + B * Y ≤ 0
    · exact hnonpos.trans hR
    · have hpos : 0 < A * X + B * Y := lt_of_not_ge hnonpos
      have hcauchy : (A * X + B * Y) ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
        have hid :
            (A ^ (2 : ℕ) + B ^ (2 : ℕ)) * (X ^ (2 : ℕ) + Y ^ (2 : ℕ)) -
                (A * X + B * Y) ^ (2 : ℕ) =
              (A * Y - B * X) ^ (2 : ℕ) := by ring
        nlinarith [sq_nonneg (A * Y - B * X)]
      nlinarith
  unfold xiMassSpacelikeContourQuadratic
    xiMassSpacelikePropagationRateSq
  dsimp only [A, B, R] at hdot
  linarith

theorem xiMassSpacelikeDoubleAngle_unit
    {c s : ℝ} (hunit : c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1) :
    (c ^ (2 : ℕ) - s ^ (2 : ℕ)) ^ (2 : ℕ) + (2 * c * s) ^ (2 : ℕ) = 1 := by
  nlinarith [sq_nonneg (c ^ (2 : ℕ) + s ^ (2 : ℕ))]

theorem exists_xiMassSpacelike_nonnegative_doubleAngle_lift
    {X Y : ℝ} (hunit : X ^ (2 : ℕ) + Y ^ (2 : ℕ) = 1) (hY : 0 ≤ Y) :
    ∃ c s : ℝ, 0 ≤ c ∧ 0 ≤ s ∧ c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1 ∧
      c ^ (2 : ℕ) - s ^ (2 : ℕ) = X ∧ 2 * c * s = Y := by
  let c := Real.sqrt ((1 + X) / 2)
  let s := Real.sqrt ((1 - X) / 2)
  have hXsq : X ^ (2 : ℕ) ≤ 1 := by nlinarith [sq_nonneg Y]
  have hXlow : -1 ≤ X := by nlinarith [sq_nonneg (X + 1)]
  have hXhigh : X ≤ 1 := by nlinarith [sq_nonneg (X - 1)]
  have hcarg : 0 ≤ (1 + X) / 2 := by linarith
  have hsarg : 0 ≤ (1 - X) / 2 := by linarith
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hc2 : c ^ (2 : ℕ) = (1 + X) / 2 := by
    dsimp only [c]
    rw [Real.sq_sqrt hcarg]
  have hs2 : s ^ (2 : ℕ) = (1 - X) / 2 := by
    dsimp only [s]
    rw [Real.sq_sqrt hsarg]
  have hcsSq : (2 * c * s) ^ (2 : ℕ) = Y ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (c * s)]
  have hcs0 : 0 ≤ 2 * c * s := by positivity
  refine ⟨c, s, hc0, hs0, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

theorem xiMassSpacelikeContourRateSq_eq_quadratic
    {sigma u h c s : ℝ} (hunit : c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1) :
    xiMassSpacelikeContourRateSq sigma u h c s =
      xiMassSpacelikeContourQuadratic sigma u h
        (c ^ (2 : ℕ) - s ^ (2 : ℕ)) (2 * c * s) := by
  unfold xiMassSpacelikeContourRateSq xiMassSpacelikeContourQuadratic
    xiMassSpacelikeTrace xiMassSpacelikeAnisotropy
    xiMassSpacelikeCoupling
  nlinarith

theorem xiMassSpacelikeContourRateSq_le_propagationRateSq
    {sigma u h c s : ℝ} (hunit : c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1) :
    xiMassSpacelikeContourRateSq sigma u h c s ≤
      xiMassSpacelikePropagationRateSq sigma u h := by
  rw [xiMassSpacelikeContourRateSq_eq_quadratic hunit]
  exact xiMassSpacelikeContourQuadratic_le_rateSq
    (xiMassSpacelikeDoubleAngle_unit hunit)

theorem xiMassSpacelikeOptimalDoubleAngle_unit
    {sigma u h : ℝ}
    (hR : 0 < xiMassSpacelikeContourRadius sigma u h) :
    (xiMassSpacelikeAnisotropy sigma u h /
        xiMassSpacelikeContourRadius sigma u h) ^ (2 : ℕ) +
      (xiMassSpacelikeCoupling sigma h /
        xiMassSpacelikeContourRadius sigma u h) ^ (2 : ℕ) = 1 := by
  have hR2 := sq_xiMassSpacelikeContourRadius sigma u h
  field_simp [hR.ne']
  nlinarith

theorem xiMassSpacelikeContourQuadratic_optimalDoubleAngle
    {sigma u h : ℝ}
    (hR : 0 < xiMassSpacelikeContourRadius sigma u h) :
    xiMassSpacelikeContourQuadratic sigma u h
        (xiMassSpacelikeAnisotropy sigma u h /
          xiMassSpacelikeContourRadius sigma u h)
        (xiMassSpacelikeCoupling sigma h /
          xiMassSpacelikeContourRadius sigma u h) =
      xiMassSpacelikePropagationRateSq sigma u h := by
  have hR2 := sq_xiMassSpacelikeContourRadius sigma u h
  unfold xiMassSpacelikeContourQuadratic xiMassSpacelikePropagationRateSq
  field_simp [hR.ne']
  nlinarith

theorem xiMassSpacelikePropagationRateSq_is_exact_contourSupremum
    {sigma u h : ℝ}
    (hR : 0 < xiMassSpacelikeContourRadius sigma u h) :
    (∀ X Y : ℝ, X ^ (2 : ℕ) + Y ^ (2 : ℕ) = 1 →
      xiMassSpacelikeContourQuadratic sigma u h X Y ≤
        xiMassSpacelikePropagationRateSq sigma u h) ∧
    ∃ X Y : ℝ, X ^ (2 : ℕ) + Y ^ (2 : ℕ) = 1 ∧
      xiMassSpacelikeContourQuadratic sigma u h X Y =
        xiMassSpacelikePropagationRateSq sigma u h := by
  constructor
  · intro X Y hunit
    exact xiMassSpacelikeContourQuadratic_le_rateSq hunit
  · refine ⟨xiMassSpacelikeAnisotropy sigma u h /
        xiMassSpacelikeContourRadius sigma u h,
      xiMassSpacelikeCoupling sigma h /
        xiMassSpacelikeContourRadius sigma u h,
      xiMassSpacelikeOptimalDoubleAngle_unit hR,
      xiMassSpacelikeContourQuadratic_optimalDoubleAngle hR⟩

theorem exists_xiMassSpacelikeOptimalContour
    {sigma u h : ℝ} (hsigma : 0 < sigma) (hh : 0 < h) :
    ∃ c s : ℝ, 0 ≤ c ∧ 0 ≤ s ∧ c ^ (2 : ℕ) + s ^ (2 : ℕ) = 1 ∧
      xiMassSpacelikeContourRateSq sigma u h c s =
        xiMassSpacelikePropagationRateSq sigma u h := by
  let R := xiMassSpacelikeContourRadius sigma u h
  let X := xiMassSpacelikeAnisotropy sigma u h / R
  let Y := xiMassSpacelikeCoupling sigma h / R
  have hR : 0 < R := by
    dsimp only [R]
    rw [xiMassSpacelikeContourRadius, Real.sqrt_pos]
    have hB : 0 < xiMassSpacelikeCoupling sigma h := by
      rw [xiMassSpacelikeCoupling]
      positivity
    nlinarith [sq_pos_of_pos hB]
  have hunit : X ^ (2 : ℕ) + Y ^ (2 : ℕ) = 1 := by
    simpa only [X, Y, R] using xiMassSpacelikeOptimalDoubleAngle_unit hR
  have hY : 0 ≤ Y := by
    dsimp only [Y]
    exact div_nonneg (mul_nonneg hsigma.le hh.le) hR.le
  rcases exists_xiMassSpacelike_nonnegative_doubleAngle_lift hunit hY with
    ⟨c, s, hc, hs, hcs, hX, hYeq⟩
  refine ⟨c, s, hc, hs, hcs, ?_⟩
  rw [xiMassSpacelikeContourRateSq_eq_quadratic hcs, hX, hYeq]
  simpa only [X, Y, R] using
    xiMassSpacelikeContourQuadratic_optimalDoubleAngle hR

theorem xiMassSpacelikeContourRadius_pos
    {sigma h : ℝ} (hsigma : 0 < sigma) (hh : 0 < h) (u : ℝ) :
    0 < xiMassSpacelikeContourRadius sigma u h := by
  rw [xiMassSpacelikeContourRadius, Real.sqrt_pos]
  have hB : 0 < xiMassSpacelikeCoupling sigma h := by
    rw [xiMassSpacelikeCoupling]
    positivity
  nlinarith [sq_pos_of_pos hB]

theorem sqrt_spacelikeGap_lt_csqrtRe_propagationArgument
    {sigma u h : ℝ} (hsigma : 0 < sigma) (hu0 : 0 ≤ u) (huh : u < h) :
    Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) <
      HTGeometry.csqrtRe
        (xiMassSpacelikePropagationArgument sigma u h) := by
  have hgap : 0 < h ^ (2 : ℕ) - u ^ (2 : ℕ) := by nlinarith
  have htrace : 0 < xiMassSpacelikeTrace sigma u h := by
    rw [xiMassSpacelikeTrace]
    nlinarith [sq_pos_of_pos hsigma]
  have hsqrt0 : 0 ≤ Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) := Real.sqrt_nonneg _
  have hrate0 : 0 ≤ HTGeometry.csqrtRe
      (xiMassSpacelikePropagationArgument sigma u h) :=
    HTGeometry.csqrtRe_nonneg _
  have hgapSq : Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) ^ (2 : ℕ) = h ^ (2 : ℕ) - u ^ (2 : ℕ) := by
    rw [Real.sq_sqrt hgap.le]
  have hrateSq := sq_csqrtRe_xiMassSpacelikePropagationArgument htrace
  have hstrict : h ^ (2 : ℕ) - u ^ (2 : ℕ) <
      xiMassSpacelikePropagationRateSq sigma u h := by
    rw [← hrateSq]
    have hargtrace :
        0 < (xiMassSpacelikePropagationArgument sigma u h).re := by
      rwa [xiMassSpacelikePropagationArgument_re]
    have hrele := HTGeometry.re_le_sq_csqrtRe
      (z := xiMassSpacelikePropagationArgument sigma u h) hargtrace
    rw [xiMassSpacelikePropagationArgument_re, xiMassSpacelikeTrace] at hrele
    nlinarith [sq_pos_of_pos hsigma]
  nlinarith

theorem xiMassHorizontalNullGap_lt_sqrt_spacelikeGap
    {u h : ℝ} (hu : 0 < u) (huh : u < h) :
    h - u < Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) := by
  have hh : 0 < h := hu.trans huh
  have hgap : 0 < h ^ (2 : ℕ) - u ^ (2 : ℕ) := by nlinarith
  have hsqrt0 : 0 ≤ Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) ^ (2 : ℕ) = h ^ (2 : ℕ) - u ^ (2 : ℕ) := by
    rw [Real.sq_sqrt hgap.le]
  nlinarith [sq_pos_of_pos hu]

theorem xiMassHorizontalNullGap_lt_csqrtRe_propagationArgument
    {sigma u h : ℝ} (hsigma : 0 < sigma) (hu : 0 < u) (huh : u < h) :
    h - u < HTGeometry.csqrtRe
      (xiMassSpacelikePropagationArgument sigma u h) :=
  (xiMassHorizontalNullGap_lt_sqrt_spacelikeGap hu huh).trans
    (sqrt_spacelikeGap_lt_csqrtRe_propagationArgument hsigma hu.le huh)

theorem xiMassSpacelikeSharpSlope_denominator_pos
    {a : ℝ} (ha : 1 / 2 < a) :
    0 < Real.sqrt (a ^ (2 : ℕ) - 1 / 4) := by
  rw [Real.sqrt_pos]
  have ha0 : 0 < a := by linarith
  nlinarith [sq_pos_of_pos ha0]

theorem xiMassSpacelikeBesselDecay_iff_above_sharpSlope
    {a u h : ℝ} (ha : 1 / 2 < a) (hu : 0 < u) (huh : u < h) :
    h / 2 < a * Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ)) ↔
      xiMassSpacelikeSharpSlope a * u < h := by
  let q := Real.sqrt (h ^ (2 : ℕ) - u ^ (2 : ℕ))
  let k := Real.sqrt (a ^ (2 : ℕ) - 1 / 4)
  have ha0 : 0 < a := by linarith
  have hh : 0 < h := hu.trans huh
  have hq : 0 < q := by
    dsimp only [q]
    rw [Real.sqrt_pos]
    nlinarith
  have hk : 0 < k := by
    simpa only [k] using xiMassSpacelikeSharpSlope_denominator_pos ha
  have hq2 : q ^ (2 : ℕ) = h ^ (2 : ℕ) - u ^ (2 : ℕ) := by
    dsimp only [q]
    rw [Real.sq_sqrt]
    nlinarith
  have hk2 : k ^ (2 : ℕ) = a ^ (2 : ℕ) - 1 / 4 := by
    dsimp only [k]
    rw [Real.sq_sqrt]
    nlinarith [sq_pos_of_pos ha0]
  constructor
  · intro hdecay
    have hsq : (h / 2) ^ (2 : ℕ) < (a * q) ^ (2 : ℕ) := by
      nlinarith [mul_pos ha0 hq]
    have hsquareLinear : (a * u) ^ (2 : ℕ) < (k * h) ^ (2 : ℕ) := by
      nlinarith
    have hlin : a * u < k * h := by
      nlinarith [sq_nonneg (a * u + k * h), mul_pos ha0 hu, mul_pos hk hh]
    rw [xiMassSpacelikeSharpSlope]
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ hk).2 (by nlinarith)
  · intro hslope
    rw [xiMassSpacelikeSharpSlope] at hslope
    have hlin : a * u < k * h := by
      rw [div_mul_eq_mul_div] at hslope
      have := (div_lt_iff₀ hk).1 hslope
      nlinarith
    have hsquareLinear : (a * u) ^ (2 : ℕ) < (k * h) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (a * u + k * h), mul_pos ha0 hu, mul_pos hk hh]
    have hsq : (h / 2) ^ (2 : ℕ) < (a * q) ^ (2 : ℕ) := by
      nlinarith
    nlinarith [mul_pos ha0 hq]

theorem xiMassSpacelikeSharpSlope_lt_horizontalStripLimitingSlope
    {a : ℝ} (ha : 1 / 2 < a) :
    xiMassSpacelikeSharpSlope a < xiMassHorizontalStripLimitingSlope a := by
  let k := Real.sqrt (a ^ (2 : ℕ) - 1 / 4)
  let d := a - 1 / 2
  have ha0 : 0 < a := by linarith
  have hk : 0 < k := by
    simpa only [k] using xiMassSpacelikeSharpSlope_denominator_pos ha
  have hd : 0 < d := by dsimp only [d]; linarith
  have hk2 : k ^ (2 : ℕ) = a ^ (2 : ℕ) - 1 / 4 := by
    dsimp only [k]
    rw [Real.sq_sqrt]
    nlinarith [sq_pos_of_pos ha0]
  have hdk : d < k := by
    dsimp only [d]
    nlinarith [sq_nonneg (k + (a - 1 / 2))]
  rw [xiMassSpacelikeSharpSlope, xiMassHorizontalStripLimitingSlope]
  change a / k < a / d
  exact (div_lt_div_iff₀ hk hd).2 (by nlinarith)

end

end RHTower
