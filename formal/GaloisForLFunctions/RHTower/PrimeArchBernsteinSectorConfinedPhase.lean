import GaloisForLFunctions.RHTower.PrimeArchBernsteinConfinedPhase
import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound

/-!
# Narrow-sector confinement of the prime--archimedean Bernstein phase

The disk-only Bernstein estimate loses the narrow sector forced by the exact off-line-quartet
orientation bound.  After endpoint normalization every reciprocal-square atom satisfies

`im u ^ 2 ≤ (1 / 84) * re u ^ 2`.

For an off-line atom one also has `‖u‖ < 1 / 4`.  These two source-derived inequalities imply the
strict elliptic bound

`‖u‖ + ‖1 - u‖ < 501 / 500`.

The initial complete-Bernstein bound is `501 / 500`; the same geometry admits the tighter
rational base `100197 / 100000`.  The older exact square formula is retained for downstream
compatibility.  Failure of RH can therefore occupy only a strict near-critical exponential
window above exponent one.
-/

open Complex Filter Topology
open scoped BigOperators Polynomial
open Polynomial

set_option maxHeartbeats 1600000

namespace RHTower

noncomputable section

/-- Rational amplitude ceiling supplied jointly by the endpoint quarter disk and the exact
one-eighty-fourth orientation sector. -/
def xiSectorConfinedBernsteinAmplitudeBase : ℝ := 501 / 500

theorem one_lt_xiSectorConfinedBernsteinAmplitudeBase :
    1 < xiSectorConfinedBernsteinAmplitudeBase := by
  norm_num [xiSectorConfinedBernsteinAmplitudeBase]

/-- Tighter rational ellipse ceiling extracted from the same quarter-disk and `1/84` sector
constraints. -/
def xiSectorRefinedBernsteinAmplitudeBase : ℝ := 100197 / 100000

theorem one_lt_xiSectorRefinedBernsteinAmplitudeBase :
    1 < xiSectorRefinedBernsteinAmplitudeBase := by
  norm_num [xiSectorRefinedBernsteinAmplitudeBase]

/-- Exact radical ellipse ceiling from the quarter disk and `1/84` orientation sector. -/
def xiSectorRadicalBernsteinAmplitudeBase : ℝ :=
  1 / 4 + Real.sqrt (17 / 16 - Real.sqrt (84 / 85) / 2)

theorem one_lt_xiSectorRadicalBernsteinAmplitudeBase :
    1 < xiSectorRadicalBernsteinAmplitudeBase := by
  let c : ℝ := Real.sqrt (84 / 85 : ℝ)
  let g : ℝ := Real.sqrt (17 / 16 - c / 2)
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    exact Real.sqrt_nonneg _
  have hcSq : c ^ 2 = 84 / 85 := by
    dsimp only [c]
    rw [Real.sq_sqrt]
    norm_num
  have hcOne : c < 1 := by
    nlinarith [sq_nonneg (c + 1)]
  have hrad : 0 ≤ 17 / 16 - c / 2 := by
    nlinarith
  have hgSq : g ^ 2 = 17 / 16 - c / 2 := by
    dsimp only [g]
    rw [Real.sq_sqrt hrad]
  have hg0 : 0 ≤ g := by
    dsimp only [g]
    exact Real.sqrt_nonneg _
  have hthree : 3 / 4 < g := by
    have hsq : (3 / 4 : ℝ) ^ 2 < g ^ 2 := by
      rw [hgSq]
      nlinarith
    nlinarith [sq_nonneg (g + (3 / 4 : ℝ))]
  change 1 < 1 / 4 + g
  linarith

theorem xiSectorRadicalBernsteinAmplitudeBase_lt_refined :
    xiSectorRadicalBernsteinAmplitudeBase < xiSectorRefinedBernsteinAmplitudeBase := by
  let c : ℝ := Real.sqrt (84 / 85 : ℝ)
  let R : ℝ := 1 / 4
  let g : ℝ := Real.sqrt (1 - 2 * c * R + R ^ 2)
  let B : ℝ := R + g
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    exact Real.sqrt_nonneg _
  have hcSq : c ^ 2 = 84 / 85 := by
    dsimp only [c]
    rw [Real.sq_sqrt]
    norm_num
  have hcLower : 9941 / 10000 < c := by
    have hsq : (9941 / 10000 : ℝ) ^ 2 < c ^ 2 := by
      rw [hcSq]
      norm_num
    nlinarith [sq_nonneg (c + (9941 / 10000 : ℝ))]
  have hrad : 0 ≤ 1 - 2 * c * R + R ^ 2 := by
    have hcOne : c ≤ 1 := by
      nlinarith [sq_nonneg (c + 1)]
    dsimp only [R]
    nlinarith
  have hgSq : g ^ 2 = 1 - 2 * c * R + R ^ 2 := by
    dsimp only [g]
    rw [Real.sq_sqrt hrad]
  have hg0 : 0 ≤ g := by
    dsimp only [g]
    exact Real.sqrt_nonneg _
  have hgLess : g < 75197 / 100000 := by
    have hsq : g ^ 2 < (75197 / 100000 : ℝ) ^ 2 := by
      rw [hgSq]
      dsimp only [R]
      nlinarith
    nlinarith [sq_nonneg (g + (75197 / 100000 : ℝ))]
  have hBdef : B = xiSectorRadicalBernsteinAmplitudeBase := by
    dsimp only [B, g, c, R, xiSectorRadicalBernsteinAmplitudeBase]
    congr 1
    ring
  rw [← hBdef]
  dsimp only [xiSectorRefinedBernsteinAmplitudeBase, B, R]
  linarith

theorem xiSectorRefinedBernsteinAmplitudeBase_lt_sectorConfined :
    xiSectorRefinedBernsteinAmplitudeBase < xiSectorConfinedBernsteinAmplitudeBase := by
  norm_num [xiSectorRefinedBernsteinAmplitudeBase, xiSectorConfinedBernsteinAmplitudeBase]

theorem xiSectorConfinedBernsteinAmplitudeBase_sq_eq :
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 = 251001 / 250000 := by
  norm_num [xiSectorConfinedBernsteinAmplitudeBase]

theorem xiSectorConfinedBernsteinAmplitudeBase_sq_lt_twoHundredOne_over_twoHundred :
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 < 201 / 200 := by
  norm_num [xiSectorConfinedBernsteinAmplitudeBase]

theorem xiSectorConfinedBernsteinAmplitudeBase_sq_lt_oneThousandSeven_over_oneThousand :
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 < 1007 / 1000 := by
  norm_num [xiSectorConfinedBernsteinAmplitudeBase]

theorem xiSectorConfinedBernsteinAmplitudeBase_sq_lt_oneHundredOne_over_oneHundred :
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 < 101 / 100 := by
  norm_num [xiSectorConfinedBernsteinAmplitudeBase]

/-- Pure geometry: the `1/84` sector inside the strict quarter disk lies in the Bernstein ellipse
with major-axis sum `501/500`. -/
theorem norm_add_norm_one_sub_lt_sectorConfinedBase
    {u : ℂ} (hr : ‖u‖ < 1 / 4)
    (hx : 0 ≤ u.re)
    (hy : u.im ^ 2 ≤ (1 / 84 : ℝ) * u.re ^ 2) :
    ‖u‖ + ‖1 - u‖ < xiSectorConfinedBernsteinAmplitudeBase := by
  let r : ℝ := ‖u‖
  let s : ℝ := ‖1 - u‖
  let x : ℝ := u.re
  have hr0 : 0 ≤ r := norm_nonneg u
  have hs0 : 0 ≤ s := norm_nonneg (1 - u)
  have hx0 : 0 ≤ x := hx
  have hrSq : r ^ 2 = x ^ 2 + u.im ^ 2 := by
    dsimp only [r, x]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hrx : r ^ 2 ≤ (85 / 84 : ℝ) * x ^ 2 := by
    rw [hrSq]
    dsimp only [x] at hy ⊢
    nlinarith
  have hcxSq : ((497 / 500 : ℝ) * r) ^ 2 ≤ x ^ 2 := by
    have hconst : (497 / 500 : ℝ) ^ 2 * (85 / 84 : ℝ) < 1 := by
      norm_num
    nlinarith [sq_nonneg x]
  have hcx0 : 0 ≤ (497 / 500 : ℝ) * r := by positivity
  have hcx : (497 / 500 : ℝ) * r ≤ x := by
    nlinarith [sq_nonneg (x + (497 / 500 : ℝ) * r)]
  have hsSq : s ^ 2 = 1 - 2 * x + r ^ 2 := by
    dsimp only [s, x, r]
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im]
    ring
  have hBr : 0 < xiSectorConfinedBernsteinAmplitudeBase - r := by
    dsimp only [r] at hr ⊢
    norm_num [xiSectorConfinedBernsteinAmplitudeBase] at hr ⊢
    linarith
  have hlinear :
      2 * (xiSectorConfinedBernsteinAmplitudeBase - 497 / 500) * r <
        xiSectorConfinedBernsteinAmplitudeBase ^ 2 - 1 := by
    have hcoeff :
        0 < xiSectorConfinedBernsteinAmplitudeBase - 497 / 500 := by
      norm_num [xiSectorConfinedBernsteinAmplitudeBase]
    have hconst :
        2 * (xiSectorConfinedBernsteinAmplitudeBase - 497 / 500) * (1 / 4 : ℝ) <
          xiSectorConfinedBernsteinAmplitudeBase ^ 2 - 1 := by
      norm_num [xiSectorConfinedBernsteinAmplitudeBase]
    nlinarith
  have hsLt : s ^ 2 < (xiSectorConfinedBernsteinAmplitudeBase - r) ^ 2 := by
    nlinarith
  have hs : s < xiSectorConfinedBernsteinAmplitudeBase - r := by
    nlinarith [sq_nonneg (s + (xiSectorConfinedBernsteinAmplitudeBase - r))]
  dsimp only [s, r] at hs ⊢
  linarith

/-- Pure geometry with the tightened rational major axis.  The sole inputs remain the strict
quarter disk, nonnegative real part, and the exact `1/84` orientation sector. -/
theorem norm_add_norm_one_sub_lt_refinedSectorConfinedBase
    {u : ℂ} (hr : ‖u‖ < 1 / 4)
    (hx : 0 ≤ u.re)
    (hy : u.im ^ 2 ≤ (1 / 84 : ℝ) * u.re ^ 2) :
    ‖u‖ + ‖1 - u‖ < xiSectorRefinedBernsteinAmplitudeBase := by
  let r : ℝ := ‖u‖
  let s : ℝ := ‖1 - u‖
  let x : ℝ := u.re
  have hr0 : 0 ≤ r := norm_nonneg u
  have hs0 : 0 ≤ s := norm_nonneg (1 - u)
  have hx0 : 0 ≤ x := hx
  have hrSq : r ^ 2 = x ^ 2 + u.im ^ 2 := by
    dsimp only [r, x]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hrx : r ^ 2 ≤ (85 / 84 : ℝ) * x ^ 2 := by
    rw [hrSq]
    dsimp only [x] at hy ⊢
    nlinarith
  have hcxSq : ((9941 / 10000 : ℝ) * r) ^ 2 ≤ x ^ 2 := by
    have hconst : (9941 / 10000 : ℝ) ^ 2 * (85 / 84 : ℝ) < 1 := by
      norm_num
    nlinarith [sq_nonneg x]
  have hcx0 : 0 ≤ (9941 / 10000 : ℝ) * r := by positivity
  have hcx : (9941 / 10000 : ℝ) * r ≤ x := by
    nlinarith [sq_nonneg (x + (9941 / 10000 : ℝ) * r)]
  have hsSq : s ^ 2 = 1 - 2 * x + r ^ 2 := by
    dsimp only [s, x, r]
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im]
    ring
  have hBr : 0 < xiSectorRefinedBernsteinAmplitudeBase - r := by
    dsimp only [r] at hr ⊢
    norm_num [xiSectorRefinedBernsteinAmplitudeBase] at hr ⊢
    linarith
  have hlinear :
      2 * (xiSectorRefinedBernsteinAmplitudeBase - 9941 / 10000) * r <
        xiSectorRefinedBernsteinAmplitudeBase ^ 2 - 1 := by
    have hcoeff : 0 < xiSectorRefinedBernsteinAmplitudeBase - 9941 / 10000 := by
      norm_num [xiSectorRefinedBernsteinAmplitudeBase]
    have hconst :
        2 * (xiSectorRefinedBernsteinAmplitudeBase - 9941 / 10000) * (1 / 4 : ℝ) <
          xiSectorRefinedBernsteinAmplitudeBase ^ 2 - 1 := by
      norm_num [xiSectorRefinedBernsteinAmplitudeBase]
    nlinarith
  have hsLt : s ^ 2 < (xiSectorRefinedBernsteinAmplitudeBase - r) ^ 2 := by
    nlinarith
  have hs : s < xiSectorRefinedBernsteinAmplitudeBase - r := by
    nlinarith [sq_nonneg (s + (xiSectorRefinedBernsteinAmplitudeBase - r))]
  dsimp only [s, r] at hs ⊢
  linarith

/-- The exact radical sector ceiling.  Its proof uses the sharp square identity
`1 - (sqrt (84 / 85))^2 = 1 / 85`, rather than a decimal lower certificate. -/
theorem norm_add_norm_one_sub_lt_radicalSectorConfinedBase
    {u : ℂ} (hr : ‖u‖ < 1 / 4)
    (hx : 0 ≤ u.re)
    (hy : u.im ^ 2 ≤ (1 / 84 : ℝ) * u.re ^ 2) :
    ‖u‖ + ‖1 - u‖ < xiSectorRadicalBernsteinAmplitudeBase := by
  let r : ℝ := ‖u‖
  let s : ℝ := ‖1 - u‖
  let x : ℝ := u.re
  let c : ℝ := Real.sqrt (84 / 85 : ℝ)
  let R : ℝ := 1 / 4
  let g : ℝ := Real.sqrt (1 - 2 * c * R + R ^ 2)
  let B : ℝ := R + g
  have hr0 : 0 ≤ r := norm_nonneg u
  have hs0 : 0 ≤ s := norm_nonneg (1 - u)
  have hx0 : 0 ≤ x := hx
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    exact Real.sqrt_nonneg _
  have hcSq : c ^ 2 = 84 / 85 := by
    dsimp only [c]
    rw [Real.sq_sqrt]
    norm_num
  have hR0 : 0 ≤ R := by dsimp only [R]; norm_num
  have hcR : R < c := by
    have hsquare : R ^ 2 < c ^ 2 := by
      rw [hcSq]
      dsimp only [R]
      norm_num
    nlinarith [sq_nonneg (c + R)]
  have hcOne : c ≤ 1 := by
    nlinarith [sq_nonneg (c + 1)]
  have hrSq : r ^ 2 = x ^ 2 + u.im ^ 2 := by
    dsimp only [r, x]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hrx : r ^ 2 ≤ (85 / 84 : ℝ) * x ^ 2 := by
    rw [hrSq]
    dsimp only [x] at hy ⊢
    nlinarith
  have hcxSq : (c * r) ^ 2 ≤ x ^ 2 := by
    rw [mul_pow, hcSq]
    nlinarith
  have hcx0 : 0 ≤ c * r := mul_nonneg hc0 hr0
  have hcx : c * r ≤ x := by
    nlinarith [sq_nonneg (x + c * r)]
  have hsSq : s ^ 2 = 1 - 2 * x + r ^ 2 := by
    dsimp only [s, x, r]
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im]
    ring
  have hgSq : g ^ 2 = 1 - 2 * c * R + R ^ 2 := by
    dsimp only [g]
    rw [Real.sq_sqrt]
    dsimp only [R]
    nlinarith
  have hg0 : 0 ≤ g := by
    dsimp only [g]
    exact Real.sqrt_nonneg _
  have hcg : c - R < g := by
    have hpos : 0 ≤ c - R := by linarith
    have hsq : (c - R) ^ 2 < g ^ 2 := by
      rw [hgSq]
      dsimp only [R]
      nlinarith
    nlinarith [sq_nonneg (g + (c - R))]
  have hBc : 0 < B - c := by
    dsimp only [B]
    linarith
  have hBsq : B ^ 2 - 1 = 2 * (B - c) * R := by
    dsimp only [B]
    nlinarith [hgSq]
  have hrR : r < R := by
    dsimp only [r, R]
    exact hr
  have hlinear : 2 * (B - c) * r < B ^ 2 - 1 := by
    rw [hBsq]
    nlinarith
  have hBr : 0 < B - r := by
    dsimp only [B]
    linarith
  have hsLt : s ^ 2 < (B - r) ^ 2 := by
    nlinarith
  have hs : s < B - r := by
    nlinarith [sq_nonneg (s + (B - r))]
  have hBdef : B = xiSectorRadicalBernsteinAmplitudeBase := by
    dsimp only [B, g, c, R, xiSectorRadicalBernsteinAmplitudeBase]
    congr 1
    ring
  rw [← hBdef]
  linarith

/-- Endpoint normalization preserves the exact atomwise orientation ratio. -/
theorem xiEndpointNormalizedReciprocalSquare_orientation_sq_le
    (q : XiZeroCopy) :
    (xiEndpointNormalizedReciprocalSquare q).im ^ 2 ≤
      (1 / 84 : ℝ) * (xiEndpointNormalizedReciprocalSquare q).re ^ 2 := by
  have hR : 0 < primeArchEndpointHausdorffRadius :=
    primeArchEndpointHausdorffRadius_pos
  have h := xiThermalOrientationTerm_le_one_over_eightyFour_node_sq q
  rw [xiEndpointNormalizedReciprocalSquare]
  simp only [Complex.div_re, Complex.div_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, Complex.normSq_ofReal]
  rw [xiThermalNode] at h
  have hscaled := mul_le_mul_of_nonneg_right h
    (sq_nonneg primeArchEndpointHausdorffRadius)
  field_simp [hR.ne']
  nlinarith

/-- **Narrow-sector atom law.** Every endpoint-normalized Xi atom has Bernstein amplitude strictly
below `501/500`; line atoms have amplitude exactly one and off-line atoms use both the disk and
orientation constraints. -/
theorem xiEndpointBernsteinAtomAmplitudeBase_lt_sectorConfined
    (q : XiZeroCopy) :
    xiEndpointBernsteinAtomAmplitudeBase q <
      xiSectorConfinedBernsteinAmplitudeBase := by
  by_cases hoff : (q.1 : ℂ).re ≠ 1 / 2
  · have hr : ‖xiEndpointNormalizedReciprocalSquare q‖ < 1 / 4 :=
      (norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius q hoff).trans_lt
        xiOffLineNormalizedBernsteinRadius_lt_one_fourth
    have hx : 0 ≤ (xiEndpointNormalizedReciprocalSquare q).re := by
      have hR : 0 < primeArchEndpointHausdorffRadius :=
        primeArchEndpointHausdorffRadius_pos
      have hnode : 0 < (xiZeroCopyReciprocalSquare q).re := by
        simpa only [xiThermalNode] using xiThermalNode_pos q
      rw [xiEndpointNormalizedReciprocalSquare]
      simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        Complex.normSq_ofReal]
      positivity
    exact norm_add_norm_one_sub_lt_sectorConfinedBase hr hx
      (xiEndpointNormalizedReciprocalSquare_orientation_sq_le q)
  · have hline : (q.1 : ℂ).re = 1 / 2 := not_ne_iff.mp hoff
    rw [xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine q hline]
    exact one_lt_xiSectorConfinedBernsteinAmplitudeBase

/-- Every endpoint-normalized Xi atom obeys the tightened sector amplitude ceiling. -/
theorem xiEndpointBernsteinAtomAmplitudeBase_lt_refinedSectorConfined
    (q : XiZeroCopy) :
    xiEndpointBernsteinAtomAmplitudeBase q <
      xiSectorRefinedBernsteinAmplitudeBase := by
  by_cases hoff : (q.1 : ℂ).re ≠ 1 / 2
  · have hr : ‖xiEndpointNormalizedReciprocalSquare q‖ < 1 / 4 :=
      (norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius q hoff).trans_lt
        xiOffLineNormalizedBernsteinRadius_lt_one_fourth
    have hx : 0 ≤ (xiEndpointNormalizedReciprocalSquare q).re := by
      have hR : 0 < primeArchEndpointHausdorffRadius :=
        primeArchEndpointHausdorffRadius_pos
      have hnode : 0 < (xiZeroCopyReciprocalSquare q).re := by
        simpa only [xiThermalNode] using xiThermalNode_pos q
      rw [xiEndpointNormalizedReciprocalSquare]
      simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        Complex.normSq_ofReal]
      positivity
    exact norm_add_norm_one_sub_lt_refinedSectorConfinedBase hr hx
      (xiEndpointNormalizedReciprocalSquare_orientation_sq_le q)
  · have hline : (q.1 : ℂ).re = 1 / 2 := not_ne_iff.mp hoff
    rw [xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine q hline]
    exact one_lt_xiSectorRefinedBernsteinAmplitudeBase

/-- Every endpoint-normalized Xi atom obeys the exact radical sector amplitude ceiling. -/
theorem xiEndpointBernsteinAtomAmplitudeBase_lt_radicalSectorConfined
    (q : XiZeroCopy) :
    xiEndpointBernsteinAtomAmplitudeBase q <
      xiSectorRadicalBernsteinAmplitudeBase := by
  by_cases hoff : (q.1 : ℂ).re ≠ 1 / 2
  · have hr : ‖xiEndpointNormalizedReciprocalSquare q‖ < 1 / 4 :=
      (norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius q hoff).trans_lt
        xiOffLineNormalizedBernsteinRadius_lt_one_fourth
    have hx : 0 ≤ (xiEndpointNormalizedReciprocalSquare q).re := by
      have hR : 0 < primeArchEndpointHausdorffRadius :=
        primeArchEndpointHausdorffRadius_pos
      have hnode : 0 < (xiZeroCopyReciprocalSquare q).re := by
        simpa only [xiThermalNode] using xiThermalNode_pos q
      rw [xiEndpointNormalizedReciprocalSquare]
      simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        Complex.normSq_ofReal]
      positivity
    exact norm_add_norm_one_sub_lt_radicalSectorConfinedBase hr hx
      (xiEndpointNormalizedReciprocalSquare_orientation_sq_le q)
  · have hline : (q.1 : ℂ).re = 1 / 2 := not_ne_iff.mp hoff
    rw [xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine q hline]
    exact one_lt_xiSectorRadicalBernsteinAmplitudeBase

/-- **Sector-confined total variation.** The complete endpoint Bernstein vector has amplitude
base `501/500`. -/
theorem primeArchEndpointBernsteinTotalVariation_le_sectorConfined (n : ℕ) :
    primeArchEndpointBernsteinTotalVariation n ≤
      xiReciprocalSquareAbsoluteMass *
        xiSectorConfinedBernsteinAmplitudeBase ^ n := by
  exact primeArchEndpointBernsteinTotalVariation_le_of_atomAmplitudeBase
    xiSectorConfinedBernsteinAmplitudeBase
    (fun q => (xiEndpointBernsteinAtomAmplitudeBase_lt_sectorConfined q).le) n

/-- The complete endpoint Bernstein vector satisfies the tightened sector amplitude ceiling. -/
theorem primeArchEndpointBernsteinTotalVariation_le_refinedSectorConfined (n : ℕ) :
    primeArchEndpointBernsteinTotalVariation n ≤
      xiReciprocalSquareAbsoluteMass *
        xiSectorRefinedBernsteinAmplitudeBase ^ n := by
  exact primeArchEndpointBernsteinTotalVariation_le_of_atomAmplitudeBase
    xiSectorRefinedBernsteinAmplitudeBase
    (fun q => (xiEndpointBernsteinAtomAmplitudeBase_lt_refinedSectorConfined q).le) n

/-- The complete endpoint Bernstein vector satisfies the exact radical sector ceiling. -/
theorem primeArchEndpointBernsteinTotalVariation_le_radicalSectorConfined (n : ℕ) :
    primeArchEndpointBernsteinTotalVariation n ≤
      xiReciprocalSquareAbsoluteMass *
        xiSectorRadicalBernsteinAmplitudeBase ^ n := by
  exact primeArchEndpointBernsteinTotalVariation_le_of_atomAmplitudeBase
    xiSectorRadicalBernsteinAmplitudeBase
    (fun q => (xiEndpointBernsteinAtomAmplitudeBase_lt_radicalSectorConfined q).le) n

/-- A positive geometric total-variation ceiling yields decay at every strictly larger
normalization base. -/
theorem tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_geometric_bound
    {B r : ℝ} (hB : 0 < B)
    (hbound : ∀ n : ℕ, primeArchEndpointBernsteinTotalVariation n ≤
      xiReciprocalSquareAbsoluteMass * B ^ n)
    (hr : B < r) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinTotalVariation n / r ^ n)
      atTop (nhds 0) := by
  have hrpos : 0 < r := hB.trans hr
  let q : ℝ := B / r
  have hq0 : 0 ≤ q := div_nonneg
    hB.le hrpos.le
  have hq1 : q < 1 := (div_lt_one hrpos).2 hr
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hupper : Tendsto
      (fun n : ℕ => xiReciprocalSquareAbsoluteMass * q ^ n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpow
  apply squeeze_zero (fun n => ?_) (fun n => ?_) hupper
  · exact div_nonneg
      (show 0 ≤ primeArchEndpointBernsteinTotalVariation n by
        unfold primeArchEndpointBernsteinTotalVariation bernsteinCoefficientL1
        exact Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (pow_nonneg hrpos.le n)
  · calc
      primeArchEndpointBernsteinTotalVariation n / r ^ n ≤
          (xiReciprocalSquareAbsoluteMass *
            B ^ n) / r ^ n :=
        div_le_div_of_nonneg_right
          (hbound n)
          (pow_nonneg hrpos.le n)
      _ = xiReciprocalSquareAbsoluteMass * q ^ n := by
        dsimp only [q]
        rw [div_pow]
        ring

/-- Every exponential normalization strictly above the original sector-confined `501/500`
amplitude annihilates the complete endpoint Bernstein total variation. -/
theorem tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_sectorBase_lt
    {r : ℝ} (hr : xiSectorConfinedBernsteinAmplitudeBase < r) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinTotalVariation n / r ^ n)
      atTop (nhds 0) :=
  tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_geometric_bound
    (zero_lt_one.trans one_lt_xiSectorConfinedBernsteinAmplitudeBase)
    primeArchEndpointBernsteinTotalVariation_le_sectorConfined hr

/-- Every exponential normalization strictly above the tightened `100197/100000` sector
amplitude annihilates the complete endpoint Bernstein total variation. -/
theorem tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_refinedSectorBase_lt
    {r : ℝ} (hr : xiSectorRefinedBernsteinAmplitudeBase < r) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinTotalVariation n / r ^ n)
      atTop (nhds 0) :=
  tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_geometric_bound
    (zero_lt_one.trans one_lt_xiSectorRefinedBernsteinAmplitudeBase)
    primeArchEndpointBernsteinTotalVariation_le_refinedSectorConfined hr

/-- Every exponential normalization strictly above the exact radical sector amplitude annihilates
the complete endpoint Bernstein total variation. -/
theorem tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_radicalSectorBase_lt
    {r : ℝ} (hr : xiSectorRadicalBernsteinAmplitudeBase < r) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinTotalVariation n / r ^ n)
      atTop (nhds 0) :=
  tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_geometric_bound
    (zero_lt_one.trans one_lt_xiSectorRadicalBernsteinAmplitudeBase)
    primeArchEndpointBernsteinTotalVariation_le_radicalSectorConfined hr

/-- The positive Loschmidt purity inherits the square of the narrow-sector amplitude estimate. -/
theorem primeArchEndpointBernsteinPurity_le_sectorConfined (n : ℕ) :
    primeArchEndpointBernsteinPurity n ≤
      (xiReciprocalSquareAbsoluteMass *
        xiSectorConfinedBernsteinAmplitudeBase ^ n) ^ 2 :=
  (bernsteinCoefficientPurity_le_l1_sq _ _).trans
    ((sq_le_sq₀
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (mul_nonneg xiReciprocalSquareAbsoluteMass_nonneg
        (pow_nonneg
          (zero_le_one.trans one_lt_xiSectorConfinedBernsteinAmplitudeBase.le) n))).2
      (primeArchEndpointBernsteinTotalVariation_le_sectorConfined n))

/-- Normalization above the narrow-sector squared base kills the endpoint purity
unconditionally. -/
theorem tendsto_primeArchEndpointBernsteinPurity_div_pow_of_sectorBase_sq_lt
    {r : ℝ} (hr : xiSectorConfinedBernsteinAmplitudeBase ^ 2 < r) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
      atTop (nhds 0) := by
  have hrpos : 0 < r := lt_trans
    (sq_pos_of_pos (zero_lt_one.trans one_lt_xiSectorConfinedBernsteinAmplitudeBase)) hr
  let q : ℝ := xiSectorConfinedBernsteinAmplitudeBase ^ 2 / r
  have hq0 : 0 ≤ q := div_nonneg
    (sq_nonneg xiSectorConfinedBernsteinAmplitudeBase) hrpos.le
  have hq1 : q < 1 := (div_lt_one hrpos).2 hr
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hupper : Tendsto
      (fun n : ℕ => xiReciprocalSquareAbsoluteMass ^ 2 * q ^ n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpow
  apply squeeze_zero
    (fun n => div_nonneg (bernsteinCoefficientPurity_nonneg _ n)
      (pow_nonneg hrpos.le n))
    (fun n => ?_) hupper
  calc
    primeArchEndpointBernsteinPurity n / r ^ n ≤
        (xiReciprocalSquareAbsoluteMass *
          xiSectorConfinedBernsteinAmplitudeBase ^ n) ^ 2 / r ^ n :=
      div_le_div_of_nonneg_right
        (primeArchEndpointBernsteinPurity_le_sectorConfined n)
        (pow_nonneg hrpos.le n)
    _ = xiReciprocalSquareAbsoluteMass ^ 2 * q ^ n := by
      dsimp only [q]
      rw [div_pow]
      ring

/-- **Exact false-RH phase law.** Failure of RH forces a surviving purity exponent above one and
at most the exact narrow-sector squared base. -/
theorem exists_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ r : ℝ,
      1 < r ∧ r ≤ xiSectorConfinedBernsteinAmplitudeBase ^ 2 ∧
        ¬ Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
          atTop (nhds 0) := by
  have hnsub :
      ¬ SubexponentialSquareEnergyAtNatInfinity primeArchEndpointBernsteinPurity := by
    intro hsub
    exact hRH
      (riemannHypothesis_iff_primeArchEndpointBernsteinPurity_subexponential.mpr hsub)
  simp only [SubexponentialSquareEnergyAtNatInfinity] at hnsub
  push Not at hnsub
  obtain ⟨r, hr, hnot⟩ := hnsub
  have hrbase : r ≤ xiSectorConfinedBernsteinAmplitudeBase ^ 2 := by
    by_contra hle
    have hgt : xiSectorConfinedBernsteinAmplitudeBase ^ 2 < r := lt_of_not_ge hle
    exact hnot
      (tendsto_primeArchEndpointBernsteinPurity_div_pow_of_sectorBase_sq_lt hgt)
  exact ⟨r, hr, hrbase, hnot⟩

/-- The false-RH witness may be chosen strictly below the narrow-sector squared ceiling. -/
theorem exists_strict_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ s : ℝ,
      1 < s ∧ s < xiSectorConfinedBernsteinAmplitudeBase ^ 2 ∧
        ¬ Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / s ^ n)
          atTop (nhds 0) := by
  obtain ⟨r, hr, hrbase, hnot⟩ :=
    exists_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis hRH
  let s : ℝ := (1 + r) / 2
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hs0 : 0 < s := by dsimp only [s]; linarith
  have hones : 1 < s := by dsimp only [s]; linarith
  have hsr : s < r := by dsimp only [s]; linarith
  have hsbase : s < xiSectorConfinedBernsteinAmplitudeBase ^ 2 := hsr.trans_le hrbase
  refine ⟨s, hones, hsbase, ?_⟩
  intro hs
  have hratio0 : 0 ≤ s / r := div_nonneg hs0.le hr0.le
  have hratio1 : s / r < 1 := (div_lt_one hr0).2 hsr
  have hpow : Tendsto (fun n : ℕ => (s / r) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1
  have hprod := hs.mul hpow
  apply hnot
  convert hprod using 1
  · funext n
    simp only [div_pow]
    field_simp [hr0.ne', hs0.ne']
  · norm_num

/-- A convenient five-per-mille corollary of the exact false-RH chamber. -/
theorem exists_fivePerMille_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ r : ℝ,
      1 < r ∧ r < 201 / 200 ∧
        ¬ Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
          atTop (nhds 0) := by
  obtain ⟨r, hr, hrbase, hnot⟩ :=
    exists_strict_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis
      hRH
  exact ⟨r, hr,
    hrbase.trans
      xiSectorConfinedBernsteinAmplitudeBase_sq_lt_twoHundredOne_over_twoHundred,
    hnot⟩

/-- A weaker seven-per-mille corollary retained for downstream compatibility. -/
theorem exists_sevenPerMille_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ r : ℝ,
      1 < r ∧ r < 1007 / 1000 ∧
        ¬ Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
          atTop (nhds 0) := by
  obtain ⟨r, hr, hrbase, hnot⟩ :=
    exists_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis hRH
  exact ⟨r, hr,
    hrbase.trans_lt
      xiSectorConfinedBernsteinAmplitudeBase_sq_lt_oneThousandSeven_over_oneThousand,
    hnot⟩

/-- **Narrow-sector Loschmidt master theorem.** The endpoint purity is trapped between its
conserved polynomial floor and the exact `(501/500)^(2M)` energy ceiling.  RH is the bounded
phase; false RH is forced into the remaining five-per-mille exponential chamber. -/
theorem primeArchBernsteinSectorConfinedLoschmidtPhaseMaster :
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 = 251001 / 250000 ∧
    xiSectorConfinedBernsteinAmplitudeBase ^ 2 < 201 / 200 ∧
    (∀ n : ℕ,
      normalizedPrimeArchMoment 0 ^ 2 ≤
          (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n ∧
        primeArchEndpointBernsteinPurity n ≤
          (xiReciprocalSquareAbsoluteMass *
            xiSectorConfinedBernsteinAmplitudeBase ^ n) ^ 2) ∧
    (RiemannHypothesis ↔
      ∀ n : ℕ,
        primeArchEndpointBernsteinPurity n ≤ normalizedPrimeArchMoment 0 ^ 2) ∧
    (RiemannHypothesis ↔ PrimeArchEndpointBernsteinPurityBounded) ∧
    (¬ RiemannHypothesis →
      ∃ r : ℝ,
        1 < r ∧ r < xiSectorConfinedBernsteinAmplitudeBase ^ 2 ∧
          ¬ Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
            atTop (nhds 0)) := by
  exact ⟨
    xiSectorConfinedBernsteinAmplitudeBase_sq_eq,
    xiSectorConfinedBernsteinAmplitudeBase_sq_lt_twoHundredOne_over_twoHundred,
    fun n => ⟨mass_sq_le_card_mul_primeArchEndpointBernsteinPurity n,
      primeArchEndpointBernsteinPurity_le_sectorConfined n⟩,
    riemannHypothesis_iff_primeArchEndpointBernsteinPurity_le_mass_sq,
    riemannHypothesis_iff_primeArchEndpointBernsteinPurity_bounded,
    exists_strict_sectorConfined_primeArchEndpointBernsteinPurity_phase_of_not_riemannHypothesis⟩

end

end RHTower
