import GaloisForLFunctions.RHTower.PrimeArchBernsteinConfinedPhase
import GaloisForLFunctions.RHTower.XiOffLineQuartetThermalOrientationBound
import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyThreeSourceBudgetClosure

/-!
# Narrow-sector confinement of the prime--archimedean Bernstein phase

The disk-only Bernstein estimate loses the narrow sector forced by source-side exclusion.
The unconditional order-23 residual-annulus theorem implies, after endpoint normalization,

`im u ^ 2 < (1 / 215) * re u ^ 2`.

Together with the exact source-calibrated radius

`R = (1 - C) / (4 - C) < 1/4`,

this gives the complete-Bernstein amplitude base

`R + sqrt (1 - 2 sqrt (215 / 216) R + R^2)`.

Earlier `1/84`, rational, and radical bounds remain available as stable downstream APIs.  Failure
of RH can therefore occupy only the correspondingly narrower near-critical exponential window
above exponent one.
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

/-- Exact disk ellipse ceiling associated with radius `R` and lower cosine bound `c`. -/
def diskCosineBernsteinAmplitudeBase (R c : ℝ) : ℝ :=
  R + Real.sqrt (1 - 2 * c * R + R ^ 2)

/-- Exact quarter-disk ellipse ceiling associated with a lower cosine bound `c`. -/
def quarterDiskCosineBernsteinAmplitudeBase (c : ℝ) : ℝ :=
  1 / 4 + Real.sqrt (17 / 16 - c / 2)

/-- Strongest unconditional sector ceiling currently supplied by the order-23 source-budget
exclusion. -/
def xiOrderTwentyThreeSectorBernsteinAmplitudeBase : ℝ :=
  quarterDiskCosineBernsteinAmplitudeBase (Real.sqrt (215 / 216 : ℝ))

/-- Order-23 sector ceiling retaining the exact source-calibrated off-line radius. -/
def xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase : ℝ :=
  diskCosineBernsteinAmplitudeBase xiOffLineNormalizedBernsteinRadius
    (Real.sqrt (215 / 216 : ℝ))

/-- Boundary ray of the abstract quarter-disk and `1/84` sector constraints.  It is not
asserted to consist of actual Xi atoms; it witnesses sharpness of that geometry alone. -/
def radicalSectorBoundaryPoint (t : ℝ) : ℂ :=
  (t * Real.sqrt (84 / 85 : ℝ) : ℝ) +
    (t * Real.sqrt (1 / 85 : ℝ) : ℝ) * I

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

theorem one_lt_xiOrderTwentyThreeSectorBernsteinAmplitudeBase :
    1 < xiOrderTwentyThreeSectorBernsteinAmplitudeBase := by
  let c : ℝ := Real.sqrt (215 / 216 : ℝ)
  let g : ℝ := Real.sqrt (17 / 16 - c / 2)
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hcSq : c ^ 2 = 215 / 216 := by
    dsimp only [c]
    rw [Real.sq_sqrt]
    norm_num
  have hcOne : c < 1 := by
    nlinarith [sq_nonneg (c + 1)]
  have hgSq : g ^ 2 = 17 / 16 - c / 2 := by
    dsimp only [g]
    rw [Real.sq_sqrt]
    nlinarith
  have hg0 : 0 ≤ g := by dsimp only [g]; positivity
  have hthree : 3 / 4 < g := by
    have hsq : (3 / 4 : ℝ) ^ 2 < g ^ 2 := by
      rw [hgSq]
      nlinarith
    nlinarith [sq_nonneg (g + (3 / 4 : ℝ))]
  change 1 < 1 / 4 + g
  linarith

theorem one_lt_xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase :
    1 < xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase := by
  let R : ℝ := xiOffLineNormalizedBernsteinRadius
  let c : ℝ := Real.sqrt (215 / 216 : ℝ)
  let g : ℝ := Real.sqrt (1 - 2 * c * R + R ^ 2)
  have hR0 : 0 < R := by
    simpa only [R] using xiOffLineNormalizedBernsteinRadius_pos
  have hRQ : R < 1 / 4 := by
    simpa only [R] using xiOffLineNormalizedBernsteinRadius_lt_one_fourth
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hcSq : c ^ 2 = 215 / 216 := by
    dsimp only [c]
    rw [Real.sq_sqrt]
    norm_num
  have hcQ : 1 / 4 < c := by
    have hs : (1 / 4 : ℝ) ^ 2 < c ^ 2 := by rw [hcSq]; norm_num
    nlinarith [sq_nonneg (c + (1 / 4 : ℝ))]
  have hcOne : c < 1 := by
    nlinarith [sq_nonneg (c + 1)]
  have hrad : 0 ≤ 1 - 2 * c * R + R ^ 2 := by
    nlinarith [sq_nonneg (R - c), sq_nonneg (c + 1)]
  have hgSq : g ^ 2 = 1 - 2 * c * R + R ^ 2 := by
    dsimp only [g]
    rw [Real.sq_sqrt hrad]
  have hg0 : 0 ≤ g := by dsimp only [g]; positivity
  have hOneR : 0 < 1 - R := by linarith
  have hg : 1 - R < g := by
    have hs : (1 - R) ^ 2 < g ^ 2 := by
      rw [hgSq]
      nlinarith
    nlinarith [sq_nonneg (g + (1 - R))]
  change 1 < R + g
  linarith

/-- Retaining the exact positive source curvature strictly improves the quarter-disk ceiling. -/
theorem xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase_lt_sector :
    xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase <
      xiOrderTwentyThreeSectorBernsteinAmplitudeBase := by
  let R : ℝ := xiOffLineNormalizedBernsteinRadius
  let Q : ℝ := 1 / 4
  let c : ℝ := Real.sqrt (215 / 216 : ℝ)
  let gR : ℝ := Real.sqrt (1 - 2 * c * R + R ^ 2)
  let gQ : ℝ := Real.sqrt (1 - 2 * c * Q + Q ^ 2)
  have hR0 : 0 ≤ R := by
    simpa only [R] using xiOffLineNormalizedBernsteinRadius_pos.le
  have hRQ : R < Q := by
    simpa only [R, Q] using xiOffLineNormalizedBernsteinRadius_lt_one_fourth
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hcSq : c ^ 2 = 215 / 216 := by
    dsimp only [c]
    rw [Real.sq_sqrt]
    norm_num
  have hcQ : Q < c := by
    have hs : Q ^ 2 < c ^ 2 := by
      rw [hcSq]
      dsimp only [Q]
      norm_num
    dsimp only [Q]
    nlinarith [sq_nonneg (c + (1 / 4 : ℝ))]
  have hcOne : c < 1 := by
    nlinarith [sq_nonneg (c + 1)]
  have hradR : 0 ≤ 1 - 2 * c * R + R ^ 2 := by
    nlinarith [sq_nonneg (R - c), sq_nonneg (c + 1)]
  have hradQ : 0 ≤ 1 - 2 * c * Q + Q ^ 2 := by
    nlinarith [sq_nonneg (Q - c), sq_nonneg (c + 1)]
  have hgRSq : gR ^ 2 = 1 - 2 * c * R + R ^ 2 := by
    dsimp only [gR]
    rw [Real.sq_sqrt hradR]
  have hgQSq : gQ ^ 2 = 1 - 2 * c * Q + Q ^ 2 := by
    dsimp only [gQ]
    rw [Real.sq_sqrt hradQ]
  have hgR0 : 0 ≤ gR := by dsimp only [gR]; positivity
  have hgQ0 : 0 ≤ gQ := by dsimp only [gQ]; positivity
  have hcgQ : c - Q < gQ := by
    have hpos : 0 ≤ c - Q := by linarith
    have hs : (c - Q) ^ 2 < gQ ^ 2 := by
      rw [hgQSq]
      nlinarith
    nlinarith [sq_nonneg (gQ + (c - Q))]
  have hbase : R + gR < Q + gQ := by
    by_contra hnot
    have hle : gQ + (Q - R) ≤ gR := by linarith
    have hleft0 : 0 ≤ gQ + (Q - R) := by linarith
    have hsq : (gQ + (Q - R)) ^ 2 ≤ gR ^ 2 :=
      (sq_le_sq₀ hleft0 hgR0).2 hle
    nlinarith
  have hradEq : 1 - 2 * c * Q + Q ^ 2 = 17 / 16 - c / 2 := by
    dsimp only [Q]
    ring
  dsimp only [gQ] at hbase
  rw [hradEq] at hbase
  simpa only [xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase,
    diskCosineBernsteinAmplitudeBase, R, c, gR,
    xiOrderTwentyThreeSectorBernsteinAmplitudeBase,
    quarterDiskCosineBernsteinAmplitudeBase, Q] using hbase

/-- The globally excluded order-23 residual annulus supplies a strictly narrower sector than the
earlier quartet-height estimate. -/
theorem xiOrderTwentyThreeSectorBernsteinAmplitudeBase_lt_radical :
    xiOrderTwentyThreeSectorBernsteinAmplitudeBase <
      xiSectorRadicalBernsteinAmplitudeBase := by
  let cNew : ℝ := Real.sqrt (215 / 216 : ℝ)
  let cOld : ℝ := Real.sqrt (84 / 85 : ℝ)
  let gNew : ℝ := Real.sqrt (17 / 16 - cNew / 2)
  let gOld : ℝ := Real.sqrt (17 / 16 - cOld / 2)
  have hcNew0 : 0 ≤ cNew := by dsimp only [cNew]; positivity
  have hcOld0 : 0 ≤ cOld := by dsimp only [cOld]; positivity
  have hcNewSq : cNew ^ 2 = 215 / 216 := by
    dsimp only [cNew]
    rw [Real.sq_sqrt]
    norm_num
  have hcOldSq : cOld ^ 2 = 84 / 85 := by
    dsimp only [cOld]
    rw [Real.sq_sqrt]
    norm_num
  have hc : cOld < cNew := by
    have hs : cOld ^ 2 < cNew ^ 2 := by
      rw [hcOldSq, hcNewSq]
      norm_num
    nlinarith [sq_nonneg (cOld + cNew)]
  have hgNewSq : gNew ^ 2 = 17 / 16 - cNew / 2 := by
    dsimp only [gNew]
    rw [Real.sq_sqrt]
    nlinarith
  have hgOldSq : gOld ^ 2 = 17 / 16 - cOld / 2 := by
    dsimp only [gOld]
    rw [Real.sq_sqrt]
    nlinarith
  have hgNew0 : 0 ≤ gNew := by dsimp only [gNew]; positivity
  have hgOld0 : 0 ≤ gOld := by dsimp only [gOld]; positivity
  have hg : gNew < gOld := by
    have hs : gNew ^ 2 < gOld ^ 2 := by
      rw [hgNewSq, hgOldSq]
      linarith
    nlinarith [sq_nonneg (gNew + gOld)]
  change 1 / 4 + gNew < 1 / 4 + gOld
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

/-- Generic disk ellipse bound. Strictness may come from either the radius or cosine input. -/
theorem norm_add_norm_one_sub_lt_diskCosineBase
    {u : ℂ} {R c : ℝ} (hR0 : 0 ≤ R) (hRc : R < c) (hcOne : c < 1)
    (hr : ‖u‖ ≤ R) (hcos : c * ‖u‖ ≤ u.re)
    (hstrict : ‖u‖ < R ∨ c * ‖u‖ < u.re) :
    ‖u‖ + ‖1 - u‖ < diskCosineBernsteinAmplitudeBase R c := by
  let r : ℝ := ‖u‖
  let s : ℝ := ‖1 - u‖
  let x : ℝ := u.re
  let g : ℝ := Real.sqrt (1 - 2 * c * R + R ^ 2)
  let B : ℝ := R + g
  have hr0 : 0 ≤ r := norm_nonneg u
  have hs0 : 0 ≤ s := norm_nonneg (1 - u)
  have hc0 : 0 ≤ c := by linarith
  have hcx : c * r ≤ x := by simpa only [r, x] using hcos
  have hrad : 0 ≤ 1 - 2 * c * R + R ^ 2 := by
    nlinarith [sq_nonneg (R - c), sq_nonneg (c + 1)]
  have hgSq : g ^ 2 = 1 - 2 * c * R + R ^ 2 := by
    dsimp only [g]
    rw [Real.sq_sqrt hrad]
  have hg0 : 0 ≤ g := by
    dsimp only [g]
    exact Real.sqrt_nonneg _
  have hcSq : c ^ 2 < 1 := by
    nlinarith [sq_nonneg (c + 1)]
  have hcg : c - R < g := by
    have hpos : 0 ≤ c - R := by linarith
    have hsq : (c - R) ^ 2 < g ^ 2 := by
      rw [hgSq]
      nlinarith
    nlinarith [sq_nonneg (g + (c - R))]
  have hBc : 0 < B - c := by
    dsimp only [B]
    linarith
  have hBsq : B ^ 2 - 1 = 2 * (B - c) * R := by
    dsimp only [B]
    nlinarith [hgSq]
  have hlinear : 2 * (B - c) * r ≤ B ^ 2 - 1 := by
    rw [hBsq]
    nlinarith
  have hBr : 0 < B - r := by
    dsimp only [B, r] at hr ⊢
    linarith
  have hsSq : s ^ 2 = 1 - 2 * x + r ^ 2 := by
    dsimp only [s, x, r]
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm,
      Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im]
    ring
  have hsLt : s ^ 2 < (B - r) ^ 2 := by
    rcases hstrict with hradStrict | hcosStrict
    · have hlinearStrict : 2 * (B - c) * r < B ^ 2 - 1 := by
        rw [hBsq]
        nlinarith
      nlinarith
    · have hcxStrict : c * r < x := by
        simpa only [r, x] using hcosStrict
      nlinarith
  have hs : s < B - r := by
    nlinarith [sq_nonneg (s + (B - r))]
  have hBdef : B = diskCosineBernsteinAmplitudeBase R c := by
    rfl
  rw [← hBdef]
  linarith

/-- Quarter-disk specialization of the generic two-focus geometry. -/
theorem norm_add_norm_one_sub_lt_quarterDiskCosineBase
    {u : ℂ} {c : ℝ} (hcR : 1 / 4 < c) (hcOne : c < 1)
    (hr : ‖u‖ < 1 / 4) (hcos : c * ‖u‖ ≤ u.re) :
    ‖u‖ + ‖1 - u‖ < quarterDiskCosineBernsteinAmplitudeBase c := by
  have hbase : diskCosineBernsteinAmplitudeBase (1 / 4) c =
      quarterDiskCosineBernsteinAmplitudeBase c := by
    unfold diskCosineBernsteinAmplitudeBase quarterDiskCosineBernsteinAmplitudeBase
    congr 1
    ring
  rw [← hbase]
  exact norm_add_norm_one_sub_lt_diskCosineBase (by norm_num) hcR hcOne hr.le hcos
    (Or.inl hr)

/-- The exact radical sector ceiling.  Its source-specific part is the `1/84` orientation
certificate; generic ellipse geometry is delegated to `norm_add_norm_one_sub_lt_quarterDiskCosineBase`. -/
theorem norm_add_norm_one_sub_lt_radicalSectorConfinedBase
    {u : ℂ} (hr : ‖u‖ < 1 / 4)
    (hx : 0 ≤ u.re)
    (hy : u.im ^ 2 ≤ (1 / 84 : ℝ) * u.re ^ 2) :
    ‖u‖ + ‖1 - u‖ < xiSectorRadicalBernsteinAmplitudeBase := by
  let r : ℝ := ‖u‖
  let x : ℝ := u.re
  let c : ℝ := Real.sqrt (84 / 85 : ℝ)
  have hr0 : 0 ≤ r := norm_nonneg u
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    exact Real.sqrt_nonneg _
  have hcSq : c ^ 2 = 84 / 85 := by
    dsimp only [c]
    rw [Real.sq_sqrt]
    norm_num
  have hcR : 1 / 4 < c := by
    have hsquare : (1 / 4 : ℝ) ^ 2 < c ^ 2 := by
      rw [hcSq]
      norm_num
    nlinarith [sq_nonneg (c + (1 / 4 : ℝ))]
  have hcOne : c < 1 := by
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
  simpa only [c, r, x, quarterDiskCosineBernsteinAmplitudeBase,
    diskCosineBernsteinAmplitudeBase,
    xiSectorRadicalBernsteinAmplitudeBase] using
    norm_add_norm_one_sub_lt_quarterDiskCosineBase hcR hcOne hr hcx

/-- The boundary-ray norm equals its nonnegative real parameter. -/
theorem norm_radicalSectorBoundaryPoint (t : ℝ) (ht : 0 ≤ t) :
    ‖radicalSectorBoundaryPoint t‖ = t := by
  let a : ℝ := Real.sqrt (84 / 85 : ℝ)
  let b : ℝ := Real.sqrt (1 / 85 : ℝ)
  have haSq : a ^ 2 = 84 / 85 := by
    dsimp only [a]
    rw [Real.sq_sqrt]
    norm_num
  have hbSq : b ^ 2 = 1 / 85 := by
    dsimp only [b]
    rw [Real.sq_sqrt]
    norm_num
  have hab : a ^ 2 + b ^ 2 = 1 := by
    rw [haSq, hbSq]
    norm_num
  dsimp only [a, b] at hab
  have hsq : ‖radicalSectorBoundaryPoint t‖ ^ 2 = t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [radicalSectorBoundaryPoint, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, zero_sub,
      add_zero, zero_add, mul_one]
    change (t * a) * (t * a) + (t * b) * (t * b) = t ^ 2
    nlinarith [hab]
  have hn : 0 ≤ ‖radicalSectorBoundaryPoint t‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖radicalSectorBoundaryPoint t‖ + t)]

/-- The second focus distance on the boundary ray has the exact radical form. -/
theorem norm_one_sub_radicalSectorBoundaryPoint (t : ℝ) :
    ‖1 - radicalSectorBoundaryPoint t‖ =
      Real.sqrt (1 - 2 * Real.sqrt (84 / 85 : ℝ) * t + t ^ 2) := by
  let a : ℝ := Real.sqrt (84 / 85 : ℝ)
  let b : ℝ := Real.sqrt (1 / 85 : ℝ)
  have haSq : a ^ 2 = 84 / 85 := by
    dsimp only [a]
    rw [Real.sq_sqrt]
    norm_num
  have hbSq : b ^ 2 = 1 / 85 := by
    dsimp only [b]
    rw [Real.sq_sqrt]
    norm_num
  have hab : a ^ 2 + b ^ 2 = 1 := by
    rw [haSq, hbSq]
    norm_num
  dsimp only [a, b] at hab
  rw [Complex.norm_def]
  congr 1
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    radicalSectorBoundaryPoint, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, zero_mul, zero_sub, add_zero, zero_add, mul_one]
  change (1 - t * a) * (1 - t * a) + (-(t * b)) * (-(t * b)) =
    1 - 2 * a * t + t ^ 2
  nlinarith [hab]

/-- Every nonnegative parameter strictly below the quarter-disk radius is admissible for the
abstract sector geometry. -/
theorem radicalSectorBoundaryPoint_admissible {t : ℝ} (ht0 : 0 ≤ t) (htR : t < 1 / 4) :
    ‖radicalSectorBoundaryPoint t‖ < 1 / 4 ∧
      0 ≤ (radicalSectorBoundaryPoint t).re ∧
      (radicalSectorBoundaryPoint t).im ^ 2 ≤
        (1 / 84 : ℝ) * (radicalSectorBoundaryPoint t).re ^ 2 := by
  let a : ℝ := Real.sqrt (84 / 85 : ℝ)
  let b : ℝ := Real.sqrt (1 / 85 : ℝ)
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact Real.sqrt_nonneg _
  have haSq : a ^ 2 = 84 / 85 := by
    dsimp only [a]
    rw [Real.sq_sqrt]
    norm_num
  have hbSq : b ^ 2 = 1 / 85 := by
    dsimp only [b]
    rw [Real.sq_sqrt]
    norm_num
  have hratio : b ^ 2 = (1 / 84 : ℝ) * a ^ 2 := by
    rw [haSq, hbSq]
    norm_num
  refine ⟨(norm_radicalSectorBoundaryPoint t ht0).trans_lt htR, ?_, ?_⟩
  · simp only [radicalSectorBoundaryPoint, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, zero_sub,
      add_zero, zero_add, mul_one]
    change 0 ≤ t * a
    exact mul_nonneg ht0 ha0
  · simp only [radicalSectorBoundaryPoint, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul, zero_sub,
      add_zero, zero_add, mul_one]
    change (t * b) ^ 2 ≤ (1 / 84 : ℝ) * (t * a) ^ 2
    calc
      (t * b) ^ 2 = t ^ 2 * b ^ 2 := by ring
      _ = t ^ 2 * ((1 / 84 : ℝ) * a ^ 2) := by rw [hratio]
      _ ≤ (1 / 84 : ℝ) * (t * a) ^ 2 := le_of_eq (by ring)

/-- The abstract boundary ray varies continuously. -/
theorem continuous_radicalSectorBoundaryPoint : Continuous radicalSectorBoundaryPoint := by
  unfold radicalSectorBoundaryPoint
  fun_prop

/-- The admissible boundary ray approaches exactly the radical sector ceiling from inside the
quarter disk.  Hence no argument using only these abstract geometric constraints can lower that
uniform ceiling. -/
theorem radicalSectorBoundaryPoint_tendsto_amplitude :
    Tendsto (fun t : ℝ => ‖radicalSectorBoundaryPoint t‖ + ‖1 - radicalSectorBoundaryPoint t‖)
      (nhdsWithin (1 / 4 : ℝ) (Set.Iio (1 / 4 : ℝ)))
      (nhds xiSectorRadicalBernsteinAmplitudeBase) := by
  let f : ℝ → ℝ := fun t =>
    ‖radicalSectorBoundaryPoint t‖ + ‖1 - radicalSectorBoundaryPoint t‖
  have hf : Continuous f := by
    exact (continuous_norm.comp continuous_radicalSectorBoundaryPoint).add
      (continuous_norm.comp (continuous_const.sub continuous_radicalSectorBoundaryPoint))
  have hvalue : f (1 / 4 : ℝ) = xiSectorRadicalBernsteinAmplitudeBase := by
    dsimp only [f]
    rw [norm_radicalSectorBoundaryPoint (1 / 4 : ℝ) (by norm_num),
      norm_one_sub_radicalSectorBoundaryPoint]
    simp only [xiSectorRadicalBernsteinAmplitudeBase]
    ring
  rw [← hvalue]
  exact (hf.tendsto (1 / 4 : ℝ)).mono_left
    (nhdsWithin_le_nhds : nhdsWithin (1 / 4 : ℝ) (Set.Iio (1 / 4 : ℝ)) ≤ nhds (1 / 4 : ℝ))

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

/-- Order-23 source-budget closure removes every possible failure of the `215` sector ratio. -/
theorem xiZeroCopy_orderTwentyThree_global_sector_ratio
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    215 * (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 <
      ((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) ^ 2 := by
  by_contra hnot
  have hfail := not_lt.mp hnot
  exact xiCenteredOrderTwentyThreeResidualAnnulusEmpty
    ⟨q, xiCenteredOrderTwentyThreeSectorFailure_mem_residualAnnulus q hoff hfail⟩

/-- The global order-23 sector ratio transfers through the common reciprocal-square denominator. -/
theorem xiZeroCopyReciprocalSquare_orderTwentyThree_orientation_sq_lt
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 <
      (1 / 215 : ℝ) * (xiZeroCopyReciprocalSquare q).re ^ 2 := by
  let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
  let v : ℝ := (q.1 : ℂ).im ^ 2
  let D : ℝ := (u + v) ^ 2
  have hu0 : 0 ≤ u := by dsimp only [u]; positivity
  have hv : 85 < v := by
    simpa only [v] using xiZeroCopy_offLine_eightyFive_lt_im_sq q hoff
  have hv0 : 0 < v := by linarith
  have hD : 0 < D := by dsimp only [D]; positivity
  have hsector := xiZeroCopy_orderTwentyThree_global_sector_ratio q hoff
  have hprod :
      (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 = 4 * u * v := by
    dsimp only [u, v]
    ring
  have hsector' : 215 * (4 * u * v) < (v - u) ^ 2 := by
    rw [← hprod]
    simpa only [u, v] using hsector
  rw [xiZeroCopyReciprocalSquare_re_formula,
    xiZeroCopyReciprocalSquare_im_formula]
  change (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im /
        (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2 <
    (1 / 215 : ℝ) *
      (((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) /
        (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2
  rw [show ((q.1 : ℂ).re - 1 / 2) ^ 2 = u by rfl,
    show (q.1 : ℂ).im ^ 2 = v by rfl,
    show (u + v) ^ 2 = D by rfl]
  rw [div_pow, div_pow]
  rw [show (1 / 215 : ℝ) * ((v - u) ^ 2 / D ^ 2) =
      ((1 / 215 : ℝ) * (v - u) ^ 2) / D ^ 2 by ring]
  apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hD)).2
  rw [hprod]
  nlinarith

/-- Positive endpoint normalization preserves the strict order-23 orientation sector. -/
theorem xiEndpointNormalizedReciprocalSquare_orderTwentyThree_orientation_sq_lt
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    (xiEndpointNormalizedReciprocalSquare q).im ^ 2 <
      (1 / 215 : ℝ) * (xiEndpointNormalizedReciprocalSquare q).re ^ 2 := by
  have hR : 0 < primeArchEndpointHausdorffRadius :=
    primeArchEndpointHausdorffRadius_pos
  have h := xiZeroCopyReciprocalSquare_orderTwentyThree_orientation_sq_lt q hoff
  rw [xiEndpointNormalizedReciprocalSquare]
  simp only [Complex.div_re, Complex.div_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, Complex.normSq_ofReal]
  have hscaled := mul_lt_mul_of_pos_right h
    (sq_pos_of_pos primeArchEndpointHausdorffRadius_pos)
  field_simp [hR.ne']
  nlinarith

/-- The strict order-23 orientation sector is exactly a strict normalized cosine bound. -/
theorem xiEndpointNormalizedReciprocalSquare_orderTwentyThree_cosine_lt
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    Real.sqrt (215 / 216 : ℝ) * ‖xiEndpointNormalizedReciprocalSquare q‖ <
      (xiEndpointNormalizedReciprocalSquare q).re := by
  let z : ℂ := xiEndpointNormalizedReciprocalSquare q
  let c : ℝ := Real.sqrt (215 / 216 : ℝ)
  have hx : 0 < z.re := by
    have hR : 0 < primeArchEndpointHausdorffRadius :=
      primeArchEndpointHausdorffRadius_pos
    have hnode : 0 < (xiZeroCopyReciprocalSquare q).re := by
      simpa only [xiThermalNode] using xiThermalNode_pos q
    dsimp only [z, xiEndpointNormalizedReciprocalSquare]
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      Complex.normSq_ofReal]
    positivity
  have hy : z.im ^ 2 < (1 / 215 : ℝ) * z.re ^ 2 := by
    simpa only [z] using
      xiEndpointNormalizedReciprocalSquare_orderTwentyThree_orientation_sq_lt q hoff
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hcSq : c ^ 2 = 215 / 216 := by
    dsimp only [c]
    rw [Real.sq_sqrt]
    norm_num
  have hrSq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hrx : ‖z‖ ^ 2 < (216 / 215 : ℝ) * z.re ^ 2 := by
    rw [hrSq]
    nlinarith
  have hcxSq : (c * ‖z‖) ^ 2 < z.re ^ 2 := by
    rw [mul_pow, hcSq]
    nlinarith
  have hcx0 : 0 ≤ c * ‖z‖ := mul_nonneg hc0 (norm_nonneg z)
  have hcx : c * ‖z‖ < z.re := by
    nlinarith [sq_nonneg (z.re + c * ‖z‖)]
  simpa only [z, c] using hcx

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

/-- The order-23 source-budget exclusion improves the endpoint atom sector from `1/84` to the
strict ratio `1/215`. -/
theorem xiEndpointBernsteinAtomAmplitudeBase_lt_orderTwentyThreeSectorConfined
    (q : XiZeroCopy) :
    xiEndpointBernsteinAtomAmplitudeBase q <
      xiOrderTwentyThreeSectorBernsteinAmplitudeBase := by
  by_cases hoff : (q.1 : ℂ).re ≠ 1 / 2
  · let z : ℂ := xiEndpointNormalizedReciprocalSquare q
    let c : ℝ := Real.sqrt (215 / 216 : ℝ)
    have hr : ‖z‖ < 1 / 4 :=
      (norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius q hoff).trans_lt
        xiOffLineNormalizedBernsteinRadius_lt_one_fourth
    have hcSq : c ^ 2 = 215 / 216 := by
      dsimp only [c]
      rw [Real.sq_sqrt]
      norm_num
    have hc0 : 0 ≤ c := by dsimp only [c]; positivity
    have hcR : 1 / 4 < c := by
      have hs : (1 / 4 : ℝ) ^ 2 < c ^ 2 := by
        rw [hcSq]
        norm_num
      nlinarith [sq_nonneg (c + (1 / 4 : ℝ))]
    have hcOne : c < 1 := by
      nlinarith [sq_nonneg (c + 1)]
    have hcx : c * ‖z‖ < z.re := by
      simpa only [c, z] using
        xiEndpointNormalizedReciprocalSquare_orderTwentyThree_cosine_lt q hoff
    simpa only [xiEndpointBernsteinAtomAmplitudeBase, z,
      xiOrderTwentyThreeSectorBernsteinAmplitudeBase] using
      norm_add_norm_one_sub_lt_quarterDiskCosineBase hcR hcOne hr hcx.le
  · have hline : (q.1 : ℂ).re = 1 / 2 := not_ne_iff.mp hoff
    rw [xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine q hline]
    exact one_lt_xiOrderTwentyThreeSectorBernsteinAmplitudeBase

/-- Every endpoint-normalized Xi atom obeys the exact source-calibrated order-23 ceiling. -/
theorem xiEndpointBernsteinAtomAmplitudeBase_lt_orderTwentyThreeCurvatureConfined
    (q : XiZeroCopy) :
    xiEndpointBernsteinAtomAmplitudeBase q <
      xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase := by
  by_cases hoff : (q.1 : ℂ).re ≠ 1 / 2
  · let z : ℂ := xiEndpointNormalizedReciprocalSquare q
    let R : ℝ := xiOffLineNormalizedBernsteinRadius
    let c : ℝ := Real.sqrt (215 / 216 : ℝ)
    have hR0 : 0 ≤ R := by
      simpa only [R] using xiOffLineNormalizedBernsteinRadius_pos.le
    have hRQ : R < 1 / 4 := by
      simpa only [R] using xiOffLineNormalizedBernsteinRadius_lt_one_fourth
    have hr : ‖z‖ ≤ R := by
      simpa only [z, R] using
        norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius q hoff
    have hcSq : c ^ 2 = 215 / 216 := by
      dsimp only [c]
      rw [Real.sq_sqrt]
      norm_num
    have hc0 : 0 ≤ c := by dsimp only [c]; positivity
    have hcQ : 1 / 4 < c := by
      have hs : (1 / 4 : ℝ) ^ 2 < c ^ 2 := by rw [hcSq]; norm_num
      nlinarith [sq_nonneg (c + (1 / 4 : ℝ))]
    have hcOne : c < 1 := by
      nlinarith [sq_nonneg (c + 1)]
    have hcx : c * ‖z‖ < z.re := by
      simpa only [c, z] using
        xiEndpointNormalizedReciprocalSquare_orderTwentyThree_cosine_lt q hoff
    simpa only [xiEndpointBernsteinAtomAmplitudeBase, z,
      xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase, R, c] using
      norm_add_norm_one_sub_lt_diskCosineBase hR0 (hRQ.trans hcQ) hcOne hr hcx.le
        (Or.inr hcx)
  · have hline : (q.1 : ℂ).re = 1 / 2 := not_ne_iff.mp hoff
    rw [xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine q hline]
    exact one_lt_xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase

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

/-- The complete endpoint Bernstein vector satisfies the unconditional order-23 sector ceiling. -/
theorem primeArchEndpointBernsteinTotalVariation_le_orderTwentyThreeSectorConfined (n : ℕ) :
    primeArchEndpointBernsteinTotalVariation n ≤
      xiReciprocalSquareAbsoluteMass *
        xiOrderTwentyThreeSectorBernsteinAmplitudeBase ^ n := by
  exact primeArchEndpointBernsteinTotalVariation_le_of_atomAmplitudeBase
    xiOrderTwentyThreeSectorBernsteinAmplitudeBase
    (fun q =>
      (xiEndpointBernsteinAtomAmplitudeBase_lt_orderTwentyThreeSectorConfined q).le) n

/-- The complete endpoint Bernstein vector retains the exact source-calibrated off-line radius. -/
theorem primeArchEndpointBernsteinTotalVariation_le_orderTwentyThreeCurvatureConfined (n : ℕ) :
    primeArchEndpointBernsteinTotalVariation n ≤
      xiReciprocalSquareAbsoluteMass *
        xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase ^ n := by
  exact primeArchEndpointBernsteinTotalVariation_le_of_atomAmplitudeBase
    xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase
    (fun q =>
      (xiEndpointBernsteinAtomAmplitudeBase_lt_orderTwentyThreeCurvatureConfined q).le) n

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

/-- Every exponential normalization strictly above the unconditional order-23 sector amplitude
annihilates the complete endpoint Bernstein total variation. -/
theorem
    tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_orderTwentyThreeSectorBase_lt
    {r : ℝ} (hr : xiOrderTwentyThreeSectorBernsteinAmplitudeBase < r) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinTotalVariation n / r ^ n)
      atTop (nhds 0) :=
  tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_geometric_bound
    (zero_lt_one.trans one_lt_xiOrderTwentyThreeSectorBernsteinAmplitudeBase)
    primeArchEndpointBernsteinTotalVariation_le_orderTwentyThreeSectorConfined hr

/-- Every exponential normalization strictly above the source-calibrated order-23 amplitude
annihilates the complete endpoint Bernstein total variation. -/
theorem
    tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_orderTwentyThreeCurvatureBase_lt
    {r : ℝ} (hr : xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase < r) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinTotalVariation n / r ^ n)
      atTop (nhds 0) :=
  tendsto_primeArchEndpointBernsteinTotalVariation_div_pow_of_geometric_bound
    (zero_lt_one.trans one_lt_xiOrderTwentyThreeCurvatureBernsteinAmplitudeBase)
    primeArchEndpointBernsteinTotalVariation_le_orderTwentyThreeCurvatureConfined hr

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
