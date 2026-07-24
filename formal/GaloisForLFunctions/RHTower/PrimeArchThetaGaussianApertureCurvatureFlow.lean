import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureCompositeWindow
import GaloisForLFunctions.RHTower.PrimeArchThetaLiouvilleWard
import GaloisForLFunctions.RHTower.PrimeArchThetaModularDifferentialClosure
import GaloisForLFunctions.HTGeometry.AffineGammaMomentCurvature

/-!
# Gaussian-aperture curvature flow

The Gaussian aperture does more than supply a one-parameter family of moment inequalities.  Its
gamma-normalized adjacent ratios satisfy an autonomous discrete flow.  The boundary second
difference consumed by GABTC therefore has an exact parabolic-reaction law.  At a zero of the
curvature at level `j`, the reaction term disappears and the surviving derivative is

`4 (q_j-q_(j+1))^2 + (j+7/2) q_(j+2) S_(j+1)`.

Thus nonnegative curvature one level higher is a forward barrier against loss of curvature at the
current level.  This identifies the genuinely infinite part of GABTC: a first failure cannot be
born at a finite level whose successor remains nonnegative; it must enter through the large-degree
boundary.  The generic algebra is the affine-Gamma moment-curvature law from `HTGeometry`; this
module verifies the literal completed theta moment shift and specializes that universal theorem,
rather than assuming a moment flow.
-/

open Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Gamma shape attached to the `j`-th even half moment. -/
def thetaCuspGaussianApertureGammaShape (j : ℕ) : ℝ :=
  (j : ℝ) + 1 / 2

/-! ### The common cold-aperture seam coefficient -/

private theorem thetaCuspSourceTerm_zero_nonneg_for_cold_seam (n : ℕ) :
    0 ≤ thetaCuspSourceTerm 0 n := by
  cases n with
  | zero => simp [thetaCuspSourceTerm, thetaCuspSeed]
  | succ n =>
      have hn : (1 : ℝ) ≤ n.succ := by exact_mod_cast n.succ_pos
      have hseed : 0 < thetaCuspSeed (n.succ : ℝ) := by
        apply thetaCuspSeed_pos
        nlinarith [Real.pi_gt_three]
      simpa [thetaCuspSourceTerm] using hseed.le

theorem thetaCuspFullSource_zero_pos_for_cold_seam :
    0 < thetaCuspFullSource 0 := by
  rw [thetaCuspFullSource]
  exact (summable_thetaCuspSourceTerm 0).tsum_pos
    thetaCuspSourceTerm_zero_nonneg_for_cold_seam 1
    thetaCuspSourceTerm_one_zero_pos

/-- Quadratic Taylor coefficient of the completed source, normalized by its seam value. -/
def thetaCuspGaussianApertureColdJetOne : ℝ :=
  iteratedDeriv 2 thetaCuspFullSource 0 / (2 * thetaCuspFullSource 0)

/-- Quartic Taylor coefficient of the completed source, normalized by its seam value. -/
def thetaCuspGaussianApertureColdJetTwo : ℝ :=
  iteratedDeriv 4 thetaCuspFullSource 0 / (24 * thetaCuspFullSource 0)

/-- Sixth Taylor coefficient of the completed source, normalized by its seam value. -/
def thetaCuspGaussianApertureColdJetThree : ℝ :=
  iteratedDeriv 6 thetaCuspFullSource 0 / (720 * thetaCuspFullSource 0)

/-- Third correction coefficient in the cold-aperture expansion of the `j`-th normalized adjacent
moment ratio.  Its second degree difference is the first term not killed by Gaussian rigidity. -/
def thetaCuspGaussianApertureColdRatioCorrectionThree (j : ℕ) : ℝ :=
  let a := thetaCuspGaussianApertureGammaShape j
  let c1 := thetaCuspGaussianApertureColdJetOne
  let c2 := thetaCuspGaussianApertureColdJetTwo
  let c3 := thetaCuspGaussianApertureColdJetThree
  a ^ 2 * c1 ^ 3 - 3 * a ^ 2 * c1 * c2 + 3 * a ^ 2 * c3 -
    3 * a * c1 * c2 + 9 * a * c3 + 6 * c3

/-- **All-fixed-degree seam law.**  The first non-Gaussian cold-aperture curvature coefficient is
independent of degree and is exactly the completed sixth-seam numerator.  Analytically, Watson
localization multiplies this coefficient by `L⁻⁴`; this theorem closes the exact algebraic
coefficient calculation for every fixed `j`. -/
theorem thetaCuspGaussianApertureColdRatioCorrectionThree_secondDiff
    (j : ℕ) :
    thetaCuspGaussianApertureColdRatioCorrectionThree j -
        2 * thetaCuspGaussianApertureColdRatioCorrectionThree (j + 1) +
        thetaCuspGaussianApertureColdRatioCorrectionThree (j + 2) =
      thetaCuspGaussianApertureSixthSeamNumerator /
        (120 * thetaCuspFullSource 0 ^ 3) := by
  have hf0 : thetaCuspFullSource 0 ≠ 0 :=
    thetaCuspFullSource_zero_pos_for_cold_seam.ne'
  simp only [thetaCuspGaussianApertureColdRatioCorrectionThree,
    thetaCuspGaussianApertureColdJetOne,
    thetaCuspGaussianApertureColdJetTwo,
    thetaCuspGaussianApertureColdJetThree,
    thetaCuspGaussianApertureGammaShape,
    thetaCuspGaussianApertureSixthSeamNumerator]
  field_simp [hf0]
  push_cast
  ring

/-- The first non-Gaussian cold-aperture curvature coefficient is strictly positive in every
fixed moment degree. -/
theorem thetaCuspGaussianApertureColdRatioCorrectionThree_secondDiff_pos
    (j : ℕ) :
    0 <
      thetaCuspGaussianApertureColdRatioCorrectionThree j -
        2 * thetaCuspGaussianApertureColdRatioCorrectionThree (j + 1) +
        thetaCuspGaussianApertureColdRatioCorrectionThree (j + 2) := by
  rw [thetaCuspGaussianApertureColdRatioCorrectionThree_secondDiff]
  exact div_pos thetaCuspGaussianApertureSixthSeamNumerator_pos
    (mul_pos (by norm_num)
      (pow_pos thetaCuspFullSource_zero_pos_for_cold_seam 3))

/-! ### The large-degree theta saddle -/

/-- Leading moment degree selected by the exact double-exponential tail of the first theta atom.
It is the stationary-phase relation `j = π x exp(2x)` for the factor
`x^(2j) exp(-π exp(2x))`. -/
def thetaCuspGaussianApertureTailSaddleDegree (x : ℝ) : ℝ :=
  Real.pi * x * Real.exp (2 * x)

/-- Leading gamma-normalized adjacent-ratio profile at saddle height `x`. -/
def thetaCuspGaussianApertureTailSaddleRatio (x : ℝ) : ℝ :=
  x / (Real.pi * Real.exp (2 * x))

/-- First derivative of the saddle ratio with respect to the saddle degree. -/
def thetaCuspGaussianApertureTailSaddleRatioDegreeSlope (x : ℝ) : ℝ :=
  (1 - 2 * x) /
    (Real.pi ^ 2 * Real.exp (4 * x) * (1 + 2 * x))

/-- Second derivative of the saddle ratio with respect to the saddle degree. -/
def thetaCuspGaussianApertureTailSaddleRatioDegreeCurvature (x : ℝ) : ℝ :=
  8 * (2 * x ^ 2 - 1) /
    (Real.pi ^ 3 * Real.exp (6 * x) * (1 + 2 * x) ^ 3)

theorem hasDerivAt_thetaCuspGaussianApertureTailSaddleDegree (x : ℝ) :
    HasDerivAt thetaCuspGaussianApertureTailSaddleDegree
      (Real.pi * Real.exp (2 * x) * (1 + 2 * x)) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (2 * y))
      (2 * Real.exp (2 * x)) x := by
    convert (Real.hasDerivAt_exp (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1
    all_goals ring
  convert ((hasDerivAt_id x).const_mul Real.pi).mul hexp using 1
  simp only [id_eq]
  ring

theorem hasDerivAt_thetaCuspGaussianApertureTailSaddleRatio (x : ℝ) :
    HasDerivAt thetaCuspGaussianApertureTailSaddleRatio
      ((1 - 2 * x) / (Real.pi * Real.exp (2 * x))) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (2 * y))
      (2 * Real.exp (2 * x)) x := by
    convert (Real.hasDerivAt_exp (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1
    all_goals ring
  have hden := hexp.const_mul Real.pi
  have hquot := (hasDerivAt_id x).div hden (by positivity)
  convert hquot using 1
  simp only [id_eq]
  field_simp [Real.pi_ne_zero, Real.exp_ne_zero]

/-- The displayed slope is literally `dr/dj` along the theta tail saddle. -/
theorem deriv_thetaCuspGaussianApertureTailSaddleRatio_div_degree
    {x : ℝ} (hx : 0 < x) :
    deriv thetaCuspGaussianApertureTailSaddleRatio x /
        deriv thetaCuspGaussianApertureTailSaddleDegree x =
      thetaCuspGaussianApertureTailSaddleRatioDegreeSlope x := by
  rw [(hasDerivAt_thetaCuspGaussianApertureTailSaddleRatio x).deriv,
    (hasDerivAt_thetaCuspGaussianApertureTailSaddleDegree x).deriv]
  simp only [thetaCuspGaussianApertureTailSaddleRatioDegreeSlope]
  have hlin : 1 + 2 * x ≠ 0 := by positivity
  have hexp4 : Real.exp (4 * x) = Real.exp (2 * x) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp4]
  field_simp [Real.pi_ne_zero, Real.exp_ne_zero, hlin]

theorem hasDerivAt_thetaCuspGaussianApertureTailSaddleRatioDegreeSlope
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt thetaCuspGaussianApertureTailSaddleRatioDegreeSlope
      (thetaCuspGaussianApertureTailSaddleRatioDegreeCurvature x *
        (Real.pi * Real.exp (2 * x) * (1 + 2 * x))) x := by
  have hnum : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) x := by
    convert (hasDerivAt_const x 1).sub ((hasDerivAt_id x).const_mul 2) using 1
    all_goals ring
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (4 * y))
      (4 * Real.exp (4 * x)) x := by
    convert (Real.hasDerivAt_exp (4 * x)).comp x
      ((hasDerivAt_id x).const_mul 4) using 1
    all_goals ring
  have hlin : HasDerivAt (fun y : ℝ => 1 + 2 * y) 2 x := by
    convert (hasDerivAt_const x 1).add ((hasDerivAt_id x).const_mul 2) using 1
    all_goals ring
  have hden := (hexp.const_mul (Real.pi ^ 2)).mul hlin
  have hlinNe : 1 + 2 * x ≠ 0 := by positivity
  have hdenNe : Real.pi ^ 2 * Real.exp (4 * x) * (1 + 2 * x) ≠ 0 := by
    positivity
  have hquot := hnum.div hden hdenNe
  convert hquot using 1
  simp only [thetaCuspGaussianApertureTailSaddleRatioDegreeCurvature, Pi.mul_apply]
  have hexp6 : Real.exp (6 * x) = Real.exp (4 * x) * Real.exp (2 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp6]
  field_simp [Real.pi_ne_zero, Real.exp_ne_zero, hlinNe]
  ring

/-- **Large-degree saddle curvature law.**  The exact second derivative of the leading theta-tail
ratio profile with respect to moment degree has the displayed source-height formula. -/
theorem deriv_thetaCuspGaussianApertureTailSaddleRatioDegreeSlope_div_degree
    {x : ℝ} (hx : 0 < x) :
    deriv thetaCuspGaussianApertureTailSaddleRatioDegreeSlope x /
        deriv thetaCuspGaussianApertureTailSaddleDegree x =
      thetaCuspGaussianApertureTailSaddleRatioDegreeCurvature x := by
  rw [(hasDerivAt_thetaCuspGaussianApertureTailSaddleRatioDegreeSlope hx).deriv,
    (hasDerivAt_thetaCuspGaussianApertureTailSaddleDegree x).deriv]
  have hdegree : Real.pi * Real.exp (2 * x) * (1 + 2 * x) ≠ 0 := by positivity
  field_simp [hdegree]

/-- Past the explicit saddle-height threshold `x²>1/2`, the tail ratio model is strictly convex
in moment degree. -/
theorem thetaCuspGaussianApertureTailSaddleRatioDegreeCurvature_pos
    {x : ℝ} (hx : 0 < x) (hxsq : 1 / 2 < x ^ 2) :
    0 < thetaCuspGaussianApertureTailSaddleRatioDegreeCurvature x := by
  simp only [thetaCuspGaussianApertureTailSaddleRatioDegreeCurvature]
  have hnum : 0 < 2 * x ^ 2 - 1 := by linarith
  exact div_pos (mul_pos (by norm_num) hnum) (by positivity)

/-! ### Exact height-localized higher-atom separation -/

/-- **Exact cusp-scale atom domination.**  Unlike the earlier uniform and linear-height bounds,
this estimate retains the full double-exponential separation of the `n`-th theta atom from the
first.  At the large-degree saddle it is the factor that makes all `n ≥ 2` atoms negligible. -/
theorem thetaCuspSourceTerm_le_first_mul_exp_exactHeight
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x n ≤
      (2 * (n : ℝ) ^ 4 *
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1) * Real.exp (2 * x))) *
          thetaCuspSourceTerm x 1 := by
  let u : ℝ := Real.exp x
  have hu : 1 ≤ u := by
    dsimp [u]
    simpa using Real.exp_le_exp.mpr hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpoly_u :
      0 ≤ 2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2) := by
    have hcore : 0 ≤ 2 * Real.pi * u ^ 2 - 3 := by
      nlinarith [Real.pi_gt_three]
    rw [show 2 * Real.pi * u ^ 4 - 3 * u ^ 2 =
      u ^ 2 * (2 * Real.pi * u ^ 2 - 3) by ring]
    positivity
  have hpolyUpper :
      2 * Real.pi *
          (2 * Real.pi * ((n : ℝ) * u) ^ 4 -
            3 * ((n : ℝ) * u) ^ 2) ≤
        2 * (n : ℝ) ^ 4 *
          (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2)) := by
    have hcore : 0 ≤ 2 * Real.pi * u ^ 2 - 6 := by
      nlinarith [Real.pi_gt_three]
    have hbracket :
        0 ≤ (n : ℝ) ^ 2 * (2 * Real.pi * u ^ 2 - 6) + 3 := by
      positivity
    have hid :
        2 * (n : ℝ) ^ 4 *
              (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2)) -
            2 * Real.pi *
              (2 * Real.pi * ((n : ℝ) * u) ^ 4 -
                3 * ((n : ℝ) * u) ^ 2) =
          2 * Real.pi * (n : ℝ) ^ 2 * u ^ 2 *
            ((n : ℝ) ^ 2 * (2 * Real.pi * u ^ 2 - 6) + 3) := by
      ring
    apply sub_nonneg.mp
    rw [hid]
    positivity
  have huSq : u ^ 2 = Real.exp (2 * x) := by
    dsimp [u]
    rw [show 2 * x = x + x by ring, Real.exp_add]
    ring
  have hgauss :
      Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2) =
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1) * Real.exp (2 * x)) *
          Real.exp (-Real.pi * u ^ 2) := by
    rw [← Real.exp_add, ← huSq]
    congr 1
    ring
  unfold thetaCuspSourceTerm thetaCuspSeed
  simp only [Nat.cast_one, one_mul]
  change Real.exp (x / 2) *
      (2 * Real.pi *
        (2 * Real.pi * ((n : ℝ) * u) ^ 4 -
          3 * ((n : ℝ) * u) ^ 2) *
            Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2)) ≤ _
  calc
    _ ≤ Real.exp (x / 2) *
        ((2 * (n : ℝ) ^ 4 *
          (2 * Real.pi * (2 * Real.pi * u ^ 4 - 3 * u ^ 2))) *
            Real.exp (-Real.pi * ((n : ℝ) * u) ^ 2)) := by
      gcongr
    _ = _ := by
      rw [hgauss]
      dsimp [u]
      ring

/-- Universal height factor left after extracting the old all-atom domination weights. -/
def thetaCuspHigherAtomExactHeightDamping (x : ℝ) : ℝ :=
  Real.exp (-3 * Real.pi * (Real.exp (2 * x) - 1))

theorem thetaCuspSourceAtomExactHeightWeight_le
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    2 * (n : ℝ) ^ 4 *
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1) * Real.exp (2 * x)) ≤
      thetaCuspSourceAtomDominationWeight n *
        thetaCuspHigherAtomExactHeightDamping x := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hA : (3 : ℝ) ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
  have hexpTwo : 1 ≤ Real.exp (2 * x) := by
    simpa using Real.exp_le_exp.mpr (by linarith : 0 ≤ 2 * x)
  have hB : 0 ≤ Real.exp (2 * x) - 1 := sub_nonneg.mpr hexpTwo
  have hprod : 0 ≤ ((n : ℝ) ^ 2 - 1 - 3) *
      (Real.exp (2 * x) - 1) := mul_nonneg (by linarith) hB
  have hexponent :
      -Real.pi * ((n : ℝ) ^ 2 - 1) * Real.exp (2 * x) ≤
        -Real.pi * ((n : ℝ) ^ 2 - 1) +
          (-3 * Real.pi * (Real.exp (2 * x) - 1)) := by
    have := mul_nonneg Real.pi_pos.le hprod
    nlinarith
  unfold thetaCuspSourceAtomDominationWeight thetaCuspHigherAtomExactHeightDamping
  calc
    2 * (n : ℝ) ^ 4 *
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1) * Real.exp (2 * x)) ≤
      2 * (n : ℝ) ^ 4 *
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1) +
          (-3 * Real.pi * (Real.exp (2 * x) - 1))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)
    _ = 2 * (n : ℝ) ^ 4 *
        Real.exp (-Real.pi * ((n : ℝ) ^ 2 - 1)) *
          Real.exp (-3 * Real.pi * (Real.exp (2 * x) - 1)) := by
      simp only [Real.exp_add]
      ring

/-- **Completed-source double-exponential separation.**  The full higher-atom tail is bounded by
the old summable atom weight times one explicit height factor.  At a moving high-degree saddle this
factor is `exp(-3π exp(2x)+O(1))`, rather than merely exponential in `x`. -/
theorem thetaCuspFullSource_sub_first_le_exactHeight
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullSource x - thetaCuspSourceTerm x 1 ≤
      thetaCuspHigherAtomDominationWeight *
        thetaCuspHigherAtomExactHeightDamping x *
          thetaCuspSourceTerm x 1 := by
  have hs := summable_thetaCuspSourceTerm x
  have htail : Summable (fun k : ℕ => thetaCuspSourceTerm x (k + 2)) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hweight : Summable
      (fun k : ℕ => thetaCuspSourceAtomDominationWeight (k + 2)) :=
    summable_thetaCuspSourceAtomDominationWeight.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hweighted : Summable (fun k : ℕ =>
      thetaCuspSourceAtomDominationWeight (k + 2) *
        (thetaCuspHigherAtomExactHeightDamping x * thetaCuspSourceTerm x 1)) :=
    hweight.mul_right _
  have hfirst : 0 ≤ thetaCuspSourceTerm x 1 := by
    rcases hx.eq_or_lt with rfl | hxpos
    · exact thetaCuspSourceTerm_one_zero_pos.le
    · exact thetaCuspSourceTerm_nonneg_of_pos hxpos 1
  have hhead :
      (∑ n ∈ Finset.range 2, thetaCuspSourceTerm x n) =
        thetaCuspSourceTerm x 1 := by
    calc
      (∑ n ∈ Finset.range 2, thetaCuspSourceTerm x n) =
          thetaCuspSourceTerm x 0 + thetaCuspSourceTerm x 1 := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      _ = thetaCuspSourceTerm x 1 := by
        simp [thetaCuspSourceTerm, thetaCuspSeed]
  calc
    thetaCuspFullSource x - thetaCuspSourceTerm x 1 =
        ∑' k : ℕ, thetaCuspSourceTerm x (k + 2) := by
      rw [thetaCuspFullSource, ← hs.sum_add_tsum_nat_add 2, hhead]
      ring
    _ ≤ ∑' k : ℕ,
        thetaCuspSourceAtomDominationWeight (k + 2) *
          (thetaCuspHigherAtomExactHeightDamping x *
            thetaCuspSourceTerm x 1) := by
      exact Summable.tsum_le_tsum (fun k => by
        calc
          thetaCuspSourceTerm x (k + 2) ≤
              (2 * ((k + 2 : ℕ) : ℝ) ^ 4 *
                Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ 2 - 1) *
                  Real.exp (2 * x))) * thetaCuspSourceTerm x 1 :=
            thetaCuspSourceTerm_le_first_mul_exp_exactHeight
              (by positivity : 0 < k + 2) hx
          _ ≤ (thetaCuspSourceAtomDominationWeight (k + 2) *
                thetaCuspHigherAtomExactHeightDamping x) *
              thetaCuspSourceTerm x 1 := by
            exact mul_le_mul_of_nonneg_right
              (thetaCuspSourceAtomExactHeightWeight_le (n := k + 2)
                (by omega : 2 ≤ k + 2) hx)
              hfirst
          _ = thetaCuspSourceAtomDominationWeight (k + 2) *
              (thetaCuspHigherAtomExactHeightDamping x *
                thetaCuspSourceTerm x 1) := by ring)
        htail hweighted
    _ = thetaCuspHigherAtomDominationWeight *
        thetaCuspHigherAtomExactHeightDamping x *
          thetaCuspSourceTerm x 1 := by
      rw [thetaCuspHigherAtomDominationWeight]
      simpa [mul_assoc] using hweight.tsum_mul_right
        (thetaCuspHigherAtomExactHeightDamping x * thetaCuspSourceTerm x 1)

/-- Rational closed form of the completed higher-tail separation. -/
theorem thetaCuspFullSource_sub_first_le_exactHeight_rational
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullSource x - thetaCuspSourceTerm x 1 ≤
      (8 / 2997 : ℝ) * thetaCuspHigherAtomExactHeightDamping x *
        thetaCuspSourceTerm x 1 := by
  have hfirst : 0 ≤ thetaCuspSourceTerm x 1 := by
    rcases hx.eq_or_lt with rfl | hxpos
    · exact thetaCuspSourceTerm_one_zero_pos.le
    · exact thetaCuspSourceTerm_nonneg_of_pos hxpos 1
  have hfactor :
      0 ≤ thetaCuspHigherAtomExactHeightDamping x *
        thetaCuspSourceTerm x 1 :=
    mul_nonneg (Real.exp_nonneg _) hfirst
  calc
    _ ≤ thetaCuspHigherAtomDominationWeight *
        thetaCuspHigherAtomExactHeightDamping x * thetaCuspSourceTerm x 1 :=
      thetaCuspFullSource_sub_first_le_exactHeight hx
    _ = thetaCuspHigherAtomDominationWeight *
        (thetaCuspHigherAtomExactHeightDamping x *
          thetaCuspSourceTerm x 1) := by ring
    _ ≤ (8 / 2997 : ℝ) *
        (thetaCuspHigherAtomExactHeightDamping x *
          thetaCuspSourceTerm x 1) :=
      mul_le_mul_of_nonneg_right
        thetaCuspHigherAtomDominationWeight_le_geometric_rational hfactor
    _ = _ := by ring

/-! ### Exact two-channel resolution of the first saddle atom -/

/-- Positive polynomial-Gaussian channel underlying the first theta atom after aperture tilt.
The leading saddle channel is `p=4`; the unique lower channel is `p=2`. -/
def thetaCuspGaussianApertureTailChannelMoment
    (lambda : ℝ) (p j : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
      thetaCuspPolynomialAtom (X ^ p) 1 x

theorem integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
    {lambda : ℝ} (hlambda : lambda ≤ 0) (p j : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
        thetaCuspPolynomialAtom (X ^ p) 1 x) (Ioi 0) := by
  have hbase := integrableOn_pow_mul_thetaCuspPolynomialAtom_Ioi_of_pos
    (2 * j) (X ^ p) (n := 1) (by norm_num)
  apply MeasureTheory.Integrable.mono hbase
  · exact Continuous.aestronglyMeasurable
      (((continuous_id.pow (2 * j)).mul
        (Real.continuous_exp.comp
          (continuous_const.mul (continuous_id.pow 2)))).mul
        (continuous_iff_continuousAt.mpr fun x =>
          (hasDerivAt_thetaCuspPolynomialAtom (X ^ p) 1 x).continuousAt))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hexpLe : Real.exp (lambda * x ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg hlambda (sq_nonneg x))
    rw [show x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
          thetaCuspPolynomialAtom (X ^ p) 1 x =
        Real.exp (lambda * x ^ 2) *
          (x ^ (2 * j) * thetaCuspPolynomialAtom (X ^ p) 1 x) by ring,
      norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) hexpLe

theorem thetaCuspGaussianApertureTailChannelMoment_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) (p j : ℕ) :
    0 < thetaCuspGaussianApertureTailChannelMoment lambda p j := by
  let f : ℝ → ℝ := fun x =>
    x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
      thetaCuspPolynomialAtom (X ^ p) 1 x
  have hfcont : Continuous f := by
    exact ((continuous_id.pow (2 * j)).mul
      (Real.continuous_exp.comp
        (continuous_const.mul (continuous_id.pow 2)))).mul
      (continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspPolynomialAtom (X ^ p) 1 x).continuousAt)
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa only [f] using
      integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
        hlambda p j
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp only [f, thetaCuspPolynomialAtom]
    simp only [Nat.cast_one, one_mul, eval_pow, eval_X]
    exact mul_nonneg
      (mul_nonneg ((even_two_mul j).pow_nonneg x) (Real.exp_nonneg _))
      (by positivity)
  rw [thetaCuspGaussianApertureTailChannelMoment]
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change f 1 ≠ 0
  dsimp only [f, thetaCuspPolynomialAtom]
  simp only [Nat.cast_one, one_mul, eval_pow, eval_X]
  positivity

/-- The lower first-atom channel is the leading channel times the exact decreasing likelihood
ratio `exp(-2x)`. -/
theorem thetaCuspPolynomialAtom_two_eq_exp_neg_two_mul_four (x : ℝ) :
    thetaCuspPolynomialAtom (X ^ 2) 1 x =
      Real.exp (-2 * x) * thetaCuspPolynomialAtom (X ^ 4) 1 x := by
  simp only [thetaCuspPolynomialAtom, Nat.cast_one, one_mul, eval_pow, eval_X]
  have hpow : Real.exp (-2 * x) * Real.exp x ^ 4 = Real.exp x ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [show Real.exp (-2 * x) *
        (Real.exp (x / 2) * Real.exp x ^ 4 *
          Real.exp (-Real.pi * Real.exp x ^ 2)) =
      Real.exp (x / 2) *
        (Real.exp (-2 * x) * Real.exp x ^ 4) *
          Real.exp (-Real.pi * Real.exp x ^ 2) by ring,
    hpow]

/-- Exact signed two-channel decomposition of the first theta atom. -/
theorem thetaCuspSourceTerm_one_eq_tailChannelDifference (x : ℝ) :
    thetaCuspSourceTerm x 1 =
      4 * Real.pi ^ 2 * thetaCuspPolynomialAtom (X ^ 4) 1 x -
        6 * Real.pi * thetaCuspPolynomialAtom (X ^ 2) 1 x := by
  simp [thetaCuspSourceTerm, thetaCuspSeed, thetaCuspPolynomialAtom]
  ring

/-- Aperture moment of the literal first theta atom. -/
def thetaCuspGaussianApertureFirstAtomHalfMoment
    (lambda : ℝ) (j : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ (2 * j) * Real.exp (lambda * x ^ 2) * thetaCuspSourceTerm x 1

/-- The full polynomial amplitude of the first atom is exactly a difference of two positive
Laplace channels. -/
theorem thetaCuspGaussianApertureFirstAtomHalfMoment_eq_tailChannels
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureFirstAtomHalfMoment lambda j =
      4 * Real.pi ^ 2 *
          thetaCuspGaussianApertureTailChannelMoment lambda 4 j -
        6 * Real.pi *
          thetaCuspGaussianApertureTailChannelMoment lambda 2 j := by
  have h4 :=
    integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
      hlambda 4 j
  have h2 :=
    integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
      hlambda 2 j
  rw [thetaCuspGaussianApertureFirstAtomHalfMoment,
    thetaCuspGaussianApertureTailChannelMoment,
    thetaCuspGaussianApertureTailChannelMoment,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_sub (h4.const_mul (4 * Real.pi ^ 2))
      (h2.const_mul (6 * Real.pi))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [thetaCuspSourceTerm_one_eq_tailChannelDifference]
  ring

/-- **Amplitude-correction likelihood law.**  Under every physical Gaussian aperture, the
lower-to-leading channel ratio decreases with moment degree.  Equivalently, size bias moves mass
to heights where the unique signed first-atom correction `exp(-2x)` is smaller. -/
theorem thetaCuspGaussianApertureTailChannel_two_succ_mul_four_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailChannelMoment lambda 2 (j + 1) *
        thetaCuspGaussianApertureTailChannelMoment lambda 4 j ≤
      thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) *
        thetaCuspGaussianApertureTailChannelMoment lambda 2 j := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x =>
    x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
      thetaCuspPolynomialAtom (X ^ 4) 1 x
  let h : ℝ → ℝ := fun x =>
    x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
      thetaCuspPolynomialAtom (X ^ 2) 1 x
  let g : ℝ → ℝ := fun x => x ^ 2
  have hf : Integrable f mu := by
    simpa only [f, mu] using
      integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
        hlambda 4 j
  have hh : Integrable h mu := by
    simpa only [h, mu] using
      integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
        hlambda 2 j
  have hgf : Integrable (fun x => g x * f x) mu := by
    have hbase :=
      integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
        hlambda 4 (j + 1)
    apply hbase.congr
    filter_upwards [] with x
    simp only [g, f]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hgh : Integrable (fun x => g x * h x) mu := by
    have hbase :=
      integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
        hlambda 2 (j + 1)
    apply hbase.congr
    filter_upwards [] with x
    simp only [g, h]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hordered : ∀ {x y : ℝ}, x ∈ Ioi 0 → y ∈ Ioi 0 → x ≤ y →
      0 ≤ (g y - g x) * (h x * f y - h y * f x) := by
    intro x y hx hy hxy
    have hgdiff : 0 ≤ g y - g x := by
      dsimp only [g]
      exact sub_nonneg.mpr ((sq_le_sq₀ hx.le hy.le).2 hxy)
    have hediff : 0 ≤ Real.exp (-2 * x) - Real.exp (-2 * y) := by
      exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
    have hcommon : 0 ≤
        (x ^ (2 * j) * Real.exp (lambda * x ^ 2)) *
        (y ^ (2 * j) * Real.exp (lambda * y ^ 2)) *
        thetaCuspPolynomialAtom (X ^ 4) 1 x *
        thetaCuspPolynomialAtom (X ^ 4) 1 y := by
      have hxpow : 0 ≤ x ^ (2 * j) := pow_nonneg hx.le _
      have hypow : 0 ≤ y ^ (2 * j) := pow_nonneg hy.le _
      have hAx : 0 ≤ thetaCuspPolynomialAtom (X ^ 4) 1 x := by
        simp [thetaCuspPolynomialAtom]
        positivity
      have hAy : 0 ≤ thetaCuspPolynomialAtom (X ^ 4) 1 y := by
        simp [thetaCuspPolynomialAtom]
        positivity
      positivity
    have hbracket : 0 ≤ h x * f y - h y * f x := by
      dsimp only [h, f]
      rw [thetaCuspPolynomialAtom_two_eq_exp_neg_two_mul_four,
        thetaCuspPolynomialAtom_two_eq_exp_neg_two_mul_four]
      rw [show
        (x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
              (Real.exp (-2 * x) * thetaCuspPolynomialAtom (X ^ 4) 1 x)) *
            (y ^ (2 * j) * Real.exp (lambda * y ^ 2) *
              thetaCuspPolynomialAtom (X ^ 4) 1 y) -
          (y ^ (2 * j) * Real.exp (lambda * y ^ 2) *
              (Real.exp (-2 * y) * thetaCuspPolynomialAtom (X ^ 4) 1 y)) *
            (x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
              thetaCuspPolynomialAtom (X ^ 4) 1 x) =
          ((x ^ (2 * j) * Real.exp (lambda * x ^ 2)) *
            (y ^ (2 * j) * Real.exp (lambda * y ^ 2)) *
            thetaCuspPolynomialAtom (X ^ 4) 1 x *
            thetaCuspPolynomialAtom (X ^ 4) 1 y) *
              (Real.exp (-2 * x) - Real.exp (-2 * y)) by ring]
      exact mul_nonneg hcommon hediff
    exact mul_nonneg hgdiff hbracket
  have hmem : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu,
      z ∈ (Ioi 0 ×ˢ Ioi 0) := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Ioi.prod measurableSet_Ioi)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact ⟨hx, hy⟩
  have hkernel : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu,
      0 ≤ (g z.2 - g z.1) *
        (h z.1 * f z.2 - h z.2 * f z.1) := by
    filter_upwards [hmem] with z hz
    rcases hz with ⟨hx, hy⟩
    rcases le_total z.1 z.2 with hxy | hyx
    · exact hordered hx hy hxy
    · convert hordered hy hx hyx using 1
      all_goals ring
  have hcross :=
    HTGeometry.integral_mul_integral_le_of_monotoneLikelihoodKernel
      hf hh hgf hgh hkernel
  have hshift2 : (fun x => g x * h x) = fun x : ℝ =>
      x ^ (2 * (j + 1)) * Real.exp (lambda * x ^ 2) *
        thetaCuspPolynomialAtom (X ^ 2) 1 x := by
    funext x
    dsimp only [g, h]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hshift4 : (fun x => g x * f x) = fun x : ℝ =>
      x ^ (2 * (j + 1)) * Real.exp (lambda * x ^ 2) *
        thetaCuspPolynomialAtom (X ^ 4) 1 x := by
    funext x
    dsimp only [g, f]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  rw [hshift2, hshift4] at hcross
  simpa only [thetaCuspGaussianApertureTailChannelMoment, f, h, mu] using hcross

/-- Relative size of the unique `p=2` correction channel inside the leading `p=4` saddle
channel. -/
def thetaCuspGaussianApertureTailCorrectionRatio
    (lambda : ℝ) (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureTailChannelMoment lambda 2 j /
    thetaCuspGaussianApertureTailChannelMoment lambda 4 j

/-- The exact signed amplitude correction is antitone in degree for every physical aperture. -/
theorem thetaCuspGaussianApertureTailCorrectionRatio_succ_le
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailCorrectionRatio lambda (j + 1) ≤
      thetaCuspGaussianApertureTailCorrectionRatio lambda j := by
  rw [thetaCuspGaussianApertureTailCorrectionRatio,
    thetaCuspGaussianApertureTailCorrectionRatio]
  exact (div_le_div_iff₀
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 (j + 1))
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j)).2 (by
      simpa only [mul_comm] using
        thetaCuspGaussianApertureTailChannel_two_succ_mul_four_le hlambda j)

theorem thetaCuspGaussianApertureTailChannelMoment_two_le_four
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailChannelMoment lambda 2 j ≤
      thetaCuspGaussianApertureTailChannelMoment lambda 4 j := by
  have h2 :=
    integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
      hlambda 2 j
  have h4 :=
    integrableOn_thetaCuspGaussianApertureTailChannelMomentIntegrand
      hlambda 4 j
  rw [thetaCuspGaussianApertureTailChannelMoment,
    thetaCuspGaussianApertureTailChannelMoment]
  apply integral_mono_ae h2 h4
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hexpLe : Real.exp (-2 * x) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hx.le)
  have hcommon : 0 ≤
      x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
        thetaCuspPolynomialAtom (X ^ 4) 1 x := by
    have hpow : 0 ≤ x ^ (2 * j) := pow_nonneg hx.le _
    have hA : 0 ≤ thetaCuspPolynomialAtom (X ^ 4) 1 x := by
      simp [thetaCuspPolynomialAtom]
      positivity
    positivity
  rw [thetaCuspPolynomialAtom_two_eq_exp_neg_two_mul_four]
  calc
    x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
          (Real.exp (-2 * x) * thetaCuspPolynomialAtom (X ^ 4) 1 x) =
        Real.exp (-2 * x) *
          (x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
            thetaCuspPolynomialAtom (X ^ 4) 1 x) := by ring
    _ ≤ 1 * (x ^ (2 * j) * Real.exp (lambda * x ^ 2) *
          thetaCuspPolynomialAtom (X ^ 4) 1 x) :=
      mul_le_mul_of_nonneg_right hexpLe hcommon
    _ = _ := by ring

theorem thetaCuspGaussianApertureTailCorrectionRatio_nonneg
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    0 ≤ thetaCuspGaussianApertureTailCorrectionRatio lambda j := by
  rw [thetaCuspGaussianApertureTailCorrectionRatio]
  exact div_nonneg
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 2 j).le
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j).le

theorem thetaCuspGaussianApertureTailCorrectionRatio_le_one
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailCorrectionRatio lambda j ≤ 1 := by
  rw [thetaCuspGaussianApertureTailCorrectionRatio]
  exact (div_le_one
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j)).2
      (thetaCuspGaussianApertureTailChannelMoment_two_le_four hlambda j)

/-- Positive fraction of the leading saddle channel left after the unique signed polynomial
correction is subtracted. -/
def thetaCuspGaussianApertureTailAmplitudeFactor
    (lambda : ℝ) (j : ℕ) : ℝ :=
  1 - (3 / (2 * Real.pi)) *
    thetaCuspGaussianApertureTailCorrectionRatio lambda j

theorem thetaCuspGaussianApertureTailAmplitudeFactor_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    0 < thetaCuspGaussianApertureTailAmplitudeFactor lambda j := by
  have hcpos : 0 < (3 / (2 * Real.pi) : ℝ) := by positivity
  have hclt : (3 / (2 * Real.pi) : ℝ) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [Real.pi_gt_three]
  have hrho0 :=
    thetaCuspGaussianApertureTailCorrectionRatio_nonneg hlambda j
  have hrho1 :=
    thetaCuspGaussianApertureTailCorrectionRatio_le_one hlambda j
  have hmul :
      (3 / (2 * Real.pi) : ℝ) *
          thetaCuspGaussianApertureTailCorrectionRatio lambda j ≤
        3 / (2 * Real.pi) := by
    nlinarith [mul_le_mul_of_nonneg_left hrho1 hcpos.le]
  rw [thetaCuspGaussianApertureTailAmplitudeFactor]
  linarith

/-- Degree bias monotonically removes the signed polynomial correction from the first atom. -/
theorem thetaCuspGaussianApertureTailAmplitudeFactor_le_succ
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailAmplitudeFactor lambda j ≤
      thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 1) := by
  have hcpos : 0 ≤ (3 / (2 * Real.pi) : ℝ) := by positivity
  have hratio :=
    thetaCuspGaussianApertureTailCorrectionRatio_succ_le hlambda j
  rw [thetaCuspGaussianApertureTailAmplitudeFactor,
    thetaCuspGaussianApertureTailAmplitudeFactor]
  nlinarith [mul_le_mul_of_nonneg_left hratio hcpos]

/-- Factored form of the first-atom moment: a positive leading saddle channel times an exact,
positive, degree-monotone amplitude factor. -/
theorem thetaCuspGaussianApertureFirstAtomHalfMoment_eq_leading_mul_amplitude
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureFirstAtomHalfMoment lambda j =
      4 * Real.pi ^ 2 *
        thetaCuspGaussianApertureTailChannelMoment lambda 4 j *
          thetaCuspGaussianApertureTailAmplitudeFactor lambda j := by
  rw [thetaCuspGaussianApertureFirstAtomHalfMoment_eq_tailChannels hlambda,
    thetaCuspGaussianApertureTailAmplitudeFactor,
    thetaCuspGaussianApertureTailCorrectionRatio]
  have h4ne :=
    (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j).ne'
  field_simp [h4ne, Real.pi_ne_zero]
  ring

theorem thetaCuspGaussianApertureFirstAtomHalfMoment_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    0 < thetaCuspGaussianApertureFirstAtomHalfMoment lambda j := by
  rw [thetaCuspGaussianApertureFirstAtomHalfMoment_eq_leading_mul_amplitude
    hlambda]
  exact mul_pos
    (mul_pos (by positivity)
      (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j))
    (thetaCuspGaussianApertureTailAmplitudeFactor_pos hlambda j)

/-- Multiplicative change in the first-atom amplitude correction between adjacent degrees. -/
def thetaCuspGaussianApertureTailAmplitudeMultiplier
    (lambda : ℝ) (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureTailAmplitudeFactor lambda (j + 1) /
    thetaCuspGaussianApertureTailAmplitudeFactor lambda j

theorem one_le_thetaCuspGaussianApertureTailAmplitudeMultiplier
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    1 ≤ thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j := by
  rw [thetaCuspGaussianApertureTailAmplitudeMultiplier,
    one_le_div
      (thetaCuspGaussianApertureTailAmplitudeFactor_pos hlambda j)]
  exact thetaCuspGaussianApertureTailAmplitudeFactor_le_succ hlambda j

/-- Exact adjacent-ratio resolution of the first atom.  Its signed polynomial correction appears
only through a multiplicative factor at least one. -/
theorem thetaCuspGaussianApertureFirstAtomMomentRatio_eq_leading_mul_amplitudeMultiplier
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureFirstAtomHalfMoment lambda (j + 1) /
        thetaCuspGaussianApertureFirstAtomHalfMoment lambda j =
      (thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) /
          thetaCuspGaussianApertureTailChannelMoment lambda 4 j) *
        thetaCuspGaussianApertureTailAmplitudeMultiplier lambda j := by
  rw [thetaCuspGaussianApertureFirstAtomHalfMoment_eq_leading_mul_amplitude
      hlambda,
    thetaCuspGaussianApertureFirstAtomHalfMoment_eq_leading_mul_amplitude
      hlambda,
    thetaCuspGaussianApertureTailAmplitudeMultiplier]
  have h4j :=
    thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j
  have hAj := thetaCuspGaussianApertureTailAmplitudeFactor_pos hlambda j
  field_simp [h4j.ne', hAj.ne', Real.pi_ne_zero]

/-- The signed polynomial amplitude can only increase the adjacent first-atom moment ratio above
the pure leading saddle-channel ratio. -/
theorem thetaCuspGaussianApertureTailChannelRatio_le_firstAtomMomentRatio
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    thetaCuspGaussianApertureTailChannelMoment lambda 4 (j + 1) /
        thetaCuspGaussianApertureTailChannelMoment lambda 4 j ≤
      thetaCuspGaussianApertureFirstAtomHalfMoment lambda (j + 1) /
        thetaCuspGaussianApertureFirstAtomHalfMoment lambda j := by
  rw [thetaCuspGaussianApertureFirstAtomMomentRatio_eq_leading_mul_amplitudeMultiplier
    hlambda]
  exact le_mul_of_one_le_right
    (div_nonneg
      (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 (j + 1)).le
      (thetaCuspGaussianApertureTailChannelMoment_pos hlambda 4 j).le)
    (one_le_thetaCuspGaussianApertureTailAmplitudeMultiplier hlambda j)

/-! ### Degree-scale form of the exact higher-atom contraction -/

/-- The double-exponential higher-atom damping written exactly in the moving saddle degree. -/
theorem thetaCuspHigherAtomExactHeightDamping_eq_saddleDegree
    {x : ℝ} (hx : x ≠ 0) :
    thetaCuspHigherAtomExactHeightDamping x =
      Real.exp (3 * Real.pi -
        3 * thetaCuspGaussianApertureTailSaddleDegree x / x) := by
  unfold thetaCuspHigherAtomExactHeightDamping
    thetaCuspGaussianApertureTailSaddleDegree
  congr 1
  field_simp [hx]
  ring

/-- Once `exp(2x)≥2`, the complete higher-atom tail loses at least
`exp(-(3/2) degree/x)` relative to the first atom at height `x`. -/
theorem thetaCuspHigherAtomExactHeightDamping_le_saddleDegree
    {x : ℝ} (hx : 0 < x) (hlarge : 2 ≤ Real.exp (2 * x)) :
    thetaCuspHigherAtomExactHeightDamping x ≤
      Real.exp (-(3 / 2 : ℝ) *
        (thetaCuspGaussianApertureTailSaddleDegree x / x)) := by
  rw [thetaCuspHigherAtomExactHeightDamping_eq_saddleDegree hx.ne']
  apply Real.exp_le_exp.mpr
  have hquot :
      thetaCuspGaussianApertureTailSaddleDegree x / x =
        Real.pi * Real.exp (2 * x) := by
    unfold thetaCuspGaussianApertureTailSaddleDegree
    field_simp [hx.ne']
  have hscale := mul_le_mul_of_nonneg_left hlarge
    (by positivity : 0 ≤ (3 / 2 : ℝ) * Real.pi)
  calc
    3 * Real.pi -
          3 * thetaCuspGaussianApertureTailSaddleDegree x / x =
        3 * Real.pi - 3 * (Real.pi * Real.exp (2 * x)) := by
      rw [show 3 * thetaCuspGaussianApertureTailSaddleDegree x / x =
        3 * (thetaCuspGaussianApertureTailSaddleDegree x / x) by ring,
        hquot]
    _ ≤ -(3 / 2 : ℝ) * (Real.pi * Real.exp (2 * x)) := by nlinarith
    _ = -(3 / 2 : ℝ) *
        (thetaCuspGaussianApertureTailSaddleDegree x / x) := by rw [hquot]

/-! ### Exact physical saddle, including aperture and polynomial amplitude -/

/-- Exact stationary degree of the positive `p=4` first-atom channel. -/
def thetaCuspGaussianApertureExactTailSaddleDegree
    (lambda x : ℝ) : ℝ :=
  Real.pi * x * Real.exp (2 * x) - lambda * x ^ 2 - 9 * x / 4

/-- Gamma-normalized degree scale at the exact leading-channel saddle. -/
def thetaCuspGaussianApertureExactTailSaddleGammaScale
    (lambda x : ℝ) : ℝ :=
  thetaCuspGaussianApertureExactTailSaddleDegree lambda x + 1 / 2

/-- Exact derivative of the physical saddle degree with respect to height. -/
def thetaCuspGaussianApertureExactTailSaddleDegreeSlope
    (lambda x : ℝ) : ℝ :=
  Real.pi * Real.exp (2 * x) * (1 + 2 * x) -
    2 * lambda * x - 9 / 4

/-- Exact second height derivative of the physical saddle degree. -/
def thetaCuspGaussianApertureExactTailSaddleDegreeCurvature
    (lambda x : ℝ) : ℝ :=
  4 * Real.pi * Real.exp (2 * x) * (1 + x) - 2 * lambda

/-- Leading gamma-normalized ratio evaluated on the exact stationary degree. -/
def thetaCuspGaussianApertureExactTailSaddleRatio
    (lambda x : ℝ) : ℝ :=
  x ^ 2 / thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x

/-- First derivative of the exact saddle ratio with respect to saddle degree. -/
def thetaCuspGaussianApertureExactTailSaddleRatioDegreeSlope
    (lambda x : ℝ) : ℝ :=
  let G := thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x
  let p := thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x
  (2 * x * G - x ^ 2 * p) / (G ^ 2 * p)

/-- Cancellation coordinate in the exact degree-curvature numerator. -/
def thetaCuspGaussianApertureExactTailSaddleDefect
    (lambda x : ℝ) : ℝ :=
  thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x -
    x * thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x

/-- Numerator governing convexity of the exact physical saddle ratio in degree. -/
def thetaCuspGaussianApertureExactTailSaddleCurvatureNumerator
    (lambda x : ℝ) : ℝ :=
  let G := thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x
  let p := thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x
  let q := thetaCuspGaussianApertureExactTailSaddleDegreeCurvature lambda x
  p * thetaCuspGaussianApertureExactTailSaddleDefect lambda x ^ 2 -
    x * q * G ^ 2

/-- Exact second derivative of the physical leading-channel ratio with respect to saddle degree. -/
def thetaCuspGaussianApertureExactTailSaddleRatioDegreeCurvature
    (lambda x : ℝ) : ℝ :=
  2 * thetaCuspGaussianApertureExactTailSaddleCurvatureNumerator lambda x /
    (thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x ^ 3 *
      thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x ^ 3)

/-- The linear amplitude shift `9x/4` cancels completely from the key curvature defect. -/
theorem thetaCuspGaussianApertureExactTailSaddleDefect_eq
    (lambda x : ℝ) :
    thetaCuspGaussianApertureExactTailSaddleDefect lambda x =
      1 / 2 + lambda * x ^ 2 -
        2 * Real.pi * x ^ 2 * Real.exp (2 * x) := by
  unfold thetaCuspGaussianApertureExactTailSaddleDefect
    thetaCuspGaussianApertureExactTailSaddleGammaScale
    thetaCuspGaussianApertureExactTailSaddleDegree
    thetaCuspGaussianApertureExactTailSaddleDegreeSlope
  ring

theorem hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree
    (lambda x : ℝ) :
    HasDerivAt (thetaCuspGaussianApertureExactTailSaddleDegree lambda)
      (thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (2 * y))
      (2 * Real.exp (2 * x)) x := by
    convert (Real.hasDerivAt_exp (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1
    all_goals ring
  have htail := ((hasDerivAt_id x).const_mul Real.pi).mul hexp
  have haperture := ((hasDerivAt_id x).pow 2).const_mul lambda
  have hamplitude := ((hasDerivAt_id x).const_mul 9).div_const 4
  convert (htail.sub haperture).sub hamplitude using 1
  all_goals
    simp only [thetaCuspGaussianApertureExactTailSaddleDegreeSlope, id_eq]
    ring

theorem hasDerivAt_thetaCuspGaussianApertureExactTailSaddleGammaScale
    (lambda x : ℝ) :
    HasDerivAt (thetaCuspGaussianApertureExactTailSaddleGammaScale lambda)
      (thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x) x := by
  convert (hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree lambda x).add_const
    (1 / 2 : ℝ) using 1

theorem hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegreeSlope
    (lambda x : ℝ) :
    HasDerivAt (thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda)
      (thetaCuspGaussianApertureExactTailSaddleDegreeCurvature lambda x) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (2 * y))
      (2 * Real.exp (2 * x)) x := by
    convert (Real.hasDerivAt_exp (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1
    all_goals ring
  have hA := hexp.const_mul Real.pi
  have hlin : HasDerivAt (fun y : ℝ => 1 + 2 * y) 2 x := by
    convert (hasDerivAt_const x 1).add ((hasDerivAt_id x).const_mul 2) using 1
    all_goals ring
  have haperture := (hasDerivAt_id x).const_mul (2 * lambda)
  convert ((hA.mul hlin).sub haperture).sub_const (9 / 4 : ℝ) using 1
  all_goals
    simp only [thetaCuspGaussianApertureExactTailSaddleDegreeCurvature]
    ring

theorem hasDerivAt_thetaCuspGaussianApertureExactTailSaddleRatio
    {lambda x : ℝ}
    (hG : thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x ≠ 0) :
    HasDerivAt (thetaCuspGaussianApertureExactTailSaddleRatio lambda)
      ((2 * x * thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x -
          x ^ 2 * thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x) /
        thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x ^ 2) x := by
  have hnum := (hasDerivAt_id x).pow 2
  have hden :=
    hasDerivAt_thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x
  convert hnum.div hden hG using 1
  all_goals
    simp only [Pi.pow_apply, id_eq]
    field_simp [hG]
    ring

/-- The displayed exact slope is literally `dr/dj` along the physical leading-channel saddle. -/
theorem deriv_thetaCuspGaussianApertureExactTailSaddleRatio_div_degree
    {lambda x : ℝ}
    (hG : thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x ≠ 0)
    (hp : thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x ≠ 0) :
    deriv (thetaCuspGaussianApertureExactTailSaddleRatio lambda) x /
        deriv (thetaCuspGaussianApertureExactTailSaddleDegree lambda) x =
      thetaCuspGaussianApertureExactTailSaddleRatioDegreeSlope lambda x := by
  rw [(hasDerivAt_thetaCuspGaussianApertureExactTailSaddleRatio hG).deriv,
    (hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree lambda x).deriv]
  simp only [thetaCuspGaussianApertureExactTailSaddleRatioDegreeSlope]
  field_simp [hG, hp]

theorem hasDerivAt_thetaCuspGaussianApertureExactTailSaddleRatioDegreeSlope
    {lambda x : ℝ}
    (hG : thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x ≠ 0)
    (hp : thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x ≠ 0) :
    HasDerivAt (thetaCuspGaussianApertureExactTailSaddleRatioDegreeSlope lambda)
      (thetaCuspGaussianApertureExactTailSaddleRatioDegreeCurvature lambda x *
        thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x) x := by
  let G := thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x
  let p := thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x
  let q := thetaCuspGaussianApertureExactTailSaddleDegreeCurvature lambda x
  have hGderiv :=
    hasDerivAt_thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x
  have hpderiv :=
    hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x
  have hU : HasDerivAt (fun y : ℝ =>
      2 * y * thetaCuspGaussianApertureExactTailSaddleGammaScale lambda y -
        y ^ 2 * thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda y)
      (2 * G - x ^ 2 * q) x := by
    have hleft := ((hasDerivAt_id x).const_mul 2).mul hGderiv
    have hright := ((hasDerivAt_id x).pow 2).mul hpderiv
    convert hleft.sub hright using 1
    all_goals
      simp only [G, q, Pi.pow_apply, id_eq]
      ring
  have hV : HasDerivAt (fun y : ℝ =>
      thetaCuspGaussianApertureExactTailSaddleGammaScale lambda y ^ 2 *
        thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda y)
      (2 * G * p ^ 2 + G ^ 2 * q) x := by
    convert (hGderiv.pow 2).mul hpderiv using 1
    all_goals
      simp only [G, p, q, Pi.pow_apply]
      ring
  have hVne : G ^ 2 * p ≠ 0 := by
    dsimp only [G, p]
    exact mul_ne_zero (pow_ne_zero _ hG) hp
  have hquot := hU.div hV hVne
  convert hquot using 1
  all_goals
    dsimp [thetaCuspGaussianApertureExactTailSaddleRatioDegreeSlope,
      thetaCuspGaussianApertureExactTailSaddleRatioDegreeCurvature,
      thetaCuspGaussianApertureExactTailSaddleCurvatureNumerator,
      thetaCuspGaussianApertureExactTailSaddleDefect, G, p, q]
    field_simp [hG, hp]
    ring

/-- Exact second derivative identity for the physical leading-channel saddle ratio. -/
theorem deriv_thetaCuspGaussianApertureExactTailSaddleRatioDegreeSlope_div_degree
    {lambda x : ℝ}
    (hG : thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x ≠ 0)
    (hp : thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x ≠ 0) :
    deriv (thetaCuspGaussianApertureExactTailSaddleRatioDegreeSlope lambda) x /
        deriv (thetaCuspGaussianApertureExactTailSaddleDegree lambda) x =
      thetaCuspGaussianApertureExactTailSaddleRatioDegreeCurvature lambda x := by
  rw [(hasDerivAt_thetaCuspGaussianApertureExactTailSaddleRatioDegreeSlope
      hG hp).deriv,
    (hasDerivAt_thetaCuspGaussianApertureExactTailSaddleDegree lambda x).deriv]
  field_simp [hp]

private theorem thetaCusp_exactTailSaddleCurvatureNumerator_pos_of_chamber
    {A ell x : ℝ} (hA : 3 < A) (hell : 0 ≤ ell) (hx : 6 ≤ x)
    (hsmall : 4 * ell * x ≤ A) :
    0 <
      (A * (1 + 2 * x) + 2 * ell * x - 9 / 4) *
          (1 / 2 - ell * x ^ 2 - 2 * A * x ^ 2) ^ 2 -
        x * (4 * A * (1 + x) + 2 * ell) *
          (A * x + ell * x ^ 2 - 9 * x / 4 + 1 / 2) ^ 2 := by
  have hA0 : 0 < A := by linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hell_le_mul : ell ≤ ell * x := by
    nlinarith [mul_nonneg hell (sub_nonneg.mpr hx1)]
  have hell_mul_le : ell * x ≤ A / 4 := by linarith
  have hell_le : ell ≤ A / 4 := hell_le_mul.trans hell_mul_le
  have hell_sq_le : ell * x ^ 2 ≤ A * x / 4 := by
    have h := mul_le_mul_of_nonneg_right hsmall hx0.le
    nlinarith
  have hAx : 0 < A * x := mul_pos hA0 hx0
  have hhalf : (1 / 2 : ℝ) ≤ A * x / 4 := by nlinarith
  let p := A * (1 + 2 * x) + 2 * ell * x - 9 / 4
  let q := 4 * A * (1 + x) + 2 * ell
  let G := A * x + ell * x ^ 2 - 9 * x / 4 + 1 / 2
  let D := 1 / 2 - ell * x ^ 2 - 2 * A * x ^ 2
  let P := 2 * A * x
  let Q := 9 * A * x
  let B := (3 / 2 : ℝ) * A * x
  let K := (3 / 2 : ℝ) * A * x ^ 2
  have hP : 0 < P := by dsimp [P]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hp : P < p := by
    dsimp [P, p]
    nlinarith
  have hG0 : 0 < G := by
    dsimp [G]
    have hprod : 0 < (A - 9 / 4) * x :=
      mul_pos (by linarith) hx0
    nlinarith
  have hG : G ≤ B := by
    dsimp [G, B]
    nlinarith
  have hq0 : 0 < q := by
    dsimp [q]
    positivity
  have hq : q ≤ Q := by
    dsimp [q, Q]
    have hone : 1 + x ≤ 2 * x := by linarith
    have hmain := mul_le_mul_of_nonneg_left hone
      (by positivity : 0 ≤ 4 * A)
    nlinarith
  have hD : D ≤ -K := by
    dsimp [D, K]
    have hAxSq : 1 ≤ A * x ^ 2 := by
      have : 0 < A * x ^ 2 := mul_pos hA0 (sq_pos_of_pos hx0)
      nlinarith
    nlinarith
  have hDsq : K ^ 2 ≤ D ^ 2 := by
    have hnegD : K ≤ -D := by linarith
    have hnegD0 : 0 ≤ -D := hK.le.trans hnegD
    convert (sq_le_sq₀ hK.le hnegD0).2 hnegD using 1
    ring
  have hGsq : G ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ hG0.le hB.le).2 hG
  have hPD : P * K ^ 2 < p * D ^ 2 := by
    have hp0 : 0 < p := hP.trans hp
    calc
      P * K ^ 2 < p * K ^ 2 := mul_lt_mul_of_pos_right hp (sq_pos_of_pos hK)
      _ ≤ p * D ^ 2 := mul_le_mul_of_nonneg_left hDsq hp0.le
  have htail : x * q * G ^ 2 ≤ x * Q * B ^ 2 := by
    have hxq : x * q ≤ x * Q := mul_le_mul_of_nonneg_left hq hx0.le
    exact calc
      x * q * G ^ 2 ≤ x * q * B ^ 2 :=
        mul_le_mul_of_nonneg_left hGsq (mul_nonneg hx0.le hq0.le)
      _ ≤ x * Q * B ^ 2 :=
        mul_le_mul_of_nonneg_right hxq (sq_nonneg B)
  have hscale : x * Q * B ^ 2 ≤ P * K ^ 2 := by
    let C := A ^ 3 * x ^ 4
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hcoef : (81 / 4 : ℝ) ≤ (9 / 2 : ℝ) * x := by linarith
    rw [show x * Q * B ^ 2 = (81 / 4 : ℝ) * C by
      dsimp [Q, B, C]
      ring]
    rw [show P * K ^ 2 = (9 / 2 : ℝ) * x * C by
      dsimp [P, K, C]
      ring]
    exact mul_le_mul_of_nonneg_right hcoef hC
  dsimp [p, q, G, D] at hp hG0 hG hq0 hq hD hDsq hPD htail ⊢
  linarith

private theorem three_lt_pi_mul_exp_two_of_six_le
    {x : ℝ} (hx : 6 ≤ x) :
    3 < Real.pi * Real.exp (2 * x) := by
  have hexp : 1 < Real.exp (2 * x) :=
    Real.one_lt_exp_iff.mpr (by linarith)
  have hgain : 0 < Real.pi * (Real.exp (2 * x) - 1) :=
    mul_pos Real.pi_pos (sub_pos.mpr hexp)
  nlinarith [Real.pi_gt_three]

theorem thetaCuspGaussianApertureExactTailSaddleGammaScale_pos
    {lambda x : ℝ} (hlambda : lambda ≤ 0) (hx : 6 ≤ x) :
    0 < thetaCuspGaussianApertureExactTailSaddleGammaScale lambda x := by
  have hA := three_lt_pi_mul_exp_two_of_six_le hx
  have hx0 : 0 < x := by linarith
  have hmain : 0 < (Real.pi * Real.exp (2 * x) - 9 / 4) * x :=
    mul_pos (by linarith) hx0
  have haperture : 0 ≤ -lambda * x ^ 2 :=
    mul_nonneg (neg_nonneg.mpr hlambda) (sq_nonneg x)
  unfold thetaCuspGaussianApertureExactTailSaddleGammaScale
    thetaCuspGaussianApertureExactTailSaddleDegree
  nlinarith

theorem thetaCuspGaussianApertureExactTailSaddleDegreeSlope_pos
    {lambda x : ℝ} (hlambda : lambda ≤ 0) (hx : 6 ≤ x) :
    0 < thetaCuspGaussianApertureExactTailSaddleDegreeSlope lambda x := by
  have hA := three_lt_pi_mul_exp_two_of_six_le hx
  have hA0 : 0 < Real.pi * Real.exp (2 * x) := by positivity
  have hx0 : 0 < x := by linarith
  have haperture : 0 ≤ -2 * lambda * x := by
    exact mul_nonneg (by nlinarith : 0 ≤ -2 * lambda) hx0.le
  unfold thetaCuspGaussianApertureExactTailSaddleDegreeSlope
  nlinarith [mul_pos hA0 (by linarith : 0 < 1 + 2 * x)]

/-- **Exact physical saddle chamber.**  Once height is at least six and the cusp scale dominates
the bounded aperture perturbation by `-4 lambda x ≤ π exp(2x)`, the exact leading-channel
degree-curvature numerator is strictly positive. -/
theorem thetaCuspGaussianApertureExactTailSaddleCurvatureNumerator_pos
    {lambda x : ℝ} (hlambda : lambda ≤ 0) (hx : 6 ≤ x)
    (haperture : -4 * lambda * x ≤ Real.pi * Real.exp (2 * x)) :
    0 < thetaCuspGaussianApertureExactTailSaddleCurvatureNumerator lambda x := by
  let A := Real.pi * Real.exp (2 * x)
  let ell := -lambda
  have hA : 3 < A := by
    simpa only [A] using three_lt_pi_mul_exp_two_of_six_le hx
  have hell : 0 ≤ ell := by dsimp [ell]; linarith
  have hsmall : 4 * ell * x ≤ A := by
    dsimp only [ell, A]
    nlinarith
  have h := thetaCusp_exactTailSaddleCurvatureNumerator_pos_of_chamber
    hA hell hx hsmall
  simp only [thetaCuspGaussianApertureExactTailSaddleCurvatureNumerator,
    thetaCuspGaussianApertureExactTailSaddleGammaScale,
    thetaCuspGaussianApertureExactTailSaddleDegree,
    thetaCuspGaussianApertureExactTailSaddleDegreeSlope,
    thetaCuspGaussianApertureExactTailSaddleDegreeCurvature,
    thetaCuspGaussianApertureExactTailSaddleDefect_eq]
  dsimp only [A, ell] at h
  convert h using 1
  all_goals ring

/-- Strict degree convexity of the exact aperture- and amplitude-corrected leading saddle. -/
theorem thetaCuspGaussianApertureExactTailSaddleRatioDegreeCurvature_pos
    {lambda x : ℝ} (hlambda : lambda ≤ 0) (hx : 6 ≤ x)
    (haperture : -4 * lambda * x ≤ Real.pi * Real.exp (2 * x)) :
    0 < thetaCuspGaussianApertureExactTailSaddleRatioDegreeCurvature lambda x := by
  unfold thetaCuspGaussianApertureExactTailSaddleRatioDegreeCurvature
  exact div_pos
    (mul_pos (by norm_num)
      (thetaCuspGaussianApertureExactTailSaddleCurvatureNumerator_pos
        hlambda hx haperture))
    (mul_pos
      (pow_pos
        (thetaCuspGaussianApertureExactTailSaddleGammaScale_pos hlambda hx) 3)
      (pow_pos
        (thetaCuspGaussianApertureExactTailSaddleDegreeSlope_pos hlambda hx) 3))

/-- Gamma-normalized adjacent moment ratio.  A pure Gaussian has the same value at every `j`. -/
def thetaCuspGaussianApertureGammaRatio (lambda : ℝ) (j : ℕ) : ℝ :=
  (thetaCuspGaussianApertureHalfMoment lambda (j + 1) /
      thetaCuspGaussianApertureHalfMoment lambda j) /
    thetaCuspGaussianApertureGammaShape j

/-- Boundary second difference of consecutive gamma-normalized ratios. -/
def thetaCuspGaussianApertureRatioCurvature (lambda : ℝ) (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureGammaRatio lambda j -
    2 * thetaCuspGaussianApertureGammaRatio lambda (j + 1) +
    thetaCuspGaussianApertureGammaRatio lambda (j + 2)

/-- Autonomous velocity of one gamma-normalized ratio under Gaussian aperture flow. -/
def thetaCuspGaussianApertureGammaRatioVelocity (lambda : ℝ) (j : ℕ) : ℝ :=
  thetaCuspGaussianApertureGammaRatio lambda j *
    (thetaCuspGaussianApertureGammaShape (j + 1) *
        thetaCuspGaussianApertureGammaRatio lambda (j + 1) -
      thetaCuspGaussianApertureGammaShape j *
        thetaCuspGaussianApertureGammaRatio lambda j)

/-- Reaction coefficient in the exact discrete curvature equation. -/
def thetaCuspGaussianApertureRatioCurvatureReaction (lambda : ℝ) (j : ℕ) : ℝ :=
  -(thetaCuspGaussianApertureGammaShape j + 4) *
      thetaCuspGaussianApertureGammaRatio lambda j +
    (1 - thetaCuspGaussianApertureGammaShape j) *
      thetaCuspGaussianApertureGammaRatio lambda (j + 1) +
    (thetaCuspGaussianApertureGammaShape j + 4) *
      thetaCuspGaussianApertureGammaRatio lambda (j + 2)

theorem thetaCuspGaussianApertureGammaShape_pos (j : ℕ) :
    0 < thetaCuspGaussianApertureGammaShape j := by
  rw [thetaCuspGaussianApertureGammaShape]
  positivity

/-- Differentiating the literal aperture inserts one factor `x^2`, hence advances the moment
index by one.  The open condition `lambda < 0` supplies a local integrable majorant. -/
theorem hasDerivAt_thetaCuspGaussianApertureHalfMoment
    {lambda : ℝ} (hlambda : lambda < 0) (j : ℕ) :
    HasDerivAt (fun eta => thetaCuspGaussianApertureHalfMoment eta j)
      (thetaCuspGaussianApertureHalfMoment lambda (j + 1)) lambda := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ → ℝ → ℝ := fun eta x =>
    x ^ (2 * j) * thetaCuspGaussianApertureDensity eta x
  let F' : ℝ → ℝ → ℝ := fun eta x =>
    x ^ (2 * (j + 1)) * thetaCuspGaussianApertureDensity eta x
  let bound : ℝ → ℝ := fun x => x ^ (2 * (j + 1)) * thetaCuspFullSource x
  have hs : Iio (lambda / 2) ∈ nhds lambda :=
    Iio_mem_nhds (by linarith)
  have hFmeas : ∀ᶠ eta : ℝ in nhds lambda, AEStronglyMeasurable (F eta) mu := by
    filter_upwards [] with eta
    exact Continuous.aestronglyMeasurable
      (continuous_thetaCuspGaussianApertureMomentIntegrand eta j) (μ := mu)
  have hFint : Integrable (F lambda) mu := by
    simpa only [F, mu] using
      integrableOn_thetaCuspGaussianApertureMomentIntegrand hlambda.le j
  have hF'meas : AEStronglyMeasurable (F' lambda) mu := by
    exact Continuous.aestronglyMeasurable
      (continuous_thetaCuspGaussianApertureMomentIntegrand lambda (j + 1)) (μ := mu)
  have hbound : ∀ᵐ x : ℝ ∂mu, ∀ eta ∈ Iio (lambda / 2),
      ‖F' eta x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx eta heta
    have hhalf : lambda / 2 < 0 := div_neg_of_neg_of_pos hlambda (by norm_num)
    have hetaNonpos : eta ≤ 0 := (heta.trans hhalf).le
    have hpow : 0 ≤ x ^ (2 * (j + 1)) := pow_nonneg hx.le _
    have hsource : 0 ≤ thetaCuspFullSource x :=
      (thetaCuspFullSource_pos_of_pos hx).le
    have hexpNonneg : 0 ≤ Real.exp (eta * x ^ 2) := Real.exp_nonneg _
    have hexpLe : Real.exp (eta * x ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg hetaNonpos (sq_nonneg x))
    dsimp only [F', bound, thetaCuspGaussianApertureDensity]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg hpow (mul_nonneg hexpNonneg hsource))]
    nlinarith [mul_nonneg hpow hsource]
  have hboundInt : Integrable bound mu := by
    simpa only [bound, mu] using integrableOn_thetaCuspRawMoment (2 * (j + 1))
  have hdiff : ∀ᵐ x : ℝ ∂mu, ∀ eta ∈ Iio (lambda / 2),
      HasDerivAt (fun z => F z x) (F' eta x) eta := by
    filter_upwards [] with x eta heta
    have hexp : HasDerivAt (fun z : ℝ => Real.exp (z * x ^ 2))
        (Real.exp (eta * x ^ 2) * x ^ 2) eta := by
      simpa only [one_mul] using
        (Real.hasDerivAt_exp (eta * x ^ 2)).comp eta
          ((hasDerivAt_id eta).mul_const (x ^ 2))
    have hscaled := hexp.const_mul (x ^ (2 * j) * thetaCuspFullSource x)
    convert hscaled using 1
    · funext z
      simp only [F, thetaCuspGaussianApertureDensity]
      ring
    · simp only [F', thetaCuspGaussianApertureDensity]
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
      ring
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hFmeas hFint hF'meas hbound hboundInt hdiff
  simpa only [thetaCuspGaussianApertureHalfMoment, F, F', mu] using hresult.2

theorem thetaCuspGaussianApertureGammaRatio_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    0 < thetaCuspGaussianApertureGammaRatio lambda j := by
  rw [thetaCuspGaussianApertureGammaRatio]
  exact div_pos
    (div_pos (thetaCuspGaussianApertureHalfMoment_pos hlambda (j + 1))
      (thetaCuspGaussianApertureHalfMoment_pos hlambda j))
    (thetaCuspGaussianApertureGammaShape_pos j)

/-- Exact autonomous Riccati flow of the actual gamma-normalized theta moment ratio. -/
theorem hasDerivAt_thetaCuspGaussianApertureGammaRatio
    {lambda : ℝ} (hlambda : lambda < 0) (j : ℕ) :
    HasDerivAt (fun eta => thetaCuspGaussianApertureGammaRatio eta j)
      (thetaCuspGaussianApertureGammaRatioVelocity lambda j) lambda := by
  have hgeneric := HTGeometry.hasDerivAt_normalizedMomentRatio
    (M := thetaCuspGaussianApertureHalfMoment)
    (a := thetaCuspGaussianApertureGammaShape) (lambda := lambda) j
    (fun k => hasDerivAt_thetaCuspGaussianApertureHalfMoment hlambda k)
    (fun k => (thetaCuspGaussianApertureHalfMoment_pos hlambda.le k).ne')
    (fun k => (thetaCuspGaussianApertureGammaShape_pos k).ne')
  simpa only [HTGeometry.normalizedMomentRatio,
    HTGeometry.weightedMomentRatioVelocity,
    thetaCuspGaussianApertureGammaRatio,
    thetaCuspGaussianApertureGammaRatioVelocity] using hgeneric

/-- Literal derivative of one ratio-curvature coordinate. -/
theorem hasDerivAt_thetaCuspGaussianApertureRatioCurvature
    {lambda : ℝ} (hlambda : lambda < 0) (j : ℕ) :
    HasDerivAt (fun eta => thetaCuspGaussianApertureRatioCurvature eta j)
      (thetaCuspGaussianApertureGammaRatioVelocity lambda j -
        2 * thetaCuspGaussianApertureGammaRatioVelocity lambda (j + 1) +
        thetaCuspGaussianApertureGammaRatioVelocity lambda (j + 2)) lambda := by
  have h0 := hasDerivAt_thetaCuspGaussianApertureGammaRatio hlambda j
  have h1 := (hasDerivAt_thetaCuspGaussianApertureGammaRatio hlambda (j + 1)).const_mul 2
  have h2 := hasDerivAt_thetaCuspGaussianApertureGammaRatio hlambda (j + 2)
  convert (h0.sub h1).add h2 using 1

/-- The completed theta curvature flow is the literal source specialization of the universal
affine-Gamma moment-curvature theorem.  This stronger `HasDerivAt` form supplies both the closed
parabolic-reaction law and all derivative consumers below. -/
theorem hasDerivAt_thetaCuspGaussianApertureRatioCurvature_affineGamma
    {lambda : ℝ} (hlambda : lambda < 0) (j : ℕ) :
    HasDerivAt (fun eta => thetaCuspGaussianApertureRatioCurvature eta j)
      (4 * (thetaCuspGaussianApertureGammaRatio lambda j -
          thetaCuspGaussianApertureGammaRatio lambda (j + 1)) ^ 2 +
        thetaCuspGaussianApertureGammaShape (j + 3) *
          thetaCuspGaussianApertureGammaRatio lambda (j + 2) *
          thetaCuspGaussianApertureRatioCurvature lambda (j + 1) +
        thetaCuspGaussianApertureRatioCurvature lambda j *
          thetaCuspGaussianApertureRatioCurvatureReaction lambda j) lambda := by
  have hgeneric :=
    HTGeometry.hasDerivAt_normalizedMomentRatioCurvature_of_affineWeights
      (M := thetaCuspGaussianApertureHalfMoment)
      (a := thetaCuspGaussianApertureGammaShape)
      (lambda := lambda) (A := thetaCuspGaussianApertureGammaShape j) (h := 1) j
      (fun k => hasDerivAt_thetaCuspGaussianApertureHalfMoment hlambda k)
      (fun k => (thetaCuspGaussianApertureHalfMoment_pos hlambda.le k).ne')
      (fun k => (thetaCuspGaussianApertureGammaShape_pos k).ne')
      rfl
      (by simp [thetaCuspGaussianApertureGammaShape, Nat.cast_add]; ring)
      (by simp [thetaCuspGaussianApertureGammaShape, Nat.cast_add]; ring)
      (by simp [thetaCuspGaussianApertureGammaShape, Nat.cast_add]; ring)
  convert hgeneric using 1
  simp only [HTGeometry.normalizedMomentRatio, HTGeometry.ratioSecondCurvature,
    thetaCuspGaussianApertureGammaRatio,
    thetaCuspGaussianApertureRatioCurvature,
    thetaCuspGaussianApertureRatioCurvatureReaction,
    thetaCuspGaussianApertureGammaShape]
  push_cast
  ring

/-- **Discrete parabolic-reaction law.**  The curvature velocity is a positive square, transport
from the next curvature level, and a reaction multiple of the current curvature. -/
theorem deriv_thetaCuspGaussianApertureRatioCurvature_eq
    {lambda : ℝ} (hlambda : lambda < 0) (j : ℕ) :
    deriv (fun eta => thetaCuspGaussianApertureRatioCurvature eta j) lambda =
      4 * (thetaCuspGaussianApertureGammaRatio lambda j -
          thetaCuspGaussianApertureGammaRatio lambda (j + 1)) ^ 2 +
        thetaCuspGaussianApertureGammaShape (j + 3) *
          thetaCuspGaussianApertureGammaRatio lambda (j + 2) *
          thetaCuspGaussianApertureRatioCurvature lambda (j + 1) +
        thetaCuspGaussianApertureRatioCurvature lambda j *
          thetaCuspGaussianApertureRatioCurvatureReaction lambda j := by
  exact
    (hasDerivAt_thetaCuspGaussianApertureRatioCurvature_affineGamma hlambda j).deriv

/-- On a zero-curvature boundary, only the positive square and next-level transport survive. -/
theorem deriv_thetaCuspGaussianApertureRatioCurvature_eq_of_eq_zero
    {lambda : ℝ} (hlambda : lambda < 0) (j : ℕ)
    (hzero : thetaCuspGaussianApertureRatioCurvature lambda j = 0) :
    deriv (fun eta => thetaCuspGaussianApertureRatioCurvature eta j) lambda =
      4 * (thetaCuspGaussianApertureGammaRatio lambda j -
          thetaCuspGaussianApertureGammaRatio lambda (j + 1)) ^ 2 +
        thetaCuspGaussianApertureGammaShape (j + 3) *
          thetaCuspGaussianApertureGammaRatio lambda (j + 2) *
          thetaCuspGaussianApertureRatioCurvature lambda (j + 1) := by
  rw [deriv_thetaCuspGaussianApertureRatioCurvature_eq hlambda, hzero, zero_mul, add_zero]

/-- **Forward barrier.**  If level `j` is at zero and level `j+1` is nonnegative, the actual
Gaussian flow cannot point into the negative-curvature chamber at level `j`. -/
theorem deriv_thetaCuspGaussianApertureRatioCurvature_nonneg_of_boundary
    {lambda : ℝ} (hlambda : lambda < 0) (j : ℕ)
    (hzero : thetaCuspGaussianApertureRatioCurvature lambda j = 0)
    (hnext : 0 ≤ thetaCuspGaussianApertureRatioCurvature lambda (j + 1)) :
    0 ≤ deriv (fun eta => thetaCuspGaussianApertureRatioCurvature eta j) lambda := by
  rw [deriv_thetaCuspGaussianApertureRatioCurvature_eq_of_eq_zero hlambda j hzero]
  exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg
      (mul_nonneg (thetaCuspGaussianApertureGammaShape_pos (j + 3)).le
        (thetaCuspGaussianApertureGammaRatio_pos hlambda.le (j + 2)).le)
      hnext)

/-- **Quantitative entrance cascade.**  If curvature at level `j` is zero but is moving into the
negative chamber, the next curvature level is already negative by an explicit square margin.
Thus a forward loss cannot originate at a finite terminal degree. -/
theorem thetaCuspGaussianApertureRatioCurvature_next_mul_lt_of_boundary_deriv_neg
    {lambda : ℝ} (hlambda : lambda < 0) (j : ℕ)
    (hzero : thetaCuspGaussianApertureRatioCurvature lambda j = 0)
    (hderiv : deriv (fun eta => thetaCuspGaussianApertureRatioCurvature eta j) lambda < 0) :
    thetaCuspGaussianApertureGammaShape (j + 3) *
          thetaCuspGaussianApertureGammaRatio lambda (j + 2) *
          thetaCuspGaussianApertureRatioCurvature lambda (j + 1) <
      -4 * (thetaCuspGaussianApertureGammaRatio lambda j -
          thetaCuspGaussianApertureGammaRatio lambda (j + 1)) ^ 2 := by
  rw [deriv_thetaCuspGaussianApertureRatioCurvature_eq_of_eq_zero
    hlambda j hzero] at hderiv
  linarith

/-- A negative forward crossing at one degree forces a strict negative curvature one level
higher.  This is the local form of the `failure must enter from infinity` principle. -/
theorem thetaCuspGaussianApertureRatioCurvature_next_neg_of_boundary_deriv_neg
    {lambda : ℝ} (hlambda : lambda < 0) (j : ℕ)
    (hzero : thetaCuspGaussianApertureRatioCurvature lambda j = 0)
    (hderiv : deriv (fun eta => thetaCuspGaussianApertureRatioCurvature eta j) lambda < 0) :
    thetaCuspGaussianApertureRatioCurvature lambda (j + 1) < 0 := by
  have htransport :=
    thetaCuspGaussianApertureRatioCurvature_next_mul_lt_of_boundary_deriv_neg
      hlambda j hzero hderiv
  have hcoeff : 0 < thetaCuspGaussianApertureGammaShape (j + 3) *
      thetaCuspGaussianApertureGammaRatio lambda (j + 2) :=
    mul_pos (thetaCuspGaussianApertureGammaShape_pos (j + 3))
      (thetaCuspGaussianApertureGammaRatio_pos hlambda.le (j + 2))
  have hsquare : 0 ≤
      4 * (thetaCuspGaussianApertureGammaRatio lambda j -
        thetaCuspGaussianApertureGammaRatio lambda (j + 1)) ^ 2 := by positivity
  nlinarith

/-! ### Identification with the actual GABTC balance -/

/-- The first ratio-curvature coordinate is exactly the Gaussian-aperture balance, including its
forced numerical normalization. -/
theorem thetaCuspGaussianApertureBalance_eq_ratioCurvature (lambda : ℝ) :
    thetaCuspGaussianApertureBalance lambda =
      (15 / 2 : ℝ) * thetaCuspGaussianApertureRatioCurvature lambda 0 := by
  simp only [thetaCuspGaussianApertureBalance,
    thetaCuspGaussianApertureMoment_eq_two_mul_halfMoment,
    thetaCuspGaussianApertureRatioCurvature,
    thetaCuspGaussianApertureGammaRatio,
    thetaCuspGaussianApertureGammaShape]
  norm_num
  ring

/-- The literal GABTC balance inherits the discrete moment-flow derivative. -/
theorem hasDerivAt_thetaCuspGaussianApertureBalance
    {lambda : ℝ} (hlambda : lambda < 0) :
    HasDerivAt thetaCuspGaussianApertureBalance
      ((15 / 2 : ℝ) *
        (thetaCuspGaussianApertureGammaRatioVelocity lambda 0 -
          2 * thetaCuspGaussianApertureGammaRatioVelocity lambda 1 +
          thetaCuspGaussianApertureGammaRatioVelocity lambda 2)) lambda := by
  have hcurv :=
    (hasDerivAt_thetaCuspGaussianApertureRatioCurvature hlambda 0).const_mul
      (15 / 2 : ℝ)
  convert hcurv using 1
  funext eta
  exact thetaCuspGaussianApertureBalance_eq_ratioCurvature eta

/-- **GABTC forward barrier.**  At a zero of the physical aperture balance, nonnegative curvature
at the next degree prevents the balance from crossing forward into the negative chamber. -/
theorem deriv_thetaCuspGaussianApertureBalance_nonneg_of_boundary
    {lambda : ℝ} (hlambda : lambda < 0)
    (hzero : thetaCuspGaussianApertureBalance lambda = 0)
    (hnext : 0 ≤ thetaCuspGaussianApertureRatioCurvature lambda 1) :
    0 ≤ deriv thetaCuspGaussianApertureBalance lambda := by
  have hzeroCurv : thetaCuspGaussianApertureRatioCurvature lambda 0 = 0 := by
    rw [thetaCuspGaussianApertureBalance_eq_ratioCurvature] at hzero
    linarith
  have hcurv := deriv_thetaCuspGaussianApertureRatioCurvature_nonneg_of_boundary
    hlambda 0 hzeroCurv hnext
  have hcurvDeriv :=
    (hasDerivAt_thetaCuspGaussianApertureRatioCurvature hlambda 0).deriv
  have hbalanceDeriv := (hasDerivAt_thetaCuspGaussianApertureBalance hlambda).deriv
  rw [hcurvDeriv] at hcurv
  rw [hbalanceDeriv]
  nlinarith

/-- If the physical GABTC balance crosses forward through zero in the wrong direction, the next
degree curvature is already strictly negative. -/
theorem thetaCuspGaussianApertureRatioCurvature_one_neg_of_balance_boundary_deriv_neg
    {lambda : ℝ} (hlambda : lambda < 0)
    (hzero : thetaCuspGaussianApertureBalance lambda = 0)
    (hderiv : deriv thetaCuspGaussianApertureBalance lambda < 0) :
    thetaCuspGaussianApertureRatioCurvature lambda 1 < 0 := by
  by_contra hnot
  have hnext : 0 ≤ thetaCuspGaussianApertureRatioCurvature lambda 1 := le_of_not_gt hnot
  exact (not_lt_of_ge
    (deriv_thetaCuspGaussianApertureBalance_nonneg_of_boundary
      hlambda hzero hnext)) hderiv

end

end RHTower
