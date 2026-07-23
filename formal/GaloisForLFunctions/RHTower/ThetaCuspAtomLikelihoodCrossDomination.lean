import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodGapCumulantRiccati
import GaloisForLFunctions.RHTower.ThetaCuspReflectedRiccatiAngle

/-!
# Atom domination of theta likelihood Riccati interference

Existing symbolic tail bounds control the reflected likelihood jets.  A new uniform half-factor
law for the first theta atom then yields a purely algebraic atom-margin estimate which strictly
dominates the negative atom--likelihood Riccati channel.  Consequently the completed reflected
Riccati margin, and hence the same-half-line correlation-angle law, are unconditional.
-/

open Set Filter Topology

namespace RHTower

noncomputable section

/-- The exact reflected first-atom factor stays strictly above one half throughout the closed
same-half-line chamber. -/
theorem one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    1 / 2 <
      thetaCuspSingleAtomReflectionFactor
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t) := by
  let Y := Real.exp (2 * u)
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let Z := (Y - 1) ^ 2 / (2 * Y)
  have hu : 0 ≤ u := le_trans ht htu
  have hY : 0 < Y := by
    dsimp [Y]
    positivity
  have hYone : 1 ≤ Y := by
    dsimp [Y]
    exact Real.one_le_exp (by linarith)
  have hA : 0 < A := by
    dsimp [A, thetaCuspSingleAtomReflectionScale]
    positivity
  have hcosh :
      Real.cosh (2 * t) ≤ Real.cosh (2 * u) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (by linarith : 0 ≤ 2 * t),
      abs_of_nonneg (by linarith : 0 ≤ 2 * u)]
    linarith
  have hcoshZ : Real.cosh (2 * u) - 1 = Z := by
    dsimp [Z, Y]
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp [hY.ne']
    ring
  have hzle : z ≤ Z := by
    dsimp [z, thetaCuspSingleAtomReflectionDefect]
    rw [← hcoshZ]
    linarith
  have hAZ : 6 * A * Z = 3 * Real.pi * (Y - 1) ^ 2 := by
    dsimp [A, Z, Y, thetaCuspSingleAtomReflectionScale]
    simp only [Nat.cast_one, one_pow]
    field_simp [Real.exp_ne_zero]
    ring
  have hgapIdentity :
      (A - 3 / 2) ^ 2 - 3 * Real.pi * (Y - 1) ^ 2 =
        Real.pi * (Real.pi - 3) * Y ^ 2 +
          3 * Real.pi * (Y - 1) + 9 / 4 := by
    dsimp [A, Y, thetaCuspSingleAtomReflectionScale]
    simp only [Nat.cast_one, one_pow]
    ring
  have hgapPos :
      0 < (A - 3 / 2) ^ 2 - 3 * Real.pi * (Y - 1) ^ 2 := by
    rw [hgapIdentity]
    have hpiGap : 0 < Real.pi - 3 := sub_pos.mpr Real.pi_gt_three
    have hYsq : 0 < Y ^ 2 := sq_pos_of_pos hY
    have hfirst :
        0 < Real.pi * (Real.pi - 3) * Y ^ 2 := by positivity
    have hsecond : 0 ≤ 3 * Real.pi * (Y - 1) := by positivity
    positivity
  have hmain : 6 * A * z < (A - 3 / 2) ^ 2 := by
    have hle : 6 * A * z ≤ 6 * A * Z :=
      mul_le_mul_of_nonneg_left hzle (mul_nonneg (by norm_num) hA.le)
    rw [hAZ] at hle
    linarith
  have hden : 0 < (A - 3 / 2) ^ 2 := by
    have hAthree : 3 < A := by
      simpa only [A] using
        three_lt_thetaCuspSingleAtomReflectionScale
          (n := 1) (by norm_num) hu
    exact sq_pos_of_pos (by linarith)
  have hratio :
      thetaCuspSingleAtomReflectionLambda A * z < 1 / 2 := by
    unfold thetaCuspSingleAtomReflectionLambda
    rw [show
      3 * A / (A - 3 / 2) ^ 2 * z =
        (3 * A * z) / (A - 3 / 2) ^ 2 by ring]
    apply (div_lt_iff₀ hden).2
    nlinarith
  unfold thetaCuspSingleAtomReflectionFactor
  linarith

/-- The existing positive-half-line likelihood curvature estimate, expressed in the cumulant
source coordinates. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_thirteen_tenths
    {x : ℝ} (hx : 0 < x) :
    thetaCuspLikelihoodSourceLogPartitionJetTwo x < 13 / 10 := by
  rw [thetaCuspLikelihoodSourceLogPartitionJetTwo_eq_higherLikelihoodLogJetTwo hx]
  exact (thetaCuspHigherLikelihoodLogJetTwo_le hx).trans_lt
    (thetaCuspHigherLikelihoodJetTwo_lt hx)

/-- Closed-half-line version of the likelihood curvature bound. -/
theorem thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspLikelihoodSourceLogPartitionJetTwo x ≤ 13 / 10 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · apply le_of_tendsto
      ((hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo
          (thetaCuspLikelihoodCoordinate_pos le_rfl)).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left))
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact
      (thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_thirteen_tenths hy).le
  · exact
      (thetaCuspLikelihoodSourceLogPartitionJetTwo_lt_thirteen_tenths hx).le

/-- The magnitude of the negative reflected likelihood second jet is at most `13/5`. -/
theorem neg_thetaCuspReflectedLikelihoodCumulantJetTwo_le_thirteen_fifths
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    -thetaCuspReflectedLikelihoodCumulantJetTwo u t ≤ 13 / 5 := by
  have hminus :=
    thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths
      (show 0 ≤ u - t by linarith)
  have hplus :=
    thetaCuspLikelihoodSourceLogPartitionJetTwo_le_thirteen_tenths
      (show 0 ≤ u + t by linarith)
  unfold thetaCuspReflectedLikelihoodCumulantJetTwo
  linarith

/-- Mean-value transport bounds the negative reflected first jet by elapsed displacement. -/
theorem neg_thetaCuspReflectedLikelihoodCumulantJetOne_le_thirteen_fifths_mul
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    -thetaCuspReflectedLikelihoodCumulantJetOne u t ≤ 13 / 5 * t := by
  let f := thetaCuspReflectedLikelihoodCumulantJetOne u
  have hcont : ContinuousOn f (Icc 0 t) := by
    intro s hs
    rcases hs with ⟨hs0, hst⟩
    have hplus :
        0 < thetaCuspLikelihoodCoordinate (u + s) :=
      thetaCuspLikelihoodCoordinate_pos (by linarith)
    have hminus :
        0 < thetaCuspLikelihoodCoordinate (u - s) :=
      thetaCuspLikelihoodCoordinate_pos (by linarith)
    exact (hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetOne
      hplus hminus).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc 0 t)) := by
    intro s hs
    rw [interior_Icc] at hs
    rcases hs with ⟨hs0, hst⟩
    have hplus :
        0 < thetaCuspLikelihoodCoordinate (u + s) :=
      thetaCuspLikelihoodCoordinate_pos (by linarith)
    have hminus :
        0 < thetaCuspLikelihoodCoordinate (u - s) :=
      thetaCuspLikelihoodCoordinate_pos (by linarith)
    exact (hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetOne
      hplus hminus).differentiableAt.differentiableWithinAt
  have hderiv :
      ∀ s ∈ interior (Icc 0 t), -(13 / 5 : ℝ) ≤ deriv f s := by
    intro s hs
    rw [interior_Icc] at hs
    rcases hs with ⟨hs0, hst⟩
    have hplus :
        0 < thetaCuspLikelihoodCoordinate (u + s) :=
      thetaCuspLikelihoodCoordinate_pos (by linarith)
    have hminus :
        0 < thetaCuspLikelihoodCoordinate (u - s) :=
      thetaCuspLikelihoodCoordinate_pos (by linarith)
    rw [(hasDerivAt_thetaCuspReflectedLikelihoodCumulantJetOne
      hplus hminus).deriv]
    have hbound :=
      neg_thetaCuspReflectedLikelihoodCumulantJetTwo_le_thirteen_fifths
        hs0.le (hst.le.trans htu)
    linarith
  have hgrowth :=
    (convex_Icc 0 t).mul_sub_le_image_sub_of_le_deriv
      hcont hdiff hderiv 0 (by simp [ht]) t (by simp [ht]) ht
  dsimp [f] at hgrowth
  have hzero : thetaCuspReflectedLikelihoodCumulantJetOne u 0 = 0 := by
    unfold thetaCuspReflectedLikelihoodCumulantJetOne
    ring
  rw [hzero] at hgrowth
  linarith

/-- Hyperbolic velocity form of the reflected first-jet bound. -/
theorem neg_thetaCuspReflectedLikelihoodCumulantJetOne_le_velocity
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    -thetaCuspReflectedLikelihoodCumulantJetOne u t ≤
      13 / 20 * (2 * Real.sinh (2 * t)) := by
  have hlinear :=
    neg_thetaCuspReflectedLikelihoodCumulantJetOne_le_thirteen_fifths_mul
      ht htu
  have hsinh : 2 * t ≤ Real.sinh (2 * t) :=
    Real.self_le_sinh_iff.mpr (by linarith)
  nlinarith

/-- Pure atom algebra: the reduced atom margin dominates the coefficients forced by the two
likelihood-jet bounds. -/
theorem thetaCuspSingleAtomRiccatiReducedMargin_crossBudget
    {A z : ℝ} (hA : 3 < A) (hz : 0 ≤ z)
    (hr : 1 / 2 < thetaCuspSingleAtomReflectionFactor A z) :
    26 / 5 * thetaCuspSingleAtomReflectionSlope A z +
        13 / 10 * thetaCuspSingleAtomReflectedActionJetTwo A z <
      4 * thetaCuspSingleAtomReflectedReducedMargin A z := by
  let l := thetaCuspSingleAtomReflectionLambda A
  let r := thetaCuspSingleAtomReflectionFactor A z
  let w := l / r
  let K := (16 * A - 26 / 5) * z * (z + 2) - 4 * (z + 1)
  let H := (32 * A - 26 / 5) * (z + 1) - 46 / 5
  let J := A * ((32 * A - 52 / 5) * (z + 1) - 92 / 5)
  have hl : 0 < l := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_pos hA
  have hl4 : l ≤ 4 := by
    simpa only [l] using thetaCuspSingleAtomReflectionLambda_le_four hA.le
  have hr0 : 0 < r := by
    dsimp [r]
    linarith
  have hw : 0 < w := by
    dsimp [w]
    positivity
  have hw8 : w < 8 := by
    dsimp [w]
    apply (div_lt_iff₀ hr0).2
    nlinarith
  have hK : -4 ≤ K := by
    dsimp [K]
    have hcoeff : 0 < 16 * A - 26 / 5 := by linarith
    have hinner : 0 ≤ (16 * A - 26 / 5) * (z + 2) - 4 := by
      nlinarith [mul_nonneg (sub_pos.mpr hA).le hz]
    nlinarith [mul_nonneg hz hinner]
  have hH : 32 < H := by
    dsimp [H]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 32 * A - 26 / 5) hz]
  have hJ : 0 < J := by
    dsimp [J]
    have hA0 : 0 < A := by linarith
    have hinner :
        0 < (32 * A - 52 / 5) * (z + 1) - 92 / 5 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 32 * A - 52 / 5) hz]
    exact mul_pos hA0 hinner
  have hwSq : w ^ 2 < 8 * w := by
    nlinarith [mul_pos hw (sub_pos.mpr hw8)]
  have hKw : -4 * w ^ 2 ≤ K * w ^ 2 :=
    mul_le_mul_of_nonneg_right hK (sq_nonneg w)
  have hHw : 32 * w < H * w :=
    mul_lt_mul_of_pos_right hH hw
  have hpositive : 0 < K * w ^ 2 + H * w + J := by
    have hpair : 0 < K * w ^ 2 + H * w := by
      nlinarith
    linarith
  have hidentity :
      4 * thetaCuspSingleAtomReflectedReducedMargin A z -
          (26 / 5 * thetaCuspSingleAtomReflectionSlope A z +
            13 / 10 * thetaCuspSingleAtomReflectedActionJetTwo A z) =
        K * w ^ 2 + H * w + J := by
    unfold thetaCuspSingleAtomReflectedReducedMargin
      thetaCuspSingleAtomReflectionSlope
      thetaCuspSingleAtomReflectedActionJetTwo
    unfold thetaCuspSingleAtomReflectionSlope
    dsimp only
    dsimp [K, H, J, w, l, r]
    field_simp [hr0.ne']
    ring
  nlinarith [hidentity, hpositive]

/-- **Strict atom domination of interference.**  The first-atom margin alone dominates the
negative atom--likelihood cross channel. -/
theorem neg_thetaCuspReflectedAtomLikelihoodRiccatiCross_lt_atomMargin
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    -thetaCuspReflectedAtomLikelihoodRiccatiCross u t <
      thetaCuspSingleAtomReflectedRiccatiMargin
        (thetaCuspSingleAtomReflectionScale 1 u)
        (thetaCuspSingleAtomReflectionDefect t)
        (2 * Real.sinh (2 * t)) := by
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let zp := 2 * Real.sinh (2 * t)
  let a1 := thetaCuspSingleAtomReflectedActionJetOne A z zp
  let a2 := thetaCuspSingleAtomReflectedActionJetTwo A z
  let q1 := thetaCuspReflectedLikelihoodCumulantJetOne u t
  let q2 := thetaCuspReflectedLikelihoodCumulantJetTwo u t
  let S := thetaCuspSingleAtomReflectionSlope A z
  let R := thetaCuspSingleAtomReflectedReducedMargin A z
  have hu : 0 ≤ u := le_trans ht.le htu
  have hA : 3 < A := by
    simpa only [A] using
      three_lt_thetaCuspSingleAtomReflectionScale
        (n := 1) (by norm_num) hu
  have hz : 0 ≤ z := by
    dsimp [z, thetaCuspSingleAtomReflectionDefect]
    exact sub_nonneg.mpr (Real.one_le_cosh (2 * t))
  have hzp : 0 < zp := by
    dsimp [zp]
    have := Real.sinh_pos_iff.mpr (show 0 < 2 * t by linarith)
    positivity
  have hrHalf : 1 / 2 < thetaCuspSingleAtomReflectionFactor A z := by
    simpa only [A, z] using
      one_half_lt_thetaCuspSingleAtomReflectionFactor_of_sameHalfLine ht.le htu
  have hS : 0 < S := by
    unfold S thetaCuspSingleAtomReflectionSlope
    have hl := thetaCuspSingleAtomReflectionLambda_pos hA
    have hr : 0 < thetaCuspSingleAtomReflectionFactor A z := by linarith
    positivity
  have ha1 : a1 = S * zp := by rfl
  have ha1pos : 0 < a1 := by rw [ha1]; positivity
  have ha2pos : 0 < a2 := by
    simpa only [A, z, a2] using
      thetaCuspSingleAtomReflectedActionJetTwo_pos_of_sameHalfLine ht htu
  have hq1 : -q1 ≤ 13 / 20 * zp := by
    simpa only [q1, zp] using
      neg_thetaCuspReflectedLikelihoodCumulantJetOne_le_velocity ht.le htu
  have hq2 : -q2 ≤ 13 / 5 := by
    simpa only [q2] using
      neg_thetaCuspReflectedLikelihoodCumulantJetTwo_le_thirteen_fifths ht.le htu
  have hcrossBound :
      -thetaCuspReflectedAtomLikelihoodRiccatiCross u t ≤
        zp * (26 / 5 * S + 13 / 10 * a2) := by
    have hfirst : a1 * (-q2) ≤ a1 * (13 / 5) :=
      mul_le_mul_of_nonneg_left hq2 ha1pos.le
    have hsecond : (-q1) * a2 ≤ (13 / 20 * zp) * a2 :=
      mul_le_mul_of_nonneg_right hq1 ha2pos.le
    unfold thetaCuspReflectedAtomLikelihoodRiccatiCross
    dsimp [a1, a2, q1, q2, S, A, z, zp] at hfirst hsecond ⊢
    nlinarith
  have hatomBudget :
      26 / 5 * S + 13 / 10 * a2 < 4 * R := by
    simpa only [S, a2, R] using
      thetaCuspSingleAtomRiccatiReducedMargin_crossBudget hA hz hrHalf
  have hstrict :
      zp * (26 / 5 * S + 13 / 10 * a2) < zp * (4 * R) :=
    mul_lt_mul_of_pos_left hatomBudget hzp
  have hrpos : 0 < thetaCuspSingleAtomReflectionFactor A z := by linarith
  have hmargin :
      thetaCuspSingleAtomReflectedRiccatiMargin A z zp = 4 * zp * R := by
    simpa only [R] using
      thetaCuspSingleAtomReflectedRiccatiMargin_eq hrpos.ne'
  rw [hmargin]
  nlinarith

/-- The completed theta-source reflected Riccati margin is strictly positive off the seam on every
same-half-line packet. -/
theorem thetaCuspCompletedReflectedCumulantRiccatiMargin_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u) :
    0 < thetaCuspCompletedReflectedCumulantRiccatiMargin u t := by
  rw [thetaCuspCompletedReflectedCumulantRiccatiMargin_eq_atom_add_likelihood_add_cross]
  have hatom :=
    neg_thetaCuspReflectedAtomLikelihoodRiccatiCross_lt_atomMargin ht htu
  have hlik :=
    thetaCuspReflectedLikelihoodCumulantRiccatiMargin_pos ht htu
  linarith

/-- The completed margin is nonnegative on the closed same-half-line displacement interval. -/
theorem thetaCuspCompletedReflectedCumulantRiccatiMargin_nonneg
    {u t : ℝ} (ht : 0 ≤ t) (htu : t ≤ u) :
    0 ≤ thetaCuspCompletedReflectedCumulantRiccatiMargin u t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · unfold thetaCuspCompletedReflectedCumulantRiccatiMargin
      thetaCuspSingleAtomReflectedActionJetOne
      thetaCuspSingleAtomReflectedActionJetTwo
      thetaCuspSingleAtomReflectedActionJetThree
      thetaCuspReflectedLikelihoodCumulantJetOne
      thetaCuspReflectedLikelihoodCumulantJetTwo
      thetaCuspReflectedLikelihoodCumulantJetThree
      thetaCuspSingleAtomReflectionDefect
    simp
  · exact (thetaCuspCompletedReflectedCumulantRiccatiMargin_pos ht htu).le

/-- **Unconditional completed-source same-half-line angle law.** -/
theorem thetaCuspFullSource_reflectedCorrelationAngle_subadditive
    {u x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyu : x + y ≤ u) :
    Real.arccos
        (thetaCuspFullSource (u + (x + y)) *
          thetaCuspFullSource (u - (x + y)) /
          thetaCuspFullSource u ^ 2) ≤
      Real.arccos
          (thetaCuspFullSource (u + x) * thetaCuspFullSource (u - x) /
            thetaCuspFullSource u ^ 2) +
        Real.arccos
          (thetaCuspFullSource (u + y) * thetaCuspFullSource (u - y) /
            thetaCuspFullSource u ^ 2) := by
  apply
    thetaCuspFullSource_reflectedCorrelationAngle_subadditive_of_margin_nonneg
      hx hy hxyu
  intro t ht
  exact thetaCuspCompletedReflectedCumulantRiccatiMargin_nonneg
    ht.1 (ht.2.trans hxyu)

end

end RHTower
