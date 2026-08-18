import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPrimeEnvelope
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaAsymptotics

/-!
# The Route-T twisted envelope with its width made explicit

The Route-T twisted prime envelope is stated in terms of the zero-free width at the relevant height,
which is not itself an elementary expression.  For the short-interval argument the width is needed
only through two elementary consequences: it is at most the fixed regularity `delta`, and it is at
least an explicit reciprocal polylogarithm in the height.  Substituting both turns the envelope into
a closed expression in `x` and `τ`.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- The explicit polylogarithmic lower bound for the Route-T zero-free width at height `3|τ|/2 + 1`. -/
def routeTWidthPolylogLower (A τ : ℝ) : ℝ :=
  1 / (10 * routeTZeroFreeDeltaEnvelopeConstant A
      * (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) ^ ((9 : ℝ) / 10)
      * (1 + Real.log (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)))) ^ 2)

theorem routeTWidthPolylogLower_pos (A τ : ℝ) : 0 < routeTWidthPolylogLower A τ := by
  have hZ1 : 1 ≤ routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) := by
    refine routeTLogHeightEnvelope_one_le ?_
    have := abs_nonneg τ
    linarith
  have hZ0 : (0 : ℝ) < routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) := by linarith
  have hlogZ : (0 : ℝ) ≤ Real.log (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) :=
    Real.log_nonneg hZ1
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hpow : (0 : ℝ) < (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) ^ ((9 : ℝ) / 10) :=
    Real.rpow_pos_of_pos hZ0 _
  rw [routeTWidthPolylogLower]
  positivity

/-- **The explicit lower bound is a lower bound for the Route-T width.** -/
theorem routeTWidthPolylogLower_le {A τ : ℝ} (hτ : 16 * Real.pi / 3 ≤ |τ|) :
    routeTWidthPolylogLower A τ ≤ routeTZeroFreeWidth A (3 * |τ| / 2 + 1) := by
  have hγ : 8 * Real.pi + 1 ≤ 3 * |τ| / 2 + 1 := by linarith
  have hbase := routeTZeroFreeDelta_polylog_lower (A := A) (γ := 3 * |τ| / 2 + 1) hγ
  rw [routeTZeroFreeWidth, routeTWidthPolylogLower]
  have hZ1 : 1 ≤ routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) := by
    refine routeTLogHeightEnvelope_one_le ?_
    have := abs_nonneg τ
    linarith
  have hZ0 : (0 : ℝ) < routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)) := by linarith
  have hlogZ : (0 : ℝ) ≤ Real.log (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) :=
    Real.log_nonneg hZ1
  have hD := routeTZeroFreeDeltaEnvelopeConstant_pos A
  have hpow : (0 : ℝ) < (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) ^ ((9 : ℝ) / 10) :=
    Real.rpow_pos_of_pos hZ0 _
  have hden : (0 : ℝ) < routeTZeroFreeDeltaEnvelopeConstant A
      * (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1))) ^ ((9 : ℝ) / 10)
      * (1 + Real.log (routeTLogHeightEnvelope (4 * (3 * |τ| / 2 + 1)))) ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 10)]
  rw [div_le_iff₀ hden] at hbase
  nlinarith [hbase, hden, routeTZeroFreeDelta_pos A (3 * |τ| / 2 + 1)]

/-- The regularity width never exceeds half the fixed regularity. -/
theorem routeTUniformRegWidth_le_delta_half {A delta K : ℝ} :
    routeTUniformRegWidth A delta K ≤ delta / 2 := by
  rw [routeTUniformRegWidth]
  have := min_le_left delta (routeTZeroFreeWidth A (K + 1))
  linarith

/-- The regularity width is at least half the explicit polylogarithmic bound. -/
theorem routeTUniformRegWidth_ge {A delta τ : ℝ} (hτ : 16 * Real.pi / 3 ≤ |τ|) :
    min delta (routeTWidthPolylogLower A τ) / 2
      ≤ routeTUniformRegWidth A delta (3 * |τ| / 2) := by
  rw [routeTUniformRegWidth]
  have hmin : min delta (routeTWidthPolylogLower A τ)
      ≤ min delta (routeTZeroFreeWidth A (3 * |τ| / 2 + 1)) := by
    refine le_min (min_le_left _ _) ?_
    exact le_trans (min_le_right _ _) (routeTWidthPolylogLower_le hτ)
  linarith

/-- **The Route-T twisted envelope, with both exponents made explicit.** -/
theorem routeTTwistEnvelope_le_explicit {A delta C τ x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hτ : 16 * Real.pi / 3 ≤ |τ|) :
    routeTTwistEnvelope A delta C τ x
      ≤ C * ((3 * x) ^ (1 - min delta (routeTWidthPolylogLower A τ) / 6)
              * (routeTTwistHeightFactor A τ + Real.log (2 * x))
            + (3 * x) ^ (1 + delta / 3)
                * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|))
        + 2 * Real.sqrt x * Real.log x := by
  have h3x : (1 : ℝ) ≤ 3 * x := by linarith
  have hH := routeTTwistHeightFactor_nonneg A τ
  have hlog2x : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hτ0 : (0 : ℝ) < 1 + |τ| := by
    have := abs_nonneg τ
    linarith
  have hlow := routeTUniformRegWidth_ge (A := A) (delta := delta) hτ
  have hhigh := routeTUniformRegWidth_le_delta_half (A := A) (delta := delta) (K := 3 * |τ| / 2)
  have hexp1 : (1 : ℝ) - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3
      ≤ 1 - min delta (routeTWidthPolylogLower A τ) / 6 := by linarith
  have hexp2 : (1 : ℝ) + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3
      ≤ 1 + delta / 3 := by linarith
  have hp1 : (3 * x) ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
      ≤ (3 * x) ^ (1 - min delta (routeTWidthPolylogLower A τ) / 6) :=
    Real.rpow_le_rpow_of_exponent_le h3x hexp1
  have hp2 : (3 * x) ^ (1 + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
      ≤ (3 * x) ^ (1 + delta / 3) :=
    Real.rpow_le_rpow_of_exponent_le h3x hexp2
  rw [routeTTwistEnvelope]
  have hstep1 : (3 * x) ^ (1 - routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
        * (routeTTwistHeightFactor A τ + Real.log (2 * x))
      ≤ (3 * x) ^ (1 - min delta (routeTWidthPolylogLower A τ) / 6)
        * (routeTTwistHeightFactor A τ + Real.log (2 * x)) :=
    mul_le_mul_of_nonneg_right hp1 (by linarith)
  have hstep2 : (3 * x) ^ (1 + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
        * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|)
      ≤ (3 * x) ^ (1 + delta / 3)
        * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|) := by
    have hnum : (3 * x) ^ (1 + 2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
        * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ)
        ≤ (3 * x) ^ (1 + delta / 3) * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) :=
      mul_le_mul_of_nonneg_right hp2 (by nlinarith [sq_nonneg (Real.log x), hH])
    exact (div_le_div_iff_of_pos_right hτ0).mpr hnum
  nlinarith [hstep1, hstep2, hC]

/-! ## The height factor, and the exponents as exponentials -/

/-- **The height factor with the width made explicit.** -/
theorem routeTTwistHeightFactor_le_explicit {A τ : ℝ} (hτ : 16 * Real.pi / 3 ≤ |τ|) :
    routeTTwistHeightFactor A τ
      ≤ 1 / (1 + |τ|)
        + Real.log (3 * |τ| / 2 + 3) / routeTWidthPolylogLower A τ := by
  rw [routeTTwistHeightFactor]
  have hlow := routeTWidthPolylogLower_le (A := A) (τ := τ) hτ
  have hpos := routeTWidthPolylogLower_pos A τ
  have hW : 0 < routeTZeroFreeWidth A (3 * |τ| / 2 + 1) := routeTZeroFreeWidth_pos _ _
  have hnum : (0 : ℝ) ≤ Real.log (3 * |τ| / 2 + 3) := by
    refine Real.log_nonneg ?_
    have := abs_nonneg τ
    linarith
  have hdiv : Real.log (3 * |τ| / 2 + 3) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1)
      ≤ Real.log (3 * |τ| / 2 + 3) / routeTWidthPolylogLower A τ :=
    div_le_div_of_nonneg_left hnum hpos hlow
  linarith

/-- A one-sided exponent is the base times an exponential of its logarithm. -/
theorem rpow_one_sub_eq {y c : ℝ} (hy : 0 < y) :
    y ^ (1 - c) = y * Real.exp (-(c * Real.log y)) := by
  rw [Real.rpow_def_of_pos hy, show Real.log y * (1 - c) = Real.log y + -(c * Real.log y) by ring,
    Real.exp_add, Real.exp_log hy]

theorem rpow_one_add_eq {y c : ℝ} (hy : 0 < y) :
    y ^ (1 + c) = y * Real.exp (c * Real.log y) := by
  rw [Real.rpow_def_of_pos hy, show Real.log y * (1 + c) = Real.log y + c * Real.log y by ring,
    Real.exp_add, Real.exp_log hy]

/-- **The Route-T twisted envelope, entirely elementary.**  The saving is an explicit exponential in
the width times the logarithm of the cutoff. -/
theorem routeTTwistEnvelope_le_exp {A delta C τ x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hτ : 16 * Real.pi / 3 ≤ |τ|) :
    routeTTwistEnvelope A delta C τ x
      ≤ C * (3 * x * Real.exp (-(min delta (routeTWidthPolylogLower A τ) / 6
                * Real.log (3 * x)))
              * (routeTTwistHeightFactor A τ + Real.log (2 * x))
            + 3 * x * Real.exp (delta / 3 * Real.log (3 * x))
                * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|))
        + 2 * Real.sqrt x * Real.log x := by
  have h3x : (0 : ℝ) < 3 * x := by linarith
  have hbase := routeTTwistEnvelope_le_explicit (A := A) (delta := delta) (C := C) hC hx hτ
  rw [rpow_one_sub_eq h3x, rpow_one_add_eq h3x] at hbase
  exact hbase

end

end RHTower.Sieve
