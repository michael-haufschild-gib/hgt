import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistScaledEnvelope
import GaloisForLFunctions.RHTower.Sieve.RouteTWidthExplicit

/-!
# The scaled envelope, estimated

The relative size of the scaled Route-T envelope has three parts: a height term decaying like
`1/|τ|`, a contour term decaying like `exp(−w log x)` with `w` the Route-T width, and the
desmoothing term `log(2x)/D`.  Both the width and the height cost are replaced here by their
explicit polylogarithmic surrogates, leaving an expression in elementary functions alone.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- The explicit surrogate for the height cost of the Route-T width. -/
def scaledHeightMajorant (A τ : ℝ) : ℝ :=
  1 / |τ| + Real.log (3 * |τ| / 2) / routeTWidthPolylogLower A τ

theorem scaledHeightFactor_le_majorant {A τ : ℝ} (hτ : 16 * Real.pi / 3 ≤ |τ|) :
    scaledHeightFactor A τ ≤ scaledHeightMajorant A τ := by
  have hτ1 : (1 : ℝ) ≤ |τ| := by
    have := Real.pi_gt_three
    linarith
  have hlow := routeTWidthPolylogLower_le (A := A) (τ := τ) hτ
  have hplw := routeTWidthPolylogLower_pos A τ
  have hW : 0 < routeTZeroFreeWidth A (3 * |τ| / 2 + 1) := routeTZeroFreeWidth_pos _ _
  have hlog : (0 : ℝ) ≤ Real.log (3 * |τ| / 2) := Real.log_nonneg (by linarith)
  have hdiv : Real.log (3 * |τ| / 2) / routeTZeroFreeWidth A (3 * |τ| / 2 + 1)
      ≤ Real.log (3 * |τ| / 2) / routeTWidthPolylogLower A τ :=
    div_le_div_of_nonneg_left hlog hplw hlow
  rw [scaledHeightFactor, scaledHeightMajorant]
  linarith

theorem scaledHeightMajorant_nonneg {A τ : ℝ} (hτ : 1 ≤ |τ|) : 0 ≤ scaledHeightMajorant A τ := by
  have hplw := routeTWidthPolylogLower_pos A τ
  have hlog : (0 : ℝ) ≤ Real.log (3 * |τ| / 2) := Real.log_nonneg (by linarith)
  have h1 : (0 : ℝ) ≤ 1 / |τ| := by positivity
  rw [scaledHeightMajorant]
  have := div_nonneg hlog hplw.le
  linarith

/-- **The relative scaled envelope, in elementary terms.** -/
theorem relScaledEnvelope_le {A delta Ctot D τ x : ℝ}
    (hCtot : 0 ≤ Ctot) (hD : 0 < D) (hτ : 16 * Real.pi / 3 ≤ |τ|) (hx : 1 ≤ x)
    {Lx q μ : ℝ} (hLx : Real.log x ≤ Lx) (hq0 : 0 ≤ q) (hq : q ≤ Real.log x)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ min delta (routeTWidthPolylogLower A τ) / 2) :
    relScaledEnvelope A delta Ctot D τ x
      ≤ Ctot * D ^ 2
          * (Lx ^ 2 / |τ|
            + scaledHeightMajorant A τ * (Real.exp (-(μ * q)) + 1 / |τ| ^ 2))
          / (2 * Real.pi)
        + Real.log (2 * x) / D + 2 * Real.log x / Real.sqrt x := by
  have hτ1 : (1 : ℝ) ≤ |τ| := by
    have := Real.pi_gt_three
    linarith
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have hlogx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hwge := routeTUniformRegWidth_ge (A := A) (delta := delta) (τ := τ) hτ
  have hμw : μ ≤ routeTUniformRegWidth A delta (3 * |τ| / 2) := le_trans hμ hwge
  have hw0 : (0 : ℝ) ≤ routeTUniformRegWidth A delta (3 * |τ| / 2) := le_trans hμ0 hμw
  -- the contour factor
  have h3 : (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h30 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) :=
    Real.rpow_nonneg (by norm_num) _
  have hxw : x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) ≤ Real.exp (-(μ * q)) :=
    rpow_neg_le_exp_neg hx hμ0 hμw hq0 hq
  have hxw0 : (0 : ℝ) ≤ x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) :=
    Real.rpow_nonneg hx0.le _
  have hcont : (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
      * x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) ≤ Real.exp (-(μ * q)) := by
    calc (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
        * x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
        ≤ 1 * x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) :=
          mul_le_mul_of_nonneg_right h3 hxw0
      _ = x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) := one_mul _
      _ ≤ Real.exp (-(μ * q)) := hxw
  -- the height factor
  have hHmaj := scaledHeightFactor_le_majorant (A := A) (τ := τ) hτ
  have hH0 := scaledHeightFactor_nonneg (A := A) (τ := τ) hτ1
  have hHm0 := scaledHeightMajorant_nonneg (A := A) (τ := τ) hτ1
  have hinner : (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
        * x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) + 1 / |τ| ^ 2
      ≤ Real.exp (-(μ * q)) + 1 / |τ| ^ 2 := by linarith
  have hinner0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
        * x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) + 1 / |τ| ^ 2 := by positivity
  have hprod : scaledHeightFactor A τ
        * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
          * x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) + 1 / |τ| ^ 2)
      ≤ scaledHeightMajorant A τ * (Real.exp (-(μ * q)) + 1 / |τ| ^ 2) :=
    mul_le_mul hHmaj hinner hinner0 hHm0
  -- the logarithm
  have hlogsq : (Real.log x) ^ 2 / |τ| ≤ Lx ^ 2 / |τ| := by
    have hsq : (Real.log x) ^ 2 ≤ Lx ^ 2 := pow_le_pow_left₀ hlogx hLx 2
    exact div_le_div_of_nonneg_right hsq hτ0.le
  have hbrack : (Real.log x) ^ 2 / |τ|
        + scaledHeightFactor A τ
          * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
            * x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) + 1 / |τ| ^ 2)
      ≤ Lx ^ 2 / |τ| + scaledHeightMajorant A τ * (Real.exp (-(μ * q)) + 1 / |τ| ^ 2) := by
    linarith
  rw [relScaledEnvelope]
  have hmain : Ctot * D ^ 2
        * ((Real.log x) ^ 2 / |τ|
          + scaledHeightFactor A τ
            * ((3 : ℝ) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
              * x ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2))) + 1 / |τ| ^ 2))
        / (2 * Real.pi)
      ≤ Ctot * D ^ 2
        * (Lx ^ 2 / |τ| + scaledHeightMajorant A τ * (Real.exp (-(μ * q)) + 1 / |τ| ^ 2))
        / (2 * Real.pi) := by
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left hbrack (by positivity)
  linarith

end

end RHTower.Sieve
