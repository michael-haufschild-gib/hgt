import GaloisForLFunctions.RHTower.DeBruijnPolynomialGaussianAverage
import GaloisForLFunctions.RHTower.HeatGaussianTiltedMoments
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville

/-!
# The Gaussian average of a locally tame entire function

Let `F` be entire and `z ∈ ℂ`, and let `g_t(u) = (4πt)^{−1/2} e^{−u²/4t}` be the heat kernel of
variance `2t`.  Suppose `F` is *tame at `z` with rate `a ≥ 1`*,

  `‖F(w)‖ ≤ ‖F(z)‖ e^{a‖w − z‖}`   for `‖w − z‖ ≤ 2`,

and has a *vertical tail* `‖F(z − iu)‖ ≤ B ‖F(z)‖ e^{b|u|}` for `|u| > 1`.  Then for every
`λ ≥ 0` (`norm_integral_gaussDensity_mul_sub_le`)

  `‖∫ g_t(u) F(z − iu) du − F(z)‖ ≤ 7t ‖F(z)‖ (6a² e^{4a²t} + (B + 1 + 4a) e^{−λ + 4(b+λ)²t})`.

So the average stays within a small multiple of `‖F(z)‖` once `t ≪ a^{−2}` and the tail is paid
by the Gaussian.

**Proof.**  Since `∫ g_t = 1` and `∫ g_t u = 0`, the difference is the average of the second-order
Taylor remainder `G(w) = F(w) − F(z) − (w − z) F′(z)` along `w = z − iu`.
* Cauchy's estimates on the circle of radius `2/a` give
  `‖G(w)‖ ≤ (e²/2) a² ‖w − z‖² ‖F(z)‖` for `‖w − z‖ ≤ 1/a` (`norm_taylorRemainder_le`).
  Directly, `‖G(z − iu)‖ ≤ 6 a² u² e^{a|u|} ‖F(z)‖` for `|u| ≤ 1`.
* For `|u| > 1` the tail gives `‖G(z − iu)‖ ≤ (B + 1 + 4a) u² e^{b|u|} ‖F(z)‖`.
* The Gaussian moment `∫ g_t u² e^{c|u|} ≤ 7t e^{4c²t}`
  (`integral_gaussDensity_mul_sq_mul_exp_abs_le`) follows from
  `u² e^{c|u|} ≤ u⁴/(2t) + (t/2)(e^{2cu} + e^{−2cu})`, the fourth moment `12t²`, and
  `∫ g_t e^{xu} = e^{tx²}`.
-/

open Complex MeasureTheory Metric Filter Set
open scoped Nat

namespace RHTower.DeBruijn

noncomputable section

/-! ## The Gaussian moment -/

theorem sq_mul_exp_abs_le {t : ℝ} (ht : 0 < t) (c u : ℝ) :
    u ^ 2 * Real.exp (c * |u|) ≤
      u ^ 4 / (2 * t) + t / 2 * (Real.exp (u * (2 * c)) + Real.exp (u * (-(2 * c)))) := by
  have hamgm : u ^ 2 * Real.exp (c * |u|) ≤ u ^ 4 / (2 * t) + t / 2 * Real.exp (c * |u|) ^ 2 := by
    have h := sq_nonneg (u ^ 2 / t - Real.exp (c * |u|))
    have : u ^ 4 / (2 * t) + t / 2 * Real.exp (c * |u|) ^ 2 - u ^ 2 * Real.exp (c * |u|)
        = t / 2 * (u ^ 2 / t - Real.exp (c * |u|)) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ t / 2) h]
  have hsq : Real.exp (c * |u|) ^ 2 ≤ Real.exp (u * (2 * c)) + Real.exp (u * (-(2 * c))) := by
    rw [← Real.exp_nat_mul]
    push_cast
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
      have : (2 : ℝ) * (c * u) = u * (2 * c) := by ring
      rw [this]
      linarith [Real.exp_pos (u * (-(2 * c)))]
    · rw [abs_of_nonpos hu]
      have : (2 : ℝ) * (c * -u) = u * (-(2 * c)) := by ring
      rw [this]
      linarith [Real.exp_pos (u * (2 * c))]
  nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ t / 2)]

theorem integrable_gaussDensity_mul_rexp' {t : ℝ} (ht : 0 < t) (c : ℝ) :
    Integrable (fun u : ℝ => gaussDensity t u * Real.exp (u * c)) := by
  simpa using integrable_gaussDensity_sub_mul_rexp ht 0 c

theorem integrable_gaussDensity_mul_sq_mul_exp_abs {t : ℝ} (ht : 0 < t) (c : ℝ) :
    Integrable (fun u : ℝ => gaussDensity t u * (u ^ 2 * Real.exp (c * |u|))) := by
  have hmaj : Integrable (fun u : ℝ => gaussDensity t u * u ^ 4 / (2 * t)
      + t / 2 * (gaussDensity t u * Real.exp (u * (2 * c))
        + gaussDensity t u * Real.exp (u * (-(2 * c))))) :=
    ((integrable_gaussDensity_mul_pow ht 4).div_const _).add
      (((integrable_gaussDensity_mul_rexp' ht _).add
        (integrable_gaussDensity_mul_rexp' ht _)).const_mul _)
  refine hmaj.mono' ?_ (Eventually.of_forall fun u => ?_)
  · exact ((continuous_gaussDensity_aux ht).mul (by fun_prop)).aestronglyMeasurable
  · have hg := (gaussDensity_pos ht u).le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc gaussDensity t u * (u ^ 2 * Real.exp (c * |u|))
        ≤ gaussDensity t u * (u ^ 4 / (2 * t)
            + t / 2 * (Real.exp (u * (2 * c)) + Real.exp (u * (-(2 * c))))) :=
          mul_le_mul_of_nonneg_left (sq_mul_exp_abs_le ht c u) hg
      _ = _ := by ring

/-- `∫ g_t(u) u² e^{c|u|} du ≤ 7t e^{4c²t}`. -/
theorem integral_gaussDensity_mul_sq_mul_exp_abs_le {t : ℝ} (ht : 0 < t) (c : ℝ) :
    ∫ u : ℝ, gaussDensity t u * (u ^ 2 * Real.exp (c * |u|)) ≤ 7 * t * Real.exp (4 * c ^ 2 * t) := by
  have h4 : ∫ u : ℝ, gaussDensity t u * u ^ 4 = 12 * t ^ 2 := by
    have := integral_gaussDensity_mul_pow_even ht 2
    norm_num [Nat.factorial] at this
    linarith
  have hp := integral_gaussDensity_mul_rexp ht (2 * c)
  have hm := integral_gaussDensity_mul_rexp ht (-(2 * c))
  have hi4 := (integrable_gaussDensity_mul_pow ht 4).div_const (2 * t)
  have hip := integrable_gaussDensity_mul_rexp' ht (2 * c)
  have him := integrable_gaussDensity_mul_rexp' ht (-(2 * c))
  calc ∫ u : ℝ, gaussDensity t u * (u ^ 2 * Real.exp (c * |u|))
      ≤ ∫ u : ℝ, (gaussDensity t u * u ^ 4 / (2 * t)
          + t / 2 * (gaussDensity t u * Real.exp (u * (2 * c))
            + gaussDensity t u * Real.exp (u * (-(2 * c))))) := by
        refine integral_mono (integrable_gaussDensity_mul_sq_mul_exp_abs ht c)
          (hi4.add ((hip.add him).const_mul _)) fun u => ?_
        have hg := (gaussDensity_pos ht u).le
        calc gaussDensity t u * (u ^ 2 * Real.exp (c * |u|))
            ≤ gaussDensity t u * (u ^ 4 / (2 * t)
                + t / 2 * (Real.exp (u * (2 * c)) + Real.exp (u * (-(2 * c))))) :=
              mul_le_mul_of_nonneg_left (sq_mul_exp_abs_le ht c u) hg
          _ = _ := by ring
    _ = 12 * t ^ 2 / (2 * t) + t / 2 * (Real.exp (t * (2 * c) ^ 2)
          + Real.exp (t * (-(2 * c)) ^ 2)) := by
        rw [integral_add hi4 ((hip.add him).const_mul _), integral_div, h4,
          integral_const_mul, integral_add hip him, hp, hm]
    _ ≤ 7 * t * Real.exp (4 * c ^ 2 * t) := by
        have he : Real.exp (t * (2 * c) ^ 2) = Real.exp (4 * c ^ 2 * t) := by ring_nf
        have he' : Real.exp (t * (-(2 * c)) ^ 2) = Real.exp (4 * c ^ 2 * t) := by ring_nf
        rw [he, he']
        have h1 : 1 ≤ Real.exp (4 * c ^ 2 * t) := Real.one_le_exp (by positivity)
        have : 12 * t ^ 2 / (2 * t) = 6 * t := by field_simp; ring
        rw [this]
        nlinarith

end

end RHTower.DeBruijn
