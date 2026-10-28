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
  · have hcont : Continuous fun u : ℝ => gaussDensity t u := by
      unfold gaussDensity; fun_prop
    exact (hcont.mul (by fun_prop)).aestronglyMeasurable
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
  have hi4 : Integrable (fun u : ℝ => gaussDensity t u * u ^ 4 / (2 * t)) :=
    (integrable_gaussDensity_mul_pow ht 4).div_const (2 * t)
  have hip := integrable_gaussDensity_mul_rexp' ht (2 * c)
  have him := integrable_gaussDensity_mul_rexp' ht (-(2 * c))
  have hg : Integrable (fun u : ℝ => t / 2 * (gaussDensity t u * Real.exp (u * (2 * c))
      + gaussDensity t u * Real.exp (u * (-(2 * c))))) := (hip.add him).const_mul _
  calc ∫ u : ℝ, gaussDensity t u * (u ^ 2 * Real.exp (c * |u|))
      ≤ ∫ u : ℝ, (gaussDensity t u * u ^ 4 / (2 * t)
          + t / 2 * (gaussDensity t u * Real.exp (u * (2 * c))
            + gaussDensity t u * Real.exp (u * (-(2 * c))))) := by
        refine integral_mono (integrable_gaussDensity_mul_sq_mul_exp_abs ht c)
          (hi4.add hg) fun u => ?_
        have hg := (gaussDensity_pos ht u).le
        calc gaussDensity t u * (u ^ 2 * Real.exp (c * |u|))
            ≤ gaussDensity t u * (u ^ 4 / (2 * t)
                + t / 2 * (Real.exp (u * (2 * c)) + Real.exp (u * (-(2 * c))))) :=
              mul_le_mul_of_nonneg_left (sq_mul_exp_abs_le ht c u) hg
          _ = _ := by ring
    _ = 12 * t ^ 2 / (2 * t) + t / 2 * (Real.exp (t * (2 * c) ^ 2)
          + Real.exp (t * (-(2 * c)) ^ 2)) := by
        rw [integral_add hi4 hg, integral_div, h4, integral_const_mul, integral_add hip him,
          hp, hm]
    _ ≤ 7 * t * Real.exp (4 * c ^ 2 * t) := by
        have he : Real.exp (t * (2 * c) ^ 2) = Real.exp (4 * c ^ 2 * t) := by ring_nf
        have he' : Real.exp (t * (-(2 * c)) ^ 2) = Real.exp (4 * c ^ 2 * t) := by ring_nf
        rw [he, he']
        have h1 : 1 ≤ Real.exp (4 * c ^ 2 * t) := Real.one_le_exp (by positivity)
        have : 12 * t ^ 2 / (2 * t) = 6 * t := by field_simp; ring
        rw [this]
        nlinarith

/-! ## The second-order Taylor remainder -/

/-- Cauchy's estimate for the second-order Taylor remainder: if `‖F‖ ≤ M` on the circle of radius
`ρ` about `z`, then `‖F(w) − F(z) − (w − z) F′(z)‖ ≤ 2M (‖w − z‖/ρ)²` for `‖w − z‖ ≤ ρ/2`. -/
theorem norm_taylorRemainder_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z w : ℂ} {ρ M : ℝ}
    (hρ : 0 < ρ) (hM : ∀ v ∈ sphere z ρ, ‖F v‖ ≤ M) (hw : ‖w - z‖ ≤ ρ / 2) :
    ‖F w - F z - (w - z) * deriv F z‖ ≤ 2 * M * (‖w - z‖ / ρ) ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (z + ρ) (by simp [abs_of_pos hρ]))
  set q : ℝ := ‖w - z‖ / ρ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 2 := by rw [hq, div_le_iff₀ hρ]; linarith
  have hwball : w ∈ ball z ρ := by rw [mem_ball, dist_eq_norm]; linarith
  have hsum := Complex.hasSum_taylorSeries_on_ball hF.differentiableOn hwball
  have htail := (hasSum_nat_add_iff' 2).mpr hsum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, pow_one, one_smul, iteratedDeriv_zero,
    iteratedDeriv_one, smul_eq_mul] at htail
  have hgeo : HasSum (fun n : ℕ => M * q ^ 2 * q ^ n) (M * q ^ 2 * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left _
  have hbound : ∀ n : ℕ, ‖((n + 2)! : ℂ)⁻¹ • (w - z) ^ (n + 2) • iteratedDeriv (n + 2) F z‖
      ≤ M * q ^ 2 * q ^ n := by
    intro n
    have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n + 2) hρ
      hF.diffContOnCl hM
    rw [norm_smul, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
    have hfac : (0 : ℝ) < ((n + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    calc ((n + 2)! : ℝ)⁻¹ * (‖w - z‖ ^ (n + 2) * ‖iteratedDeriv (n + 2) F z‖)
        ≤ ((n + 2)! : ℝ)⁻¹ * (‖w - z‖ ^ (n + 2) * ((n + 2)! * M / ρ ^ (n + 2))) := by
          gcongr
      _ = M * (‖w - z‖ / ρ) ^ (n + 2) := by
          rw [div_pow]; field_simp
      _ = M * q ^ 2 * q ^ n := by rw [← hq]; ring
  have hle := htail.norm_le_of_bounded hgeo hbound
  have hle' : ‖F w - F z - (w - z) * deriv F z‖ ≤ M * q ^ 2 * (1 - q)⁻¹ := by
    convert hle using 2
    trace_state
    sorry
  refine hle'.trans ?_
  have h1q : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc M * q ^ 2 * (1 - q)⁻¹ ≤ M * q ^ 2 * 2 := by gcongr
    _ = 2 * M * q ^ 2 := by ring

/-! ## The Gaussian average -/

/-- **The Gaussian average of a locally tame function.**  If `‖F(w)‖ ≤ ‖F(z)‖ e^{a‖w − z‖}` on
`‖w − z‖ ≤ 2` and `‖F(z − iu)‖ ≤ B ‖F(z)‖ e^{b|u|}` for `|u| > 1`, then for every `λ ≥ 0`
`‖∫ g_t(u) F(z − iu) du − F(z)‖ ≤ 7t ‖F(z)‖ (6a² e^{4a²t} + (B + 1 + 4a) e^{−λ + 4(b+λ)²t})`. -/
theorem norm_integral_gaussDensity_mul_sub_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) {z : ℂ}
    {t a b B lam : ℝ} (ht : 0 < t) (ha : 1 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (hlam : 0 ≤ lam)
    (hloc : ∀ w ∈ closedBall z 2, ‖F w‖ ≤ ‖F z‖ * Real.exp (a * ‖w - z‖))
    (htail : ∀ u : ℝ, 1 < |u| → ‖F (z - I * u)‖ ≤ B * ‖F z‖ * Real.exp (b * |u|))
    (hint : Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * F (z - I * u))) :
    ‖(∫ u : ℝ, (gaussDensity t u : ℂ) * F (z - I * u)) - F z‖ ≤
      7 * t * ‖F z‖ * (6 * a ^ 2 * Real.exp (4 * a ^ 2 * t)
        + (B + 1 + 4 * a) * Real.exp (-lam + 4 * (b + lam) ^ 2 * t)) := by
  set N : ℝ := ‖F z‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have ha0 : 0 < a := by linarith
  set ρ : ℝ := 2 / a with hρdef
  have hρ : 0 < ρ := by positivity
  have hρ2 : ρ ≤ 2 := by rw [hρdef, div_le_iff₀ ha0]; linarith
  -- the bound on the circle of radius `2/a`
  have hsph : ∀ v ∈ sphere z ρ, ‖F v‖ ≤ N * Real.exp 2 := by
    intro v hv
    have hvz : ‖v - z‖ = ρ := by simpa [dist_eq_norm] using hv
    have := hloc v (by rw [mem_closedBall, dist_eq_norm, hvz]; exact hρ2)
    rw [hvz, hρdef, mul_div_cancel₀ _ ha0.ne'] at this
    exact this
  have he2 : Real.exp 2 ≤ 8 := by
    have := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    nlinarith [Real.exp_pos 1]
  -- the derivative at the centre
  have hder : ‖deriv F z‖ ≤ 4 * a * N := by
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hF.diffContOnCl hsph
    refine h.trans ?_
    rw [hρdef, div_div_eq_mul_div]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul_of_nonneg_left he2 (mul_nonneg hN0 ha0.le)]
  -- the pointwise bound on the Taylor remainder along the vertical line
  set G : ℝ → ℂ := fun u => F (z - I * u) - F z - (-(I * u)) * deriv F z with hG
  set phi : ℝ → ℝ := fun u => 6 * a ^ 2 * (u ^ 2 * Real.exp (a * |u|))
      + (B + 1 + 4 * a) * Real.exp (-lam) * (u ^ 2 * Real.exp ((b + lam) * |u|)) with hphi
  have hphi1 : ∀ u, 0 ≤ (B + 1 + 4 * a) * Real.exp (-lam) * (u ^ 2 * Real.exp ((b + lam) * |u|)) :=
    fun u => by positivity
  have hphi0 : ∀ u, 0 ≤ 6 * a ^ 2 * (u ^ 2 * Real.exp (a * |u|)) := fun u => by positivity
  have hnormIu : ∀ u : ℝ, ‖I * (u : ℂ)‖ = |u| := fun u => by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hGbound : ∀ u : ℝ, ‖G u‖ ≤ N * phi u := by
    intro u
    have hwz : (z - I * u) - z = -(I * u) := by ring
    by_cases h1 : |u| ≤ 1
    · by_cases ha1 : |u| ≤ 1 / a
      · have hw : ‖(z - I * u) - z‖ ≤ ρ / 2 := by
          rw [hwz, norm_neg, hnormIu, hρdef]
          calc |u| ≤ 1 / a := ha1
            _ = 2 / a / 2 := by ring
        have h := norm_taylorRemainder_le hF hρ hsph hw
        rw [hwz] at h
        have hG' : G u = F (z - I * u) - F z - -(I * ↑u) * deriv F z := rfl
        rw [hG']
        refine h.trans ?_
        rw [norm_neg, hnormIu, hρdef]
        have hexp : 1 ≤ Real.exp (a * |u|) := Real.one_le_exp (by positivity)
        have hkey : 2 * (N * Real.exp 2) * (|u| / (2 / a)) ^ 2 ≤ 6 * a ^ 2 * (u ^ 2 * Real.exp (a * |u|)) * N := by
          have hsq : (|u| / (2 / a)) ^ 2 = a ^ 2 * u ^ 2 / 4 := by
            rw [div_div_eq_mul_div, div_pow, mul_pow, sq_abs]; ring
          rw [hsq]
          have hu2 : 0 ≤ a ^ 2 * u ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hexp (mul_nonneg hu2 hN0),
            mul_le_mul_of_nonneg_left he2 (mul_nonneg hu2 hN0)]
        rw [hphi]
        nlinarith [hphi1 u, hkey]
      · push Not at ha1
        have hau : 1 ≤ a * |u| := by rwa [div_lt_iff₀ ha0, mul_comm] at ha1 |>.le
        have hfar : ‖F (z - I * u)‖ ≤ N * Real.exp (a * |u|) := by
          have := hloc (z - I * u) (by
            rw [mem_closedBall, dist_eq_norm, hwz, norm_neg, hnormIu]; linarith)
          rwa [hwz, norm_neg, hnormIu] at this
        have hG' : ‖G u‖ ≤ ‖F (z - I * u)‖ + N + |u| * ‖deriv F z‖ := by
          have h := norm_sub_le (F (z - I * u) - F z) (-(I * u) * deriv F z)
          have h2 := norm_sub_le (F (z - I * u)) (F z)
          rw [norm_mul, norm_neg, hnormIu] at h
          simp only [hG]
          linarith
        have hexp : 1 ≤ Real.exp (a * |u|) := Real.one_le_exp (by positivity)
        have hsq : 1 ≤ a ^ 2 * u ^ 2 := by
          have : a ^ 2 * u ^ 2 = (a * |u|) ^ 2 := by rw [mul_pow, sq_abs]
          rw [this]; nlinarith
        have hlin : a * |u| ≤ a ^ 2 * u ^ 2 := by
          have : a ^ 2 * u ^ 2 = (a * |u|) ^ 2 := by rw [mul_pow, sq_abs]
          rw [this]; nlinarith
        have hkey : ‖F (z - I * u)‖ + N + |u| * ‖deriv F z‖
            ≤ N * (6 * a ^ 2 * (u ^ 2 * Real.exp (a * |u|))) := by
          have h3 : |u| * ‖deriv F z‖ ≤ 4 * N * (a * |u|) := by
            nlinarith [mul_le_mul_of_nonneg_left hder (abs_nonneg u)]
          have hE : 0 ≤ a ^ 2 * u ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hexp (mul_nonneg hE hN0),
            mul_le_mul_of_nonneg_left hsq hN0, mul_le_mul_of_nonneg_left hlin hN0,
            mul_le_mul_of_nonneg_left hsq (mul_nonneg hN0 (Real.exp_pos (a * |u|)).le)]
        rw [hphi]
        nlinarith [hphi1 u, mul_le_mul_of_nonneg_left (le_of_eq rfl : (0:ℝ) ≤ 0) hN0, hG', hkey,
          mul_nonneg hN0 (hphi1 u)]
    · push Not at h1
      have hG' : ‖G u‖ ≤ ‖F (z - I * u)‖ + N + |u| * ‖deriv F z‖ := by
        have h := norm_sub_le (F (z - I * u) - F z) (-(I * u) * deriv F z)
        have h2 := norm_sub_le (F (z - I * u)) (F z)
        rw [norm_mul, norm_neg, hnormIu] at h
        simp only [hG]
        linarith
      have hu1 : 1 ≤ u ^ 2 := by
        have : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
        rw [this]; nlinarith
      have hulin : |u| ≤ u ^ 2 := by
        have : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
        rw [this]; nlinarith
      have hexpb : 1 ≤ Real.exp (b * |u|) := Real.one_le_exp (by positivity)
      have hshift : Real.exp (b * |u|) ≤ Real.exp (-lam) * Real.exp ((b + lam) * |u|) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith)
      have hkey : ‖F (z - I * u)‖ + N + |u| * ‖deriv F z‖
          ≤ N * ((B + 1 + 4 * a) * u ^ 2 * Real.exp (b * |u|)) := by
        have htl := htail u h1
        have h3 : |u| * ‖deriv F z‖ ≤ 4 * a * N * u ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hder (abs_nonneg u),
            mul_le_mul_of_nonneg_left hulin (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * a) hN0)]
        have hBpart : B * N * Real.exp (b * |u|) ≤ N * (B * u ^ 2 * Real.exp (b * |u|)) := by
          nlinarith [mul_le_mul_of_nonneg_left hu1
            (mul_nonneg (mul_nonneg hB hN0) (Real.exp_pos (b * |u|)).le)]
        have hNpart : N ≤ N * (u ^ 2 * Real.exp (b * |u|)) := by
          have : 1 ≤ u ^ 2 * Real.exp (b * |u|) := by nlinarith
          nlinarith
        have hapart : 4 * a * N * u ^ 2 ≤ N * (4 * a * u ^ 2 * Real.exp (b * |u|)) := by
          nlinarith [mul_le_mul_of_nonneg_left hexpb
            (mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 4 * a) hN0) (sq_nonneg u))]
        nlinarith
      have hfinal : N * ((B + 1 + 4 * a) * u ^ 2 * Real.exp (b * |u|))
          ≤ N * ((B + 1 + 4 * a) * Real.exp (-lam) * (u ^ 2 * Real.exp ((b + lam) * |u|))) := by
        have hc : 0 ≤ N * ((B + 1 + 4 * a) * u ^ 2) := by
          have : 0 ≤ B + 1 + 4 * a := by linarith
          positivity
        nlinarith [mul_le_mul_of_nonneg_left hshift hc]
      rw [hphi]
      nlinarith [hphi0 u, mul_nonneg hN0 (hphi0 u)]
  -- the integral identity
  have hg1 : ∫ u : ℝ, (gaussDensity t u : ℂ) = 1 := by
    have h := integral_gaussDensity_mul_pow_even ht 0
    simp only [mul_zero, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one] at h
    rw [integral_complex_ofReal, h]; simp
  have hgu : ∫ u : ℝ, (gaussDensity t u : ℂ) * (u : ℂ) = 0 := by
    have h := integral_gaussDensity_mul_pow_odd t 0
    simp only [mul_zero, zero_add, pow_one] at h
    have : (fun u : ℝ => (gaussDensity t u : ℂ) * (u : ℂ)) =
        fun u : ℝ => ((gaussDensity t u * u : ℝ) : ℂ) := by funext u; push_cast; ring
    rw [this, integral_complex_ofReal, h]; simp
  have hintg : Integrable (fun u : ℝ => (gaussDensity t u : ℂ)) := by
    have h := integrable_gaussDensity_mul_pow ht 0
    simp only [pow_zero, mul_one] at h
    exact h.ofReal
  have hintgu : Integrable (fun u : ℝ => (gaussDensity t u : ℂ) * (u : ℂ)) := by
    have h := integrable_gaussDensity_mul_pow ht 1
    simp only [pow_one] at h
    exact h.ofReal.congr (Eventually.of_forall fun u => by push_cast; ring)
  have hident : (∫ u : ℝ, (gaussDensity t u : ℂ) * F (z - I * u)) - F z
      = ∫ u : ℝ, (gaussDensity t u : ℂ) * G u := by
    have hsplit : ∀ u : ℝ, (gaussDensity t u : ℂ) * G u
        = (gaussDensity t u : ℂ) * F (z - I * u) - F z * (gaussDensity t u : ℂ)
          + (I * deriv F z) * ((gaussDensity t u : ℂ) * (u : ℂ)) := by
      intro u; simp only [hG]; ring
    simp_rw [hsplit]
    rw [integral_add (hint.sub (hintg.const_mul _)) (hintgu.const_mul _),
      integral_sub hint (hintg.const_mul _), integral_const_mul, integral_const_mul, hg1, hgu]
    ring
  -- the estimate
  have hintphi : Integrable (fun u : ℝ => gaussDensity t u * phi u) := by
    have h1 := (integrable_gaussDensity_mul_sq_mul_exp_abs ht a).const_mul (6 * a ^ 2)
    have h2 := (integrable_gaussDensity_mul_sq_mul_exp_abs ht (b + lam)).const_mul
      ((B + 1 + 4 * a) * Real.exp (-lam))
    exact (h1.add h2).congr (Eventually.of_forall fun u => by simp only [hphi]; ring)
  have hphiint : ∫ u : ℝ, gaussDensity t u * phi u ≤
      6 * a ^ 2 * (7 * t * Real.exp (4 * a ^ 2 * t))
        + (B + 1 + 4 * a) * Real.exp (-lam) * (7 * t * Real.exp (4 * (b + lam) ^ 2 * t)) := by
    have h1 := (integrable_gaussDensity_mul_sq_mul_exp_abs ht a).const_mul (6 * a ^ 2)
    have h2 := (integrable_gaussDensity_mul_sq_mul_exp_abs ht (b + lam)).const_mul
      ((B + 1 + 4 * a) * Real.exp (-lam))
    have heq : (fun u : ℝ => gaussDensity t u * phi u) = fun u =>
        6 * a ^ 2 * (gaussDensity t u * (u ^ 2 * Real.exp (a * |u|)))
          + (B + 1 + 4 * a) * Real.exp (-lam)
            * (gaussDensity t u * (u ^ 2 * Real.exp ((b + lam) * |u|))) := by
      funext u; simp only [hphi]; ring
    rw [heq, integral_add h1 h2, integral_const_mul, integral_const_mul]
    have hc : 0 ≤ (B + 1 + 4 * a) * Real.exp (-lam) := by
      have : 0 ≤ B + 1 + 4 * a := by linarith
      positivity
    gcongr
    · exact integral_gaussDensity_mul_sq_mul_exp_abs_le ht a
    · exact integral_gaussDensity_mul_sq_mul_exp_abs_le ht (b + lam)
  rw [hident]
  calc ‖∫ u : ℝ, (gaussDensity t u : ℂ) * G u‖ ≤ ∫ u : ℝ, gaussDensity t u * (N * phi u) := by
        refine norm_integral_le_of_norm_le (hintphi.const_mul N |>.congr
          (Eventually.of_forall fun u => by ring)) (Eventually.of_forall fun u => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussDensity_pos ht u)]
        exact mul_le_mul_of_nonneg_left (hGbound u) (gaussDensity_pos ht u).le
    _ = N * ∫ u : ℝ, gaussDensity t u * phi u := by
        rw [← integral_const_mul]; congr 1; funext u; ring
    _ ≤ N * (6 * a ^ 2 * (7 * t * Real.exp (4 * a ^ 2 * t))
        + (B + 1 + 4 * a) * Real.exp (-lam) * (7 * t * Real.exp (4 * (b + lam) ^ 2 * t))) :=
        mul_le_mul_of_nonneg_left hphiint hN0
    _ = 7 * t * N * (6 * a ^ 2 * Real.exp (4 * a ^ 2 * t)
        + (B + 1 + 4 * a) * Real.exp (-lam + 4 * (b + lam) ^ 2 * t)) := by
        rw [Real.exp_add]; ring

end

end RHTower.DeBruijn
