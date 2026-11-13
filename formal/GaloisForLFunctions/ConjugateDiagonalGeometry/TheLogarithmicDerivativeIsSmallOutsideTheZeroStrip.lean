import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis
import GaloisForLFunctions.RHTower.CCM.CCMGeneralizedVonKoch
import GaloisForLFunctions.RHTower.ZetaLogDerivLineBound
import GaloisForLFunctions.HTGeometry.ThreeCircles
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The logarithmic derivative outside the zero strip

The zero-free half-plane to the right of seven eighths gives a logarithmic bound
for `ζ'/ζ`. Three circles interpolate this bound with the bounded Dirichlet series
on a smaller disk lying to the right of one. Every fixed line between seven
eighths and one therefore has `ζ'/ζ = o(log |t|)`.
-/

noncomputable section

open Complex Metric Filter Topology

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open _root_.RHTower
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

private theorem xi_halfPlane_three_eighths : XiZeroHalfPlaneBound (3 / 8) := by
  intro z hz
  have hζ := (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hz).1
  have hle : z.re ≤ 7 / 8 := le_of_not_gt fun h =>
    riemannZeta_ne_zero_of_seven_eighths_lt_re h hζ
  linarith only [hle]

private theorem norm_logDeriv_zeta_right_le {z : ℂ}
    (hlo : (17 : ℝ) / 16 ≤ z.re) (hhi : z.re ≤ 2) :
    ‖logDeriv riemannZeta z‖ ≤ 2048 := by
  have hz : 1 < z.re := by linarith only [hlo]
  have h := norm_zeta_logDeriv_le_line hz hhi
  have hd : (1 : ℝ) / 16 ≤ z.re - 1 := by linarith only [hlo]
  have hs : (1 : ℝ) / 256 ≤ (z.re - 1) ^ 2 := by
    nlinarith only [sq_nonneg (z.re - 1 - 1 / 16), hd]
  have hden : 0 < (z.re - 1) ^ 2 := by linarith only [hs]
  rw [logDeriv_apply]
  exact h.trans ((div_le_iff₀ hden).mpr (by nlinarith only [hs]))

/-- A fixed disk strictly inside the zero-free half-plane has logarithmic growth. -/
private theorem exists_logDeriv_disk_log_bound {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1 / 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 8 ≤ |t| →
      ∀ z : ℂ, ‖z - ((9 / 8 : ℂ) + (t : ℂ) * I)‖ ≤ r →
        ‖logDeriv riemannZeta z‖ ≤ K * Real.log |t| := by
  obtain ⟨C, hC, hb⟩ :=
    Sieve.exists_logDeriv_zeta_bound_of_xiZeroHalfPlaneBound
      (by norm_num : (0 : ℝ) ≤ 3 / 8) xi_halfPlane_three_eighths
  have hδ : 0 < (1 : ℝ) / 4 - r := by linarith only [hr]
  refine ⟨2 * C / (1 / 4 - r) + 2048, by positivity, ?_⟩
  intro t ht z hz
  have hcre : ((9 / 8 : ℂ) + (t : ℂ) * I).re = 9 / 8 := by norm_num
  have hcim : ((9 / 8 : ℂ) + (t : ℂ) * I).im = t := by norm_num
  have hre := Complex.abs_re_le_norm (z - ((9 / 8 : ℂ) + (t : ℂ) * I))
  have him := Complex.abs_im_le_norm (z - ((9 / 8 : ℂ) + (t : ℂ) * I))
  rw [Complex.sub_re, hcre] at hre
  rw [Complex.sub_im, hcim] at him
  have hrelo : 9 / 8 - r ≤ z.re := by linarith only [(abs_le.mp (hre.trans hz)).1]
  have hrehi : z.re ≤ 9 / 8 + r := by linarith only [(abs_le.mp (hre.trans hz)).2]
  have himdiff : |z.im - t| ≤ r := him.trans hz
  have htlo : |t| - r ≤ |z.im| := by
    have h : |t| ≤ |z.im - t| + |z.im| := by
      calc |t| = |(t - z.im) + z.im| := by ring_nf
        _ ≤ |t - z.im| + |z.im| := abs_add_le _ _
        _ = |z.im - t| + |z.im| := by rw [abs_sub_comm t z.im]
    linarith only [h, himdiff]
  have hthi : |z.im| ≤ |t| + r := by
    have h : |z.im| ≤ |z.im - t| + |t| := by
      calc |z.im| = |(z.im - t) + t| := by ring_nf
        _ ≤ |z.im - t| + |t| := abs_add_le _ _
    linarith only [h, himdiff]
  have ht0 : 0 < |t| := by linarith only [ht]
  have hz0 : 0 < |z.im| := by linarith only [htlo, ht, hr]
  have htlog : 1 ≤ Real.log |t| := by
    have he : Real.exp 1 ≤ |t| := by
      have he := Real.exp_one_lt_d9
      linarith only [he, ht]
    have h := Real.log_le_log (Real.exp_pos 1) he
    simpa only [Real.log_exp] using h
  have hzlog : Real.log |z.im| ≤ 2 * Real.log |t| := by
    have h := Real.log_le_log hz0 (show |z.im| ≤ 2 * |t| by
      linarith only [hthi, hr, ht])
    rw [Real.log_mul (by norm_num) ht0.ne'] at h
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [this]
    linarith only [h, h2, htlog]
  rcases le_or_gt z.re (9 / 8) with hzright | hzright
  · have hgap : 0 < z.re - (1 / 2 + 3 / 8) := by
      linarith only [hrelo, hr]
    have hbz := hb z.re z.im (by linarith only [htlo, ht, hr])
      (by linarith only [hgap]) hzright
    rw [Complex.re_add_im] at hbz
    have hq : C * Real.log |z.im| / (z.re - (1 / 2 + 3 / 8)) ≤
        (2 * C / (1 / 4 - r)) * Real.log |t| := by
      have hnum : C * Real.log |z.im| ≤ C * (2 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hzlog hC.le
      calc C * Real.log |z.im| / (z.re - (1 / 2 + 3 / 8))
          ≤ C * (2 * Real.log |t|) / (1 / 4 - r) :=
            div_le_div₀ (by positivity) hnum hδ (by linarith only [hrelo])
        _ = _ := by ring
    exact (hbz.trans hq).trans (by
      have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2048) (by linarith : 0 ≤ Real.log |t|)
      nlinarith only [this])
  · have hbz := norm_logDeriv_zeta_right_le (z := z)
      (by linarith only [hzright]) (by linarith only [hrehi, hr])
    have hK0 : 0 ≤ 2 * C / (1 / 4 - r) := by positivity
    have hx := mul_nonneg hK0 (show 0 ≤ Real.log |t| by linarith only [htlog])
    nlinarith only [hbz, htlog, hx]

private theorem differentiableOn_logDeriv_zeta_disk {t : ℝ} (ht : 8 ≤ |t|) :
    DifferentiableOn ℂ (logDeriv riemannZeta)
      (ball ((9 / 8 : ℂ) + (t : ℂ) * I) (1 / 4)) := by
  have hne : ∀ z ∈ ball ((9 / 8 : ℂ) + (t : ℂ) * I) (1 / 4), z ≠ 1 := by
    intro z hz hzone
    have hi := Complex.abs_im_le_norm (z - ((9 / 8 : ℂ) + (t : ℂ) * I))
    rw [hzone] at hi
    have he : (1 - ((9 / 8 : ℂ) + (t : ℂ) * I)).im = -t := by norm_num
    rw [he, abs_neg] at hi
    have hd := mem_ball_iff_norm.mp hz
    rw [hzone] at hd
    linarith only [hi, hd, ht]
  have hdiff : DifferentiableOn ℂ riemannZeta
      (ball ((9 / 8 : ℂ) + (t : ℂ) * I) (1 / 4)) :=
    fun z hz => (differentiableAt_riemannZeta (hne z hz)).differentiableWithinAt
  have hzfree : ∀ z ∈ ball ((9 / 8 : ℂ) + (t : ℂ) * I) (1 / 4),
      riemannZeta z ≠ 0 := by
    intro z hz
    apply riemannZeta_ne_zero_of_seven_eighths_lt_re
    have hr := Complex.abs_re_le_norm (z - ((9 / 8 : ℂ) + (t : ℂ) * I))
    have he : (z - ((9 / 8 : ℂ) + (t : ℂ) * I)).re = z.re - 9 / 8 := by norm_num
    rw [he] at hr
    have hd := mem_ball_iff_norm.mp hz
    linarith only [(abs_le.mp hr).1, hd]
  change DifferentiableOn ℂ (fun z => deriv riemannZeta z / riemannZeta z) _
  exact (hdiff.deriv isOpen_ball).div hdiff hzfree

/-- Three circles turn the zero-free strip into a power saving in the logarithm. -/
theorem exists_logDeriv_zeta_log_power_bound {σ : ℝ}
    (hσ : (7 : ℝ) / 8 < σ) (hσ1 : σ < 1) :
    ∃ K θ : ℝ, 0 < K ∧ 0 ≤ θ ∧ θ < 1 ∧
      ∀ t : ℝ, 8 ≤ |t| →
        ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
          K * (Real.log |t|) ^ θ := by
  let r : ℝ := 9 / 8 - σ
  let r₃ : ℝ := (r + 1 / 4) / 2
  have hr1 : (1 : ℝ) / 16 < r := by dsimp [r]; linarith only [hσ1]
  have hr : r < 1 / 4 := by dsimp [r]; linarith only [hσ]
  have hr0 : 0 < r := by linarith only [hr1]
  have hrr₃ : r < r₃ := by dsimp [r₃]; linarith only [hr]
  have hr₃ : r₃ < 1 / 4 := by dsimp [r₃]; linarith only [hr]
  have hr₃0 : 0 < r₃ := lt_trans hr0 hrr₃
  obtain ⟨C, hC, hb⟩ := exists_logDeriv_disk_log_bound hr₃0 hr₃
  let θ : ℝ := (Real.log r - Real.log (1 / 16)) /
    (Real.log r₃ - Real.log (1 / 16))
  have hl1 : Real.log (1 / 16) < Real.log r :=
    Real.log_lt_log (by norm_num) hr1
  have hl3 : Real.log r < Real.log r₃ := Real.log_lt_log hr0 hrr₃
  have hden : 0 < Real.log r₃ - Real.log (1 / 16) := by linarith only [hl1, hl3]
  have hθ0 : 0 ≤ θ := by dsimp [θ]; exact div_nonneg (by linarith only [hl1]) hden.le
  have hθ1 : θ < 1 := by
    dsimp [θ]
    exact (div_lt_one hden).mpr (by linarith only [hl3])
  refine ⟨(2048 : ℝ) ^ (1 - θ) * C ^ θ, θ, by positivity, hθ0, hθ1, ?_⟩
  intro t ht
  let c : ℂ := (9 / 8 : ℂ) + (t : ℂ) * I
  let z : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hdist : ‖z - c‖ = r := by
    have he : z - c = ((σ - 9 / 8 : ℝ) : ℂ) := by dsimp [z, c]; push_cast; ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hσ1])]
    dsimp [r]
    ring
  have hsmall : ∀ w : ℂ, ‖w - c‖ = 1 / 16 →
      ‖logDeriv riemannZeta w‖ ≤ 2048 := by
    intro w hw
    have hwr := Complex.abs_re_le_norm (w - c)
    have he : (w - c).re = w.re - 9 / 8 := by dsimp [c]; norm_num
    rw [he, hw] at hwr
    exact norm_logDeriv_zeta_right_le
      (by linarith only [(abs_le.mp hwr).1])
      (by linarith only [(abs_le.mp hwr).2])
  have hlarge : ∀ w : ℂ, ‖w - c‖ = r₃ →
      ‖logDeriv riemannZeta w‖ ≤ C * Real.log |t| :=
    fun w hw => hb t ht w hw.le
  have hthree := HTGeometry.norm_le_of_three_circles_center
    (g := logDeriv riemannZeta) (c := c) (r₁ := 1 / 16) (r₃ := r₃) (R := 1 / 4)
    (by norm_num) (lt_trans hr1 hrr₃) hr₃ (differentiableOn_logDeriv_zeta_disk ht)
    hsmall hlarge (z := z) (by rw [hdist]; exact hr1.le)
    (by rw [hdist]; exact hrr₃.le)
  rw [hdist] at hthree
  change ‖logDeriv riemannZeta z‖ ≤ (2048 : ℝ) ^ (1 - θ) *
    (C * Real.log |t|) ^ θ at hthree
  have hlog : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith only [ht])
  rw [Real.mul_rpow hC.le hlog] at hthree
  simpa only [mul_assoc, z] using hthree

/-- On each fixed line right of seven eighths, `ζ'/ζ` is sublogarithmic. -/
theorem exists_logDeriv_zeta_le_epsilon_log {σ ε : ℝ}
    (hσ : (7 : ℝ) / 8 < σ) (hσ1 : σ < 1) (hε : 0 < ε) :
    ∃ T : ℝ, 8 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ ε * Real.log |t| := by
  obtain ⟨K, θ, hK, _, hθ, hb⟩ := exists_logDeriv_zeta_log_power_bound hσ hσ1
  have hlim : Tendsto (fun x : ℝ => K * x ^ (-(1 - θ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by linarith only [hθ] : 0 < 1 - θ)).const_mul K
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨max 8 (Real.exp (max 1 A)), le_max_left _ _, ?_⟩
  intro t ht
  have ht8 : 8 ≤ |t| := (le_max_left _ _).trans ht
  have hte : Real.exp (max 1 A) ≤ |t| := (le_max_right _ _).trans ht
  have hlog : max 1 A ≤ Real.log |t| := by
    have h := Real.log_le_log (Real.exp_pos _) hte
    simpa only [Real.log_exp] using h
  have hx : 0 < Real.log |t| := by linarith only [(le_max_left (1 : ℝ) A).trans hlog]
  have hsmall := hA (Real.log |t|) ((le_max_right _ _).trans hlog)
  have heq : (K * (Real.log |t|) ^ (-(1 - θ))) * Real.log |t| =
      K * (Real.log |t|) ^ θ := by
    calc (K * (Real.log |t|) ^ (-(1 - θ))) * Real.log |t|
        = K * ((Real.log |t|) ^ (-(1 - θ)) * (Real.log |t|) ^ (1 : ℝ)) := by
          rw [Real.rpow_one]
          ring
      _ = K * (Real.log |t|) ^ (-(1 - θ) + 1) := by rw [← Real.rpow_add hx]
      _ = K * (Real.log |t|) ^ θ := by congr 2; ring
  have hmul := mul_le_mul_of_nonneg_right hsmall.le hx.le
  rw [heq] at hmul
  exact (hb t ht8).trans hmul

end GaloisForLFunctions.ConjugateDiagonalGeometry
