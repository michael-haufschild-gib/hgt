import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovZeroFree
import GaloisForLFunctions.HTGeometry.LogDerivativeBound
import GaloisForLFunctions.RHTower.CompletedSplitRightHalfPlane
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Sublogarithmic logarithmic derivative on the one-line

The Vinogradov–Korobov zero-free disks sit inside the wider disks where zeta has
polylogarithmic growth. A logarithm on each zero-free disk therefore gives
`‖ζ'/ζ(1+it)‖ = o(log |t|)`. The anchor lower bound is the three-four-one inequality.
-/

namespace RHTower.Sieve

open Complex Metric Filter

private theorem vk_zeroFreeWidth_pos_le {t : ℝ}
    (ht : Real.exp 30 ≤ Real.log (5 * t)) :
    0 < vinogradovKorobovZeroFreeWidth t ∧
      vinogradovKorobovZeroFreeWidth t ≤ 1 / 100 := by
  have hθ := vinogradovKorobovWidth_pos ht
  have hM := one_le_log_of_exp_thirty_le ht
  unfold vinogradovKorobovZeroFreeWidth
  refine ⟨div_pos hθ (by linarith), ?_⟩
  exact (div_le_self hθ.le (by linarith)).trans
    ((vinogradovKorobovWidth_le ht).trans (by norm_num))

private theorem vk_zeroFreeWidth_antitone {s t : ℝ} (hs : 0 < s)
    (hlarge : Real.exp 30 ≤ Real.log (5 * s)) (hst : s ≤ t) :
    vinogradovKorobovZeroFreeWidth t ≤ vinogradovKorobovZeroFreeWidth s := by
  have hlog : Real.log (5 * s) ≤ Real.log (5 * t) :=
    Real.log_le_log (by positivity) (by linarith)
  have hθ := vinogradovKorobovWidth_anti hlarge hlog
  have hM := one_le_log_of_exp_thirty_le hlarge
  have hlogpos : 0 < Real.log (5 * s) := lt_of_lt_of_le (Real.exp_pos _) hlarge
  have hMM := Real.log_le_log hlogpos hlog
  unfold vinogradovKorobovZeroFreeWidth
  exact (div_le_div_of_nonneg_right hθ (by linarith)).trans
    (div_le_div_of_nonneg_left (vinogradovKorobovWidth_pos hlarge).le
      (by linarith) (by linarith))

/-- Zero-free disks and polylogarithmic growth replace the usual `log t` numerator
in the logarithmic-derivative estimate by `log log t`. -/
theorem exists_logDeriv_zeta_bound_loglog_div_width :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ‖logDeriv riemannZeta (1 + (t : ℂ) * I)‖ ≤
        64 * Real.log (Real.log (5 * (t + 1))) /
          vinogradovKorobovZeroFreeWidth (t + 1) := by
  obtain ⟨T₀, hfree⟩ := exists_riemannZeta_ne_zero_vinogradovKorobov_width
  obtain ⟨C, hCdef⟩ : ∃ C, C = vinogradovKorobovGrowthConstant := ⟨_, rfl⟩
  have hC : 0 ≤ C := by
    rw [hCdef]
    unfold vinogradovKorobovGrowthConstant vinogradovKorobovBlockConstant
    positivity
  refine ⟨max (max (T₀ + 1) (2 * Real.exp (Real.exp 30) + 1))
    (Real.exp (Real.exp (max (Real.log (C + 1)) (Real.log 1600001)))), ?_⟩
  intro t ht
  have htT : T₀ + 1 ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have htE : 2 * Real.exp (Real.exp 30) + 1 ≤ t :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  have htM : Real.exp (Real.exp (max (Real.log (C + 1)) (Real.log 1600001))) ≤ t :=
    (le_max_right _ _).trans ht
  have hE := Real.exp_pos (Real.exp 30)
  have hE1 := Real.one_le_exp (Real.exp_pos (30 : ℝ)).le
  have ht0 : 0 < t := by linarith only [htE, hE]
  have hLt : Real.exp 30 ≤ Real.log (5 * t) := by
    rw [← Real.log_exp (Real.exp 30)]
    exact Real.log_le_log hE (by linarith only [htE, hE])
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (5 * (t + 1)) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = Real.log L := ⟨_, rfl⟩
  have hLtL : Real.log (5 * t) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by positivity) (by linarith)
  have hL : Real.exp 30 ≤ L := hLt.trans hLtL
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 30)).trans hL
  have hM30 : 30 ≤ M := by rw [hMdef]; exact one_le_log_of_exp_thirty_le hL
  have hM0 : 0 < M := by linarith only [hM30]
  have hMlarge : max (Real.log (C + 1)) (Real.log 1600001) ≤ M := by
    have h1 := Real.log_le_log (Real.exp_pos _) htM
    rw [Real.log_exp] at h1
    have htlog : Real.log t ≤ L :=
      (Real.log_le_log ht0 (by linarith only [ht0])).trans hLtL
    have h2 := Real.log_le_log (Real.exp_pos _) (h1.trans htlog)
    rwa [Real.log_exp, ← hMdef] at h2
  obtain ⟨r, hrdef⟩ : ∃ r, r = vinogradovKorobovZeroFreeWidth (t + 1) := ⟨_, rfl⟩
  have hrprops : 0 < r ∧ r ≤ 1 / 100 := by
    rw [hrdef]; exact vk_zeroFreeWidth_pos_le (by rwa [← hLdef])
  have hr0 := hrprops.1
  have hrsmall := hrprops.2
  have hrθ : r ≤ vinogradovKorobovWidth (Real.log (5 * t)) := by
    rw [hrdef, vinogradovKorobovZeroFreeWidth, ← hLdef, ← hMdef]
    exact (div_le_self (vinogradovKorobovWidth_pos hL).le (by linarith only [hM30])).trans
      (vinogradovKorobovWidth_anti hLt hLtL)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((1 + r / 4 : ℝ) : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  have hcre : c.re = 1 + r / 4 := by rw [hc]; simp
  have hcim : c.im = t := by rw [hc]; simp
  have hdisc_im : ∀ w ∈ ball c r, t - 1 < w.im ∧ w.im < t + 1 := by
    intro w hw
    have hd := mem_ball_iff_norm.mp hw
    have hi := Complex.abs_im_le_norm (w - c)
    rw [Complex.sub_im, hcim] at hi
    have hi' := abs_le.mp hi
    constructor <;> linarith only [hi'.1, hi'.2, hd, hrsmall]
  have hne : ∀ w ∈ ball c r, w ≠ 1 := by
    intro w hw hw1
    have hi := (hdisc_im w hw).1
    rw [hw1, Complex.one_im] at hi
    linarith only [hi, htE, hE]
  have hzfree : ∀ w ∈ ball c r, riemannZeta w ≠ 0 := by
    intro w hw
    have hi := hdisc_im w hw
    have hi0 : 0 < w.im := by linarith only [hi.1, htE, hE]
    have hiL : Real.exp 30 ≤ Real.log (5 * w.im) := by
      rw [← Real.log_exp (Real.exp 30)]
      exact Real.log_le_log hE (by linarith only [hi.1, htE, hE])
    have hrw : r ≤ vinogradovKorobovZeroFreeWidth w.im := by
      rw [hrdef]
      exact vk_zeroFreeWidth_antitone hi0 hiL hi.2.le
    have hd := mem_ball_iff_norm.mp hw
    have hre := Complex.abs_re_le_norm (w - c)
    rw [Complex.sub_re, hcre] at hre
    have hre' := (abs_le.mp hre).1
    have hβ : 1 - vinogradovKorobovZeroFreeWidth w.im < w.re := by
      linarith only [hre', hd, hrw, hr0]
    simpa only [Complex.re_add_im] using
      hfree w.re w.im (by linarith only [hi.1, htT]) hβ
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c r) := by
    intro w hw
    exact (differentiableAt_riemannZeta (hne w hw)).differentiableWithinAt
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ, Φ = C * L + 1 := ⟨_, rfl⟩
  have hΦ0 : 0 < Φ := by rw [hΦdef]; positivity
  have hgrowth : ∀ h : ℝ, t ≤ h → h ≤ 4 * t →
      ∀ w ∈ ball (((1 + r / 4 : ℝ) : ℂ) + (h : ℂ) * I)
        (vinogradovKorobovWidth (Real.log (5 * t))), ‖riemannZeta w‖ ≤ Φ := by
    intro h hh1 hh2 w hw
    have hb := norm_riemannZeta_lt_on_disc (by linarith only [htE])
      (by linarith only [hr0]) (by linarith only [hrsmall]) hh1 hh2 hw
    refine hb.le.trans ?_
    rw [← hCdef, hΦdef]
    linarith only [mul_le_mul_of_nonneg_left hLtL hC]
  have hbound : ∀ w ∈ ball c r, ‖riemannZeta w‖ ≤ Φ := by
    intro w hw
    apply hgrowth t le_rfl (by linarith only [ht0]) w
    rw [← hc, mem_ball_iff_norm]
    exact (mem_ball_iff_norm.mp hw).trans_le hrθ
  have hB : ‖riemannZeta (((1 + r / 4 : ℝ) : ℂ) + (2 * t : ℂ) * I)‖ ≤ Φ := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      hgrowth (2 * t) (by linarith only [ht0]) (by linarith only [ht0]) _
        (mem_ball_self (vinogradovKorobovWidth_pos hLt))
  have hlogΦ : Real.log Φ ≤ 2 * M := by
    rw [hΦdef, hMdef]
    exact vk_log_Phi_le hC hL1 (by
      rw [← hMdef]; exact (le_max_left _ _).trans hMlarge)
  have hlogδ : Real.log (1 + 1 / (r / 4)) ≤ 5 * M := by
    have hbase : Real.log (1 + 1 / (7 * r)) ≤ 4 * M := by
      rw [hrdef, vinogradovKorobovZeroFreeWidth, ← hLdef, hMdef]
      exact vk_log_delta_le hL (by
        rw [← hMdef]; exact (le_max_right _ _).trans hMlarge)
    have heq : 28 * (1 + 1 / (7 * r)) = (1 + 1 / (r / 4)) + 27 := by
      field_simp
      ring
    have hb := Real.log_le_log (by positivity : 0 < 1 + 1 / (r / 4))
      (show 1 + 1 / (r / 4) ≤ 28 * (1 + 1 / (7 * r)) by linarith only [heq])
    rw [Real.log_mul (by norm_num) (by positivity)] at hb
    have h28 : Real.log 28 ≤ 27 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 28)
      linarith only [this]
    linarith only [hb, h28, hbase, hM30]
  have hanchor : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr
    (riemannZeta_ne_zero_of_one_le_re (by rw [hcre]; linarith only [hr0]))
  have hratio : Real.log (Φ / ‖riemannZeta c‖) + 1 ≤ 8 * M := by
    have hb := neg_log_norm_riemannZeta_le_of
      (by linarith only [hr0] : 1 < 1 + r / 4) hB
    rw [show 1 + r / 4 - 1 = r / 4 by ring, ← hc] at hb
    rw [Real.log_div hΦ0.ne' hanchor.ne']
    linarith only [hb, hlogΦ, hlogδ, hM30]
  have hdist : ‖(1 + (t : ℂ) * I) - c‖ ≤ r / 4 := by
    have heq : (1 + (t : ℂ) * I) - c = ((-r / 4 : ℝ) : ℂ) := by
      rw [hc]; push_cast; ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hr0])]
    linarith
  have hb := GaloisForLFunctions.HTGeometry.norm_logDeriv_le
    (R := r) (r := r / 2) (ρ := r / 4) (M := Φ)
    (by linarith only [hr0]) (by linarith only [hr0]) (by linarith only [hr0])
    hdiff hzfree hbound hanchor le_rfl hdist
  rw [← hrdef, ← hLdef, ← hMdef]
  rw [logDeriv_apply]
  calc ‖deriv riemannZeta (1 + (t : ℂ) * I) / riemannZeta (1 + (t : ℂ) * I)‖
      ≤ 2 * (Real.log (Φ / ‖riemannZeta c‖) + 1) * (r / 2) /
          (r - r / 2) / (r / 2 - r / 4) := hb
    _ = 8 * (Real.log (Φ / ‖riemannZeta c‖) + 1) / r := by field_simp; ring
    _ ≤ 64 * M / r := div_le_div_of_nonneg_right (by linarith only [hratio]) hr0.le

private theorem eventually_loglog_div_vkWidth_le {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      64 * Real.log (Real.log (5 * (t + 1))) /
          vinogradovKorobovZeroFreeWidth (t + 1) ≤ ε * Real.log t := by
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop ((8 : ℝ) / 3)
      (by norm_num : (0 : ℝ) < 1 / 3)).bound
        (show 0 < ε / 204800000 by positivity))
  refine ⟨max 10 (Real.exp (max (Real.exp 30) L₀)), ?_⟩
  intro t ht
  have ht10 : (10 : ℝ) ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith only [ht10]
  have hte : Real.exp (max (Real.exp 30) L₀) ≤ t := (le_max_right _ _).trans ht
  have htlog : max (Real.exp 30) L₀ ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos _) hte
    rwa [Real.log_exp] at h
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (5 * (t + 1)) := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M, M = Real.log L := ⟨_, rfl⟩
  have hlogL : Real.log t ≤ L := by
    rw [hLdef]
    exact Real.log_le_log ht0 (by linarith only [ht0])
  have hL : Real.exp 30 ≤ L := (le_max_left _ _).trans (htlog.trans hlogL)
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hM0 : 0 < M := by
    rw [hMdef]
    linarith only [one_le_log_of_exp_thirty_le hL]
  have hpow : M ^ ((8 : ℝ) / 3) ≤ (ε / 204800000) * L ^ ((1 : ℝ) / 3) := by
    have hb := hL₀ L ((le_max_right _ _).trans (htlog.trans hlogL))
    rw [← hMdef, Real.norm_of_nonneg (Real.rpow_nonneg hM0.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _)] at hb
    exact hb
  have hLL : L ≤ 2 * Real.log t := by
    have hsq : 5 * (t + 1) ≤ t ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right ht10 ht0.le
      nlinarith only [hh, ht10]
    have hh := Real.log_le_log (by positivity : 0 < 5 * (t + 1)) hsq
    rw [Real.log_pow, ← hLdef] at hh
    norm_num only [Nat.cast_ofNat] at hh
    exact hh
  have hwidth : 64 * M / vinogradovKorobovZeroFreeWidth (t + 1) =
      102400000 * L ^ ((2 : ℝ) / 3) * M ^ ((8 : ℝ) / 3) := by
    rw [vinogradovKorobovZeroFreeWidth, ← hLdef, ← hMdef,
      vinogradovKorobovWidth, ← hMdef]
    have heq : M ^ ((8 : ℝ) / 3) = M ^ 2 * M ^ ((2 : ℝ) / 3) := by
      rw [show (8 : ℝ) / 3 = 2 + 2 / 3 by norm_num, Real.rpow_add hM0, Real.rpow_two]
    rw [show -(2 : ℝ) / 3 = -((2 : ℝ) / 3) by ring,
      Real.rpow_neg hL0.le, Real.rpow_neg hM0.le, heq]
    field_simp
    ring
  rw [← hLdef, ← hMdef, hwidth]
  calc 102400000 * L ^ ((2 : ℝ) / 3) * M ^ ((8 : ℝ) / 3)
      ≤ 102400000 * L ^ ((2 : ℝ) / 3) *
          ((ε / 204800000) * L ^ ((1 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ε / 2 * L := by
      rw [show 102400000 * L ^ ((2 : ℝ) / 3) *
          ((ε / 204800000) * L ^ ((1 : ℝ) / 3)) =
          ε / 2 * (L ^ ((2 : ℝ) / 3) * L ^ ((1 : ℝ) / 3)) by ring,
        ← Real.rpow_add hL0]
      norm_num
    _ ≤ ε * Real.log t := by
      have hpay := mul_le_mul_of_nonneg_left hLL hε.le
      linarith only [hpay]

/-- On the positive one-line the logarithmic derivative is smaller than every
positive multiple of `log t`, beyond a fixed threshold. -/
theorem exists_logDeriv_zeta_le_epsilon_log_pos {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      ‖logDeriv riemannZeta (1 + (t : ℂ) * I)‖ ≤ ε * Real.log t := by
  obtain ⟨T₁, hT₁⟩ := exists_logDeriv_zeta_bound_loglog_div_width
  obtain ⟨T₂, hT₂⟩ := eventually_loglog_div_vkWidth_le hε
  refine ⟨max 2 (max T₁ T₂), le_max_left _ _, ?_⟩
  intro t ht
  have hmax : max T₁ T₂ ≤ t := (le_max_right _ _).trans ht
  exact (hT₁ t ((le_max_left _ _).trans hmax)).trans
    (hT₂ t ((le_max_right _ _).trans hmax))

/-- The norm of `ζ'/ζ` on `Re s = 1` is sublogarithmic in both directions. -/
theorem exists_logDeriv_zeta_le_epsilon_log_abs {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      ‖logDeriv riemannZeta (1 + (t : ℂ) * I)‖ ≤ ε * Real.log |t| := by
  obtain ⟨T, hT, hb⟩ := exists_logDeriv_zeta_le_epsilon_log_pos hε
  refine ⟨T, hT, ?_⟩
  intro t ht
  have hh := hb |t| ht
  rcases le_or_gt 0 t with ht0 | ht0
  · simpa only [abs_of_nonneg ht0] using hh
  · have heq : 1 + ((|t| : ℝ) : ℂ) * I =
        (starRingEnd ℂ) (1 + (t : ℂ) * I) := by
      rw [abs_of_neg ht0]
      apply Complex.ext <;> simp
    rwa [heq, RHTower.logDeriv_riemannZeta_conj, Complex.norm_conj] at hh

end RHTower.Sieve
