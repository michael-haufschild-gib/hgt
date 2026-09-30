import GaloisForLFunctions.RHTower.ConvexLogModulusTransport
import GaloisForLFunctions.RHTower.ZetaLogDerivTypicalBox
import GaloisForLFunctions.RHTower.XiNearLineModulusComparison
import GaloisForLFunctions.RHTower.XiSliceLogLogOrderPositivity

/-!
# The arc of the slice saddle from log-derivative scale data

Let `ZetaLogDerivScaleData t R B` hold, `R ≤ Rs ≤ 5R` and `z₀ = ½ + Rs + it`. On the box
`½ + 3R/4 ≤ Re s ≤ ½ + 6R`, `|Im s − t| ≤ 6R`, which lies in the zero-free convex set
`½ + R/2 < Re s < 2`, `|Im s − t| < 12R`, the Stirling comparison gives
`|ξ'/ξ(s) − ½ log(z₀/2)| ≤ 4 + B`, hence

`|ξ(s)| ≤ |ξ(z₀)| exp(Re((s − z₀) ½ log(z₀/2)) + (4 + B)|s − z₀|)` (`norm_xi_le_of_box`).

For the arc point `w = Rs e^{iθ} = a + ib`, `|g_t(w)| = |ξ(½ + a + i(t+b))| |ξ(½ + a + i(t−b))|`. If
`a ≥ 3R/4` both points lie in the box; otherwise the near-line comparison
(`norm_xi_half_add_le_of_zeros`, whose zero condition follows from the zero-free part of the data)
moves them to `Re = ½ + 3R/4`. The main terms of the two factors add to `(a − Rs) log|z₀/2|`, and

`|S(θ)| ≤ exp(−Rs θ₁² log(t/2)/10)` for `θ₁ ≤ θ ≤ π/2` when `80(4 + B) ≤ θ₁ log(t/2)`
(`norm_sliceArc_le_of_logDerivScaleData`).
-/

noncomputable section

open Complex Set Metric

namespace RHTower

/-- The zero-free convex set `½ + R/2 < Re s < 2`, `|Im s − t| < 12R`. -/
def logDerivZeroFreeBox (t R : ℝ) : Set ℂ :=
  {s | 1 / 2 + R / 2 < s.re} ∩ {s | s.re < 2} ∩ {s | t - 12 * R < s.im} ∩ {s | s.im < t + 12 * R}

/-- The closed box `½ + 3R/4 ≤ Re s ≤ ½ + 6R`, `|Im s − t| ≤ 6R`. -/
def logDerivBox (t R : ℝ) : Set ℂ :=
  {s | 1 / 2 + 3 * R / 4 ≤ s.re} ∩ {s | s.re ≤ 1 / 2 + 6 * R} ∩ {s | t - 6 * R ≤ s.im} ∩
    {s | s.im ≤ t + 6 * R}

theorem isOpen_logDerivZeroFreeBox (t R : ℝ) : IsOpen (logDerivZeroFreeBox t R) := by
  unfold logDerivZeroFreeBox
  refine (((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).inter
    (isOpen_lt continuous_const Complex.continuous_im)).inter
    (isOpen_lt Complex.continuous_im continuous_const)

theorem convex_logDerivZeroFreeBox (t R : ℝ) : Convex ℝ (logDerivZeroFreeBox t R) :=
  (((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)).inter
    (convex_halfSpace_im_gt _)).inter (convex_halfSpace_im_lt _)

theorem convex_logDerivBox (t R : ℝ) : Convex ℝ (logDerivBox t R) :=
  (((convex_halfSpace_re_ge _).inter (convex_halfSpace_re_le _)).inter
    (convex_halfSpace_im_ge _)).inter (convex_halfSpace_im_le _)

theorem mem_logDerivBox {t R : ℝ} {s : ℂ} :
    s ∈ logDerivBox t R ↔ 1 / 2 + 3 * R / 4 ≤ s.re ∧ s.re ≤ 1 / 2 + 6 * R ∧
      |s.im - t| ≤ 6 * R := by
  unfold logDerivBox
  simp only [mem_inter_iff, mem_setOf_eq, abs_le]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, by linarith⟩, by linarith⟩

theorem logDerivBox_subset {t R : ℝ} (hR : 0 < R) (hR16 : R ≤ 1 / 16) :
    logDerivBox t R ⊆ logDerivZeroFreeBox t R := by
  intro s hs
  rw [mem_logDerivBox] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  have h3' := abs_le.mp h3
  unfold logDerivZeroFreeBox
  simp only [mem_inter_iff, mem_setOf_eq]
  exact ⟨⟨⟨by linarith, by linarith⟩, by linarith⟩, by linarith⟩

namespace ZetaLogDerivScaleData

variable {t R B : ℝ}

/-- `ξ` has no zero on the zero-free box. -/
theorem xi_ne_zero (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) {s : ℂ}
    (hs : s ∈ logDerivZeroFreeBox t R) : xi s ≠ 0 := by
  unfold logDerivZeroFreeBox at hs
  simp only [mem_inter_iff, mem_setOf_eq] at hs
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hs
  by_cases hre : 1 ≤ s.re
  · exact xi_ne_zero_of_one_le_re hre
  intro h0
  have hs1 : s ≠ 1 := by intro e; rw [e] at hre; simp at hre
  have hζ := (xi_eq_zero_iff (by linarith) hs1).1 h0
  have := h.zeroFree s hζ h1
  have hab : |s.im - t| < 12 * R := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

/-- `ζ` has no zero on the box. -/
theorem riemannZeta_ne_zero (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) {s : ℂ}
    (hs : s ∈ logDerivBox t R) : riemannZeta s ≠ 0 := by
  rw [mem_logDerivBox] at hs
  intro h0
  have := h.zeroFree s h0 (by linarith [hs.1])
  linarith [hs.2.2]

/-- **Stirling comparison on the box.** -/
theorem stirling_box (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 8 ≤ t) {s : ℂ} (hs : s ∈ logDerivBox t R) :
    ‖_root_.logDeriv xi s - Complex.log (s / 2) / 2‖ ≤ 3 + B := by
  have hζ := h.riemannZeta_ne_zero hR hs
  rw [mem_logDerivBox] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  have h3' := abs_le.mp h3
  have him : 4 ≤ s.im := by linarith
  refine norm_logDeriv_xi_sub_half_log_le_of_zeta (by linarith) (by linarith) ?_ hζ
    (h.logDeriv s h1 h2 h3)
  exact le_trans (by rw [abs_of_pos (by linarith)]; exact him) (Complex.abs_im_le_norm s)

end ZetaLogDerivScaleData

/-- `‖log(s/2) − log(z₀/2)‖ ≤ 1/2` on the box. -/
theorem norm_log_half_sub_le_of_box {t R : ℝ} (hR : 0 < R) (hR16 : R ≤ 1 / 16) (ht : 64 ≤ t)
    {s z₀ : ℂ} (hs : s ∈ logDerivBox t R) (hz₀ : z₀ ∈ logDerivBox t R) :
    ‖Complex.log (s / 2) - Complex.log (z₀ / 2)‖ ≤ 1 / 2 := by
  have hseg : ∀ u ∈ Icc (0 : ℝ) 1, z₀ + (u : ℂ) * (s - z₀) ∈ logDerivBox t R := by
    intro u hu
    have hc := convex_logDerivBox t R hz₀ hs (show 0 ≤ 1 - u by linarith [hu.2]) hu.1 (by ring)
    have e : (1 - u) • z₀ + u • s = z₀ + (u : ℂ) * (s - z₀) := by
      rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
    rwa [e] at hc
  have him : ∀ p ∈ logDerivBox t R, 32 ≤ p.im := by
    intro p hp
    rw [mem_logDerivBox] at hp
    have := abs_le.mp hp.2.2
    linarith
  have hderiv : ∀ p ∈ logDerivBox t R,
      HasDerivAt (fun z : ℂ => Complex.log (z / 2)) (1 / p) p := by
    intro p hp
    have hslit : p / 2 ∈ Complex.slitPlane := by
      refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      have := him p hp
      simp only [Complex.div_ofNat_im]
      linarith
    have hp0 : p ≠ 0 := by
      intro h0; have := him p hp; rw [h0] at this; simp at this; linarith
    exact (((hasDerivAt_id' p).div_const 2).clog hslit).congr_deriv (by field_simp)
  have hdiff : ∀ u ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ (fun z : ℂ => Complex.log (z / 2))
      (z₀ + (u : ℂ) * (s - z₀)) := fun u hu => (hderiv _ (hseg u hu)).differentiableAt
  have hM : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖deriv (fun z : ℂ => Complex.log (z / 2)) (z₀ + (u : ℂ) * (s - z₀))‖ ≤ 1 / 32 := by
    intro u hu
    rw [(hderiv _ (hseg u hu)).deriv, norm_div, norm_one]
    have := him _ (hseg u hu)
    have hn : 32 ≤ ‖z₀ + (u : ℂ) * (s - z₀)‖ :=
      le_trans (by rw [abs_of_pos (by linarith)]; exact this) (Complex.abs_im_le_norm _)
    exact one_div_le_one_div_of_le (by norm_num) hn
  have hmv := Sieve.norm_sub_le_segment hdiff hM
  have hdist : ‖s - z₀‖ ≤ 16 := by
    rw [mem_logDerivBox] at hs hz₀
    have h1 := abs_le.mp hs.2.2
    have h2 := abs_le.mp hz₀.2.2
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have : |s.re - z₀.re| ≤ 6 * R := abs_le.mpr ⟨by linarith, by linarith⟩
    have : |s.im - z₀.im| ≤ 12 * R := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  calc ‖Complex.log (s / 2) - Complex.log (z₀ / 2)‖ ≤ 1 / 32 * ‖s - z₀‖ := hmv
    _ ≤ 1 / 32 * 16 := by gcongr
    _ = 1 / 2 := by norm_num

theorem segment_mem_logDerivBox {t R : ℝ} {s z₀ : ℂ} (hs : s ∈ logDerivBox t R)
    (hz₀ : z₀ ∈ logDerivBox t R) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    z₀ + (u : ℂ) * (s - z₀) ∈ logDerivBox t R := by
  have hc := convex_logDerivBox t R hz₀ hs (show 0 ≤ 1 - u by linarith [hu.2]) hu.1 (by ring)
  have e : (1 - u) • z₀ + u • s = z₀ + (u : ℂ) * (s - z₀) := by
    rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
  rwa [e] at hc

/-- The two main terms of the arc add to `(a − Rs) log|z₀/2|`. -/
theorem re_main_terms_eq (t Rs a b : ℝ) :
    (((((1 / 2 + a : ℝ) : ℂ) + ((t + b : ℝ) : ℂ) * I) - (((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I)) *
        (Complex.log ((((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I) / 2) / 2)).re +
      (((((1 / 2 + a : ℝ) : ℂ) + ((t - b : ℝ) : ℂ) * I) - (((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I)) *
        (Complex.log ((((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I) / 2) / 2)).re =
      (a - Rs) * Real.log ‖(((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I) / 2‖ := by
  rw [← Complex.add_re, ← add_mul]
  have e : (((1 / 2 + a : ℝ) : ℂ) + ((t + b : ℝ) : ℂ) * I) - (((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I) +
      ((((1 / 2 + a : ℝ) : ℂ) + ((t - b : ℝ) : ℂ) * I) - (((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I)) =
      ((2 * (a - Rs) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.div_ofNat_re, Complex.log_re]
  ring

namespace ZetaLogDerivScaleData

variable {t R B : ℝ}

/-- **Transport of `|ξ|` on the box.** -/
theorem norm_xi_le_of_box (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 64 ≤ t) {z₀ s : ℂ} (hz₀ : z₀ ∈ logDerivBox t R) (hs : s ∈ logDerivBox t R) :
    ‖xi s‖ ≤ ‖xi z₀‖ * Real.exp (((s - z₀) * (Complex.log (z₀ / 2) / 2)).re +
      (4 + B) * ‖s - z₀‖) := by
  have hsub := logDerivBox_subset (t := t) hR hR16
  have hg0 : ∀ z ∈ logDerivZeroFreeBox t R, xi z ≠ 0 := fun z hz => h.xi_ne_zero hR hz
  have hE : ∀ u ∈ Icc (0 : ℝ) 1,
      ‖_root_.logDeriv xi (z₀ + (u : ℂ) * (s - z₀)) - Complex.log (z₀ / 2) / 2‖ ≤ 4 + B := by
    intro u hu
    have hp := segment_mem_logDerivBox hs hz₀ hu
    have h1 := h.stirling_box hR hR16 (by linarith) hp
    have h2 := norm_log_half_sub_le_of_box hR hR16 ht hp hz₀
    have e : _root_.logDeriv xi (z₀ + (u : ℂ) * (s - z₀)) - Complex.log (z₀ / 2) / 2 =
        (_root_.logDeriv xi (z₀ + (u : ℂ) * (s - z₀)) -
          Complex.log ((z₀ + (u : ℂ) * (s - z₀)) / 2) / 2) +
        (Complex.log ((z₀ + (u : ℂ) * (s - z₀)) / 2) - Complex.log (z₀ / 2)) / 2 := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, Complex.norm_ofNat]
    linarith
  have hlog := log_norm_sub_le_of_logDeriv_sub_const (isOpen_logDerivZeroFreeBox t R)
    (convex_logDerivZeroFreeBox t R) (xi_analyticOnNhd_univ.mono (subset_univ _)) hg0
    (hsub hs) (hsub hz₀) hE
  have hs0 : 0 < ‖xi s‖ := norm_pos_iff.mpr (hg0 s (hsub hs))
  have hz0 : 0 < ‖xi z₀‖ := norm_pos_iff.mpr (hg0 z₀ (hsub hz₀))
  rw [← Real.exp_log hs0, ← Real.exp_log hz0, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **The near-line zero condition** at heights within `5R` of `t`, for `d = 3R/4`. -/
theorem nearLine_zero_condition (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) {y : ℝ}
    (hy : |y - t| ≤ 5 * R) :
    ∀ ρ : ℂ, xi ρ = 0 →
      2 * (ρ.re - 1 / 2) ^ 2 ≤ (3 * R / 4) ^ 2 ∨ (ρ.re - 1 / 2) ^ 2 ≤ (ρ.im - y) ^ 2 := by
  intro ρ hρ
  obtain ⟨h0, h1⟩ := xi_zero_re_mem_open_unit hρ
  by_cases hsmall : |ρ.re - 1 / 2| ≤ R / 2
  · left
    have := sq_le_sq' (abs_le.mp hsmall).1 (abs_le.mp hsmall).2
    nlinarith
  right
  push Not at hsmall
  -- a zero `w` with `Re w − ½ = |ρ.re − ½|` and `Im w = Im ρ`
  obtain ⟨w, hw0, hwre, hwim⟩ : ∃ w : ℂ, riemannZeta w = 0 ∧ w.re - 1 / 2 = |ρ.re - 1 / 2| ∧
      w.im = ρ.im := by
    rcases le_or_gt (1 / 2) ρ.re with hge | hlt
    · refine ⟨ρ, ?_, by rw [abs_of_nonneg (by linarith)], rfl⟩
      have hρ1 : ρ ≠ 1 := by intro e; rw [e] at h1; simp at h1
      exact (xi_eq_zero_iff h0 hρ1).1 hρ
    · refine ⟨1 - (starRingEnd ℂ) ρ, ?_, ?_, ?_⟩
      · have hxi : xi (1 - (starRingEnd ℂ) ρ) = 0 := by
          rw [xi_one_sub, xi_conj, hρ, map_zero]
        have hre : 0 < (1 - (starRingEnd ℂ) ρ).re := by simp; linarith
        have hne : 1 - (starRingEnd ℂ) ρ ≠ 1 := by
          intro e
          have := congrArg Complex.re e
          simp at this
          linarith
        exact (xi_eq_zero_iff hre hne).1 hxi
      · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        rw [abs_of_neg (by linarith)]; ring
      · simp
  have hzf := h.zeroFree w hw0 (by linarith)
  rw [hwim, hwre] at hzf
  have hy' := abs_le.mp hy
  have hdist : |ρ.re - 1 / 2| ≤ |ρ.im - y| := by
    have h2 : |ρ.im - t| ≤ |ρ.im - y| + |y - t| := by
      have := abs_sub_le ρ.im y t; linarith
    linarith
  exact sq_le_sq.mpr hdist

end ZetaLogDerivScaleData

/-- Exponent of the arc when both points are in the box. -/
theorem arc_exponent_inbox {Rs θ θ₁ X E : ℝ} (hRs : 0 < Rs) (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ)
    (hθπ : θ ≤ Real.pi / 2) (hX : 0 ≤ X) (hE : 80 * E ≤ θ₁ * X) :
    -(Rs * (1 - Real.cos θ)) * X + E * (4 * (Rs * θ)) ≤ -(Rs * θ₁ ^ 2 * X / 10) := by
  have hθ0 : 0 ≤ θ := by linarith
  have hc5 : θ ^ 2 / 5 ≤ 1 - Real.cos θ :=
    one_sub_cos_ge_sq_div_five (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_pos])
  have h1 : Rs * (θ ^ 2 / 5) * X ≤ Rs * (1 - Real.cos θ) * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc5 hRs.le) hX
  have h2 : E * (4 * (Rs * θ)) ≤ Rs * θ * (θ₁ * X) / 20 := by
    have : 4 * E ≤ θ₁ * X / 20 := by linarith
    have hRθ : 0 ≤ Rs * θ := by positivity
    nlinarith
  have h3 : Rs * θ * (θ₁ * X) ≤ Rs * θ * (θ * X) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθ hX) (by positivity)
  have h4 : Rs * θ₁ ^ 2 * X ≤ Rs * θ ^ 2 * X := by
    have : θ₁ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₁.le hθ 2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hRs.le) hX
  have h5 : 0 ≤ Rs * θ ^ 2 * X := by positivity
  linarith

/-- Exponent of the arc near the critical line. -/
theorem arc_exponent_nearLine {Rs θ₁ X E : ℝ} (hRs : 0 < Rs) (hθ₁ : 0 < θ₁) (hθ₁1 : θ₁ ≤ 1)
    (hX : 0 ≤ X) (hE : 80 * E ≤ θ₁ * X) :
    -(Rs / 4) * X + E * (4 * Rs) ≤ -(Rs * θ₁ ^ 2 * X / 10) := by
  have h1 : 4 * E ≤ X / 20 := by nlinarith
  have h2 : θ₁ ^ 2 ≤ 1 := by nlinarith
  have h3 : Rs * θ₁ ^ 2 * X ≤ Rs * X := by
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hRs.le hX)
    nlinarith
  nlinarith

namespace ZetaLogDerivScaleData

variable {t R B : ℝ}

/-- **The two factors of the arc** at real offset `a ∈ [3R/4, Rs]` and heights `t ± b`. -/
theorem norm_xi_pair_le (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 64 ≤ t) (hB : 0 ≤ B) {Rs a b : ℝ} (hRs1 : R ≤ Rs) (hRs5 : Rs ≤ 5 * R)
    (ha1 : 3 * R / 4 ≤ a) (ha2 : a ≤ Rs) (hb0 : 0 ≤ b) (hb : b ≤ Rs) :
    ‖xi (((1 / 2 + a : ℝ) : ℂ) + ((t + b : ℝ) : ℂ) * I)‖ *
        ‖xi (((1 / 2 + a : ℝ) : ℂ) + ((t - b : ℝ) : ℂ) * I)‖ ≤
      ‖xi (((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 *
        Real.exp ((a - Rs) * Real.log ‖(((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I) / 2‖ +
          (4 + B) * (2 * ((Rs - a) + b))) := by
  set z₀ : ℂ := ((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I with hz₀def
  set zp : ℂ := ((1 / 2 + a : ℝ) : ℂ) + ((t + b : ℝ) : ℂ) * I with hzp
  set zm : ℂ := ((1 / 2 + a : ℝ) : ℂ) + ((t - b : ℝ) : ℂ) * I with hzm
  have hz₀ : z₀ ∈ logDerivBox t R := by
    rw [mem_logDerivBox]; simp only [hz₀def]; simp
    exact ⟨by linarith, by linarith, by linarith⟩
  have hzpB : zp ∈ logDerivBox t R := by
    rw [mem_logDerivBox]; simp only [hzp]; simp
    refine ⟨by linarith, by linarith, ?_⟩
    rw [abs_of_nonneg hb0]; linarith
  have hzmB : zm ∈ logDerivBox t R := by
    rw [mem_logDerivBox]; simp only [hzm]; simp
    refine ⟨by linarith, by linarith, ?_⟩
    rw [abs_of_nonneg hb0]; linarith
  have h1 := h.norm_xi_le_of_box hR hR16 ht hz₀ hzpB
  have h2 := h.norm_xi_le_of_box hR hR16 ht hz₀ hzmB
  have hdp : ‖zp - z₀‖ ≤ (Rs - a) + b := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp only [hzp, hz₀def, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero]
    rw [show 1 / 2 + a - (1 / 2 + Rs) = -(Rs - a) by ring, abs_neg,
      abs_of_nonneg (by linarith), show t + b - t = b by ring, abs_of_nonneg hb0]
  have hdm : ‖zm - z₀‖ ≤ (Rs - a) + b := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp only [hzm, hz₀def, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero]
    rw [show 1 / 2 + a - (1 / 2 + Rs) = -(Rs - a) by ring, abs_neg,
      abs_of_nonneg (by linarith), show t - b - t = -b by ring, abs_neg, abs_of_nonneg hb0]
  have hmain := re_main_terms_eq t Rs a b
  rw [← hz₀def, ← hzp, ← hzm] at hmain
  have hE0 : 0 ≤ 4 + B := by linarith
  calc ‖xi zp‖ * ‖xi zm‖
      ≤ (‖xi z₀‖ * Real.exp (((zp - z₀) * (Complex.log (z₀ / 2) / 2)).re + (4 + B) * ‖zp - z₀‖)) *
        (‖xi z₀‖ * Real.exp (((zm - z₀) * (Complex.log (z₀ / 2) / 2)).re +
          (4 + B) * ‖zm - z₀‖)) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖xi z₀‖ ^ 2 * Real.exp ((((zp - z₀) * (Complex.log (z₀ / 2) / 2)).re +
          ((zm - z₀) * (Complex.log (z₀ / 2) / 2)).re) +
          (4 + B) * (‖zp - z₀‖ + ‖zm - z₀‖)) := by
        rw [sq, show ∀ x y : ℝ, x + y = x + y from fun _ _ => rfl]
        rw [mul_mul_mul_comm, ← Real.exp_add]
        congr 2; ring
    _ ≤ ‖xi z₀‖ ^ 2 * Real.exp ((a - Rs) * Real.log ‖z₀ / 2‖ +
          (4 + B) * (2 * ((Rs - a) + b))) := by
        rw [hmain]
        gcongr
        linarith

end ZetaLogDerivScaleData

namespace ZetaLogDerivScaleData

variable {t R B : ℝ}

/-- **The arc tail from log-derivative scale data.** -/
theorem norm_sliceArc_le (h : ZetaLogDerivScaleData t R B) (hR : 0 < R) (hR16 : R ≤ 1 / 16)
    (ht : 64 ≤ t) (hB : 0 ≤ B) (k : ℕ) {Rs θ₁ θ : ℝ} (hRs1 : R ≤ Rs) (hRs5 : Rs ≤ 5 * R)
    (hθ₁ : 0 < θ₁) (hθ₁1 : θ₁ ≤ 1) (hθ : θ₁ ≤ θ) (hθπ : θ ≤ Real.pi / 2)
    (hsmall : 80 * (4 + B) ≤ θ₁ * Real.log (t / 2)) :
    ‖sliceArc t Rs k θ‖ ≤ Real.exp (-(Rs * θ₁ ^ 2 * Real.log (t / 2) / 10)) := by
  have hRs0 : 0 < Rs := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hθπ
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  have hsinθ : Real.sin θ ≤ θ := Real.sin_le hθ0
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  set z₀ : ℂ := ((1 / 2 + Rs : ℝ) : ℂ) + (t : ℂ) * I with hz₀def
  have hz₀ : z₀ ∈ logDerivBox t R := by
    rw [mem_logDerivBox]; simp only [hz₀def]; simp
    exact ⟨by linarith, by linarith, by linarith⟩
  have hxz₀ : xi z₀ ≠ 0 := h.xi_ne_zero hR (logDerivBox_subset hR hR16 hz₀)
  have hg : ‖xiSliceProduct t (Rs : ℂ)‖ = ‖xi z₀‖ ^ 2 := norm_xiSliceProduct_real t Rs
  have hgpos : 0 < ‖xiSliceProduct t (Rs : ℂ)‖ := by
    rw [hg]; exact pow_pos (norm_pos_iff.mpr hxz₀) 2
  set X := Real.log (t / 2) with hXdef
  have hX0 : 0 ≤ X := Real.log_nonneg (by linarith)
  have hXz : X ≤ Real.log ‖z₀ / 2‖ := by
    apply Real.log_le_log (by linarith)
    rw [norm_div, Complex.norm_ofNat]
    have : t ≤ ‖z₀‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm z₀)
      simp [hz₀def]; rw [abs_of_pos (by linarith)]
    linarith
  set a := Rs * Real.cos θ with ha
  set b := Rs * Real.sin θ with hb
  have hb0 : 0 ≤ b := by positivity
  have hbR : b ≤ Rs := by rw [hb]; nlinarith
  have haR : a ≤ Rs := by rw [ha]; nlinarith
  have ha0 : 0 ≤ a := by positivity
  rw [norm_sliceArc_eq, div_le_iff₀ hgpos, ofReal_mul_exp_mul_I, norm_xiSliceProduct_eq, hg]
  have hE0 : 0 ≤ 4 + B := by linarith
  by_cases hin : 3 * R / 4 ≤ a
  · have hpair := h.norm_xi_pair_le hR hR16 ht hB hRs1 hRs5 hin haR hb0 hbR
    refine hpair.trans ?_
    rw [mul_comm (Real.exp _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have h1 : (a - Rs) * Real.log ‖z₀ / 2‖ ≤ -(Rs * (1 - Real.cos θ)) * X := by
      have e : a - Rs = -(Rs * (1 - Real.cos θ)) := by rw [ha]; ring
      rw [e]
      have : 0 ≤ Rs * (1 - Real.cos θ) := mul_nonneg hRs0.le (by linarith)
      nlinarith
    have h2 : (Rs - a) + b ≤ 2 * (Rs * θ) := by
      have hc : 1 - Real.cos θ ≤ θ := by
        have := Real.one_sub_sq_div_two_le_cos (x := θ)
        have hθ2 : θ ^ 2 / 2 ≤ θ := by
          have : θ ≤ 2 := by linarith [Real.pi_lt_d2]
          nlinarith
        linarith
      have e : Rs - a = Rs * (1 - Real.cos θ) := by rw [ha]; ring
      rw [e, hb]
      have := mul_le_mul_of_nonneg_left hc hRs0.le
      have := mul_le_mul_of_nonneg_left hsinθ hRs0.le
      linarith
    have h3 : (4 + B) * (2 * ((Rs - a) + b)) ≤ (4 + B) * (4 * (Rs * θ)) := by
      apply mul_le_mul_of_nonneg_left _ hE0; linarith
    have := arc_exponent_inbox hRs0 hθ₁ hθ hθπ hX0 hsmall
    linarith
  · push Not at hin
    have hy : ∀ c : ℝ, |c| ≤ Rs → ‖xi (((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖ ≤
        ‖xi (((1 / 2 + 3 * R / 4 : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖ := by
      intro c hc
      refine norm_xi_half_add_le_of_zeros ha0 hin.le (h.nearLine_zero_condition hR ?_)
      rw [show t + c - t = c by ring]; linarith
    have hp := hy b (by rw [abs_of_nonneg hb0]; exact hbR)
    have hm := hy (-b) (by rw [abs_neg, abs_of_nonneg hb0]; exact hbR)
    rw [← sub_eq_add_neg] at hm
    have hpair := h.norm_xi_pair_le hR hR16 ht hB hRs1 hRs5 le_rfl (by linarith) hb0 hbR
    refine (mul_le_mul hp hm (norm_nonneg _) (norm_nonneg _)).trans (hpair.trans ?_)
    rw [mul_comm (Real.exp _)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have h1 : (3 * R / 4 - Rs) * Real.log ‖z₀ / 2‖ ≤ -(Rs / 4) * X := by
      have hle : 3 * R / 4 - Rs ≤ -(Rs / 4) := by linarith
      have h0 : 3 * R / 4 - Rs ≤ 0 := by linarith
      have := mul_le_mul_of_nonpos_left hXz h0
      nlinarith
    have h2 : (4 + B) * (2 * ((Rs - 3 * R / 4) + b)) ≤ (4 + B) * (4 * Rs) := by
      apply mul_le_mul_of_nonneg_left _ hE0; linarith
    have := arc_exponent_nearLine hRs0 hθ₁ hθ₁1 hX0 hsmall
    linarith

end ZetaLogDerivScaleData

end RHTower
