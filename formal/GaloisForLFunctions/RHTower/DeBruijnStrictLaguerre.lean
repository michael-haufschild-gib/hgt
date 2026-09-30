import GaloisForLFunctions.RHTower.DeBruijnNewmanCollisionCriterion

/-!
# The strict first Laguerre inequality along the de Bruijn–Newman flow

For `t > newmanConstant` the first Laguerre expression of `H_t` is strictly positive on the real
line (`laguerre_pos_of_newmanConstant_lt`):

`H_t'(x)² − H_t(x) H_t''(x) > 0`   for every real `x`.

At a zero this is simplicity (Csordas–Smith–Varga). Off the zeros, all zeros being real, the Hadamard
product gives `|H(x + iy)|² ≥ H(x)² (1 + y²/(x₀ − x)²)` for a real zero `x₀`, while the third-order
Taylor expansion gives `|H(x + iy)|² = H(x)² + y²(H'² − HH'')(x) + O(|y|³)`; hence
`H'² − HH'' ≥ H(x)²/(x₀ − x)² > 0`.

If RH fails, the last collision at `t = Λ > 0` is a real double zero of `H_Λ`, where the Laguerre
expression vanishes. Therefore

`RH ⇔` for every `t > 0` the strict first Laguerre inequality holds on `ℝ`
(`riemannHypothesis_iff_forall_laguerre_pos`),

whereas the non-strict inequality at `t = 0` alone is weaker than RH.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.EntireZeroDivisor

namespace RHTower.DeBruijn

noncomputable section

/-! ## Reality on the real axis -/

theorem riemannHeat_ofReal_im {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : (riemannHeat t x).im = 0 := by
  have h := riemannHeat_conj ht (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

theorem im_deriv_eq_zero_of_real {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hreal : ∀ r : ℝ, (f r).im = 0) (x : ℝ) : (deriv f x).im = 0 := by
  have h1 : HasDerivAt (fun r : ℝ => f r) (deriv f x) x := (hf x).hasDerivAt.comp_ofReal
  have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h1
  have h3 : HasDerivAt (fun r : ℝ => Complex.imCLM (f r)) 0 x := by
    have : (fun r : ℝ => Complex.imCLM (f r)) = fun _ => (0 : ℝ) := by
      funext r; simpa using hreal r
    rw [this]; exact hasDerivAt_const x 0
  have := h2.unique h3
  simpa using this

theorem deriv_riemannHeat_ofReal_im {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    (deriv (riemannHeat t) x).im = 0 :=
  im_deriv_eq_zero_of_real (differentiable_riemannHeat ht) (riemannHeat_ofReal_im ht) x

theorem deriv_deriv_riemannHeat_ofReal_im {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    (deriv (deriv (riemannHeat t)) x).im = 0 := by
  have hd : Differentiable ℂ (deriv (riemannHeat t)) := by
    have := differentiable_iteratedDeriv_riemannHeat ht 1
    simpa [iteratedDeriv_one] using this
  exact im_deriv_eq_zero_of_real hd (deriv_riemannHeat_ofReal_im ht) x

/-! ## The Hadamard lower bound for vertical growth -/

/-- For a real-rooted `H_t` and a real zero `x₀ ≠ x`: `‖H(x + iy)‖² ≥ ‖H(x)‖²(1 + y²/(x₀ − x)²)`. -/
theorem sq_norm_riemannHeat_vertical_ge {t : ℝ} (ht : 0 ≤ t)
    (hreal : ∀ z, riemannHeat t z = 0 → z.im = 0) {x x₀ : ℝ} (hx : riemannHeat t x ≠ 0)
    (hx₀ : riemannHeat t x₀ = 0) (y : ℝ) :
    ‖riemannHeat t x‖ ^ 2 * (1 + y ^ 2 / (x₀ - x) ^ 2) ≤
      ‖riemannHeat t ((x : ℂ) + y * I)‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq ht).exists_envelope
  have hf := riemannHeat_analytic ht
  have hf0 := riemannHeat_zero_ne ht
  have heven := riemannHeat_neg ht
  have hsum := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hane := zeroCopyPoint_ne_zero hf hf0
  have hxx₀ : x ≠ x₀ := by intro h; rw [h] at hx; exact hx hx₀
  have hd : 0 < (x₀ - x) ^ 2 := by
    have : x₀ - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxx₀); positivity
  -- off the real axis `H_t` has no zeros, so the vertical point is not a zero
  set w := (x : ℂ) + y * I
  by_cases hy : y = 0
  · subst hy; simp [w]
  have hw : riemannHeat t w ≠ 0 := by
    intro h
    have := hreal w h
    simp [w] at this
    exact hy this
  rw [norm_eq_exp_tsum hC hf hf0 heven hbound hw, norm_eq_exp_tsum hC hf hf0 heven hbound hx]
  have hsu := summable_log_norm_weierstrassE1 hsum (x : ℂ)
  have hsv := summable_log_norm_weierstrassE1 hsum w
  set φ : ZeroCopy (riemannHeat t) → ℝ := fun q =>
    Real.log ‖weierstrassE1 (w / zeroCopyPoint (riemannHeat t) q)‖ -
      Real.log ‖weierstrassE1 ((x : ℂ) / zeroCopyPoint (riemannHeat t) q)‖ with hφ
  have hterm : ∀ q, φ q = Real.log (1 + y ^ 2 / ((zeroCopyPoint (riemannHeat t) q).re - x) ^ 2) / 2 := by
    intro q
    set a := zeroCopyPoint (riemannHeat t) q
    have ha0 := hane q
    have haz : riemannHeat t a = 0 := apply_zeroCopyPoint hf q
    have hareal : a.im = 0 := hreal a haz
    have hax : a.re ≠ x := by
      intro h
      apply hx
      rw [← haz]; congr 1; apply Complex.ext <;> simp [hareal, h]
    have hsq : 0 < (a.re - x) ^ 2 := by
      have : a.re - x ≠ 0 := sub_ne_zero.mpr hax; positivity
    have hnorm : ∀ v : ℂ, v.im = y ∨ v.im = 0 → v.re = x →
        ‖weierstrassE1 (v / a)‖ = Real.sqrt ((a.re - x) ^ 2 + v.im ^ 2) / ‖a‖ *
          Real.exp (x * a.re / Complex.normSq a) := by
      intro v _ hvre
      unfold weierstrassE1
      rw [norm_mul, Complex.norm_exp]
      have ha0' : a ≠ 0 := ha0
      have h1 : ‖1 - v / a‖ = ‖a - v‖ / ‖a‖ := by
        rw [show (1 : ℂ) - v / a = (a - v) / a by rw [sub_div, div_self ha0'], norm_div]
      have h2 : (v / a).re = x * a.re / Complex.normSq a := by
        rw [Complex.div_re]; simp [hareal, hvre]
      have h3 : ‖a - v‖ = Real.sqrt ((a.re - x) ^ 2 + v.im ^ 2) := by
        rw [Complex.norm_eq_sqrt_sq_add_sq]; congr 1; simp [hvre, hareal]
      rw [h1, h2, h3]
    have hwv := hnorm w (Or.inl (by simp [w])) (by simp [w])
    have hxv := hnorm (x : ℂ) (Or.inr (by simp)) (by simp)
    simp only [hφ]
    rw [hwv, hxv]
    have hwim : w.im = y := by simp [w]
    rw [hwim, Complex.ofReal_im]
    have hpos1 : 0 < Real.sqrt ((a.re - x) ^ 2 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hpos2 : 0 < Real.sqrt ((a.re - x) ^ 2 + 0 ^ 2) := Real.sqrt_pos.mpr (by simpa using hsq)
    have ha : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity)
      (Real.exp_pos _).ne', Real.log_div hpos1.ne' ha.ne', Real.log_div hpos2.ne' ha.ne',
      Real.log_sqrt (by positivity), Real.log_sqrt (by positivity)]
    have e : (a.re - x) ^ 2 + y ^ 2 = (a.re - x) ^ 2 * (1 + y ^ 2 / (a.re - x) ^ 2) := by
      field_simp
    rw [e, Real.log_mul hsq.ne' (by positivity)]
    simp
    ring
  have hφnn : ∀ q, 0 ≤ φ q := fun q => by
    rw [hterm]; have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + y ^ 2 / ((zeroCopyPoint (riemannHeat t) q).re - x) ^ 2 by
      have : 0 ≤ y ^ 2 / ((zeroCopyPoint (riemannHeat t) q).re - x) ^ 2 := by positivity
      linarith)
    linarith
  obtain ⟨q₀, hq₀⟩ := exists_zeroCopy_of_eq_zero hf hf0 hx₀
  have hsφ : Summable φ := hsv.sub hsu
  have hle := hsφ.le_tsum q₀ (fun j _ => hφnn j)
  rw [hterm, hq₀, Complex.ofReal_re, hsv.tsum_sub hsu] at hle
  set Sw := ∑' q, Real.log ‖weierstrassE1 (w / zeroCopyPoint (riemannHeat t) q)‖
  set Sx := ∑' q, Real.log ‖weierstrassE1 ((x : ℂ) / zeroCopyPoint (riemannHeat t) q)‖
  have hkey : 1 + y ^ 2 / (x₀ - x) ^ 2 ≤ Real.exp (Sw - Sx) ^ 2 := by
    have e2 : Real.exp (Sw - Sx) ^ 2 = Real.exp (2 * (Sw - Sx)) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [e2, ← Real.exp_log (show 0 < 1 + y ^ 2 / (x₀ - x) ^ 2 by positivity)]
    exact Real.exp_le_exp.mpr (by linarith)
  have e1 : Real.exp Sw = Real.exp Sx * Real.exp (Sw - Sx) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1]
  calc (‖riemannHeat t 0‖ * Real.exp Sx) ^ 2 * (1 + y ^ 2 / (x₀ - x) ^ 2)
      ≤ (‖riemannHeat t 0‖ * Real.exp Sx) ^ 2 * Real.exp (Sw - Sx) ^ 2 :=
        mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    _ = (‖riemannHeat t 0‖ * (Real.exp Sx * Real.exp (Sw - Sx))) ^ 2 := by ring

/-! ## The strict Laguerre inequality -/

/-- If `c ≤ L + K y` for all `0 < y ≤ 1` with `K ≥ 0`, then `c ≤ L`. -/
theorem le_of_forall_le_add_mul {c L K : ℝ} (hK : 0 ≤ K)
    (h : ∀ y : ℝ, 0 < y → y ≤ 1 → c ≤ L + K * y) : c ≤ L := by
  by_contra hlt
  rw [not_le] at hlt
  have hδ : 0 < c - L := by linarith
  have hy : 0 < min 1 ((c - L) / (K + 1)) := lt_min one_pos (by positivity)
  have h1 := h _ hy (min_le_left _ _)
  have h2 : K * min 1 ((c - L) / (K + 1)) ≤ K * ((c - L) / (K + 1)) :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hK
  have h3 : K * ((c - L) / (K + 1)) < c - L := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  linarith

/-- **Quantitative strict Laguerre inequality.** If all zeros of `H_t` are real, `x` is not a
zero and `x₀` is a real zero, then `H_t(x)² / (x₀ − x)² ≤ H_t'(x)² − H_t(x) H_t''(x)`. -/
theorem sq_div_le_laguerre {t : ℝ} (ht : 0 ≤ t)
    (hreal : ∀ z, riemannHeat t z = 0 → z.im = 0) {x x₀ : ℝ} (hx : riemannHeat t x ≠ 0)
    (hx₀ : riemannHeat t x₀ = 0) :
    (riemannHeat t x).re ^ 2 / (x₀ - x) ^ 2 ≤
      (deriv (riemannHeat t) x ^ 2 - riemannHeat t x * deriv (deriv (riemannHeat t)) x).re := by
  set h0 := (riemannHeat t x).re
  set h1 := (deriv (riemannHeat t) x).re
  set h2 := (deriv (deriv (riemannHeat t)) x).re
  have e0 : riemannHeat t x = h0 := Complex.ext (by simp [h0]) (by simp [riemannHeat_ofReal_im ht])
  have e1 : deriv (riemannHeat t) x = h1 :=
    Complex.ext (by simp [h1]) (by simp [deriv_riemannHeat_ofReal_im ht])
  have e2 : deriv (deriv (riemannHeat t)) x = h2 :=
    Complex.ext (by simp [h2]) (by simp [deriv_deriv_riemannHeat_ofReal_im ht])
  have hL : (deriv (riemannHeat t) x ^ 2 - riemannHeat t x * deriv (deriv (riemannHeat t)) x).re =
      h1 ^ 2 - h0 * h2 := by
    rw [e0, e1, e2]; simp [sq]
  rw [hL]
  have hxx₀ : x ≠ x₀ := by intro h; rw [h] at hx; exact hx hx₀
  have hd : 0 < (x₀ - x) ^ 2 := by
    have : x₀ - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxx₀); positivity
  set M := ∫ u, |u| ^ 3 * ‖heatWeight t u‖ * Real.exp ((|((x : ℂ)).im| + 1) * |u|)
  have hM : 0 ≤ M := MeasureTheory.integral_nonneg fun u => by positivity
  set B := |h0| + |h1| + |h2|
  refine le_of_forall_le_add_mul (K := h2 ^ 2 / 4 + 2 * B * M + M ^ 2)
    (by positivity) fun y hy hy1 => ?_
  have hlow := sq_norm_riemannHeat_vertical_ge ht hreal hx hx₀ y
  have hT := norm_riemannHeat_taylor_three_le ht (z₀ := (x : ℂ)) (z := (x : ℂ) + y * I)
    (by simp [abs_of_pos hy, hy1])
  rw [show (x : ℂ) + y * I - x = y * I by ring, e0, e1, e2] at hT
  have hyn : ‖(y : ℂ) * I‖ = y := by simp [abs_of_pos hy]
  rw [hyn] at hT
  set P : ℂ := ((h0 - h2 * y ^ 2 / 2 : ℝ) : ℂ) + ((h1 * y : ℝ) : ℂ) * I
  have hPeq : (h0 : ℂ) + h1 * (y * I) + h2 / 2 * (y * I) ^ 2 = P := by
    simp only [P]; push_cast; ring_nf; rw [I_sq]; ring
  have hsplit : riemannHeat t ((x : ℂ) + y * I) = P +
      (riemannHeat t ((x : ℂ) + y * I) - h0 - h1 * (y * I) - h2 / 2 * (y * I) ^ 2) := by
    rw [← hPeq]; ring
  have hPn : ‖P‖ ^ 2 = (h0 - h2 * y ^ 2 / 2) ^ 2 + (h1 * y) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hPB : ‖P‖ ≤ B := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have hy2 : y ^ 2 ≤ 1 := by nlinarith
    have a1 : |h0 - h2 * y ^ 2 / 2| ≤ |h0| + |h2| := by
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg y), abs_two]
      nlinarith [abs_nonneg h2]
    have a2 : |h1 * y| ≤ |h1| := by
      rw [abs_mul, abs_of_pos hy]; nlinarith [abs_nonneg h1]
    simp only [B]; linarith
  have hupper : ‖riemannHeat t ((x : ℂ) + y * I)‖ ≤ ‖P‖ + M * y ^ 3 := by
    rw [hsplit]; exact (norm_add_le _ _).trans (add_le_add le_rfl hT)
  have hn0 : ‖riemannHeat t x‖ ^ 2 = h0 ^ 2 := by rw [e0, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hn0] at hlow
  have hsq : ‖riemannHeat t ((x : ℂ) + y * I)‖ ^ 2 ≤ (‖P‖ + M * y ^ 3) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hupper 2
  have hy3 : y ^ 3 ≤ y ^ 2 * y := by ring_nf; rfl
  have hy6 : y ^ 6 ≤ y ^ 3 := pow_le_pow_of_le_one hy.le hy1 (by norm_num)
  have hy4 : y ^ 4 ≤ y ^ 3 := pow_le_pow_of_le_one hy.le hy1 (by norm_num)
  -- `h0² y²/d² ≤ y² L + y³ K`
  have hmain : h0 ^ 2 * (y ^ 2 / (x₀ - x) ^ 2) ≤ y ^ 2 * (h1 ^ 2 - h0 * h2) +
      y ^ 3 * (h2 ^ 2 / 4 + 2 * B * M + M ^ 2) := by
    have hPB' : ‖P‖ * (M * y ^ 3) ≤ B * (M * y ^ 3) :=
      mul_le_mul_of_nonneg_right hPB (by positivity)
    have hM6 : M ^ 2 * y ^ 6 ≤ M ^ 2 * y ^ 3 := mul_le_mul_of_nonneg_left hy6 (sq_nonneg M)
    have hh4 : h2 ^ 2 * y ^ 4 ≤ h2 ^ 2 * y ^ 3 := mul_le_mul_of_nonneg_left hy4 (sq_nonneg h2)
    have hexp : (‖P‖ + M * y ^ 3) ^ 2 = ‖P‖ ^ 2 + 2 * (‖P‖ * (M * y ^ 3)) + M ^ 2 * y ^ 6 := by ring
    rw [hexp, hPn] at hsq
    nlinarith
  have hy2 : 0 < y ^ 2 := by positivity
  have : h0 ^ 2 / (x₀ - x) ^ 2 * y ^ 2 ≤
      (h1 ^ 2 - h0 * h2 + (h2 ^ 2 / 4 + 2 * B * M + M ^ 2) * y) * y ^ 2 := by
    have l1 : h0 ^ 2 / (x₀ - x) ^ 2 * y ^ 2 = h0 ^ 2 * (y ^ 2 / (x₀ - x) ^ 2) := by ring
    rw [l1]; linarith
  exact le_of_mul_le_mul_right this hy2

/-- **Strict first Laguerre inequality past the de Bruijn–Newman constant.** For
`t > newmanConstant`, `H_t'(x)² − H_t(x) H_t''(x) > 0` at every real `x`. -/
theorem laguerre_pos_of_newmanConstant_lt {t : ℝ} (ht : newmanConstant < t) (x : ℝ) :
    0 < (deriv (riemannHeat t) x ^ 2 - riemannHeat t x * deriv (deriv (riemannHeat t)) x).re := by
  have ht0 : 0 < t := lt_of_le_of_lt newmanConstant_nonneg ht
  have hmem := (mem_realRootedTimes_iff ht0.le).mpr ht.le
  by_cases hx : riemannHeat t x = 0
  · have hd := deriv_riemannHeat_ne_zero_of_newmanConstant_lt ht hx
    have e1 : deriv (riemannHeat t) x = (deriv (riemannHeat t) x).re :=
      Complex.ext (by simp) (by simp [deriv_riemannHeat_ofReal_im ht0.le])
    rw [hx, zero_mul, sub_zero, e1, ← Complex.ofReal_pow, Complex.ofReal_re]
    have : (deriv (riemannHeat t) x).re ≠ 0 := by
      intro h; apply hd; rw [e1, h, Complex.ofReal_zero]
    positivity
  · obtain ⟨x₀, hx₀⟩ := exists_riemannHeat_real_zero ht0
    have hle := sq_div_le_laguerre ht0.le hmem.2 hx hx₀
    have hxx₀ : x ≠ x₀ := by intro h; rw [h] at hx; exact hx hx₀
    have h0 : (riemannHeat t x).re ≠ 0 := by
      intro h; apply hx
      exact Complex.ext (by simp [h]) (by simp [riemannHeat_ofReal_im ht0.le])
    have hd : x₀ - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxx₀)
    exact lt_of_lt_of_le (by positivity) hle

/-- **RH as the strict Laguerre inequality along the flow.** The Riemann hypothesis holds iff for
every `t > 0` the first Laguerre expression `H_t'² − H_t H_t''` is strictly positive on `ℝ`. -/
theorem riemannHypothesis_iff_forall_laguerre_pos :
    RiemannHypothesis ↔ ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      0 < (deriv (riemannHeat t) x ^ 2 - riemannHeat t x * deriv (deriv (riemannHeat t)) x).re := by
  constructor
  · intro hRH t ht x
    have hΛ := riemannHypothesis_iff_newmanConstant_eq_zero.mp hRH
    exact laguerre_pos_of_newmanConstant_lt (by rw [hΛ]; exact ht) x
  · intro hpos
    rw [riemannHypothesis_iff_newmanConstant_eq_zero]
    by_contra hne
    have hΛ : 0 < newmanConstant := lt_of_le_of_ne newmanConstant_nonneg (Ne.symm hne)
    obtain ⟨z, hz, hdz⟩ := exists_multiple_zero_of_newmanConstant_pos hΛ
    have hmem := (mem_realRootedTimes_iff hΛ.le).mpr le_rfl
    have hzre : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hmem.2 z hz])
    have := hpos _ hΛ z.re
    rw [← hzre, hz, hdz] at this
    simp at this

end

end RHTower.DeBruijn
