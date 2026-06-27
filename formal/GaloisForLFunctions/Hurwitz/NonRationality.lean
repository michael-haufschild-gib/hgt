/-
# `n^{-s}` is not a polynomial ratio (the Hurwitz N=2 non-rationality obstruction)

The N=2 Hurwitz descent ends at: `q(-n)·R_{n,0}(0) + l₂(-n) = 0` with `R_{n,0}(0) = ζ(s) + η·H_n^{(s)}`,
whose finite difference is `η·n^{-s}` (`hzeta_neg_nat_diff`). If the quadratic coefficient `q` were
nonzero, `R_{n,0}(0)` would be rational in `n`, so `η·n^{-s}` would be a rational finite difference —
itself rational. This file rules that out **in the modulus regime** `Re s ∉ ℤ`: a polynomial `p`
evaluated along `ℕ` has `‖p(n)‖ ∼ ‖lead p‖·n^{deg p}` (an *integer* power), while `‖n^{-s}‖ = n^{-Re s}`;
matching forces `Re s ∈ ℤ`.

The complementary regime `Re s ∈ ℤ ∧ Im s ≠ 0` needs the oscillation of `n^{i·Im s}` (handled
separately). Together they give the full `s ∉ ℤ` obstruction.
-/
import GaloisForLFunctions.U0.PolyAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Polynomial Filter Topology

namespace HurwitzNonRat

/-- **Norm asymptotic of a polynomial evaluated along `ℕ`.** `‖p(n)‖ / n^{deg p} → ‖lead p‖`. -/
theorem tendsto_norm_eval_div_pow (p : ℂ[X]) :
    Tendsto (fun n : ℕ => ‖p.eval (n : ℂ)‖ / (n : ℝ) ^ p.natDegree) atTop (𝓝 ‖p.leadingCoeff‖) := by
  have hR : Tendsto (fun t : ℝ => ‖p.eval (t : ℂ)‖ / t ^ p.natDegree) atTop (𝓝 ‖p.leadingCoeff‖) := by
    refine ((continuous_norm.tendsto _).comp
      (PolyAsymptotics.tendsto_eval_div_pow_natDegree p)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Function.comp_apply, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  refine (hR.comp tendsto_natCast_atTop_atTop).congr (fun n => ?_)
  simp only [Function.comp_apply, Complex.ofReal_natCast]

/-- **Complex asymptotic of a polynomial evaluated along `ℕ`.** `p(n) / n^{deg p} → lead p`. -/
theorem tendsto_eval_div_pow_nat (p : ℂ[X]) :
    Tendsto (fun n : ℕ => p.eval (n : ℂ) / (n : ℂ) ^ p.natDegree) atTop (𝓝 p.leadingCoeff) := by
  refine ((PolyAsymptotics.tendsto_eval_div_pow_natDegree p).comp
    tendsto_natCast_atTop_atTop).congr (fun n => ?_)
  simp only [Function.comp_apply, Complex.ofReal_natCast]

/-- If `n^a → c > 0` (real `rpow`), the exponent `a` is `0`: positive exponent blows up, negative
exponent decays to `0`. -/
theorem exponent_zero_of_tendsto_pos {a c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop (𝓝 c)) : a = 0 := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · exfalso
    have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := -a) (by linarith)).comp tendsto_natCast_atTop_atTop
      simpa [neg_neg] using this
    have hc0 : c = 0 := tendsto_nhds_unique h h0
    rw [hc0] at hc; exact lt_irrefl 0 hc
  · exact ha
  · exfalso
    have hinf : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop atTop :=
      (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
    exact not_tendsto_nhds_of_tendsto_atTop hinf c h

/-- **Modulus non-rationality (`Re s ∉ ℤ`).** If `n^{-s}·denom(n) = num(n)` for all large `n` (with
`num, denom ≠ 0`), then `Re s = deg denom − deg num ∈ ℤ`. Hence for `Re s ∉ ℤ` no such polynomial
relation exists — the Hurwitz N=2 obstruction in the generic modulus regime. -/
theorem re_int_of_eventually_cpow_polyRatio {s : ℂ} {num denom : ℂ[X]}
    (hnum : num ≠ 0) (hdenom : denom ≠ 0)
    (h : ∀ᶠ n : ℕ in atTop, (n : ℂ) ^ (-s) * denom.eval (n : ℂ) = num.eval (n : ℂ)) :
    s.re = (denom.natDegree : ℝ) - num.natDegree := by
  have hlnum : ‖num.leadingCoeff‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact leadingCoeff_ne_zero.mpr hnum
  have hldenom : (0 : ℝ) < ‖denom.leadingCoeff‖ := by
    rw [norm_pos_iff]; exact leadingCoeff_ne_zero.mpr hdenom
  -- A(n) = ‖num n‖/n^degnum → ‖lead num‖ ;  B(n) = ‖denom n‖/n^degdenom → ‖lead denom‖
  have hA := tendsto_norm_eval_div_pow num
  have hB := tendsto_norm_eval_div_pow denom
  -- the ratio A/B tends to ‖lead num‖/‖lead denom‖ > 0
  have hquot : Tendsto (fun n : ℕ => (‖num.eval (n : ℂ)‖ / (n : ℝ) ^ num.natDegree)
      / (‖denom.eval (n : ℂ)‖ / (n : ℝ) ^ denom.natDegree)) atTop
      (𝓝 (‖num.leadingCoeff‖ / ‖denom.leadingCoeff‖)) := hA.div hB (ne_of_gt hldenom)
  -- `denom(n) ≠ 0` for large `n` (its norm tends to a positive limit)
  have hBne : ∀ᶠ n : ℕ in atTop, denom.eval (n : ℂ) ≠ 0 := by
    filter_upwards [hB.eventually (eventually_gt_nhds hldenom)] with n hn hc
    rw [hc, norm_zero, zero_div] at hn; exact lt_irrefl 0 hn
  set a : ℝ := -s.re + ((denom.natDegree : ℝ) - num.natDegree) with ha
  have hpos : (0 : ℝ) < ‖num.leadingCoeff‖ / ‖denom.leadingCoeff‖ :=
    div_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hlnum)) hldenom
  -- on the tail the ratio equals `n^a`
  have heq : (fun n : ℕ => (‖num.eval (n : ℂ)‖ / (n : ℝ) ^ num.natDegree)
        / (‖denom.eval (n : ℂ)‖ / (n : ℝ) ^ denom.natDegree)) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) := by
    filter_upwards [h, eventually_gt_atTop 0, hBne] with n hn hn0 hBn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hdne : ‖denom.eval (n : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hBn
    have hcpow : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
      rw [← Complex.ofReal_natCast n, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.neg_re]
    have hnorm : (n : ℝ) ^ (-s.re) * ‖denom.eval (n : ℂ)‖ = ‖num.eval (n : ℂ)‖ := by
      have h2 := congrArg norm hn
      rwa [norm_mul, hcpow] at h2
    have hratio : ‖num.eval (n : ℂ)‖ / ‖denom.eval (n : ℂ)‖ = (n : ℝ) ^ (-s.re) := by
      rw [← hnorm, mul_div_assoc, div_self hdne, mul_one]
    calc (‖num.eval (n : ℂ)‖ / (n : ℝ) ^ num.natDegree)
            / (‖denom.eval (n : ℂ)‖ / (n : ℝ) ^ denom.natDegree)
        = (‖num.eval (n : ℂ)‖ / ‖denom.eval (n : ℂ)‖)
            * ((n : ℝ) ^ denom.natDegree / (n : ℝ) ^ num.natDegree) := by
          field_simp
      _ = (n : ℝ) ^ (-s.re)
            * ((n : ℝ) ^ (denom.natDegree : ℝ) / (n : ℝ) ^ (num.natDegree : ℝ)) := by
          rw [hratio, Real.rpow_natCast, Real.rpow_natCast]
      _ = (n : ℝ) ^ a := by
          rw [← Real.rpow_sub hnpos, ← Real.rpow_add hnpos]
  have hfinal : Tendsto (fun n : ℕ => (n : ℝ) ^ a) atTop
      (𝓝 (‖num.leadingCoeff‖ / ‖denom.leadingCoeff‖)) := hquot.congr' heq
  have := exponent_zero_of_tendsto_pos hpos hfinal
  rw [ha] at this; linarith

/-- **Number-theory crux of the oscillation case:** `3^a = 2^b` (naturals) forces `a = 0` (else
`3 ∣ 2^b`, impossible). Hence also `b = 0`. With the `Im s ≠ 0` oscillation argument
(`τ log 2, τ log 3 ∈ 2πℤ` ⟹ `3^a = 2^b`), this completes the non-rationality obstruction for the
`Re s ∈ ℤ` regime. -/
theorem eq_zero_of_three_pow_eq_two_pow {a b : ℕ} (h : (3 : ℕ) ^ a = 2 ^ b) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    by_contra ha
    have h3 : (3 : ℕ) ∣ 2 ^ b := h ▸ dvd_pow_self 3 ha
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  subst ha
  refine ⟨rfl, ?_⟩
  simpa using h.symm

/-- **`b·log 2 = a·log 3` (integers) forces `a = 0`.** Take absolute values: `|b|·log2 = |a|·log3`,
exponentiate to `2^|b| = 3^|a|`, then `eq_zero_of_three_pow_eq_two_pow`. (Equivalently: `log 2 / log 3`
is irrational.) The algebraic heart of the oscillation case. -/
theorem eq_zero_of_log_eq {a b : ℤ} (h : (b : ℝ) * Real.log 2 = (a : ℝ) * Real.log 3) : a = 0 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have habs : (b.natAbs : ℝ) * Real.log 2 = (a.natAbs : ℝ) * Real.log 3 := by
    have h1 := congrArg abs h
    rw [abs_mul, abs_mul, abs_of_pos hlog2, abs_of_pos hlog3] at h1
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
    exact h1
  have hexp : (2 : ℝ) ^ b.natAbs = (3 : ℝ) ^ a.natAbs := by
    have he : Real.exp ((b.natAbs : ℝ) * Real.log 2) = Real.exp ((a.natAbs : ℝ) * Real.log 3) := by
      rw [habs]
    rwa [Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by norm_num),
      Real.exp_log (by norm_num)] at he
  have hnat : (3 : ℕ) ^ a.natAbs = (2 : ℕ) ^ b.natAbs := by exact_mod_cast hexp.symm
  have := (eq_zero_of_three_pow_eq_two_pow hnat).1
  omega

/-- **`e^{iτ·log n}` does not converge for `τ ≠ 0`** (the oscillation obstruction). If it tended to `c`,
then `|c| = 1` and, on the subsequences `n ↦ 2n, 3n`, `e^{iτ log 2} = e^{iτ log 3} = 1`, giving
`τ log2 = 2π a`, `τ log3 = 2π b` (`a,b ∈ ℤ`); cross-multiplying, `b log2 = a log3`, so `a = 0`
(`eq_zero_of_log_eq`), whence `τ log2 = 0` and `τ = 0`. -/
theorem not_tendsto_cexp_I_mul_log {τ : ℝ} (hτ : τ ≠ 0) {c : ℂ}
    (h : Tendsto (fun n : ℕ => Complex.exp ((τ : ℂ) * (Real.log n : ℂ) * Complex.I)) atTop (𝓝 c)) :
    False := by
  have hc1 : ‖c‖ = 1 := by
    refine tendsto_nhds_unique ((continuous_norm.tendsto c).comp h) (tendsto_const_nhds.congr' ?_)
    filter_upwards with n
    rw [Function.comp_apply, ← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I]
  have hcne : c ≠ 0 := fun hc => by rw [hc, norm_zero] at hc1; norm_num at hc1
  have hfac : ∀ q : ℕ, 0 < q →
      Complex.exp ((τ : ℂ) * (Real.log q : ℂ) * Complex.I) = 1 := by
    intro q hq
    have hqto : Tendsto (fun n : ℕ => q * n) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hq) tendsto_id
    have hsub := h.comp hqto
    have hsplit : Tendsto (fun n : ℕ =>
        Complex.exp ((τ : ℂ) * (Real.log q : ℂ) * Complex.I)
          * Complex.exp ((τ : ℂ) * (Real.log n : ℂ) * Complex.I)) atTop
        (𝓝 (Complex.exp ((τ : ℂ) * (Real.log q : ℂ) * Complex.I) * c)) := tendsto_const_nhds.mul h
    have hcong : Tendsto (fun n : ℕ =>
        Complex.exp ((τ : ℂ) * (Real.log q : ℂ) * Complex.I)
          * Complex.exp ((τ : ℂ) * (Real.log n : ℂ) * Complex.I)) atTop (𝓝 c) := by
      refine hsub.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [Function.comp_apply, ← Complex.exp_add,
        show ((q * n : ℕ) : ℝ) = (q : ℝ) * n from by push_cast; ring,
        Real.log_mul (by positivity) (by positivity)]
      push_cast; ring_nf
    have : Complex.exp ((τ : ℂ) * (Real.log q : ℂ) * Complex.I) * c = c :=
      tendsto_nhds_unique hsplit hcong
    exact mul_right_cancel₀ hcne (by rw [this, one_mul])
  obtain ⟨a, ha⟩ := Complex.exp_eq_one_iff.mp (hfac 2 (by norm_num))
  obtain ⟨b, hb⟩ := Complex.exp_eq_one_iff.mp (hfac 3 (by norm_num))
  have hreal : ∀ (q : ℕ) (m : ℤ),
      (τ : ℂ) * (Real.log q : ℂ) * Complex.I = (m : ℂ) * (2 * ↑Real.pi * Complex.I)
      → τ * Real.log q = 2 * Real.pi * m := by
    intro q m hqm
    have hcancel : (τ : ℂ) * (Real.log q : ℂ) = (m : ℂ) * (2 * ↑Real.pi) :=
      mul_right_cancel₀ Complex.I_ne_zero (by rw [hqm]; ring)
    have h2 : ((τ * Real.log q : ℝ) : ℂ) = ((2 * Real.pi * m : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul, hcancel]; push_cast; ring
    exact_mod_cast h2
  have ha2 : τ * Real.log 2 = 2 * Real.pi * a := by
    have := hreal 2 a ha; simpa using this
  have hb3 : τ * Real.log 3 = 2 * Real.pi * b := by
    have := hreal 3 b hb; simpa using this
  have hcross : (b : ℝ) * Real.log 2 = (a : ℝ) * Real.log 3 := by
    have e : τ * Real.log 2 * (Real.log 3) = τ * Real.log 3 * (Real.log 2) := by ring
    rw [ha2, hb3] at e
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    nlinarith [e, hπ]
  have hazero : a = 0 := eq_zero_of_log_eq hcross
  rw [hazero] at ha2
  simp only [Int.cast_zero, mul_zero] at ha2
  have : τ = 0 := by
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rcases mul_eq_zero.mp ha2 with h | h
    · exact h
    · exact absurd h (ne_of_gt hlog2)
  exact hτ this

/-- **Non-rationality for all `s ∉ ℤ` (spine form).** `n^{-s}` is not eventually a polynomial ratio
`num/denom` when `s ∉ ℤ`: the modulus case forces `Re s = deg denom − deg num ∈ ℤ`, so `Im s ≠ 0`; the
ratio `→ lead num / lead denom` (a constant) while equalling the oscillating `e^{-i·Im s·log n}`,
contradicting `not_tendsto_cexp_I_mul_log`. The obstruction the Hurwitz N=2 row descent needs. -/
theorem not_eventually_cpow_polyRatio {s : ℂ} (hs : ∀ k : ℤ, s ≠ (k : ℂ))
    {num denom : ℂ[X]} (hnum : num ≠ 0) (hdenom : denom ≠ 0)
    (h : ∀ᶠ n : ℕ in atTop, (n : ℂ) ^ (-s) * denom.eval (n : ℂ) = num.eval (n : ℂ)) : False := by
  have hre : s.re = (denom.natDegree : ℝ) - num.natDegree :=
    re_int_of_eventually_cpow_polyRatio hnum hdenom h
  have hims : s.im ≠ 0 := by
    intro him
    apply hs ((denom.natDegree : ℤ) - num.natDegree)
    apply Complex.ext
    · simp only [Complex.intCast_re]; rw [hre]; push_cast; ring
    · simp only [Complex.intCast_im]; exact him
  have hldne : denom.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hdenom
  have hquot := (tendsto_eval_div_pow_nat num).div (tendsto_eval_div_pow_nat denom) hldne
  have hdenne : ∀ᶠ n : ℕ in atTop, denom.eval (n : ℂ) ≠ 0 := by
    filter_upwards [(tendsto_eval_div_pow_nat denom).eventually_ne hldne] with n hn hc
    apply hn; rw [hc, zero_div]
  have heq : (fun n : ℕ => num.eval (n : ℂ) / (n : ℂ) ^ num.natDegree
        / (denom.eval (n : ℂ) / (n : ℂ) ^ denom.natDegree)) =ᶠ[atTop]
      (fun n : ℕ => Complex.exp (((-s.im : ℝ) : ℂ) * (Real.log n : ℂ) * Complex.I)) := by
    filter_upwards [h, hdenne, eventually_gt_atTop 0] with n hn hdne hn0
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
    have hND : num.eval (n : ℂ) / denom.eval (n : ℂ) = (n : ℂ) ^ (-s) := by
      rw [← hn, mul_div_assoc, div_self hdne, mul_one]
    have hexp : -s + ((denom.natDegree : ℂ) - num.natDegree) = ((-s.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.neg_re, Complex.sub_re, Complex.natCast_re,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, mul_one, sub_zero]
        rw [hre]; ring
      · simp only [Complex.add_im, Complex.neg_im, Complex.sub_im, Complex.natCast_im,
          Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, mul_one, add_zero, sub_zero]
    calc num.eval (n : ℂ) / (n : ℂ) ^ num.natDegree
            / (denom.eval (n : ℂ) / (n : ℂ) ^ denom.natDegree)
        = (num.eval (n : ℂ) / denom.eval (n : ℂ))
            * ((n : ℂ) ^ denom.natDegree / (n : ℂ) ^ num.natDegree) := by field_simp
      _ = (n : ℂ) ^ (-s) * ((n : ℂ) ^ (denom.natDegree : ℂ) / (n : ℂ) ^ (num.natDegree : ℂ)) := by
          rw [hND]; simp only [Complex.cpow_natCast]
      _ = (n : ℂ) ^ (-s + ((denom.natDegree : ℂ) - num.natDegree)) := by
          rw [← Complex.cpow_sub _ _ hnc, ← Complex.cpow_add _ _ hnc]
      _ = Complex.exp (((-s.im : ℝ) : ℂ) * (Real.log n : ℂ) * Complex.I) := by
          rw [hexp, Complex.cpow_def_of_ne_zero hnc, ← Complex.ofReal_natCast n,
            ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ (n : ℝ))]
          congr 1; push_cast; ring
  exact not_tendsto_cexp_I_mul_log (neg_ne_zero.mpr hims) (hquot.congr' heq)

end HurwitzNonRat
