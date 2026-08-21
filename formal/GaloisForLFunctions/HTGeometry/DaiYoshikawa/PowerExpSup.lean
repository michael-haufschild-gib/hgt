import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `sup_{x ≥ 0} xᵐ e^{−x/a}` and Gaussian-decay absorption

Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the Laplacian*
(arXiv:2509.06151v2), uses four explicit extremal constants and never evaluates them:

* `B := sup_{x≥0} x² e^{−x/2}` (Lemma 2.1),
* `B' := sup_{x≥0} x e^{−x/2}` (proof of Proposition 3.5),
* `B'_m := sup_{x≥0} xᵐ e^{−x/16}` (Theorem 2.5),
* `B(n) := sup_{x>0} xⁿ e^{−x/64}` (Lemma 2.7).

All four are instances of one elementary maximum: for `a > 0` the function `x ↦ xᵐ e^{−x/a}` on
`[0,∞)` attains its greatest value `(m a)ᵐ e^{−m}` at `x = m a`.  The proof is not calculus but the
single tangent-line inequality `t ≤ e^{t−1}`, raised to the `m`-th power.

The second half of the file is the way those constants are *used* in the paper — (2.10)–(2.13) and
Lemma 2.7 — namely to trade a negative power of the heat time `s` against half of a Gaussian factor:

```text
s^{−m} e^{−δ²/(c s)}  ≤  (2 m c)ᵐ e^{−m} δ^{−2m} · e^{−δ²/(2 c s)} .
```

Every constant here is explicit, so the resulting estimates are effective.
-/

open Real Set

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-! ## The extremal inequality -/

/-- `t ≤ a · e^{t/a − 1}`: the tangent-line bound for the exponential, rescaled by `a > 0`. -/
theorem le_mul_exp_div_sub_one {a : ℝ} (ha : 0 < a) (t : ℝ) :
    t ≤ a * exp (t / a - 1) := by
  have h : t / a ≤ exp (t / a - 1) := by
    have := Real.add_one_le_exp (t / a - 1)
    linarith
  have h2 := mul_le_mul_of_nonneg_left h ha.le
  rwa [mul_div_cancel₀ _ ha.ne'] at h2

/-- **The extremal inequality.**  For `a > 0`, `m : ℕ` and `x ≥ 0`,
`xᵐ e^{−x/a} ≤ (m a)ᵐ e^{−m}`. -/
theorem pow_mul_exp_neg_div_le (m : ℕ) {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    x ^ m * exp (-(x / a)) ≤ ((m : ℝ) * a) ^ m * exp (-(m : ℝ)) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [pow_zero, one_mul, Nat.cast_zero, neg_zero, exp_zero, mul_one]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hx ha.le))
  · have hma : 0 < (m : ℝ) * a := by positivity
    have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have h1 : x ≤ ((m : ℝ) * a) * exp (x / ((m : ℝ) * a) - 1) := le_mul_exp_div_sub_one hma x
    have h2 : x ^ m ≤ (((m : ℝ) * a) * exp (x / ((m : ℝ) * a) - 1)) ^ m :=
      pow_le_pow_left₀ hx h1 m
    have h3 : (((m : ℝ) * a) * exp (x / ((m : ℝ) * a) - 1)) ^ m
        = ((m : ℝ) * a) ^ m * exp (x / a - (m : ℝ)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 1
      rw [Real.exp_eq_exp]
      field_simp
    rw [h3] at h2
    calc x ^ m * exp (-(x / a))
        ≤ (((m : ℝ) * a) ^ m * exp (x / a - (m : ℝ))) * exp (-(x / a)) :=
          mul_le_mul_of_nonneg_right h2 (exp_nonneg _)
      _ = ((m : ℝ) * a) ^ m * exp (-(m : ℝ)) := by
          rw [mul_assoc, ← Real.exp_add]
          ring_nf

/-- The extremal value is attained at `x = m a`. -/
theorem pow_mul_exp_neg_div_at_max (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ((m : ℝ) * a) ^ m * exp (-(((m : ℝ) * a) / a)) = ((m : ℝ) * a) ^ m * exp (-(m : ℝ)) := by
  rw [mul_div_cancel_right₀ _ ha.ne']

/-- **`sup_{x ≥ 0} xᵐ e^{−x/a} = (m a)ᵐ e^{−m}`, attained.** -/
theorem isGreatest_pow_mul_exp_neg_div (m : ℕ) {a : ℝ} (ha : 0 < a) :
    IsGreatest ((fun x : ℝ => x ^ m * exp (-(x / a))) '' Ici 0)
      (((m : ℝ) * a) ^ m * exp (-(m : ℝ))) := by
  constructor
  · exact ⟨(m : ℝ) * a, mem_Ici.mpr (by positivity), pow_mul_exp_neg_div_at_max m ha⟩
  · rintro y ⟨x, hx, rfl⟩
    exact pow_mul_exp_neg_div_le m ha (mem_Ici.mp hx)

/-! ## The four constants of the paper -/

/-- Dai–Yoshikawa's `B := sup_{x≥0} x² e^{−x/2}`, evaluated: `B = 16 e^{−2}`. -/
theorem isGreatest_sq_exp_neg_half :
    IsGreatest ((fun x : ℝ => x ^ 2 * exp (-(x / 2))) '' Ici 0) (16 * exp (-2)) := by
  have h := isGreatest_pow_mul_exp_neg_div 2 (a := 2) (by norm_num)
  norm_num at h
  exact h

/-- Dai–Yoshikawa's `B' := sup_{x≥0} x e^{−x/2}`, evaluated: `B' = 2 e^{−1}`. -/
theorem isGreatest_id_exp_neg_half :
    IsGreatest ((fun x : ℝ => x * exp (-(x / 2))) '' Ici 0) (2 * exp (-1)) := by
  have h := isGreatest_pow_mul_exp_neg_div 1 (a := 2) (by norm_num)
  norm_num at h
  exact h

/-- Dai–Yoshikawa's `B'_m := sup_{x≥0} xᵐ e^{−x/16}`, evaluated: `B'_m = (16 m)ᵐ e^{−m}`. -/
theorem isGreatest_pow_exp_neg_sixteenth (m : ℕ) :
    IsGreatest ((fun x : ℝ => x ^ m * exp (-(x / 16))) '' Ici 0)
      (((m : ℝ) * 16) ^ m * exp (-(m : ℝ))) :=
  isGreatest_pow_mul_exp_neg_div m (by norm_num)

/-- Dai–Yoshikawa's `B(n) := sup_{x≥0} xⁿ e^{−x/64}`, evaluated: `B(n) = (64 n)ⁿ e^{−n}`. -/
theorem isGreatest_pow_exp_neg_sixtyfourth (n : ℕ) :
    IsGreatest ((fun x : ℝ => x ^ n * exp (-(x / 64))) '' Ici 0)
      (((n : ℝ) * 64) ^ n * exp (-(n : ℝ))) :=
  isGreatest_pow_mul_exp_neg_div n (by norm_num)

/-! ## Gaussian-decay absorption

The way the paper uses these maxima: a negative power of the heat time is absorbed into half of a
Gaussian factor, at the cost of the corresponding negative power of the spatial separation. -/

/-- **Absorption of a negative power of the heat time into half a Gaussian.**

For `c, δ, s > 0` and `m : ℕ`,
`s^{−m} e^{−δ²/(c s)} ≤ (2 m c)ᵐ e^{−m} δ^{−2m} e^{−δ²/(2 c s)}`.

This is (2.10)–(2.13) of Dai–Yoshikawa with `c = 8`: there `s^{-(2n+1)} e^{−δ²/(8s)}` is traded for
`B'_{2n+1} δ^{−2(2n+1)} e^{−δ²/(16 s)}`, and the constant produced here,
`(16(2n+1))^{2n+1} e^{−(2n+1)}`, is exactly their `B'_{2n+1}`. -/
theorem exp_neg_sq_div_div_pow_le (m : ℕ) {c δ s : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hs : 0 < s) :
    exp (-(δ ^ 2 / (c * s))) / s ^ m
      ≤ ((m : ℝ) * (2 * c)) ^ m * exp (-(m : ℝ)) / δ ^ (2 * m)
          * exp (-(δ ^ 2 / (2 * c * s))) := by
  set y : ℝ := δ ^ 2 / s with hy
  have hy0 : 0 ≤ y := by positivity
  have hδm : (0 : ℝ) < δ ^ (2 * m) := by positivity
  have hsm : (0 : ℝ) < s ^ m := by positivity
  have key : y ^ m * exp (-(y / (2 * c))) ≤ ((m : ℝ) * (2 * c)) ^ m * exp (-(m : ℝ)) :=
    pow_mul_exp_neg_div_le m (by positivity) hy0
  have hym : y ^ m = δ ^ (2 * m) / s ^ m := by
    rw [hy, div_pow, ← pow_mul]
  have hstep : exp (-(y / (2 * c))) / s ^ m
      ≤ ((m : ℝ) * (2 * c)) ^ m * exp (-(m : ℝ)) / δ ^ (2 * m) := by
    rw [le_div_iff₀ hδm]
    have hrw : exp (-(y / (2 * c))) / s ^ m * δ ^ (2 * m) = y ^ m * exp (-(y / (2 * c))) := by
      rw [hym]; field_simp
    rw [hrw]
    exact key
  have hsplit : -(δ ^ 2 / (c * s)) = -(y / (2 * c)) + -(δ ^ 2 / (2 * c * s)) := by
    rw [hy]; field_simp; ring
  rw [hsplit, Real.exp_add]
  have hpos : (0 : ℝ) < exp (-(δ ^ 2 / (2 * c * s))) := exp_pos _
  calc exp (-(y / (2 * c))) * exp (-(δ ^ 2 / (2 * c * s))) / s ^ m
      = (exp (-(y / (2 * c))) / s ^ m) * exp (-(δ ^ 2 / (2 * c * s))) := by ring
    _ ≤ (((m : ℝ) * (2 * c)) ^ m * exp (-(m : ℝ)) / δ ^ (2 * m))
          * exp (-(δ ^ 2 / (2 * c * s))) := mul_le_mul_of_nonneg_right hstep hpos.le

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
