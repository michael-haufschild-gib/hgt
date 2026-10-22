import Mathlib

set_option autoImplicit false

/-!
# The exponent algebra of Guth–Maynard Lemma 11.9

After Cauchy–Schwarz over the gcd and Lemmas 11.5, 11.6 at `M = N/d`, the large-gcd sum of
Guth–Maynard (arXiv 2405.20552, (11.3)) is bounded by

`(|W|²N + |W|T + |W|^{5/4}T^{1/2}N)^{1/2} (N|W|⁴ + E T + E^{3/4}|W|T^{1/2}N)^{1/2}`.

For `1 ≤ |W| ≤ 2T`, `|W|² ≤ E ≤ 3|W|³` and `N ≥ T^{3/4}` this is at most
`6 (N|W|³ + N T^{1/4} |W|^{21/8} + E^{1/2}|W|^{1/2}N²)` (`largeGcd_algebra_rpow`).

Proof. With `x = |W|^{1/8}`, `τ = T^{1/4}`, `e = E^{1/4}` every quantity is a monomial, and each of
the nine products in the expansion is at most `3` times the square of one of the three target
terms (`largeGcd_algebra`); the only case split is the paper's `|W| ≤ T^{2/3}` (here `x³ ≤ τ`) for
the product of the two `T^{1/2}` terms.
-/

namespace RHTower.GuthMaynard

/-- `e³ ≤ 3x^{18}` from `e⁴ ≤ 3x^{24}`. -/
theorem cube_le_of_pow_four_le {x e : ℝ} (h : e ^ 4 ≤ 3 * x ^ 24) :
    e ^ 3 ≤ 3 * x ^ 18 := by
  by_contra hc
  have hc' : 3 * x ^ 18 < e ^ 3 := lt_of_not_ge hc
  have h4 : (3 * x ^ 18) ^ 4 < (e ^ 3) ^ 4 := pow_lt_pow_left₀ hc' (by positivity) (by norm_num)
  have h3 : (e ^ 4) ^ 3 ≤ (3 * x ^ 24) ^ 3 := pow_le_pow_left₀ (by positivity) h 3
  have hx72 : 0 ≤ x ^ 72 := by positivity
  rw [show (3 * x ^ 18) ^ 4 = 81 * x ^ 72 by ring, show (e ^ 3) ^ 4 = (e ^ 4) ^ 3 by ring] at h4
  rw [show (3 * x ^ 24) ^ 3 = 27 * x ^ 72 by ring] at h3
  linarith

/-- **The nine products.** For `1 ≤ x`, `1 ≤ τ`, `x⁴ ≤ e`, `e⁴ ≤ 3x^{24}`, `x⁸ ≤ 2τ⁴`, `τ³ ≤ N`:
`(x^{16}N + x⁸τ⁴ + x^{10}τ²N)(x^{32}N + e⁴τ⁴ + e³x⁸τ²N) ≤ 27 (N x^{24} + N τ x^{21} + e²x⁴N²)²`. -/
theorem largeGcd_algebra {x τ e N : ℝ} (hx : 1 ≤ x) (hτ : 1 ≤ τ) (he : x ^ 4 ≤ e)
    (he3 : e ^ 4 ≤ 3 * x ^ 24) (hxτ : x ^ 8 ≤ 2 * τ ^ 4) (hN : τ ^ 3 ≤ N) :
    (x ^ 16 * N + x ^ 8 * τ ^ 4 + x ^ 10 * τ ^ 2 * N) *
        (x ^ 32 * N + e ^ 4 * τ ^ 4 + e ^ 3 * x ^ 8 * τ ^ 2 * N) ≤
      27 * (N * x ^ 24 + N * τ * x ^ 21 + e ^ 2 * x ^ 4 * N ^ 2) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hτ0 : 0 ≤ τ := by linarith
  have hN0 : 0 ≤ N := le_trans (by positivity) hN
  have he0 : 0 ≤ e := le_trans (by positivity) he
  set t₁ := N * x ^ 24
  set t₂ := N * τ * x ^ 21
  set t₃ := e ^ 2 * x ^ 4 * N ^ 2
  have ht₁ : 0 ≤ t₁ := by positivity
  have ht₂ : 0 ≤ t₂ := by positivity
  have ht₃ : 0 ≤ t₃ := by positivity
  -- elementary consequences of the hypotheses
  have hτ2N : τ ^ 2 ≤ N := le_trans (pow_le_pow_right₀ hτ (by norm_num)) hN
  have hτ8N : τ ^ 8 ≤ N ^ 3 := by
    calc τ ^ 8 ≤ τ ^ 9 := pow_le_pow_right₀ hτ (by norm_num)
      _ = (τ ^ 3) ^ 3 := by ring
      _ ≤ N ^ 3 := pow_le_pow_left₀ (by positivity) hN 3
  have hτ6N : τ ^ 6 ≤ N ^ 2 := by
    calc τ ^ 6 = (τ ^ 3) ^ 2 := by ring
      _ ≤ N ^ 2 := pow_le_pow_left₀ (by positivity) hN 2
  have hx4 : x ^ 4 ≤ 2 * τ ^ 2 := by
    have h1 : (x ^ 4) ^ 2 ≤ (2 * τ ^ 2) ^ 2 := by
      have h4 : 0 ≤ τ ^ 4 := by positivity
      calc (x ^ 4) ^ 2 = x ^ 8 := by ring
        _ ≤ 2 * τ ^ 4 := hxτ
        _ ≤ 4 * τ ^ 4 := by linarith
        _ = (2 * τ ^ 2) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h1
  have he3' : e ^ 3 ≤ 3 * x ^ 18 := cube_le_of_pow_four_le he3
  have hx2 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)
  have h1sq : t₁ ^ 2 ≤ (t₁ + t₂ + t₃) ^ 2 := pow_le_pow_left₀ ht₁ (by linarith) 2
  have h2sq : t₂ ^ 2 ≤ (t₁ + t₂ + t₃) ^ 2 := pow_le_pow_left₀ ht₂ (by linarith) 2
  have h3sq : t₃ ^ 2 ≤ (t₁ + t₂ + t₃) ^ 2 := pow_le_pow_left₀ ht₃ (by linarith) 2
  set S := (t₁ + t₂ + t₃) ^ 2
  -- the nine products, each at most `3S`
  have p11 : x ^ 16 * N * (x ^ 32 * N) ≤ 3 * S := by
    have : x ^ 16 * N * (x ^ 32 * N) = t₁ ^ 2 := by simp only [t₁]; ring
    linarith [sq_nonneg t₁, sq_nonneg t₂, sq_nonneg t₃]
  have p12 : x ^ 16 * N * (e ^ 4 * τ ^ 4) ≤ 3 * S := by
    have k : x ^ 8 * τ ^ 4 ≤ 2 * N ^ 3 := by
      calc x ^ 8 * τ ^ 4 ≤ (2 * τ ^ 4) * τ ^ 4 := mul_le_mul_of_nonneg_right hxτ (by positivity)
        _ = 2 * τ ^ 8 := by ring
        _ ≤ 2 * N ^ 3 := by linarith
    have : x ^ 16 * N * (e ^ 4 * τ ^ 4) ≤ 2 * t₃ ^ 2 := by
      calc x ^ 16 * N * (e ^ 4 * τ ^ 4) = (e ^ 4 * x ^ 8 * N) * (x ^ 8 * τ ^ 4) := by ring
        _ ≤ (e ^ 4 * x ^ 8 * N) * (2 * N ^ 3) := mul_le_mul_of_nonneg_left k (by positivity)
        _ = 2 * t₃ ^ 2 := by simp only [t₃]; ring
    linarith [sq_nonneg t₁, sq_nonneg t₂, sq_nonneg t₃]
  have p13 : x ^ 16 * N * (e ^ 3 * x ^ 8 * τ ^ 2 * N) ≤ 3 * S := by
    have : x ^ 16 * N * (e ^ 3 * x ^ 8 * τ ^ 2 * N) ≤ 3 * t₂ ^ 2 := by
      calc x ^ 16 * N * (e ^ 3 * x ^ 8 * τ ^ 2 * N) = (x ^ 24 * τ ^ 2 * N ^ 2) * e ^ 3 := by ring
        _ ≤ (x ^ 24 * τ ^ 2 * N ^ 2) * (3 * x ^ 18) := mul_le_mul_of_nonneg_left he3' (by positivity)
        _ = 3 * t₂ ^ 2 := by simp only [t₂]; ring
    linarith [sq_nonneg t₁, sq_nonneg t₂, sq_nonneg t₃]
  have p21 : x ^ 8 * τ ^ 4 * (x ^ 32 * N) ≤ 3 * S := by
    have k : τ ^ 2 ≤ N * x ^ 2 := le_trans hτ2N (le_mul_of_one_le_right hN0 (one_le_pow₀ hx))
    have : x ^ 8 * τ ^ 4 * (x ^ 32 * N) ≤ t₂ ^ 2 := by
      calc x ^ 8 * τ ^ 4 * (x ^ 32 * N) = (x ^ 40 * τ ^ 2 * N) * τ ^ 2 := by ring
        _ ≤ (x ^ 40 * τ ^ 2 * N) * (N * x ^ 2) := mul_le_mul_of_nonneg_left k (by positivity)
        _ = t₂ ^ 2 := by simp only [t₂]; ring
    linarith [sq_nonneg t₁, sq_nonneg t₂, sq_nonneg t₃]
  have p22 : x ^ 8 * τ ^ 4 * (e ^ 4 * τ ^ 4) ≤ 3 * S := by
    have k : τ ^ 8 ≤ N ^ 4 := by
      calc τ ^ 8 = (τ ^ 2) ^ 4 := by ring
        _ ≤ N ^ 4 := pow_le_pow_left₀ (by positivity) hτ2N 4
    have : x ^ 8 * τ ^ 4 * (e ^ 4 * τ ^ 4) ≤ t₃ ^ 2 := by
      calc x ^ 8 * τ ^ 4 * (e ^ 4 * τ ^ 4) = (e ^ 4 * x ^ 8) * τ ^ 8 := by ring
        _ ≤ (e ^ 4 * x ^ 8) * N ^ 4 := mul_le_mul_of_nonneg_left k (by positivity)
        _ = t₃ ^ 2 := by simp only [t₃]; ring
    linarith [sq_nonneg t₁, sq_nonneg t₂, sq_nonneg t₃]
  have p23 : x ^ 8 * τ ^ 4 * (e ^ 3 * x ^ 8 * τ ^ 2 * N) ≤ 3 * S := by
    have k : x ^ 8 * τ ^ 6 ≤ 2 * e * N ^ 3 := by
      calc x ^ 8 * τ ^ 6 = x ^ 4 * (x ^ 4 * τ ^ 6) := by ring
        _ ≤ e * (2 * τ ^ 2 * τ ^ 6) :=
            mul_le_mul he (mul_le_mul_of_nonneg_right hx4 (by positivity)) (by positivity) he0
        _ = 2 * e * τ ^ 8 := by ring
        _ ≤ 2 * e * N ^ 3 := mul_le_mul_of_nonneg_left hτ8N (by positivity)
    have : x ^ 8 * τ ^ 4 * (e ^ 3 * x ^ 8 * τ ^ 2 * N) ≤ 2 * t₃ ^ 2 := by
      calc x ^ 8 * τ ^ 4 * (e ^ 3 * x ^ 8 * τ ^ 2 * N) = (e ^ 3 * x ^ 8 * N) * (x ^ 8 * τ ^ 6) := by
            ring
        _ ≤ (e ^ 3 * x ^ 8 * N) * (2 * e * N ^ 3) := mul_le_mul_of_nonneg_left k (by positivity)
        _ = 2 * t₃ ^ 2 := by simp only [t₃]; ring
    linarith [sq_nonneg t₁, sq_nonneg t₂, sq_nonneg t₃]
  have p31 : x ^ 10 * τ ^ 2 * N * (x ^ 32 * N) ≤ 3 * S := by
    have : x ^ 10 * τ ^ 2 * N * (x ^ 32 * N) = t₂ ^ 2 := by simp only [t₂]; ring
    linarith [sq_nonneg t₁, sq_nonneg t₂, sq_nonneg t₃]
  have p32 : x ^ 10 * τ ^ 2 * N * (e ^ 4 * τ ^ 4) ≤ 3 * S := by
    have k : x ^ 2 * τ ^ 6 ≤ 2 * N ^ 3 := by
      calc x ^ 2 * τ ^ 6 ≤ (2 * τ ^ 2) * τ ^ 6 :=
            mul_le_mul_of_nonneg_right (hx2.trans hx4) (by positivity)
        _ = 2 * τ ^ 8 := by ring
        _ ≤ 2 * N ^ 3 := by linarith
    have : x ^ 10 * τ ^ 2 * N * (e ^ 4 * τ ^ 4) ≤ 2 * t₃ ^ 2 := by
      calc x ^ 10 * τ ^ 2 * N * (e ^ 4 * τ ^ 4) = (e ^ 4 * x ^ 8 * N) * (x ^ 2 * τ ^ 6) := by ring
        _ ≤ (e ^ 4 * x ^ 8 * N) * (2 * N ^ 3) := mul_le_mul_of_nonneg_left k (by positivity)
        _ = 2 * t₃ ^ 2 := by simp only [t₃]; ring
    linarith [sq_nonneg t₁, sq_nonneg t₂, sq_nonneg t₃]
  have p33 : x ^ 10 * τ ^ 2 * N * (e ^ 3 * x ^ 8 * τ ^ 2 * N) ≤ 3 * S := by
    rcases le_or_gt (x ^ 3) τ with hc | hc
    · -- `|W| ≤ T^{2/3}`
      have k : x ^ 10 * τ ^ 4 ≤ e * N ^ 2 := by
        have hx6 : x ^ 6 ≤ τ ^ 2 := by
          calc x ^ 6 = (x ^ 3) ^ 2 := by ring
            _ ≤ τ ^ 2 := pow_le_pow_left₀ (by positivity) hc 2
        calc x ^ 10 * τ ^ 4 = x ^ 4 * (x ^ 6 * τ ^ 4) := by ring
          _ ≤ e * (τ ^ 2 * τ ^ 4) :=
              mul_le_mul he (mul_le_mul_of_nonneg_right hx6 (by positivity)) (by positivity) he0
          _ = e * τ ^ 6 := by ring
          _ ≤ e * N ^ 2 := mul_le_mul_of_nonneg_left hτ6N he0
      have : x ^ 10 * τ ^ 2 * N * (e ^ 3 * x ^ 8 * τ ^ 2 * N) ≤ t₃ ^ 2 := by
        calc x ^ 10 * τ ^ 2 * N * (e ^ 3 * x ^ 8 * τ ^ 2 * N) =
              (e ^ 3 * x ^ 8 * N ^ 2) * (x ^ 10 * τ ^ 4) := by ring
          _ ≤ (e ^ 3 * x ^ 8 * N ^ 2) * (e * N ^ 2) := mul_le_mul_of_nonneg_left k (by positivity)
          _ = t₃ ^ 2 := by simp only [t₃]; ring
      linarith [sq_nonneg t₁, sq_nonneg t₂, sq_nonneg t₃]
    · -- `|W| > T^{2/3}`
      have hτ2 : τ ^ 2 ≤ x ^ 6 := by
        calc τ ^ 2 ≤ (x ^ 3) ^ 2 := pow_le_pow_left₀ hτ0 hc.le 2
          _ = x ^ 6 := by ring
      have k : τ ^ 2 * e ^ 3 ≤ 3 * x ^ 24 := by
        calc τ ^ 2 * e ^ 3 ≤ x ^ 6 * (3 * x ^ 18) := mul_le_mul hτ2 he3' (by positivity) (by positivity)
          _ = 3 * x ^ 24 := by ring
      have : x ^ 10 * τ ^ 2 * N * (e ^ 3 * x ^ 8 * τ ^ 2 * N) ≤ 3 * t₂ ^ 2 := by
        calc x ^ 10 * τ ^ 2 * N * (e ^ 3 * x ^ 8 * τ ^ 2 * N) =
              (x ^ 18 * τ ^ 2 * N ^ 2) * (τ ^ 2 * e ^ 3) := by ring
          _ ≤ (x ^ 18 * τ ^ 2 * N ^ 2) * (3 * x ^ 24) := mul_le_mul_of_nonneg_left k (by positivity)
          _ = 3 * t₂ ^ 2 := by simp only [t₂]; ring
      linarith [sq_nonneg t₁, sq_nonneg t₂, sq_nonneg t₃]
  have hexp : (x ^ 16 * N + x ^ 8 * τ ^ 4 + x ^ 10 * τ ^ 2 * N) *
      (x ^ 32 * N + e ^ 4 * τ ^ 4 + e ^ 3 * x ^ 8 * τ ^ 2 * N) =
        x ^ 16 * N * (x ^ 32 * N) + x ^ 16 * N * (e ^ 4 * τ ^ 4) +
        x ^ 16 * N * (e ^ 3 * x ^ 8 * τ ^ 2 * N) + x ^ 8 * τ ^ 4 * (x ^ 32 * N) +
        x ^ 8 * τ ^ 4 * (e ^ 4 * τ ^ 4) + x ^ 8 * τ ^ 4 * (e ^ 3 * x ^ 8 * τ ^ 2 * N) +
        x ^ 10 * τ ^ 2 * N * (x ^ 32 * N) + x ^ 10 * τ ^ 2 * N * (e ^ 4 * τ ^ 4) +
        x ^ 10 * τ ^ 2 * N * (e ^ 3 * x ^ 8 * τ ^ 2 * N) := by ring
  rw [hexp]
  linarith

/-- **The exponent algebra of Lemma 11.9.** For `1 ≤ X ≤ 2T`, `T ≥ 1`, `X² ≤ E ≤ 3X³` and
`T^{3/4} ≤ N`:
`√((X²N + XT + X^{5/4}T^{1/2}N)(X⁴N + ET + E^{3/4}XT^{1/2}N)) ≤
  6 (N X³ + N T^{1/4} X^{21/8} + √E √X N²)`. -/
theorem largeGcd_algebra_rpow {X E T N : ℝ} (hX : 1 ≤ X) (hT : 1 ≤ T) (hXE : X ^ 2 ≤ E)
    (hE : E ≤ 3 * X ^ 3) (hXT : X ≤ 2 * T) (hN : T ^ (3 / 4 : ℝ) ≤ N) :
    Real.sqrt ((X ^ 2 * N + X * T + X ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) *
        (X ^ 4 * N + E * T + E ^ (3 / 4 : ℝ) * X * T ^ (1 / 2 : ℝ) * N)) ≤
      6 * (N * X ^ 3 + N * T ^ (1 / 4 : ℝ) * X ^ (21 / 8 : ℝ) +
        Real.sqrt E * Real.sqrt X * N ^ 2) := by
  have hX0 : 0 ≤ X := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hE0 : 0 ≤ E := le_trans (by positivity) hXE
  have pw : ∀ {Y : ℝ}, 0 ≤ Y → ∀ (a : ℝ) (k : ℕ), (Y ^ a) ^ k = Y ^ (a * k) :=
    fun hY a k => (Real.rpow_mul_natCast hY a k).symm
  -- every quantity is a monomial in `x = X^{1/8}`, `τ = T^{1/4}`, `e = E^{1/4}`
  have eX : X = (X ^ (1 / 8 : ℝ)) ^ 8 := by rw [pw hX0]; norm_num
  have eX54 : X ^ (5 / 4 : ℝ) = (X ^ (1 / 8 : ℝ)) ^ 10 := by rw [pw hX0]; norm_num
  have eX218 : X ^ (21 / 8 : ℝ) = (X ^ (1 / 8 : ℝ)) ^ 21 := by rw [pw hX0]; norm_num
  have eXs : Real.sqrt X = (X ^ (1 / 8 : ℝ)) ^ 4 := by
    rw [Real.sqrt_eq_rpow, pw hX0]; norm_num
  have eT : T = (T ^ (1 / 4 : ℝ)) ^ 4 := by rw [pw hT0]; norm_num
  have eT12 : T ^ (1 / 2 : ℝ) = (T ^ (1 / 4 : ℝ)) ^ 2 := by rw [pw hT0]; norm_num
  have eT34 : T ^ (3 / 4 : ℝ) = (T ^ (1 / 4 : ℝ)) ^ 3 := by rw [pw hT0]; norm_num
  have eE : E = (E ^ (1 / 4 : ℝ)) ^ 4 := by rw [pw hE0]; norm_num
  have eE34 : E ^ (3 / 4 : ℝ) = (E ^ (1 / 4 : ℝ)) ^ 3 := by rw [pw hE0]; norm_num
  have eEs : Real.sqrt E = (E ^ (1 / 4 : ℝ)) ^ 2 := by
    rw [Real.sqrt_eq_rpow, pw hE0]; norm_num
  have hx1 : 1 ≤ X ^ (1 / 8 : ℝ) := Real.one_le_rpow hX (by norm_num)
  have hτ1 : 1 ≤ T ^ (1 / 4 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have he0 : 0 ≤ E ^ (1 / 4 : ℝ) := by positivity
  set x := X ^ (1 / 8 : ℝ)
  set τ := T ^ (1 / 4 : ℝ)
  set e := E ^ (1 / 4 : ℝ)
  have he : x ^ 4 ≤ e := by
    have h : (x ^ 4) ^ 4 ≤ e ^ 4 := by
      have : X ^ 2 = (x ^ 4) ^ 4 := by rw [eX]; ring
      rw [← this, ← eE]; exact hXE
    exact (pow_le_pow_iff_left₀ (by positivity) he0 (by norm_num)).mp h
  have he3 : e ^ 4 ≤ 3 * x ^ 24 := by
    have : 3 * X ^ 3 = 3 * x ^ 24 := by rw [eX]; ring
    rw [← eE, ← this]; exact hE
  have hxτ : x ^ 8 ≤ 2 * τ ^ 4 := by rw [← eX, ← eT]; exact hXT
  have hNτ : τ ^ 3 ≤ N := by rw [← eT34]; exact hN
  have halg := largeGcd_algebra hx1 hτ1 he he3 hxτ hNτ
  have hlhs : (X ^ 2 * N + X * T + X ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) *
      (X ^ 4 * N + E * T + E ^ (3 / 4 : ℝ) * X * T ^ (1 / 2 : ℝ) * N) =
        (x ^ 16 * N + x ^ 8 * τ ^ 4 + x ^ 10 * τ ^ 2 * N) *
          (x ^ 32 * N + e ^ 4 * τ ^ 4 + e ^ 3 * x ^ 8 * τ ^ 2 * N) := by
    rw [eX54, eT12, eE34]
    rw [show X ^ 2 = x ^ 16 by rw [eX]; ring, show X ^ 4 = x ^ 32 by rw [eX]; ring]
    rw [eX, eT, eE]
  have hrhs : N * X ^ 3 + N * T ^ (1 / 4 : ℝ) * X ^ (21 / 8 : ℝ) +
      Real.sqrt E * Real.sqrt X * N ^ 2 = N * x ^ 24 + N * τ * x ^ 21 + e ^ 2 * x ^ 4 * N ^ 2 := by
    rw [eX218, eEs, eXs, show X ^ 3 = x ^ 24 by rw [eX]; ring]
  rw [hlhs, hrhs]
  have hN0 : 0 ≤ N := le_trans (by positivity) hNτ
  have hR0 : 0 ≤ N * x ^ 24 + N * τ * x ^ 21 + e ^ 2 * x ^ 4 * N ^ 2 := by positivity
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have hsq := sq_nonneg (N * x ^ 24 + N * τ * x ^ 21 + e ^ 2 * x ^ 4 * N ^ 2)
  calc _ ≤ 27 * (N * x ^ 24 + N * τ * x ^ 21 + e ^ 2 * x ^ 4 * N ^ 2) ^ 2 := halg
    _ ≤ 36 * (N * x ^ 24 + N * τ * x ^ 21 + e ^ 2 * x ^ 4 * N ^ 2) ^ 2 := by linarith
    _ = (6 * (N * x ^ 24 + N * τ * x ^ 21 + e ^ 2 * x ^ 4 * N ^ 2)) ^ 2 := by ring

end RHTower.GuthMaynard
