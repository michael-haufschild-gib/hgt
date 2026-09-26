import GaloisForLFunctions.RHTower.XiSliceHighOrderCoeffPositivity
import GaloisForLFunctions.RHTower.ZetaConvexityBound
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin

/-!
# Tail of the saddle arc when the saddle point is near the critical strip

Let `S(θ) = g_t(Re^{iθ}) e^{−2ikθ}/g_t(R)` be the normalised arc value of the slice product
`g_t(x) = ξ(½+x+it)ξ(½−x+it)`.  For a saddle radius `½ + 2η ≤ R ≤ R₁` and `θ₁ ≤ θ ≤ π/2`,

`|S(θ)| ≤ A (t^{−η} + t^{−θ₁²/10})`,

with `A` depending only on `η`, `R₁`.  The circle-decay law of `|g_t|`
(`norm_xiSliceProduct_circle_le`) reduces this to `ζ` bounds at the arc points
`½ + R cos θ + i(t ± R sin θ)` and a lower bound at the saddle point `½ + R + it`:
* at the saddle point `‖ζ‖ ≥ 1/(1 + 1/(2η))`, since `‖1/ζ‖ ≤ Σ n^{−σ}`;
* where `½ + R cos θ ≥ 1 + η`, `‖ζ‖ ≤ 1 + 1/η`, and the Gamma decay `(t/2π)^{−R(1−cos θ)}` with
  `R(1 − cos θ) ≥ θ₁²/10` gives the second term;
* where `½ + R cos θ < 1 + η`, the convexity bound `‖ζ(σ+it')‖ ≤ C t'^{(1+η−σ)/2}` costs
  `(2t)^{½+η−R cos θ}`, and against the Gamma decay `(t/2π)^{−(R − R cos θ)}` it leaves
  `t^{½+η−R} ≤ t^{−η}`.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- `(x/(2π))^{−y} ≤ (2π)^{Y} x^{−y}` for `x > 0` and `y ≤ Y`. -/
theorem div_two_pi_rpow_neg_le {x y Y : ℝ} (hx : 0 < x) (hyY : y ≤ Y) :
    (x / (2 * Real.pi)) ^ (-y) ≤ (2 * Real.pi) ^ Y * x ^ (-y) := by
  have h2pi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  rw [Real.div_rpow hx.le (by positivity), Real.rpow_neg (x := 2 * Real.pi) (by positivity),
    div_inv_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h2pi hyY) (by positivity)

/-- `exp(−y log(x/2π)) = (x/2π)^{−y}`. -/
theorem exp_neg_mul_log_div_two_pi {x y : ℝ} (hx : 0 < x) :
    Real.exp (-y * Real.log (x / (2 * Real.pi))) = (x / (2 * Real.pi)) ^ (-y) := by
  rw [Real.rpow_def_of_pos (by positivity)]; ring_nf

/-- At the saddle point `½ + R + it` with `R ≥ ½ + 2η`, `‖ζ‖ ≥ 1/(1 + 1/(2η))`. -/
theorem inv_le_norm_riemannZeta_saddle {η R : ℝ} (t : ℝ) (hη : 0 < η) (hR : 1 / 2 + 2 * η ≤ R) :
    1 / (1 + 1 / (2 * η)) ≤ ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  have hre : (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I).re = 1 / 2 + R := by simp
  have hinv := norm_inv_riemannZeta_le_of_le_re (σ₁ := 1 + 2 * η) (by linarith)
    (s := ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) (by rw [hre]; linarith)
  rw [norm_inv, show (1 + 2 * η - 1) = 2 * η by ring] at hinv
  have hpos : 0 < ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; linarith))
  rw [one_div, inv_le_comm₀ (by positivity) hpos]
  exact hinv

/-- The lower-order terms of the circle decay exponent are at most `1`. -/
theorem circle_remainder_le_one {t R R₁ θ : ℝ} (ht : 32 * R₁ + 16 ≤ t) (hR0 : 0 ≤ R)
    (hRR₁ : R ≤ R₁) (hcos : 0 ≤ Real.cos θ) :
    12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t + 4 * (1 / 2 + R * Real.cos θ) / t
      ≤ 1 := by
  have ht0 : 0 < t := by linarith
  have h1 : R * (1 - Real.cos θ) ≤ R := mul_le_of_le_one_right hR0 (by linarith)
  have h2 : R * |Real.sin θ| ≤ R := mul_le_of_le_one_right hR0 (Real.abs_sin_le_one θ)
  have h3 : R * Real.cos θ ≤ R := mul_le_of_le_one_right hR0 (Real.cos_le_one θ)
  rw [← add_div, div_le_one ht0]
  linarith

/-- The circle decay factor with a lower bound `d ≤ R(1 − cos θ)` for the decay exponent. -/
theorem circle_decay_exp_le {t R R₁ θ d : ℝ} (ht : 32 * R₁ + 16 ≤ t) (hR0 : 0 ≤ R)
    (hRR₁ : R ≤ R₁) (hcos : 0 ≤ Real.cos θ) (hd : d ≤ R * (1 - Real.cos θ))
    (hdR : d ≤ R₁) :
    Real.exp (-(R * (1 - Real.cos θ)) * Real.log (t / (2 * Real.pi))
        + 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t + 4 * (1 / 2 + R * Real.cos θ) / t)
      ≤ Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-d)) := by
  have ht0 : 0 < t := by linarith
  have hlog0 : 0 ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith [Real.pi_lt_d2])
  have hsmall := circle_remainder_le_one ht hR0 hRR₁ hcos
  have hdl : d * Real.log (t / (2 * Real.pi))
      ≤ R * (1 - Real.cos θ) * Real.log (t / (2 * Real.pi)) :=
    mul_le_mul_of_nonneg_right hd hlog0
  have e1 : -(R * (1 - Real.cos θ)) * Real.log (t / (2 * Real.pi))
      + 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t + 4 * (1 / 2 + R * Real.cos θ) / t
      ≤ 1 + (-d * Real.log (t / (2 * Real.pi))) := by
    rw [neg_mul, neg_mul]; linarith
  calc _ ≤ Real.exp (1 + (-d * Real.log (t / (2 * Real.pi)))) := Real.exp_le_exp.mpr e1
    _ = Real.exp 1 * (t / (2 * Real.pi)) ^ (-d) := by
        rw [Real.exp_add, exp_neg_mul_log_div_two_pi ht0]
    _ ≤ Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-d)) :=
        mul_le_mul_of_nonneg_left (div_two_pi_rpow_neg_le ht0 hdR) (Real.exp_pos 1).le

/-- The real part of `(½ + a) + i(t + c)` is `½ + a`. -/
theorem re_ofReal_add_ofReal_mul_I (a b : ℝ) : ((a : ℂ) + (b : ℂ) * I).re = a := by
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- **Arc bound when the arc point lies in the half-plane `Re ≥ 1 + η`.** -/
theorem norm_sliceArc_le_of_euler_arc {η R₁ θ₁ m₀ t R θ : ℝ} (k : ℕ) (hη : 0 < η)
    (ht : 32 * R₁ + 16 ≤ t) (hR : 1 / 2 ≤ R) (hRR₁ : R ≤ R₁) (hθ₁ : 0 < θ₁)
    (hθ : θ₁ ≤ θ) (hθπ : θ ≤ Real.pi / 2) (hm₀ : 0 < m₀)
    (hz₀ : m₀ ≤ ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖)
    (hE : 1 / 2 + η ≤ R * Real.cos θ) :
    ‖sliceArc t R k θ‖
      ≤ ((1 + 1 / η) / m₀) ^ 2 * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(θ₁ ^ 2 / 10)))) := by
  have hR0 : 0 < R := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hθπ
  have hB : ∀ c : ℝ, ‖riemannZeta (((1 / 2 + R * Real.cos θ : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖
      ≤ 1 + 1 / η := by
    intro c
    have hre := re_ofReal_add_ofReal_mul_I (1 / 2 + R * Real.cos θ) (t + c)
    have h := Sieve.norm_riemannZeta_le
      (s := ((1 / 2 + R * Real.cos θ : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I) (by rw [hre]; linarith)
    rw [hre] at h
    have : 1 / (1 / 2 + R * Real.cos θ - 1) ≤ 1 / η :=
      one_div_le_one_div_of_le hη (by linarith)
    linarith
  have hB2 : ‖riemannZeta (((1 / 2 + R * Real.cos θ : ℝ) : ℂ)
      + ((t - R * Real.sin θ : ℝ) : ℂ) * I)‖ ≤ 1 + 1 / η := by
    have := hB (-(R * Real.sin θ)); rwa [← sub_eq_add_neg] at this
  have hcirc := norm_xiSliceProduct_circle_le (by linarith) hR0.le (by linarith) hcos hm₀ hz₀
    (hB _) hB2
  have hθsq : θ₁ ^ 2 / 10 ≤ R * (1 - Real.cos θ) := by
    have hc5 := one_sub_cos_ge_sq_div_five (θ := θ)
      (by rw [abs_of_nonneg hθ0]; linarith [Real.pi_pos])
    have hθ2 : θ₁ ^ 2 ≤ θ ^ 2 := pow_le_pow_left₀ hθ₁.le hθ 2
    have h1c : 0 ≤ 1 - Real.cos θ := by linarith [Real.cos_le_one θ]
    calc θ₁ ^ 2 / 10 ≤ 1 / 2 * (θ ^ 2 / 5) := by linarith
      _ ≤ 1 / 2 * (1 - Real.cos θ) := by linarith
      _ ≤ R * (1 - Real.cos θ) := mul_le_mul_of_nonneg_right hR h1c
  have hdR : θ₁ ^ 2 / 10 ≤ R₁ :=
    hθsq.trans ((mul_le_of_le_one_right hR0.le (by linarith)).trans hRR₁)
  have hexpX := circle_decay_exp_le (d := θ₁ ^ 2 / 10) ht hR0.le hRR₁ hcos hθsq hdR
  have haR : R * Real.cos θ ≤ R := mul_le_of_le_one_right hR0.le (Real.cos_le_one θ)
  have hgR : 0 < ‖xiSliceProduct t (R : ℂ)‖ := by
    rw [norm_xiSliceProduct_real]
    exact pow_pos (norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by
      rw [re_ofReal_add_ofReal_mul_I]; linarith))) 2
  rw [norm_sliceArc_eq, div_le_iff₀ hgR]
  calc ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
      ≤ _ := hcirc
    _ ≤ ‖xiSliceProduct t (R : ℂ)‖ * ((1 + 1 / η) / m₀) ^ 2
        * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(θ₁ ^ 2 / 10)))) :=
        mul_le_mul_of_nonneg_left hexpX (by positivity)
    _ = _ := by ring

/-- **Arc bound when the arc point lies in the strip `Re < 1 + η`**, via convexity. -/
theorem norm_sliceArc_le_of_strip_arc {η R₁ m₀ Cc t R θ : ℝ} (k : ℕ) (hη : 0 < η)
    (hη1 : η ≤ 1 / 2) (hCc : 0 < Cc)
    (hconv : ∀ σ t : ℝ, -η ≤ σ → σ ≤ 1 + η → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cc * t ^ ((1 + η - σ) / 2))
    (ht : 32 * R₁ + 16 ≤ t) (hR : 1 / 2 + 2 * η ≤ R) (hRR₁ : R ≤ R₁)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi / 2) (hm₀ : 0 < m₀)
    (hz₀ : m₀ ≤ ‖riemannZeta (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖)
    (hS : R * Real.cos θ < 1 / 2 + η) :
    ‖sliceArc t R k θ‖ ≤ (Cc / m₀) ^ 2 * Real.exp 1 * (2 * (2 * Real.pi) ^ R₁ * t ^ (-η)) := by
  have ht0 : 0 < t := by linarith
  have hR0 : 0 < R := by linarith
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hθπ
  have haR : R * Real.cos θ ≤ R := mul_le_of_le_one_right hR0.le (Real.cos_le_one θ)
  have ha0 : 0 ≤ R * Real.cos θ := mul_nonneg hR0.le hcos
  have hBc : ∀ c : ℝ, |c| ≤ R₁ →
      ‖riemannZeta (((1 / 2 + R * Real.cos θ : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖
        ≤ Cc * (2 * t) ^ ((1 + η - (1 / 2 + R * Real.cos θ)) / 2) := by
    intro c hc
    have hc' := abs_le.mp hc
    refine (hconv _ _ (by linarith) (by linarith) (by linarith)).trans ?_
    gcongr
    all_goals linarith
  have hsinR : |R * Real.sin θ| ≤ R₁ := by
    rw [abs_mul, abs_of_pos hR0]
    exact (mul_le_of_le_one_right hR0.le (Real.abs_sin_le_one θ)).trans hRR₁
  have hB2 : ‖riemannZeta (((1 / 2 + R * Real.cos θ : ℝ) : ℂ)
      + ((t - R * Real.sin θ : ℝ) : ℂ) * I)‖
        ≤ Cc * (2 * t) ^ ((1 + η - (1 / 2 + R * Real.cos θ)) / 2) := by
    have := hBc (-(R * Real.sin θ)) (by rwa [abs_neg]); rwa [← sub_eq_add_neg] at this
  have hcirc := norm_xiSliceProduct_circle_le (by linarith) hR0.le (by linarith) hcos hm₀ hz₀
    (hBc _ hsinR) hB2
  have hpow : (Cc * (2 * t) ^ ((1 + η - (1 / 2 + R * Real.cos θ)) / 2) / m₀) ^ 2
      = (Cc / m₀) ^ 2 * (2 * t) ^ (1 / 2 + η - R * Real.cos θ) := by
    rw [div_pow, mul_pow, ← Real.rpow_natCast ((2 * t) ^ _), ← Real.rpow_mul (by positivity)]
    push_cast
    rw [show (1 + η - (1 / 2 + R * Real.cos θ)) / 2 * 2 = 1 / 2 + η - R * Real.cos θ by ring]
    ring
  have hd : R - R * Real.cos θ ≤ R * (1 - Real.cos θ) := by rw [mul_sub, mul_one]
  have hdR : R - R * Real.cos θ ≤ R₁ := by linarith
  have hexpX := circle_decay_exp_le (d := R - R * Real.cos θ) ht hR0.le hRR₁ hcos hd hdR
  have hkey : (2 * t) ^ (1 / 2 + η - R * Real.cos θ) * t ^ (-(R - R * Real.cos θ))
      ≤ 2 * t ^ (-η) := by
    rw [Real.mul_rpow (by norm_num) ht0.le, mul_assoc, ← Real.rpow_add ht0]
    have h2 : (2 : ℝ) ^ (1 / 2 + η - R * Real.cos θ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 2 + η - R * Real.cos θ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h4 : t ^ (1 / 2 + η - R * Real.cos θ + -(R - R * Real.cos θ)) ≤ t ^ (-η) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    exact mul_le_mul h2 h4 (by positivity) (by norm_num)
  have hgR : 0 < ‖xiSliceProduct t (R : ℂ)‖ := by
    rw [norm_xiSliceProduct_real]
    exact pow_pos (norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by
      rw [re_ofReal_add_ofReal_mul_I]; linarith))) 2
  rw [norm_sliceArc_eq, div_le_iff₀ hgR]
  calc ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
      ≤ _ := hcirc
    _ = ‖xiSliceProduct t (R : ℂ)‖ * ((Cc / m₀) ^ 2 * (2 * t) ^ (1 / 2 + η - R * Real.cos θ))
        * Real.exp (-(R * (1 - Real.cos θ)) * Real.log (t / (2 * Real.pi))
          + 12 * (R * (1 - Real.cos θ) + R * |Real.sin θ|) / t
          + 4 * (1 / 2 + R * Real.cos θ) / t) := by rw [hpow]
    _ ≤ ‖xiSliceProduct t (R : ℂ)‖ * ((Cc / m₀) ^ 2 * (2 * t) ^ (1 / 2 + η - R * Real.cos θ))
        * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(R - R * Real.cos θ)))) :=
        mul_le_mul_of_nonneg_left hexpX (by positivity)
    _ = ‖xiSliceProduct t (R : ℂ)‖ * (Cc / m₀) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
        * ((2 * t) ^ (1 / 2 + η - R * Real.cos θ) * t ^ (-(R - R * Real.cos θ))) := by ring
    _ ≤ ‖xiSliceProduct t (R : ℂ)‖ * (Cc / m₀) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
        * (2 * t ^ (-η)) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by ring

/-- **Arc tail with the saddle near the strip.**  For `½ + 2η ≤ R ≤ R₁` and
`θ₁ ≤ θ ≤ π/2`, `|S(θ)| ≤ A (t^{−η} + t^{−θ₁²/10})` uniformly in the order `k`. -/
theorem exists_sliceArc_tail_le_euler {η R₁ θ₁ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (hθ₁ : 0 < θ₁) :
    ∃ A : ℝ, 0 < A ∧ ∀ (t R θ : ℝ) (k : ℕ), 32 * R₁ + 16 ≤ t → 1 / 2 + 2 * η ≤ R → R ≤ R₁ →
      θ₁ ≤ θ → θ ≤ Real.pi / 2 →
      ‖sliceArc t R k θ‖ ≤ A * (t ^ (-η) + t ^ (-(θ₁ ^ 2 / 10))) := by
  obtain ⟨Cc, hCc, hconv⟩ := exists_norm_riemannZeta_le_convexity (η := η) hη (by linarith)
  set m₀ : ℝ := 1 / (1 + 1 / (2 * η)) with hm₀
  have hm₀0 : 0 < m₀ := by rw [hm₀]; positivity
  refine ⟨Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * ((Cc + 1 + 1 / η) / m₀) ^ 2, by positivity, ?_⟩
  intro t R θ k ht hR hRR₁ hθ hθπ
  have hz₀ := inv_le_norm_riemannZeta_saddle t hη hR
  have ht0 : 0 < t := by linarith
  have htη : 0 ≤ t ^ (-η) := Real.rpow_nonneg ht0.le _
  have htθ : 0 ≤ t ^ (-(θ₁ ^ 2 / 10)) := Real.rpow_nonneg ht0.le _
  have hq : 0 ≤ (2 * Real.pi) ^ R₁ := by positivity
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  rcases le_or_gt (1 / 2 + η) (R * Real.cos θ) with hE | hS
  · have h := norm_sliceArc_le_of_euler_arc k hη ht (by linarith) hRR₁ hθ₁
      hθ hθπ hm₀0 hz₀ hE
    have hBm : ((1 + 1 / η) / m₀) ^ 2 ≤ ((Cc + 1 + 1 / η) / m₀) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (by linarith) hm₀0.le) 2
    refine h.trans ?_
    calc ((1 + 1 / η) / m₀) ^ 2 * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(θ₁ ^ 2 / 10))))
        ≤ ((Cc + 1 + 1 / η) / m₀) ^ 2
          * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(θ₁ ^ 2 / 10)))) :=
          mul_le_mul_of_nonneg_right hBm (by positivity)
      _ ≤ _ := by
          have key : Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * ((Cc + 1 + 1 / η) / m₀) ^ 2
                * (t ^ (-η) + t ^ (-(θ₁ ^ 2 / 10)))
              = ((Cc + 1 + 1 / η) / m₀) ^ 2
                * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(θ₁ ^ 2 / 10))))
                + ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
                  * (2 * t ^ (-η) + t ^ (-(θ₁ ^ 2 / 10))) := by ring
          rw [key]
          exact le_add_of_nonneg_right (by positivity)
  · have h := norm_sliceArc_le_of_strip_arc k hη (by linarith) hCc hconv ht hR hRR₁ (by linarith) hθπ hm₀0
      hz₀ hS
    have hCm : (Cc / m₀) ^ 2 ≤ ((Cc + 1 + 1 / η) / m₀) ^ 2 :=
      pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right (by have : 0 ≤ 1 / η := by positivity
                                        linarith) hm₀0.le) 2
    refine h.trans ?_
    calc (Cc / m₀) ^ 2 * Real.exp 1 * (2 * (2 * Real.pi) ^ R₁ * t ^ (-η))
        ≤ ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1 * (2 * (2 * Real.pi) ^ R₁ * t ^ (-η)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCm he) (by positivity)
      _ ≤ _ := by
          have key : Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * ((Cc + 1 + 1 / η) / m₀) ^ 2
                * (t ^ (-η) + t ^ (-(θ₁ ^ 2 / 10)))
              = ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1 * (2 * (2 * Real.pi) ^ R₁ * t ^ (-η))
                + ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1
                  * (2 * (2 * Real.pi) ^ R₁ * t ^ (-(θ₁ ^ 2 / 10))) := by ring
          rw [key]
          exact le_add_of_nonneg_right (by positivity)

end

end RHTower
