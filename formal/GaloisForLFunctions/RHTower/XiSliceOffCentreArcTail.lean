import GaloisForLFunctions.RHTower.XiSliceOffCentreSaddleArc
import GaloisForLFunctions.RHTower.XiSliceArcTailConvexity

/-!
# Tail of the saddle arc about an off-centre point

Let `f(w) = g_t(x₀ + w)` with `g_t(x) = ξ(½+x+it) ξ(½−x+it)` and `x₀ ≥ 0`, and let
`G(θ) = f(Re^{iθ}) e^{−inθ}/f(R)` be the normalised arc value on the circle `|w| = R`.  Put
`a = x₀ + R cos θ`, `c = R sin θ`.  Since `g_t` is even and real on the real axis,

  `|f(Re^{iθ})| = |ξ(½ + |a| + i(t + c))| · |ξ(½ + |a| + i(t − c))|`  (`norm_xiSliceShift_arc`),

so the arc point behaves like the point at real part `½ + |a|`, at distance
`d(θ) = x₀ + R − |a|` to the left of the saddle point `½ + x₀ + R + it`.  The Gamma factors give the
decay `(t/2π)^{−d(θ)}` (`norm_xi_split_le`), and:

* where `½ + |a| ≥ 1 + η` the `ζ` ratio is bounded (`norm_shiftArc_le_euler`);
* where `½ + |a| < 1 + η` the convexity bound costs `(2t)^{½+η−|a|}`, and against the decay this
  leaves `t^{½+η−x₀−R} ≤ t^{−η}` once `x₀ + R ≥ ½ + 2η` (`norm_shiftArc_le_strip`).

On `θ₁ ≤ θ ≤ π` the decay exponent is at least `min(Rθ₁²/5, 2x₀)` (`min_le_shift_decay`): on the
near half `d(θ) = R(1 − cos θ)`, and where `a < 0` it is `2x₀ + R(1 + cos θ)`.  So the whole arc
beyond `θ₁`, including the far side `θ ≈ π`, is `O(t^{−η} + t^{−min(Rθ₁²/5, 2x₀)})`
(`exists_shiftArc_tail_le`).  At `x₀ = 0` the far side does not decay, which is why the centred
analysis folds the circle to a quarter.
-/

open Complex Real Metric
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- `|G(θ)| = |f(Re^{iθ})| / |f(R)|`. -/
theorem norm_saddleArc_xiSliceShift (t x₀ R θ : ℝ) (n : ℕ) :
    ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖
      = ‖xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
        / ‖xiSliceShift t x₀ (R : ℂ)‖ := by
  simp only [HTGeometry.saddleArc, norm_div, norm_mul]
  rw [show ‖Complex.exp (-((((n : ℝ) * θ : ℝ)) : ℂ) * I)‖ = 1 by
    rw [Complex.norm_exp]; simp]
  ring

/-- The arc point of the shifted slice in terms of `ξ` at real part `½ + |x₀ + R cos θ|`. -/
theorem norm_xiSliceShift_arc (t x₀ R θ : ℝ) :
    ‖xiSliceShift t x₀ ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
      = ‖xi (((1 / 2 + |x₀ + R * Real.cos θ| : ℝ) : ℂ) + ((t + R * Real.sin θ : ℝ) : ℂ) * I)‖
        * ‖xi (((1 / 2 + |x₀ + R * Real.cos θ| : ℝ) : ℂ)
            + ((t - R * Real.sin θ : ℝ) : ℂ) * I)‖ := by
  have hpt : (x₀ : ℂ) + (R : ℂ) * Complex.exp ((θ : ℂ) * I)
      = ((x₀ + R * Real.cos θ : ℝ) : ℂ) + ((R * Real.sin θ : ℝ) : ℂ) * I := by
    rw [ofReal_mul_exp_mul_I]
    push_cast
    ring
  rw [xiSliceShift, hpt]
  rcases le_or_gt 0 (x₀ + R * Real.cos θ) with ha | ha
  · rw [abs_of_nonneg ha]
    exact norm_xiSliceProduct_eq t _ _
  · rw [abs_of_neg ha]
    set a : ℝ := x₀ + R * Real.cos θ
    set c : ℝ := R * Real.sin θ
    have h1 : xiSliceProduct t ((a : ℂ) + (c : ℂ) * I)
        = (starRingEnd ℂ) (xiSliceProduct t (((-a : ℝ) : ℂ) + (c : ℂ) * I)) := by
      rw [← xiSliceProduct_conj, ← xiSliceProduct_neg]
      congr 1
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_conj, norm_xiSliceProduct_eq]

/-- The decay factor of an arc point: the lower-order Stirling terms cost at most `e`, and
`(t/2π)^{−D} ≤ (2π)^{R₁} t^{−d}` for `d ≤ D ≤ R₁`. -/
theorem exp_shift_decay_le {t R₁ d D c a : ℝ} (ht : 32 * R₁ + 16 ≤ t) (hdD : d ≤ D)
    (hD0 : 0 ≤ D) (hDR : D ≤ R₁) (hc : |c| ≤ R₁) (haR : a ≤ R₁) :
    Real.exp (-D * Real.log (t / (2 * Real.pi)) + 12 * (D + |c|) / t + 4 * (1 / 2 + a) / t)
      ≤ Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-d)) := by
  have hR₁ : 0 ≤ R₁ := hD0.trans hDR
  have ht0 : 0 < t := by linarith
  have hlog0 : 0 ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith [Real.pi_lt_d2])
  have hsmall : 12 * (D + |c|) / t + 4 * (1 / 2 + a) / t ≤ 1 := by
    rw [← add_div, div_le_one ht0]
    linarith
  have hdl : d * Real.log (t / (2 * Real.pi)) ≤ D * Real.log (t / (2 * Real.pi)) :=
    mul_le_mul_of_nonneg_right hdD hlog0
  have e1 : -D * Real.log (t / (2 * Real.pi)) + 12 * (D + |c|) / t + 4 * (1 / 2 + a) / t
      ≤ 1 + (-d * Real.log (t / (2 * Real.pi))) := by
    rw [neg_mul, neg_mul]
    linarith
  calc _ ≤ Real.exp (1 + (-d * Real.log (t / (2 * Real.pi)))) := Real.exp_le_exp.mpr e1
    _ = Real.exp 1 * (t / (2 * Real.pi)) ^ (-d) := by
        rw [Real.exp_add, exp_neg_mul_log_div_two_pi ht0]
    _ ≤ Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-d)) :=
        mul_le_mul_of_nonneg_left (div_two_pi_rpow_neg_le ht0 (hdD.trans hDR)) (Real.exp_pos 1).le

/-- **Arc bound with `ζ` bounds supplied.**  With `a = x₀ + R cos θ`,
`|G(θ)| ≤ (B/m₀)² exp(−(x₀+R−|a|) log(t/2π) + 12(x₀+R−|a|+|R sin θ|)/t + 4(½+|a|)/t)`. -/
theorem norm_saddleArc_xiSliceShift_le {t x₀ R θ B m₀ : ℝ} (n : ℕ) (ht : 8 ≤ t) (hx₀ : 0 ≤ x₀)
    (hR : 0 ≤ R) (hRt : R ≤ t / 2) (hxR : 1 / 2 < x₀ + R) (hm₀ : 0 < m₀)
    (hz₀ : m₀ ≤ ‖riemannZeta (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖)
    (hz₁ : ‖riemannZeta (((1 / 2 + |x₀ + R * Real.cos θ| : ℝ) : ℂ)
      + ((t + R * Real.sin θ : ℝ) : ℂ) * I)‖ ≤ B)
    (hz₂ : ‖riemannZeta (((1 / 2 + |x₀ + R * Real.cos θ| : ℝ) : ℂ)
      + ((t - R * Real.sin θ : ℝ) : ℂ) * I)‖ ≤ B) :
    ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖
      ≤ (B / m₀) ^ 2 * Real.exp (-(x₀ + R - |x₀ + R * Real.cos θ|) * Real.log (t / (2 * Real.pi))
        + 12 * (x₀ + R - |x₀ + R * Real.cos θ| + |R * Real.sin θ|) / t
        + 4 * (1 / 2 + |x₀ + R * Real.cos θ|) / t) := by
  have hcR : |x₀ + R * Real.cos θ| ≤ x₀ + R := by
    rw [abs_le]
    have h1 := Real.cos_le_one θ
    have h2 := Real.neg_one_le_cos θ
    constructor <;> nlinarith
  have hsin : |R * Real.sin θ| ≤ t / 2 := by
    rw [abs_mul, abs_of_nonneg hR]
    calc R * |Real.sin θ| ≤ R * 1 := by gcongr; exact Real.abs_sin_le_one θ
      _ ≤ t / 2 := by linarith
  have h := norm_xi_split_le ht (abs_nonneg _) hcR hsin hm₀ hz₀ hz₁ hz₂
  have hRe : xiSliceShift t x₀ (R : ℂ) = xiSliceProduct t ((x₀ + R : ℝ) : ℂ) := by
    rw [xiSliceShift]; push_cast; ring_nf
  have hgR : 0 < ‖xi (((1 / 2 + (x₀ + R) : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by rw [re_ofReal_add_ofReal_mul_I]; linarith))
  rw [norm_saddleArc_xiSliceShift, norm_xiSliceShift_arc, hRe, norm_xiSliceProduct_real,
    div_le_iff₀ (by positivity)]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **Arc bound in the Euler region.** -/
theorem norm_shiftArc_le_euler {η R₁ t x₀ R θ d : ℝ} (n : ℕ) (hη : 0 < η)
    (ht : 32 * R₁ + 16 ≤ t) (hx₀ : 0 ≤ x₀) (hR : 0 ≤ R) (hxR : 1 / 2 + 2 * η ≤ x₀ + R)
    (hxR₁ : x₀ + R ≤ R₁) (hE : 1 / 2 + η ≤ |x₀ + R * Real.cos θ|)
    (hd : d ≤ x₀ + R - |x₀ + R * Real.cos θ|) :
    ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖
      ≤ ((1 + 1 / η) / (1 / (1 + 1 / (2 * η)))) ^ 2
        * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-d))) := by
  have hR₁ : 0 ≤ R₁ := by linarith
  have hB : ∀ c : ℝ, ‖riemannZeta (((1 / 2 + |x₀ + R * Real.cos θ| : ℝ) : ℂ)
      + ((t + c : ℝ) : ℂ) * I)‖ ≤ 1 + 1 / η := by
    intro c
    have hre := re_ofReal_add_ofReal_mul_I (1 / 2 + |x₀ + R * Real.cos θ|) (t + c)
    have h := Sieve.norm_riemannZeta_le
      (s := ((1 / 2 + |x₀ + R * Real.cos θ| : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)
      (by rw [hre]; linarith)
    rw [hre] at h
    have : 1 / (1 / 2 + |x₀ + R * Real.cos θ| - 1) ≤ 1 / η :=
      one_div_le_one_div_of_le hη (by linarith)
    linarith
  have hB2 : ‖riemannZeta (((1 / 2 + |x₀ + R * Real.cos θ| : ℝ) : ℂ)
      + ((t - R * Real.sin θ : ℝ) : ℂ) * I)‖ ≤ 1 + 1 / η := by
    have := hB (-(R * Real.sin θ)); rwa [← sub_eq_add_neg] at this
  have hz₀ := inv_le_norm_riemannZeta_saddle t hη hxR
  have h := norm_saddleArc_xiSliceShift_le n (by linarith) hx₀ hR (by linarith) (by linarith)
    (by positivity) hz₀ (hB _) hB2
  have hcR : |x₀ + R * Real.cos θ| ≤ x₀ + R := by
    rw [abs_le]
    have h1 := Real.cos_le_one θ
    have h2 := Real.neg_one_le_cos θ
    constructor <;> nlinarith
  have hsin : |R * Real.sin θ| ≤ R₁ := by
    rw [abs_mul, abs_of_nonneg hR]
    calc R * |Real.sin θ| ≤ R * 1 := by gcongr; exact Real.abs_sin_le_one θ
      _ ≤ R₁ := by linarith
  have habs := abs_nonneg (x₀ + R * Real.cos θ)
  have hexp := exp_shift_decay_le (d := d) (c := R * Real.sin θ) (a := |x₀ + R * Real.cos θ|)
    ht hd (by linarith) (by linarith) hsin (by linarith)
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Arc bound in the strip**, via convexity. -/
theorem norm_shiftArc_le_strip {η R₁ Cc t x₀ R θ : ℝ} (n : ℕ) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hCc : 0 < Cc)
    (hconv : ∀ σ t : ℝ, -η ≤ σ → σ ≤ 1 + η → 8 ≤ t →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Cc * t ^ ((1 + η - σ) / 2))
    (ht : 32 * R₁ + 16 ≤ t) (hx₀ : 0 ≤ x₀) (hR : 0 ≤ R) (hxR : 1 / 2 + 2 * η ≤ x₀ + R)
    (hxR₁ : x₀ + R ≤ R₁) (hS : |x₀ + R * Real.cos θ| < 1 / 2 + η) :
    ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖
      ≤ (Cc / (1 / (1 + 1 / (2 * η)))) ^ 2 * Real.exp 1 * (2 * (2 * Real.pi) ^ R₁ * t ^ (-η)) := by
  have ht0 : 0 < t := by linarith
  have hR₁ : 0 ≤ R₁ := by linarith
  set a : ℝ := |x₀ + R * Real.cos θ| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have hcR : a ≤ x₀ + R := by
    rw [ha, abs_le]
    have h1 := Real.cos_le_one θ
    have h2 := Real.neg_one_le_cos θ
    constructor <;> nlinarith
  have hsinR : |R * Real.sin θ| ≤ R₁ := by
    rw [abs_mul, abs_of_nonneg hR]
    calc R * |Real.sin θ| ≤ R * 1 := by gcongr; exact Real.abs_sin_le_one θ
      _ ≤ R₁ := by linarith
  have hBc : ∀ c : ℝ, |c| ≤ R₁ →
      ‖riemannZeta (((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖
        ≤ Cc * (2 * t) ^ ((1 + η - (1 / 2 + a)) / 2) := by
    intro c hc
    have hc' := abs_le.mp hc
    refine (hconv _ _ (by linarith) (by linarith) (by linarith)).trans ?_
    gcongr
    all_goals linarith
  have hB2 : ‖riemannZeta (((1 / 2 + a : ℝ) : ℂ) + ((t - R * Real.sin θ : ℝ) : ℂ) * I)‖
      ≤ Cc * (2 * t) ^ ((1 + η - (1 / 2 + a)) / 2) := by
    have := hBc (-(R * Real.sin θ)) (by rwa [abs_neg]); rwa [← sub_eq_add_neg] at this
  have hz₀ := inv_le_norm_riemannZeta_saddle t hη hxR
  have h := norm_saddleArc_xiSliceShift_le n (by linarith) hx₀ hR (by linarith) (by linarith)
    (by positivity) hz₀ (hBc _ hsinR) hB2
  rw [← ha] at h
  have hpow : (Cc * (2 * t) ^ ((1 + η - (1 / 2 + a)) / 2) / (1 / (1 + 1 / (2 * η)))) ^ 2
      = (Cc / (1 / (1 + 1 / (2 * η)))) ^ 2 * (2 * t) ^ (1 / 2 + η - a) := by
    rw [div_pow, mul_pow, ← Real.rpow_natCast ((2 * t) ^ _), ← Real.rpow_mul (by positivity)]
    push_cast
    rw [show (1 + η - (1 / 2 + a)) / 2 * 2 = 1 / 2 + η - a by ring]
    ring
  have hexpX := exp_shift_decay_le (d := x₀ + R - a) (c := R * Real.sin θ) (a := a) ht le_rfl
    (by linarith) (by linarith) hsinR (by linarith)
  have hkey : (2 * t) ^ (1 / 2 + η - a) * t ^ (-(x₀ + R - a)) ≤ 2 * t ^ (-η) := by
    rw [Real.mul_rpow (by norm_num) ht0.le, mul_assoc, ← Real.rpow_add ht0]
    have h2 : (2 : ℝ) ^ (1 / 2 + η - a) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 2 + η - a) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 2 := Real.rpow_one 2
    have h4 : t ^ (1 / 2 + η - a + -(x₀ + R - a)) ≤ t ^ (-η) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    exact mul_le_mul h2 h4 (by positivity) (by norm_num)
  refine h.trans ?_
  rw [hpow]
  calc (Cc / (1 / (1 + 1 / (2 * η)))) ^ 2 * (2 * t) ^ (1 / 2 + η - a)
        * Real.exp (-(x₀ + R - a) * Real.log (t / (2 * Real.pi))
          + 12 * (x₀ + R - a + |R * Real.sin θ|) / t + 4 * (1 / 2 + a) / t)
      ≤ (Cc / (1 / (1 + 1 / (2 * η)))) ^ 2 * (2 * t) ^ (1 / 2 + η - a)
        * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-(x₀ + R - a)))) :=
        mul_le_mul_of_nonneg_left hexpX (by positivity)
    _ = (Cc / (1 / (1 + 1 / (2 * η)))) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
        * ((2 * t) ^ (1 / 2 + η - a) * t ^ (-(x₀ + R - a))) := by ring
    _ ≤ (Cc / (1 / (1 + 1 / (2 * η)))) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
        * (2 * t ^ (-η)) := mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by ring

/-- The decay exponent beyond `θ₁`: `min(Rθ₁²/5, 2x₀) ≤ x₀ + R − |x₀ + R cos θ|` for
`θ₁ ≤ θ ≤ π`. -/
theorem min_le_shift_decay {x₀ R θ₁ θ : ℝ} (hR : 0 ≤ R) (hθ₁ : 0 < θ₁)
    (hθ : θ₁ ≤ θ) (hθπ : θ ≤ Real.pi) :
    min (R * θ₁ ^ 2 / 5) (2 * x₀) ≤ x₀ + R - |x₀ + R * Real.cos θ| := by
  rcases le_or_gt 0 (x₀ + R * Real.cos θ) with ha | ha
  · rw [abs_of_nonneg ha]
    refine (min_le_left _ _).trans ?_
    have hc5 := one_sub_cos_ge_sq_div_five (θ := θ₁) (by rw [abs_of_pos hθ₁]; linarith)
    have hcos : Real.cos θ ≤ Real.cos θ₁ :=
      Real.cos_le_cos_of_nonneg_of_le_pi hθ₁.le hθπ hθ
    nlinarith
  · rw [abs_of_neg ha]
    refine (min_le_right _ _).trans ?_
    have := Real.neg_one_le_cos θ
    nlinarith

/-- **Tail of the shifted arc.**  For `0 < η ≤ 1/4` there is `A` such that, whenever
`t ≥ 32R₁ + 16`, `x₀, R ≥ 0`, `½ + 2η ≤ x₀ + R ≤ R₁` and `0 ≤ d ≤ x₀ + R − |x₀ + R cos θ|`,
`|G(θ)| ≤ A (t^{−η} + t^{−d})`, uniformly in the order. -/
theorem exists_shiftArc_tail_le {η R₁ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4) :
    ∃ A : ℝ, 0 < A ∧ ∀ (t x₀ R θ d : ℝ) (n : ℕ), 32 * R₁ + 16 ≤ t → 0 ≤ x₀ → 0 ≤ R →
      1 / 2 + 2 * η ≤ x₀ + R → x₀ + R ≤ R₁ → d ≤ x₀ + R - |x₀ + R * Real.cos θ| →
      ‖HTGeometry.saddleArc (xiSliceShift t x₀) R n θ‖ ≤ A * (t ^ (-η) + t ^ (-d)) := by
  obtain ⟨Cc, hCc, hconv⟩ := exists_norm_riemannZeta_le_convexity (η := η) hη (by linarith)
  set m₀ : ℝ := 1 / (1 + 1 / (2 * η)) with hm₀
  have hm₀0 : 0 < m₀ := by rw [hm₀]; positivity
  refine ⟨Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * ((Cc + 1 + 1 / η) / m₀) ^ 2, ?_, ?_⟩
  · have : 0 < (2 * Real.pi) ^ R₁ := Real.rpow_pos_of_pos (by positivity) _
    positivity
  intro t x₀ R θ d n ht hx₀ hR hxR hxR₁ hd
  have ht0 : 0 < t := by linarith
  have htη : 0 ≤ t ^ (-η) := Real.rpow_nonneg ht0.le _
  have htd : 0 ≤ t ^ (-d) := Real.rpow_nonneg ht0.le _
  have hq : 0 < (2 * Real.pi) ^ R₁ := Real.rpow_pos_of_pos (by positivity) _
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  rcases le_or_gt (1 / 2 + η) |x₀ + R * Real.cos θ| with hE | hS
  · have h := norm_shiftArc_le_euler n hη ht hx₀ hR hxR hxR₁ hE hd
    rw [← hm₀] at h
    have hBm : ((1 + 1 / η) / m₀) ^ 2 ≤ ((Cc + 1 + 1 / η) / m₀) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (by linarith) hm₀0.le) 2
    refine h.trans ?_
    calc ((1 + 1 / η) / m₀) ^ 2 * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-d)))
        ≤ ((Cc + 1 + 1 / η) / m₀) ^ 2 * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-d))) :=
          mul_le_mul_of_nonneg_right hBm (by positivity)
      _ ≤ _ := by
          have key : Real.exp 1 * (2 * (2 * Real.pi) ^ R₁) * ((Cc + 1 + 1 / η) / m₀) ^ 2
                * (t ^ (-η) + t ^ (-d))
              = ((Cc + 1 + 1 / η) / m₀) ^ 2 * (Real.exp 1 * ((2 * Real.pi) ^ R₁ * t ^ (-d)))
                + ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1 * (2 * Real.pi) ^ R₁
                  * (2 * t ^ (-η) + t ^ (-d)) := by ring
          rw [key]
          exact le_add_of_nonneg_right (by positivity)
  · have h := norm_shiftArc_le_strip n hη (by linarith) hCc hconv ht hx₀ hR hxR hxR₁ hS
    rw [← hm₀] at h
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
                * (t ^ (-η) + t ^ (-d))
              = ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1 * (2 * (2 * Real.pi) ^ R₁ * t ^ (-η))
                + ((Cc + 1 + 1 / η) / m₀) ^ 2 * Real.exp 1
                  * (2 * (2 * Real.pi) ^ R₁ * t ^ (-d)) := by ring
          rw [key]
          exact le_add_of_nonneg_right (by positivity)

end

end RHTower
