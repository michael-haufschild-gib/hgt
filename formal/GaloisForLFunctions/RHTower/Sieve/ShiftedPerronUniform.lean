import GaloisForLFunctions.RHTower.Sieve.ShiftedPerronHalfPlane
import GaloisForLFunctions.RHTower.Sieve.PerronErrorTotalChebyshev
import GaloisForLFunctions.RHTower.Sieve.PerronVerticalLogBound

/-!
# Height-uniform convergence of the von Mangoldt series right of a Xi frontier

Let every Xi zero satisfy `Re ρ ≤ ½ + α`, and fix `½ + α < σ₁ < 1` and `η > 0`.  Then for every
`s₀` with `σ₁ + η ≤ Re s₀ < 9/8`, `s₀ ≠ 1`, and every `N ≥ 1`, with `x = N + ½`,

`|Σ_{n≤N} Λ(n) n^{−s₀} − x^{1−s₀}/(1−s₀) + ζ'/ζ(s₀)| ≤ K · x^{σ₁ − Re s₀} · (1 + log(x + |Im s₀| + 9))²`

with `K` depending only on `α, σ₁, η` (`exists_norm_shiftedChebyshev_sub_le_uniform`).

So the Dirichlet series of `−ζ'/ζ`, corrected by its pole term, converges at every point right of
the frontier, with a power saving `x^{σ₁ − Re s₀}` and a loss only logarithmic in the height of
`s₀`.  The proof bounds the three pieces of the shifted master inequality
(`norm_shiftedChebyshev_sub_le`) at height `T = x + |Im s₀| + 7`:

* the truncation error is `x^{−Re s₀}` times the untwisted error at abscissa `9/8`;
* the left edge carries `ζ'/ζ` on the line `Re = σ₁`, bounded by `K₁(1 + log(2 + |t|))`, against
  `∫ dy/|a + iy| ≤ 2(1 + log(1 + T/|a|))`;
* the horizontal edges carry the frontier bound `C log|γ|/(σ − ½ − α)` against `x^c/T`.
-/

open Complex ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-- The shifted truncation error is `x^{−Re s₀}` times the untwisted one at abscissa `Re s₀ + c`. -/
theorem shiftedTruncation_eq {s₀ : ℂ} {x c T : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, ‖shiftedVonMangoldt s₀ n‖ *
        ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|)))
      = x ^ (-s₀.re) * ∑' n : ℕ, ‖((Λ n : ℝ) : ℂ)‖ *
        ((x / n) ^ (s₀.re + c) / (Real.pi * T * |Real.log (x / n)|)) := by
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [norm_shiftedVonMangoldt, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (0 : ℝ) < x ^ s₀.re := Real.rpow_pos_of_pos hx _
    have h2 : (0 : ℝ) < (n : ℝ) ^ s₀.re := Real.rpow_pos_of_pos hn0 _
    rw [Real.div_rpow hx.le hn0.le, Real.div_rpow hx.le hn0.le, Real.rpow_add hx,
      Real.rpow_add hn0, Real.rpow_neg hn0.le, Real.rpow_neg hx.le]
    field_simp

/-- **The left edge.**  On `Re w = σ₁ − Re s₀` the shifted integrand is `ζ'/ζ` on the line
`Re = σ₁` times `x^w/w`. -/
theorem norm_vIntegral_shiftedPerron_left_le {s₀ : ℂ} {x σ₁ T K₁ : ℝ} (hx : 0 < x)
    (hσ : σ₁ < s₀.re) (hT : 0 ≤ T) (hK₁0 : 0 ≤ K₁)
    (hK₁ : ∀ t : ℝ, ‖logDeriv riemannZeta ((σ₁ : ℂ) + (t : ℂ) * I)‖
      ≤ K₁ * (1 + Real.log (2 + |t|))) :
    ‖VIntegral (shiftedPerronIntegrand s₀ x) (σ₁ - s₀.re) (-T) T‖
      ≤ K₁ * (1 + Real.log (2 + |s₀.im| + T)) * x ^ (σ₁ - s₀.re) *
        (2 * (1 + Real.log (1 + T / (s₀.re - σ₁)))) := by
  set d := s₀.re - σ₁ with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set B := K₁ * (1 + Real.log (2 + |s₀.im| + T)) * x ^ (σ₁ - s₀.re) with hB
  have hlogT : 0 ≤ Real.log (2 + |s₀.im| + T) :=
    Real.log_nonneg (by linarith [abs_nonneg s₀.im])
  have hB0 : 0 ≤ B := by
    have : 0 ≤ x ^ (σ₁ - s₀.re) := Real.rpow_nonneg hx.le _
    rw [hB]; positivity
  have hpt : ∀ y ∈ Set.Ioc (-T) T,
      ‖shiftedPerronIntegrand s₀ x (((σ₁ - s₀.re : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ B * (1 / ‖(d : ℂ) + (y : ℝ) * I‖) := by
    intro y hy
    have hyT : |y| ≤ T := abs_le.mpr ⟨hy.1.le, hy.2⟩
    have hpt_eq : s₀ + (((σ₁ - s₀.re : ℝ) : ℂ) + (y : ℂ) * I)
        = (σ₁ : ℂ) + ((s₀.im + y : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have hre : ((((σ₁ - s₀.re : ℝ) : ℂ) + (y : ℂ) * I)).re = σ₁ - s₀.re := by simp
    have hnorm : ‖(((σ₁ - s₀.re : ℝ) : ℂ) + (y : ℂ) * I)‖ = ‖(d : ℂ) + (y : ℝ) * I‖ := by
      rw [Complex.norm_add_mul_I, Complex.norm_add_mul_I, hd]
      congr 1
      ring
    rw [shiftedPerronIntegrand, hpt_eq, norm_mul, norm_div ((x : ℂ) ^ _),
      Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, hnorm]
    have hlog : ‖-deriv riemannZeta ((σ₁ : ℂ) + ((s₀.im + y : ℝ) : ℂ) * I) /
        riemannZeta ((σ₁ : ℂ) + ((s₀.im + y : ℝ) : ℂ) * I)‖
          ≤ K₁ * (1 + Real.log (2 + |s₀.im| + T)) := by
      rw [neg_div, norm_neg, ← logDeriv_apply]
      refine (hK₁ (s₀.im + y)).trans ?_
      have habs := abs_add_le s₀.im y
      have hl : Real.log (2 + |s₀.im + y|) ≤ Real.log (2 + |s₀.im| + T) :=
        Real.log_le_log (by positivity) (by linarith)
      exact mul_le_mul_of_nonneg_left (by linarith) hK₁0
    have hq : 0 ≤ x ^ (σ₁ - s₀.re) / ‖(d : ℂ) + (y : ℝ) * I‖ := by
      have : 0 ≤ x ^ (σ₁ - s₀.re) := Real.rpow_nonneg hx.le _
      positivity
    calc _ ≤ K₁ * (1 + Real.log (2 + |s₀.im| + T)) *
          (x ^ (σ₁ - s₀.re) / ‖(d : ℂ) + (y : ℝ) * I‖) := mul_le_mul_of_nonneg_right hlog hq
      _ = B * (1 / ‖(d : ℂ) + (y : ℝ) * I‖) := by rw [hB]; ring
  have hint : IntervalIntegrable (fun y : ℝ => B * (1 / ‖(d : ℂ) + (y : ℝ) * I‖))
      MeasureTheory.volume (-T) T :=
    ((continuous_inv_norm_line hd0).const_mul B).intervalIntegrable _ _
  rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
  refine (intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    (Filter.Eventually.of_forall fun y hy => hpt y hy) hint).trans ?_
  rw [intervalIntegral.integral_const_mul]
  calc B * ∫ y in (-T)..T, 1 / ‖(d : ℂ) + (y : ℝ) * I‖
      ≤ B * (2 * (1 + Real.log (1 + T / d))) :=
        mul_le_mul_of_nonneg_left (integral_symm_inv_norm_line_le hd0 hT) hB0
    _ = _ := by rw [hB]

/-- **A horizontal edge.**  At height `y` the shifted integrand carries `ζ'/ζ` at height
`Im s₀ + y`, bounded through the frontier estimate. -/
theorem norm_hIntegral_shiftedPerron_le {alpha : ℝ} {s₀ : ℂ} {x σ₁ c y C : ℝ} (hx : 1 ≤ x)
    (hσ₁ : 1 / 2 + alpha < σ₁) (hc : s₀.re + c ≤ 9 / 8) (hac : σ₁ - s₀.re ≤ c)
    (hy7 : 7 ≤ |s₀.im + y|) (hy2 : |s₀.im + y| ≤ 2 * |y|) (hC0 : 0 < C)
    (hC : ∀ sigma gamma : ℝ, 7 ≤ |gamma| → 1 / 2 + alpha < sigma → sigma ≤ 9 / 8 →
      ‖logDeriv riemannZeta ((sigma : ℂ) + (gamma : ℂ) * I)‖
        ≤ C * Real.log |gamma| / (sigma - (1 / 2 + alpha))) :
    ‖HIntegral (shiftedPerronIntegrand s₀ x) (σ₁ - s₀.re) c y‖
      ≤ (C * Real.log (2 * |y|) / (σ₁ - (1 / 2 + alpha))) * (x ^ c / |y|) *
        |c - (σ₁ - s₀.re)| := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < |y| := by linarith
  rw [HIntegral]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
  rw [Set.uIoc_of_le hac] at hu
  have hpt_eq : s₀ + ((u : ℂ) + (y : ℂ) * I)
      = ((s₀.re + u : ℝ) : ℂ) + ((s₀.im + y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hre : (((u : ℂ) + (y : ℂ) * I)).re = u := by simp
  rw [shiftedPerronIntegrand, hpt_eq, norm_mul, norm_div ((x : ℂ) ^ _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, hre]
  have hsig1 : 1 / 2 + alpha < s₀.re + u := by linarith [hu.1]
  have hsig2 : s₀.re + u ≤ 9 / 8 := by linarith [hu.2]
  have hlogd := hC (s₀.re + u) (s₀.im + y) hy7 hsig1 hsig2
  have hl0 : 0 ≤ Real.log |s₀.im + y| := Real.log_nonneg (by linarith)
  have hl : Real.log |s₀.im + y| ≤ Real.log (2 * |y|) := Real.log_le_log (by linarith) hy2
  have hlog1 : ‖-deriv riemannZeta (((s₀.re + u : ℝ) : ℂ) + ((s₀.im + y : ℝ) : ℂ) * I) /
      riemannZeta (((s₀.re + u : ℝ) : ℂ) + ((s₀.im + y : ℝ) : ℂ) * I)‖
        ≤ C * Real.log (2 * |y|) / (σ₁ - (1 / 2 + alpha)) := by
    rw [neg_div, norm_neg, ← logDeriv_apply]
    refine hlogd.trans ?_
    exact div_le_div₀ (by have := hl0.trans hl; positivity)
      (mul_le_mul_of_nonneg_left hl hC0.le) (by linarith) (by linarith [hu.1])
  have hxu : x ^ u ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx hu.2
  have hden : |y| ≤ ‖(u : ℂ) + (y : ℂ) * I‖ := abs_le_norm_sigma_add_mul_I
  have hq : x ^ u / ‖(u : ℂ) + (y : ℂ) * I‖ ≤ x ^ c / |y| := by
    have hxu0 : 0 ≤ x ^ u := Real.rpow_nonneg hx0.le _
    calc x ^ u / ‖(u : ℂ) + (y : ℂ) * I‖ ≤ x ^ u / |y| :=
          div_le_div_of_nonneg_left hxu0 hy0 hden
      _ ≤ x ^ c / |y| := div_le_div_of_nonneg_right hxu hy0.le
  have hq0 : 0 ≤ x ^ u / ‖(u : ℂ) + (y : ℂ) * I‖ := by
    have : 0 ≤ x ^ u := Real.rpow_nonneg hx0.le _
    positivity
  have hR0 : 0 ≤ C * Real.log (2 * |y|) / (σ₁ - (1 / 2 + alpha)) := by
    have := hl0.trans hl
    have : 0 < σ₁ - (1 / 2 + alpha) := by linarith
    positivity
  exact mul_le_mul hlog1 hq hq0 hR0

/-- `log a ≤ log k + log b` whenever `0 < a ≤ k b` and `k > 0`. -/
theorem log_le_log_add_of_le_mul {a b k : ℝ} (ha : 0 < a) (hk : 0 < k) (hab : a ≤ k * b) :
    Real.log a ≤ Real.log k + Real.log b := by
  have hb : 0 < b := by
    by_contra h
    push Not at h
    nlinarith
  rw [← Real.log_mul hk.ne' hb.ne']
  exact Real.log_le_log ha hab

/-- The logarithmic comparisons at height `T = x + t + 7` against `L = 1 + log(x + t + 9)`. -/
theorem shifted_log_bounds {x t T X : ℝ} (hx : 1 ≤ x) (ht : 0 ≤ t) (hT : T = x + t + 7)
    (hX : X = x + t + 9) :
    Real.log (2 * T) ≤ 1 + Real.log X ∧ Real.log (2 * x) ≤ 1 + Real.log X ∧
      1 + Real.log (2 * x + 1) ≤ 3 * (1 + Real.log X) ∧
      1 + Real.log (2 + t + T) ≤ 2 * (1 + Real.log X) := by
  have hlog2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have h1 := log_le_log_add_of_le_mul (by linarith) (by norm_num : (0 : ℝ) < 2)
    (show 2 * T ≤ 2 * X by linarith)
  have h2 := log_le_log_add_of_le_mul (by linarith) (by norm_num : (0 : ℝ) < 2)
    (show 2 * x ≤ 2 * X by linarith)
  have h3 := log_le_log_add_of_le_mul (by linarith) (by norm_num : (0 : ℝ) < 3)
    (show 2 * x + 1 ≤ 3 * X by linarith)
  have h4 := log_le_log_add_of_le_mul (by linarith) (by norm_num : (0 : ℝ) < 2)
    (show 2 + t + T ≤ 2 * X by linarith)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The width logarithm `1 + log(1 + T/d)` with `d ≥ η` against `L = 1 + log X`, `X ≥ T`. -/
theorem shifted_log_bound_width {T X d η : ℝ} (hT : 0 ≤ T) (hTX : T ≤ X) (hX1 : 1 ≤ X)
    (hη : 0 < η) (hd : η ≤ d) :
    1 + Real.log (1 + T / d) ≤ (1 + Real.log (1 + 1 / η)) * (1 + Real.log X) := by
  have hd0 : 0 < d := lt_of_lt_of_le hη hd
  have h1 : T / d ≤ T / η := div_le_div_of_nonneg_left hT hη hd
  have h2 : T / η ≤ X / η := div_le_div_of_nonneg_right hTX hη.le
  have h3 : (1 + 1 / η) * X = X + X / η := by ring
  have h4 : 1 + T / d ≤ (1 + 1 / η) * X := by rw [h3]; linarith
  have hTd : 0 ≤ T / d := div_nonneg hT hd0.le
  have h5 := log_le_log_add_of_le_mul (by linarith) (by positivity) h4
  have hℓ0 : 0 ≤ Real.log (1 + 1 / η) :=
    Real.log_nonneg (by have : 0 < 1 / η := by positivity
                        linarith)
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  nlinarith [mul_nonneg hℓ0 hlX]

/-- The power comparisons at height `T ≥ x`. -/
theorem shifted_pow_bounds {x T σ σ₁ : ℝ} (hx : 1 ≤ x) (hxT : x ≤ T) (hσ₁ : 1 / 8 ≤ σ₁) :
    x ^ ((9 : ℝ) / 8 - σ) / T ≤ x ^ (σ₁ - σ) ∧ x ^ (-σ) ≤ x ^ (σ₁ - σ) := by
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  refine ⟨?_, Real.rpow_le_rpow_of_exponent_le hx (by linarith)⟩
  rw [div_le_iff₀ hT0]
  have hsplit : x ^ ((9 : ℝ) / 8 - σ) = x ^ (σ₁ - σ) * x ^ ((9 : ℝ) / 8 - σ₁) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0.le _)
  calc x ^ ((9 : ℝ) / 8 - σ₁) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    _ = x := Real.rpow_one x
    _ ≤ T := hxT

/-- **The truncation error, uniformly.**  At height `T ≥ x = N + ½` the shifted truncation error
with `c = 9/8 − Re s₀` is at most `A · x^{σ₁ − Re s₀} L²`. -/
theorem shiftedTruncation_le_uniform {s₀ : ℂ} {N : ℕ} (hN : 1 ≤ N) {x σ₁ T L : ℝ}
    (hxdef : x = (N : ℝ) + 1 / 2) (hσ₁ : 1 / 8 ≤ σ₁) (hT : x ≤ T) (hL1 : 1 ≤ L)
    (hlog2x : Real.log (2 * x) ≤ L) (hlogN : 1 + Real.log (2 * x + 1) ≤ 3 * L) :
    (∑' n : ℕ, ‖shiftedVonMangoldt s₀ n‖ *
        ((x / n) ^ (9 / 8 - s₀.re) / (Real.pi * T * |Real.log (x / n)|)))
      ≤ (512 / (Real.pi * Real.log 2) + 192 / Real.pi) * (x ^ (σ₁ - s₀.re) * L ^ 2) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 ≤ x := by rw [hxdef]; linarith
  have hx0 : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  have htot := perron_error_vonMangoldt_total_le (N := N) (σ := 9 / 8) (T := T) hN
    (by norm_num) (by norm_num) hT0
  have hcast : ((2 * N + 2 : ℕ) : ℝ) = 2 * x + 1 := by rw [hxdef]; push_cast; ring
  rw [show (8 / ((9 : ℝ) / 8 - 1) ^ 2) = 512 by norm_num, hcast, ← hxdef] at htot
  rw [shiftedTruncation_eq hx0, show s₀.re + (9 / 8 - s₀.re) = (9 : ℝ) / 8 by ring]
  obtain ⟨hpowT, hneg⟩ := shifted_pow_bounds (σ := s₀.re) hx1 hT hσ₁
  set P := x ^ (σ₁ - s₀.re) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg hx0.le _
  have hneg0 : 0 ≤ x ^ (-s₀.re) := Real.rpow_nonneg hx0.le _
  have hlog2x0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hlogN0 : 0 ≤ 1 + Real.log (2 * x + 1) := by
    have : 0 ≤ Real.log (2 * x + 1) := Real.log_nonneg (by linarith)
    linarith
  have hR1 : x ^ (-s₀.re) * ((1 / (Real.pi * T * Real.log 2)) * (x ^ ((9 : ℝ) / 8) * 512))
      ≤ 512 / (Real.pi * Real.log 2) * P := by
    have heq : x ^ (-s₀.re) * ((1 / (Real.pi * T * Real.log 2)) * (x ^ ((9 : ℝ) / 8) * 512))
        = 512 / (Real.pi * Real.log 2) * (x ^ ((9 : ℝ) / 8 - s₀.re) / T) := by
      rw [show (9 : ℝ) / 8 - s₀.re = -s₀.re + 9 / 8 by ring, Real.rpow_add hx0]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hpowT (by positivity)
  have hR2 : x ^ (-s₀.re) * ((16 * Real.log (2 * x) * x / (Real.pi * T)) *
        (4 * (1 + Real.log (2 * x + 1)))) ≤ 192 / Real.pi * (P * L ^ 2) := by
    have hxT' : x / T ≤ 1 := (div_le_one hT0).mpr hT
    have heq : x ^ (-s₀.re) * ((16 * Real.log (2 * x) * x / (Real.pi * T)) *
          (4 * (1 + Real.log (2 * x + 1))))
        = 64 / Real.pi * (Real.log (2 * x) * (1 + Real.log (2 * x + 1))) *
          (x ^ (-s₀.re) * (x / T)) := by ring
    rw [heq]
    have hprod : Real.log (2 * x) * (1 + Real.log (2 * x + 1)) ≤ L * (3 * L) :=
      mul_le_mul hlog2x hlogN hlogN0 (by linarith)
    have hxx : x ^ (-s₀.re) * (x / T) ≤ P :=
      (mul_le_of_le_one_right hneg0 hxT').trans hneg
    have hxx0 : 0 ≤ x ^ (-s₀.re) * (x / T) := mul_nonneg hneg0 (div_nonneg hx0.le hT0.le)
    have hLL : 0 ≤ L * (3 * L) := mul_nonneg (by linarith) (by linarith)
    calc 64 / Real.pi * (Real.log (2 * x) * (1 + Real.log (2 * x + 1))) *
          (x ^ (-s₀.re) * (x / T))
        ≤ 64 / Real.pi * (L * (3 * L)) * P :=
          mul_le_mul (mul_le_mul_of_nonneg_left hprod (by positivity)) hxx hxx0
            (mul_nonneg (by positivity) hLL)
      _ = 192 / Real.pi * (P * L ^ 2) := by ring
  have hPQ : P ≤ P * L ^ 2 := le_mul_of_one_le_right hP0 (by nlinarith)
  calc x ^ (-s₀.re) * (∑' n : ℕ, ‖((Λ n : ℝ) : ℂ)‖ *
        ((x / n) ^ ((9 : ℝ) / 8) / (Real.pi * T * |Real.log (x / n)|)))
      ≤ x ^ (-s₀.re) * ((1 / (Real.pi * T * Real.log 2)) * (x ^ ((9 : ℝ) / 8) * 512)
        + (16 * Real.log (2 * x) * x / (Real.pi * T)) * (4 * (1 + Real.log (2 * x + 1)))) :=
        mul_le_mul_of_nonneg_left htot hneg0
    _ ≤ 512 / (Real.pi * Real.log 2) * P + 192 / Real.pi * (P * L ^ 2) := by
        rw [mul_add]; exact add_le_add hR1 hR2
    _ ≤ (512 / (Real.pi * Real.log 2) + 192 / Real.pi) * (P * L ^ 2) := by
        have := mul_le_mul_of_nonneg_left hPQ (by positivity : 0 ≤ 512 / (Real.pi * Real.log 2))
        rw [add_mul]; linarith

/-- **The left edge, uniformly**, at height `T = x + |Im s₀| + 7`. -/
theorem norm_vIntegral_shiftedPerron_left_le_uniform {s₀ : ℂ} {x σ₁ η T X K₁ : ℝ} (hx : 1 ≤ x)
    (hη : 0 < η) (hs₀ : σ₁ + η ≤ s₀.re) (hTdef : T = x + |s₀.im| + 7)
    (hXdef : X = x + |s₀.im| + 9) (hK₁0 : 0 ≤ K₁)
    (hK₁ : ∀ t : ℝ, ‖logDeriv riemannZeta ((σ₁ : ℂ) + (t : ℂ) * I)‖
      ≤ K₁ * (1 + Real.log (2 + |t|))) :
    ‖VIntegral (shiftedPerronIntegrand s₀ x) (σ₁ - s₀.re) (-T) T‖
      ≤ 4 * K₁ * (1 + Real.log (1 + 1 / η)) * (x ^ (σ₁ - s₀.re) * (1 + Real.log X) ^ 2) := by
  have habs0 := abs_nonneg s₀.im
  have hT0 : 0 ≤ T := by linarith
  have hV := norm_vIntegral_shiftedPerron_left_le (s₀ := s₀) (x := x) (σ₁ := σ₁) (T := T)
    (by linarith) (by linarith) hT0 hK₁0 hK₁
  obtain ⟨-, -, -, hlogV⟩ := shifted_log_bounds hx habs0 hTdef hXdef
  have hlogW := shifted_log_bound_width (X := X) (d := s₀.re - σ₁) hT0 (by linarith) (by linarith) hη
    (by linarith)
  refine hV.trans ?_
  have hP0 : 0 ≤ x ^ (σ₁ - s₀.re) := Real.rpow_nonneg (by linarith) _
  have hL1 : 1 ≤ 1 + Real.log X := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ X by linarith); linarith
  have ha2 : 0 ≤ 1 + Real.log (1 + T / (s₀.re - σ₁)) := by
    have : 0 ≤ T / (s₀.re - σ₁) := div_nonneg hT0 (by linarith)
    have := Real.log_nonneg (show (1 : ℝ) ≤ 1 + T / (s₀.re - σ₁) by linarith)
    linarith
  calc K₁ * (1 + Real.log (2 + |s₀.im| + T)) * x ^ (σ₁ - s₀.re) *
        (2 * (1 + Real.log (1 + T / (s₀.re - σ₁))))
      ≤ K₁ * (2 * (1 + Real.log X)) * x ^ (σ₁ - s₀.re) *
        (2 * ((1 + Real.log (1 + 1 / η)) * (1 + Real.log X))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogV hK₁0) hP0)
          (by linarith) (by linarith)
          (mul_nonneg (mul_nonneg hK₁0 (by linarith)) hP0)
    _ = _ := by ring

/-- **A horizontal edge, uniformly**, at height `|y| = T = x + |Im s₀| + 7`. -/
theorem norm_hIntegral_shiftedPerron_le_uniform {alpha : ℝ} {s₀ : ℂ} {x σ₁ T X y C : ℝ}
    (hx : 1 ≤ x) (halpha : 0 ≤ alpha) (hσ₁ : 1 / 2 + alpha < σ₁) (hσ₁1 : σ₁ < 1)
    (hTdef : T = x + |s₀.im| + 7) (hXdef : X = x + |s₀.im| + 9) (hy : |y| = T)
    (hy7 : 7 ≤ |s₀.im + y|) (hy2 : |s₀.im + y| ≤ 2 * |y|) (hC0 : 0 < C)
    (hC : ∀ sigma gamma : ℝ, 7 ≤ |gamma| → 1 / 2 + alpha < sigma → sigma ≤ 9 / 8 →
      ‖logDeriv riemannZeta ((sigma : ℂ) + (gamma : ℂ) * I)‖
        ≤ C * Real.log |gamma| / (sigma - (1 / 2 + alpha))) :
    ‖HIntegral (shiftedPerronIntegrand s₀ x) (σ₁ - s₀.re) (9 / 8 - s₀.re) y‖
      ≤ C / (σ₁ - (1 / 2 + alpha)) * (x ^ (σ₁ - s₀.re) * (1 + Real.log X) ^ 2) := by
  have habs0 := abs_nonneg s₀.im
  have hgap : 0 < σ₁ - (1 / 2 + alpha) := by linarith
  have h := norm_hIntegral_shiftedPerron_le (alpha := alpha) (s₀ := s₀) (x := x) (σ₁ := σ₁)
    (c := 9 / 8 - s₀.re) (y := y) (C := C) hx hσ₁ (by linarith) (by linarith) hy7 hy2 hC0 hC
  rw [hy, show |9 / 8 - s₀.re - (σ₁ - s₀.re)| = 9 / 8 - σ₁ by
    rw [show 9 / 8 - s₀.re - (σ₁ - s₀.re) = 9 / 8 - σ₁ by ring]
    exact abs_of_nonneg (by linarith)] at h
  refine h.trans ?_
  have hxT : x ≤ T := by linarith
  obtain ⟨hlog2T, -, -, -⟩ := shifted_log_bounds hx habs0 hTdef hXdef
  obtain ⟨hpowT, -⟩ := shifted_pow_bounds (σ := s₀.re) hx hxT (show 1 / 8 ≤ σ₁ by linarith)
  have hP0 : 0 ≤ x ^ (σ₁ - s₀.re) := Real.rpow_nonneg (by linarith) _
  have hL1 : 1 ≤ 1 + Real.log X := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ X by linarith); linarith
  have hlogT0 : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  calc C * Real.log (2 * T) / (σ₁ - (1 / 2 + alpha)) * (x ^ ((9 : ℝ) / 8 - s₀.re) / T) *
        (9 / 8 - σ₁)
      ≤ C * (1 + Real.log X) / (σ₁ - (1 / 2 + alpha)) * x ^ (σ₁ - s₀.re) * 1 := by
        refine mul_le_mul (mul_le_mul ?_ hpowT
          (div_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith)) ?_) (by linarith)
          (by linarith) ?_
        · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog2T hC0.le) hgap.le
        · have : 0 ≤ 1 + Real.log X := by linarith
          positivity
        · have : 0 ≤ 1 + Real.log X := by linarith
          positivity
    _ = C / (σ₁ - (1 / 2 + alpha)) * (x ^ (σ₁ - s₀.re) * (1 + Real.log X)) := by ring
    _ ≤ C / (σ₁ - (1 / 2 + alpha)) * (x ^ (σ₁ - s₀.re) * (1 + Real.log X) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hP0) (by positivity)
        nlinarith

/-- **Height-uniform convergence of the von Mangoldt series right of a Xi frontier.** -/
theorem exists_norm_shiftedChebyshev_sub_le_uniform {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hXi : XiZeroHalfPlaneBound alpha) {σ₁ η : ℝ} (hσ₁ : 1 / 2 + alpha < σ₁) (hσ₁1 : σ₁ < 1)
    (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ s₀ : ℂ, σ₁ + η ≤ s₀.re → s₀.re < 9 / 8 → s₀ ≠ 1 →
      ∀ N : ℕ, 1 ≤ N →
        ‖(∑ n ∈ Finset.Icc 1 N, shiftedVonMangoldt s₀ n)
            - ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) ^ (1 - s₀) / (1 - s₀)
              + -deriv riemannZeta s₀ / riemannZeta s₀)‖
          ≤ K * (((N : ℝ) + 1 / 2) ^ (σ₁ - s₀.re) *
            (1 + Real.log ((N : ℝ) + 1 / 2 + |s₀.im| + 9)) ^ 2) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ :=
    exists_logDeriv_zeta_line_bound_of_xiZeroHalfPlaneBound halpha hXi hσ₁ hσ₁1
  obtain ⟨C, hC0, hC⟩ := exists_logDeriv_zeta_bound_of_xiZeroHalfPlaneBound halpha hXi
  have hpi : 0 < Real.pi := Real.pi_pos
  have hgap : 0 < σ₁ - (1 / 2 + alpha) := by linarith
  have hℓ0 : 0 ≤ Real.log (1 + 1 / η) :=
    Real.log_nonneg (by have : 0 < 1 / η := by positivity
                        linarith)
  refine ⟨(512 / (Real.pi * Real.log 2) + 192 / Real.pi) + 1 / (2 * Real.pi) *
      (4 * K₁ * (1 + Real.log (1 + 1 / η)) + 2 * (C / (σ₁ - (1 / 2 + alpha)))),
    by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity, ?_⟩
  intro s₀ hs₀ hs₀' hs₀1 N hN
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (N : ℝ) + 1 / 2 := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = x + |s₀.im| + 7 := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = x + |s₀.im| + 9 := ⟨_, rfl⟩
  rw [← hxdef, ← hXdef]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 ≤ x := by rw [hxdef]; linarith
  have habs0 := abs_nonneg s₀.im
  have hT0 : 0 < T := by linarith
  have hTim : |s₀.im| < T := by linarith
  obtain ⟨-, hlog2x, hlogN, -⟩ := shifted_log_bounds hx1 habs0 hTdef hXdef
  have hL1 : 1 ≤ 1 + Real.log X := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ X by linarith); linarith
  have htrunc := shiftedTruncation_le_uniform (s₀ := s₀) hN hxdef (show 1 / 8 ≤ σ₁ by linarith)
    (show x ≤ T by linarith) hL1 hlog2x hlogN
  have hV := norm_vIntegral_shiftedPerron_left_le_uniform hx1 hη hs₀ hTdef hXdef hK₁0.le hK₁
  have hHt := norm_hIntegral_shiftedPerron_le_uniform hx1 halpha hσ₁ hσ₁1 hTdef hXdef
    (abs_of_pos hT0)
    (by rw [abs_of_pos (by linarith [neg_abs_le s₀.im])]; linarith [neg_abs_le s₀.im])
    (by rw [abs_of_pos hT0]
        exact (abs_add_le _ _).trans (by rw [abs_of_pos hT0]; linarith)) hC0 hC
  have hHb := norm_hIntegral_shiftedPerron_le_uniform hx1 halpha hσ₁ hσ₁1 hTdef hXdef
    (y := -T) (by rw [abs_neg, abs_of_pos hT0])
    (by rw [abs_of_neg (by linarith [le_abs_self s₀.im])]; linarith [le_abs_self s₀.im])
    (by rw [abs_neg, abs_of_pos hT0]
        exact (abs_add_le _ _).trans (by rw [abs_neg, abs_of_pos hT0]; linarith)) hC0 hC
  have hmaster := norm_shiftedChebyshev_sub_le halpha hXi (s₀ := s₀) (N := N) (σ₁ := σ₁)
    (c := 9 / 8 - s₀.re) (T := T) hσ₁ hσ₁1 (by linarith) (by linarith) (by linarith) hTim hs₀1
  rw [← hxdef] at hmaster
  generalize x ^ (σ₁ - s₀.re) * (1 + Real.log X) ^ 2 = Q at htrunc hV hHt hHb ⊢
  have hsum := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hV hHt) hHb)
    (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  refine hmaster.trans ?_
  have hfin := add_le_add htrunc hsum
  refine hfin.trans (le_of_eq ?_)
  ring

end

end RHTower.Sieve
