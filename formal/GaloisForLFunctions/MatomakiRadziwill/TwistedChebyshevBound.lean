import GaloisForLFunctions.MatomakiRadziwill.TwistedChebyshevContour

/-!
# Route T for `χ`: twisted Chebyshev sums at heights up to `X`

For a nonprincipal character `χ`, every `θ > 2/3` and every `A ≥ 0` there is `X₀` such that
(`exists_twistedChebyshev_le`)

`‖Σ_{n ≤ N} χ(n)Λ(n)n^{-iτ}‖ ≤ N / (log X)^A`   for `X ≥ X₀`, `|τ| ≤ X`, `N ≤ X`, `log N ≥ (log X)^θ`.

The master inequality (`norm_twistedChebyshev_le`) is applied with `x = N + ½`, `σ₀ = 1 + 1/log x`,
`T = (log X)^{A+6}`, and left edge `σ₁ = 1 − ε(2X+1)/2` (`vkWidth`), where the strip bound
`‖L'/L‖ ≤ C log(2X)/ε(2X+1)` holds at all heights `≤ 2X` (`exists_LFunction_logDeriv_strip`).

* The width is at least a power of `1/log`: `ε(t) ≥ κ₀ (log t)^{-β}` for any `β > 2/3`
  (`exists_vkWidth_rpow_lower`, from `log log t ≤ (log t)^ε/ε`).  Hence `B ≪ (log X)²`.
* The left edge contributes `B T x^{σ₁} ≤ B T x · exp(−κ (log X)^{θ−β})`, since
  `ε · log x ≥ κ₀ (2 log X)^{-β} (log X)^θ`; the exponential beats every power of `log X`
  (`eventually_mul_rpow_mul_exp_le_one`).
* The truncation and the horizontal edges contribute `O(N (log X)²/T)`.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- `ε^{5/3}(log t)^{-2/3-5ε/3}/10⁸ ≤ ε(t)`, from `log log t ≤ (log t)^ε/ε`. -/
theorem rpow_le_vkWidth {t ε : ℝ} (ht : vkThreshold ≤ t) (hε : 0 < ε) :
    ε ^ ((5 : ℝ) / 3) * Real.log t ^ (-(2 : ℝ) / 3 + -(5 : ℝ) / 3 * ε) / 10 ^ 8 ≤ vkWidth t := by
  obtain ⟨ha, hb⟩ := one_le_log_log_of_vkThreshold_le ht
  unfold vkWidth
  set a := Real.log t with hadef
  set b := Real.log a with hbdef
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hbl : b ≤ a ^ ε / ε := Real.log_le_rpow_div ha0.le hε
  have h1 : (a ^ ε / ε) ^ (-(5 : ℝ) / 3) ≤ b ^ (-(5 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hb0 hbl (by norm_num)
  have hu0 : 0 < a ^ ε := Real.rpow_pos_of_pos ha0 ε
  have h2 : (a ^ ε / ε) ^ (-(5 : ℝ) / 3) = ε ^ ((5 : ℝ) / 3) * (a ^ ε) ^ (-(5 : ℝ) / 3) := by
    rw [Real.div_rpow hu0.le hε.le, div_eq_mul_inv, ← Real.rpow_neg hε.le, mul_comm]
    congr 2
    ring
  have h3 : (a ^ ε) ^ (-(5 : ℝ) / 3) = a ^ (-(5 : ℝ) / 3 * ε) := by
    rw [← Real.rpow_mul ha0.le]
    congr 1
    ring
  have h4 : a ^ (-(2 : ℝ) / 3 + -(5 : ℝ) / 3 * ε) = a ^ (-(2 : ℝ) / 3) * a ^ (-(5 : ℝ) / 3 * ε) :=
    Real.rpow_add ha0 _ _
  refine div_le_div_of_nonneg_right ?_ (by norm_num)
  rw [h4]
  have ha23 : 0 ≤ a ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg ha0.le _
  calc ε ^ ((5 : ℝ) / 3) * (a ^ (-(2 : ℝ) / 3) * a ^ (-(5 : ℝ) / 3 * ε))
      = a ^ (-(2 : ℝ) / 3) * (ε ^ ((5 : ℝ) / 3) * a ^ (-(5 : ℝ) / 3 * ε)) := by ring
    _ = a ^ (-(2 : ℝ) / 3) * (a ^ ε / ε) ^ (-(5 : ℝ) / 3) := by rw [h2, h3]
    _ ≤ a ^ (-(2 : ℝ) / 3) * b ^ (-(5 : ℝ) / 3) := mul_le_mul_of_nonneg_left h1 ha23

/-- **The width is at least a power of `1/log`.**  For `θ > 2/3` there are `κ₀ > 0` and
`β ∈ (0, min θ 1]`, `β < θ`, with `κ₀ (log t)^{-β} ≤ ε(t)`. -/
theorem exists_vkWidth_rpow_lower {θ : ℝ} (hθ : 2 / 3 < θ) :
    ∃ κ₀ β : ℝ, 0 < κ₀ ∧ 0 < β ∧ β < θ ∧ β ≤ 1 ∧
      ∀ t : ℝ, vkThreshold ≤ t → κ₀ * Real.log t ^ (-β) ≤ vkWidth t := by
  set β : ℝ := min ((θ + 2 / 3) / 2) (5 / 6) with hβdef
  have hβlo : 2 / 3 < β := lt_min (by linarith) (by norm_num)
  have hβθ : β < θ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hβ1 : β ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  set ε : ℝ := 3 / 5 * (β - 2 / 3) with hεdef
  have hε : 0 < ε := by rw [hεdef]; nlinarith
  have hε53 : 0 < ε ^ ((5 : ℝ) / 3) := Real.rpow_pos_of_pos hε _
  refine ⟨ε ^ ((5 : ℝ) / 3) / 10 ^ 8, β, by positivity, by linarith, hβθ, hβ1, fun t ht => ?_⟩
  have h := rpow_le_vkWidth ht hε
  have hexp : -(2 : ℝ) / 3 + -(5 : ℝ) / 3 * ε = -β := by rw [hεdef]; ring
  rw [hexp] at h
  calc ε ^ ((5 : ℝ) / 3) / 10 ^ 8 * Real.log t ^ (-β)
      = ε ^ ((5 : ℝ) / 3) * Real.log t ^ (-β) / 10 ^ 8 := by ring
    _ ≤ vkWidth t := h

/-- **A positive power beats a logarithm.**  `P log ℓ + K ≤ κ ℓ^η` for all large `ℓ`. -/
theorem eventually_log_le_rpow {κ η P K : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hP : 0 ≤ P) :
    ∀ᶠ ℓ : ℝ in atTop, P * Real.log ℓ + K ≤ κ * ℓ ^ η := by
  set M : ℝ := 4 * P / (η * κ) + 2 * |K| / κ + 1 with hMdef
  have hM1 : 1 ≤ M := by
    have h1 : 0 ≤ 4 * P / (η * κ) := by positivity
    have h2 : 0 ≤ 2 * |K| / κ := by positivity
    linarith
  have hev := (tendsto_rpow_atTop (by positivity : (0 : ℝ) < η / 2)).eventually_ge_atTop M
  filter_upwards [hev, eventually_gt_atTop 0] with ℓ hM hℓ
  set u : ℝ := ℓ ^ (η / 2) with hudef
  have hu1 : 1 ≤ u := le_trans hM1 hM
  have hsq : ℓ ^ η = u * u := by
    rw [hudef, ← Real.rpow_add hℓ]
    congr 1
    ring
  have hlog : Real.log ℓ ≤ u / (η / 2) := Real.log_le_rpow_div hℓ.le (by positivity)
  set w : ℝ := 2 * P / η * u with hwdef
  have hw0 : 0 ≤ w := by positivity
  have h1 : P * Real.log ℓ ≤ w := by
    have h := mul_le_mul_of_nonneg_left hlog hP
    have he : P * (u / (η / 2)) = w := by rw [hwdef]; field_simp
    linarith
  have hK : K ≤ |K| * u := le_trans (le_abs_self K) (le_mul_of_one_le_right (abs_nonneg K) hu1)
  have hκM : κ * M * u = 2 * w + 2 * (|K| * u) + κ * u := by
    rw [hMdef, hwdef]
    field_simp
    ring
  have h2 : κ * M * u ≤ κ * (u * u) := by
    have h := mul_le_mul_of_nonneg_left hM (by positivity : (0 : ℝ) ≤ κ * u)
    calc κ * M * u = κ * u * M := by ring
      _ ≤ κ * u * u := h
      _ = κ * (u * u) := by ring
  have hKu : 0 ≤ |K| * u := by positivity
  have hκu : 0 ≤ κ * u := by positivity
  rw [hsq]
  linarith

/-- **The exponential beats every power.**  `K ℓ^p e^{−κ ℓ^η} ≤ 1` for all large `ℓ`. -/
theorem eventually_mul_rpow_mul_exp_le_one {κ η K p : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hK : 0 < K)
    (hp : 0 ≤ p) :
    ∀ᶠ ℓ : ℝ in atTop, K * ℓ ^ p * Real.exp (-(κ * ℓ ^ η)) ≤ 1 := by
  filter_upwards [eventually_log_le_rpow (K := Real.log K) hκ hη hp, eventually_gt_atTop 0]
    with ℓ h hℓ
  have heq : K * ℓ ^ p = Real.exp (Real.log K + p * Real.log ℓ) := by
    rw [Real.exp_add, Real.exp_log hK, Real.rpow_def_of_pos hℓ, mul_comm (Real.log ℓ)]
  rw [heq, ← Real.exp_add]
  calc Real.exp (Real.log K + p * Real.log ℓ + -(κ * ℓ ^ η)) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- `x^{1 + 1/log x} = e · x` for `x > 1`. -/
theorem rpow_one_add_inv_log {x : ℝ} (hx : 1 < x) :
    x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
  have hx0 : 0 < x := by linarith
  have hL : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [Real.rpow_add hx0, Real.rpow_one, Real.rpow_def_of_pos hx0,
    show Real.log x * (1 / Real.log x) = 1 by field_simp]
  ring

/-- `log y ≤ 2 log X` for `0 < y ≤ X²`. -/
theorem log_le_two_log_of_le_sq {X y : ℝ} (hy : 0 < y) (h : y ≤ X ^ 2) :
    Real.log y ≤ 2 * Real.log X := by
  have h1 := Real.log_le_log hy h
  rw [Real.log_pow] at h1
  push_cast at h1
  exact h1

/-- **The Perron term.**  At `x = N + ½`, `σ₀ = 1 + 1/log x`, the truncation error of
`norm_twistedChebyshev_le` is at most `720 N (log X)²/T` for `N ≤ X`, `X ≥ 4`. -/
theorem perron_term_le {N : ℕ} (hN : 1 ≤ N) {X T σ₀ : ℝ} (hX : 4 ≤ X) (hNX : (N : ℝ) ≤ X)
    (hT : 0 < T) (hlog : 1 ≤ Real.log ((N : ℝ) + 1 / 2))
    (hσ₀ : σ₀ = 1 + 1 / Real.log ((N : ℝ) + 1 / 2)) :
    (1 / (Real.pi * T * Real.log 2)) * (((N : ℝ) + 1 / 2) ^ σ₀ * (8 / (σ₀ - 1) ^ 2))
      + (16 * Real.log (2 * ((N : ℝ) + 1 / 2)) * ((N : ℝ) + 1 / 2) / (Real.pi * T))
        * (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ)))
      ≤ 720 * N * Real.log X ^ 2 / T := by
  set x : ℝ := (N : ℝ) + 1 / 2 with hxdef
  set Lx : ℝ := Real.log x with hLxdef
  set ℓ : ℝ := Real.log X with hℓdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 < x := by rw [hxdef]; linarith
  have hx0 : 0 < x := by linarith
  have hLx0 : 0 < Lx := by linarith
  have hxσ : x ^ σ₀ = Real.exp 1 * x := by rw [hσ₀]; exact rpow_one_add_inv_log hx1
  have hσ8 : 8 / (σ₀ - 1) ^ 2 = 8 * Lx ^ 2 := by
    rw [hσ₀, show (1 + 1 / Lx) - 1 = 1 / Lx by ring, div_pow, one_pow, div_div_eq_mul_div,
      div_one]
  have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hlog2 : 1 / 2 ≤ Real.log 2 := le_of_lt (lt_trans (by norm_num) Real.log_two_gt_d9)
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓdef, Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hLx : Lx ≤ 2 * ℓ := log_le_two_log_of_le_sq hx0 (by rw [hxdef]; nlinarith)
  have hL2x : Real.log (2 * x) ≤ 2 * ℓ :=
    log_le_two_log_of_le_sq (by positivity) (by rw [hxdef]; nlinarith)
  have hLN : Real.log ((2 * N + 2 : ℕ) : ℝ) ≤ 2 * ℓ :=
    log_le_two_log_of_le_sq (by positivity) (by push_cast; nlinarith)
  have hL2x0 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hLN0 : 0 ≤ Real.log ((2 * N + 2 : ℕ) : ℝ) := Real.log_nonneg (by push_cast; linarith)
  rw [hxσ, hσ8]
  -- the first term
  have hden1 : T ≤ Real.pi * T * Real.log 2 := by
    have h : 1 ≤ Real.pi * Real.log 2 := by nlinarith
    nlinarith
  have hA1 : (1 / (Real.pi * T * Real.log 2)) * (Real.exp 1 * x * (8 * Lx ^ 2))
      ≤ 96 * x * ℓ ^ 2 / T := by
    have hfac : 1 / (Real.pi * T * Real.log 2) ≤ 1 / T := one_div_le_one_div_of_le hT hden1
    have hnum : Real.exp 1 * x * (8 * Lx ^ 2) ≤ 96 * x * ℓ ^ 2 := by
      have hL2 : Lx ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
      have h1 : Real.exp 1 * x ≤ 3 * x := mul_le_mul_of_nonneg_right he hx0.le
      have h2 := mul_le_mul h1 (by linarith : 8 * Lx ^ 2 ≤ 8 * (4 * ℓ ^ 2)) (by positivity)
        (by positivity)
      linarith
    calc (1 / (Real.pi * T * Real.log 2)) * (Real.exp 1 * x * (8 * Lx ^ 2))
        ≤ (1 / T) * (96 * x * ℓ ^ 2) :=
          mul_le_mul hfac hnum (by positivity) (by positivity)
      _ = 96 * x * ℓ ^ 2 / T := by ring
  -- the second term
  have hA2 : (16 * Real.log (2 * x) * x / (Real.pi * T))
        * (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ))) ≤ 384 * x * ℓ ^ 2 / T := by
    have h1 : 16 * Real.log (2 * x) * x / (Real.pi * T) ≤ 32 * ℓ * x / T := by
      refine div_le_div₀ (by positivity) ?_ hT (by nlinarith)
      have := mul_le_mul_of_nonneg_right hL2x hx0.le
      nlinarith
    have h2 : 4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ)) ≤ 12 * ℓ := by linarith
    calc (16 * Real.log (2 * x) * x / (Real.pi * T)) * (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ)))
        ≤ (32 * ℓ * x / T) * (12 * ℓ) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 384 * x * ℓ ^ 2 / T := by ring
  have hx32 : 480 * x ≤ 720 * N := by rw [hxdef]; linarith
  have hsum : 96 * x * ℓ ^ 2 / T + 384 * x * ℓ ^ 2 / T ≤ 720 * N * ℓ ^ 2 / T := by
    rw [← add_div]
    refine div_le_div_of_nonneg_right ?_ hT.le
    have := mul_le_mul_of_nonneg_right hx32 (sq_nonneg ℓ)
    linarith
  linarith

/-- **The contour term.**  With `σ₁ ≥ ½`, `σ₀ − σ₁ ≤ 1` and `x^{σ₀} ≤ 3x`, the three shifted sides
contribute at most `B T x^{σ₁} + B x/T`. -/
theorem contour_term_le {B x σ₁ σ₀ T : ℝ} (hB : 0 ≤ B) (hx : 0 < x) (hσ₁ : 1 / 2 ≤ σ₁)
    (hd : σ₀ - σ₁ ≤ 1) (hxσ₀ : x ^ σ₀ ≤ 3 * x) (hT : 0 < T) :
    (1 / (2 * Real.pi)) * (B * (x ^ σ₁ / σ₁) * (2 * T) + 2 * (B * (x ^ σ₀ / T) * (σ₀ - σ₁)))
      ≤ B * T * x ^ σ₁ + B * x / T := by
  have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
  have hxs : 0 ≤ x ^ σ₁ := Real.rpow_nonneg hx.le _
  have h1 : x ^ σ₁ / σ₁ ≤ 2 * x ^ σ₁ := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h2 : B * (x ^ σ₁ / σ₁) * (2 * T) ≤ 4 * (B * T * x ^ σ₁) := by
    have h := mul_le_mul_of_nonneg_left h1 hB
    have h' := mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ 2 * T)
    linarith
  have h3 : 2 * (B * (x ^ σ₀ / T) * (σ₀ - σ₁)) ≤ 6 * (B * x / T) := by
    have hq : x ^ σ₀ / T ≤ 3 * x / T := div_le_div_of_nonneg_right hxσ₀ hT.le
    have hq0 : 0 ≤ x ^ σ₀ / T := by positivity
    have h := mul_le_mul_of_nonneg_left hq hB
    have h' : B * (x ^ σ₀ / T) * (σ₀ - σ₁) ≤ B * (x ^ σ₀ / T) * 1 :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    have he : B * (3 * x / T) = 3 * (B * x / T) := by ring
    linarith
  have hP : 0 ≤ B * T * x ^ σ₁ := by positivity
  have hQ : 0 ≤ B * x / T := by positivity
  have h4 : 1 / (2 * Real.pi) ≤ 1 / 6 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hsum0 : 0 ≤ 4 * (B * T * x ^ σ₁) + 6 * (B * x / T) := by positivity
  calc (1 / (2 * Real.pi)) * (B * (x ^ σ₁ / σ₁) * (2 * T) + 2 * (B * (x ^ σ₀ / T) * (σ₀ - σ₁)))
      ≤ (1 / (2 * Real.pi)) * (4 * (B * T * x ^ σ₁) + 6 * (B * x / T)) :=
        mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity)
    _ ≤ (1 / 6) * (4 * (B * T * x ^ σ₁) + 6 * (B * x / T)) :=
        mul_le_mul_of_nonneg_right h4 hsum0
    _ ≤ B * T * x ^ σ₁ + B * x / T := by linarith

/-- `ℓ^A ℓ⁶ ≤ e^ℓ` once `(A + 6) log ℓ ≤ ℓ`. -/
theorem rpow_mul_pow_six_le_exp {ℓ A : ℝ} (hℓ : 0 < ℓ) (h : (A + 6) * Real.log ℓ ≤ ℓ) :
    ℓ ^ A * ℓ ^ 6 ≤ Real.exp ℓ := by
  have h6 : ℓ ^ 6 = Real.exp (6 * Real.log ℓ) := by
    rw [show (6 : ℝ) * Real.log ℓ = ((6 : ℕ) : ℝ) * Real.log ℓ by norm_num, Real.exp_nat_mul,
      Real.exp_log hℓ]
  rw [Real.rpow_def_of_pos hℓ, h6, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **Assembly at a fixed scale.**  The master inequality, with the three pieces bounded by
`N/(3(log X)^A)` each. -/
theorem twistedChebyshev_arith {N : ℕ} (hN : 1 ≤ N) {X ℓ La T B E K₁ σ₀ σ₁ x S : ℝ}
    (hX4 : 4 ≤ X) (hNX : (N : ℝ) ≤ X) (hℓ : ℓ = Real.log X) (hℓ0 : 0 < ℓ) (hLa : 0 < La)
    (hT : T = La * ℓ ^ 6) (hx : x = (N : ℝ) + 1 / 2) (hlogx : 1 ≤ Real.log x)
    (hσ₀ : σ₀ = 1 + 1 / Real.log x) (hσ₁half : 1 / 2 ≤ σ₁) (hd : σ₀ - σ₁ ≤ 1)
    (hxσ₀ : x ^ σ₀ ≤ 3 * x) (hB0 : 0 ≤ B) (hBle : B ≤ 4 * K₁ * ℓ ^ 2) (hE0 : 0 ≤ E)
    (hxσ₁ : x ^ σ₁ ≤ x * E) (h2160 : 2160 ≤ ℓ ^ 4) (hK : 18 * K₁ ≤ ℓ ^ 4)
    (hexp : 18 * K₁ * (La * La * ℓ ^ 8) * E ≤ 1)
    (hS : S ≤ ((1 / (Real.pi * T * Real.log 2)) * (x ^ σ₀ * (8 / (σ₀ - 1) ^ 2))
          + (16 * Real.log (2 * x) * x / (Real.pi * T))
            * (4 * (1 + Real.log ((2 * N + 2 : ℕ) : ℝ))))
        + (1 / (2 * Real.pi)) * (B * (x ^ σ₁ / σ₁) * (2 * T)
          + 2 * (B * (x ^ σ₀ / T) * (σ₀ - σ₁)))) :
    S ≤ N / La := by
  subst hx hT hℓ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < (N : ℝ) + 1 / 2 := by linarith
  have hT0 : 0 < La * Real.log X ^ 6 := by positivity
  have hperron := perron_term_le hN hX4 hNX hT0 hlogx hσ₀
  have hcontour := contour_term_le hB0 hx0 hσ₁half hd hxσ₀ hT0
  have hx32 : (N : ℝ) + 1 / 2 ≤ 3 / 2 * N := by linarith
  have hNLa : 0 ≤ (N : ℝ) * La * Real.log X ^ 2 := by positivity
  have hpa : 720 * N * Real.log X ^ 2 / (La * Real.log X ^ 6) ≤ N / (3 * La) := by
    rw [div_le_div_iff₀ hT0 (by positivity)]
    calc 720 * N * Real.log X ^ 2 * (3 * La) = 2160 * (N * La * Real.log X ^ 2) := by ring
      _ ≤ Real.log X ^ 4 * (N * La * Real.log X ^ 2) := mul_le_mul_of_nonneg_right h2160 hNLa
      _ = N * (La * Real.log X ^ 6) := by ring
  have hpb : B * ((N : ℝ) + 1 / 2) / (La * Real.log X ^ 6) ≤ N / (3 * La) := by
    have h1 : B * ((N : ℝ) + 1 / 2) ≤ 4 * K₁ * Real.log X ^ 2 * (3 / 2 * N) :=
      mul_le_mul hBle hx32 hx0.le (le_trans hB0 hBle)
    have h2 := div_le_div_of_nonneg_right h1 hT0.le
    have h3 : 4 * K₁ * Real.log X ^ 2 * (3 / 2 * N) / (La * Real.log X ^ 6) ≤ N / (3 * La) := by
      rw [div_le_div_iff₀ hT0 (by positivity)]
      calc 4 * K₁ * Real.log X ^ 2 * (3 / 2 * N) * (3 * La)
          = 18 * K₁ * (N * La * Real.log X ^ 2) := by ring
        _ ≤ Real.log X ^ 4 * (N * La * Real.log X ^ 2) := mul_le_mul_of_nonneg_right hK hNLa
        _ = N * (La * Real.log X ^ 6) := by ring
    linarith
  have hpc : B * (La * Real.log X ^ 6) * ((N : ℝ) + 1 / 2) ^ σ₁ ≤ N / (3 * La) := by
    have hxE : ((N : ℝ) + 1 / 2) ^ σ₁ ≤ 3 / 2 * N * E :=
      le_trans hxσ₁ (mul_le_mul_of_nonneg_right hx32 hE0)
    have h1 : B * (La * Real.log X ^ 6) * ((N : ℝ) + 1 / 2) ^ σ₁
        ≤ 4 * K₁ * Real.log X ^ 2 * (La * Real.log X ^ 6) * (3 / 2 * N * E) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hBle hT0.le) hxE
        (Real.rpow_nonneg hx0.le _) (mul_nonneg (le_trans hB0 hBle) hT0.le)
    have h2 : 4 * K₁ * Real.log X ^ 2 * (La * Real.log X ^ 6) * (3 / 2 * N * E)
        ≤ N / (3 * La) := by
      rw [le_div_iff₀ (by positivity)]
      calc 4 * K₁ * Real.log X ^ 2 * (La * Real.log X ^ 6) * (3 / 2 * N * E) * (3 * La)
          = (N : ℝ) * (18 * K₁ * (La * La * Real.log X ^ 8) * E) := by ring
        _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = (N : ℝ) := mul_one _
    linarith
  have hthree : (N : ℝ) / (3 * La) + N / (3 * La) + N / (3 * La) = N / La := by
    field_simp
    ring
  linarith

/-- **The width at the scale `X`.**  From `κ₀ (log 4X)^{-β} ≤ v` with `β ≤ 1`:
`κ₀ (2 log X)^{-β} ≤ v` and `C log(2X)/v ≤ 4(C/κ₀)(log X)²`. -/
theorem width_at_scale {C κ₀ β X v : ℝ} (hC : 0 < C) (hκ₀ : 0 < κ₀) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hX4 : 4 ≤ X) (hℓ1 : 1 ≤ Real.log X) (hv : κ₀ * Real.log (4 * X) ^ (-β) ≤ v) :
    κ₀ * (2 * Real.log X) ^ (-β) ≤ v ∧ C * Real.log (2 * X) / v ≤ 4 * (C / κ₀) * Real.log X ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hlog4X : Real.log (4 * X) ≤ 2 * Real.log X :=
    log_le_two_log_of_le_sq (by positivity) (by nlinarith)
  have hlog4X0 : 0 < Real.log (4 * X) := Real.log_pos (by linarith)
  have hv1 : κ₀ * (2 * Real.log X) ^ (-β) ≤ v := by
    have h3 : (2 * Real.log X) ^ (-β) ≤ Real.log (4 * X) ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos hlog4X0 hlog4X (by linarith)
    have h4 := mul_le_mul_of_nonneg_left h3 hκ₀.le
    linarith
  refine ⟨hv1, ?_⟩
  have hvlow : κ₀ / (2 * Real.log X) ≤ v := by
    have h1 : (2 * Real.log X) ^ (-1 : ℝ) ≤ (2 * Real.log X) ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hκ₀.le
    rw [div_eq_mul_inv]
    linarith
  have hlog2X : Real.log (2 * X) ≤ 2 * Real.log X :=
    log_le_two_log_of_le_sq (by positivity) (by nlinarith)
  have hℓ0 : 0 < Real.log X := by linarith
  have h := div_le_div₀ (by positivity : (0 : ℝ) ≤ C * (2 * Real.log X))
    (mul_le_mul_of_nonneg_left hlog2X hC.le) (by positivity : (0 : ℝ) < κ₀ / (2 * Real.log X))
    hvlow
  have he : C * (2 * Real.log X) / (κ₀ / (2 * Real.log X)) = 4 * (C / κ₀) * Real.log X ^ 2 := by
    field_simp
    ring
  linarith

/-- **The saving on the left edge.**  `x^{1 − v/2} ≤ x e^{−κ ℓ^{θ−β}}` with `κ = κ₀ 2^{-β}/2`,
when `κ₀ (2ℓ)^{-β} ≤ v` and `ℓ^θ ≤ log x`. -/
theorem rpow_left_edge_le {κ₀ β θ ℓ v x : ℝ} (hκ₀ : 0 < κ₀) (hℓ0 : 0 < ℓ) (hx : 0 < x)
    (hv : κ₀ * (2 * ℓ) ^ (-β) ≤ v) (hlogx : ℓ ^ θ ≤ Real.log x) :
    x ^ (1 - v / 2) ≤ x * Real.exp (-(κ₀ * (2 : ℝ) ^ (-β) / 2 * ℓ ^ (θ - β))) := by
  have hsave : κ₀ * (2 : ℝ) ^ (-β) / 2 * ℓ ^ (θ - β) ≤ Real.log x * (v / 2) := by
    have h1 : κ₀ * (2 * ℓ) ^ (-β) / 2 * ℓ ^ θ = κ₀ * (2 : ℝ) ^ (-β) / 2 * ℓ ^ (θ - β) := by
      rw [Real.mul_rpow (by norm_num) hℓ0.le, Real.rpow_sub hℓ0, Real.rpow_neg hℓ0.le]
      field_simp
    have hθ0 : 0 ≤ ℓ ^ θ := Real.rpow_nonneg hℓ0.le θ
    have hpos : 0 ≤ κ₀ * (2 * ℓ) ^ (-β) / 2 := by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * ℓ) (-β)
      positivity
    have h2 : κ₀ * (2 * ℓ) ^ (-β) / 2 * ℓ ^ θ ≤ (v / 2) * Real.log x :=
      mul_le_mul (by linarith) hlogx hθ0 (by linarith)
    linarith
  rw [Real.rpow_sub hx, Real.rpow_one, Real.rpow_def_of_pos hx, div_eq_mul_inv, ← Real.exp_neg]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hx.le

/-- The conditions on `ℓ = log X` used by the assembly, all eventually true. -/
theorem eventually_scale_conditions {θ A κ η K₁ : ℝ} (hθ : 0 < θ) (hA : 0 ≤ A) (hκ : 0 < κ)
    (hη : 0 < η) (hK₁ : 0 < K₁) :
    ∀ᶠ ℓ : ℝ in atTop, 0 < ℓ ∧ 8 ≤ ℓ ^ θ ∧ max 2160 (18 * K₁) ≤ ℓ ^ 4 ∧
      18 * K₁ * (ℓ ^ A * ℓ ^ A * ℓ ^ 8) * Real.exp (-(κ * ℓ ^ η)) ≤ 1 ∧
      (A + 6) * Real.log ℓ ≤ ℓ := by
  have e1 := eventually_gt_atTop (0 : ℝ)
  have e2 := (tendsto_rpow_atTop hθ).eventually_ge_atTop 8
  have e3 := (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).eventually_ge_atTop
    (max 2160 (18 * K₁))
  have e4 := eventually_mul_rpow_mul_exp_le_one (p := 2 * A + 8) hκ hη
    (by positivity : (0 : ℝ) < 18 * K₁) (by linarith)
  have e5 := eventually_log_le_rpow (κ := 1) (η := 1) (P := A + 6) (K := 0) one_pos one_pos
    (by linarith)
  filter_upwards [e1, e2, e3, e4, e5] with ℓ h1 h2 h3 h4 h5
  refine ⟨h1, h2, h3, ?_, by simpa using h5⟩
  have hsplit : ℓ ^ (2 * A + 8) = ℓ ^ A * ℓ ^ A * ℓ ^ 8 := by
    rw [show 2 * A + 8 = A + A + 8 by ring, Real.rpow_add h1, Real.rpow_add h1]
    congr 1
    exact_mod_cast Real.rpow_natCast ℓ 8
  rw [← hsplit]
  exact h4

variable {q : ℕ} [NeZero q]

/-- **Route T for `χ`.**  For a nonprincipal character `χ`, `θ > 2/3` and `A ≥ 0`, for all large
`X`, every `|τ| ≤ X` and every `N ≤ X` with `log N ≥ (log X)^θ`:
`‖Σ_{n ≤ N} χ(n)Λ(n)n^{-iτ}‖ ≤ N/(log X)^A`. -/
theorem exists_twistedChebyshev_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {θ A : ℝ}
    (hθ : 2 / 3 < θ) (hA : 0 ≤ A) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ τ : ℝ, |τ| ≤ X → ∀ N : ℕ,
      Real.log X ^ θ ≤ Real.log N → (N : ℝ) ≤ X →
        ‖∑ n ∈ Finset.Icc 1 N, twistedVM χ τ n‖ ≤ N / Real.log X ^ A := by
  obtain ⟨C, Y₀, hC, hY₀v, hstrip⟩ := exists_LFunction_logDeriv_strip χ hχ
  obtain ⟨κ₀, β, hκ₀, hβ0, hβθ, hβ1, hvk⟩ := exists_vkWidth_rpow_lower hθ
  have hη : 0 < θ - β := by linarith
  have hκ : 0 < κ₀ * (2 : ℝ) ^ (-β) / 2 := by
    have := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-β)
    positivity
  have hK₁ : 0 < C / κ₀ := by positivity
  have hXev := (Real.tendsto_log_atTop.eventually (eventually_scale_conditions (A := A)
    (by linarith : (0 : ℝ) < θ) hA hκ hη hK₁)).and ((eventually_ge_atTop 4).and
      ((eventually_ge_atTop Y₀).and (eventually_ge_atTop vkThreshold)))
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hXev
  refine ⟨X₀, fun X hX τ hτ N hlogN hNX => ?_⟩
  obtain ⟨⟨hℓ0, hℓθ, hℓ4, hexp, hT6⟩, hX4, hXY, hXv⟩ := hX₀ X hX
  have hX0 : 0 < X := by linarith
  have hℓ1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    linarith [le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num : (2.7182818286 : ℝ) < 4))]
  -- `N ≥ 1` and `log x ≥ (log X)^θ`
  have hlogN8 : 8 ≤ Real.log N := le_trans hℓθ hlogN
  have hN : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h] at hlogN8; simp at hlogN8; linarith
    · exact h
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (N : ℝ) + 1 / 2 := ⟨_, rfl⟩
  have hx1 : 1 < x := by rw [hxdef]; linarith
  have hx0 : 0 < x := by linarith
  have hlogx : Real.log X ^ θ ≤ Real.log x :=
    le_trans hlogN (Real.log_le_log (by linarith) (by rw [hxdef]; linarith))
  have hlogx8 : 8 ≤ Real.log x := le_trans hℓθ hlogx
  -- the abscissae and the height
  obtain ⟨σ₀, hσ₀def⟩ : ∃ σ₀ : ℝ, σ₀ = 1 + 1 / Real.log x := ⟨_, rfl⟩
  have hinv : 0 < 1 / Real.log x := by positivity
  have hinv8 : 1 / Real.log x ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hlogx8
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀def]; linarith
  have hσ₀98 : σ₀ ≤ 9 / 8 := by rw [hσ₀def]; linarith
  have hYv : vkThreshold ≤ 2 * X + 1 := by linarith
  obtain ⟨v, hvdef⟩ : ∃ v : ℝ, v = vkWidth (2 * X + 1) := ⟨_, rfl⟩
  have hv0 : 0 < v := by rw [hvdef]; exact vkWidth_pos hYv
  have hv80 : v ≤ 1 / 80 := by rw [hvdef]; exact vkWidth_le hYv
  obtain ⟨σ₁, hσ₁def⟩ : ∃ σ₁ : ℝ, σ₁ = 1 - v / 2 := ⟨_, rfl⟩
  have hσ₁half : 1 / 2 ≤ σ₁ := by rw [hσ₁def]; linarith
  have hσ₁₀ : σ₁ ≤ σ₀ := by rw [hσ₁def]; linarith
  have hd : σ₀ - σ₁ ≤ 1 := by rw [hσ₁def]; linarith
  obtain ⟨La, hLadef⟩ : ∃ La : ℝ, La = Real.log X ^ A := ⟨_, rfl⟩
  have hLa : 0 < La := by rw [hLadef]; exact Real.rpow_pos_of_pos hℓ0 A
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = La * Real.log X ^ 6 := ⟨_, rfl⟩
  have hT : 0 < T := by rw [hTdef]; positivity
  have hTX : T ≤ X := by
    have h := rpow_mul_pow_six_le_exp hℓ0 hT6
    rw [Real.exp_log hX0, ← hLadef, ← hTdef] at h
    exact h
  -- the strip
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = C * Real.log (2 * X) / v := ⟨_, rfl⟩
  have hstrip' : ∀ u t : ℝ, σ₁ ≤ u → u ≤ σ₀ → |t| ≤ T →
      DirichletCharacter.LFunction χ ((u : ℂ) + ((t + τ : ℝ) : ℂ) * I) ≠ 0 ∧
      ‖logDeriv (DirichletCharacter.LFunction χ) ((u : ℂ) + ((t + τ : ℝ) : ℂ) * I)‖ ≤ B := by
    intro u t hu1 hu2 ht
    have hht : |t + τ| ≤ 2 * X := by linarith [abs_add_le t τ]
    have h := hstrip (2 * X) (by linarith) u (t + τ) hht (by rw [← hvdef, ← hσ₁def]; exact hu1)
      (le_trans hu2 hσ₀98)
    rw [← hvdef, ← hBdef] at h
    exact h
  have hmaster := norm_twistedChebyshev_le χ hχ τ hN (by linarith : 0 < σ₁) hσ₁₀ hσ₀1
    (by linarith) hT hstrip'
  rw [← hxdef] at hmaster
  -- the width
  have hv4 : κ₀ * Real.log (4 * X) ^ (-β) ≤ v := by
    have h1 : vkWidth (4 * X) ≤ v := by rw [hvdef]; exact vkWidth_anti hYv (by linarith)
    have h2 := hvk (4 * X) (by linarith)
    linarith
  obtain ⟨hv2ℓ, hBle⟩ := width_at_scale hC hκ₀ hβ0 hβ1 hX4 hℓ1 hv4
  rw [← hBdef] at hBle
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
    positivity
  have hxσ₁ := rpow_left_edge_le hκ₀ hℓ0 hx0 hv2ℓ hlogx
  rw [← hσ₁def] at hxσ₁
  have hxσ₀ : x ^ σ₀ ≤ 3 * x := by
    rw [hσ₀def, rpow_one_add_inv_log hx1]
    exact mul_le_mul_of_nonneg_right
      (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hx0.le
  have hres := twistedChebyshev_arith hN hX4 hNX rfl hℓ0 hLa hTdef hxdef (by linarith) hσ₀def
    hσ₁half hd hxσ₀ hB0 hBle (Real.exp_pos _).le hxσ₁ (le_trans (le_max_left _ _) hℓ4)
    (le_trans (le_max_right _ _) hℓ4) (by rw [hLadef]; exact hexp) hmaster
  rw [hLadef] at hres
  exact hres

end

end GaloisForLFunctions.MatomakiRadziwill
