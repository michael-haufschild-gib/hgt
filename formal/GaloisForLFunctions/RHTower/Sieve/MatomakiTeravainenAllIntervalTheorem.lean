import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAllIntervalWindowCompare

/-!
# Matomäki–Teräväinen Theorem 1.2, quantitative form

For `a ∈ [a₀, 11/10]`, `a₀ ≥ 1.0999`, every interval `(x, x + √x (log x)^{1+a/2}]` with `x` large
contains `≫ h/(log P₁ (log x)²)` products `p₁p₂n` with `p₁ ∼ P₁ = (log x)^a`,
`p₂ ∼ √(x/P₁)/2`, weighted by Harman's minorant `ρ⁻(n)`.  The short window is compared with the
long window `h₁ = x e^{-(c/8)√log x}`, whose main term is known; the comparison is the Perron
window bound of `Sieve/MatomakiTeravainenAllIntervalWindowCompare`, fed by the claim (5.2) for
`P₁P` above `T₀ = exp((c/32)(log X)^{1/2})` and the improved mean value theorem for the dyadic
prime polynomial `P₂`, with the dyadic count `J = ⌈12 log log x⌉`.  The analytic inputs of (5.2),
the Deshouillers–Iwaniec bound and Watt's bound, enter as the hypotheses `MTDeshouillersIwaniecBound`
and `MTWattBound`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory Filter

noncomputable section

/-- **The claim (5.2) in affine form.**  With `L/2 ≤ log X` and `X = P₁T₁L`:
`2(log X)^{-(2+ε/10)} + 2(log X)^{-(1+ε/10)}P₁T/X ≤ 16 L^{-(2+ε/10)}(1 + T/T₁)`. -/
theorem mt_meanSquare_affine_alpha {X L P₁ T₁ T ε : ℝ} (hL : 2 ≤ L) (hXl : L / 2 ≤ Real.log X)
    (hε : 0 ≤ ε) (hε10 : ε ≤ 10) (hT₁ : 0 < T₁) (hT : 0 ≤ T) (hX : 0 < X) (hP : 0 ≤ P₁)
    (hPX : P₁ * T₁ * L = X) :
    2 * Real.log X ^ (-(2 + ε / 10)) + 2 * Real.log X ^ (-(1 + ε / 10)) * P₁ * T / X ≤
      16 * L ^ (-(2 + ε / 10)) * (1 + T / T₁) := by
  have hL0 : 0 < L := by linarith
  have hlX : 0 < Real.log X := lt_of_lt_of_le (by linarith) hXl
  have key : ∀ s : ℝ, 0 ≤ s → s ≤ 3 → Real.log X ^ (-s) ≤ 8 * L ^ (-s) := by
    intro s hs0 hs3
    have h1 : Real.log X ^ (-s) ≤ (L / 2) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hXl (by linarith)
    have h2 : (L / 2) ^ (-s) = 2 ^ s * L ^ (-s) := by
      rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    have h8 : (2 : ℝ) ^ (3 : ℝ) = 8 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have h3 : (2 : ℝ) ^ s ≤ 8 := by
      rw [← h8]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hs3
    rw [h2] at h1
    have : 0 ≤ L ^ (-s) := by positivity
    nlinarith
  have hP0 : 0 < P₁ := by
    rcases hP.lt_or_eq with h | h
    · exact h
    · rw [← h] at hPX; simp at hPX; linarith
  have hPTX : P₁ * T / X = T / T₁ / L := by
    rw [← hPX]; field_simp
  have hLs : L ^ (-(1 + ε / 10)) / L = L ^ (-(2 + ε / 10)) := by
    rw [show -(2 + ε / 10) = -(1 + ε / 10) + (-1) by ring, Real.rpow_add hL0, Real.rpow_neg_one]
    ring
  have e1 := key (2 + ε / 10) (by positivity) (by linarith)
  have e2 := key (1 + ε / 10) (by positivity) (by linarith)
  have hTT : 0 ≤ T / T₁ := by positivity
  calc 2 * Real.log X ^ (-(2 + ε / 10)) + 2 * Real.log X ^ (-(1 + ε / 10)) * P₁ * T / X
      = 2 * Real.log X ^ (-(2 + ε / 10)) + 2 * Real.log X ^ (-(1 + ε / 10)) * (P₁ * T / X) := by
        ring
    _ ≤ 2 * (8 * L ^ (-(2 + ε / 10))) + 2 * (8 * L ^ (-(1 + ε / 10))) * (T / T₁ / L) := by
        rw [hPTX]
        have : 0 ≤ T / T₁ / L := by positivity
        gcongr
    _ = 16 * L ^ (-(2 + ε / 10)) * (1 + T / T₁) := by
        rw [show 2 * (8 * L ^ (-(1 + ε / 10))) * (T / T₁ / L) =
          16 * (L ^ (-(1 + ε / 10)) / L) * (T / T₁) by ring, hLs]
        ring

/-- **The prime mean square in affine form.**  With `log R ≥ L/3` and `T₁L ≤ 2R`:
`C(T/(R log R) + (log R)^{-2}) ≤ (9C/L²)(1 + T/T₁)`. -/
theorem mt_meanSquare_affine_beta {C R L T₁ T : ℝ} (hC : 0 ≤ C) (hL : 0 < L) (hR : 0 < R)
    (hlogR : L / 3 ≤ Real.log R) (hT₁ : 0 < T₁) (hT₁L : T₁ * L ≤ 2 * R) (hT : 0 ≤ T) :
    C * (T / (R * Real.log R) + 1 / Real.log R ^ 2) ≤ 9 * C / L ^ 2 * (1 + T / T₁) := by
  have hlR : 0 < Real.log R := lt_of_lt_of_le (by positivity) hlogR
  have h1 : 1 / Real.log R ^ 2 ≤ 9 / L ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : T / (R * Real.log R) ≤ 9 / L ^ 2 * (T / T₁) := by
    rw [show 9 / L ^ 2 * (T / T₁) = 9 * T / (T₁ * L ^ 2) by field_simp,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : T₁ * L ^ 2 ≤ 2 * R * L := by nlinarith
    have h4 : 2 * R * L ≤ 9 * (R * Real.log R) := by nlinarith
    nlinarith
  calc C * (T / (R * Real.log R) + 1 / Real.log R ^ 2)
      ≤ C * (9 / L ^ 2 * (T / T₁) + 9 / L ^ 2) := by gcongr
    _ = 9 * C / L ^ 2 * (1 + T / T₁) := by ring

/-- `√(16 L^{-(2+ε/10)} · 9C/L²) = 12 √C L^{-(2+ε/20)}`. -/
theorem mt_sqrt_alpha_beta {L C ε : ℝ} (hL : 0 < L) (hC : 0 ≤ C) :
    Real.sqrt (16 * L ^ (-(2 + ε / 10)) * (9 * C / L ^ 2)) =
      12 * Real.sqrt C * L ^ (-(2 + ε / 20)) := by
  have hsq : 16 * L ^ (-(2 + ε / 10)) * (9 * C / L ^ 2) =
      (12 * Real.sqrt C * L ^ (-(2 + ε / 20))) ^ 2 := by
    have h1 : (L ^ (-(2 + ε / 20))) ^ 2 = L ^ (-(2 + ε / 10)) / L ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le, ← Real.rpow_natCast L 2,
        ← Real.rpow_sub hL]
      congr 1; push_cast; ring
    rw [mul_pow, mul_pow, Real.sq_sqrt hC, h1]
    ring
  rw [hsq, Real.sqrt_sq (by positivity)]

/-- The dyadic count `J = ⌈12 log L⌉`: `J ≤ 12 log L + 1`, `L⁸ ≤ 2^J ≤ 2L⁹`. -/
theorem ceil_twelve_log_facts {L : ℝ} (hL : 1 ≤ L) :
    ((⌈12 * Real.log L⌉₊ : ℕ) : ℝ) ≤ 12 * Real.log L + 1 ∧
      L ^ 8 ≤ (2 : ℝ) ^ ⌈12 * Real.log L⌉₊ ∧ (2 : ℝ) ^ ⌈12 * Real.log L⌉₊ ≤ 2 * L ^ 9 := by
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hL0 : 0 < L := by linarith
  have hJu : ((⌈12 * Real.log L⌉₊ : ℕ) : ℝ) ≤ 12 * Real.log L + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hJ : 12 * Real.log L ≤ (⌈12 * Real.log L⌉₊ : ℝ) := Nat.le_ceil _
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hexpL : ∀ n : ℕ, L ^ n = Real.exp (n * Real.log L) := fun n => by
    rw [Real.exp_nat_mul, Real.exp_log hL0]
  have hexp2 : (2 : ℝ) ^ ⌈12 * Real.log L⌉₊ = Real.exp (⌈12 * Real.log L⌉₊ * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  refine ⟨hJu, ?_, ?_⟩
  · rw [hexpL, hexp2]
    apply Real.exp_le_exp.2
    push_cast
    nlinarith
  · rw [hexpL, hexp2, show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm,
      ← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [Real.log_exp]
    push_cast
    nlinarith

/-- **The comparison error is below the main term.**  Each of the three error pieces is at most
`h/(108000 log L · L²)`. -/
theorem mt_all_interval_error_small {x L h h₁ T₀ C ε c : ℝ} {J : ℕ} (hL16 : 16 ≤ L)
    (hLx : Real.log (8 * x) ≤ 2 * L) (hx1 : 1 ≤ x) (hh : 0 ≤ h)
    (hJ : (J : ℝ) ≤ 12 * Real.log L + 1) (hJ8 : L ^ 8 ≤ (2 : ℝ) ^ J)
    (hT₀ : T₀ ^ 2 * h₁ / x ≤ Real.exp (-(c / 16) * Real.sqrt L))
    (hL2 : (11 + 96 * Real.log L) * Real.log L * 1296000 * Real.sqrt C ≤ L ^ (ε / 20))
    (hL3 : 26000 * Real.exp (-(c / 16) * Real.sqrt L) * (108000 * Real.log L * L ^ 2) ≤ 1)
    (hL4 : 124800 * 108000 * Real.log L ≤ L ^ 3) :
    (3 + 8 * J) * (12 * Real.sqrt C * L ^ (-(2 + ε / 20))) * h + 26000 * T₀ ^ 2 * h * h₁ / x
        + 10400 * h * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) / 2 ^ J ≤
      3 * (h / (108000 * Real.log L * L ^ 2)) := by
  have hL0 : 0 < L := by linarith
  have hlL : 0 < Real.log L := Real.log_pos (by linarith)
  set D := 108000 * Real.log L * L ^ 2 with hD
  have hD0 : 0 < D := by positivity
  set u := L ^ (ε / 20) with hu
  have hu0 : 0 < u := by positivity
  have hsC : 0 ≤ Real.sqrt C := Real.sqrt_nonneg C
  -- piece 1
  have hLu : L ^ (-(2 + ε / 20)) = 1 / (L ^ 2 * u) := by
    rw [hu, Real.rpow_neg hL0.le, ← Real.rpow_natCast L 2, ← Real.rpow_add hL0]
    push_cast; ring_nf
  have p1 : (3 + 8 * J) * (12 * Real.sqrt C * L ^ (-(2 + ε / 20))) ≤ 1 / D := by
    rw [hLu, hD, show (3 + 8 * (J : ℝ)) * (12 * Real.sqrt C * (1 / (L ^ 2 * u))) =
      (3 + 8 * J) * (12 * Real.sqrt C) / (L ^ 2 * u) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (3 + 8 * (J : ℝ)) ≤ 11 + 96 * Real.log L := by linarith
    have h2 : (3 + 8 * (J : ℝ)) * (12 * Real.sqrt C * 1) * (108000 * Real.log L) ≤ u := by
      have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 1296000 * Real.sqrt C * Real.log L)
      nlinarith
    have hL2' : 0 ≤ L ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hL2']
  -- piece 2
  have p2 : 26000 * T₀ ^ 2 * h * h₁ / x ≤ h / D := by
    have hx0 : 0 < x := by linarith
    have e : 26000 * T₀ ^ 2 * h * h₁ / x = 26000 * h * (T₀ ^ 2 * h₁ / x) := by ring
    rw [e, le_div_iff₀ hD0]
    have h26 : 26000 * (T₀ ^ 2 * h₁ / x) * D ≤ 1 := by
      calc 26000 * (T₀ ^ 2 * h₁ / x) * D ≤ 26000 * Real.exp (-(c / 16) * Real.sqrt L) * D := by
            gcongr
        _ ≤ 1 := hL3
    nlinarith
  -- piece 3
  have p3 : 10400 * h * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) / 2 ^ J ≤ h / D := by
    have hl8 : 0 ≤ Real.log (8 * x) := Real.log_nonneg (by linarith)
    have hpow : (0 : ℝ) < 2 ^ J := by positivity
    rw [div_le_div_iff₀ hpow hD0]
    have hnum : Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) ≤ 12 * L ^ 3 := by
      have h1 : Real.log (8 * x) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
      have h2 : 1 + Real.log (8 * x) ≤ 3 * L := by linarith
      calc Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) ≤ (4 * L ^ 2) * (3 * L) := by gcongr
        _ = 12 * L ^ 3 := by ring
    have hK : 124800 * D ≤ L ^ 5 := by
      rw [hD]
      have : L ^ 5 = L ^ 3 * L ^ 2 := by ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_right hL4 (by positivity : (0 : ℝ) ≤ L ^ 2)]
    calc 10400 * h * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) * D
        = 10400 * h * (Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x))) * D := by ring
      _ ≤ 10400 * h * (12 * L ^ 3) * D := by gcongr
      _ = h * L ^ 3 * (124800 * D) := by ring
      _ ≤ h * L ^ 3 * L ^ 5 := by gcongr
      _ = h * L ^ 8 := by ring
      _ ≤ h * 2 ^ J := by gcongr
  have p1' : (3 + 8 * J) * (12 * Real.sqrt C * L ^ (-(2 + ε / 20))) * h ≤ h / D := by
    calc (3 + 8 * J) * (12 * Real.sqrt C * L ^ (-(2 + ε / 20))) * h ≤ 1 / D * h :=
          mul_le_mul_of_nonneg_right p1 hh
      _ = h / D := by ring
  linarith

/-- **The main term survives the comparison factor.**  If `S₁ ≥ h₁ m`, `h, h₁ ≥ 2`,
`H ≥ h - 1` and `0 < H₁ ≤ h₁ + 1`, then `(H/H₁) S₁ ≥ h m/4`. -/
theorem mt_all_interval_main_term {S₁ h h₁ H H₁ m : ℝ} (hh : 2 ≤ h) (hh₁ : 2 ≤ h₁)
    (hH : h - 1 ≤ H) (hH₁ : H₁ ≤ h₁ + 1) (hH₁0 : 0 < H₁) (hm : 0 ≤ m) (hS : h₁ * m ≤ S₁) :
    h * m / 4 ≤ H / H₁ * S₁ := by
  have hS0 : 0 ≤ S₁ := le_trans (by positivity) hS
  have h1 : (h - 1) / (h₁ + 1) ≤ H / H₁ := by
    rw [div_le_div_iff₀ (by linarith) hH₁0]
    have : (h - 1) * H₁ ≤ (h - 1) * (h₁ + 1) := mul_le_mul_of_nonneg_left hH₁ (by linarith)
    nlinarith
  have h2 : h * m / 4 ≤ (h - 1) / (h₁ + 1) * (h₁ * m) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    have : h * (h₁ + 1) ≤ 4 * ((h - 1) * h₁) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hm]
  calc h * m / 4 ≤ (h - 1) / (h₁ + 1) * (h₁ * m) := h2
    _ ≤ H / H₁ * S₁ := mul_le_mul h1 hS (mul_nonneg (by linarith) hm)
        (le_trans (div_nonneg (by linarith) (by linarith)) h1)

/-- The growth facts in `L = log x` used by the all-interval theorem. -/
theorem mt_all_interval_log_facts {C c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, 16 ≤ L ∧
      (11 + 96 * Real.log L) * Real.log L * 1296000 * Real.sqrt C ≤ L ^ (ε / 20) ∧
      26000 * Real.exp (-(c / 16) * Real.sqrt L) * (108000 * Real.log L * L ^ 2) ≤ 1 ∧
      124800 * 108000 * Real.log L ≤ L ^ 3 ∧ Real.exp (-(c / 8) * Real.sqrt L) ≤ 1 / 2 := by
  set K : ℝ := 26000 * 108000 with hK
  set b : ℝ := c / 16 with hb
  have hb0 : 0 < b := by positivity
  filter_upwards [eventually_ge_atTop (16 : ℝ),
    eventually_polylog_le_rpow 2 (C := 107 * (1296000 * Real.sqrt C)) (κ := ε / 20)
      (by positivity) (by positivity),
    eventually_ge_atTop ((5040 * K / b ^ 7) ^ 2), eventually_ge_atTop (124800 * 108000 : ℝ),
    eventually_ge_atTop ((8 / c) ^ 2)] with L hL16 hpoly hLb hL4 hL5
  have hL0 : 0 < L := by linarith
  have hlL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogL : Real.log L ≤ L := by have := Real.log_le_sub_one_of_pos hL0; linarith
  refine ⟨hL16, ?_, ?_, ?_, ?_⟩
  · have hm : Real.log L ≤ 1 + Real.log (24 * L) := by
      rw [Real.log_mul (by norm_num) hL0.ne']
      have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
      linarith
    have h1 : (11 + 96 * Real.log L) * Real.log L ≤ 107 * (1 + Real.log (24 * L)) ^ 2 := by
      set m := 1 + Real.log (24 * L) with hmdef
      have hm1 : 1 ≤ m := by
        rw [hmdef, Real.log_mul (by norm_num) hL0.ne']
        have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
        linarith
      have hsq : Real.log L * Real.log L ≤ m * m := mul_le_mul hm hm hlL (by linarith)
      have hmm : m ≤ m * m := by nlinarith
      nlinarith
    have hsC : 0 ≤ 1296000 * Real.sqrt C := by positivity
    calc (11 + 96 * Real.log L) * Real.log L * 1296000 * Real.sqrt C
        = ((11 + 96 * Real.log L) * Real.log L) * (1296000 * Real.sqrt C) := by ring
      _ ≤ (107 * (1 + Real.log (24 * L)) ^ 2) * (1296000 * Real.sqrt C) :=
          mul_le_mul_of_nonneg_right h1 hsC
      _ = 107 * (1296000 * Real.sqrt C) * (1 + Real.log (24 * L)) ^ 2 := by ring
      _ ≤ L ^ (ε / 20) := hpoly
  · -- `K log L · L² ≤ K u⁶ ≤ (bu)⁷/7! ≤ exp(bu)` with `u = √L`
    set u := Real.sqrt L with hu
    have hu0 : 0 ≤ u := Real.sqrt_nonneg L
    have hu2 : u ^ 2 = L := Real.sq_sqrt hL0.le
    have hub : 5040 * K / b ^ 7 ≤ u := by
      rw [hu, Real.le_sqrt (by positivity) hL0.le]; exact hLb
    have hexp := Real.pow_div_factorial_le_exp (b * u) (by positivity) 7
    have h7 : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]
    rw [h7] at hexp
    have hKu : K * u ^ 6 ≤ (b * u) ^ 7 / 5040 := by
      rw [le_div_iff₀ (by norm_num), mul_pow]
      have : 5040 * K ≤ b ^ 7 * u := by
        rw [div_le_iff₀ (by positivity)] at hub; linarith
      have hu6 : 0 ≤ u ^ 6 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right this hu6]
    have hL3 : 108000 * Real.log L * L ^ 2 * 26000 ≤ K * u ^ 6 := by
      rw [hK, show u ^ 6 = (u ^ 2) ^ 3 by ring, hu2]
      have : Real.log L * L ^ 2 ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right hlogL (by positivity)
      nlinarith
    have hE : Real.exp (-(c / 16) * u) * Real.exp (b * u) = 1 := by
      rw [← Real.exp_add, hb]; simp
    have hEpos : 0 < Real.exp (-(c / 16) * u) := Real.exp_pos _
    calc 26000 * Real.exp (-(c / 16) * u) * (108000 * Real.log L * L ^ 2)
        = Real.exp (-(c / 16) * u) * (108000 * Real.log L * L ^ 2 * 26000) := by ring
      _ ≤ Real.exp (-(c / 16) * u) * Real.exp (b * u) :=
          mul_le_mul_of_nonneg_left (hL3.trans (hKu.trans hexp)) hEpos.le
      _ = 1 := hE
  · have hK1 : (1 : ℝ) ≤ 124800 * 108000 := by norm_num
    calc 124800 * 108000 * Real.log L ≤ L * L := mul_le_mul hL4 hlogL hlL (by linarith)
      _ ≤ L ^ 3 := by nlinarith
  · have hsq : 8 / c ≤ Real.sqrt L := by
      rw [Real.le_sqrt (by positivity) hL0.le]; exact hL5
    have hle : -(c / 8) * Real.sqrt L ≤ -1 := by
      have : c / 8 * (8 / c) = 1 := by field_simp
      nlinarith
    calc Real.exp (-(c / 8) * Real.sqrt L) ≤ Real.exp (-1) := Real.exp_le_exp.2 hle
      _ ≤ 1 / 2 := Real.exp_neg_one_lt_half.le

/-- Eventually `z = ⌈X^{2/11}⌉` satisfies `2 ≤ z` and `4X < z⁶`. -/
theorem eventually_mtProposition22ZNat_facts :
    ∀ᶠ X : ℝ in atTop, 2 ≤ mtProposition22ZNat X ∧ 4 * X < (mtProposition22ZNat X : ℝ) ^ 6 := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 11)).eventually_ge_atTop 5,
    eventually_gt_atTop (1 : ℝ)] with X h11 hX1
  have hX0 : 0 < X := by linarith
  have hzR : X ^ (2 / 11 : ℝ) ≤ (mtProposition22ZNat X : ℝ) := Nat.le_ceil _
  have h11' : X ^ (1 / 11 : ℝ) ≤ X ^ (2 / 11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
  refine ⟨?_, ?_⟩
  · have : (2 : ℝ) ≤ (mtProposition22ZNat X : ℝ) := by linarith
    exact_mod_cast this
  · have h12 : X ^ (12 / 11 : ℝ) ≤ (mtProposition22ZNat X : ℝ) ^ 6 := by
      calc X ^ (12 / 11 : ℝ) = (X ^ (2 / 11 : ℝ)) ^ 6 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
        _ ≤ (mtProposition22ZNat X : ℝ) ^ 6 := pow_le_pow_left₀ (by positivity) hzR 6
    have hs : X ^ (12 / 11 : ℝ) = X ^ (1 / 11 : ℝ) * X := by
      rw [← Real.rpow_add_one hX0.ne']; norm_num
    nlinarith

/-- `2^{11/10} ≤ 3`. -/
theorem two_rpow_eleven_tenths_le_three : (2 : ℝ) ^ (11 / 10 : ℝ) ≤ 3 := by
  have h : ((2 : ℝ) ^ (11 / 10 : ℝ)) ^ (10 : ℕ) ≤ (3 : ℝ) ^ (10 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).1 h

/-- The scale `X = √(xP₁)` of the all-interval theorem. -/
theorem mt_all_interval_scale_X {x L a P₁ X : ℝ} (hx : 0 < x) (hL : L = Real.log x)
    (hL16 : 16 ≤ L) (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) (hP : P₁ = L ^ a)
    (hX : X = Real.sqrt (x * P₁)) (h64 : 64 * L ^ 2 ≤ x) :
    2 ≤ P₁ ∧ P₁ ≤ L ^ 2 ∧ P₁ ≤ L ^ (11 / 10 : ℝ) ∧ Real.sqrt x ≤ X ∧ X ≤ Real.sqrt x * L ∧
      X ^ 2 = x * P₁ ∧ L / 2 ≤ Real.log X ∧ Real.log X ≤ L ∧ 8 * P₁ ≤ X := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hPL : L ≤ P₁ := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 ha1; rwa [Real.rpow_one, ← hP] at this
  have hP11 : P₁ ≤ L ^ (11 / 10 : ℝ) := hP ▸ Real.rpow_le_rpow_of_exponent_le hL1 ha11
  have hL112 : L ^ (11 / 10 : ℝ) ≤ L ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (11 / 10 : ℝ) ≤ 2)
    rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hPL2 : P₁ ≤ L ^ 2 := hP11.trans hL112
  have hP0 : 0 < P₁ := by linarith
  have hxP : 0 < x * P₁ := by positivity
  have hXsq : X ^ 2 = x * P₁ := by rw [hX]; exact Real.sq_sqrt hxP.le
  -- `log L ≤ L/2`
  have hsL : 4 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hlogL2 : Real.log L ≤ L / 2 := by
    have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0.le
    have h1 : Real.log L = 2 * Real.log (Real.sqrt L) := by
      rw [← Real.log_rpow (by linarith), show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, hsq]
    have h2 := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt L by linarith)
    nlinarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogX : Real.log X = (L + a * Real.log L) / 2 := by
    rw [hX, Real.log_sqrt hxP.le, Real.log_mul hx.ne' hP0.ne', hP, Real.log_rpow hL0, hL]
  refine ⟨by linarith, hPL2, hP11, ?_, ?_, hXsq, ?_, ?_, ?_⟩
  · rw [hX]; exact Real.sqrt_le_sqrt (le_mul_of_one_le_right hx.le (by linarith))
  · rw [hX, show Real.sqrt x * L = Real.sqrt (x * L ^ 2) by
      rw [Real.sqrt_mul hx.le, Real.sqrt_sq hL0.le]]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hPL2 hx.le)
  · rw [hlogX]; have : 0 ≤ a * Real.log L := by positivity
    linarith
  · rw [hlogX]
    have : a * Real.log L ≤ 11 / 10 * (L / 2) :=
      mul_le_mul ha11 hlogL2 hlogL0 (by norm_num)
    linarith
  · rw [hX, Real.le_sqrt (by positivity) hxP.le]
    have : 64 * P₁ ≤ x := by nlinarith
    nlinarith

/-- The scale `R = √(x/P₁)/2`: `RX = x/2`, `R ≥ √x/(2L) ≥ x^{1/3}`, `log R ≥ L/3`. -/
theorem mt_all_interval_scale_R {x L P₁ X R : ℝ} (hx : 0 < x) (hL : L = Real.log x)
    (hL1 : 1 ≤ L) (hP0 : 0 < P₁) (hPL2 : P₁ ≤ L ^ 2) (hX : X = Real.sqrt (x * P₁))
    (hR : R = Real.sqrt (x / P₁) / 2) (hL6 : 2 * L ≤ x ^ (1 / 6 : ℝ)) :
    R * X = x / 2 ∧ Real.sqrt x / (2 * L) ≤ R ∧ x ^ (1 / 3 : ℝ) ≤ R ∧ L / 3 ≤ Real.log R := by
  have hL0 : 0 < L := by linarith
  have hRX : R * X = x / 2 := by
    rw [hR, hX, div_mul_eq_mul_div, ← Real.sqrt_mul (by positivity),
      show x / P₁ * (x * P₁) = x ^ 2 by field_simp, Real.sqrt_sq hx.le]
  have hRge : Real.sqrt x / (2 * L) ≤ R := by
    have h1 : Real.sqrt (x / L ^ 2) ≤ Real.sqrt (x / P₁) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hx.le hP0 hPL2)
    rw [Real.sqrt_div hx.le, Real.sqrt_sq hL0.le] at h1
    rw [hR, show Real.sqrt x / (2 * L) = Real.sqrt x / L / 2 by field_simp]
    linarith
  have hx13 : x ^ (1 / 3 : ℝ) ≤ R := by
    refine le_trans ?_ hRge
    rw [le_div_iff₀ (by positivity)]
    have hs : Real.sqrt x = x ^ (1 / 3 : ℝ) * x ^ (1 / 6 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]; norm_num
    rw [hs]
    exact mul_le_mul_of_nonneg_left hL6 (by positivity)
  refine ⟨hRX, hRge, hx13, ?_⟩
  have := Real.log_le_log (by positivity) hx13
  rwa [Real.log_rpow hx, ← hL, show 1 / 3 * L = L / 3 by ring] at this

/-- The windows `h = XL`, `h₁ = x e^{-(c/8)√L}`, the height `T₁ = x/h` and the cutoff
`T₀ = exp((c/32)(log X)^{1/2})`. -/
theorem mt_all_interval_scale_h {x L c P₁ X R T₀ : ℝ} (hx : 0 < x) (hL : L = Real.log x)
    (hL1 : 1 ≤ L) (hc : 0 < c) (hLc : c ^ 2 / 4 ≤ L) (hsX : Real.sqrt x ≤ X)
    (hXle : X ≤ Real.sqrt x * L) (hXsq : X ^ 2 = x * P₁) (hlogX0 : 0 ≤ Real.log X)
    (hlogX : Real.log X ≤ L) (hRX : R * X = x / 2) (hsx1 : 1 ≤ Real.sqrt x)
    (hL2x : L ^ 2 ≤ x ^ (1 / 4 : ℝ)) (hh₁2 : Real.exp (-(c / 8) * Real.sqrt L) ≤ 1 / 2)
    (hT₀ : T₀ = Real.exp (c / 32 * Real.log X ^ ((1 : ℝ) / 2))) :
    1 ≤ X * L ∧ x / (X * L) ≤ Real.sqrt x ∧ x ^ (1 / 4 : ℝ) ≤ x / (X * L) ∧
      x / (X * L) * L = 2 * R ∧ P₁ * (x / (X * L)) * L = X ∧
      X * L ≤ x * Real.exp (-(c / 8) * Real.sqrt L) ∧
      x * Real.exp (-(c / 8) * Real.sqrt L) ≤ x / 2 ∧ 1 ≤ T₀ ∧ T₀ ≤ x / (X * L) ∧
      T₀ ^ 2 * (x * Real.exp (-(c / 8) * Real.sqrt L)) / x ≤
        Real.exp (-(c / 16) * Real.sqrt L) := by
  have hL0 : 0 < L := by linarith
  have hX0 : 0 < X := by linarith
  have hh0 : 0 < X * L := by positivity
  have hsx2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  have hs4 : Real.sqrt x = x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]; norm_num
  have hx4 : x ^ (1 / 4 : ℝ) = Real.exp (L / 4) := by
    rw [Real.rpow_def_of_pos hx, ← hL]; ring_nf
  -- `(c/8)√L ≤ L/4`
  have hcL : c / 8 * Real.sqrt L ≤ L / 4 := by
    have hsq : c / 2 ≤ Real.sqrt L := by
      rw [Real.le_sqrt (by positivity) hL0.le]; linarith
    have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
    nlinarith [Real.sqrt_nonneg L]
  have hE8 : Real.exp (c / 8 * Real.sqrt L) ≤ x ^ (1 / 4 : ℝ) := by
    rw [hx4]; exact Real.exp_le_exp.2 hcL
  -- `(log X)^{1/2} ≤ √L`
  have hsqX : Real.log X ^ ((1 : ℝ) / 2) ≤ Real.sqrt L := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow hlogX0 hlogX (by norm_num)
  have hT₀le : T₀ ≤ Real.exp (c / 32 * Real.sqrt L) := by
    rw [hT₀]; exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hsqX (by positivity))
  have hhs : Real.sqrt x ≤ X * L := by
    calc Real.sqrt x = Real.sqrt x * 1 := (mul_one _).symm
      _ ≤ X * L := mul_le_mul hsX hL1 zero_le_one hX0.le
  have hhle : X * L ≤ Real.sqrt x * L ^ 2 := by
    calc X * L ≤ Real.sqrt x * L * L := mul_le_mul_of_nonneg_right hXle hL0.le
      _ = Real.sqrt x * L ^ 2 := by ring
  have hT₁le : x / (X * L) ≤ Real.sqrt x := by
    rw [div_le_iff₀ hh0]
    calc x = Real.sqrt x * Real.sqrt x := hsx2.symm
      _ ≤ Real.sqrt x * (X * L) := mul_le_mul_of_nonneg_left hhs (Real.sqrt_nonneg x)
  have hT₁ge : x ^ (1 / 4 : ℝ) ≤ x / (X * L) := by
    rw [le_div_iff₀ hh0]
    calc x ^ (1 / 4 : ℝ) * (X * L) ≤ x ^ (1 / 4 : ℝ) * (Real.sqrt x * L ^ 2) :=
          mul_le_mul_of_nonneg_left hhle (by positivity)
      _ ≤ x ^ (1 / 4 : ℝ) * (Real.sqrt x * x ^ (1 / 4 : ℝ)) := by gcongr
      _ = Real.sqrt x * Real.sqrt x := by rw [hs4]; ring
      _ = x := hsx2
  have hT₁L : x / (X * L) * L = 2 * R := by
    have : x / (X * L) * L = x / X := by field_simp
    rw [this, eq_comm, show 2 * R = 2 * (R * X) / X by field_simp, hRX]; ring
  refine ⟨hsx1.trans hhs, hT₁le, hT₁ge, hT₁L, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, hT₁L]
    have : P₁ * (2 * R) * X = X * X := by
      rw [mul_assoc, mul_assoc, hRX]; nlinarith [hXsq]
    exact mul_right_cancel₀ hX0.ne' this
  · -- `XL ≤ √x L² ≤ x^{1/4}·x^{1/4}·x^{1/4}·... ≤ x e^{-(c/8)√L}`
    have hE : Real.exp (-(c / 8) * Real.sqrt L) * Real.exp (c / 8 * Real.sqrt L) = 1 := by
      rw [← Real.exp_add]; simp
    have hEp : 0 < Real.exp (-(c / 8) * Real.sqrt L) := Real.exp_pos _
    have h1 : Real.sqrt x * (L ^ 2 * Real.exp (c / 8 * Real.sqrt L)) ≤ x := by
      calc Real.sqrt x * (L ^ 2 * Real.exp (c / 8 * Real.sqrt L))
          ≤ Real.sqrt x * (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by gcongr
        _ = x := by rw [← hs4, hsx2]
    calc X * L ≤ Real.sqrt x * L ^ 2 := hhle
      _ = Real.sqrt x * (L ^ 2 * Real.exp (c / 8 * Real.sqrt L)) *
            Real.exp (-(c / 8) * Real.sqrt L) := by
          rw [mul_assoc, mul_assoc, mul_comm (Real.exp (c / 8 * _)), hE, mul_one]
      _ ≤ x * Real.exp (-(c / 8) * Real.sqrt L) := mul_le_mul_of_nonneg_right h1 hEp.le
  · have := mul_le_mul_of_nonneg_left hh₁2 hx.le
    linarith
  · rw [hT₀]; exact Real.one_le_exp (by positivity)
  · refine hT₀le.trans (le_trans ?_ hT₁ge)
    refine le_trans (Real.exp_le_exp.2 ?_) hE8
    have : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    nlinarith
  · have hT2 : T₀ ^ 2 ≤ Real.exp (c / 16 * Real.sqrt L) := by
      calc T₀ ^ 2 ≤ Real.exp (c / 32 * Real.sqrt L) ^ 2 :=
            pow_le_pow_left₀ (by rw [hT₀]; positivity) hT₀le 2
        _ = Real.exp (c / 16 * Real.sqrt L) := by rw [← Real.exp_nat_mul]; ring_nf
    have e : T₀ ^ 2 * (x * Real.exp (-(c / 8) * Real.sqrt L)) / x =
        T₀ ^ 2 * Real.exp (-(c / 8) * Real.sqrt L) := by field_simp
    rw [e]
    calc T₀ ^ 2 * Real.exp (-(c / 8) * Real.sqrt L)
        ≤ Real.exp (c / 16 * Real.sqrt L) * Real.exp (-(c / 8) * Real.sqrt L) :=
          mul_le_mul_of_nonneg_right hT2 (Real.exp_pos _).le
      _ = Real.exp (-(c / 16) * Real.sqrt L) := by rw [← Real.exp_add]; ring_nf

/-- The source scale `Y = ⌊X/P₁⌋ - 1`: `X^{1-ε/100} < Y ≤ X/2` and `X ≤ 2P₁Y`. -/
theorem mt_all_interval_scale_Y {x L X P₁ ε : ℝ} (hε : 0 < ε) (hP2 : 2 ≤ P₁)
    (hPL2 : P₁ ≤ L ^ 2) (hL1 : 1 ≤ L) (hx : 0 < x) (hXP : 8 * P₁ ≤ X)
    (hsX : Real.sqrt x ≤ X) (hLε : 4 * L ^ 2 ≤ x ^ (ε / 200)) :
    1 ≤ ⌊X / P₁⌋₊ - 1 ∧ X ^ (1 - ε / 100) < ((⌊X / P₁⌋₊ - 1 : ℕ) : ℝ) ∧
      ((⌊X / P₁⌋₊ - 1 : ℕ) : ℝ) ≤ X / 2 ∧ X ≤ 2 * P₁ * ((⌊X / P₁⌋₊ - 1 : ℕ) : ℝ) := by
  have hP0 : 0 < P₁ := by linarith
  have hX0 : 0 < X := by linarith
  have hV8 : 8 ≤ X / P₁ := by rw [le_div_iff₀ hP0]; linarith
  have hfl8 : 8 ≤ ⌊X / P₁⌋₊ := Nat.le_floor (by exact_mod_cast hV8)
  have hYR : ((⌊X / P₁⌋₊ - 1 : ℕ) : ℝ) = (⌊X / P₁⌋₊ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  have hflV : (⌊X / P₁⌋₊ : ℝ) ≤ X / P₁ := Nat.floor_le (by linarith)
  have hVfl : X / P₁ < (⌊X / P₁⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hYlo : X / P₁ / 2 ≤ ((⌊X / P₁⌋₊ - 1 : ℕ) : ℝ) := by rw [hYR]; linarith
  have hVX : X / P₁ ≤ X / 2 := div_le_div_of_nonneg_left hX0.le (by norm_num) hP2
  refine ⟨by omega, ?_, by rw [hYR]; linarith, ?_⟩
  · have hXe : x ^ (ε / 200) ≤ X ^ (ε / 100) := by
      have h1 : x ^ (ε / 200) = Real.sqrt x ^ (ε / 100) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]; ring_nf
      rw [h1]; exact Real.rpow_le_rpow (Real.sqrt_nonneg x) hsX (by positivity)
    have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
    have h2P : 2 * P₁ < X ^ (ε / 100) := by linarith
    have hsplit : X ^ (1 - ε / 100) = X / X ^ (ε / 100) := by
      rw [Real.rpow_sub hX0, Real.rpow_one]
    rw [hsplit]
    have h1 : X / X ^ (ε / 100) < X / (2 * P₁) := div_lt_div_of_pos_left hX0 (by positivity) h2P
    have hV2 : X / (2 * P₁) = X / P₁ / 2 := by field_simp
    linarith
  · have hXV : X = P₁ * (X / P₁) := by field_simp
    calc X = P₁ * (X / P₁) := hXV
      _ = 2 * P₁ * (X / P₁ / 2) := by ring
      _ ≤ 2 * P₁ * ((⌊X / P₁⌋₊ - 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hYlo (by positivity)

/-- The Perron height `T₁ 2^J` stays below `R^{201/200}`. -/
theorem mt_all_interval_height_le {x L R T₁ : ℝ} {J : ℕ} (hx : 0 < x) (hL1 : 1 ≤ L)
    (hT₁ : T₁ ≤ Real.sqrt x) (hJ : (2 : ℝ) ^ J ≤ 2 * L ^ 9) (hR : Real.sqrt x / (2 * L) ≤ R)
    (hx13 : x ^ (1 / 3 : ℝ) ≤ R) (hL10 : 4 * L ^ 10 ≤ x ^ (1 / 600 : ℝ)) :
    T₁ * 2 ^ J ≤ R ^ (201 / 200 : ℝ) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hx13
  have hL0 : 0 < L := by linarith
  have hRsplit : R ^ (201 / 200 : ℝ) = R * R ^ (1 / 200 : ℝ) := by
    rw [show (201 / 200 : ℝ) = 1 + 1 / 200 by norm_num, Real.rpow_add hR0, Real.rpow_one]
  have hR200 : x ^ (1 / 600 : ℝ) ≤ R ^ (1 / 200 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hx13 (by norm_num : (0 : ℝ) ≤ 1 / 200)
    rwa [← Real.rpow_mul hx.le, show (1 / 3 : ℝ) * (1 / 200) = 1 / 600 by norm_num] at this
  rw [hRsplit]
  calc T₁ * 2 ^ J ≤ Real.sqrt x * (2 * L ^ 9) :=
        mul_le_mul hT₁ hJ (by positivity) (Real.sqrt_nonneg x)
    _ = Real.sqrt x / (2 * L) * (4 * L ^ 10) := by field_simp; ring
    _ ≤ R * x ^ (1 / 600 : ℝ) := mul_le_mul hR hL10 (by positivity) hR0.le
    _ ≤ R * R ^ (1 / 200 : ℝ) := mul_le_mul_of_nonneg_left hR200 hR0.le

/-- **The `E₃` comparison at one `x`, for any set `B₁` of small primes.**  Under the growth facts
in `L = log x`, a one-sided mean square `64 L^{-(2+ε/10)}(1 + T/T₁)` for `P_{B₁}P` above `T₀` and
the improved mean value theorem for `P₂`, the short window `h = XL` differs from `H/H₁` times the
long window `h₁ = x e^{-(c/8)√L}` by at most `3h/(108000 log L · L²)`. -/
theorem mt_all_interval_compare_small_on {B₁ : Finset ℕ} {x L a c C₂ ε P₁ R₀ : ℝ} {z Q D E : ℕ}
    (hx : 0 < x) (hL : L = Real.log x) (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) (hP : P₁ = L ^ a)
    (hc : 0 < c) (hC₂ : 0 < C₂) (hε0 : 0 < ε) (hL16 : 16 ≤ L)
    (hB₁ : ∀ p ∈ B₁, p.Prime ∧ P₁ < p ∧ (p : ℝ) ≤ 2 * P₁)
    (hLf2 : (11 + 96 * Real.log L) * Real.log L * 1296000 * Real.sqrt (4 * C₂) ≤ L ^ (ε / 20))
    (hLf3 : 26000 * Real.exp (-(c / 16) * Real.sqrt L) * (108000 * Real.log L * L ^ 2) ≤ 1)
    (hLf4 : 124800 * 108000 * Real.log L ≤ L ^ 3)
    (hLf5 : Real.exp (-(c / 8) * Real.sqrt L) ≤ 1 / 2) (hLc : c ^ 2 / 4 ≤ L)
    (h64 : 64 * L ^ 2 ≤ x) (hL2x : L ^ 2 ≤ x ^ (1 / 4 : ℝ)) (hLε : 4 * L ^ 2 ≤ x ^ (ε / 200))
    (hL6 : 2 * L ≤ x ^ (1 / 6 : ℝ)) (hL10 : 4 * L ^ 10 ≤ x ^ (1 / 600 : ℝ))
    (hsx1 : 1 ≤ Real.sqrt x) (hRx : max R₀ 1 ^ 3 ≤ x)
    (hz2 : 2 ≤ z) (hz6 : 4 * Real.sqrt (x * P₁) < (z : ℝ) ^ 6)
    (hαB : ∀ T, Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2)) ≤ T →
      T ≤ x / (Real.sqrt (x * P₁) * L) * 2 ^ ⌈12 * Real.log L⌉₊ →
      ∫ t in Set.Icc (Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2))) T,
          ‖(∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
            LSeries (fun n => mtHarmanProposition22SourceAF z Q D E
              (⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1) n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
        64 * L ^ (-(2 + ε / 10)) * (1 + T / (x / (Real.sqrt (x * P₁) * L))))
    (hP2 : ∀ R' : ℝ, R₀ ≤ R' → ∀ T : ℝ, 1 ≤ T → T ≤ R' ^ (201 / 200 : ℝ) →
      ∫ t in Set.Icc (-T) T,
          ‖∑ p ∈ (Finset.Ioc ⌊R'⌋₊ ⌊2 * R'⌋₊).filter Nat.Prime,
            (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ^ 2 ≤
        C₂ * (T / (R' * Real.log R') + 1 / Real.log R' ^ 2)) :
    |mtAllIntervalSumOn B₁ ((Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊
          ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime) z Q D E x (Real.sqrt (x * P₁) * L) -
        (((⌊x + Real.sqrt (x * P₁) * L⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) /
          ((⌊x + x * Real.exp (-(c / 8) * Real.sqrt L)⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) *
          mtAllIntervalSumOn B₁ ((Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊
            ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime) z Q D E x
            (x * Real.exp (-(c / 8) * Real.sqrt L))|
      ≤ 3 * (Real.sqrt (x * P₁) * L / (108000 * Real.log L * L ^ 2)) := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hx1 : 1 ≤ x := by nlinarith
  obtain ⟨hP2', hPL2, hP11, hsX, hXle, hXsq, hlogXlo, hlogXhi, hXP⟩ :=
    mt_all_interval_scale_X hx hL hL16 ha1 ha11 hP rfl h64
  have hP0 : 0 < P₁ := by linarith
  obtain ⟨hRX, hRge, hx13, hlogR⟩ := mt_all_interval_scale_R hx hL hL1 hP0 hPL2 rfl rfl hL6
  have hlogX0 : 0 ≤ Real.log (Real.sqrt (x * P₁)) := by linarith
  obtain ⟨hh1, hT₁le, hT₁ge, hT₁L, hPT₁L, hhh₁, hh₁x, hT₀1, hT₀₁, hT₀h₁⟩ :=
    mt_all_interval_scale_h (T₀ := Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2)))
      hx hL hL1 hc hLc hsX hXle hXsq hlogX0 hlogXhi hRX hsx1 hL2x hLf5 rfl
  obtain ⟨hY1, hYX1, hYX2, hYX3⟩ := mt_all_interval_scale_Y hε0 hP2' hPL2 hL1 hx hXP hsX hLε
  obtain ⟨hJ1, hJ8, hJ9⟩ := ceil_twelve_log_facts hL1
  have hheight := mt_all_interval_height_le hx hL1 hT₁le hJ9 hRge hx13 hL10
  have hX0 : 0 < Real.sqrt (x * P₁) := by linarith
  have hT₁0 : 0 < x / (Real.sqrt (x * P₁) * L) := by positivity
  have hRR₀ : R₀ ≤ Real.sqrt (x / P₁) / 2 := by
    have h1 : max R₀ 1 ≤ x ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hRx (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at this
    linarith [le_max_left R₀ 1]
  have hYz : 4 * (⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1) < z ^ 6 := by
    have : ((4 * (⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1) : ℕ) : ℝ) < ((z ^ 6 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hβ : ∀ T, Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2)) ≤ T →
      T ≤ x / (Real.sqrt (x * P₁) * L) * 2 ^ ⌈12 * Real.log L⌉₊ →
      ∫ t in Set.Icc (-T) T, ‖∑ p ∈ (Finset.Ioc ⌊Real.sqrt (x / P₁) / 2⌋₊
          ⌊2 * (Real.sqrt (x / P₁) / 2)⌋₊).filter Nat.Prime,
          (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ^ 2 ≤
        9 * C₂ / L ^ 2 * (1 + T / (x / (Real.sqrt (x * P₁) * L))) := by
    intro T hT hTJ
    refine (hP2 _ hRR₀ T (hT₀1.trans hT) (hTJ.trans hheight)).trans ?_
    exact mt_meanSquare_affine_beta hC₂.le hL0 (lt_of_lt_of_le (by positivity) hx13) hlogR hT₁0
      hT₁L.le (by linarith)
  have hR0 : 0 ≤ Real.sqrt (x / P₁) / 2 := by positivity
  have hcomp := abs_mtAllIntervalSumOn_compare_le_of_meanSquares (Q := Q) (D := D) (E := E)
    ⌈12 * Real.log L⌉₊ (by linarith) hP2' hXP hh1 hhh₁ hh₁x hB₁
    (fun p hp => (mem_primes_Ioc_floor_iff hR0).1 hp) hz2 hYz (by linarith) hT₀₁
    (by positivity) (by positivity) hαB hβ
  rw [show 64 * L ^ (-(2 + ε / 10)) * (9 * C₂ / L ^ 2) =
      16 * L ^ (-(2 + ε / 10)) * (9 * (4 * C₂) / L ^ 2) by ring,
    mt_sqrt_alpha_beta hL0 (by positivity : (0 : ℝ) ≤ 4 * C₂)] at hcomp
  refine hcomp.trans ?_
  have hlog8 : Real.log (8 * x) ≤ 2 * L := by
    rw [Real.log_mul (by norm_num) hx.ne', ← hL]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
    linarith
  exact mt_all_interval_error_small hL16 hlog8 hx1 (by positivity) hJ1 hJ8 hT₀h₁ hLf2 hLf3 hLf4

/-- **The claim (5.2) in affine form.**  Under the growth facts in `L = log x`, the one-sided mean
square of `P₁P` above `T₀ = exp((c/32)(log X)^{1/2})` is at most `16 L^{-(2+ε/10)}(1 + T/T₁)`,
`T₁ = x/(XL)`, for the source at `Y = ⌊X/P₁⌋ - 1`. -/
theorem mt_all_interval_harman_affine {x L a c ε P₁ : ℝ} {z Q D E : ℕ}
    (hx : 0 < x) (hL : L = Real.log x) (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) (hP : P₁ = L ^ a)
    (hc : 0 < c) (hε0 : 0 < ε) (hε10 : ε ≤ 10) (hL16 : 16 ≤ L)
    (hLf5 : Real.exp (-(c / 8) * Real.sqrt L) ≤ 1 / 2) (hLc : c ^ 2 / 4 ≤ L)
    (h64 : 64 * L ^ 2 ≤ x) (hL2x : L ^ 2 ≤ x ^ (1 / 4 : ℝ)) (hLε : 4 * L ^ 2 ≤ x ^ (ε / 200))
    (hL6 : 2 * L ≤ x ^ (1 / 6 : ℝ)) (hsx1 : 1 ≤ Real.sqrt x)
    (h52 : ∀ (P : ℝ) (B : Finset ℕ), Real.log (Real.sqrt (x * P₁)) ^ a ≤ P →
      P ≤ 3 * Real.log (Real.sqrt (x * P₁)) ^ (11 / 10 : ℝ) →
      (∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ Y : ℕ, Real.sqrt (x * P₁) ^ (1 - ε / 100) < Y → (Y : ℝ) ≤ Real.sqrt (x * P₁) / 2 →
      Real.sqrt (x * P₁) ≤ 2 * P * Y → ∀ T : ℝ, 1 ≤ T →
        ∫ t in Set.Icc (Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2))) T,
            ‖(∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
              LSeries (fun n => mtHarmanProposition22SourceAF z Q D E Y n)
                (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          2 * Real.log (Real.sqrt (x * P₁)) ^ (-(2 + ε / 10)) +
            2 * Real.log (Real.sqrt (x * P₁)) ^ (-(1 + ε / 10)) * P * T / Real.sqrt (x * P₁)) :
    ∀ T, Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2)) ≤ T →
      ∫ t in Set.Icc (Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2))) T,
          ‖(∑ p ∈ (Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime,
              (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
            LSeries (fun n => mtHarmanProposition22SourceAF z Q D E
              (⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1) n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
        16 * L ^ (-(2 + ε / 10)) * (1 + T / (x / (Real.sqrt (x * P₁) * L))) := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  obtain ⟨hP2', hPL2, hP11, hsX, hXle, hXsq, hlogXlo, hlogXhi, hXP⟩ :=
    mt_all_interval_scale_X hx hL hL16 ha1 ha11 hP rfl h64
  have hP0 : 0 < P₁ := by linarith
  obtain ⟨hRX, -, -, -⟩ := mt_all_interval_scale_R hx hL hL1 hP0 hPL2 rfl rfl hL6
  have hlogX0 : 0 ≤ Real.log (Real.sqrt (x * P₁)) := by linarith
  obtain ⟨-, -, -, -, hPT₁L, -, -, hT₀1, -, -⟩ :=
    mt_all_interval_scale_h (T₀ := Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2)))
      hx hL hL1 hc hLc hsX hXle hXsq hlogX0 hlogXhi hRX hsx1 hL2x hLf5 rfl
  obtain ⟨-, hYX1, hYX2, hYX3⟩ := mt_all_interval_scale_Y hε0 hP2' hPL2 hL1 hx hXP hsX hLε
  have hX0 : 0 < Real.sqrt (x * P₁) := by linarith
  have hT₁0 : 0 < x / (Real.sqrt (x * P₁) * L) := by positivity
  -- the side conditions of (5.2)
  have hPlo : Real.log (Real.sqrt (x * P₁)) ^ a ≤ P₁ :=
    (Real.rpow_le_rpow hlogX0 hlogXhi (by linarith)).trans_eq hP.symm
  have hPhi : P₁ ≤ 3 * Real.log (Real.sqrt (x * P₁)) ^ (11 / 10 : ℝ) := by
    have h1 : L ^ (11 / 10 : ℝ) = 2 ^ (11 / 10 : ℝ) * (L / 2) ^ (11 / 10 : ℝ) := by
      rw [Real.div_rpow hL0.le (by norm_num)]; field_simp
    have h2 : (L / 2) ^ (11 / 10 : ℝ) ≤ Real.log (Real.sqrt (x * P₁)) ^ (11 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hlogXlo (by norm_num)
    have h3 := two_rpow_eleven_tenths_le_three
    have h4 : 0 ≤ (L / 2) ^ (11 / 10 : ℝ) := by positivity
    calc P₁ ≤ L ^ (11 / 10 : ℝ) := hP11
      _ = 2 ^ (11 / 10 : ℝ) * (L / 2) ^ (11 / 10 : ℝ) := h1
      _ ≤ 3 * (L / 2) ^ (11 / 10 : ℝ) := mul_le_mul_of_nonneg_right h3 h4
      _ ≤ 3 * Real.log (Real.sqrt (x * P₁)) ^ (11 / 10 : ℝ) := by gcongr
  intro T hT
  refine (h52 P₁ _ hPlo hPhi (fun p => mem_primes_Ioc_floor_iff hP0.le) _ hYX1 hYX2 hYX3 T
    (hT₀1.trans hT)).trans ?_
  exact mt_meanSquare_affine_alpha (by linarith) hlogXlo hε0.le hε10 hT₁0 (by linarith) hX0
    hP0.le hPT₁L

/-- **The `E₃` comparison at one `x`.**  Under the growth facts in `L = log x`, the claim (5.2) at
`X = √(xP₁)` and the improved mean value theorem for `P₂`, the short window `h = XL` differs from
`H/H₁` times the long window `h₁ = x e^{-(c/8)√L}` by at most `3h/(108000 log L · L²)`. -/
theorem mt_all_interval_compare_small {x L a c C₂ ε P₁ R₀ : ℝ} {z Q D E : ℕ}
    (hx : 0 < x) (hL : L = Real.log x) (ha1 : 1 ≤ a) (ha11 : a ≤ 11 / 10) (hP : P₁ = L ^ a)
    (hc : 0 < c) (hC₂ : 0 < C₂) (hε0 : 0 < ε) (hε10 : ε ≤ 10) (hL16 : 16 ≤ L)
    (hLf2 : (11 + 96 * Real.log L) * Real.log L * 1296000 * Real.sqrt (4 * C₂) ≤ L ^ (ε / 20))
    (hLf3 : 26000 * Real.exp (-(c / 16) * Real.sqrt L) * (108000 * Real.log L * L ^ 2) ≤ 1)
    (hLf4 : 124800 * 108000 * Real.log L ≤ L ^ 3)
    (hLf5 : Real.exp (-(c / 8) * Real.sqrt L) ≤ 1 / 2) (hLc : c ^ 2 / 4 ≤ L)
    (h64 : 64 * L ^ 2 ≤ x) (hL2x : L ^ 2 ≤ x ^ (1 / 4 : ℝ)) (hLε : 4 * L ^ 2 ≤ x ^ (ε / 200))
    (hL6 : 2 * L ≤ x ^ (1 / 6 : ℝ)) (hL10 : 4 * L ^ 10 ≤ x ^ (1 / 600 : ℝ))
    (hsx1 : 1 ≤ Real.sqrt x) (hRx : max R₀ 1 ^ 3 ≤ x)
    (hz2 : 2 ≤ z) (hz6 : 4 * Real.sqrt (x * P₁) < (z : ℝ) ^ 6)
    (h52 : ∀ (P : ℝ) (B : Finset ℕ), Real.log (Real.sqrt (x * P₁)) ^ a ≤ P →
      P ≤ 3 * Real.log (Real.sqrt (x * P₁)) ^ (11 / 10 : ℝ) →
      (∀ p, p ∈ B ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P) →
      ∀ Y : ℕ, Real.sqrt (x * P₁) ^ (1 - ε / 100) < Y → (Y : ℝ) ≤ Real.sqrt (x * P₁) / 2 →
      Real.sqrt (x * P₁) ≤ 2 * P * Y → ∀ T : ℝ, 1 ≤ T →
        ∫ t in Set.Icc (Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2))) T,
            ‖(∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
              LSeries (fun n => mtHarmanProposition22SourceAF z Q D E Y n)
                (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          2 * Real.log (Real.sqrt (x * P₁)) ^ (-(2 + ε / 10)) +
            2 * Real.log (Real.sqrt (x * P₁)) ^ (-(1 + ε / 10)) * P * T / Real.sqrt (x * P₁))
    (hP2 : ∀ R' : ℝ, R₀ ≤ R' → ∀ T : ℝ, 1 ≤ T → T ≤ R' ^ (201 / 200 : ℝ) →
      ∫ t in Set.Icc (-T) T,
          ‖∑ p ∈ (Finset.Ioc ⌊R'⌋₊ ⌊2 * R'⌋₊).filter Nat.Prime,
            (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ^ 2 ≤
        C₂ * (T / (R' * Real.log R') + 1 / Real.log R' ^ 2)) :
    |mtAllIntervalSum z Q D E P₁ (Real.sqrt (x / P₁) / 2) x (Real.sqrt (x * P₁) * L) -
        (((⌊x + Real.sqrt (x * P₁) * L⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) /
          ((⌊x + x * Real.exp (-(c / 8) * Real.sqrt L)⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) *
          mtAllIntervalSum z Q D E P₁ (Real.sqrt (x / P₁) / 2) x
            (x * Real.exp (-(c / 8) * Real.sqrt L))|
      ≤ 3 * (Real.sqrt (x * P₁) * L / (108000 * Real.log L * L ^ 2)) := by
  have hL0 : 0 < L := by linarith
  have hP0 : 0 < P₁ := by
    have := Real.rpow_pos_of_pos hL0 a; rw [← hP] at this; exact this
  have h16 := mt_all_interval_harman_affine (z := z) (Q := Q) (D := D) (E := E) hx hL ha1 ha11 hP
    hc hε0 hε10 hL16 hLf5 hLc h64 hL2x hLε hL6 hsx1 h52
  have hα : ∀ T, Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2)) ≤ T →
      T ≤ x / (Real.sqrt (x * P₁) * L) * 2 ^ ⌈12 * Real.log L⌉₊ →
      ∫ t in Set.Icc (Real.exp (c / 32 * Real.log (Real.sqrt (x * P₁)) ^ ((1 : ℝ) / 2))) T,
          ‖(∑ p ∈ (Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime,
              (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
            LSeries (fun n => mtHarmanProposition22SourceAF z Q D E
              (⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1) n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
        64 * L ^ (-(2 + ε / 10)) * (1 + T / (x / (Real.sqrt (x * P₁) * L))) := by
    intro T hT _
    refine (h16 T hT).trans ?_
    have hT0 : 0 ≤ T := le_trans (Real.exp_pos _).le hT
    have : 0 ≤ L ^ (-(2 + ε / 10)) * (1 + T / (x / (Real.sqrt (x * P₁) * L))) := by
      have hX0 : 0 ≤ Real.sqrt (x * P₁) := Real.sqrt_nonneg _
      positivity
    nlinarith
  rw [mtAllIntervalSum_eq_on, mtAllIntervalSum_eq_on]
  exact mt_all_interval_compare_small_on hx hL ha1 ha11 hP hc hC₂ hε0 hL16
    (fun p hp => (mem_primes_Ioc_floor_iff hP0.le).1 hp) hLf2 hLf3 hLf4 hLf5 hLc h64 hL2x hLε
    hL6 hL10 hsx1 hRx hz2 hz6 hα hP2

/-- **The final count.**  If the short sum is within `3h/(108000 log L · L²)` of `H/H₁` times the
long sum, and the long sum is at least `h₁/(2250 ℓ L²)` with `ℓ ≤ 2 log L`, then the short sum
is at least `h/(18000 ℓ L²)`. -/
theorem mt_all_interval_final {S S₁ h h₁ H H₁ L ℓ : ℝ}
    (hcmp : |S - H / H₁ * S₁| ≤ 3 * (h / (108000 * Real.log L * L ^ 2)))
    (hlong : h₁ / (2250 * ℓ * L ^ 2) ≤ S₁) (hh2 : 2 ≤ h) (hhh₁ : h ≤ h₁) (hH : h - 1 ≤ H)
    (hH₁ : H₁ ≤ h₁ + 1) (hH₁0 : 0 < H₁) (hℓ : 0 < ℓ) (hℓ2 : ℓ ≤ 2 * Real.log L) (hL : 0 < L) :
    h / (18000 * ℓ * L ^ 2) ≤ S := by
  have hlL : 0 < Real.log L := by linarith
  set m : ℝ := 1 / (2250 * ℓ * L ^ 2) with hm
  have hm0 : 0 ≤ m := by positivity
  have hS : h₁ * m ≤ S₁ := by
    have : h₁ * m = h₁ / (2250 * ℓ * L ^ 2) := by rw [hm]; ring
    linarith
  have hmain := mt_all_interval_main_term hh2 (by linarith) hH hH₁ hH₁0 hm0 hS
  have hlow := (abs_le.1 hcmp).1
  have e1 : h * m / 4 = 2 * (h / (18000 * ℓ * L ^ 2)) := by rw [hm]; field_simp; ring
  have e2 : 3 * (h / (108000 * Real.log L * L ^ 2)) ≤ h / (18000 * ℓ * L ^ 2) := by
    rw [show 3 * (h / (108000 * Real.log L * L ^ 2)) = h / (36000 * Real.log L * L ^ 2) by ring]
    apply div_le_div_of_nonneg_left (by linarith) (by positivity)
    have : 0 < L ^ 2 := by positivity
    nlinarith
  linarith

/-- The window lengths: `H = ⌊x+h⌋ - ⌊x⌋ ≥ h - 1`, `0 < H₁ = ⌊x+h₁⌋ - ⌊x⌋ ≤ h₁ + 1`. -/
theorem mt_all_interval_window_counts {x h h₁ : ℝ} (hx : 0 ≤ x) (hh : 2 ≤ h) (hhh₁ : h ≤ h₁) :
    h - 1 ≤ ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ∧ ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ h₁ + 1 ∧
      0 < ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by
  have hfx : x - 1 < (⌊x⌋₊ : ℝ) := by have := Nat.lt_floor_add_one x; linarith
  have hfx' : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hle : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_mono (by linarith)
  have hle₁ : ⌊x⌋₊ ≤ ⌊x + h₁⌋₊ := Nat.floor_mono (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.cast_sub hle]
    have := Nat.lt_floor_add_one (x + h)
    linarith
  · rw [Nat.cast_sub hle₁]
    have : (⌊x + h₁⌋₊ : ℝ) ≤ x + h₁ := Nat.floor_le (by linarith)
    linarith
  · have h2 : ⌊x⌋₊ + 1 ≤ ⌊x + h₁⌋₊ := Nat.le_floor (by push_cast; linarith)
    have : 0 < ⌊x + h₁⌋₊ - ⌊x⌋₊ := by omega
    exact_mod_cast this

/-- **Matomäki–Teräväinen Theorem 1.2, quantitative form.**  Assume the Deshouillers–Iwaniec bound
`(E1)` and Watt's bound `(E2)`.  For every large `x` and every `a ∈ [a₀, 11/10]` with
`a₀ ≥ 1.0999`, put `L = log x`, `P₁ = L^a`, `X = √(xP₁)` and `h = XL = √x L^{1+a/2}`.  Then
`∑_{P₁ < p₁ ≤ 2P₁} ∑_{R < p₂ ≤ 2R} ∑_{x < p₁p₂n ≤ x+h} ρ⁻(n) ≥ h/(18000 log P₁ · L²)`,
`R = √(x/P₁)/2`, with Harman's minorant `ρ⁻` at the parameters of Proposition 2.2 for `X` and
`ε = 10⁻⁷`.  The short window is compared with the long window `h₁ = x e^{-(c/8)√L}` through
Perron's formula; the comparison integral is controlled by the claim (5.2) and the improved mean
value theorem for `P₂`. -/
theorem eventually_mtAllIntervalSum_short_ge (hDI : MTDeshouillersIwaniecBound)
    (hW : MTWattBound) {a₀ : ℝ} (ha₀ : 10999 / 10000 ≤ a₀) :
    ∀ᶠ x : ℝ in atTop, ∀ a ∈ Set.Icc a₀ (11 / 10),
      Real.sqrt (x * Real.log x ^ a) * Real.log x /
          (18000 * Real.log (Real.log x ^ a) * Real.log x ^ 2) ≤
        mtAllIntervalSum (mtProposition22ZNat (Real.sqrt (x * Real.log x ^ a)))
          (mtProposition22QNat (Real.sqrt (x * Real.log x ^ a)))
          (mtProposition22DNat (Real.sqrt (x * Real.log x ^ a)) (1 / 10 ^ 7))
          (mtProposition22ENat (Real.sqrt (x * Real.log x ^ a)) (1 / 10 ^ 7))
          (Real.log x ^ a) (Real.sqrt (x / Real.log x ^ a) / 2) x
          (Real.sqrt (x * Real.log x ^ a) * Real.log x) := by
  have hε0 : (0 : ℝ) < 1 / 10 ^ 7 := by positivity
  obtain ⟨c, hc, hlong⟩ := exists_mtAllIntervalSum_long_ge
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (eventually_harmanProduct_meanSquare_le hDI hW (A := 5)
    le_rfl ha₀ hε0 (by norm_num) (by positivity : (0 : ℝ) < c / 32))
  obtain ⟨C₂, hC₂, hP2⟩ := eventually_integral_normSq_primeSet_floor_le
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hP2
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 eventually_mtProposition22ZNat_facts
  have hpl : ∀ {C κ : ℝ} (m : ℕ), 0 ≤ C → 0 < κ →
      ∀ᶠ x : ℝ in atTop, C * Real.log x ^ m ≤ x ^ κ := by
    intro C κ m hC hκ
    filter_upwards [eventually_polylog_le_rpow m hC hκ, eventually_ge_atTop (1 : ℝ)] with x h hx
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx
    have hle : Real.log x ≤ 1 + Real.log (24 * x) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl hle m) hC) h
  filter_upwards [hlong,
    Real.tendsto_log_atTop.eventually (mt_all_interval_log_facts (C := 4 * C₂) hc hε0),
    Real.tendsto_log_atTop.eventually_ge_atTop (c ^ 2 / 4),
    hpl (C := 64) 2 (by norm_num) (by norm_num : (0 : ℝ) < 1),
    hpl (C := 1) 2 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 4),
    hpl (C := 4) 2 (by norm_num) (by positivity : (0 : ℝ) < 1 / 10 ^ 7 / 200),
    hpl (C := 2) 1 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 6),
    hpl (C := 4) 10 (by norm_num) (by norm_num : (0 : ℝ) < 1 / 600),
    eventually_ge_atTop (max (max X₀ X₁) 1 ^ 2),
    eventually_ge_atTop (max R₀ 1 ^ 3)] with x hlongx hLf hLc h64 hL2x hLε hL6 hL10 hxX hxR
  intro a ha
  obtain ⟨hL16, hLf2, hLf3, hLf4, hLf5⟩ := hLf
  have hx1 : 1 ≤ x := by
    have hM : 1 ≤ max (max X₀ X₁) 1 ^ 2 := one_le_pow₀ (le_max_right _ _)
    linarith
  have hx0 : 0 < x := by linarith
  have ha1 : 1 ≤ a := by linarith [ha.1]
  have hsxX : max (max X₀ X₁) 1 ≤ Real.sqrt x := (Real.le_sqrt (by positivity) hx0.le).2 hxX
  have hsx1 : 1 ≤ Real.sqrt x := le_trans (le_max_right _ _) hsxX
  obtain ⟨hP2', hPL2, -, hsX, hXle, hXsq, hlogXlo, hlogXhi, hXP⟩ :=
    mt_all_interval_scale_X hx0 rfl hL16 ha1 ha.2 rfl rfl (by simpa using h64)
  have hXX₀ : X₀ ≤ Real.sqrt (x * Real.log x ^ a) := by
    have := le_trans (le_max_left X₀ X₁) (le_max_left _ 1); linarith
  have hXX₁ : X₁ ≤ Real.sqrt (x * Real.log x ^ a) := by
    have := le_trans (le_max_right X₀ X₁) (le_max_left _ 1); linarith
  obtain ⟨hz2, hz6⟩ := hX₁ _ hXX₁
  have hcmp := mt_all_interval_compare_small (a := a) (P₁ := Real.log x ^ a) hx0 rfl ha1 ha.2 rfl
    hc hC₂ hε0 (by norm_num) hL16 hLf2 hLf3 hLf4 hLf5 hLc (by simpa using h64)
    (by simpa using hL2x) hLε (by simpa using hL6) hL10 hsx1 hxR hz2 hz6
    (fun P B => hX₀ _ hXX₀ a P B ha.1 ha.2) hR₀
  -- the windows
  have hL0 : 0 < Real.log x := by linarith
  have hP0 : 0 < Real.log x ^ a := by linarith
  obtain ⟨hRX, -, -, -⟩ := mt_all_interval_scale_R hx0 rfl (by linarith) hP0 hPL2 rfl rfl
    (by simpa using hL6)
  have hlogX0 : 0 ≤ Real.log (Real.sqrt (x * Real.log x ^ a)) := by linarith
  obtain ⟨-, -, -, -, -, hhh₁, -, -, -, -⟩ :=
    mt_all_interval_scale_h hx0 rfl (by linarith) hc hLc hsX hXle hXsq hlogX0 hlogXhi
      hRX hsx1 (by simpa using hL2x) hLf5 rfl
  have hlongxa := hlongx a ⟨ha1, by linarith [ha.2]⟩ _ hε0 le_rfl
  clear hlongx hX₀ hR₀ hX₁ hP2 hlong hpl
  have hh2 : 2 ≤ Real.sqrt (x * Real.log x ^ a) * Real.log x :=
    calc (2 : ℝ) ≤ 1 * 16 := by norm_num
      _ ≤ Real.sqrt (x * Real.log x ^ a) * Real.log x :=
          mul_le_mul (hsx1.trans hsX) hL16 (by norm_num) (by positivity)
  obtain ⟨hH, hH₁, hH₁0⟩ := mt_all_interval_window_counts hx0.le hh2 hhh₁
  have hlL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (by linarith)
  have hℓ : Real.log (Real.log x ^ a) = a * Real.log (Real.log x) := Real.log_rpow hL0 a
  have hℓ0 : 0 < Real.log (Real.log x ^ a) := by
    rw [hℓ]; exact mul_pos (by linarith) (Real.log_pos (by linarith))
  have hℓ2 : Real.log (Real.log x ^ a) ≤ 2 * Real.log (Real.log x) := by
    rw [hℓ]; exact mul_le_mul_of_nonneg_right (by linarith [ha.2]) hlL0
  exact mt_all_interval_final hcmp hlongxa hh2 hhh₁ hH hH₁ hH₁0 hℓ0 hℓ2 hL0
end

end RHTower.Sieve
