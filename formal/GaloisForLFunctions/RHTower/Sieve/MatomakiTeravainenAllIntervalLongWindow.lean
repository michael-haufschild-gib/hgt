import GaloisForLFunctions.RHTower.Sieve.HarmanWindowMainTerm
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProposition22Parameters

/-!
# The long-window main term of the all-interval `E₃` theorem

Matomäki–Teräväinen §7: the `E₃` window sum
`∑_{p₁ ∼ P₁} ∑_{p₂ ∼ R} ∑_{x < p₁p₂n ≤ x+h} ρ⁻(n)`, with `P₁ = (log x)^a`, `R = √(x/P₁)/2` and
Harman's minorant `ρ⁻` at the parameters of Proposition 2.2 for `X = √(xP₁)`.  Over the long
window `h₁ = x·exp(-(c/8)√log x)` it is at least `h₁/(2250 (log P₁)(log x)²)`, uniformly in
`a ∈ [1, 2]` and `0 < ε ≤ 10⁻⁷`: each inner window `(y, y(1+θ)]`, `y = x/(p₁p₂)`, `θ = h₁/x`,
carries `θy/(250 log y)` by the window main term, and the prime sums over `(P₁, 2P₁]` and
`(R, 2R]` carry `1/(3 log P₁)` and `1/(3 log R)`.
-/

namespace RHTower.Sieve

open _root_.Real Filter Topology Finset

noncomputable section

/-- Harman's parameters at scale `X` measured against a window scale `y` with `y < X` and
`81X ≤ y^{1+κ}`. -/
theorem harmanWindowScale_of_le {κ ε X y : ℝ} (hε : 0 < ε) (h2ε : 2 * ε < κ)
    (hε4 : 2 * ε < 1 / 4) (hy : 1 < y) (hyX : y < X) (hX : 81 * X ≤ y ^ (1 + κ)) :
    HarmanWindowScale κ y (mtProposition22ZNat X) (mtProposition22QNat X)
      (mtProposition22DNat X ε) (mtProposition22ENat X ε) := by
  have hy0 : 0 < y := by linarith
  have hX0 : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  -- `X^b ≤ y^{b(1+κ)}/81^b`
  have hpow : ∀ b : ℝ, 0 ≤ b → X ^ b ≤ y ^ (b * (1 + κ)) / 81 ^ b := by
    intro b hb
    have h1 : X ≤ y ^ (1 + κ) / 81 := by linarith
    have := Real.rpow_le_rpow hX0.le h1 hb
    rwa [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hy0.le,
      mul_comm (1 + κ) b] at this
  have hylt : ∀ b : ℝ, 0 < b → y ^ b < X ^ b := fun b hb =>
    Real.rpow_lt_rpow hy0.le hyX hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (hylt _ (by norm_num)) (Nat.le_ceil _)
  · -- `⌈2X^{1/2}⌉ ≤ 3X^{1/2} ≤ y^{1/2+κ}`
    have hX12 : 1 ≤ X ^ (1 / 2 : ℝ) := Real.one_le_rpow hX1.le (by norm_num)
    have hc : (mtProposition22QNat X : ℝ) ≤ 3 * X ^ (1 / 2 : ℝ) := by
      have := (Nat.ceil_lt_add_one (by unfold mtProposition22QReal; positivity :
        (0 : ℝ) ≤ mtProposition22QReal X)).le
      unfold mtProposition22QNat
      unfold mtProposition22QReal at this ⊢
      linarith
    have h1 := hpow (1 / 2) (by norm_num)
    have h9 : (81 : ℝ) ^ (1 / 2 : ℝ) = 9 := by
      rw [show (81 : ℝ) = 9 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h9] at h1
    have h2 : y ^ (1 / 2 * (1 + κ)) ≤ y ^ (1 / 2 + κ) :=
      Real.rpow_le_rpow_of_exponent_le hy.le (by linarith)
    linarith
  · have hlt := hylt (1 / 4 - 2 * ε) (by linarith)
    have hle : y ^ (1 / 4 - κ) ≤ y ^ (1 / 4 - 2 * ε) :=
      Real.rpow_le_rpow_of_exponent_le hy.le (by linarith)
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hlt (Nat.le_ceil _))
  · have hc : (mtProposition22DNat X ε : ℝ) ≤ 2 * X ^ (1 / 4 : ℝ) := by
      have h1 : X ^ (1 / 4 - 2 * ε) ≤ X ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
      have h2 : 1 ≤ X ^ (1 / 4 : ℝ) := Real.one_le_rpow hX1.le (by norm_num)
      have := (Nat.ceil_lt_add_one (by unfold mtProposition22DReal; positivity :
        (0 : ℝ) ≤ mtProposition22DReal X ε)).le
      unfold mtProposition22DNat
      unfold mtProposition22DReal at this ⊢
      linarith
    have h1 := hpow (1 / 4) (by norm_num)
    have h9 : (81 : ℝ) ^ (1 / 4 : ℝ) = 3 := by
      rw [show (81 : ℝ) = 3 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [h9] at h1
    have h2 : y ^ (1 / 4 * (1 + κ)) ≤ y ^ (1 / 4 + κ) :=
      Real.rpow_le_rpow_of_exponent_le hy.le (by linarith)
    have h0 : 0 ≤ y ^ (1 / 4 * (1 + κ)) := by positivity
    linarith
  · have hlt := hylt (1 - 2 * ε) (by linarith)
    have hle : y ^ (1 - κ) ≤ y ^ (1 - 2 * ε) :=
      Real.rpow_le_rpow_of_exponent_le hy.le (by linarith)
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hlt (Nat.le_ceil _))
  · have hc : (mtProposition22ENat X ε : ℝ) ≤ 2 * X := by
      have h1 : X ^ (1 - 2 * ε) ≤ X := by
        calc X ^ (1 - 2 * ε) ≤ X ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
          _ = X := Real.rpow_one X
      have := (Nat.ceil_lt_add_one (by unfold mtProposition22EReal; positivity :
        (0 : ℝ) ≤ mtProposition22EReal X ε)).le
      unfold mtProposition22ENat
      unfold mtProposition22EReal at this ⊢
      linarith
    have h2 : y ^ (1 : ℝ) ≤ y ^ (1 + κ) := Real.rpow_le_rpow_of_exponent_le hy.le (by linarith)
    rw [Real.rpow_one] at h2
    linarith

/-- The `E₃` window sum of Matomäki–Teräväinen §7:
`∑_{P₁ < p₁ ≤ 2P₁} ∑_{R < p₂ ≤ 2R} ∑_{x < p₁p₂n ≤ x+h} ρ⁻(n)`. -/
def mtAllIntervalSum (z Q D E : ℕ) (P₁ R x h : ℝ) : ℝ :=
  ∑ p₁ ∈ (Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime,
    ∑ p₂ ∈ (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime,
      ∑ n ∈ Finset.Ioc ⌊x / (p₁ * p₂)⌋₊ ⌊(x + h) / (p₁ * p₂)⌋₊, (rhoMinus z Q D E n : ℝ)

/-- One inner window of the `E₃` sum, from the window main term. -/
theorem mt_inner_window_ge {c Y₀ x h : ℝ} {z Q D E : ℕ} {d : ℕ}
    (hwin : ∀ y ≥ Y₀, ∀ θ : ℝ, exp (-(c / 4) * sqrt (log y)) ≤ θ → θ ≤ 1 →
      ∀ z Q D E : ℕ, HarmanWindowScale (1 / 1000000) y z Q D E → z ≤ Q → D ≤ Q →
      (Q : ℝ) ≤ y → y * 2 < (Q : ℝ) * Q →
      1 / 250 * (θ * y / log y) ≤
        ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊y * (1 + θ)⌋₊, (rhoMinus z Q D E n : ℝ))
    (hx : 1 < x) (hh : 0 < h) (hhx : h ≤ x) (hd : 0 < d) (hdx : (d : ℝ) * 3 ≤ x)
    (hY : Y₀ ≤ x / d) (hθ : exp (-(c / 4) * sqrt (log (x / d))) ≤ h / x)
    (hP : HarmanWindowScale (1 / 1000000) (x / d) z Q D E) (hzQ : z ≤ Q) (hDQ : D ≤ Q)
    (hQy : (Q : ℝ) ≤ x / d) (hQ2 : x / d * 2 < (Q : ℝ) * Q) :
    1 / 250 * (h / d) / log x ≤
      ∑ n ∈ Finset.Ioc ⌊x / d⌋₊ ⌊(x + h) / d⌋₊, (rhoMinus z Q D E n : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hθ1 : h / x ≤ 1 := (div_le_one hx0).2 hhx
  have hw := hwin (x / d) hY (h / x) hθ hθ1 z Q D E hP hzQ hDQ hQy hQ2
  have e1 : x / d * (1 + h / x) = (x + h) / d := by field_simp
  have e2 : h / x * (x / d) = h / d := by field_simp
  rw [e1, e2] at hw
  refine le_trans ?_ hw
  have hy1 : 1 < x / d := by rw [lt_div_iff₀ hd0]; linarith
  have hly : 0 < log (x / d) := Real.log_pos hy1
  have hlx : log (x / d) ≤ log x :=
    Real.log_le_log (by positivity) (div_le_self hx0.le (by exact_mod_cast hd))
  have : h / d / log x ≤ h / d / log (x / d) :=
    div_le_div_of_nonneg_left (by positivity) hly hlx
  calc 1 / 250 * (h / d) / log x = 1 / 250 * (h / d / log x) := by ring
    _ ≤ 1 / 250 * (h / d / log (x / d)) := by linarith

/-- `K (log x)² ≤ x^s` eventually. -/
theorem eventually_mul_log_sq_le_rpow {K s : ℝ} (hK : 0 < K) (hs : 0 < s) :
    ∀ᶠ x : ℝ in atTop, K * (log x) ^ 2 ≤ x ^ s := by
  filter_upwards [(isLittleO_log_rpow_rpow_atTop 2 hs).bound (inv_pos.2 hK),
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hl : 0 ≤ log x := Real.log_nonneg hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _), Real.norm_of_nonneg (by positivity),
    Real.rpow_two] at hx
  rw [inv_mul_eq_div, le_div_iff₀ hK] at hx
  linarith

/-- The geometry of the two prime scales: `P₁ · 2R = X` and `X · 2R = x`. -/
theorem mt_scale_geometry {x P₁ : ℝ} (hx : 0 < x) (hP : 0 < P₁) :
    P₁ * (2 * (sqrt (x / P₁) / 2)) = sqrt (x * P₁) ∧
      sqrt (x * P₁) * (2 * (sqrt (x / P₁) / 2)) = x := by
  have e : 2 * (sqrt (x / P₁) / 2) = sqrt (x / P₁) := by ring
  rw [e]
  constructor
  · rw [show P₁ = sqrt (P₁ ^ 2) from (Real.sqrt_sq hP.le).symm]
    rw [Real.sqrt_sq hP.le, ← Real.sqrt_sq hP.le, ← Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hP.le]
    congr 1; field_simp
  · rw [← Real.sqrt_mul (by positivity)]
    rw [show x * P₁ * (x / P₁) = x ^ 2 by field_simp]
    exact Real.sqrt_sq hx.le

/-- The window conditions for one pair `(p₁, p₂)`, `d = p₁p₂ ∈ (X/2, 2X]`. -/
theorem mt_pair_window_conditions {x P₁ R X : ℝ} {ε : ℝ} {d : ℕ} (hε : 0 < ε)
    (hε7 : ε ≤ 1 / 10 ^ 7) (hP2 : 2 ≤ P₁) (hR : 18 * P₁ ≤ R) (hRκ : 162 * P₁ ≤ R ^ (1 / 1000000 : ℝ))
    (hPR : P₁ * (2 * R) = X) (hXR : X * (2 * R) = x)
    (hd1 : X / 2 < d) (hd2 : (d : ℝ) ≤ 2 * X) :
    HarmanWindowScale (1 / 1000000) (x / d) (mtProposition22ZNat X) (mtProposition22QNat X)
        (mtProposition22DNat X ε) (mtProposition22ENat X ε) ∧
      mtProposition22ZNat X ≤ mtProposition22QNat X ∧
      mtProposition22DNat X ε ≤ mtProposition22QNat X ∧
      (mtProposition22QNat X : ℝ) ≤ x / d ∧
      x / d * 2 < (mtProposition22QNat X : ℝ) * mtProposition22QNat X ∧
      (d : ℝ) * 3 ≤ x ∧ R ≤ x / d := by
  have hP0 : 0 < P₁ := by linarith
  have hR0 : 0 < R := by nlinarith
  have hX0 : 0 < X := by rw [← hPR]; positivity
  have hd0 : (0 : ℝ) < d := by linarith
  have hx0 : 0 < x := by rw [← hXR]; positivity
  -- `y = x/d ∈ [R, 4R)`
  have hylo : R ≤ x / d := by
    rw [le_div_iff₀ hd0, ← hXR]; nlinarith
  have hyhi : x / d < 4 * R := by
    rw [div_lt_iff₀ hd0, ← hXR]; nlinarith
  have hR1 : 1 < R := by nlinarith
  have hy1 : 1 < x / d := lt_of_lt_of_le hR1 hylo
  have hyX : x / d < X := by
    have : 4 * R ≤ X := by rw [← hPR]; nlinarith
    linarith
  have hX1 : 1 ≤ X := by linarith
  have h81 : 81 * X ≤ (x / d) ^ (1 + 1 / 1000000 : ℝ) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
    have hyκ : R ^ (1 / 1000000 : ℝ) ≤ (x / d) ^ (1 / 1000000 : ℝ) :=
      Real.rpow_le_rpow hR0.le hylo (by norm_num)
    have : 81 * X = 162 * P₁ * R := by rw [← hPR]; ring
    rw [this]
    have h0 : 0 ≤ 162 * P₁ := by positivity
    calc 162 * P₁ * R ≤ R ^ (1 / 1000000 : ℝ) * R := mul_le_mul_of_nonneg_right hRκ hR0.le
      _ ≤ (x / d) ^ (1 / 1000000 : ℝ) * (x / d) :=
          mul_le_mul hyκ hylo hR0.le (by positivity)
      _ = x / d * (x / d) ^ (1 / 1000000 : ℝ) := by ring
  have hscale := harmanWindowScale_of_le (κ := 1 / 1000000) (ε := ε) hε
    (by linarith [show (1 : ℝ) / 10 ^ 7 = 1 / 10000000 by norm_num]) (by linarith) hy1 hyX h81
  -- the ceilings
  have hX12 : 1 ≤ X ^ (1 / 2 : ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hQlo : 2 * X ^ (1 / 2 : ℝ) ≤ (mtProposition22QNat X : ℝ) := Nat.le_ceil _
  have hQhi : (mtProposition22QNat X : ℝ) ≤ 3 * X ^ (1 / 2 : ℝ) := by
    have := (Nat.ceil_lt_add_one (by unfold mtProposition22QReal; positivity :
      (0 : ℝ) ≤ mtProposition22QReal X)).le
    unfold mtProposition22QNat; unfold mtProposition22QReal at this ⊢; linarith
  refine ⟨hscale, ?_, ?_, ?_, ?_, ?_, hylo⟩
  · unfold mtProposition22ZNat mtProposition22QNat mtProposition22ZReal mtProposition22QReal
    refine Nat.ceil_mono ?_
    have : X ^ (2 / 11 : ℝ) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    linarith
  · unfold mtProposition22DNat mtProposition22QNat mtProposition22DReal mtProposition22QReal
    refine Nat.ceil_mono ?_
    have : X ^ (1 / 4 - 2 * ε) ≤ X ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    linarith
  · -- `3 X^{1/2} ≤ R`
    have hsq : X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) = X := by
      rw [← Real.rpow_add hX0]; norm_num
    have : 3 * X ^ (1 / 2 : ℝ) ≤ R := by
      nlinarith [hPR, sq_nonneg (3 * X ^ (1 / 2 : ℝ) - R)]
    linarith
  · have hsq : X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) = X := by
      rw [← Real.rpow_add hX0]; norm_num
    have hQ2 : 4 * X ≤ (mtProposition22QNat X : ℝ) * mtProposition22QNat X := by nlinarith
    linarith
  · have h1 : (d : ℝ) * 3 ≤ 6 * X := by linarith
    have h2 : 6 * X ≤ x := by rw [← hXR]; nlinarith
    linarith

/-- The reciprocal prime sum over `(Z, 2Z]` from a prime count `≥ (9/10) Z/log Z`. -/
theorem one_div_three_log_le_sum_inv_primes {Z : ℝ} (hZ : 0 < Z) (hlog : 0 < log Z)
    (hcard : 9 / 10 * (Z / log Z) ≤ ((primesIn Z (Z * (1 + 1))).card : ℝ)) :
    1 / (3 * log Z) ≤ ∑ p ∈ (Finset.Ioc ⌊Z⌋₊ ⌊2 * Z⌋₊).filter Nat.Prime, 1 / (p : ℝ) := by
  have hS : primesIn Z (Z * (1 + 1)) = (Finset.Ioc ⌊Z⌋₊ ⌊2 * Z⌋₊).filter Nat.Prime := by
    unfold primesIn; rw [show Z * (1 + 1) = 2 * Z by ring]
  rw [hS] at hcard
  have hle : ∀ p ∈ (Finset.Ioc ⌊Z⌋₊ ⌊2 * Z⌋₊).filter Nat.Prime, 1 / (2 * Z) ≤ 1 / (p : ℝ) := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp'.2.pos
    have : (p : ℝ) ≤ 2 * Z := by
      have h2 : p ≤ ⌊2 * Z⌋₊ := (Finset.mem_Ioc.1 hp'.1).2
      exact (Nat.cast_le.2 h2).trans (Nat.floor_le (by positivity))
    exact one_div_le_one_div_of_le hp0 this
  have hsum := Finset.card_nsmul_le_sum _ _ _ hle
  rw [nsmul_eq_mul] at hsum
  calc 1 / (3 * log Z) ≤ 9 / 10 * (Z / log Z) * (1 / (2 * Z)) := by
        rw [div_le_iff₀ (by positivity)]
        field_simp
        norm_num
    _ ≤ (((Finset.Ioc ⌊Z⌋₊ ⌊2 * Z⌋₊).filter Nat.Prime).card : ℝ) * (1 / (2 * Z)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ _ := hsum

/-- **The long-window main term of the all-interval `E₃` theorem.**  With `P₁ = (log x)^a`,
`R = √(x/P₁)/2`, `X = √(xP₁)` and `h₁ = x exp(-(c/8)√log x)`, the `E₃` window sum is at least
`h₁/(2250 (log P₁)(log x)²)`, uniformly in `a ∈ [1, 2]` and `0 < ε ≤ 10⁻⁷`. -/
theorem exists_mtAllIntervalSum_long_ge :
    ∃ c > 0, ∀ᶠ x : ℝ in atTop, ∀ a ∈ Set.Icc (1 : ℝ) 2, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 ^ 7 →
      x * exp (-(c / 8) * sqrt (log x)) / (2250 * log ((log x) ^ a) * (log x) ^ 2) ≤
        mtAllIntervalSum (mtProposition22ZNat (sqrt (x * (log x) ^ a)))
          (mtProposition22QNat (sqrt (x * (log x) ^ a)))
          (mtProposition22DNat (sqrt (x * (log x) ^ a)) ε)
          (mtProposition22ENat (sqrt (x * (log x) ^ a)) ε)
          ((log x) ^ a) (sqrt (x / (log x) ^ a) / 2) x (x * exp (-(c / 8) * sqrt (log x))) := by
  obtain ⟨c, hc, hW⟩ := exists_window_rhoMinus_ge
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 hW
  obtain ⟨c', hc', hPNT⟩ := exists_card_primesIn_window
  obtain ⟨Z₀, hZ₀⟩ := Filter.eventually_atTop.1 (hPNT (1 / 10) (by norm_num))
  refine ⟨c, hc, ?_⟩
  filter_upwards [tendsto_log_atTop.eventually_ge_atTop (max 2 Z₀),
    eventually_mul_log_sq_le_rpow (K := 18) (s := 1 / 4) (by norm_num) (by norm_num),
    eventually_mul_log_sq_le_rpow (K := 162) (s := 1 / 4000000) (by norm_num) (by norm_num),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop (max Y₀ Z₀),
    eventually_gt_atTop (1 : ℝ)] with x hL h18 h162 hY hx1
  intro a ha ε hε hε7
  have hx0 : 0 < x := by linarith
  set L := log x with hLdef
  have hL2 : 2 ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : 0 < L := by linarith
  set P₁ := L ^ a with hP₁
  set R := sqrt (x / P₁) / 2 with hR
  set X := sqrt (x * P₁) with hX
  set h₁ := x * exp (-(c / 8) * sqrt L) with hh₁
  -- the scales
  have hPL : L ≤ P₁ := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ L) ha.1
    rwa [Real.rpow_one] at this
  have hPL2 : P₁ ≤ L ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ L) ha.2
    rwa [Real.rpow_two] at this
  have hP2 : 2 ≤ P₁ := hL2.trans hPL
  have hP0 : 0 < P₁ := by linarith
  obtain ⟨hPR, hXR⟩ := mt_scale_geometry hx0 hP0
  rw [← hR, ← hX] at hPR hXR
  have hq : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = sqrt x := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have h4pos : 0 < x ^ (1 / 4 : ℝ) := by positivity
  have h2L : 2 * L ≤ x ^ (1 / 4 : ℝ) := by
    have : 2 * L ≤ 18 * L ^ 2 := by nlinarith
    linarith
  -- `R ≥ x^{1/4}`
  have hRlo : x ^ (1 / 4 : ℝ) ≤ R := by
    have h1 : sqrt x / L ≤ sqrt (x / P₁) := by
      rw [Real.sqrt_div' x hP0.le]
      apply div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.sqrt_pos.2 hP0)
      calc sqrt P₁ ≤ sqrt (L ^ 2) := Real.sqrt_le_sqrt hPL2
        _ = L := Real.sqrt_sq hL0.le
    have h2 : 2 * x ^ (1 / 4 : ℝ) ≤ sqrt x / L := by
      rw [le_div_iff₀ hL0, ← hq]
      have := mul_le_mul_of_nonneg_left h2L h4pos.le
      linarith
    rw [hR]; linarith
  have hR18 : 18 * P₁ ≤ R := by linarith
  have hRκ : 162 * P₁ ≤ R ^ (1 / 1000000 : ℝ) := by
    have h1 : x ^ (1 / 4000000 : ℝ) ≤ R ^ (1 / 1000000 : ℝ) := by
      have := Real.rpow_le_rpow h4pos.le hRlo (by norm_num : (0 : ℝ) ≤ 1 / 1000000)
      rwa [← Real.rpow_mul hx0.le, show (1 / 4 : ℝ) * (1 / 1000000) = 1 / 4000000 by norm_num]
        at this
    linarith
  have hθ1 : exp (-(c / 8) * sqrt L) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c / 8 * sqrt L := by positivity
    linarith
  have hh0 : 0 < h₁ := by positivity
  have hhx : h₁ ≤ x := mul_le_of_le_one_right hx0.le hθ1
  have hR0 : 0 < R := by linarith
  have hX1 : 1 ≤ X := by
    have h1 : 2 * 1 ≤ P₁ * (2 * R) := mul_le_mul hP2 (by linarith) (by norm_num) hP0.le
    linarith
  -- one pair
  have hpair : ∀ p₁ ∈ (Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime,
      ∀ p₂ ∈ (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime,
      1 / 250 * (h₁ / ((p₁ * p₂ : ℕ) : ℝ)) / L ≤
        ∑ n ∈ Finset.Ioc ⌊x / (p₁ * p₂)⌋₊ ⌊(x + h₁) / (p₁ * p₂)⌋₊,
          (rhoMinus (mtProposition22ZNat X) (mtProposition22QNat X)
            (mtProposition22DNat X ε) (mtProposition22ENat X ε) n : ℝ) := by
    intro p₁ hp₁ p₂ hp₂
    have hm1 := Finset.mem_Ioc.1 (Finset.mem_filter.1 hp₁).1
    have hm2 := Finset.mem_Ioc.1 (Finset.mem_filter.1 hp₂).1
    have hp1lo : P₁ < p₁ := (Nat.floor_lt hP0.le).1 hm1.1
    have hp1hi : (p₁ : ℝ) ≤ 2 * P₁ :=
      (Nat.cast_le.2 hm1.2).trans (Nat.floor_le (by positivity))
    have hp2lo : R < p₂ := (Nat.floor_lt hR0.le).1 hm2.1
    have hp2hi : (p₂ : ℝ) ≤ 2 * R :=
      (Nat.cast_le.2 hm2.2).trans (Nat.floor_le (by positivity))
    have hd : 0 < p₁ * p₂ :=
      Nat.mul_pos (Finset.mem_filter.1 hp₁).2.pos (Finset.mem_filter.1 hp₂).2.pos
    have hdcast : ((p₁ * p₂ : ℕ) : ℝ) = (p₁ : ℝ) * p₂ := Nat.cast_mul _ _
    have hd1 : X / 2 < ((p₁ * p₂ : ℕ) : ℝ) := by
      rw [hdcast]
      have := mul_lt_mul'' hp1lo hp2lo hP0.le hR0.le
      linarith
    have hd2 : ((p₁ * p₂ : ℕ) : ℝ) ≤ 2 * X := by
      rw [hdcast]
      have := mul_le_mul hp1hi hp2hi (Nat.cast_nonneg _) (by linarith)
      linarith
    obtain ⟨hscale, hzQ, hDQ, hQy, hQ2, hd3, hyR⟩ :=
      mt_pair_window_conditions hε hε7 hP2 hR18 hRκ hPR hXR hd1 hd2
    have hyY : Y₀ ≤ x / ((p₁ * p₂ : ℕ) : ℝ) :=
      (le_max_left _ _).trans (hY.trans (hRlo.trans hyR))
    have hθ : exp (-(c / 4) * sqrt (log (x / ((p₁ * p₂ : ℕ) : ℝ)))) ≤ h₁ / x := by
      rw [hh₁, mul_div_cancel_left₀ _ hx0.ne']
      apply Real.exp_le_exp.2
      have hy4 : x ^ (1 / 4 : ℝ) ≤ x / ((p₁ * p₂ : ℕ) : ℝ) := hRlo.trans hyR
      have hlog : L / 4 ≤ log (x / ((p₁ * p₂ : ℕ) : ℝ)) := by
        have := Real.log_le_log h4pos hy4
        rw [Real.log_rpow hx0] at this; linarith
      have hs : sqrt L / 2 ≤ sqrt (log (x / ((p₁ * p₂ : ℕ) : ℝ))) := by
        have := Real.sqrt_le_sqrt hlog
        rwa [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4),
          show sqrt (4 : ℝ) = 2 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
      have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ c / 4)
      linarith
    have := mt_inner_window_ge (hY₀) hx1 hh0 hhx hd hd3 hyY hθ hscale hzQ hDQ hQy hQ2
    rw [hdcast] at this ⊢
    exact this
  -- the reciprocal prime sums
  have hPNT₁ := (hZ₀ P₁ ((le_max_right _ _).trans (hL.trans hPL)) 1
    (by rw [Real.exp_le_one_iff]; have : 0 ≤ c' * sqrt (log P₁) := by positivity
        linarith) le_rfl).1
  have hlogP : 0 < log P₁ := Real.log_pos (by linarith)
  rw [one_mul] at hPNT₁
  have hS₁ := one_div_three_log_le_sum_inv_primes hP0 hlogP (by linarith)
  have hRZ : Z₀ ≤ R := (le_max_right _ _).trans (hY.trans hRlo)
  have hPNT₂ := (hZ₀ R hRZ 1
    (by rw [Real.exp_le_one_iff]; have : 0 ≤ c' * sqrt (log R) := by positivity
        linarith) le_rfl).1
  have hlogR : 0 < log R := Real.log_pos (by linarith)
  rw [one_mul] at hPNT₂
  have hS₂ := one_div_three_log_le_sum_inv_primes hR0 hlogR (by linarith)
  have hRx : log R ≤ L := by
    have h1 : 2 * R * 1 ≤ 2 * R * X := mul_le_mul_of_nonneg_left hX1 (by linarith)
    have h2 : R ≤ x := by linarith
    exact Real.log_le_log hR0 h2
  -- assemble
  unfold mtAllIntervalSum
  set S₁ := (Finset.Ioc ⌊P₁⌋₊ ⌊2 * P₁⌋₊).filter Nat.Prime with hS₁def
  set S₂ := (Finset.Ioc ⌊R⌋₊ ⌊2 * R⌋₊).filter Nat.Prime with hS₂def
  have hsum : 1 / 250 * (h₁ / L) * ((∑ p₁ ∈ S₁, 1 / (p₁ : ℝ)) * ∑ p₂ ∈ S₂, 1 / (p₂ : ℝ)) ≤
      ∑ p₁ ∈ S₁, ∑ p₂ ∈ S₂, ∑ n ∈ Finset.Ioc ⌊x / (p₁ * p₂)⌋₊ ⌊(x + h₁) / (p₁ * p₂)⌋₊,
        (rhoMinus (mtProposition22ZNat X) (mtProposition22QNat X)
          (mtProposition22DNat X ε) (mtProposition22ENat X ε) n : ℝ) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum (fun p₁ hp₁ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p₂ hp₂ => ?_)
    refine le_trans (le_of_eq ?_) (hpair p₁ hp₁ p₂ hp₂)
    push_cast
    field_simp
  refine le_trans ?_ hsum
  have hA : 0 ≤ ∑ p₂ ∈ S₂, 1 / (p₂ : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
  have hprod : 1 / (3 * log P₁) * (1 / (3 * L)) ≤
      (∑ p₁ ∈ S₁, 1 / (p₁ : ℝ)) * ∑ p₂ ∈ S₂, 1 / (p₂ : ℝ) := by
    have h3 : 1 / (3 * L) ≤ 1 / (3 * log R) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact mul_le_mul hS₁ (h3.trans hS₂) (by positivity) ((by positivity : (0 : ℝ) ≤ _).trans hS₁)
  calc h₁ / (2250 * log P₁ * L ^ 2)
      = 1 / 250 * (h₁ / L) * (1 / (3 * log P₁) * (1 / (3 * L))) := by
        field_simp; ring
    _ ≤ 1 / 250 * (h₁ / L) * ((∑ p₁ ∈ S₁, 1 / (p₁ : ℝ)) * ∑ p₂ ∈ S₂, 1 / (p₂ : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

end

end RHTower.Sieve
