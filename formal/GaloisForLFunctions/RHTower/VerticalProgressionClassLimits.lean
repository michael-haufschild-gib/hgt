import GaloisForLFunctions.RHTower.VerticalProgressionResonantSmall

/-!
# The negligible ratio classes

With `0 < θ < ½`, `η = (½ − θ)/4`, `N = ⌊T^θ⌋` and the phase width `δ = T^{−1+η}`:

* **off-resonant ratios** `‖u(c)‖ ≥ δ` (`tendsto_offResonant_div`): `r`-fold summation by parts
  gives `≪ N T² /(T δ)^r = N T^{2−rη}`;
* **near-diagonal ratios** `0 < |u(c)| < δ` (`tendsto_nearDiagonal_div`): `mn ≥ T^{1+6η}/C`, and
  the decay of `V` gives `≪ T^{θ+1+6η−6ηA}`;
* **huge ratios** `ab > Z = T^{1+η}N²` (`tendsto_hugeRatio_div`): `mn ≥ T^{1+η}`, giving
  `≪ T^{θ+1+η−ηA}`.

Each contribution is `o(T)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower.VerticalAP

noncomputable section

open ZetaNotch (pairAmp pairFreq pairProd)

theorem eventually_molLen_ge_one {θ : ℝ} (hθ : 0 < θ) : ∀ᶠ T : ℝ in atTop, 1 ≤ molLen θ T :=
  (tendsto_molLen hθ).eventually (eventually_ge_atTop 1)

theorem molLen_cast_le_rpow {θ T : ℝ} (hT : 0 ≤ T) : (molLen θ T : ℝ) ≤ T ^ θ := molLen_le hT

/-- The progression positions for `2|β| ≤ αT`. -/
theorem pos_of_progression {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {α β T : ℝ}
    (hα : 0 < α) (hT : 0 < T) (hβ : 2 * |β| ≤ α * T) :
    ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β := by
  intro x hx
  obtain ⟨h1, _⟩ := hsupp hx
  rw [le_div_iff₀ hT] at h1
  have := neg_abs_le β
  nlinarith

theorem eventually_progression {α β : ℝ} (hα : 0 < α) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧ 2 * |β| ≤ α * T := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (2 * |β| / α)] with T h1 h2
  exact ⟨h1, by rw [div_le_iff₀ hα] at h2; linarith⟩

/-! ## Off-resonant ratios -/

theorem tendsto_offResonant_div {ψ : ℝ → ℝ} (hψ : ∀ r : ℕ, ContDiff ℝ r ψ)
    (hsupp : Function.support ψ ⊆ Icc 1 2) {α β θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ)
    (hθ : θ < 1 / 2) :
    Tendsto (fun T => ‖∑' c, (offResonant α (T ^ (-1 + resExp θ))).indicator
      (fiberTerm ψ α β (molLen θ T) T) c‖ / T) atTop (𝓝 0) := by
  set η := resExp θ with hηdef
  have hη : 0 < η := by rw [hηdef]; unfold resExp; linarith
  set r : ℕ := ⌈(2 + θ) / η⌉₊ with hr
  have hrη : 2 + θ ≤ r * η := by
    have := Nat.le_ceil ((2 + θ) / η)
    rw [div_le_iff₀ hη] at this
    exact this
  obtain ⟨C, hC0, hC⟩ := sum_offResonant_le hψ hsupp (β := β) hα r
  have hlim : Tendsto (fun T : ℝ => C * T ^ (θ + 1 - r * η)) atTop (𝓝 0) := by
    have := (tendsto_rpow_of_neg (show θ + 1 - r * η < 0 by linarith)).const_mul C
    rwa [mul_zero] at this
  refine squeeze_zero' (by filter_upwards [eventually_ge_atTop 0] with T hT; positivity) ?_ hlim
  filter_upwards [eventually_progression (β := β) hα] with T hTβ
  obtain ⟨hT, hβ⟩ := hTβ
  have hT0 : 0 < T := by linarith
  have hδ : 0 < T ^ (-1 + η) := Real.rpow_pos_of_pos hT0 _
  have h1 := norm_tsum_indicator_fiberTerm_le hsupp (molLen θ T) hT0
    (pos_of_progression hsupp hα hT0 hβ) (offResonant α (T ^ (-1 + η)))
  have h2 := hC (molLen θ T) hT hβ hδ
  have hN := molLen_cast_le_rpow (θ := θ) hT0.le
  have hTr : T ^ r * (T ^ (-1 + η)) ^ r = T ^ (r * η) := by
    rw [← mul_pow, ← Real.rpow_one_add' hT0.le (by linarith), show 1 + (-1 + η) = η by ring,
      ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
    ring_nf
  rw [div_le_iff₀ hT0]
  calc ‖∑' c, (offResonant α (T ^ (-1 + η))).indicator (fiberTerm ψ α β (molLen θ T) T) c‖
      ≤ C * molLen θ T * T ^ 2 / (T ^ r * (T ^ (-1 + η)) ^ r) := h1.trans h2
    _ = C * molLen θ T * T ^ 2 / T ^ (r * η) := by rw [hTr]
    _ ≤ C * T ^ θ * T ^ 2 / T ^ (r * η) := by gcongr
    _ = C * T ^ (θ + 1 - r * η) * T := by
        rw [Real.rpow_sub hT0, Real.rpow_add hT0, Real.rpow_one]
        field_simp

/-! ## Near-diagonal ratios -/

theorem tendsto_nearDiagonal_div {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {Ψ₀ : ℝ}
    (hΨ : ∀ y, |ψ y| ≤ Ψ₀) {α β θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    Tendsto (fun T => ‖∑' c, (nearDiagonal α (T ^ (-1 + resExp θ))).indicator
      (fiberTerm ψ α β (molLen θ T) T) c‖ / T) atTop (𝓝 0) := by
  set η := resExp θ with hηdef
  have hη : 0 < η := by rw [hηdef]; unfold resExp; linarith
  have h2θ : 2 * θ = 1 - 8 * η := by rw [hηdef]; unfold resExp; ring
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  set A : ℝ := (θ + 2 + 6 * η) / (6 * η) + 1 with hA
  have hA1 : 1 < A := by rw [hA]; have : 0 < (θ + 2 + 6 * η) / (6 * η) := by positivity
                         linarith
  have hAη : θ + 2 + 6 * η < 6 * η * A := by
    rw [hA, mul_add, mul_div_cancel₀ _ (by positivity : (6 * η : ℝ) ≠ 0)]; linarith
  obtain ⟨K, hK, hKb⟩ := sum_nearDiagonal_le hsupp hΨ (β := β) hα hA1
  set D : ℝ := 4 * (2 * Ψ₀ * (K * (3 * α / (2 * Real.pi)) ^ A)) *
    (Real.exp 1 * (2 * Real.pi / α) ^ 2) ^ (A - 1) * pairSum
  have hD : 0 ≤ D := by have := pairSum_nonneg; positivity
  set κ : ℝ := θ + A - (1 + 6 * η) * (A - 1)
  have hκ : κ < 0 := by simp only [κ]; nlinarith
  have hlim : Tendsto (fun T : ℝ => D * T ^ κ) atTop (𝓝 0) := by
    have := (tendsto_rpow_of_neg hκ).const_mul D
    rwa [mul_zero] at this
  have hδ1 : ∀ᶠ T : ℝ in atTop, 2 * Real.pi * T ^ (-1 + η) / α ≤ 1 := by
    have h := ((tendsto_rpow_of_neg (show -1 + η < 0 by linarith)).const_mul (2 * Real.pi)).div_const α
    simp only [mul_zero, zero_div] at h
    exact h.eventually (ge_mem_nhds one_pos)
  refine squeeze_zero' (by filter_upwards [eventually_ge_atTop 0] with T hT; positivity) ?_ hlim
  filter_upwards [eventually_progression (β := β) hα, hδ1, eventually_molLen_ge_one hθ0]
    with T hTβ hδT hN1
  obtain ⟨hT, hβ⟩ := hTβ
  have hT0 : 0 < T := by linarith
  have hδ : 0 < T ^ (-1 + η) := Real.rpow_pos_of_pos hT0 _
  have h1 := norm_tsum_indicator_fiberTerm_le hsupp (molLen θ T) hT0
    (pos_of_progression hsupp hα hT0 hβ) (nearDiagonal α (T ^ (-1 + η)))
  have h2 := hKb (molLen θ T) hT0 hβ hδ hδT
  have hN := molLen_cast_le_rpow (θ := θ) hT0.le
  have hN0 : (0 : ℝ) ≤ molLen θ T := Nat.cast_nonneg _
  rw [div_le_iff₀ hT0]
  refine (h1.trans h2).trans ?_
  -- `(e δ'² N²)^{A−1} ≤ (e(2π/α)²)^{A−1} T^{−(1+6η)(A−1)}`
  have hbase : Real.exp 1 * (2 * Real.pi * T ^ (-1 + η) / α) ^ 2 * (molLen θ T : ℝ) ^ 2 ≤
      Real.exp 1 * (2 * Real.pi / α) ^ 2 * T ^ (-(1 + 6 * η)) := by
    have e1 : (2 * Real.pi * T ^ (-1 + η) / α) ^ 2 = (2 * Real.pi / α) ^ 2 * T ^ (-2 + 2 * η) := by
      rw [show (-2 + 2 * η : ℝ) = (-1 + η) * 2 by ring, Real.rpow_mul hT0.le, Real.rpow_two]
      ring
    have e2 : (molLen θ T : ℝ) ^ 2 ≤ T ^ (2 * θ) := by
      rw [show (2 : ℝ) * θ = θ * 2 by ring, Real.rpow_mul hT0.le, Real.rpow_two]
      exact pow_le_pow_left₀ hN0 hN 2
    rw [e1]
    calc Real.exp 1 * ((2 * Real.pi / α) ^ 2 * T ^ (-2 + 2 * η)) * (molLen θ T : ℝ) ^ 2
        ≤ Real.exp 1 * ((2 * Real.pi / α) ^ 2 * T ^ (-2 + 2 * η)) * T ^ (2 * θ) := by gcongr
      _ = Real.exp 1 * (2 * Real.pi / α) ^ 2 * (T ^ (-2 + 2 * η) * T ^ (2 * θ)) := by ring
      _ = Real.exp 1 * (2 * Real.pi / α) ^ 2 * T ^ (-(1 + 6 * η)) := by
          rw [← Real.rpow_add hT0, h2θ]; ring_nf
  have hpow : (Real.exp 1 * (2 * Real.pi * T ^ (-1 + η) / α) ^ 2 * (molLen θ T : ℝ) ^ 2) ^ (A - 1) ≤
      (Real.exp 1 * (2 * Real.pi / α) ^ 2) ^ (A - 1) * T ^ (-(1 + 6 * η) * (A - 1)) := by
    calc _ ≤ (Real.exp 1 * (2 * Real.pi / α) ^ 2 * T ^ (-(1 + 6 * η))) ^ (A - 1) :=
          Real.rpow_le_rpow (by positivity) hbase (by linarith)
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hT0.le]
  have hT1 : T + 1 ≤ 2 * T := by linarith
  have h3 : (3 * α * T / (2 * Real.pi)) ^ A = (3 * α / (2 * Real.pi)) ^ A * T ^ A := by
    rw [show 3 * α * T / (2 * Real.pi) = 3 * α / (2 * Real.pi) * T by ring,
      Real.mul_rpow (by positivity) hT0.le]
  rw [h3]
  have hκT : T ^ θ * T * T ^ A * T ^ (-(1 + 6 * η) * (A - 1)) = T ^ κ * T := by
    rw [show T ^ θ * T * T ^ A * T ^ (-(1 + 6 * η) * (A - 1)) =
      T ^ θ * T ^ A * T ^ (-(1 + 6 * η) * (A - 1)) * T by ring, ← Real.rpow_add hT0,
      ← Real.rpow_add hT0]
    congr 2
    simp only [κ]; ring
  calc 4 * (molLen θ T : ℝ) * ((T + 1) * (Ψ₀ * (K * ((3 * α / (2 * Real.pi)) ^ A * T ^ A))) *
        (Real.exp 1 * (2 * Real.pi * T ^ (-1 + η) / α) ^ 2 * (molLen θ T : ℝ) ^ 2) ^ (A - 1) *
          pairSum)
      ≤ 4 * T ^ θ * ((2 * T) * (Ψ₀ * (K * ((3 * α / (2 * Real.pi)) ^ A * T ^ A))) *
        ((Real.exp 1 * (2 * Real.pi / α) ^ 2) ^ (A - 1) * T ^ (-(1 + 6 * η) * (A - 1))) *
          pairSum) := by
        have := pairSum_nonneg
        gcongr
    _ = D * (T ^ θ * T * T ^ A * T ^ (-(1 + 6 * η) * (A - 1))) := by simp only [D]; ring
    _ = D * T ^ κ * T := by rw [hκT]; ring

/-! ## Huge ratios -/

/-- The size cut `Z = T^{1+η} N²` above which ratios are huge. -/
def hugeCut (θ T : ℝ) : ℝ := T ^ (1 + resExp θ) * (molLen θ T : ℝ) ^ 2

theorem tendsto_huge_div {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {Ψ₀ : ℝ}
    (hΨ : ∀ y, |ψ y| ≤ Ψ₀) {α β θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
    (R : ℝ → Set (ℕ × ℕ)) :
    Tendsto (fun T => ‖∑' c, (R T ∩ hugeRatio (hugeCut θ T)).indicator
      (fiberTerm ψ α β (molLen θ T) T) c‖ / T) atTop (𝓝 0) := by
  set η := resExp θ with hηdef
  have hη : 0 < η := by rw [hηdef]; unfold resExp; linarith
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  set A : ℝ := (θ + 2 + η) / η + 1 with hA
  have hA1 : 1 < A := by
    have : 0 < (θ + 2 + η) / η := by positivity
    rw [hA]; linarith
  have hAη : θ + 2 + η < η * A := by
    rw [hA, mul_add, mul_div_cancel₀ _ hη.ne']; linarith
  obtain ⟨K, hK, hKb⟩ := sum_decay_le hsupp hΨ (β := β) hα hA1
  set D : ℝ := 4 * (2 * Ψ₀ * (K * (3 * α / (2 * Real.pi)) ^ A)) * pairSum
  have hD : 0 ≤ D := by have := pairSum_nonneg; positivity
  set κ : ℝ := θ + A - (1 + η) * (A - 1)
  have hκ : κ < 0 := by simp only [κ]; nlinarith
  have hlim : Tendsto (fun T : ℝ => D * T ^ κ) atTop (𝓝 0) := by
    have := (tendsto_rpow_of_neg hκ).const_mul D
    rwa [mul_zero] at this
  refine squeeze_zero' (by filter_upwards [eventually_ge_atTop 0] with T hT; positivity) ?_ hlim
  filter_upwards [eventually_progression (β := β) hα, eventually_molLen_ge_one hθ0]
    with T hTβ hN1
  obtain ⟨hT, hβ⟩ := hTβ
  have hT0 : 0 < T := by linarith
  have hN1R : (1 : ℝ) ≤ molLen θ T := by exact_mod_cast hN1
  have hX : 0 < T ^ (1 + η) := Real.rpow_pos_of_pos hT0 _
  have h1 := norm_tsum_indicator_fiberTerm_le hsupp (molLen θ T) hT0
    (pos_of_progression hsupp hα hT0 hβ) (R T ∩ hugeRatio (hugeCut θ T))
  have h2 := hKb (molLen θ T) hT0 hβ
    (fun h k => (fun P => quadRatio P h k) ⁻¹' (R T ∩ hugeRatio (hugeCut θ T))) hX
    (fun h hh k hk P hP => by
      have hc := (pairProd_ge_of_huge hh hk hP.2)
      unfold hugeCut at hc
      rwa [mul_div_cancel_right₀ _ (by positivity)] at hc)
  have hN := molLen_cast_le_rpow (θ := θ) hT0.le
  rw [div_le_iff₀ hT0]
  refine (h1.trans h2).trans ?_
  have hT1 : T + 1 ≤ 2 * T := by linarith
  have h3 : (3 * α * T / (2 * Real.pi)) ^ A = (3 * α / (2 * Real.pi)) ^ A * T ^ A := by
    rw [show 3 * α * T / (2 * Real.pi) = 3 * α / (2 * Real.pi) * T by ring,
      Real.mul_rpow (by positivity) hT0.le]
  have h4 : (T ^ (1 + η)) ^ (-(A - 1)) = T ^ (-(1 + η) * (A - 1)) := by
    rw [← Real.rpow_mul hT0.le]; ring_nf
  rw [h3, h4]
  have hκT : T ^ θ * T * T ^ A * T ^ (-(1 + η) * (A - 1)) = T ^ κ * T := by
    rw [show T ^ θ * T * T ^ A * T ^ (-(1 + η) * (A - 1)) =
      T ^ θ * T ^ A * T ^ (-(1 + η) * (A - 1)) * T by ring, ← Real.rpow_add hT0,
      ← Real.rpow_add hT0]
    congr 2
    simp only [κ]; ring
  calc 4 * (molLen θ T : ℝ) * ((T + 1) * (Ψ₀ * (K * ((3 * α / (2 * Real.pi)) ^ A * T ^ A))) *
        T ^ (-(1 + η) * (A - 1)) * pairSum)
      ≤ 4 * T ^ θ * ((2 * T) * (Ψ₀ * (K * ((3 * α / (2 * Real.pi)) ^ A * T ^ A))) *
        T ^ (-(1 + η) * (A - 1)) * pairSum) := by
        have := pairSum_nonneg
        gcongr
    _ = D * (T ^ θ * T * T ^ A * T ^ (-(1 + η) * (A - 1))) := by simp only [D]; ring
    _ = D * T ^ κ * T := by rw [hκT]; ring

/-! ## Medium resonant ratios -/

/-- The medium resonant ratios: `|u(c) − j| < T^{−1+η}` for some `j ≠ 0`, `T^{1−2η} ≤ ab ≤ Z`. -/
def mediumResonant (α θ T : ℝ) : Set (ℕ × ℕ) :=
  {c | (∃ j : ℤ, j ≠ 0 ∧ |ratioPhase α c - j| < T ^ (-1 + resExp θ)) ∧
    T ^ (1 - 2 * resExp θ) ≤ ((c.1 * c.2 : ℕ) : ℝ) ∧ ((c.1 * c.2 : ℕ) : ℝ) ≤ hugeCut θ T}

/-- `(ab)^{−1/2} d(ab)(1 + log Nab) ≤ D(1 + 1/ε)(1 + log N) (ab)^{−(1/2 − 2ε)}`. -/
theorem divisor_log_rpow_le {ε : ℝ} (hε : 0 < ε) {N a b : ℕ} (hN : 1 ≤ N) (ha : 0 < a)
    (hb : 0 < b) :
    (Real.sqrt ((a : ℝ) * b))⁻¹ * (((a * b).divisors.card : ℝ) *
      (1 + Real.log ((N * a * b : ℕ) : ℝ))) ≤
      Sieve.divisorBoundConst ε * (1 + 1 / ε) * (1 + Real.log N) *
        (((a * b : ℕ) : ℝ) ^ (1 / 2 - 2 * ε))⁻¹ := by
  have hx1 : (1 : ℝ) ≤ ((a * b : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos ha hb
  have hD := Sieve.card_divisors_le_rpow hε (Nat.mul_pos ha hb).ne'
  set x : ℝ := ((a * b : ℕ) : ℝ)
  have hx0 : 0 < x := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogNab : 1 + Real.log ((N * a * b : ℕ) : ℝ) ≤ (1 + Real.log N) * ((1 + 1 / ε) * x ^ ε) := by
    have e : Real.log ((N * a * b : ℕ) : ℝ) = Real.log N + Real.log x := by
      rw [show N * a * b = N * (a * b) by ring, Nat.cast_mul, Real.log_mul (by positivity) hx0.ne']
    rw [e]
    have h1 := one_add_log_le_rpow hx1 hε
    calc 1 + (Real.log N + Real.log x) ≤ (1 + Real.log N) * (1 + Real.log x) := by nlinarith
      _ ≤ _ := by gcongr
  have hsq : (Real.sqrt ((a : ℝ) * b))⁻¹ = x ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]; simp [x]
  rw [hsq]
  have hD0 : 0 ≤ Sieve.divisorBoundConst ε := (Sieve.divisorBoundConst_pos hε).le
  calc x ^ (-(1 / 2) : ℝ) * (((a * b).divisors.card : ℝ) * (1 + Real.log ((N * a * b : ℕ) : ℝ)))
      ≤ x ^ (-(1 / 2) : ℝ) * ((Sieve.divisorBoundConst ε * x ^ ε) *
          ((1 + Real.log N) * ((1 + 1 / ε) * x ^ ε))) := by
        gcongr
    _ = Sieve.divisorBoundConst ε * (1 + 1 / ε) * (1 + Real.log N) *
          (x ^ (-(1 / 2) : ℝ) * x ^ ε * x ^ ε) := by ring
    _ = _ := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_neg hx0.le]
        congr 2; ring

/-- **The crude bound for one fibre term.** -/
theorem norm_fiberTerm_crude_le {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2) {Ψ₀ : ℝ}
    (hΨ : ∀ y, |ψ y| ≤ Ψ₀) {α β : ℝ} (hα : 0 < α) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hH : ∀ x : ℝ, 0 < x → ‖ZetaNotch.diagHarm x‖ ≤ C₀ * (1 + max 0 (Real.log x)))
    {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN1 : 1 ≤ N) {T : ℝ} (hT0 : 0 < T) (hβ : 2 * |β| ≤ α * T)
    {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    ‖fiberTerm ψ α β N T (a, b)‖ ≤ (T + 1) * (Ψ₀ * (C₀ * (1 + max 0 (Real.log (3 * α * T))) *
      (1 + Real.log N) ^ 3 * (Sieve.divisorBoundConst ε * (1 + 1 / ε)) *
        (((a * b : ℕ) : ℝ) ^ (1 / 2 - 2 * ε))⁻¹)) := by
  have hpos := pos_of_progression hsupp hα hT0 hβ
  set Mc : ℝ := C₀ * (1 + max 0 (Real.log (3 * α * T))) * (((a * b).divisors.card : ℝ) *
    (1 + Real.log N) ^ 2 * (1 + Real.log ((N * a * b : ℕ) : ℝ)))
  have hlogNab : 0 ≤ Real.log ((N * a * b : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hMc0 : 0 ≤ Mc := by positivity
  have hMc : ∀ x : ℝ, ψ (x / T) ≠ 0 → ‖ratioForm N a b (α * x + β)‖ ≤ Mc := by
    intro x hx
    have ht0 := hpos x hx
    have ht3 : α * x + β ≤ 3 * α * T := by
      obtain ⟨_, h2⟩ := hsupp hx
      rw [div_le_iff₀ hT0] at h2
      have := le_abs_self β; nlinarith
    refine (norm_ratioForm_le_crude hC₀ hH N ha hb ht0).trans ?_
    have hmax : 1 + max 0 (Real.log (α * x + β)) ≤ 1 + max 0 (Real.log (3 * α * T)) := by
      gcongr
    have hsum := Sieve.sum_gcd_mul_div_le hab ha hb N
    have hs0 : 0 ≤ ∑ h ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N,
        ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hmax hC₀) hsum hs0 (by positivity)
  refine (norm_fiberTerm_le hsupp hΨ N hT0 hpos hab ha hb hMc0 hMc).trans ?_
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  have hdl := divisor_log_rpow_le hε hN1 ha hb
  have hA : 0 ≤ C₀ * (1 + max 0 (Real.log (3 * α * T))) * (1 + Real.log N) ^ 2 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN1)
    positivity
  have key : (Real.sqrt ((a : ℝ) * b))⁻¹ * Mc ≤ C₀ * (1 + max 0 (Real.log (3 * α * T))) *
      (1 + Real.log N) ^ 3 * (Sieve.divisorBoundConst ε * (1 + 1 / ε)) *
        (((a * b : ℕ) : ℝ) ^ (1 / 2 - 2 * ε))⁻¹ := by
    calc (Real.sqrt ((a : ℝ) * b))⁻¹ * Mc
        = C₀ * (1 + max 0 (Real.log (3 * α * T))) * (1 + Real.log N) ^ 2 *
            ((Real.sqrt ((a : ℝ) * b))⁻¹ * (((a * b).divisors.card : ℝ) *
              (1 + Real.log ((N * a * b : ℕ) : ℝ)))) := by simp only [Mc]; ring
      _ ≤ C₀ * (1 + max 0 (Real.log (3 * α * T))) * (1 + Real.log N) ^ 2 *
            (Sieve.divisorBoundConst ε * (1 + 1 / ε) * (1 + Real.log N) *
              (((a * b : ℕ) : ℝ) ^ (1 / 2 - 2 * ε))⁻¹) := mul_le_mul_of_nonneg_left hdl hA
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hΨ0) (by linarith)

open Classical in
/-- **Reduction to a finite sum** over the coprime ratios of a set `M ⊆ {Y ≤ ab ≤ Z}`. -/
theorem norm_tsum_indicator_le_finset {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2)
    {α β : ℝ} (N : ℕ) {T : ℝ} (hT : 0 < T) (hpos : ∀ x : ℝ, ψ (x / T) ≠ 0 → 0 < α * x + β)
    (M : Set (ℕ × ℕ)) {Y Z : ℝ} (hY : 1 ≤ Y)
    (hM : ∀ c ∈ M, Y ≤ ((c.1 * c.2 : ℕ) : ℝ) ∧ ((c.1 * c.2 : ℕ) : ℝ) ≤ Z) :
    ‖∑' c, M.indicator (fiberTerm ψ α β N T) c‖ ≤
      ∑ c ∈ (Finset.Icc 1 ⌊Z⌋₊ ×ˢ Finset.Icc 1 ⌊Z⌋₊).filter
        (fun c => c ∈ M ∧ Nat.Coprime c.1 c.2), ‖fiberTerm ψ α β N T c‖ := by
  classical
  have hsumm := (summable_norm_fiberTerm hsupp N hT hpos).indicator M
  refine (norm_tsum_le_tsum_norm (by simpa [norm_indicator_eq_indicator_norm] using hsumm)).trans
    (le_of_eq ?_)
  simp_rw [norm_indicator_eq_indicator_norm]
  rw [tsum_eq_sum (s := (Finset.Icc 1 ⌊Z⌋₊ ×ˢ Finset.Icc 1 ⌊Z⌋₊).filter
    (fun c => c ∈ M ∧ Nat.Coprime c.1 c.2))]
  · refine Finset.sum_congr rfl fun c hc => ?_
    rw [Set.indicator_of_mem (Finset.mem_filter.mp hc).2.1]
  · intro c hc
    by_cases hcM : c ∈ M
    · rw [Set.indicator_of_mem hcM]
      obtain ⟨hYab, hZab⟩ := hM c hcM
      have hab1 : 1 ≤ c.1 * c.2 := by
        have : (1 : ℝ) ≤ ((c.1 * c.2 : ℕ) : ℝ) := hY.trans hYab
        exact_mod_cast this
      have ha : 0 < c.1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hab1)
      have hb : 0 < c.2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hab1)
      have hfl : c.1 * c.2 ≤ ⌊Z⌋₊ := Nat.le_floor hZab
      have hcop : ¬ Nat.Coprime c.1 c.2 := by
        intro hcop; apply hc
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨ha, (Nat.le_mul_of_pos_right _ hb).trans hfl⟩,
            Finset.mem_Icc.mpr ⟨hb, (Nat.le_mul_of_pos_left _ ha).trans hfl⟩⟩, hcM, hcop⟩
      rw [fiberTerm_eq_zero (fun h => hcop h.1), norm_zero]
    · rw [Set.indicator_of_notMem hcM]

theorem one_add_max_log_le {α T : ℝ} (hα : 0 < α) (hT : 1 ≤ T) :
    1 + max 0 (Real.log (3 * α * T)) ≤ (1 + |Real.log (3 * α)|) * (1 + Real.log T) := by
  have hT0 : 0 < T := by linarith
  have e : Real.log (3 * α * T) = Real.log (3 * α) + Real.log T :=
    Real.log_mul (by positivity) hT0.ne'
  have hlogT := Real.log_nonneg hT
  have h1 : max 0 (Real.log (3 * α * T)) ≤ |Real.log (3 * α)| + Real.log T := by
    rw [e]; exact max_le (by positivity) (by linarith [le_abs_self (Real.log (3 * α))])
  have := abs_nonneg (Real.log (3 * α))
  nlinarith

theorem two_floor_add_one_le {α T Z : ℝ} (hα : 0 < α) (hT : 1 ≤ T) (hZ1 : 1 ≤ Z)
    (hZ : Z ≤ T ^ (2 : ℝ)) :
    (2 * (⌊α / (2 * Real.pi) * (Real.log (2 * Z) + 1)⌋₊ : ℝ) + 1) ≤
      (2 * α / Real.pi + 1) * (1 + Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hZ0 : 0 < Z := by linarith
  have hlogT := Real.log_nonneg hT
  have hlogZ : Real.log Z ≤ 2 * Real.log T := by
    calc Real.log Z ≤ Real.log (T ^ (2 : ℝ)) := Real.log_le_log hZ0 hZ
      _ = 2 * Real.log T := by rw [Real.log_rpow hT0]
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hlog2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogZ0 : 0 ≤ Real.log Z := Real.log_nonneg hZ1
  have h0 : 0 ≤ α / (2 * Real.pi) * (Real.log (2 * Z) + 1) := by
    rw [Real.log_mul (by norm_num) hZ0.ne']; positivity
  have hfl := Nat.floor_le h0
  have hle : α / (2 * Real.pi) * (Real.log (2 * Z) + 1) ≤ α / Real.pi * (1 + Real.log T) := by
    rw [Real.log_mul (by norm_num) hZ0.ne']
    calc α / (2 * Real.pi) * (Real.log 2 + Real.log Z + 1)
        ≤ α / (2 * Real.pi) * (2 * (1 + Real.log T)) := by gcongr; linarith
      _ = α / Real.pi * (1 + Real.log T) := by field_simp
  have hαπ : 0 ≤ α / Real.pi := by positivity
  have e : 2 * α / Real.pi = 2 * (α / Real.pi) := by ring
  rw [e]
  nlinarith

/-- **Medium resonant ratios are negligible** (Farey spacing). -/
theorem tendsto_mediumResonant_div {ψ : ℝ → ℝ} (hsupp : Function.support ψ ⊆ Icc 1 2)
    {Ψ₀ : ℝ} (hΨ : ∀ y, |ψ y| ≤ Ψ₀) {α β θ : ℝ} (hα : 0 < α) (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    Tendsto (fun T => ‖∑' c, (mediumResonant α θ T).indicator
      (fiberTerm ψ α β (molLen θ T) T) c‖ / T) atTop (𝓝 0) := by
  classical
  set η := resExp θ with hηdef
  have hη : 0 < η := by rw [hηdef]; unfold resExp; linarith
  have hη8 : η < 1 / 8 := by rw [hηdef]; unfold resExp; linarith
  have h2θ : 2 * θ = 1 - 8 * η := by rw [hηdef]; unfold resExp; ring
  have hΨ0 : 0 ≤ Ψ₀ := (abs_nonneg _).trans (hΨ 0)
  obtain ⟨C₀, hC₀, hH⟩ := exists_norm_diagHarm_le
  have hε₂ : (0 : ℝ) < η / 8 := by positivity
  have hs0 : (0 : ℝ) < 1 / 2 - 2 * (η / 8) := by linarith
  have hs1 : 1 / 2 - 2 * (η / 8) < (1 : ℝ) := by linarith
  set s : ℝ := 1 / 2 - 2 * (η / 8) with hsdef
  set Dv := Sieve.divisorBoundConst (η / 8)
  have hDv : 0 ≤ Dv := (Sieve.divisorBoundConst_pos hε₂).le
  set q₁ : ℝ := (2 : ℝ) ^ (1 - s) / ((2 : ℝ) ^ (1 - s) - 1)
  set q₂ : ℝ := (2 : ℝ) ^ s / ((2 : ℝ) ^ s - 1)
  have hq₁ : 0 ≤ q₁ := by
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (show 0 < 1 - s by linarith)
    exact div_nonneg (by positivity) (by linarith)
  have hq₂ : 0 ≤ q₂ := by
    have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hs0
    exact div_nonneg (by positivity) (by linarith)
  set κ₁ : ℝ := 2 * η + 7 * η ^ 2 / 4
  set κ₂ : ℝ := (1 - 2 * η) * s
  have hκ₁ : 0 < κ₁ := by positivity
  have hκ₂ : 0 < κ₂ := by simp only [κ₂]; nlinarith
  set c₁ : ℝ := 1 + |Real.log (3 * α)|
  set Kc : ℝ := 2 * Ψ₀ * C₀ * c₁ * (Dv * (1 + 1 / (η / 8))) * (2 * α / Real.pi + 1)
  have hKc : 0 ≤ Kc := by positivity
  set B₁ : ℝ := 4 * Real.exp 3 * (2 * Real.pi / α) * q₁
  set B₂ : ℝ := (2 : ℝ) ^ s * q₂
  have hlim : Tendsto (fun T : ℝ => Kc * ((1 + Real.log T) ^ 5 * T ^ (-κ₁) * B₁ +
      (1 + Real.log T) ^ 5 * T ^ (-κ₂) * B₂)) atTop (𝓝 0) := by
    have h1 := (one_add_log_pow_mul_rpow_neg_tendsto 5 hκ₁).mul_const B₁
    have h2 := (one_add_log_pow_mul_rpow_neg_tendsto 5 hκ₂).mul_const B₂
    have := (h1.add h2).const_mul Kc
    simpa using this
  have hδ1 : ∀ᶠ T : ℝ in atTop, 2 * Real.pi * T ^ (-1 + η) / α ≤ 1 := by
    have h := ((tendsto_rpow_of_neg (show -1 + η < 0 by linarith)).const_mul (2 * Real.pi)).div_const α
    simp only [mul_zero, zero_div] at h
    exact h.eventually (ge_mem_nhds one_pos)
  refine squeeze_zero' (by filter_upwards [eventually_ge_atTop 0] with T hT; positivity) ?_ hlim
  filter_upwards [eventually_progression (β := β) hα, hδ1, eventually_molLen_ge_one hθ0]
    with T hTβ hδT hN1
  obtain ⟨hT, hβ⟩ := hTβ
  have hT0 : 0 < T := by linarith
  have hN1R : (1 : ℝ) ≤ molLen θ T := by exact_mod_cast hN1
  have hN := molLen_cast_le_rpow (θ := θ) hT0.le
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hY1 : 1 ≤ T ^ (1 - 2 * η) := Real.one_le_rpow hT (by linarith)
  have hZ : hugeCut θ T ≤ T ^ (2 - 7 * η) := by
    unfold hugeCut
    have hN2 : ((molLen θ T : ℕ) : ℝ) ^ 2 ≤ T ^ (2 * θ) := by
      rw [show (2 : ℝ) * θ = θ * 2 by ring, Real.rpow_mul hT0.le, Real.rpow_two]
      exact pow_le_pow_left₀ (by positivity) hN 2
    calc T ^ (1 + η) * ((molLen θ T : ℕ) : ℝ) ^ 2 ≤ T ^ (1 + η) * T ^ (2 * θ) := by gcongr
      _ = T ^ (2 - 7 * η) := by rw [← Real.rpow_add hT0, h2θ]; ring_nf
  have hYZ : T ^ (1 - 2 * η) ≤ hugeCut θ T := by
    unfold hugeCut
    calc T ^ (1 - 2 * η) ≤ T ^ (1 + η) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ ≤ T ^ (1 + η) * ((molLen θ T : ℕ) : ℝ) ^ 2 :=
          le_mul_of_one_le_right (by positivity) (one_le_pow₀ hN1R)
  have hZ0 : 0 < hugeCut θ T := by linarith
  have hpos := pos_of_progression hsupp hα hT0 hβ
  -- reduction to a finite sum
  have hfin := norm_tsum_indicator_le_finset hsupp (molLen θ T) hT0 hpos (mediumResonant α θ T)
    hY1 (fun c hc => ⟨hc.2.1, hc.2.2⟩)
  set Mfin := (Finset.Icc 1 ⌊hugeCut θ T⌋₊ ×ˢ Finset.Icc 1 ⌊hugeCut θ T⌋₊).filter
    (fun c => c ∈ mediumResonant α θ T ∧ Nat.Coprime c.1 c.2)
  set A : ℝ := C₀ * (1 + max 0 (Real.log (3 * α * T))) * (1 + Real.log (molLen θ T)) ^ 3 *
    (Dv * (1 + 1 / (η / 8)))
  have hterm : ∀ c ∈ Mfin, ‖fiberTerm ψ α β (molLen θ T) T c‖ ≤
      (T + 1) * (Ψ₀ * (A * (((c.1 * c.2 : ℕ) : ℝ) ^ s)⁻¹)) := by
    intro c hc
    obtain ⟨hcI, -, hcop⟩ := Finset.mem_filter.mp hc
    obtain ⟨hc1, hc2⟩ := Finset.mem_product.mp hcI
    exact norm_fiberTerm_crude_le hsupp hΨ hα hC₀ hH hε₂ hN1 hT0 hβ hcop
      (Finset.mem_Icc.mp hc1).1 (Finset.mem_Icc.mp hc2).1
  have hS : ∀ c ∈ Mfin, 0 < c.1 ∧ 0 < c.2 ∧ Nat.Coprime c.1 c.2 ∧
      (∃ j : ℤ, j ≠ 0 ∧ |ratioLog c - 2 * Real.pi * j / α| < 2 * Real.pi * T ^ (-1 + η) / α) ∧
      T ^ (1 - 2 * η) ≤ ((c.1 * c.2 : ℕ) : ℝ) ∧ ((c.1 * c.2 : ℕ) : ℝ) ≤ hugeCut θ T := by
    intro c hc
    obtain ⟨hcI, ⟨⟨j, hj0, hj⟩, hYab, hZab⟩, hcop⟩ := Finset.mem_filter.mp hc
    obtain ⟨hc1, hc2⟩ := Finset.mem_product.mp hcI
    exact ⟨(Finset.mem_Icc.mp hc1).1, (Finset.mem_Icc.mp hc2).1, hcop,
      ⟨j, hj0, abs_ratioLog_sub_lt hα hj⟩, hYab, hZab⟩
  have hfar := sum_resonant_rpow_le hα (by positivity) hδT hY1 hYZ hs0 hs1 Mfin hS
  -- the logarithmic factors
  set L : ℝ := 1 + Real.log T
  have hL1 : 1 ≤ L := by simp only [L]; linarith
  have hJ := two_floor_add_one_le hα hT (hY1.trans hYZ)
    (hZ.trans (Real.rpow_le_rpow_of_exponent_le hT (by linarith)))
  have hlogN : Real.log (molLen θ T) ≤ Real.log T := Real.log_le_log (by linarith)
    (hN.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hT (show θ ≤ 1 by linarith)))
  have hlogN0 : 0 ≤ Real.log (molLen θ T) := Real.log_nonneg hN1R
  have hA : A ≤ C₀ * (c₁ * L) * L ^ 3 * (Dv * (1 + 1 / (η / 8))) := by
    simp only [A]
    have := one_add_max_log_le hα hT
    gcongr
    simp only [L]; linarith
  have hX₁ : 4 * Real.exp 3 * (2 * Real.pi * T ^ (-1 + η) / α) * (hugeCut θ T ^ (1 - s) * q₁) ≤
      B₁ * T ^ (-κ₁) := by
    have h1 : hugeCut θ T ^ (1 - s) ≤ T ^ ((2 - 7 * η) * (1 - s)) := by
      rw [Real.rpow_mul hT0.le]; exact Real.rpow_le_rpow hZ0.le hZ (by linarith)
    have e : T ^ (-1 + η) * T ^ ((2 - 7 * η) * (1 - s)) = T ^ (-κ₁) := by
      rw [← Real.rpow_add hT0]; congr 1; simp only [κ₁, s]; ring
    calc 4 * Real.exp 3 * (2 * Real.pi * T ^ (-1 + η) / α) * (hugeCut θ T ^ (1 - s) * q₁)
        ≤ 4 * Real.exp 3 * (2 * Real.pi * T ^ (-1 + η) / α) * (T ^ ((2 - 7 * η) * (1 - s)) * q₁) := by
          gcongr
      _ = 4 * Real.exp 3 * (2 * Real.pi / α) * q₁ * (T ^ (-1 + η) * T ^ ((2 - 7 * η) * (1 - s))) := by
          ring
      _ = B₁ * T ^ (-κ₁) := by rw [e]
  have hX₂ : (2 : ℝ) ^ s * ((T ^ (1 - 2 * η)) ^ s)⁻¹ * q₂ = B₂ * T ^ (-κ₂) := by
    rw [← Real.rpow_mul hT0.le, ← Real.rpow_neg hT0.le]; simp only [B₂, κ₂]; ring
  have hsum0 : 0 ≤ ∑ c ∈ Mfin, (((c.1 * c.2 : ℕ) : ℝ) ^ s)⁻¹ :=
    Finset.sum_nonneg fun c _ => by positivity
  have hA0 : 0 ≤ A := by simp only [A]; positivity
  have hQ : ∑ c ∈ Mfin, (((c.1 * c.2 : ℕ) : ℝ) ^ s)⁻¹ ≤
      (2 * α / Real.pi + 1) * L * (B₁ * T ^ (-κ₁) + B₂ * T ^ (-κ₂)) := by
    refine hfar.trans ?_
    have hnn : 0 ≤ 4 * Real.exp 3 * (2 * Real.pi * T ^ (-1 + η) / α) *
        (hugeCut θ T ^ (1 - s) * q₁) + (2 : ℝ) ^ s * ((T ^ (1 - 2 * η)) ^ s)⁻¹ * q₂ := by
      positivity
    exact mul_le_mul hJ (add_le_add hX₁ (le_of_eq hX₂)) hnn (by positivity)
  rw [div_le_iff₀ hT0]
  refine hfin.trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  calc (T + 1) * (Ψ₀ * (A * ∑ c ∈ Mfin, (((c.1 * c.2 : ℕ) : ℝ) ^ s)⁻¹))
      ≤ (2 * T) * (Ψ₀ * ((C₀ * (c₁ * L) * L ^ 3 * (Dv * (1 + 1 / (η / 8)))) *
          ((2 * α / Real.pi + 1) * L * (B₁ * T ^ (-κ₁) + B₂ * T ^ (-κ₂))))) := by
        have hA'0 : 0 ≤ C₀ * (c₁ * L) * L ^ 3 * (Dv * (1 + 1 / (η / 8))) := by positivity
        refine mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left
          (mul_le_mul hA hQ hsum0 hA'0) hΨ0) (by positivity) (by positivity)
    _ = Kc * (L ^ 5 * T ^ (-κ₁) * B₁ + L ^ 5 * T ^ (-κ₂) * B₂) * T := by
        simp only [Kc]; ring

end

end RHTower.VerticalAP
