import Mathlib

/-!
# Exponent arithmetic of the Guth–Maynard zero-density estimate

For `σ ∈ [7/10, 8/10]` the zero-detecting polynomial is raised into the window
`[T^a, T^{3a/2}]`, `a = 10/(6 + 10σ)`, and the target is `N(σ, T) ≤ T^{E₀ + o(1)}` with
`E₀ = 15(1 - σ)/(3 + 5σ)`.  With the switching exponent `α = 15(1 - σ)/((3 + 5σ)(18/5 - 4σ))`:

* the three terms of the large values estimate meet the target exactly:
  `3a(1 - σ) = E₀`, `α(18/5 - 4σ) = E₀`, `1 + a(12/5 - 4σ) = E₀`;
* past the switch the mean value term is smaller:
  `1 + (1 - 2σ)α = (129 - 195σ + 50σ²)/(2(3+5σ)(9-10σ))
    = E₀ - (250(σ - 3/4)² + 3/8)/(2(3+5σ)(9-10σ))`;
* the Type II count has the margin `E₀ - 1 - (3a/4)(2 - 4σ) = (9 - 10σ)/(6 + 10σ) ≥ 1/14`;
* `E₀ ≤ (30/13)(1 - σ)` for `σ ≥ 7/10`, Ingham's `3/(2 - σ) ≤ 30/13` for `σ ≤ 7/10`, Huxley's
  `3/(3σ - 1) ≤ 30/13` for `σ ≥ 23/30`, and `(30/13)(1 - σ) ≥ 1` for `σ ≤ 17/30`.

The last two parts collect the power comparisons `X ↦ X^e` used with these exponents, and the
bookkeeping of the three terms `B²L²/V'² + B⁴L^{18/5}/V'⁴ + T B⁴L^{12/5}/V'⁴` of the large values
estimate for a raised polynomial of length `L ≤ 2^M X` at level `V' = X^σ v/R`
(`class_count_gm_arith`, `gm_loss_le`).
-/

set_option autoImplicit false

namespace RHTower

noncomputable section

/-- The window exponent `a(σ) = 10/(6 + 10σ)`. -/
def gmWindowExponent (σ : ℝ) : ℝ := 10 / (6 + 10 * σ)

/-- The Guth–Maynard density exponent `15(1 - σ)/(3 + 5σ)`. -/
def gmDensityExponent (σ : ℝ) : ℝ := 15 * (1 - σ) / (3 + 5 * σ)

/-- The switching exponent `α(σ) = 15(1 - σ)/((3 + 5σ)(18/5 - 4σ))`. -/
def gmSwitchExponent (σ : ℝ) : ℝ := 15 * (1 - σ) / ((3 + 5 * σ) * (18 / 5 - 4 * σ))

/-! ## The three terms of the large values estimate -/

theorem gmWindowExponent_pos {σ : ℝ} (hσ : 0 ≤ σ) : 0 < gmWindowExponent σ := by
  unfold gmWindowExponent
  positivity

theorem gmWindowExponent_le_one {σ : ℝ} (hσ : 2 / 5 ≤ σ) : gmWindowExponent σ ≤ 1 := by
  unfold gmWindowExponent
  rw [div_le_one (by linarith)]
  linarith

/-- The diagonal term: `3a(1 - σ) = E₀`. -/
theorem three_mul_gmWindowExponent_mul {σ : ℝ} (hσ : 0 ≤ σ) :
    3 * gmWindowExponent σ * (1 - σ) = gmDensityExponent σ := by
  unfold gmWindowExponent gmDensityExponent
  have h1 : (6 + 10 * σ) ≠ 0 := by linarith
  have h2 : (3 + 5 * σ) ≠ 0 := by linarith
  field_simp
  ring

/-- The switching exponent with the denominator cleared:
`α = 75(1 - σ)/(2(3 + 5σ)(9 - 10σ))`. -/
theorem gmSwitchExponent_eq {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 9 / 10) :
    gmSwitchExponent σ = 75 * (1 - σ) / (2 * (3 + 5 * σ) * (9 - 10 * σ)) := by
  unfold gmSwitchExponent
  have h1 : 0 < 18 / 5 - 4 * σ := by linarith
  have h3 : 0 < 9 - 10 * σ := by linarith
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The `N^{18/5}V⁻⁴` term at the switch: `α(18/5 - 4σ) = E₀`. -/
theorem gmSwitchExponent_mul {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 9 / 10) :
    gmSwitchExponent σ * (18 / 5 - 4 * σ) = gmDensityExponent σ := by
  unfold gmSwitchExponent gmDensityExponent
  have h1 : 0 < 18 / 5 - 4 * σ := by linarith
  rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- The `T N^{12/5}V⁻⁴` term at the window's lower end: `1 + a(12/5 - 4σ) = E₀`. -/
theorem one_add_gmWindowExponent_mul {σ : ℝ} (hσ : 0 ≤ σ) :
    1 + gmWindowExponent σ * (12 / 5 - 4 * σ) = gmDensityExponent σ := by
  unfold gmWindowExponent gmDensityExponent
  have h1 : (6 + 10 * σ) ≠ 0 := by linarith
  have h2 : (3 + 5 * σ) ≠ 0 := by linarith
  field_simp
  ring

/-! ## The mean value term past the switch -/

/-- **The identity of the switch.**
`1 + (1 - 2σ)α = (129 - 195σ + 50σ²)/(2(3+5σ)(9-10σ))`. -/
theorem one_add_mul_gmSwitchExponent_eq {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 9 / 10) :
    1 + (1 - 2 * σ) * gmSwitchExponent σ
      = (129 - 195 * σ + 50 * σ ^ 2) / (2 * (3 + 5 * σ) * (9 - 10 * σ)) := by
  have h3 : 0 < 9 - 10 * σ := by linarith
  have hD : (2 * (3 + 5 * σ) * (9 - 10 * σ)) ≠ 0 := by positivity
  rw [gmSwitchExponent_eq hσ0 hσ1, mul_div_assoc', one_add_div hD, div_left_inj' hD]
  ring

/-- **The identity of the switch, second form.**
`1 + (1 - 2σ)α = E₀ - (250(σ - 3/4)² + 3/8)/(2(3+5σ)(9-10σ))`. -/
theorem one_add_mul_gmSwitchExponent_eq_sub {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 9 / 10) :
    1 + (1 - 2 * σ) * gmSwitchExponent σ
      = gmDensityExponent σ - (250 * (σ - 3 / 4) ^ 2 + 3 / 8) / (2 * (3 + 5 * σ) * (9 - 10 * σ)) := by
  have h3 : 0 < 9 - 10 * σ := by linarith
  rw [one_add_mul_gmSwitchExponent_eq hσ0 hσ1, eq_sub_iff_add_eq, ← add_div,
    gmDensityExponent, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- Past the switch the mean value term stays below the target: `1 + α(1 - 2σ) ≤ E₀`. -/
theorem one_add_gmSwitchExponent_mul_le {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 9 / 10) :
    1 + gmSwitchExponent σ * (1 - 2 * σ) ≤ gmDensityExponent σ := by
  rw [mul_comm, one_add_mul_gmSwitchExponent_eq_sub hσ0 hσ1, sub_le_self_iff]
  have h3 : 0 < 9 - 10 * σ := by linarith
  positivity

/-! ## The Type II margin and the comparisons with `30/13` -/

/-- **The Type II margin.**  `E₀ - 1 - (3a/4)(2 - 4σ) = (9 - 10σ)/(6 + 10σ)`. -/
theorem gmDensityExponent_sub_typeTwo_eq {σ : ℝ} (hσ : 0 ≤ σ) :
    gmDensityExponent σ - 1 - 3 * gmWindowExponent σ / 4 * (2 - 4 * σ)
      = (9 - 10 * σ) / (6 + 10 * σ) := by
  unfold gmWindowExponent gmDensityExponent
  have h1 : (6 + 10 * σ) ≠ 0 := by linarith
  have h2 : (3 + 5 * σ) ≠ 0 := by linarith
  field_simp
  ring

/-- **The Type II count fits.**  For `0 ≤ σ ≤ 4/5` and `δ ≤ 1/64`,
`1 + 4δ + (3a/4)(2 - 4σ) ≤ E₀`. -/
theorem typeTwo_le_gmDensityExponent {σ δ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 4 / 5) (hδ : δ ≤ 1 / 64) :
    1 + 4 * δ + 3 * gmWindowExponent σ / 4 * (2 - 4 * σ) ≤ gmDensityExponent σ := by
  have h := gmDensityExponent_sub_typeTwo_eq hσ0
  have hmargin : 1 / 14 ≤ (9 - 10 * σ) / (6 + 10 * σ) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  linarith

/-- `E₀ ≤ (30/13)(1 - σ)` for `7/10 ≤ σ ≤ 1`. -/
theorem gmDensityExponent_le_thirty_thirteenths {σ : ℝ} (hσ0 : 7 / 10 ≤ σ) (hσ1 : σ ≤ 1) :
    gmDensityExponent σ ≤ (30 / 13) * (1 - σ) := by
  unfold gmDensityExponent
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- Ingham's exponent: `3/(2 - σ) ≤ 30/13` for `σ ≤ 7/10`. -/
theorem ingham_exponent_le_thirty_thirteenths {σ : ℝ} (hσ : σ ≤ 7 / 10) :
    3 / (2 - σ) ≤ 30 / 13 := by
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- Huxley's exponent: `3/(3σ - 1) ≤ 30/13` for `σ ≥ 23/30`. -/
theorem huxley_exponent_le_thirty_thirteenths {σ : ℝ} (hσ : 23 / 30 ≤ σ) :
    3 / (3 * σ - 1) ≤ 30 / 13 := by
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- The trivial range: `(30/13)(1 - σ) ≥ 1` for `σ ≤ 17/30`. -/
theorem one_le_thirty_thirteenths_mul {σ : ℝ} (hσ : σ ≤ 17 / 30) : 1 ≤ (30 / 13) * (1 - σ) := by
  linarith

/-! ## Power comparisons -/

/-- **The diagonal term in a window.**  If `0 ≤ X ≤ T^{3a/2} L` with `0 ≤ L`, `L² ≤ T^κ` and
`σ ≤ 1`, then `X^{2 - 2σ} ≤ T^{(3a + κ)(1 - σ)}`. -/
theorem rpow_two_sub_le_of_le_window {T X L a κ σ : ℝ} (hT : 1 ≤ T) (hX0 : 0 ≤ X) (hL0 : 0 ≤ L)
    (hX : X ≤ T ^ (3 * a / 2) * L) (hLκ : L ^ 2 ≤ T ^ κ) (hσ : σ ≤ 1) :
    X ^ (2 - 2 * σ) ≤ T ^ ((3 * a + κ) * (1 - σ)) := by
  have hT0 : 0 < T := by linarith
  have h1 : X ^ (2 - 2 * σ) ≤ (T ^ (3 * a / 2) * L) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow hX0 hX (by linarith)
  have h2 : (T ^ (3 * a / 2) * L) ^ (2 - 2 * σ) = T ^ (3 * a * (1 - σ)) * (L ^ 2) ^ (1 - σ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hT0.le _) hL0, ← Real.rpow_mul hT0.le,
      ← Real.rpow_natCast L 2, ← Real.rpow_mul hL0]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  have h3 : (L ^ 2) ^ (1 - σ) ≤ (T ^ κ) ^ (1 - σ) :=
    Real.rpow_le_rpow (by positivity) hLκ (by linarith)
  calc X ^ (2 - 2 * σ) ≤ T ^ (3 * a * (1 - σ)) * (L ^ 2) ^ (1 - σ) := h2 ▸ h1
    _ ≤ T ^ (3 * a * (1 - σ)) * (T ^ κ) ^ (1 - σ) :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hT0.le _)
    _ = T ^ ((3 * a + κ) * (1 - σ)) := by
        rw [← Real.rpow_mul hT0.le, ← Real.rpow_add hT0]
        ring_nf

/-- **Upper end, positive exponent.**  `0 ≤ X ≤ T^α`, `0 ≤ e` give `X^e ≤ T^{αe}`. -/
theorem rpow_le_rpow_mul_of_le {T X α e : ℝ} (hT : 0 ≤ T) (hX0 : 0 ≤ X) (hX : X ≤ T ^ α)
    (he : 0 ≤ e) : X ^ e ≤ T ^ (α * e) := by
  rw [Real.rpow_mul hT]
  exact Real.rpow_le_rpow hX0 hX he

/-- **Lower end, nonpositive exponent.**  `T^a ≤ X`, `e ≤ 0`, `T > 0` give `T X^e ≤ T^{1 + ae}`. -/
theorem mul_rpow_le_of_rpow_le {T X a e : ℝ} (hT : 0 < T) (hX : T ^ a ≤ X) (he : e ≤ 0) :
    T * X ^ e ≤ T ^ (1 + a * e) := by
  calc T * X ^ e ≤ T * (T ^ a) ^ e :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT _) hX he)
          hT.le
    _ = T ^ (1 + a * e) := by rw [← Real.rpow_mul hT.le, Real.rpow_add hT, Real.rpow_one]

/-! ## The three terms for a raised polynomial -/

/-- `X^{e - kσ} = X^e/(X^σ)^k` for `X > 0`. -/
theorem rpow_sub_nat_mul_eq_div {X e σ : ℝ} (hX : 0 < X) (k : ℕ) :
    X ^ (e - k * σ) = X ^ e / (X ^ σ) ^ k := by
  rw [Real.rpow_sub hX, mul_comm, Real.rpow_mul hX.le, Real.rpow_natCast]

/-- A length `0 ≤ L ≤ 2^M X` raised to `0 ≤ e ≤ 4` is at most `2^{4M} X^e`. -/
theorem rpow_le_two_pow_mul_rpow {L X e : ℝ} {M : ℕ} (hL0 : 0 ≤ L) (hX0 : 0 ≤ X)
    (hL : L ≤ 2 ^ M * X) (he0 : 0 ≤ e) (he4 : e ≤ 4) : L ^ e ≤ 2 ^ (4 * M) * X ^ e := by
  have h2M : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
  calc L ^ e ≤ (2 ^ M * X) ^ e := Real.rpow_le_rpow hL0 hL he0
    _ = (2 ^ M : ℝ) ^ e * X ^ e := Real.mul_rpow (by positivity) hX0
    _ ≤ (2 ^ M : ℝ) ^ (4 : ℝ) * X ^ e :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le h2M he4)
          (Real.rpow_nonneg hX0 _)
    _ = 2 ^ (4 * M) * X ^ e := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul, mul_comm M 4]

/-- **One term of the estimate.**  With `1 ≤ B`, `1 ≤ R`, `0 < v`, `1/v ≤ Q^M`, `1 ≤ Q`, `p > 0`,
`k ≤ 4` and `0 ≤ l ≤ 2^{4M} x`: `B^k l/(pv/R)^k ≤ B⁴ R⁴ 2^{4M} Q^{4M} · x/p^k`. -/
theorem gm_term_le {B R v Q p l x : ℝ} {k M : ℕ} (hk : k ≤ 4) (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hv : 0 < v) (hQ : 1 ≤ Q) (hvQ : 1 / Q ^ M ≤ v) (hp : 0 < p) (hl0 : 0 ≤ l)
    (hl : l ≤ 2 ^ (4 * M) * x) :
    B ^ k * l / (p * v / R) ^ k ≤ B ^ 4 * R ^ 4 * 2 ^ (4 * M) * Q ^ (4 * M) * (x / p ^ k) := by
  have hR0 : 0 < R := by linarith
  have hQM : 1 ≤ Q ^ M := one_le_pow₀ hQ
  have hw : 1 / v ≤ Q ^ M := by
    rw [div_le_iff₀ hv]
    rw [div_le_iff₀ (by positivity)] at hvQ
    linarith
  have hw0 : 0 ≤ 1 / v := by positivity
  have hkey : B ^ k * l / (p * v / R) ^ k = (B ^ k * R ^ k * (1 / v) ^ k) * (l / p ^ k) := by
    rw [div_pow, mul_pow, one_div_pow]
    field_simp
  have hBk : B ^ k ≤ B ^ 4 := pow_le_pow_right₀ hB hk
  have hRk : R ^ k ≤ R ^ 4 := pow_le_pow_right₀ hR hk
  have hwk : (1 / v) ^ k ≤ Q ^ (4 * M) := by
    calc (1 / v) ^ k ≤ (Q ^ M) ^ k := pow_le_pow_left₀ hw0 hw k
      _ ≤ (Q ^ M) ^ 4 := pow_le_pow_right₀ hQM hk
      _ = Q ^ (4 * M) := by rw [← pow_mul, mul_comm]
  have hlk : l / p ^ k ≤ 2 ^ (4 * M) * (x / p ^ k) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hl (by positivity)
  have hQ0 : 0 < Q := by linarith
  rw [hkey]
  calc B ^ k * R ^ k * (1 / v) ^ k * (l / p ^ k)
      ≤ B ^ 4 * R ^ 4 * Q ^ (4 * M) * (2 ^ (4 * M) * (x / p ^ k)) := by
        apply mul_le_mul _ hlk (by positivity) (by positivity)
        exact mul_le_mul (mul_le_mul hBk hRk (by positivity) (by positivity)) hwk
          (by positivity) (by positivity)
    _ = B ^ 4 * R ^ 4 * 2 ^ (4 * M) * Q ^ (4 * M) * (x / p ^ k) := by ring

/-- **The Guth–Maynard range, arithmetic.**  Let `T^a ≤ X ≤ T^α`, `X^{2-2σ} ≤ T^{E₀+κ}`,
`α(18/5 - 4σ) ≤ E₀` and `1 + a(12/5 - 4σ) ≤ E₀`, and let the large values estimate for a
polynomial of length `L ≤ 2^M X` at level `X^σ v` (`1/v ≤ Q^M`) on `R ≤ M + 1` blocks with
coefficients `≤ B` give
`c ≤ R C T^{ε₁}(B²L²/(X^σv/R)² + B⁴L^{18/5}/(X^σv/R)⁴ + T B⁴L^{12/5}/(X^σv/R)⁴)`.
Then `c ≤ 3(M+1)⁵ 2^{4M} C · T^{ε₁} B⁴ Q^{4M} · T^{E₀+κ}`. -/
theorem class_count_gm_arith {T X σ E₀ a α κ C ε₁ B R L v Q c : ℝ} {M : ℕ}
    (hT : 1 ≤ T) (hX : 1 ≤ X) (hσ0 : 3 / 5 < σ) (hσ1 : σ < 9 / 10)
    (hXa : T ^ a ≤ X) (hXα : X ≤ T ^ α) (hdiag : X ^ (2 - 2 * σ) ≤ T ^ (E₀ + κ)) (hκ : 0 ≤ κ)
    (hg2 : α * (18 / 5 - 4 * σ) ≤ E₀) (hg3 : 1 + a * (12 / 5 - 4 * σ) ≤ E₀)
    (hv : 0 < v) (hQ : 1 ≤ Q) (hvQ : 1 / Q ^ M ≤ v) (hR : 1 ≤ R) (hRM : R ≤ M + 1)
    (hL0 : 0 ≤ L) (hL : L ≤ 2 ^ M * X) (hB : 1 ≤ B) (hC : 0 ≤ C)
    (hc : c ≤ R * (C * T ^ ε₁ * (B ^ 2 * L ^ 2 / (X ^ σ * v / R) ^ 2
      + B ^ 4 * L ^ (18/5 : ℝ) / (X ^ σ * v / R) ^ 4
      + T * B ^ 4 * L ^ (12/5 : ℝ) / (X ^ σ * v / R) ^ 4))) :
    c ≤ 3 * ((M : ℝ) + 1) ^ 5 * 2 ^ (4 * M) * C * (T ^ ε₁ * B ^ 4 * Q ^ (4 * M)) *
      T ^ (E₀ + κ) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by linarith
  have hp : 0 < X ^ σ := Real.rpow_pos_of_pos hX0 σ
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = B ^ 4 * R ^ 4 * 2 ^ (4 * M) * Q ^ (4 * M) := ⟨_, rfl⟩
  -- the three terms
  have h1 : B ^ 2 * L ^ 2 / (X ^ σ * v / R) ^ 2 ≤ Y * X ^ (2 - 2 * σ) := by
    have hL2 : L ^ 2 ≤ 2 ^ (4 * M) * X ^ 2 := by
      have h := rpow_le_two_pow_mul_rpow hL0 hX0.le hL (e := 2) (by norm_num) (by norm_num)
      rwa [Real.rpow_two, Real.rpow_two] at h
    have h := gm_term_le (k := 2) (by norm_num) hB hR hv hQ hvQ hp (by positivity) hL2
    rw [show (2 : ℝ) - 2 * σ = 2 - ((2 : ℕ) : ℝ) * σ by norm_num, rpow_sub_nat_mul_eq_div hX0,
      Real.rpow_two, hY]
    exact h
  have h2 : B ^ 4 * L ^ (18/5 : ℝ) / (X ^ σ * v / R) ^ 4 ≤ Y * X ^ (18 / 5 - 4 * σ) := by
    have h := gm_term_le (k := 4) le_rfl hB hR hv hQ hvQ hp (by positivity)
      (rpow_le_two_pow_mul_rpow hL0 hX0.le hL (e := 18 / 5) (by norm_num) (by norm_num))
    rw [show (18 / 5 : ℝ) - 4 * σ = 18 / 5 - ((4 : ℕ) : ℝ) * σ by norm_num,
      rpow_sub_nat_mul_eq_div hX0, hY]
    exact h
  have h3 : T * B ^ 4 * L ^ (12/5 : ℝ) / (X ^ σ * v / R) ^ 4 ≤ Y * (T * X ^ (12 / 5 - 4 * σ)) := by
    have h := gm_term_le (k := 4) le_rfl hB hR hv hQ hvQ hp (by positivity)
      (rpow_le_two_pow_mul_rpow hL0 hX0.le hL (e := 12 / 5) (by norm_num) (by norm_num))
    rw [show (12 / 5 : ℝ) - 4 * σ = 12 / 5 - ((4 : ℕ) : ℝ) * σ by norm_num,
      rpow_sub_nat_mul_eq_div hX0, hY]
    rw [mul_assoc T, mul_div_assoc]
    calc T * (B ^ 4 * L ^ (12 / 5 : ℝ) / (X ^ σ * v / R) ^ 4)
        ≤ T * (B ^ 4 * R ^ 4 * 2 ^ (4 * M) * Q ^ (4 * M) * (X ^ (12 / 5 : ℝ) / (X ^ σ) ^ 4)) :=
          mul_le_mul_of_nonneg_left h hT0.le
      _ = B ^ 4 * R ^ 4 * 2 ^ (4 * M) * Q ^ (4 * M) * (T * (X ^ (12 / 5 : ℝ) / (X ^ σ) ^ 4)) := by
          ring
  -- the three exponents
  have e2 : X ^ (18 / 5 - 4 * σ) ≤ T ^ (E₀ + κ) :=
    le_trans (rpow_le_rpow_mul_of_le hT0.le hX0.le hXα (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hT (by linarith))
  have e3 : T * X ^ (12 / 5 - 4 * σ) ≤ T ^ (E₀ + κ) :=
    le_trans (mul_rpow_le_of_rpow_le hT0 hXa (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hT (by linarith))
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hsum : B ^ 2 * L ^ 2 / (X ^ σ * v / R) ^ 2 + B ^ 4 * L ^ (18/5 : ℝ) / (X ^ σ * v / R) ^ 4
      + T * B ^ 4 * L ^ (12/5 : ℝ) / (X ^ σ * v / R) ^ 4 ≤ Y * (3 * T ^ (E₀ + κ)) := by
    have := mul_le_mul_of_nonneg_left hdiag hY0
    have := mul_le_mul_of_nonneg_left e2 hY0
    have := mul_le_mul_of_nonneg_left e3 hY0
    nlinarith
  have hR4 : R ^ 4 ≤ ((M : ℝ) + 1) ^ 4 := pow_le_pow_left₀ (by linarith) hRM 4
  have hR0 : 0 ≤ R := by linarith
  have hTε : 0 ≤ T ^ ε₁ := Real.rpow_nonneg hT0.le _
  have hTE : 0 ≤ T ^ (E₀ + κ) := Real.rpow_nonneg hT0.le _
  calc c ≤ R * (C * T ^ ε₁ * (Y * (3 * T ^ (E₀ + κ)))) :=
        le_trans hc (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) hR0)
    _ = 3 * C * (R * R ^ 4) * 2 ^ (4 * M) * (T ^ ε₁ * B ^ 4 * Q ^ (4 * M)) * T ^ (E₀ + κ) := by
        rw [hY]
        ring
    _ ≤ 3 * C * (((M : ℝ) + 1) * ((M : ℝ) + 1) ^ 4) * 2 ^ (4 * M) *
          (T ^ ε₁ * B ^ 4 * Q ^ (4 * M)) * T ^ (E₀ + κ) := by
        gcongr
    _ = 3 * ((M : ℝ) + 1) ^ 5 * 2 ^ (4 * M) * C * (T ^ ε₁ * B ^ 4 * Q ^ (4 * M)) *
          T ^ (E₀ + κ) := by ring

/-- **The losses of the Guth–Maynard range.**  With the coefficient bound
`B = ((C_η + 1) T^{3η})^{2M}`, `24Mη = ε/4` and `Q^{4M} ≤ T^{ε/4}`:
`T^{ε/4} B⁴ Q^{4M} T^{E₀+ε/4} ≤ (C_η + 1)^{8M} T^{E₀+ε}`. -/
theorem gm_loss_le {T Cη η Q ε E₀ : ℝ} {M : ℕ} (hT : 0 < T) (hCη : 0 ≤ Cη)
    (h24 : 24 * (M : ℝ) * η = ε / 4) (hQ : Q ^ (4 * M) ≤ T ^ (ε / 4)) :
    T ^ (ε / 4) * (((Cη + 1) * T ^ (3 * η)) ^ (2 * M)) ^ 4 * Q ^ (4 * M) * T ^ (E₀ + ε / 4)
      ≤ (Cη + 1) ^ (8 * M) * T ^ (E₀ + ε) := by
  have hB4 : (((Cη + 1) * T ^ (3 * η)) ^ (2 * M)) ^ 4 = (Cη + 1) ^ (8 * M) * T ^ (ε / 4) := by
    rw [← pow_mul, mul_pow, ← Real.rpow_natCast (T ^ (3 * η)), ← Real.rpow_mul hT.le,
      show 2 * M * 4 = 8 * M by ring]
    congr 2
    push_cast
    linarith
  have hs : T ^ (ε / 4) * T ^ (ε / 4) * T ^ (ε / 4) * T ^ (E₀ + ε / 4) = T ^ (E₀ + ε) := by
    rw [← Real.rpow_add hT, ← Real.rpow_add hT, ← Real.rpow_add hT]
    ring_nf
  rw [hB4]
  calc T ^ (ε / 4) * ((Cη + 1) ^ (8 * M) * T ^ (ε / 4)) * Q ^ (4 * M) * T ^ (E₀ + ε / 4)
      ≤ T ^ (ε / 4) * ((Cη + 1) ^ (8 * M) * T ^ (ε / 4)) * T ^ (ε / 4) * T ^ (E₀ + ε / 4) := by
        gcongr
    _ = (Cη + 1) ^ (8 * M) * (T ^ (ε / 4) * T ^ (ε / 4) * T ^ (ε / 4) * T ^ (E₀ + ε / 4)) := by
        ring
    _ = (Cη + 1) ^ (8 * M) * T ^ (E₀ + ε) := by rw [hs]

end

end RHTower
