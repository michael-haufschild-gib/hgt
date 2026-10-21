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

The last part collects the power comparisons `X ↦ X^e` used with these exponents.
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

end

end RHTower
