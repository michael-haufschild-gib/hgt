import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheGaussianEnergyIsAFockNorm
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# The parabolic frequency is a chaos level

For a caloric transform `u` put `F(σ) = ∫ ‖u_{t₀+σ}(x + iy₀)‖² G_σ(x − x₀) dx` (`lineEnergy`),
`D(σ) = ∫ ‖∂u_{t₀+σ}(x + iy₀)‖² G_σ(x − x₀) dx` (`gradEnergy`) and `N(σ) = σ D(σ)/F(σ)` (`frequency`).
By the Fock identity, `F(σ) = Σ_n a_n σⁿ` with `a_n = 2ⁿ/n! ‖∂ⁿu_{t₀}(z₀)‖²`, and `2σ D(σ) = Σ_n n a_n σⁿ`
(`hasSum_two_mul_gradEnergy`). So `2N(σ)` is the mean Taylor degree of the measure `a_n σⁿ` on `ℕ`:

* **Monotonicity** (`frequency_le_frequency`, the Almgren–Poon theorem). Tilting an exponential family
  raises its mean; strictly unless the measure is a point mass (`frequency_lt_frequency`).
* **The order law** (`order_le_two_mul_frequency`). A zero of order `k` at `z₀` forces `N(σ) ≥ k/2` at every
  scale; a collision forces `N ≥ 1` (`one_le_frequency_of_collision`).
* **The limit** (`tendsto_frequency`). `N(σ) → k/2` as `σ → 0⁺`, with `k` the exact order.
* **Doubling** (`pow_mul_lineEnergy_le`). `F(λσ) ≥ λ^k F(σ)` for `λ ≥ 1`.

No size input enters, and every statement holds at every real time for every kernel of super-Gaussian
decay, including `H_{−τ}`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## Exponential families on `ℕ` -/

/-- Tilting a nonnegative measure on `ℕ` by `λⁿ`, `λ ≥ 1`, raises its mean degree. -/
theorem mean_le_mean_of_tilt {p : ℕ → ℝ} {l F₁ M₁ F₂ M₂ : ℝ} (hp : ∀ n, 0 ≤ p n) (hl : 1 ≤ l)
    (hF₁ : HasSum p F₁) (hM₁ : HasSum (fun n : ℕ => (n : ℝ) * p n) M₁)
    (hF₂ : HasSum (fun n => p n * l ^ n) F₂)
    (hM₂ : HasSum (fun n : ℕ => (n : ℝ) * (p n * l ^ n)) M₂) (hpos : 0 < F₁) :
    M₁ * F₂ ≤ M₂ * F₁ := by
  set m := M₁ / F₁ with hm
  have hl0 : 0 < l := by linarith
  have hzero : M₁ - m * F₁ = 0 := by rw [hm]; field_simp; ring
  have h1 := (hM₂.sub (hF₂.mul_left m))
  have h2 := ((hM₁.sub (hF₁.mul_left m)).mul_left (l ^ m))
  have hle := hasSum_le (fun n => ?_) h2 h1
  · rw [hzero, mul_zero] at hle
    have hF₁m : M₂ - m * F₂ = (M₂ * F₁ - M₁ * F₂) / F₁ := by rw [hm]; field_simp
    rw [hF₁m] at hle
    have := (div_nonneg_iff.mp hle).resolve_right (fun h => absurd hpos (not_lt.mpr h.2))
    linarith only [this.1]
  · have hsign : 0 ≤ ((n : ℝ) - m) * (l ^ n - l ^ m) := by
      rcases le_total (n : ℝ) m with h | h
      · have : l ^ n ≤ l ^ m := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hl h
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith only [h]) (by linarith only [this])
      · have : l ^ m ≤ l ^ n := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hl h
        exact mul_nonneg (by linarith only [h]) (by linarith only [this])
    have := mul_nonneg hsign (hp n)
    nlinarith only [this]

/-- The tilted mean is strictly larger as soon as two degrees carry mass. -/
theorem mean_lt_mean_of_tilt {p : ℕ → ℝ} {l F₁ M₁ F₂ M₂ : ℝ} (hp : ∀ n, 0 ≤ p n) (hl : 1 < l)
    (hF₁ : HasSum p F₁) (hM₁ : HasSum (fun n : ℕ => (n : ℝ) * p n) M₁)
    (hF₂ : HasSum (fun n => p n * l ^ n) F₂)
    (hM₂ : HasSum (fun n : ℕ => (n : ℝ) * (p n * l ^ n)) M₂) {i j : ℕ} (hij : i ≠ j)
    (hi : 0 < p i) (hj : 0 < p j) :
    M₁ * F₂ < M₂ * F₁ := by
  have hpos : 0 < F₁ := hi.trans_le (le_hasSum hF₁ i fun n _ => hp n)
  set m := M₁ / F₁ with hm
  have hl0 : 0 < l := by linarith
  have hzero : M₁ - m * F₁ = 0 := by rw [hm]; field_simp; ring
  have h1 := (hM₂.sub (hF₂.mul_left m))
  have h2 := ((hM₁.sub (hF₁.mul_left m)).mul_left (l ^ m))
  have hsign (n : ℕ) : 0 ≤ ((n : ℝ) - m) * (l ^ n - l ^ m) := by
    rcases le_total (n : ℝ) m with h | h
    · have : l ^ n ≤ l ^ m := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hl.le h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith only [h]) (by linarith only [this])
    · have : l ^ m ≤ l ^ n := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hl.le h
      exact mul_nonneg (by linarith only [h]) (by linarith only [this])
  -- one of the two degrees differs from the mean
  obtain ⟨k, hk, hkm⟩ : ∃ k, 0 < p k ∧ (k : ℝ) ≠ m := by
    by_cases hc : (i : ℝ) = m
    · refine ⟨j, hj, fun h => hij ?_⟩
      exact_mod_cast hc.trans h.symm
    · exact ⟨i, hi, hc⟩
  have hstrict : 0 < ((k : ℝ) - m) * (l ^ k - l ^ m) := by
    rcases lt_or_gt_of_ne hkm with h | h
    · have : l ^ k < l ^ m := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_lt_rpow_of_exponent_lt hl h
      exact mul_pos_of_neg_of_neg (by linarith only [h]) (by linarith only [this])
    · have : l ^ m < l ^ k := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_lt_rpow_of_exponent_lt hl h
      exact mul_pos (by linarith only [h]) (by linarith only [this])
  have hlt := hasSum_lt (i := k) (fun n => ?_) ?_ h2 h1
  · rw [hzero, mul_zero] at hlt
    have hF₁m : M₂ - m * F₂ = (M₂ * F₁ - M₁ * F₂) / F₁ := by rw [hm]; field_simp
    rw [hF₁m] at hlt
    have := (div_pos_iff.mp hlt).resolve_right (fun h => absurd hpos (not_lt.mpr h.2.le))
    linarith only [this.1]
  · have := mul_nonneg (hsign n) (hp n)
    nlinarith only [this]
  · have := mul_pos hstrict hk
    nlinarith only [this]

/-! ## The energies of a caloric transform -/

variable {g : ℝ → ℝ}

/-- The Fock coefficient `a_n = 2ⁿ/n! ‖∂ⁿf(z₀)‖²`. -/
def fockCoeff (f : ℂ → ℂ) (z₀ : ℂ) (n : ℕ) : ℝ :=
  2 ^ n / (n.factorial : ℝ) * ‖iteratedDeriv n f z₀‖ ^ 2

theorem fockCoeff_nonneg (f : ℂ → ℂ) (z₀ : ℂ) (n : ℕ) : 0 ≤ fockCoeff f z₀ n := by
  unfold fockCoeff
  positivity

theorem fockCoeff_pos_iff (f : ℂ → ℂ) (z₀ : ℂ) (n : ℕ) :
    0 < fockCoeff f z₀ n ↔ iteratedDeriv n f z₀ ≠ 0 := by
  unfold fockCoeff
  have h2 : (0 : ℝ) < 2 ^ n / (n.factorial : ℝ) := by positivity
  rw [mul_pos_iff_of_pos_left h2]
  simp [sq_pos_iff]

/-- The Gaussian energy of `u_{t₀+σ}` on the horizontal line through `z₀`. -/
def lineEnergy (g : ℝ → ℝ) (t₀ : ℝ) (z₀ : ℂ) (σ : ℝ) : ℝ :=
  ∫ x : ℝ, ‖caloric g (t₀ + σ) ((x : ℂ) + z₀.im * I)‖ ^ 2 * gaussDensity σ (x - z₀.re)

/-- The Gaussian energy of the derivative `∂u_{t₀+σ}` on the horizontal line through `z₀`. -/
def gradEnergy (g : ℝ → ℝ) (t₀ : ℝ) (z₀ : ℂ) (σ : ℝ) : ℝ :=
  ∫ x : ℝ, ‖deriv (caloric g (t₀ + σ)) ((x : ℂ) + z₀.im * I)‖ ^ 2 * gaussDensity σ (x - z₀.re)

/-- The parabolic frequency `N(σ) = σ D(σ)/F(σ)` at `(z₀, t₀)`. -/
def frequency (g : ℝ → ℝ) (t₀ : ℝ) (z₀ : ℂ) (σ : ℝ) : ℝ :=
  σ * gradEnergy g t₀ z₀ σ / lineEnergy g t₀ z₀ σ

/-- `F(σ) = Σ_n a_n σⁿ`. -/
theorem hasSum_lineEnergy (hg : SuperGaussian g) (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ) (z₀ : ℂ) :
    HasSum (fun n => fockCoeff (caloric g t₀) z₀ n * σ ^ n) (lineEnergy g t₀ z₀ σ) := by
  have h := hasSum_fock hg t₀ hσ z₀
  have hfun : (fun n : ℕ => (2 * σ) ^ n / (n.factorial : ℝ) *
      ‖iteratedDeriv n (caloric g t₀) z₀‖ ^ 2) =
      fun n => fockCoeff (caloric g t₀) z₀ n * σ ^ n := by
    funext n
    unfold fockCoeff
    rw [mul_pow]
    ring
  rw [hfun] at h
  exact h

/-- The derivative energy is the Fock norm of the shifted Taylor data. -/
theorem hasSum_gradEnergy (hg : SuperGaussian g) (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ) (z₀ : ℂ) :
    HasSum (fun n : ℕ => (2 * σ) ^ n / (n.factorial : ℝ) *
      ‖iteratedDeriv (n + 1) (caloric g t₀) z₀‖ ^ 2) (gradEnergy g t₀ z₀ σ) := by
  have h := hasSum_fock hg.mul_id t₀ hσ z₀
  have hint : gradEnergy g t₀ z₀ σ =
      ∫ x : ℝ, ‖caloric (fun y => y * g y) (t₀ + σ) ((x : ℂ) + z₀.im * I)‖ ^ 2 *
        gaussDensity σ (x - z₀.re) := by
    unfold gradEnergy
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [deriv_caloric hg, norm_mul, Complex.norm_I, one_mul]
  rw [hint]
  have hfun : (fun n : ℕ => (2 * σ) ^ n / (n.factorial : ℝ) *
      ‖iteratedDeriv (n + 1) (caloric g t₀) z₀‖ ^ 2) = fun n : ℕ => (2 * σ) ^ n /
        (n.factorial : ℝ) * ‖iteratedDeriv n (caloric (fun y => y * g y) t₀) z₀‖ ^ 2 := by
    funext n
    have hm : (∫ y : ℝ, ((g y * Real.exp (t₀ * y ^ 2) : ℝ) : ℂ) * Complex.exp (I * z₀ * y) *
          (y : ℂ) ^ (n + 1)) =
        ∫ y : ℝ, ((y * g y * Real.exp (t₀ * y ^ 2) : ℝ) : ℂ) * Complex.exp (I * z₀ * y) *
          (y : ℂ) ^ n := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      push_cast
      ring
    rw [norm_iteratedDeriv_caloric hg, norm_iteratedDeriv_caloric hg.mul_id, hm]
  rw [hfun]
  exact h

/-- `2σ D(σ) = Σ_n n a_n σⁿ`: the derivative energy is the mean degree. -/
theorem hasSum_two_mul_gradEnergy (hg : SuperGaussian g) (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ) (z₀ : ℂ) :
    HasSum (fun n : ℕ => (n : ℝ) * (fockCoeff (caloric g t₀) z₀ n * σ ^ n))
      (2 * σ * gradEnergy g t₀ z₀ σ) := by
  have h := (hasSum_gradEnergy hg t₀ hσ z₀).mul_left (2 * σ)
  have hfun : (fun n : ℕ => 2 * σ * ((2 * σ) ^ n / (n.factorial : ℝ) *
      ‖iteratedDeriv (n + 1) (caloric g t₀) z₀‖ ^ 2)) =
      fun n : ℕ => (((n + 1 : ℕ) : ℝ)) * (fockCoeff (caloric g t₀) z₀ (n + 1) * σ ^ (n + 1)) := by
    funext n
    unfold fockCoeff
    rw [Nat.factorial_succ, mul_pow]
    push_cast
    have hf : ((n.factorial : ℝ)) ≠ 0 := by positivity
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  rw [hfun] at h
  have h' := (hasSum_nat_add_iff (f := fun n : ℕ =>
    (n : ℝ) * (fockCoeff (caloric g t₀) z₀ n * σ ^ n)) 1).mp h
  simpa using h'

theorem lineEnergy_nonneg (g : ℝ → ℝ) (t₀ : ℝ) (z₀ : ℂ) {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ lineEnergy g t₀ z₀ σ :=
  integral_nonneg fun x => mul_nonneg (by positivity) (gaussDensity_pos hσ _).le

/-- Nonvanishing Taylor data make the energy positive at every scale. -/
theorem lineEnergy_pos (hg : SuperGaussian g) (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ) {z₀ : ℂ} {k : ℕ}
    (hk : iteratedDeriv k (caloric g t₀) z₀ ≠ 0) : 0 < lineEnergy g t₀ z₀ σ := by
  have h := hasSum_lineEnergy hg t₀ hσ z₀
  have hle := le_hasSum h k fun n _ => mul_nonneg (fockCoeff_nonneg _ _ _) (pow_pos hσ n).le
  exact (mul_pos ((fockCoeff_pos_iff _ _ _).mpr hk) (pow_pos hσ k)).trans_le hle

/-- An entire function that is not identically zero has nonzero Taylor data at every point. -/
theorem exists_iteratedDeriv_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {w : ℂ} (hw : f w ≠ 0)
    (z₀ : ℂ) : ∃ k, iteratedDeriv k f z₀ ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hw
  have h := Complex.taylorSeries_eq_of_entire' (c := z₀) (z := w) hf
  rw [← h]
  simp [hall]

/-- **Almgren–Poon monotonicity.** The frequency is nondecreasing in the scale. -/
theorem frequency_le_frequency (hg : SuperGaussian g) (t₀ : ℝ) {z₀ : ℂ} {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁)
    (hσ : σ₁ ≤ σ₂) (hF : 0 < lineEnergy g t₀ z₀ σ₁) :
    frequency g t₀ z₀ σ₁ ≤ frequency g t₀ z₀ σ₂ := by
  have hσ₂ : 0 < σ₂ := hσ₁.trans_le hσ
  have hl : 1 ≤ σ₂ / σ₁ := (one_le_div hσ₁).mpr hσ
  have htilt (n : ℕ) : fockCoeff (caloric g t₀) z₀ n * σ₁ ^ n * (σ₂ / σ₁) ^ n =
      fockCoeff (caloric g t₀) z₀ n * σ₂ ^ n := by
    rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ hσ₁.ne']
  have hF₂ := hasSum_lineEnergy hg t₀ hσ₂ z₀
  have hM₂ := hasSum_two_mul_gradEnergy hg t₀ hσ₂ z₀
  simp_rw [← htilt] at hF₂ hM₂
  have hmain := mean_le_mean_of_tilt (fun n => mul_nonneg (fockCoeff_nonneg _ _ _) (pow_pos hσ₁ n).le)
    hl (hasSum_lineEnergy hg t₀ hσ₁ z₀) (hasSum_two_mul_gradEnergy hg t₀ hσ₁ z₀) hF₂ hM₂ hF
  have hF₂pos : 0 < lineEnergy g t₀ z₀ σ₂ := by
    refine hF.trans_le (hasSum_le (fun n => ?_) (hasSum_lineEnergy hg t₀ hσ₁ z₀) hF₂)
    have h1 : 1 ≤ (σ₂ / σ₁) ^ n := one_le_pow₀ hl
    have h0 := mul_nonneg (fockCoeff_nonneg (caloric g t₀) z₀ n) (pow_pos hσ₁ n).le
    nlinarith only [mul_le_mul_of_nonneg_left h1 h0]
  unfold frequency
  rw [div_le_div_iff₀ hF hF₂pos]
  linarith only [hmain]

/-- The frequency is strictly increasing when two Taylor coefficients are nonzero. -/
theorem frequency_lt_frequency (hg : SuperGaussian g) (t₀ : ℝ) {z₀ : ℂ} {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁)
    (hσ : σ₁ < σ₂) {i j : ℕ} (hij : i ≠ j) (hi : iteratedDeriv i (caloric g t₀) z₀ ≠ 0)
    (hj : iteratedDeriv j (caloric g t₀) z₀ ≠ 0) :
    frequency g t₀ z₀ σ₁ < frequency g t₀ z₀ σ₂ := by
  have hσ₂ : 0 < σ₂ := hσ₁.trans hσ
  have hl : 1 < σ₂ / σ₁ := (one_lt_div hσ₁).mpr hσ
  have htilt (n : ℕ) : fockCoeff (caloric g t₀) z₀ n * σ₁ ^ n * (σ₂ / σ₁) ^ n =
      fockCoeff (caloric g t₀) z₀ n * σ₂ ^ n := by
    rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ hσ₁.ne']
  have hF₂ := hasSum_lineEnergy hg t₀ hσ₂ z₀
  have hM₂ := hasSum_two_mul_gradEnergy hg t₀ hσ₂ z₀
  simp_rw [← htilt] at hF₂ hM₂
  have hmain := mean_lt_mean_of_tilt (fun n => mul_nonneg (fockCoeff_nonneg _ _ _) (pow_pos hσ₁ n).le)
    hl (hasSum_lineEnergy hg t₀ hσ₁ z₀) (hasSum_two_mul_gradEnergy hg t₀ hσ₁ z₀) hF₂ hM₂ hij
    (mul_pos ((fockCoeff_pos_iff _ _ _).mpr hi) (pow_pos hσ₁ i))
    (mul_pos ((fockCoeff_pos_iff _ _ _).mpr hj) (pow_pos hσ₁ j))
  have hF := lineEnergy_pos hg t₀ hσ₁ hi
  have hF₂' := lineEnergy_pos hg t₀ hσ₂ hi
  unfold frequency
  rw [div_lt_div_iff₀ hF hF₂']
  linarith only [hmain]

/-- **Order law, energy form.** Vanishing Taylor data below order `k` give `k F(σ) ≤ 2σ D(σ)`. -/
theorem order_mul_lineEnergy_le (hg : SuperGaussian g) (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ) {z₀ : ℂ} {k : ℕ}
    (hvan : ∀ n < k, iteratedDeriv n (caloric g t₀) z₀ = 0) :
    (k : ℝ) * lineEnergy g t₀ z₀ σ ≤ 2 * σ * gradEnergy g t₀ z₀ σ := by
  refine hasSum_le (fun n => ?_) ((hasSum_lineEnergy hg t₀ hσ z₀).mul_left (k : ℝ))
    (hasSum_two_mul_gradEnergy hg t₀ hσ z₀)
  by_cases hn : n < k
  · have h0 : fockCoeff (caloric g t₀) z₀ n = 0 := by simp [fockCoeff, hvan n hn]
    simp [h0]
  · have hle : (k : ℝ) ≤ n := by exact_mod_cast not_lt.mp hn
    exact mul_le_mul_of_nonneg_right hle
      (mul_nonneg (fockCoeff_nonneg _ _ _) (pow_pos hσ n).le)

/-- **Order law.** A zero of order `≥ k` at `z₀` forces `N(σ) ≥ k/2` at every scale. -/
theorem order_le_two_mul_frequency (hg : SuperGaussian g) (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ) {z₀ : ℂ}
    {k : ℕ} (hvan : ∀ n < k, iteratedDeriv n (caloric g t₀) z₀ = 0)
    (hF : 0 < lineEnergy g t₀ z₀ σ) : (k : ℝ) ≤ 2 * frequency g t₀ z₀ σ := by
  have h := order_mul_lineEnergy_le hg t₀ hσ hvan
  unfold frequency
  rw [← mul_div_assoc, le_div_iff₀ hF]
  linarith only [h]

/-- A real or complex multiple zero forces `N(σ) ≥ 1` at every scale. -/
theorem one_le_frequency_of_multiple_zero (hg : SuperGaussian g) (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {z₀ : ℂ} (h0 : caloric g t₀ z₀ = 0) (h1 : deriv (caloric g t₀) z₀ = 0)
    (hF : 0 < lineEnergy g t₀ z₀ σ) : 1 ≤ frequency g t₀ z₀ σ := by
  have hvan : ∀ n < 2, iteratedDeriv n (caloric g t₀) z₀ = 0 := by
    intro n hn
    interval_cases n
    · simpa using h0
    · simpa [iteratedDeriv_one] using h1
  have h := order_le_two_mul_frequency hg t₀ hσ hvan hF
  norm_num at h
  linarith only [h]

/-- **A collision-free certificate.** `N(σ) < 1` at one scale excludes a multiple zero at `(z₀, t₀)`. -/
theorem not_multiple_zero_of_frequency_lt_one (hg : SuperGaussian g) (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ)
    {z₀ : ℂ} (hF : 0 < lineEnergy g t₀ z₀ σ) (hN : frequency g t₀ z₀ σ < 1) :
    ¬ (caloric g t₀ z₀ = 0 ∧ deriv (caloric g t₀) z₀ = 0) := fun h =>
  absurd (one_le_frequency_of_multiple_zero hg t₀ hσ h.1 h.2 hF) (not_le.mpr hN)

/-- **Doubling.** `F(lσ) ≥ l^k F(σ)` for `l ≥ 1` at a zero of order `≥ k`. -/
theorem pow_mul_lineEnergy_le (hg : SuperGaussian g) (t₀ : ℝ) {σ l : ℝ} (hσ : 0 < σ) (hl : 1 ≤ l)
    {z₀ : ℂ} {k : ℕ} (hvan : ∀ n < k, iteratedDeriv n (caloric g t₀) z₀ = 0) :
    l ^ k * lineEnergy g t₀ z₀ σ ≤ lineEnergy g t₀ z₀ (l * σ) := by
  have hlσ : 0 < l * σ := by positivity
  refine hasSum_le (fun n => ?_) ((hasSum_lineEnergy hg t₀ hσ z₀).mul_left (l ^ k))
    (hasSum_lineEnergy hg t₀ hlσ z₀)
  by_cases hn : n < k
  · have h0 : fockCoeff (caloric g t₀) z₀ n = 0 := by simp [fockCoeff, hvan n hn]
    simp [h0]
  · have hle : l ^ k ≤ l ^ n := pow_le_pow_right₀ hl (not_lt.mp hn)
    have h0 := mul_nonneg (fockCoeff_nonneg (caloric g t₀) z₀ n) (pow_pos hσ n).le
    calc l ^ k * (fockCoeff (caloric g t₀) z₀ n * σ ^ n)
        ≤ l ^ n * (fockCoeff (caloric g t₀) z₀ n * σ ^ n) := mul_le_mul_of_nonneg_right hle h0
      _ = _ := by rw [mul_pow]; ring

/-- **The limit at scale zero.** The frequency tends to half the exact order. -/
theorem tendsto_frequency (hg : SuperGaussian g) (t₀ : ℝ) {z₀ : ℂ} {k : ℕ}
    (hvan : ∀ n < k, iteratedDeriv n (caloric g t₀) z₀ = 0)
    (hk : iteratedDeriv k (caloric g t₀) z₀ ≠ 0) :
    Tendsto (frequency g t₀ z₀) (𝓝[>] 0) (𝓝 ((k : ℝ) / 2)) := by
  set a := fockCoeff (caloric g t₀) z₀ with ha
  have hak : 0 < a k := (fockCoeff_pos_iff _ _ _).mpr hk
  have han (n : ℕ) : 0 ≤ a n := fockCoeff_nonneg _ _ _
  have hzero (n : ℕ) (hn : n < k) : a n = 0 := by simp [ha, fockCoeff, hvan n hn]
  have hF1 := hasSum_lineEnergy hg t₀ one_pos z₀
  have hM1 := hasSum_two_mul_gradEnergy hg t₀ one_pos z₀
  simp only [one_pow, mul_one] at hF1 hM1
  -- the excess at scale one
  set C := 2 * gradEnergy g t₀ z₀ 1 - (k : ℝ) * lineEnergy g t₀ z₀ 1 with hC
  have hexcess := hM1.sub (hF1.mul_left (k : ℝ))
  have hbound : ∀ σ : ℝ, 0 < σ → σ ≤ 1 → frequency g t₀ z₀ σ ≤ (k : ℝ) / 2 + σ * C / (2 * a k) := by
    intro σ hσ hσ1
    have hF := hasSum_lineEnergy hg t₀ hσ z₀
    have hM := hasSum_two_mul_gradEnergy hg t₀ hσ z₀
    have hFpos := lineEnergy_pos hg t₀ hσ hk
    have hFlow : a k * σ ^ k ≤ lineEnergy g t₀ z₀ σ :=
      le_hasSum hF k fun n _ => mul_nonneg (han n) (pow_pos hσ n).le
    have hterm : 2 * σ * gradEnergy g t₀ z₀ σ - (k : ℝ) * lineEnergy g t₀ z₀ σ ≤ σ ^ (k + 1) * C := by
      refine hasSum_le (fun n => ?_) (hM.sub (hF.mul_left (k : ℝ))) (hexcess.mul_left (σ ^ (k + 1)))
      rcases lt_trichotomy n k with hn | hn | hn
      · have h0 : fockCoeff (caloric g t₀) z₀ n = 0 := hzero n hn
        simp [h0]
      · simp [hn]
      · have hpow : σ ^ n ≤ σ ^ (k + 1) := pow_le_pow_of_le_one hσ.le hσ1 hn
        have hnk : (0 : ℝ) ≤ (n : ℝ) - k := by
          have : (k : ℝ) ≤ n := by exact_mod_cast hn.le
          linarith only [this]
        have h1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hnk (han n))
        simp only [← ha]
        nlinarith only [h1]
    have hCn : 0 ≤ C := by
      have := order_mul_lineEnergy_le hg t₀ one_pos hvan
      rw [hC]
      linarith only [this]
    unfold frequency
    rw [div_le_iff₀ hFpos]
    have hcoef : (k : ℝ) / 2 + σ * C / (2 * a k) = ((k : ℝ) * a k + σ * C) / (2 * a k) := by
      field_simp
    have hstep : σ ^ (k + 1) * C ≤ σ * C / a k * lineEnergy g t₀ z₀ σ := by
      have h2 : σ * C / a k * (a k * σ ^ k) ≤ σ * C / a k * lineEnergy g t₀ z₀ σ :=
        mul_le_mul_of_nonneg_left hFlow (by positivity)
      have h3 : σ * C / a k * (a k * σ ^ k) = σ ^ (k + 1) * C := by
        field_simp
        ring
      linarith only [h2, h3]
    have hfin : σ * gradEnergy g t₀ z₀ σ ≤
        ((k : ℝ) / 2 + σ * C / (2 * a k)) * lineEnergy g t₀ z₀ σ := by
      have h4 : (k : ℝ) / 2 + σ * C / (2 * a k) = (k : ℝ) / 2 + (σ * C / a k) / 2 := by
        field_simp
      rw [h4]
      nlinarith only [hterm, hstep]
    exact hfin
  have hupper : Tendsto (fun σ : ℝ => (k : ℝ) / 2 + σ * C / (2 * a k)) (𝓝[>] 0) (𝓝 ((k : ℝ) / 2)) := by
    have hc : Continuous (fun σ : ℝ => (k : ℝ) / 2 + σ * C / (2 * a k)) := by fun_prop
    have := hc.tendsto 0
    simp only [zero_mul, zero_div, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have := order_le_two_mul_frequency hg t₀ hσ hvan (lineEnergy_pos hg t₀ hσ hk)
    linarith only [this]
  · filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with σ hσ
    exact hbound σ hσ.1 hσ.2

/-! ## The actual source -/

/-- The Riemann kernel has super-Gaussian decay. -/
theorem riemannKernel_superGaussian : SuperGaussian riemannKernelReal := by
  refine ⟨continuous_riemannKernelReal, fun c => ?_⟩
  have hc : 0 ≤ max c 0 := le_max_right _ _
  have h := (riemannKernel_superExp.mul_exp_sq hc).integrable_mul_exp 0
  refine h.mono' ((continuous_riemannKernelReal.abs.mul (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  have hpos := riemannKernelReal_pos x
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le),
    abs_of_pos hpos, zero_mul, Real.exp_zero, mul_one]
  have : c * x ^ 2 ≤ max c 0 * x ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg x)
  gcongr

/-- `H_t` is the caloric transform of the Riemann kernel, at every real time. -/
theorem caloric_riemannKernel (t : ℝ) : caloric riemannKernelReal t = riemannHeat t := by
  funext z
  rfl

/-- **The order law for `H_t`.** At every real time `t₀`, every complex point `z₀` and every scale, the order
of the zero of `H_{t₀}` at `z₀` is at most twice the frequency, read at the later time `t₀ + σ` on the
horizontal line through `z₀`. For `t₀ < 0` this is the same law at a time where `H_{t₀}` collides. -/
theorem order_le_two_mul_frequency_riemannHeat (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ) {z₀ : ℂ} {k : ℕ}
    (hvan : ∀ n < k, iteratedDeriv n (riemannHeat t₀) z₀ = 0)
    (hk : iteratedDeriv k (riemannHeat t₀) z₀ ≠ 0) :
    (k : ℝ) ≤ 2 * frequency riemannKernelReal t₀ z₀ σ := by
  rw [← caloric_riemannKernel] at hvan hk
  exact order_le_two_mul_frequency riemannKernel_superGaussian t₀ hσ hvan
    (lineEnergy_pos riemannKernel_superGaussian t₀ hσ hk)

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
