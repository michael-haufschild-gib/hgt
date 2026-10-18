import GaloisForLFunctions.BezoutValuationIncidence.CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget

/-!
# Arithmetic-Progression Harmonic Remainder Calculus and Shifted-Divisor First-Hit Bounds

This module advances **Step 1 (Shifted-Divisor Hyperbola & Progression Remainder Calculus)** of the
Wall 1 programme (`docs/reports/walls/bezout-wall1-programme.md`) from single-divisor harmonic sums
(`CompensatedHarmonicPredecessorPeakDriftAndDiagonalBudget.lean`) to **arithmetic progressions**
`n ≡ r (mod q)` and **coprime shifted-divisor pairs** `d₂ ∣ n ∧ d₁ ∣ (n + 1)`:

1. **Exact Two-Sided Sandwich for Arithmetic-Progression Harmonic Sums
   (`progressionHarmonicSum`, `progressionHarmonicSum_succ_bounds`,
   `abs_progressionHarmonicSum_succ_sub_harmonic_div_le`,
   `abs_progressionHarmonicSum_succ_sub_log_div_le`):**
   - For every modulus `q ≥ 1`, residue `1 ≤ r ≤ q`, and block count `K : ℕ`, define the
     arithmetic-progression harmonic sum
     $$\operatorname{progressionHarmonicSum}(q, r, K) = \sum_{k=0}^{K-1} \frac{1}{k q + r}.$$
   - Because `k q < k q + r ≤ (k + 1) q` for every `k ≥ 1`, separating the `k = 0` initial hit `1 / r`
     yields the unconditional two-sided sandwich
     $$0 \le \frac{1}{r} - \frac{1}{q}
       \le \operatorname{progressionHarmonicSum}(q, r, K + 1) - \frac{(\operatorname{harmonic}\,K : \mathbb{R})}{q}
       \le \frac{1}{r}.$$
   - Combining this with `|(harmonic K : ℝ) - log K| ≤ |eulerMascheroniConstant| + 1` gives the
     explicit logarithmic approximation for all `K ≥ 1`:
     $$\left|\operatorname{progressionHarmonicSum}(q, r, K + 1) - \frac{\log K}{q}\right|
       \le \frac{1}{r} + \frac{|\gamma| + 1}{q}.$$

2. **Bézout Shifted-Divisor First-Hit Lower Bound & Reciprocal Defect Suppression
   (`coprime_of_dvd_and_dvd_succ`, `max_le_succ_of_dvd_and_dvd_succ`,
   `mul_le_succ_sq_of_dvd_and_dvd_succ`, `inv_succ_le_min_of_dvd_and_dvd_succ`,
   `inv_succ_le_one_div_sqrt_mul`, `shifted_divisor_progressionHarmonicSum_defect_bounds`):**
   - Whenever `n ≥ 1` satisfies the shifted-divisor incidence `d₂ ∣ n` and `d₁ ∣ (n + 1)`:
     1. `Nat.Coprime d₁ d₂` holds unconditionally (since `Nat.Coprime n (n + 1)`),
     2. `max d₁ (d₂ + 1) ≤ n + 1` and `d₁ * d₂ ≤ (n + 1)²`,
     3. The reciprocal of `n + 1` satisfies the sharp suppression bound
        $$\frac{1}{n + 1} \le \min\left(\frac{1}{d_1},\, \frac{1}{d_2 + 1}\right) \le \frac{1}{\sqrt{d_1 d_2}}.$$
   - Consequently, for any coprime pair `(d₁, d₂)` whose initial positive hit `n₀ ≥ 1` satisfies
     `d₂ ∣ n₀`, `d₁ ∣ (n₀ + 1)`, and `n₀ + 1 ≤ d₁ * d₂`, the arithmetic-progression harmonic sum along
     `k * (d₁ * d₂) + (n₀ + 1)` differs from `(harmonic K : ℝ) / (d₁ * d₂)` by at most
     `min (1 / d₁) (1 / (d₂ + 1)) ≤ 1 / √(d₁ * d₂)`, eliminating `O(1)` starting-point defects
     whenever `max d₁ d₂` is large.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Two-Sided Sandwich for Arithmetic-Progression Harmonic Sums -/

/-- **Arithmetic-Progression Harmonic Sum (`progressionHarmonicSum`):**
For a modulus `q : ℕ`, residue offset `r : ℕ`, and block count `K : ℕ`, the sum of reciprocals
`1 / (k * q + r)` over `0 ≤ k < K`. -/
def progressionHarmonicSum (q r K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, 1 / ((k : ℝ) * (q : ℝ) + (r : ℝ))

@[simp]
theorem progressionHarmonicSum_zero (q r : ℕ) :
    progressionHarmonicSum q r 0 = 0 := by
  simp [progressionHarmonicSum]

@[simp]
theorem progressionHarmonicSum_one (q r : ℕ) :
    progressionHarmonicSum q r 1 = 1 / (r : ℝ) := by
  simp [progressionHarmonicSum]

theorem progressionHarmonicSum_succ (q r K : ℕ) :
    progressionHarmonicSum q r (K + 1) =
      progressionHarmonicSum q r K + 1 / ((K : ℝ) * (q : ℝ) + (r : ℝ)) := by
  unfold progressionHarmonicSum
  exact Finset.sum_range_succ _ K

/-- **Upper Bound on `progressionHarmonicSum q r (K + 1)`
(`progressionHarmonicSum_succ_le_inv_add_harmonic_div`):**
For every modulus `q ≥ 1`, positive offset `r ≥ 1`, and `K : ℕ`:
`progressionHarmonicSum q r (K + 1) ≤ 1 / r + (harmonic K : ℝ) / q`. -/
theorem progressionHarmonicSum_succ_le_inv_add_harmonic_div
    {q r : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r) (K : ℕ) :
    progressionHarmonicSum q r (K + 1) ≤
      1 / (r : ℝ) + (harmonic K : ℝ) / (q : ℝ) := by
  induction K with
  | zero =>
    simp [progressionHarmonicSum_one]
  | succ K ih =>
    rw [progressionHarmonicSum_succ, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
      add_div]
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hK1 : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
    have hstep :
        1 / (((K + 1 : ℕ) : ℝ) * (q : ℝ) + (r : ℝ)) ≤
          (((K + 1 : ℕ) : ℝ))⁻¹ / (q : ℝ) := by
      rw [← one_div ((K + 1 : ℕ) : ℝ), div_div]
      apply one_div_le_one_div_of_le (mul_pos hK1 hqR)
      linarith
    linarith

/-- **Sharp Lower Bound on `progressionHarmonicSum q r (K + 1)` via `harmonic (K + 1) - 1`
(`inv_add_harmonic_succ_sub_one_div_le_progressionHarmonicSum_succ`):**
For every modulus `q ≥ 1`, residue `1 ≤ r ≤ q`, and `K : ℕ`:
`1 / r + ((harmonic (K + 1) : ℝ) - 1) / q ≤ progressionHarmonicSum q r (K + 1)`. -/
theorem inv_add_harmonic_succ_sub_one_div_le_progressionHarmonicSum_succ
    {q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) (K : ℕ) :
    1 / (r : ℝ) + ((harmonic (K + 1) : ℝ) - 1) / (q : ℝ) ≤
      progressionHarmonicSum q r (K + 1) := by
  have hq : 1 ≤ q := hr.trans hrq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hrqR : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hrq
  induction K with
  | zero =>
    simp [progressionHarmonicSum_one]
  | succ K ih =>
    rw [progressionHarmonicSum_succ, harmonic_succ (K + 1), Rat.cast_add, Rat.cast_inv,
      Rat.cast_natCast]
    have hK2 : (0 : ℝ) < ((K + 1 + 1 : ℕ) : ℝ) := by positivity
    have hsplit :
        ((harmonic (K + 1) : ℝ) + (((K + 1 + 1 : ℕ) : ℝ))⁻¹ - 1) / (q : ℝ) =
          ((harmonic (K + 1) : ℝ) - 1) / (q : ℝ) +
            1 / (((K + 1 + 1 : ℕ) : ℝ) * (q : ℝ)) := by
      rw [← one_div ((K + 1 + 1 : ℕ) : ℝ), ← div_div]
      ring
    rw [hsplit]
    have hstep :
        1 / (((K + 1 + 1 : ℕ) : ℝ) * (q : ℝ)) ≤
          1 / (((K + 1 : ℕ) : ℝ) * (q : ℝ) + (r : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith
    linarith

/-- **Two-Sided Sandwich for `progressionHarmonicSum q r (K + 1)` Around `(harmonic K : ℝ) / q`
(`progressionHarmonicSum_succ_bounds`):**
For every modulus `q ≥ 1`, residue `1 ≤ r ≤ q`, and `K : ℕ`:
`0 ≤ 1 / r - 1 / q ≤ progressionHarmonicSum q r (K + 1) - (harmonic K : ℝ) / q ≤ 1 / r`. -/
theorem progressionHarmonicSum_succ_bounds
    {q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) (K : ℕ) :
    0 ≤ 1 / (r : ℝ) - 1 / (q : ℝ) ∧
      1 / (r : ℝ) - 1 / (q : ℝ) ≤
        progressionHarmonicSum q r (K + 1) - (harmonic K : ℝ) / (q : ℝ) ∧
      progressionHarmonicSum q r (K + 1) - (harmonic K : ℝ) / (q : ℝ) ≤
        1 / (r : ℝ) := by
  have hq : 1 ≤ q := hr.trans hrq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hrqR : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hrq
  have hnonneg : 0 ≤ 1 / (r : ℝ) - 1 / (q : ℝ) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le hrR hrqR)
  have hup := progressionHarmonicSum_succ_le_inv_add_harmonic_div hq hr K
  have hlow := inv_add_harmonic_succ_sub_one_div_le_progressionHarmonicSum_succ hr hrq K
  have hharm_le : (harmonic K : ℝ) ≤ (harmonic (K + 1) : ℝ) := by
    rw [harmonic_succ, Rat.cast_add]
    exact le_add_of_nonneg_right (by positivity)
  have hdiv_le :
      ((harmonic K : ℝ) - 1) / (q : ℝ) ≤ ((harmonic (K + 1) : ℝ) - 1) / (q : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hqR.le
  refine ⟨hnonneg, ?_, by linarith⟩
  have hrew :
      1 / (r : ℝ) + ((harmonic K : ℝ) - 1) / (q : ℝ) =
        1 / (r : ℝ) - 1 / (q : ℝ) + (harmonic K : ℝ) / (q : ℝ) := by ring
  linarith

/-- **Absolute Remainder Bound Against `(harmonic K : ℝ) / q`
(`abs_progressionHarmonicSum_succ_sub_harmonic_div_le`):**
For every modulus `q ≥ 1`, residue `1 ≤ r ≤ q`, and `K : ℕ`:
`|progressionHarmonicSum q r (K + 1) - (harmonic K : ℝ) / q| ≤ 1 / r`. -/
theorem abs_progressionHarmonicSum_succ_sub_harmonic_div_le
    {q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) (K : ℕ) :
    |progressionHarmonicSum q r (K + 1) - (harmonic K : ℝ) / (q : ℝ)| ≤ 1 / (r : ℝ) := by
  obtain ⟨h0, hlow, hup⟩ := progressionHarmonicSum_succ_bounds hr hrq K
  have hr0 : 0 ≤ 1 / (r : ℝ) := by positivity
  exact abs_le.mpr ⟨by linarith, hup⟩

/-- **Absolute Remainder Bound Against `1 / r + (harmonic K : ℝ) / q`
(`abs_progressionHarmonicSum_succ_sub_inv_add_harmonic_div_le`):**
For every modulus `q ≥ 1`, residue `1 ≤ r ≤ q`, and `K : ℕ`:
`|progressionHarmonicSum q r (K + 1) - (1 / r + (harmonic K : ℝ) / q)| ≤ 1 / q`. -/
theorem abs_progressionHarmonicSum_succ_sub_inv_add_harmonic_div_le
    {q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) (K : ℕ) :
    |progressionHarmonicSum q r (K + 1) -
      (1 / (r : ℝ) + (harmonic K : ℝ) / (q : ℝ))| ≤ 1 / (q : ℝ) := by
  obtain ⟨_, hlow, hup⟩ := progressionHarmonicSum_succ_bounds hr hrq K
  have hq0 : 0 ≤ 1 / (q : ℝ) := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Logarithmic Approximation for `progressionHarmonicSum q r (K + 1)`
(`abs_progressionHarmonicSum_succ_sub_log_div_le`):**
For every modulus `q ≥ 1`, residue `1 ≤ r ≤ q`, and positive block count `K ≥ 1`:
`|progressionHarmonicSum q r (K + 1) - log K / q| ≤ 1 / r + (|eulerMascheroniConstant| + 1) / q`. -/
theorem abs_progressionHarmonicSum_succ_sub_log_div_le
    {q r K : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q) (hK : 1 ≤ K) :
    |progressionHarmonicSum q r (K + 1) - Real.log (K : ℝ) / (q : ℝ)| ≤
      1 / (r : ℝ) + (|Real.eulerMascheroniConstant| + 1) / (q : ℝ) := by
  have hq : 1 ≤ q := hr.trans hrq
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have h1 := abs_progressionHarmonicSum_succ_sub_harmonic_div_le hr hrq K
  have hharm := HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hK
  have h1K : (1 : ℝ) / (K : ℝ) ≤ 1 :=
    div_le_self zero_le_one (by exact_mod_cast hK)
  have hlog : |(harmonic K : ℝ) - Real.log (K : ℝ)| ≤ |Real.eulerMascheroniConstant| + 1 := by
    have hsplit :
        (harmonic K : ℝ) - Real.log (K : ℝ) =
          ((harmonic K : ℝ) - Real.log (K : ℝ) - Real.eulerMascheroniConstant) +
            Real.eulerMascheroniConstant := by ring
    rw [hsplit]
    exact (abs_add_le _ _).trans (by linarith)
  have h2 :
      |(harmonic K : ℝ) / (q : ℝ) - Real.log (K : ℝ) / (q : ℝ)| ≤
        (|Real.eulerMascheroniConstant| + 1) / (q : ℝ) := by
    rw [← sub_div, abs_div, abs_of_nonneg hqR]
    exact div_le_div_of_nonneg_right hlog hqR
  have hsplit :
      progressionHarmonicSum q r (K + 1) - Real.log (K : ℝ) / (q : ℝ) =
        (progressionHarmonicSum q r (K + 1) - (harmonic K : ℝ) / (q : ℝ)) +
          ((harmonic K : ℝ) / (q : ℝ) - Real.log (K : ℝ) / (q : ℝ)) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-! ## §2. Bézout Shifted-Divisor First-Hit Lower Bound & Reciprocal Defect Suppression -/

/-- **Automatic Coprimality of Shifted Divisors (`coprime_of_dvd_and_dvd_succ`):**
If `d₂ ∣ n` and `d₁ ∣ (n + 1)`, then `Nat.Coprime d₁ d₂`. -/
theorem coprime_of_dvd_and_dvd_succ {d₁ d₂ n : ℕ}
    (hd₂ : d₂ ∣ n) (hd₁ : d₁ ∣ n + 1) :
    Nat.Coprime d₁ d₂ :=
  (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n)).symm.coprime_dvd_left hd₁
    |>.coprime_dvd_right hd₂

/-- **First-Hit Lower Bound for Shifted Divisors (`max_le_succ_of_dvd_and_dvd_succ`):**
Whenever `n ≥ 1` satisfies `d₂ ∣ n` and `d₁ ∣ (n + 1)`, we have `max d₁ (d₂ + 1) ≤ n + 1`. -/
theorem max_le_succ_of_dvd_and_dvd_succ {d₁ d₂ n : ℕ}
    (hn : 1 ≤ n) (hd₂ : d₂ ∣ n) (hd₁ : d₁ ∣ n + 1) :
    max d₁ (d₂ + 1) ≤ n + 1 := by
  have h1 : d₁ ≤ n + 1 := Nat.le_of_dvd (by omega) hd₁
  have h2 : d₂ ≤ n := Nat.le_of_dvd (by omega) hd₂
  exact max_le h1 (by omega)

/-- **Product-Square Bound at a Shifted-Divisor Hit (`mul_le_succ_sq_of_dvd_and_dvd_succ`):**
Whenever `n ≥ 1` satisfies `d₂ ∣ n` and `d₁ ∣ (n + 1)`, we have `d₁ * d₂ ≤ (n + 1) ^ 2`. -/
theorem mul_le_succ_sq_of_dvd_and_dvd_succ {d₁ d₂ n : ℕ}
    (hn : 1 ≤ n) (hd₂ : d₂ ∣ n) (hd₁ : d₁ ∣ n + 1) :
    d₁ * d₂ ≤ (n + 1) ^ (2 : ℕ) := by
  have hmax := max_le_succ_of_dvd_and_dvd_succ hn hd₂ hd₁
  have h1 : d₁ ≤ n + 1 := (le_max_left d₁ (d₂ + 1)).trans hmax
  have h2 : d₂ ≤ n + 1 := by
    have : d₂ + 1 ≤ n + 1 := (le_max_right d₁ (d₂ + 1)).trans hmax
    omega
  rw [sq]
  exact Nat.mul_le_mul h1 h2

/-- **Reciprocal Suppression at a Shifted-Divisor Hit (`inv_succ_le_min_of_dvd_and_dvd_succ`):**
Whenever `d₁ ≥ 1` and `n ≥ 1` satisfy `d₂ ∣ n` and `d₁ ∣ (n + 1)`:
`1 / (n + 1 : ℝ) ≤ min (1 / d₁) (1 / (d₂ + 1))`. -/
theorem inv_succ_le_min_of_dvd_and_dvd_succ {d₁ d₂ n : ℕ}
    (hd₁0 : 1 ≤ d₁) (hn : 1 ≤ n) (hd₂ : d₂ ∣ n) (hd₁ : d₁ ∣ n + 1) :
    1 / ((n + 1 : ℕ) : ℝ) ≤ min (1 / (d₁ : ℝ)) (1 / ((d₂ + 1 : ℕ) : ℝ)) := by
  have hmax := max_le_succ_of_dvd_and_dvd_succ hn hd₂ hd₁
  have h1 : (d₁ : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (le_max_left d₁ (d₂ + 1)).trans hmax
  have h2 : ((d₂ + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (le_max_right d₁ (d₂ + 1)).trans hmax
  refine le_min ?_ ?_
  · exact one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < d₁)) h1
  · exact one_div_le_one_div_of_le (by positivity) h2

/-- **Geometric-Mean Reciprocal Suppression (`inv_succ_le_one_div_sqrt_mul`):**
Whenever `n ≥ 1` satisfies `d₂ ∣ n` and `d₁ ∣ (n + 1)`:
`1 / (n + 1 : ℝ) ≤ 1 / √(d₁ * d₂)`. -/
theorem inv_succ_le_one_div_sqrt_mul {d₁ d₂ n : ℕ}
    (hn : 1 ≤ n) (hd₂ : d₂ ∣ n) (hd₁ : d₁ ∣ n + 1) :
    1 / ((n + 1 : ℕ) : ℝ) ≤ 1 / Real.sqrt ((d₁ : ℝ) * (d₂ : ℝ)) := by
  have hd₁0 : 0 < d₁ := Nat.pos_of_dvd_of_pos hd₁ (by omega)
  have hd₂0 : 0 < d₂ := Nat.pos_of_dvd_of_pos hd₂ (by omega)
  have hmul : (d₁ : ℝ) * (d₂ : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
    exact_mod_cast mul_le_succ_sq_of_dvd_and_dvd_succ hn hd₂ hd₁
  have hsqrt : Real.sqrt ((d₁ : ℝ) * (d₂ : ℝ)) ≤ ((n + 1 : ℕ) : ℝ) := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
    exact Real.sqrt_le_sqrt hmul
  exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) hsqrt

/-- **Shifted-Divisor Progression Harmonic Defect Bounds
(`shifted_divisor_progressionHarmonicSum_defect_bounds`):**
For any shifted-divisor pair `(d₁, d₂)` whose initial positive hit `n₀ ≥ 1` satisfies
`d₂ ∣ n₀`, `d₁ ∣ (n₀ + 1)`, and `n₀ + 1 ≤ d₁ * d₂`, the progression harmonic sum along
`k * (d₁ * d₂) + (n₀ + 1)` satisfies for every `K : ℕ`:
`0 ≤ progressionHarmonicSum (d₁ * d₂) (n₀ + 1) (K + 1) - (harmonic K : ℝ) / (d₁ * d₂) ≤ min (1 / d₁) (1 / (d₂ + 1))`. -/
theorem shifted_divisor_progressionHarmonicSum_defect_bounds
    {d₁ d₂ n₀ : ℕ} (hn₀ : 1 ≤ n₀) (hd₂ : d₂ ∣ n₀) (hd₁ : d₁ ∣ n₀ + 1)
    (hle : n₀ + 1 ≤ d₁ * d₂) (K : ℕ) :
    0 ≤ progressionHarmonicSum (d₁ * d₂) (n₀ + 1) (K + 1) -
        (harmonic K : ℝ) / ((d₁ * d₂ : ℕ) : ℝ) ∧
      progressionHarmonicSum (d₁ * d₂) (n₀ + 1) (K + 1) -
        (harmonic K : ℝ) / ((d₁ * d₂ : ℕ) : ℝ) ≤
        min (1 / (d₁ : ℝ)) (1 / ((d₂ + 1 : ℕ) : ℝ)) := by
  have hd₁0 : 1 ≤ d₁ := Nat.pos_of_dvd_of_pos hd₁ (by omega)
  obtain ⟨h0, hlow, hup⟩ :=
    progressionHarmonicSum_succ_bounds (by omega : 1 ≤ n₀ + 1) hle K
  have hmin := inv_succ_le_min_of_dvd_and_dvd_succ hd₁0 hn₀ hd₂ hd₁
  exact ⟨by linarith, hup.trans hmin⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
