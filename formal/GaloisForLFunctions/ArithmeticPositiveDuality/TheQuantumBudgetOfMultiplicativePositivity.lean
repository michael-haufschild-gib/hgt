import GaloisForLFunctions.MultiplicativePositivityGeometry.GrowthToForcing

/-!
# The quantum budget of multiplicative positivity

The only forcing step in the corpus is quantization: an integer below its first nonzero value is
zero. In de la Vallée Poussin's coupling a zero of order `m` at distance `η` from `Re s = 1`
enters as `m B/(δ + η)` against the pole `A/δ` and the growth `G`. This module computes exactly
which orders the coupling admits.

* **The quantum budget** (`admissible_iff_le_quantumBudget`). The order `m` survives every
  damping `δ > 0` iff `m ≤ b(η) = (√A + √(Gη))²/B`. The budget is the exact constant of the
  growth-to-forcing law read as a bound on an integer.
* **Quantization** (`forces_zero_iff_quantumBudget_lt_one`). The coupling forces every admissible
  order to vanish iff `b(η) < 1`; for invariants known to be even, iff `b(η) < 2`
  (`forces_even_zero_iff_quantumBudget_lt_two`).
* **The boundary** (`quantumBudget_zero`). At `η = 0` the budget is `A/B`, the reciprocal purchase
  ratio; with the Fejér barrier `B ≤ 2cos(π/(K+2)) A` it lies in `(1/2, 1]`, so the boundary
  quantum is purchased exactly when `B > A`.
* **The critical line** (`one_le_quantumBudget_half`, `two_le_quantumBudget_half`). With growth
  `L·W`, `W ≥ B`, the budget at `η = ½` is at least `(√(A/B) + √(L/2))²`. It exceeds the first
  quantum once `L ≥ 2`, and the first even quantum once `L ≥ 8`; with the Fejér barrier already at
  `L ≥ 2(1 − 2^{−1/2})²` and `L ≥ 1` respectively.

So the integer that plays the pole's role on `Re s = 1` is the zero order, with budget `A/B < 1`;
at the critical line multiplicative positivity has no budget below the first quantum at any
height scale where the archimedean growth is at least one. The quantized inequality the field needs
in the strip must come from an object outside multiplicative positivity.
-/

open Real

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open MultiplicativePositivityGeometry

/-- The quantum budget `b(η) = (√A + √(Gη))²/B` of the coupling at distance `η`. -/
noncomputable def quantumBudget (A B G η : ℝ) : ℝ := (Real.sqrt A + Real.sqrt (G * η)) ^ 2 / B

/-- An order `m` is admissible at distance `η` when `m B/(δ+η) ≤ A/δ + G` for every damping. -/
def Admissible (A B G η : ℝ) (m : ℕ) : Prop := ∀ δ > 0, (m : ℝ) * B / (δ + η) ≤ A / δ + G

/-- **The quantum budget.** The admissible orders are exactly `m ≤ (√A + √(Gη))²/B`. -/
theorem admissible_iff_le_quantumBudget {A B G η : ℝ} (hA : 0 < A) (hB : 0 < B) (hG : 0 < G)
    (hη : 0 < η) (m : ℕ) : Admissible A B G η m ↔ (m : ℝ) ≤ quantumBudget A B G η := by
  have hmB : 0 ≤ (m : ℝ) * B := by positivity
  have h := exclusion_iff hA hmB hG hη
  have hs : 0 ≤ Real.sqrt A + Real.sqrt (G * η) := by positivity
  unfold Admissible quantumBudget
  rw [le_div_iff₀ hB]
  constructor
  · intro hadm
    have hn : ¬ (Real.sqrt A + Real.sqrt (G * η) < Real.sqrt ((m : ℝ) * B)) := by
      rw [← h]
      rintro ⟨δ, hδ, hlt⟩
      exact absurd (hadm δ hδ) (not_le.mpr hlt)
    push Not at hn
    calc (m : ℝ) * B = Real.sqrt ((m : ℝ) * B) ^ 2 := (Real.sq_sqrt hmB).symm
      _ ≤ (Real.sqrt A + Real.sqrt (G * η)) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hn 2
  · intro hle δ hδ
    by_contra hlt
    push Not at hlt
    have := h.mp ⟨δ, hδ, hlt⟩
    have h2 : (Real.sqrt A + Real.sqrt (G * η)) ^ 2 < Real.sqrt ((m : ℝ) * B) ^ 2 :=
      pow_lt_pow_left₀ this hs (by norm_num)
    rw [Real.sq_sqrt hmB] at h2
    linarith

/-- **Quantization.** The coupling forces every admissible order to vanish iff the budget is
below the first quantum. -/
theorem forces_zero_iff_quantumBudget_lt_one {A B G η : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hG : 0 < G) (hη : 0 < η) :
    (∀ m : ℕ, Admissible A B G η m → m = 0) ↔ quantumBudget A B G η < 1 := by
  simp_rw [admissible_iff_le_quantumBudget hA hB hG hη]
  constructor
  · intro h
    by_contra hge
    push Not at hge
    exact one_ne_zero (h 1 (by exact_mod_cast hge))
  · intro hlt m hm
    have : (m : ℝ) < 1 := lt_of_le_of_lt hm hlt
    exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)

/-- **Parity doubles the quantum.** For an even invariant the coupling forces vanishing iff the
budget is below two. -/
theorem forces_even_zero_iff_quantumBudget_lt_two {A B G η : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hG : 0 < G) (hη : 0 < η) :
    (∀ m : ℕ, Even m → Admissible A B G η m → m = 0) ↔ quantumBudget A B G η < 2 := by
  simp_rw [admissible_iff_le_quantumBudget hA hB hG hη]
  constructor
  · intro h
    by_contra hge
    push Not at hge
    exact two_ne_zero (h 2 even_two (by exact_mod_cast hge))
  · intro hlt m hm hle
    obtain ⟨k, rfl⟩ := hm
    have : ((k + k : ℕ) : ℝ) < 2 := lt_of_le_of_lt hle hlt
    push_cast at this
    have hk : k = 0 := by
      have : (k : ℝ) < 1 := by linarith
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    rw [hk]

/-- At the boundary the budget is the reciprocal purchase ratio `A/B`. -/
theorem quantumBudget_zero (A B G : ℝ) (hA : 0 ≤ A) : quantumBudget A B G 0 = A / B := by
  simp [quantumBudget, Real.sq_sqrt hA]

/-- With the Fejér barrier the boundary budget lies in `[1/(2cos(π/(K+2))), …)`, above `1/2`. -/
theorem half_lt_quantumBudget_zero {a : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ) (ha0 : 0 < a 0) (ha1 : 0 < a 1) (G : ℝ) :
    1 / 2 < quantumBudget (a 0) (a 1) G 0 := by
  rw [quantumBudget_zero _ _ _ ha0.le, lt_div_iff₀ ha1]
  have h1 := cosinePolynomial_first_le_fejer hK hP
  have h2 := (fejer_ratio_mem hK).2
  nlinarith

/-- The budget at the critical line in the growth model `G = L·W`, `W ≥ B`. -/
theorem quantumBudget_half_ge {A B W L : ℝ} (hA : 0 < A) (hB : 0 < B) (hW : B ≤ W) (hL : 0 < L) :
    (Real.sqrt (A / B) + Real.sqrt (L / 2)) ^ 2 ≤ quantumBudget A B (L * W) (1 / 2) := by
  unfold quantumBudget
  rw [le_div_iff₀ hB]
  have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB.le
  have e1 : Real.sqrt (A / B) * Real.sqrt B = Real.sqrt A := by
    rw [← Real.sqrt_mul (div_nonneg hA.le hB.le), div_mul_cancel₀ _ hB.ne']
  have e2 : Real.sqrt (L / 2) * Real.sqrt B ≤ Real.sqrt (L * W * (1 / 2)) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have key : (Real.sqrt (A / B) + Real.sqrt (L / 2)) * Real.sqrt B ≤
      Real.sqrt A + Real.sqrt (L * W * (1 / 2)) := by nlinarith
  have hpos : 0 ≤ (Real.sqrt (A / B) + Real.sqrt (L / 2)) * Real.sqrt B := by positivity
  have := pow_le_pow_left₀ hpos key 2
  rw [mul_pow, hsB] at this
  exact this

/-- **No first quantum at the critical line** once the height scale is at least two. -/
theorem one_le_quantumBudget_half {A B W L : ℝ} (hA : 0 < A) (hB : 0 < B) (hW : B ≤ W)
    (hL : 2 ≤ L) : 1 ≤ quantumBudget A B (L * W) (1 / 2) := by
  refine le_trans ?_ (quantumBudget_half_ge hA hB hW (by linarith))
  have h1 : 1 ≤ Real.sqrt (L / 2) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
  have h0 : 0 ≤ Real.sqrt (A / B) := Real.sqrt_nonneg _
  nlinarith

/-- **No first even quantum at the critical line** once the height scale is at least eight. -/
theorem two_le_quantumBudget_half {A B W L : ℝ} (hA : 0 < A) (hB : 0 < B) (hW : B ≤ W)
    (hL : 8 ≤ L) : 2 ≤ quantumBudget A B (L * W) (1 / 2) := by
  refine le_trans ?_ (quantumBudget_half_ge hA hB hW (by linarith))
  have h1 : 2 ≤ Real.sqrt (L / 2) := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have h0 : 0 ≤ Real.sqrt (A / B) := Real.sqrt_nonneg _
  nlinarith

/-- **With the Fejér barrier**, the critical-line budget of a nonnegative cosine certificate is
at least one once `L ≥ 2(1 − 2^{−1/2})²`, and at least two once `L ≥ 1`. -/
theorem fejer_quantumBudget_half {a : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ) (ha0 : 0 < a 0) (ha1 : 0 < a 1)
    {W L : ℝ} (hW : a 1 ≤ W) :
    (2 * (1 - 1 / Real.sqrt 2) ^ 2 ≤ L → 1 ≤ quantumBudget (a 0) (a 1) (L * W) (1 / 2)) ∧
      (1 ≤ L → 2 ≤ quantumBudget (a 0) (a 1) (L * W) (1 / 2)) := by
  have hρ := cosinePolynomial_first_le_fejer hK hP
  have hρ2 := (fejer_ratio_mem hK).2
  have hratio : 1 / 2 < a 0 / a 1 := by
    rw [lt_div_iff₀ ha1]; nlinarith
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : 1 / Real.sqrt 2 ≤ Real.sqrt (a 0 / a 1) := by
    rw [div_le_iff₀ hs2, ← Real.sqrt_mul (by positivity)]
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hinv : 0 < 1 / Real.sqrt 2 := by positivity
  have hlt1 : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one hs2]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt 2 := (Real.sqrt_lt_sqrt_iff (by norm_num)).mpr (by norm_num)
  constructor
  · intro hL
    have hLpos : 0 < L := lt_of_lt_of_le (by
      have : 0 < 1 - 1 / Real.sqrt 2 := by linarith
      positivity) hL
    refine le_trans ?_ (quantumBudget_half_ge ha0 ha1 hW hLpos)
    have hL2 : 1 - 1 / Real.sqrt 2 ≤ Real.sqrt (L / 2) := by
      rw [show 1 - 1 / Real.sqrt 2 = Real.sqrt ((1 - 1 / Real.sqrt 2) ^ 2) by
        rw [Real.sqrt_sq (by linarith)]]
      exact Real.sqrt_le_sqrt (by linarith)
    nlinarith
  · intro hL
    refine le_trans ?_ (quantumBudget_half_ge ha0 ha1 hW (by linarith))
    have hL2 : 1 / Real.sqrt 2 ≤ Real.sqrt (L / 2) := by
      rw [show 1 / Real.sqrt 2 = Real.sqrt (1 / 2) by
        rw [Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (by linarith)
    have : Real.sqrt 2 ≤ Real.sqrt (a 0 / a 1) + Real.sqrt (L / 2) := by
      have e : Real.sqrt 2 = 1 / Real.sqrt 2 + 1 / Real.sqrt 2 := by
        field_simp
        rw [hsq2]
      linarith
    have h0 : 0 ≤ Real.sqrt 2 := hs2.le
    nlinarith

end GaloisForLFunctions.ArithmeticPositiveDuality
