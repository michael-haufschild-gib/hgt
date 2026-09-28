import GaloisForLFunctions.RHTower.ZetaZeroClassPolynomialPower

/-!
# The two large-value counts for a raised class polynomial

For a class polynomial `P = dpoly (classCoeff …) B_j` on the block `B_j ⊆ [K, 2K)`, `K = 2^j`, and a
`1`-separated set `W ⊆ [T, 2T]` with `|P| ≥ V` on `W`, raise `P` to the power `ℓ ≥ 1`.  Its mass
is `G = (K^ℓ)^{-2σ} (2K)^ℓ (1 + log (2K)^ℓ)^{2^{4ℓ}-1}` for every `0 ≤ σ ≤ σ'`.

* **Mean value:** `#W·V^{2ℓ} ≤ (T + 1 + 4L(1 + log L))(1 + 2 log L)·G`, with `L = (2K)^ℓ`.
* **Huxley:** if `G(1 + 1536√(3L/4π)) ≤ (V^ℓ/ℓ)²/3`, then
  `#W·(V^ℓ/ℓ)² ≤ ℓ·(T(1284G)²/(V^ℓ/ℓ)⁴ + 1)·2G(L + 12πL(1 + log(T+1)))`.
-/

namespace RHTower

noncomputable section

open Complex Finset RHTower.Sieve

/-- The mass bound of the `ℓ`-th power of a class polynomial on the block `2^j`. -/
def classPowerMass (j ℓ : ℕ) (σ : ℝ) : ℝ :=
  (((2 ^ j : ℕ) : ℝ) ^ ℓ) ^ (-2 * σ) * (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)
    * (1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)) ^ (2 ^ (4 * ℓ) - 1)

theorem powSupport_class_subset_Icc {N y j ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    powSupport (detDyadicBlock N y j) ℓ ⊆ Icc 1 ((2 * 2 ^ j) ^ ℓ) := by
  intro n hn
  obtain ⟨h1, h2⟩ := powSupport_class_bounds hℓ n hn
  rw [mem_Icc]
  refine ⟨le_trans (Nat.one_le_pow _ _ (Nat.two_pow_pos j)) h1, ?_⟩
  rw [mul_pow, mul_comm]
  exact h2.le

/-- **The mean value count for a raised class polynomial.** -/
theorem card_mul_pow_le_class_mvt {N y j i ℓ : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) (hℓ : 1 ≤ ℓ)
    {σ σ' T V : ℝ} (hσ : 0 ≤ σ) (hσσ' : σ ≤ σ') (hT : 0 ≤ T) (hV : 0 ≤ V) {W : Finset ℝ}
    (hW : ∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|)
    (hbig : ∀ t ∈ W, V ≤
      ‖dpoly (classCoeff N y (Real.log (N * y : ℕ)) i σ') (detDyadicBlock N y j) t‖) :
    (W.card : ℝ) * (V ^ ℓ) ^ 2
      ≤ (T + 1 + 4 * (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) * (1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)))
          * (1 + 2 * Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)) * classPowerMass j ℓ σ := by
  have hL : 2 ≤ (2 * 2 ^ j) ^ ℓ := by
    calc 2 ≤ 2 * 2 ^ j := by have := Nat.one_le_two_pow (n := j); omega
      _ ≤ (2 * 2 ^ j) ^ ℓ := Nat.le_self_pow (by omega) _
  have hdiam : ∀ x ∈ W, ∀ y ∈ W, |x - y| ≤ T := by
    intro x hx y hy
    have h1 := hW x hx
    have h2 := hW y hy
    rw [abs_le]
    constructor <;> linarith
  have hbig' : ∀ t ∈ W, V ^ ℓ ≤ ‖dpoly (powConv (classCoeff N y (Real.log (N * y : ℕ)) i σ')
      (detDyadicBlock N y j) ℓ) (powSupport (detDyadicBlock N y j) ℓ) t‖ := by
    intro t ht
    rw [← norm_pow_class_eq]
    exact pow_le_pow_left₀ hV (hbig t ht) ℓ
  have h := card_mul_sq_le_of_dpoly_large_mvt hL (powSupport_class_subset_Icc hℓ) hT hsep hdiam
    hbig' (pow_nonneg hV ℓ)
  refine le_trans h ?_
  have hmass := sum_sq_powConv_class_le (j := j) (i := i) (ℓ := ℓ) hN hy hσ hσσ'
  have hpos : 0 ≤ (T + 1 + 4 * (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)
      * (1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)))
      * (1 + 2 * Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)) := by
    have hlog : 0 ≤ Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ (2 * 2 ^ j) ^ ℓ))
    positivity
  exact mul_le_mul_of_nonneg_left hmass hpos

/-- **The Huxley count for a raised class polynomial.** -/
theorem card_mul_pow_le_class_huxley {N y j i ℓ : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) (hℓ : 1 ≤ ℓ)
    {σ σ' T V : ℝ} (hσ : 0 ≤ σ) (hσσ' : σ ≤ σ') (hT : 0 ≤ T) (hV : 0 < V) {W : Finset ℝ}
    (hW : ∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|)
    (hbig : ∀ t ∈ W, V ≤
      ‖dpoly (classCoeff N y (Real.log (N * y : ℕ)) i σ') (detDyadicBlock N y j) t‖)
    (hthresh : classPowerMass j ℓ σ
        * (1 + 1536 * Real.sqrt (3 * (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) / (4 * Real.pi)))
      ≤ (V ^ ℓ / ℓ) ^ 2 / 3) :
    (W.card : ℝ) * (V ^ ℓ / ℓ) ^ 2
      ≤ ℓ * ((T * (1284 * classPowerMass j ℓ σ) ^ 2 / (V ^ ℓ / ℓ) ^ 4 + 1) *
          (2 * classPowerMass j ℓ σ * ((((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)
            + 12 * Real.pi * (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) * (1 + Real.log (T + 1))))) := by
  have hdiam : ∀ x ∈ W, ∀ y ∈ W, |x - y| ≤ T := by
    intro x hx y hy
    have h1 := hW x hx
    have h2 := hW y hy
    rw [abs_le]
    constructor <;> linarith
  have hbig' : ∀ t ∈ W, V ^ ℓ ≤ ‖dpoly (powConv (classCoeff N y (Real.log (N * y : ℕ)) i σ')
      (detDyadicBlock N y j) ℓ) (powSupport (detDyadicBlock N y j) ℓ) t‖ := by
    intro t ht
    rw [← norm_pow_class_eq]
    exact pow_le_pow_left₀ hV.le (hbig t ht) ℓ
  have hS : ∀ n ∈ powSupport (detDyadicBlock N y j) ℓ,
      (2 ^ j) ^ ℓ ≤ n ∧ n < (2 ^ j) ^ ℓ * 2 ^ ℓ := powSupport_class_bounds hℓ
  have hN₀ : ∀ r < ℓ, (((2 ^ j) ^ ℓ * 2 ^ r : ℕ) : ℝ) ≤ (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) := by
    intro r hr
    have : (2 ^ j) ^ ℓ * 2 ^ r ≤ (2 * 2 ^ j) ^ ℓ := by
      rw [mul_pow, mul_comm (2 ^ ℓ)]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hr.le)
    exact_mod_cast this
  have hmass := sum_sq_powConv_class_le (j := j) (i := i) (ℓ := ℓ) hN hy hσ hσσ'
  exact card_mul_sq_le_of_dpoly_large_huxley_range (Nat.one_le_pow _ _ (Nat.two_pow_pos j)) hℓ hS
    hT (pow_pos hV ℓ) hmass hN₀ hsep hdiam hbig' hthresh

end

end RHTower
