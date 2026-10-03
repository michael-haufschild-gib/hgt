import GaloisForLFunctions.RHTower.ZetaZeroClassLargeValueCounts

/-!
# Large-value counts for a raised Taylor class polynomial on any dyadic block

The two counts of `ZetaZeroClassLargeValueCounts` use only three properties of the detection
block: it lies in `[2^j, 2^{j+1})`, its logarithms are at most `Λ`, and its coefficients are bounded
by the divisor function.  Here they are stated for an arbitrary finite block `B` and real
coefficients `c`, with the class coefficient `c(k) (log k/Λ)^i k^{-σ'}`, so that any zero detector
with divisor-bounded coefficients can feed them.

* **Mean value:** `#W·V^{2ℓ} ≤ (T + 1 + 4L(1 + log L))(1 + 2 log L)·G`, `L = (2·2^j)^ℓ`.
* **Huxley:** if `G(1 + 1536√(3L/4π)) ≤ (V^ℓ/ℓ)²/3`, then
  `#W·(V^ℓ/ℓ)² ≤ ℓ·(T(1284G)²/(V^ℓ/ℓ)⁴ + 1)·2G(L + 12πL(1 + log(T+1)))`,

where `G = classPowerMass j ℓ σ` is the mass of the `ℓ`-th power.
-/

namespace RHTower

noncomputable section

open Complex Finset RHTower.Sieve

/-- The class coefficients `c(k) (log k/Λ)^i k^{-σ'}` of a block with real coefficients `c`. -/
def genClassCoeff (c : ℕ → ℝ) (Λ : ℝ) (i : ℕ) (σ' : ℝ) : ℕ → ℝ :=
  fun k => c k * (Real.log k / Λ) ^ i * (k : ℝ) ^ (-σ')

/-- The Taylor class polynomial of a block with real coefficients is a real Dirichlet polynomial. -/
theorem abscissaTaylorPoly_ofReal_eq_dpoly {B : Finset ℕ} (hB : ∀ k ∈ B, 1 ≤ k) (c : ℕ → ℝ)
    (Λ : ℝ) (i : ℕ) (σ' t : ℝ) :
    abscissaTaylorPoly B (fun k => ((c k : ℝ) : ℂ)) Λ i σ' t =
      dpoly (genClassCoeff c Λ i σ') B t := by
  unfold abscissaTaylorPoly dpoly
  refine sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := hB k hk
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hcpow : (k : ℂ) ^ (-((σ' : ℂ) + (t : ℂ) * I))
      = (((k : ℝ) ^ (-σ') : ℝ) : ℂ) * Complex.exp (-(t : ℂ) * I * (Real.log k : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hk0,
      show Complex.log (k : ℂ) = (Real.log k : ℂ) by
        rw [← Complex.ofReal_natCast, Complex.ofReal_log hkR.le],
      Real.rpow_def_of_pos hkR, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [cterm, genClassCoeff, hcpow]
  push_cast
  ring

/-- The class coefficients are bounded by `k^{-σ} d(k)` for `σ ≤ σ'`. -/
theorem abs_genClassCoeff_le {c : ℕ → ℝ} {Λ : ℝ} {i : ℕ} {σ σ' : ℝ} (hσσ' : σ ≤ σ') {k : ℕ}
    (hk1 : 1 ≤ k) (hkΛ : Real.log k ≤ Λ) (hc : |c k| ≤ k.divisors.card) :
    |genClassCoeff c Λ i σ' k| ≤ (k : ℝ) ^ (-σ) * k.divisors.card := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hkR
  have hw : |(Real.log k / Λ) ^ i| ≤ 1 := by
    rw [abs_pow]
    refine pow_le_one₀ (abs_nonneg _) ?_
    rcases eq_or_lt_of_le (le_trans hlog0 hkΛ) with h | h
    · rw [← h, div_zero, abs_zero]
      norm_num
    · rw [abs_div, abs_of_nonneg hlog0, abs_of_pos h, div_le_one h]
      exact hkΛ
  have hpow : (k : ℝ) ^ (-σ') ≤ (k : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hkR (by linarith)
  unfold genClassCoeff
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  calc |c k| * |(Real.log k / Λ) ^ i| * (k : ℝ) ^ (-σ')
      ≤ (k.divisors.card : ℝ) * 1 * (k : ℝ) ^ (-σ) := by
        gcongr
    _ = (k : ℝ) ^ (-σ) * k.divisors.card := by ring

theorem powSupport_block_bounds {B : Finset ℕ} {j ℓ : ℕ}
    (hB : ∀ k ∈ B, 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1) (hℓ : 1 ≤ ℓ) :
    ∀ n ∈ powSupport B ℓ, (2 ^ j) ^ ℓ ≤ n ∧ n < (2 ^ j) ^ ℓ * 2 ^ ℓ := by
  intro n hn
  obtain ⟨h1, h2⟩ := mem_powSupport_bounds hB ℓ n hn
  refine ⟨h1, lt_of_le_of_lt h2 ?_⟩
  calc (2 * 2 ^ j - 1) ^ ℓ < (2 * 2 ^ j) ^ ℓ :=
        Nat.pow_lt_pow_left (by have := Nat.one_le_two_pow (n := j); omega) (by omega)
    _ = (2 ^ j) ^ ℓ * 2 ^ ℓ := by rw [mul_pow, mul_comm]

theorem powSupport_block_subset_Icc {B : Finset ℕ} {j ℓ : ℕ}
    (hB : ∀ k ∈ B, 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1) (hℓ : 1 ≤ ℓ) :
    powSupport B ℓ ⊆ Icc 1 ((2 * 2 ^ j) ^ ℓ) := by
  intro n hn
  obtain ⟨h1, h2⟩ := powSupport_block_bounds hB hℓ n hn
  rw [mem_Icc]
  refine ⟨le_trans (Nat.one_le_pow _ _ (Nat.two_pow_pos j)) h1, ?_⟩
  rw [mul_pow, mul_comm]
  exact h2.le

theorem norm_pow_genClass_eq {B : Finset ℕ} (hB1 : ∀ k ∈ B, 1 ≤ k) {c : ℕ → ℝ} {Λ : ℝ}
    {i ℓ : ℕ} {σ' t : ℝ} :
    ‖dpoly (genClassCoeff c Λ i σ') B t‖ ^ ℓ
      = ‖dpoly (powConv (genClassCoeff c Λ i σ') B ℓ) (powSupport B ℓ) t‖ := by
  rw [← norm_pow, dpoly_pow (genClassCoeff c Λ i σ') B hB1 t ℓ]

theorem sum_sq_powConv_genClass_le {B : Finset ℕ} {c : ℕ → ℝ} {Λ : ℝ} {j i ℓ : ℕ}
    (hB : ∀ k ∈ B, 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1) (hBΛ : ∀ k ∈ B, Real.log k ≤ Λ)
    (hc : ∀ k ∈ B, |c k| ≤ k.divisors.card) {σ σ' : ℝ} (hσ : 0 ≤ σ) (hσσ' : σ ≤ σ') :
    ∑ n ∈ powSupport B ℓ, (powConv (genClassCoeff c Λ i σ') B ℓ n) ^ 2
      ≤ classPowerMass j ℓ σ := by
  have h := sum_sq_powConv_le (a := genClassCoeff c Λ i σ') (s := B) (ℓ := ℓ) hσ
    (Nat.one_le_two_pow) hB
    (fun k hk => abs_genClassCoeff_le hσσ'
      (le_trans Nat.one_le_two_pow (hB k hk).1) (hBΛ k hk) (hc k hk))
  unfold classPowerMass
  exact_mod_cast h

/-- **The mean value count for a raised class polynomial on any block.** -/
theorem card_mul_pow_le_genClass_mvt {B : Finset ℕ} {c : ℕ → ℝ} {Λ : ℝ} {j i ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hB : ∀ k ∈ B, 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1)
    (hBΛ : ∀ k ∈ B, Real.log k ≤ Λ) (hc : ∀ k ∈ B, |c k| ≤ k.divisors.card)
    {σ σ' T V : ℝ} (hσ : 0 ≤ σ) (hσσ' : σ ≤ σ') (hT : 0 ≤ T) (hV : 0 ≤ V) {W : Finset ℝ}
    (hW : ∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|)
    (hbig : ∀ t ∈ W, V ≤ ‖dpoly (genClassCoeff c Λ i σ') B t‖) :
    (W.card : ℝ) * (V ^ ℓ) ^ 2
      ≤ (T + 1 + 4 * (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) * (1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)))
          * (1 + 2 * Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)) * classPowerMass j ℓ σ := by
  have hB1 : ∀ k ∈ B, 1 ≤ k := fun k hk => le_trans Nat.one_le_two_pow (hB k hk).1
  have hL : 2 ≤ (2 * 2 ^ j) ^ ℓ := by
    calc 2 ≤ 2 * 2 ^ j := by have := Nat.one_le_two_pow (n := j); omega
      _ ≤ (2 * 2 ^ j) ^ ℓ := Nat.le_self_pow (by omega) _
  have hdiam : ∀ x ∈ W, ∀ y ∈ W, |x - y| ≤ T := by
    intro x hx y hy
    have h1 := hW x hx
    have h2 := hW y hy
    rw [abs_le]
    constructor <;> linarith
  have hbig' : ∀ t ∈ W, V ^ ℓ ≤
      ‖dpoly (powConv (genClassCoeff c Λ i σ') B ℓ) (powSupport B ℓ) t‖ := by
    intro t ht
    rw [← norm_pow_genClass_eq hB1]
    exact pow_le_pow_left₀ hV (hbig t ht) ℓ
  have h := card_mul_sq_le_of_dpoly_large_mvt hL (powSupport_block_subset_Icc hB hℓ) hT hsep
    hdiam hbig' (pow_nonneg hV ℓ)
  refine le_trans h ?_
  have hmass := sum_sq_powConv_genClass_le (i := i) (ℓ := ℓ) hB hBΛ hc hσ hσσ'
  have hpos : 0 ≤ (T + 1 + 4 * (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)
      * (1 + Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)))
      * (1 + 2 * Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)) := by
    have hlog : 0 ≤ Real.log (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ (2 * 2 ^ j) ^ ℓ))
    positivity
  exact mul_le_mul_of_nonneg_left hmass hpos

/-- **The Huxley count for a raised class polynomial on any block.** -/
theorem card_mul_pow_le_genClass_huxley {B : Finset ℕ} {c : ℕ → ℝ} {Λ : ℝ} {j i ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hB : ∀ k ∈ B, 2 ^ j ≤ k ∧ k ≤ 2 * 2 ^ j - 1)
    (hBΛ : ∀ k ∈ B, Real.log k ≤ Λ) (hc : ∀ k ∈ B, |c k| ≤ k.divisors.card)
    {σ σ' T V : ℝ} (hσ : 0 ≤ σ) (hσσ' : σ ≤ σ') (hT : 0 ≤ T) (hV : 0 < V) {W : Finset ℝ}
    (hW : ∀ t ∈ W, T ≤ t ∧ t ≤ 2 * T) (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|)
    (hbig : ∀ t ∈ W, V ≤ ‖dpoly (genClassCoeff c Λ i σ') B t‖)
    (hthresh : classPowerMass j ℓ σ
        * (1 + 1536 * Real.sqrt (3 * (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) / (4 * Real.pi)))
      ≤ (V ^ ℓ / ℓ) ^ 2 / 3) :
    (W.card : ℝ) * (V ^ ℓ / ℓ) ^ 2
      ≤ ℓ * ((T * (1284 * classPowerMass j ℓ σ) ^ 2 / (V ^ ℓ / ℓ) ^ 4 + 1) *
          (2 * classPowerMass j ℓ σ * ((((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ)
            + 12 * Real.pi * (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) * (1 + Real.log (T + 1))))) := by
  have hB1 : ∀ k ∈ B, 1 ≤ k := fun k hk => le_trans Nat.one_le_two_pow (hB k hk).1
  have hdiam : ∀ x ∈ W, ∀ y ∈ W, |x - y| ≤ T := by
    intro x hx y hy
    have h1 := hW x hx
    have h2 := hW y hy
    rw [abs_le]
    constructor <;> linarith
  have hbig' : ∀ t ∈ W, V ^ ℓ ≤
      ‖dpoly (powConv (genClassCoeff c Λ i σ') B ℓ) (powSupport B ℓ) t‖ := by
    intro t ht
    rw [← norm_pow_genClass_eq hB1]
    exact pow_le_pow_left₀ hV.le (hbig t ht) ℓ
  have hN₀ : ∀ r < ℓ, (((2 ^ j) ^ ℓ * 2 ^ r : ℕ) : ℝ) ≤ (((2 * 2 ^ j) ^ ℓ : ℕ) : ℝ) := by
    intro r hr
    have : (2 ^ j) ^ ℓ * 2 ^ r ≤ (2 * 2 ^ j) ^ ℓ := by
      rw [mul_pow, mul_comm (2 ^ ℓ)]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hr.le)
    exact_mod_cast this
  have hmass := sum_sq_powConv_genClass_le (i := i) (ℓ := ℓ) hB hBΛ hc hσ hσσ'
  exact card_mul_sq_le_of_dpoly_large_huxley_range (Nat.one_le_pow _ _ (Nat.two_pow_pos j)) hℓ
    (powSupport_block_bounds hB hℓ) hT (pow_pos hV ℓ) hmass hN₀ hsep hdiam hbig' hthresh

end

end RHTower
