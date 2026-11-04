import GaloisForLFunctions.ArithmeticGaugeTheory.TheGaugeExponentIsATailInvariant

/-!
# The exponent is invariant on sparse prime sets

Finite flips do not move the Möbius exponent (`gaugeExponent_moebius_eq_of_agree_off_finset`). This
module extends the invariance to infinite sets of primes that are sparse at the level `θ`.

* **One prime, sharp form** (`norm_moebiusGaugeSum_le_of_agree_off`). If `x, x'` agree off a prime
  `p`, then `S_{x'}(N) = S_x(N) − (χ_{x'}(p) − χ_x(p)) A_x(⌊N/p⌋)`, and `A_x` vanishes at `0`. A bound
  `|S_x(M)| ≤ C (M + 1)^θ` therefore gives `|S_{x'}(N)| ≤ C (1 + K_θ p^{−θ}) (N + 1)^θ` with the
  absolute constant `K_θ = 2·4^θ/(1 − 2^{−θ})`: the change costs a factor `1 + O(p^{−θ})`, not a
  constant factor.
* **Finitely many primes** (`norm_moebiusGaugeSum_le_of_agree_off_finset`). The factors multiply.
* **Sparse sets** (`gaugePowerBound_moebius_of_agree_off_sparse`). If every finite part of `P` has
  `Σ p^{−θ} ≤ B`, a power bound of exponent `θ` survives every change of the gauge point on `P`,
  with constant multiplied by `exp(K_θ B)`: the sum up to `N` only reads the primes `≤ N`.
* **Exponent** (`gaugeExponent_moebius_le_of_agree_off_sparse`). If `P` is sparse at every level
  `θ > θ₀`, then `θ_μ(x') ≤ max(θ₀, θ_μ(x))`.

For `θ₀ = ½` this lets a gauge point be changed freely on a set of primes with `Σ p^{−θ} < ∞` for
every `θ > ½` (for instance `≍ √X` primes near each `X` of a geometric sequence) without raising its
exponent above `½`.
-/

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.ArithmeticGaugeTheory

open ArithmeticCorrelationGeometry

/-! ### One prime, sharp form -/

/-- **Changing one prime.** `S_{x'}(N) = S_x(N) − (χ_{x'}(p) − χ_x(p)) A_x(⌊N/p⌋)`. -/
theorem moebiusGaugeSum_eq_sub_of_agree_off {p : ℕ} (hp : p.Prime) {x x' : GaugeTorus}
    (h : ∀ q, q.Prime → q ≠ p → twist x' q = twist x q) (N : ℕ) :
    moebiusGaugeSum N x' =
      moebiusGaugeSum N x - (twist x' p - twist x p) * coprimeMoebiusSum p x (N / p) := by
  rw [moebiusGaugeSum_eq_split hp x', moebiusGaugeSum_eq_split hp x, coprimeMoebiusSum_congr h,
    coprimeMoebiusSum_congr h]
  ring

/-- The one-prime transfer constant `K_θ = 2·4^θ/(1 − 2^{−θ})`. -/
def primeTransferConst (θ : ℝ) : ℝ := 2 * 4 ^ θ * (1 - (2 : ℝ) ^ (-θ))⁻¹

theorem primeTransferConst_nonneg {θ : ℝ} (hθ : 0 < θ) : 0 ≤ primeTransferConst θ := by
  have : (2 : ℝ) ^ (-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have : 0 ≤ (1 - (2 : ℝ) ^ (-θ))⁻¹ := inv_nonneg.mpr (by linarith)
  unfold primeTransferConst
  positivity

/-- For `⌊N/p⌋ ≥ 1`: `(⌊N/p⌋ + 1)^θ ≤ 2^θ p^{−θ} (N + 1)^θ`. -/
theorem div_add_one_rpow_le {p N : ℕ} (hp : 0 < p) (hNp : 1 ≤ N / p) {θ : ℝ} (hθ : 0 ≤ θ) :
    (((N / p : ℕ) : ℝ) + 1) ^ θ ≤ 2 ^ θ * (p : ℝ) ^ (-θ) * ((N : ℝ) + 1) ^ θ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p := Nat.cast_div_le
  have h2 : (1 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hNp
  have hbase : ((N / p : ℕ) : ℝ) + 1 ≤ 2 * ((N : ℝ) + 1) / p := by
    have : (N : ℝ) / p ≤ ((N : ℝ) + 1) / p := div_le_div_of_nonneg_right (by linarith) hp0.le
    have : 2 * (((N : ℝ) + 1) / p) = 2 * ((N : ℝ) + 1) / p := by ring
    linarith
  calc (((N / p : ℕ) : ℝ) + 1) ^ θ ≤ (2 * ((N : ℝ) + 1) / p) ^ θ :=
        Real.rpow_le_rpow (by positivity) hbase hθ
    _ = 2 ^ θ * (p : ℝ) ^ (-θ) * ((N : ℝ) + 1) ^ θ := by
        rw [Real.div_rpow (by positivity) hp0.le, Real.mul_rpow (by norm_num) (by positivity),
          Real.rpow_neg hp0.le]
        field_simp

/-- **One prime, sharp form.** A power bound `C (N + 1)^θ` at `x` gives
`C (1 + K_θ p^{−θ}) (N + 1)^θ` at every point that agrees with `x` off `p`. -/
theorem norm_moebiusGaugeSum_le_of_agree_off {p : ℕ} (hp : p.Prime) {x x' : GaugeTorus}
    (h : ∀ q, q.Prime → q ≠ p → twist x' q = twist x q) {C θ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (hS : ∀ M, ‖moebiusGaugeSum M x‖ ≤ C * ((M : ℝ) + 1) ^ θ) (N : ℕ) :
    ‖moebiusGaugeSum N x'‖ ≤
      C * (1 + primeTransferConst θ * (p : ℝ) ^ (-θ)) * ((N : ℝ) + 1) ^ θ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpθ : 0 ≤ (p : ℝ) ^ (-θ) := Real.rpow_nonneg hp0.le _
  have hK := primeTransferConst_nonneg hθ
  have hN : 0 ≤ ((N : ℝ) + 1) ^ θ := by positivity
  rw [moebiusGaugeSum_eq_sub_of_agree_off hp h]
  have hdiff : ‖twist x' p - twist x p‖ ≤ 2 := by
    calc ‖twist x' p - twist x p‖ ≤ ‖twist x' p‖ + ‖twist x p‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_twist, norm_twist]; norm_num
  have hA : ‖coprimeMoebiusSum p x (N / p)‖ ≤
      C * 2 ^ θ * (1 - (2 : ℝ) ^ (-θ))⁻¹ * (2 ^ θ * (p : ℝ) ^ (-θ) * ((N : ℝ) + 1) ^ θ) := by
    rcases Nat.eq_zero_or_pos (N / p) with h0 | hpos
    · rw [h0, coprimeMoebiusSum_zero, norm_zero]
      have : 0 ≤ (1 - (2 : ℝ) ^ (-θ))⁻¹ := inv_nonneg.mpr (by
        linarith [Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (neg_lt_zero.mpr hθ)])
      positivity
    · have hbound := norm_coprimeMoebiusSum_le hp hθ hC hS (N / p)
      have hr2 : (p : ℝ) ^ (-θ) ≤ (2 : ℝ) ^ (-θ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
      have hrp : (p : ℝ) ^ (-θ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
      have h2θ : (2 : ℝ) ^ (-θ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
      have hinv0 : 0 ≤ (1 - (2 : ℝ) ^ (-θ))⁻¹ := inv_nonneg.mpr (by linarith)
      have hinv : (1 - (p : ℝ) ^ (-θ))⁻¹ ≤ (1 - (2 : ℝ) ^ (-θ))⁻¹ :=
        inv_anti₀ (by linarith) (by linarith)
      have hpow := div_add_one_rpow_le hp.pos hpos hθ.le
      have hc0 : 0 ≤ C * 2 ^ θ * (1 - (2 : ℝ) ^ (-θ))⁻¹ := by positivity
      calc ‖coprimeMoebiusSum p x (N / p)‖
          ≤ C * 2 ^ θ * (1 - (p : ℝ) ^ (-θ))⁻¹ * (((N / p : ℕ) : ℝ) + 1) ^ θ := hbound
        _ ≤ C * 2 ^ θ * (1 - (2 : ℝ) ^ (-θ))⁻¹ *
              (2 ^ θ * (p : ℝ) ^ (-θ) * ((N : ℝ) + 1) ^ θ) := by
            gcongr
  have h4 : (2 : ℝ) ^ θ * 2 ^ θ = 4 ^ θ := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  calc ‖moebiusGaugeSum N x - (twist x' p - twist x p) * coprimeMoebiusSum p x (N / p)‖
      ≤ ‖moebiusGaugeSum N x‖ + ‖twist x' p - twist x p‖ * ‖coprimeMoebiusSum p x (N / p)‖ := by
        rw [← norm_mul]; exact norm_sub_le _ _
    _ ≤ C * ((N : ℝ) + 1) ^ θ + 2 * (C * 2 ^ θ * (1 - (2 : ℝ) ^ (-θ))⁻¹ *
          (2 ^ θ * (p : ℝ) ^ (-θ) * ((N : ℝ) + 1) ^ θ)) := by
        gcongr
        exact hS N
    _ = C * (1 + primeTransferConst θ * (p : ℝ) ^ (-θ)) * ((N : ℝ) + 1) ^ θ := by
        unfold primeTransferConst
        rw [← h4]
        ring

/-! ### Finitely many primes -/

/-- Points that agree at every prime agree at every positive integer. -/
theorem twist_eq_of_forall_prime {x x' : GaugeTorus} (h : ∀ q, q.Prime → twist x' q = twist x q)
    {n : ℕ} (hn : n ≠ 0) : twist x' n = twist x n :=
  twist_eq_of_primes hn fun q hq _ => h q hq

/-- Points that agree at every prime have the same Möbius sums. -/
theorem moebiusGaugeSum_congr_of_forall_prime {x x' : GaugeTorus}
    (h : ∀ q, q.Prime → twist x' q = twist x q) (N : ℕ) :
    moebiusGaugeSum N x' = moebiusGaugeSum N x := by
  refine sum_congr rfl fun n hn => ?_
  rw [twist_eq_of_forall_prime h (by have := (mem_Icc.mp hn).1; omega)]

/-- **Finitely many primes.** The one-prime factors multiply over a finite set. -/
theorem norm_moebiusGaugeSum_le_of_agree_off_finset {C θ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (F : Finset ℕ) :
    ∀ {x x' : GaugeTorus}, (∀ q, q.Prime → q ∉ F → twist x' q = twist x q) →
      (∀ M, ‖moebiusGaugeSum M x‖ ≤ C * ((M : ℝ) + 1) ^ θ) →
      ∀ N, ‖moebiusGaugeSum N x'‖ ≤
        C * (∏ p ∈ F, (1 + primeTransferConst θ * (p : ℝ) ^ (-θ))) * ((N : ℝ) + 1) ^ θ := by
  classical
  have hK := primeTransferConst_nonneg hθ
  have hfac : ∀ p : ℕ, 1 ≤ 1 + primeTransferConst θ * (p : ℝ) ^ (-θ) := fun p => by
    have : 0 ≤ (p : ℝ) ^ (-θ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
    nlinarith
  induction F using Finset.induction_on with
  | empty =>
    intro x x' h hS N
    rw [prod_empty, mul_one, moebiusGaugeSum_congr_of_forall_prime fun q hq => h q hq (notMem_empty q)]
    exact hS N
  | insert p F hpF ih =>
    intro x x' h hS N
    set z : GaugeTorus := Function.update x' p (x p) with hz
    have hzx : ∀ q, q.Prime → q ∉ F → twist z q = twist x q := by
      intro q hq hqF
      by_cases hqp : q = p
      · subst hqp
        rw [twist_prime_apply z hq, twist_prime_apply x hq, hz, Function.update_self]
      · rw [twist_prime_apply z hq, hz, Function.update_of_ne hqp, ← twist_prime_apply x' hq]
        exact h q hq (by simp [hqp, hqF])
    have hzS := ih hzx hS
    have hP0 : 0 ≤ ∏ p ∈ F, (1 + primeTransferConst θ * (p : ℝ) ^ (-θ)) :=
      prod_nonneg fun p _ => by linarith [hfac p]
    have hagree : ∀ q, q.Prime → q ≠ p → twist x' q = twist z q := fun q hq hqp => by
      rw [twist_prime_apply z hq, twist_prime_apply x' hq, hz, Function.update_of_ne hqp]
    rw [prod_insert hpF]
    by_cases hp : p.Prime
    · have := norm_moebiusGaugeSum_le_of_agree_off hp hagree hθ (by positivity) hzS N
      calc ‖moebiusGaugeSum N x'‖ ≤ C * (∏ p ∈ F, (1 + primeTransferConst θ * (p : ℝ) ^ (-θ))) *
            (1 + primeTransferConst θ * (p : ℝ) ^ (-θ)) * ((N : ℝ) + 1) ^ θ := this
        _ = _ := by ring
    · have hall : ∀ q, q.Prime → twist x' q = twist z q := fun q hq =>
        hagree q hq fun hqp => hp (hqp ▸ hq)
      rw [moebiusGaugeSum_congr_of_forall_prime hall]
      have hN : 0 ≤ ((N : ℝ) + 1) ^ θ := by positivity
      calc ‖moebiusGaugeSum N z‖
          ≤ C * (∏ p ∈ F, (1 + primeTransferConst θ * (p : ℝ) ^ (-θ))) * ((N : ℝ) + 1) ^ θ :=
            hzS N
        _ ≤ C * ((1 + primeTransferConst θ * (p : ℝ) ^ (-θ)) *
              ∏ p ∈ F, (1 + primeTransferConst θ * (p : ℝ) ^ (-θ))) * ((N : ℝ) + 1) ^ θ := by
            gcongr
            exact le_mul_of_one_le_left hP0 (hfac p)

/-! ### Sparse sets of primes -/

/-- The Möbius sum up to `N` only reads the primes `≤ N`. -/
theorem moebiusGaugeSum_congr_of_le {x x' : GaugeTorus} {N : ℕ}
    (h : ∀ q, q.Prime → q ≤ N → twist x' q = twist x q) :
    moebiusGaugeSum N x' = moebiusGaugeSum N x := by
  refine sum_congr rfl fun n hn => ?_
  obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
  rw [twist_eq_of_primes (by omega) fun q hq hqn => h q hq ((Nat.le_of_dvd (by omega) hqn).trans hnN)]

/-- **Sparse sets.** If every finite part of `P` has `Σ p^{−θ} ≤ B`, a power bound of exponent `θ`
survives every change of the gauge point on `P`. -/
theorem gaugePowerBound_moebius_of_agree_off_sparse {P : Set ℕ} {θ B : ℝ} (hθ : 0 < θ)
    (hP : ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ P → ∑ p ∈ F, (p : ℝ) ^ (-θ) ≤ B) {x x' : GaugeTorus}
    (h : ∀ q, q.Prime → q ∉ P → twist x' q = twist x q)
    (hb : GaugePowerBound moebiusSource x θ) : GaugePowerBound moebiusSource x' θ := by
  classical
  rw [gaugePowerBound_moebius_iff] at hb ⊢
  obtain ⟨C, hC, hS⟩ := hb
  have hK := primeTransferConst_nonneg hθ
  refine ⟨C * Real.exp (primeTransferConst θ * B), by positivity, fun N => ?_⟩
  -- Move `x'` to `x` above `N`; the sum up to `N` does not see the change.
  set z : GaugeTorus := fun q => if q ≤ N then x' q else x q with hz
  set F : Finset ℕ := (range (N + 1)).filter (· ∈ P) with hF
  have hzx' : moebiusGaugeSum N x' = moebiusGaugeSum N z := by
    refine (moebiusGaugeSum_congr_of_le fun q hq hqN => ?_).symm
    rw [twist_prime_apply z hq, twist_prime_apply x' hq, hz]
    simp [hqN]
  have hzx : ∀ q, q.Prime → q ∉ F → twist z q = twist x q := by
    intro q hq hqF
    rw [twist_prime_apply z hq, twist_prime_apply x hq, hz]
    by_cases hqN : q ≤ N
    · have hqP : q ∉ P := fun hqP => hqF (by simp [hF, hqP]; omega)
      simp only [hqN, if_true]
      rw [← twist_prime_apply x' hq, ← twist_prime_apply x hq]
      exact h q hq hqP
    · simp [hqN]
  have hbound := norm_moebiusGaugeSum_le_of_agree_off_finset hθ hC F hzx hS N
  have hsub : (↑F : Set ℕ) ⊆ P := fun q hq => (mem_filter.mp hq).2
  have hprod : ∏ p ∈ F, (1 + primeTransferConst θ * (p : ℝ) ^ (-θ)) ≤
      Real.exp (primeTransferConst θ * B) := by
    calc ∏ p ∈ F, (1 + primeTransferConst θ * (p : ℝ) ^ (-θ))
        ≤ ∏ p ∈ F, Real.exp (primeTransferConst θ * (p : ℝ) ^ (-θ)) :=
          prod_le_prod (fun p _ => by
            have : 0 ≤ (p : ℝ) ^ (-θ) := Real.rpow_nonneg (Nat.cast_nonneg p) _
            nlinarith) fun p _ => by
              have := Real.add_one_le_exp (primeTransferConst θ * (p : ℝ) ^ (-θ)); linarith
      _ = Real.exp (primeTransferConst θ * ∑ p ∈ F, (p : ℝ) ^ (-θ)) := by
          rw [← Real.exp_sum, mul_sum]
      _ ≤ Real.exp (primeTransferConst θ * B) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hP F hsub) hK)
  rw [hzx']
  calc ‖moebiusGaugeSum N z‖
      ≤ C * (∏ p ∈ F, (1 + primeTransferConst θ * (p : ℝ) ^ (-θ))) * ((N : ℝ) + 1) ^ θ := hbound
    _ ≤ C * Real.exp (primeTransferConst θ * B) * ((N : ℝ) + 1) ^ θ := by gcongr

/-- **Exponent on sparse sets.** If `P` is sparse at every level `θ > θ₀`, changing a gauge point on
`P` cannot raise its Möbius exponent above `max(θ₀, θ_μ(x))`. -/
theorem gaugeExponent_moebius_le_of_agree_off_sparse {P : Set ℕ} {θ₀ : ℝ} (hθ₀ : 0 ≤ θ₀)
    (hP : ∀ θ, θ₀ < θ → ∃ B : ℝ, ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ P → ∑ p ∈ F, (p : ℝ) ^ (-θ) ≤ B)
    {x x' : GaugeTorus} (h : ∀ q, q.Prime → q ∉ P → twist x' q = twist x q) :
    gaugeExponent moebiusSource x' ≤ max θ₀ (gaugeExponent moebiusSource x) := by
  refine le_of_forall_gt fun θ hθ => ?_
  obtain ⟨θ', hθ'1, hθ'2⟩ := exists_between hθ
  have hθ'0 : θ₀ < θ' := lt_of_le_of_lt (le_max_left _ _) hθ'1
  have hθ'x : gaugeExponent moebiusSource x < θ' := lt_of_le_of_lt (le_max_right _ _) hθ'1
  obtain ⟨B, hB⟩ := hP θ' hθ'0
  have hpos : 0 < θ' := lt_of_le_of_lt hθ₀ hθ'0
  exact lt_of_le_of_lt (gaugeExponent_le hpos.le (gaugePowerBound_moebius_of_agree_off_sparse hpos hB
    h (gaugePowerBound_of_gaugeExponent_lt norm_moebiusSource_le hθ'x))) hθ'2

end GaloisForLFunctions.ArithmeticGaugeTheory
