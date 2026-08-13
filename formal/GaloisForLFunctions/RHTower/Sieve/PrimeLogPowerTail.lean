import GaloisForLFunctions.PNTPlus.BrunTitchmarsh
import Mathlib

/-!
# Summability of the prime reciprocal-log-power tail

For every `s > 0` the prime sum `∑ₚ 1/(p (log p)^s)` converges.  Splitting the primes into
dyadic blocks `[2ᵏ, 2ᵏ⁺¹)`, the Chebyshev bound `π(N) = O(N / log N)` limits the `k`-th block
count by a constant multiple of `2ᵏ/k`, while every term of that block is at most
`1/(2ᵏ (k log 2)ˢ)`; the block sums are therefore dominated by `k^{-(1+s)}`, which is summable.
The integer comparison `∑ₙ 1/(n (log n)^s)` fails for `s ≤ 1`: the sparseness of the primes is
exactly what buys the full range `s > 0`.
-/

open Filter
open scoped BigOperators

namespace RHTower.Sieve

/-- Number of primes in the dyadic block `[2ᵏ, 2ᵏ⁺¹)`. -/
def dyadicBlockPrimeCount (k : ℕ) : ℕ :=
  ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime).card

/-- Dominating weight of a single term in the `k`-th dyadic block. -/
noncomputable def dyadicBlockTermWeight (s : ℝ) (k : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ k * ((k : ℝ) * Real.log 2) ^ s)

theorem dyadicBlockTermWeight_nonneg (s : ℝ) (k : ℕ) : 0 ≤ dyadicBlockTermWeight s k := by
  unfold dyadicBlockTermWeight
  positivity

theorem dyadicBlockTermWeight_pos (s : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    0 < dyadicBlockTermWeight s k := by
  unfold dyadicBlockTermWeight
  have hkpos : (0 : ℝ) < (k : ℝ) * Real.log 2 := by
    have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  positivity

/-- Every prime lies in a positive dyadic block. -/
theorem one_le_log_two_of_prime (p : Nat.Primes) : 1 ≤ Nat.log 2 (p : ℕ) :=
  Nat.le_log_of_pow_le (by norm_num) (by simpa using p.2.two_le)

/-- Termwise dyadic domination of the reciprocal log-power weight. -/
theorem one_div_mul_log_rpow_le_blockWeight {s : ℝ} (hs : 0 < s) (p : Nat.Primes) :
    1 / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) ^ s) ≤
      dyadicBlockTermWeight s (Nat.log 2 (p : ℕ)) := by
  set k := Nat.log 2 (p : ℕ) with hk
  have hk1 : 1 ≤ k := one_le_log_two_of_prime p
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hlow : (2 : ℕ) ^ k ≤ (p : ℕ) := Nat.pow_log_le_self 2 (by omega)
  have hlowR : (2 : ℝ) ^ k ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hlow
  have hklogpos : (0 : ℝ) < (k : ℝ) * Real.log 2 := by
    have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hlogp : (k : ℝ) * Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) := by
    have hmono := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ k) hlowR
    rwa [Real.log_pow] at hmono
  have hrpow : ((k : ℝ) * Real.log 2) ^ s ≤ Real.log ((p : ℕ) : ℝ) ^ s :=
    Real.rpow_le_rpow hklogpos.le hlogp hs.le
  have hden : (2 : ℝ) ^ k * ((k : ℝ) * Real.log 2) ^ s ≤
      ((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) ^ s := by
    apply mul_le_mul hlowR hrpow (Real.rpow_nonneg hklogpos.le s) (by positivity)
  have hdenpos : (0 : ℝ) < (2 : ℝ) ^ k * ((k : ℝ) * Real.log 2) ^ s := by
    have := Real.rpow_pos_of_pos hklogpos s
    positivity
  exact one_div_le_one_div_of_le hdenpos hden

/-- The dyadic block-sum majorant is summable for every positive exponent. -/
theorem summable_dyadicBlockPrimeCount_mul_weight {s : ℝ} (hs : 0 < s) :
    Summable fun k : ℕ => (dyadicBlockPrimeCount k : ℝ) * dyadicBlockTermWeight s k := by
  have hg : Summable fun k : ℕ => 1 / (k : ℝ) ^ (1 + s) :=
    (Real.summable_one_div_nat_rpow).mpr (by linarith)
  refine summable_of_isBigO_nat hg ?_
  -- Chebyshev: the block count is eventually at most `c₀ 2^(k+1) / log 2^(k+1)`
  obtain ⟨c₀, hc₀⟩ := (BrunTitchmarsh.card_range_filter_prime_isBigO).isBigOWith
  rw [Asymptotics.isBigOWith_iff, eventually_atTop] at hc₀
  obtain ⟨N₀, hN₀⟩ := hc₀
  simp only [Asymptotics.isBigO_iff, eventually_atTop]
  refine ⟨c₀ * 2 / Real.log 2 * (1 / Real.log 2 ^ s), max N₀ 1, fun k hk => ?_⟩
  have hk1 : 1 ≤ k := le_trans (le_max_right _ _) hk
  have hkN₀ : N₀ ≤ k := le_trans (le_max_left _ _) hk
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  -- block ⊆ range, and the range count obeys Chebyshev at `2^(k+1) ≥ N₀`
  have hblock_le : dyadicBlockPrimeCount k ≤
      ((Finset.range (2 ^ (k + 1))).filter Nat.Prime).card := by
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    rw [Finset.mem_Ico] at hp
    exact ⟨Finset.mem_range.mpr hp.1.2, hp.2⟩
  have h2k : N₀ ≤ 2 ^ (k + 1) := by
    calc N₀ ≤ k := hkN₀
      _ ≤ 2 ^ (k + 1) := le_of_lt (lt_of_lt_of_le (Nat.lt_two_pow_self)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hcheb := hN₀ (2 ^ (k + 1)) h2k
  have h2kR : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hlog2k : Real.log ((2 : ℕ) ^ (k + 1) : ℕ) = (k + 1 : ℝ) * Real.log 2 := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hcount : ((dyadicBlockPrimeCount k : ℝ)) ≤
      c₀ * ((2 : ℝ) ^ (k + 1) / ((k + 1 : ℝ) * Real.log 2)) := by
    have hbR : ((dyadicBlockPrimeCount k : ℝ)) ≤
        (((Finset.range (2 ^ (k + 1))).filter Nat.Prime).card : ℝ) := by
      exact_mod_cast hblock_le
    refine le_trans hbR ?_
    have hnorm := hcheb
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
    have habs1 : |((((Finset.range (2 ^ (k + 1))).filter Nat.Prime).card : ℕ) : ℝ)| =
        (((Finset.range (2 ^ (k + 1))).filter Nat.Prime).card : ℝ) :=
      abs_of_nonneg (by positivity)
    have hquotpos : (0 : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) / Real.log ((2 ^ (k + 1) : ℕ) : ℝ) := by
      have hgt : (1 : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by
        have : (1 : ℕ) < 2 ^ (k + 1) := Nat.one_lt_two_pow_iff.mpr (by omega)
        exact_mod_cast this
      have := Real.log_pos hgt
      positivity
    rw [habs1, abs_of_nonneg hquotpos.le] at hnorm
    calc (((Finset.range (2 ^ (k + 1))).filter Nat.Prime).card : ℝ) ≤
        c₀ * (((2 ^ (k + 1) : ℕ) : ℝ) / Real.log ((2 ^ (k + 1) : ℕ) : ℝ)) := hnorm
      _ = c₀ * ((2 : ℝ) ^ (k + 1) / ((k + 1 : ℝ) * Real.log 2)) := by
          congr 1
          rw [show (((2 ^ (k + 1) : ℕ) : ℝ)) = (2 : ℝ) ^ (k + 1) by push_cast; ring]
          congr 1
          rw [show ((k : ℝ) + 1) * Real.log 2 = Real.log ((2 : ℝ) ^ (k + 1)) by
            rw [Real.log_pow]; push_cast; ring]
  -- assemble the `k^{-(1+s)}` domination
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hwval : dyadicBlockTermWeight s k =
      1 / ((2 : ℝ) ^ k * ((k : ℝ) * Real.log 2) ^ s) := rfl
  have hklogpos : (0 : ℝ) < (k : ℝ) * Real.log 2 := by positivity
  have hsplit : ((k : ℝ) * Real.log 2) ^ s = (k : ℝ) ^ s * Real.log 2 ^ s :=
    Real.mul_rpow hkpos.le hlog2.le
  have hbound : (dyadicBlockPrimeCount k : ℝ) * dyadicBlockTermWeight s k ≤
      c₀ * 2 / Real.log 2 * (1 / Real.log 2 ^ s) * (1 / (k : ℝ) ^ (1 + s)) := by
    have hwpos := dyadicBlockTermWeight_pos s hk1
    calc (dyadicBlockPrimeCount k : ℝ) * dyadicBlockTermWeight s k ≤
        (c₀ * ((2 : ℝ) ^ (k + 1) / ((k + 1 : ℝ) * Real.log 2))) * dyadicBlockTermWeight s k :=
          mul_le_mul_of_nonneg_right hcount hwpos.le
      _ = c₀ * 2 / Real.log 2 * ((2 : ℝ) ^ k / ((k + 1 : ℝ))) * dyadicBlockTermWeight s k := by
          field_simp
          ring
      _ ≤ c₀ * 2 / Real.log 2 * ((2 : ℝ) ^ k / (k : ℝ)) * dyadicBlockTermWeight s k := by
          have hc₀nonneg : 0 ≤ c₀ := by
            by_contra hneg
            push Not at hneg
            have := lt_of_le_of_lt hcount
              (mul_neg_of_neg_of_pos hneg (by positivity))
            have hnn : (0 : ℝ) ≤ (dyadicBlockPrimeCount k : ℝ) := by positivity
            linarith
          have hdiv : (2 : ℝ) ^ k / ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k / (k : ℝ) := by
            gcongr
            linarith
          have hfront : (0 : ℝ) ≤ c₀ * 2 / Real.log 2 :=
            div_nonneg (by linarith) hlog2.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdiv hfront) hwpos.le
      _ = c₀ * 2 / Real.log 2 * (1 / Real.log 2 ^ s) * (1 / ((k : ℝ) * (k : ℝ) ^ s)) := by
          rw [hwval, hsplit]
          field_simp
      _ = c₀ * 2 / Real.log 2 * (1 / Real.log 2 ^ s) * (1 / (k : ℝ) ^ (1 + s)) := by
          congr 2
          rw [Real.rpow_add hkpos, Real.rpow_one]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hlhs_nonneg : (0 : ℝ) ≤ (dyadicBlockPrimeCount k : ℝ) * dyadicBlockTermWeight s k :=
    mul_nonneg (by positivity) (dyadicBlockTermWeight_nonneg s k)
  rw [abs_of_nonneg hlhs_nonneg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (k : ℝ) ^ (1 + s))]
  exact hbound

/-- **Prime reciprocal-log-power tail.**  For every `s > 0`, `∑ₚ 1/(p (log p)^s)` converges. -/
theorem summable_primes_one_div_mul_log_rpow {s : ℝ} (hs : 0 < s) :
    Summable fun p : Nat.Primes => 1 / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) ^ s) := by
  classical
  set f : Nat.Primes → ℝ :=
    fun p => 1 / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ) ^ s) with hf
  have hnonneg : ∀ p : Nat.Primes, 0 ≤ f p := by
    intro p
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have hlogpos : 0 < Real.log ((p : ℕ) : ℝ) :=
      Real.log_pos (by linarith)
    have := Real.rpow_pos_of_pos hlogpos s
    positivity
  have hb := summable_dyadicBlockPrimeCount_mul_weight hs
  refine summable_of_sum_le
    (c := ∑' k, (dyadicBlockPrimeCount k : ℝ) * dyadicBlockTermWeight s k) hnonneg ?_
  intro S
  have hbnonneg : ∀ k : ℕ,
      0 ≤ (dyadicBlockPrimeCount k : ℝ) * dyadicBlockTermWeight s k :=
    fun k => mul_nonneg (by positivity) (dyadicBlockTermWeight_nonneg s k)
  set K := S.sup fun p => Nat.log 2 (p : ℕ) with hK
  have hmaps : ∀ p ∈ S, Nat.log 2 (p : ℕ) ∈ Finset.range (K + 1) := by
    intro p hp
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.le_sup (f := fun p : Nat.Primes => Nat.log 2 (p : ℕ)) hp
  calc ∑ p ∈ S, f p ≤ ∑ p ∈ S, dyadicBlockTermWeight s (Nat.log 2 (p : ℕ)) :=
        Finset.sum_le_sum fun p _ => one_div_mul_log_rpow_le_blockWeight hs p
    _ = ∑ k ∈ Finset.range (K + 1),
          ∑ p ∈ S.filter (fun p : Nat.Primes => Nat.log 2 (p : ℕ) = k),
            dyadicBlockTermWeight s (Nat.log 2 (p : ℕ)) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ k ∈ Finset.range (K + 1),
          ((S.filter (fun p : Nat.Primes => Nat.log 2 (p : ℕ) = k)).card : ℝ) *
            dyadicBlockTermWeight s k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl (fun p hp => by
          rw [(Finset.mem_filter.mp hp).2]), Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ Finset.range (K + 1),
          (dyadicBlockPrimeCount k : ℝ) * dyadicBlockTermWeight s k := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (dyadicBlockTermWeight_nonneg s k)
        have hcard : (S.filter (fun p : Nat.Primes => Nat.log 2 (p : ℕ) = k)).card ≤
            dyadicBlockPrimeCount k := by
          apply Finset.card_le_card_of_injOn (fun p : Nat.Primes => (p : ℕ))
          · intro p hp
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp
            obtain ⟨_, hpk⟩ := hp
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico]
            refine ⟨⟨?_, ?_⟩, p.2⟩
            · rw [← hpk]
              exact Nat.pow_log_le_self 2 (by have := p.2.two_le; omega)
            · rw [← hpk]
              exact Nat.lt_pow_succ_log_self (by norm_num) (p : ℕ)
          · intro p _ q _ hpq
            exact Subtype.ext hpq
        exact_mod_cast hcard
    _ ≤ ∑' k, (dyadicBlockPrimeCount k : ℝ) * dyadicBlockTermWeight s k :=
        hb.sum_le_tsum _ fun k _ => hbnonneg k

end RHTower.Sieve
