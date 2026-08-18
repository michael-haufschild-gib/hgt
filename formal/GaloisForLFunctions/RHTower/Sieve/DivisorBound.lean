import Mathlib

/-!
# The divisor bound `d(n) ≪_ε n^ε`

Absent from mathlib and required by every large-values estimate with divisor-bounded coefficients —
in particular by Jutila's estimate, which is the input to Matomäki–Teräväinen's Lemma 4.1 and hence
to the Type II estimate `(5.2)` of the all-interval `E₃` programme.

The proof is the classical one, made explicit: `d(n)/n^ε` is the product over the prime factors of
`(a_p+1)/p^{a_p ε}`.  Above the threshold `2^{1/ε}` each factor is at most one, because
`p^{a ε} ≥ 2^a ≥ a+1`; below it each factor is at most `K = 1 + 1/(ε log 2)`, because
`2^{aε} ≥ 1 + aε log 2`.  So the constant is `K` raised to the number of primes below the threshold.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The per-prime constant of the divisor bound. -/
def divisorBoundFactor (ε : ℝ) : ℝ := 1 + 1 / (ε * Real.log 2)

/-- The threshold above which a prime contributes nothing. -/
def divisorBoundThreshold (ε : ℝ) : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ + 1

/-- The explicit constant of the divisor bound. -/
def divisorBoundConst (ε : ℝ) : ℝ :=
  (divisorBoundFactor ε) ^ ((Nat.primesBelow (divisorBoundThreshold ε)).card)

theorem one_le_divisorBoundFactor {ε : ℝ} (hε : 0 < ε) : 1 ≤ divisorBoundFactor ε := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [divisorBoundFactor]
  have : (0 : ℝ) < 1 / (ε * Real.log 2) := by positivity
  linarith

theorem divisorBoundConst_pos {ε : ℝ} (hε : 0 < ε) : 0 < divisorBoundConst ε := by
  have h1 := one_le_divisorBoundFactor hε
  rw [divisorBoundConst]
  exact pow_pos (by linarith) _

/-- Below the threshold: the local factor is at most `K`. -/
theorem local_factor_le_small {ε : ℝ} (hε : 0 < ε) {p a : ℕ} (hp : 2 ≤ p) :
    ((a : ℝ) + 1) / ((p : ℝ)) ^ ((a : ℝ) * ε) ≤ divisorBoundFactor ε := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have haε : (0 : ℝ) ≤ (a : ℝ) * ε := by positivity
  have hmono : (2 : ℝ) ^ ((a : ℝ) * ε) ≤ ((p : ℝ)) ^ ((a : ℝ) * ε) :=
    Real.rpow_le_rpow (by norm_num) hp2 haε
  have hexp : (1 : ℝ) + (a : ℝ) * ε * Real.log 2 ≤ (2 : ℝ) ^ ((a : ℝ) * ε) := by
    have h := Real.add_one_le_exp ((a : ℝ) * ε * Real.log 2)
    have hrw : Real.exp ((a : ℝ) * ε * Real.log 2) = (2 : ℝ) ^ ((a : ℝ) * ε) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
      ring_nf
    rw [hrw] at h
    linarith
  have hden : (0 : ℝ) < 1 + (a : ℝ) * ε * Real.log 2 := by positivity
  have hstep : ((a : ℝ) + 1) / ((p : ℝ)) ^ ((a : ℝ) * ε)
      ≤ ((a : ℝ) + 1) / (1 + (a : ℝ) * ε * Real.log 2) := by
    refine div_le_div_of_nonneg_left (by positivity) hden (le_trans hexp hmono)
  refine le_trans hstep ?_
  rw [divisorBoundFactor, div_le_iff₀ hden]
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hkey : (0 : ℝ) ≤ 1 / (ε * Real.log 2) + (a : ℝ) * ε * Real.log 2 := by positivity
  have hid : (1 + 1 / (ε * Real.log 2)) * (1 + (a : ℝ) * ε * Real.log 2)
      = 1 + (a : ℝ) * ε * Real.log 2 + 1 / (ε * Real.log 2) + (a : ℝ) := by
    field_simp
    ring
  rw [hid]
  linarith [hkey]

/-- Above the threshold: the local factor is at most one. -/
theorem local_factor_le_one {ε : ℝ} (hε : 0 < ε) {p a : ℕ}
    (hp : divisorBoundThreshold ε ≤ p) :
    ((a : ℝ) + 1) / ((p : ℝ)) ^ ((a : ℝ) * ε) ≤ 1 := by
  have hthr : (2 : ℝ) ^ (1 / ε) ≤ (p : ℝ) := by
    have h1 : (2 : ℝ) ^ (1 / ε) ≤ ((⌈(2 : ℝ) ^ (1 / ε)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(2 : ℝ) ^ (1 / ε)⌉₊ : ℕ) : ℝ) ≤ (p : ℝ) := by
      have : (⌈(2 : ℝ) ^ (1 / ε)⌉₊ : ℕ) ≤ p := by
        rw [divisorBoundThreshold] at hp
        omega
      exact_mod_cast this
    linarith
  have haε : (0 : ℝ) ≤ (a : ℝ) * ε := by positivity
  have hpow : (2 : ℝ) ^ ((a : ℝ)) ≤ ((p : ℝ)) ^ ((a : ℝ) * ε) := by
    have hbase : (0 : ℝ) < (2 : ℝ) ^ (1 / ε) := Real.rpow_pos_of_pos (by norm_num) _
    have hstep : ((2 : ℝ) ^ (1 / ε)) ^ ((a : ℝ) * ε) ≤ ((p : ℝ)) ^ ((a : ℝ) * ε) :=
      Real.rpow_le_rpow hbase.le hthr haε
    have hid : ((2 : ℝ) ^ (1 / ε)) ^ ((a : ℝ) * ε) = (2 : ℝ) ^ ((a : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      field_simp
    rw [hid] at hstep
    exact hstep
  have hsucc : ((a : ℝ) + 1) ≤ (2 : ℝ) ^ ((a : ℝ)) := by
    have hnat : a < 2 ^ a := Nat.lt_pow_self (by norm_num)
    have hcast : ((a + 1 : ℕ) : ℝ) ≤ ((2 ^ a : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    rw [Real.rpow_natCast (2 : ℝ) a]
    exact hcast
  have hden : (0 : ℝ) < ((p : ℝ)) ^ ((a : ℝ) * ε) := by
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have : (0 : ℝ) < (2 : ℝ) ^ (1 / ε) := Real.rpow_pos_of_pos (by norm_num) _
      linarith
    exact Real.rpow_pos_of_pos hp0 _
  rw [div_le_one hden]
  linarith [hsucc, hpow]

/-- **The divisor bound.**  `d(n) ≤ C_ε · n^ε` with `C_ε` explicit. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : n ≠ 0) :
    (n.divisors.card : ℝ) ≤ divisorBoundConst ε * (n : ℝ) ^ ε := by
  classical
  set S : Finset ℕ := n.primeFactors with hS
  set A : ℕ → ℕ := fun p => n.factorization p with hA
  set K : ℝ := divisorBoundFactor ε with hK
  have hK1 : 1 ≤ K := one_le_divisorBoundFactor hε
  have hp2 : ∀ p ∈ S, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  -- the divisor count as a product
  have hd : (n.divisors.card : ℝ) = ∏ p ∈ S, ((A p : ℝ) + 1) := by
    rw [Nat.card_divisors hn]
    push_cast
    rfl
  -- the size as a product
  have hnprod : (n : ℝ) = ∏ p ∈ S, ((p : ℝ)) ^ (A p) := by
    have := Nat.prod_factorization_pow_eq_self hn
    rw [Nat.prod_factorization_eq_prod_primeFactors] at this
    calc (n : ℝ) = ((∏ p ∈ S, p ^ (A p) : ℕ) : ℝ) := by rw [this]
      _ = ∏ p ∈ S, ((p : ℝ)) ^ (A p) := by push_cast; rfl
  have hnrpow : (n : ℝ) ^ ε = ∏ p ∈ S, ((p : ℝ)) ^ ((A p : ℝ) * ε) := by
    rw [hnprod]
    rw [← Real.finsetProd_rpow S _ (fun p hp => by positivity) ε]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [← Real.rpow_natCast ((p : ℝ)) (A p), ← Real.rpow_mul (by positivity)]
  -- the comparison weight
  set g : ℕ → ℝ := fun p => if p < divisorBoundThreshold ε then K else 1 with hg
  have hterm : ∀ p ∈ S, ((A p : ℝ) + 1) ≤ g p * ((p : ℝ)) ^ ((A p : ℝ) * ε) := by
    intro p hp
    have hppos : (0 : ℝ) < ((p : ℝ)) ^ ((A p : ℝ) * ε) := by
      have : (0 : ℝ) < (p : ℝ) := by
        have := hp2 p hp
        exact_mod_cast (by omega : 0 < p)
      exact Real.rpow_pos_of_pos this _
    show ((A p : ℝ) + 1)
      ≤ (if p < divisorBoundThreshold ε then K else 1) * ((p : ℝ)) ^ ((A p : ℝ) * ε)
    by_cases hlt : p < divisorBoundThreshold ε
    · rw [if_pos hlt]
      have := local_factor_le_small (ε := ε) (p := p) (a := A p) hε (hp2 p hp)
      rw [div_le_iff₀ hppos] at this
      linarith
    · rw [if_neg hlt]
      have := local_factor_le_one (ε := ε) (p := p) (a := A p) hε (by omega)
      rw [div_le_one hppos] at this
      linarith
  have hprod : ∏ p ∈ S, ((A p : ℝ) + 1)
      ≤ ∏ p ∈ S, (g p * ((p : ℝ)) ^ ((A p : ℝ) * ε)) :=
    Finset.prod_le_prod (fun p _ => by positivity) hterm
  have hsplit : ∏ p ∈ S, (g p * ((p : ℝ)) ^ ((A p : ℝ) * ε))
      = (∏ p ∈ S, g p) * ∏ p ∈ S, ((p : ℝ)) ^ ((A p : ℝ) * ε) := Finset.prod_mul_distrib
  -- the weight product is at most the constant
  have hgprod : ∏ p ∈ S, g p ≤ divisorBoundConst ε := by
    have hval : ∏ p ∈ S, g p = K ^ ((S.filter (fun p => p < divisorBoundThreshold ε)).card) := by
      rw [hg, Finset.prod_ite]
      simp [Finset.prod_const]
    rw [hval, divisorBoundConst, ← hK]
    refine pow_le_pow_right₀ hK1 ?_
    refine Finset.card_le_card ?_
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨hp.2, Nat.prime_of_mem_primeFactors hp.1⟩
  have hpos : (0 : ℝ) ≤ ∏ p ∈ S, ((p : ℝ)) ^ ((A p : ℝ) * ε) := by
    refine Finset.prod_nonneg fun p hp => ?_
    positivity
  rw [hd, hnrpow]
  calc ∏ p ∈ S, ((A p : ℝ) + 1)
      ≤ (∏ p ∈ S, g p) * ∏ p ∈ S, ((p : ℝ)) ^ ((A p : ℝ) * ε) := by
        rw [← hsplit]; exact hprod
    _ ≤ divisorBoundConst ε * ∏ p ∈ S, ((p : ℝ)) ^ ((A p : ℝ) * ε) :=
        mul_le_mul_of_nonneg_right hgprod hpos

end

end RHTower.Sieve
