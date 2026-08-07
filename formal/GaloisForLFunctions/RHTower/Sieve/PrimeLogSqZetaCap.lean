import GaloisForLFunctions.RHTower.Sieve.Mertens
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
/-!
# The prime-restricted logarithmically weighted zeta cap

Over the primes the sum `∑ p^{−w}(log p)²` is one logarithm smaller than over the integers, and Chebyshev's
`θ` applied to each dyadic block is what produces the saving.  For a prime `p` put `j = ⌊log₂ p⌋`, so
`2^j ≤ p < 2^{j+1}`; then `p^{−w} ≤ 2^{−jw}` and `log p ≤ (j+1) log 2`, so

`∑_{p ∈ block j} p^{−w}(log p)² ≤ (j+1) log 2 · 2^{−jw} · ∑_{p ∈ block j} log p
    ≤ (j+1) log 2 · 2^{−jw} · 2^{j+1} log 4`,

the last step being Chebyshev's bound: a block carries `≈ 2^j/j` primes, not `2^j` integers.  Summing the
blocks against the geometric series with ratio `r = 2^{1−w} < 1`,

`∑_{p ≤ N} p^{−w}(log p)² ≤ 2 log 2 log 4 · ((1−r)⁻¹ + r/(1−r)²)`,

uniformly in `N`.  Against the integer cap `(16/(w−1)²)(1 + 2/(w−1))` this is smaller by a factor `1/(w−1)`:
the prime support of the coefficients is used here and nowhere else in the argument.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The geometric tail that the dyadic blocks produce. -/
theorem sum_range_succ_mul_geometric_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (J : ℕ) :
    (∑ j ∈ Finset.range J, ((j : ℝ) + 1) * r ^ j)
      ≤ (1 - r)⁻¹ + r / (1 - r) ^ 2 := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hs1 : HasSum (fun j : ℕ => r ^ j) (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr0.le hr1
  have hs2 : HasSum (fun j : ℕ => (j : ℝ) * r ^ j) (r / (1 - r) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hs : HasSum (fun j : ℕ => ((j : ℝ) + 1) * r ^ j) (r / (1 - r) ^ 2 + (1 - r)⁻¹) := by
    have h := hs2.add hs1
    refine h.congr_fun ?_
    intro j
    ring
  have hle := hs.summable.sum_le_tsum (Finset.range J) (fun j _ => by positivity)
  rw [hs.tsum_eq] at hle
  linarith [hle]

/-- **The prime-restricted logarithmically weighted zeta cap.**  Chebyshev's `θ` applied to each dyadic
block: a block `2^j ≤ p < 2^{j+1}` carries `∑_{p} log p ≤ 2^{j+1} log 4`, which is one logarithm smaller than
the number of integers in the block, so

`∑_{p ≤ N} p^{−w}(log p)² ≤ 2 log 2 log 4 · ((1−r)⁻¹ + r/(1−r)²)`,   `r = 2^{1−w} < 1`,

uniformly in `N`.  Compared with the same sum over all integers this saves a factor `1/(w−1)`: the prime
support of the coefficients is used here and nowhere else. -/
theorem sum_prime_logSq_rpow_neg_le {w : ℝ} (hw : 1 < w) (N : ℕ) :
    (∑ p ∈ Finset.Icc 1 N with Nat.Prime p, (p : ℝ) ^ (-w) * (Real.log p) ^ 2)
      ≤ 2 * Real.log 2 * Real.log 4
          * ((1 - (2 : ℝ) ^ (1 - w))⁻¹
              + (2 : ℝ) ^ (1 - w) / (1 - (2 : ℝ) ^ (1 - w)) ^ 2) := by
  classical
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  set r : ℝ := (2 : ℝ) ^ (1 - w) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hrdef]
    have hneg : (1 : ℝ) - w < 0 := by linarith
    calc (2 : ℝ) ^ (1 - w) < (2 : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hneg
      _ = 1 := Real.rpow_zero 2
  have hmaps : ∀ p ∈ Finset.filter (fun p => Nat.Prime p) (Finset.Icc 1 N),
      Nat.log 2 p ∈ Finset.range (Nat.log 2 N + 1) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.log_mono_right hp.1.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ j ∈ Finset.range (Nat.log 2 N + 1),
      (∑ p ∈ Finset.filter (fun p => Nat.log 2 p = j)
            (Finset.filter (fun p => Nat.Prime p) (Finset.Icc 1 N)),
          (p : ℝ) ^ (-w) * (Real.log p) ^ 2)
        ≤ 2 * Real.log 2 * Real.log 4 * (((j : ℝ) + 1) * r ^ j) := by
    intro j _
    have hrj : r ^ j = (2 : ℝ) ^ ((1 - w) * (j : ℝ)) := by
      rw [hrdef, ← Real.rpow_natCast ((2 : ℝ) ^ (1 - w)) j, ← Real.rpow_mul (by norm_num)]
    -- each term against `log p`
    have hterm : ∀ p ∈ Finset.filter (fun p => Nat.log 2 p = j)
        (Finset.filter (fun p => Nat.Prime p) (Finset.Icc 1 N)),
        (p : ℝ) ^ (-w) * (Real.log p) ^ 2
          ≤ (((j : ℝ) + 1) * Real.log 2) * (r ^ j * (2 : ℝ) ^ (-(j : ℝ))) * Real.log p := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hp1, hpN⟩, hprime⟩, hlogj⟩ := hp
      have hp2 : 2 ≤ p := hprime.two_le
      have hppos : (0 : ℝ) < (p : ℝ) := by
        have : 0 < p := by omega
        exact_mod_cast this
      have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
      have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg hp1R
      have hwpos : (0 : ℝ) < w := by linarith
      -- the block inequalities
      have hlow : (2 : ℕ) ^ j ≤ p := by
        rw [← hlogj]
        exact Nat.pow_log_le_self 2 (by omega)
      have hhigh : p < 2 ^ (j + 1) := by
        rw [← hlogj]
        exact Nat.lt_pow_succ_log_self (by norm_num) p
      have hlowR : ((2 : ℝ) ^ (j : ℕ)) ≤ (p : ℝ) := by
        have : ((2 ^ j : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlow
        simpa using this
      have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (j : ℕ) := by positivity
      -- the damping
      have hdamp : (p : ℝ) ^ (-w) ≤ r ^ j * (2 : ℝ) ^ (-(j : ℝ)) := by
        have hbase : ((2 : ℝ) ^ (j : ℝ)) ^ w ≤ (p : ℝ) ^ w := by
          refine Real.rpow_le_rpow (by positivity) ?_ hwpos.le
          rw [Real.rpow_natCast]
          exact hlowR
        have hinv : ((p : ℝ) ^ w)⁻¹ ≤ (((2 : ℝ) ^ (j : ℝ)) ^ w)⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos (by positivity) w) hbase
        rw [Real.rpow_neg hppos.le]
        refine hinv.trans (le_of_eq ?_)
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ)),
          ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)), hrj,
          ← Real.rpow_add (by norm_num : (0 : ℝ) < (2 : ℝ))]
        congr 1
        ring
      -- the squared logarithm
      have hsq : (Real.log p) ^ 2 ≤ (((j : ℝ) + 1) * Real.log 2) * Real.log p := by
        have hupper : Real.log (p : ℝ) ≤ ((j : ℝ) + 1) * Real.log 2 := by
          have hhR : (p : ℝ) ≤ (2 : ℝ) ^ ((j : ℕ) + 1) := by
            have : ((p : ℕ) : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hhigh.le
            simpa using this
          have hlg := Real.log_le_log hppos hhR
          rw [Real.log_pow] at hlg
          calc Real.log (p : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * Real.log 2 := hlg
            _ = ((j : ℝ) + 1) * Real.log 2 := by push_cast; ring
        calc (Real.log p) ^ 2 = Real.log p * Real.log p := sq (Real.log p) ▸ by ring
          _ ≤ (((j : ℝ) + 1) * Real.log 2) * Real.log p :=
              mul_le_mul_of_nonneg_right hupper hlogp
      calc (p : ℝ) ^ (-w) * (Real.log p) ^ 2
          ≤ (r ^ j * (2 : ℝ) ^ (-(j : ℝ))) * ((((j : ℝ) + 1) * Real.log 2) * Real.log p) :=
            mul_le_mul hdamp hsq (by positivity) (by positivity)
        _ = (((j : ℝ) + 1) * Real.log 2) * (r ^ j * (2 : ℝ) ^ (-(j : ℝ))) * Real.log p := by ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have hsub : Finset.filter (fun p => Nat.log 2 p = j)
        (Finset.filter (fun p => Nat.Prime p) (Finset.Icc 1 N))
        ⊆ Nat.primesLE (2 ^ (j + 1)) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hp1, _⟩, hprime⟩, hlogj⟩ := hp
      have hhigh : p < 2 ^ (j + 1) := by
        rw [← hlogj]
        exact Nat.lt_pow_succ_log_self (by norm_num) p
      exact Nat.mem_primesLE.2 ⟨hhigh.le, hprime⟩
    have hnn : ∀ p ∈ Nat.primesLE (2 ^ (j + 1)), p ∉ Finset.filter (fun p => Nat.log 2 p = j)
        (Finset.filter (fun p => Nat.Prime p) (Finset.Icc 1 N)) → 0 ≤ Real.log (p : ℝ) := by
      intro p hp _
      have hprime : p.Prime := Nat.prime_of_mem_primesLE hp
      have h1 : (1 : ℝ) ≤ (p : ℝ) := by
        have := hprime.two_le
        exact_mod_cast this.trans' (by norm_num)
      exact Real.log_nonneg h1
    have hθ : (∑ p ∈ Finset.filter (fun p => Nat.log 2 p = j)
          (Finset.filter (fun p => Nat.Prime p) (Finset.Icc 1 N)), Real.log (p : ℝ))
        ≤ ((2 ^ (j + 1) : ℕ) : ℝ) * Real.log 4 :=
      le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn)
        (sum_log_primesLE_le (2 ^ (j + 1)))
    have hcoeff0 : (0 : ℝ) ≤ (((j : ℝ) + 1) * Real.log 2) * (r ^ j * (2 : ℝ) ^ (-(j : ℝ))) := by
      have : (0 : ℝ) < (2 : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
      have hj : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
      have hrj0 : (0 : ℝ) ≤ r ^ j := by positivity
      exact mul_nonneg (mul_nonneg hj hlog2.le) (mul_nonneg hrj0 this.le)
    refine le_trans (mul_le_mul_of_nonneg_left hθ hcoeff0) (le_of_eq ?_)
    have hpow : ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ ((j : ℝ) + 1) := by
      rw [show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      push_cast
      ring
    rw [hpow, hrj]
    have hcomb : (2 : ℝ) ^ (-(j : ℝ)) * (2 : ℝ) ^ ((j : ℝ) + 1) = 2 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < (2 : ℝ))]
      norm_num
    calc (((j : ℝ) + 1) * Real.log 2) * ((2 : ℝ) ^ ((1 - w) * (j : ℝ)) * (2 : ℝ) ^ (-(j : ℝ)))
          * ((2 : ℝ) ^ ((j : ℝ) + 1) * Real.log 4)
        = 2 * Real.log 2 * Real.log 4
            * (((j : ℝ) + 1) * (2 : ℝ) ^ ((1 - w) * (j : ℝ)))
              * ((2 : ℝ) ^ (-(j : ℝ)) * (2 : ℝ) ^ ((j : ℝ) + 1)) / 2 := by ring
      _ = 2 * Real.log 2 * Real.log 4 * (((j : ℝ) + 1) * (2 : ℝ) ^ ((1 - w) * (j : ℝ))) := by
          rw [hcomb]
          ring
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (sum_range_succ_mul_geometric_le hr0 hr1 _) (by positivity)

end RHTower.Sieve
end
