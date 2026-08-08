import GaloisForLFunctions.RHTower.Sieve.PrimeLogSqZetaCap
import GaloisForLFunctions.RHTower.Sieve.DyadicBlockQuantities
/-!
# The damped `ℓ¹` mass of the prime logarithms

Chebyshev's `θ` on each dyadic block, summed geometrically:

`∑_{p ≤ N} log p·p^{−w} ≤ 2 log 4·(1 − 2^{1−w})⁻¹`,   `w > 1`, uniformly in `N`.

The single power of the logarithm is absorbed by `θ` itself, so — unlike the squared-logarithm cap — no polynomial
factor in the block index appears and the geometric series is bare.  This is the bound the `ℓ¹` masses of the two
prime weights of the convolution consume: `A·(that)` with `A = 1` for the inner weight and `A = 1/log 2` for the
outer one.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- **The damped `ℓ¹` mass of the prime logarithms.**  Chebyshev's `θ` on each dyadic block, summed geometrically:

`∑_{p ≤ N} log p·p^{−w} ≤ 2 log 4·(1 − 2^{1−w})⁻¹`,   `w > 1`, uniformly in `N`.

One power of the logarithm is absorbed by `θ` itself, so no polynomial factor in the block index appears — this is
the bound the `ℓ¹` masses of the two prime weights consume. -/
theorem sum_prime_log_rpow_neg_le {w : ℝ} (hw : 1 < w) (N : ℕ) :
    (∑ p ∈ Finset.Icc 1 N with Nat.Prime p, Real.log (p : ℝ) * (p : ℝ) ^ (-w))
      ≤ 2 * Real.log 4 * (1 - (2 : ℝ) ^ (1 - w))⁻¹ := by
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
          Real.log (p : ℝ) * (p : ℝ) ^ (-w))
        ≤ 2 * Real.log 4 * r ^ j := by
    intro j _
    have hrj : r ^ j = (2 : ℝ) ^ ((1 - w) * (j : ℝ)) := by
      rw [hrdef, ← Real.rpow_natCast ((2 : ℝ) ^ (1 - w)) j, ← Real.rpow_mul (by norm_num)]
    have hterm : ∀ p ∈ Finset.filter (fun p => Nat.log 2 p = j)
        (Finset.filter (fun p => Nat.Prime p) (Finset.Icc 1 N)),
        Real.log (p : ℝ) * (p : ℝ) ^ (-w)
          ≤ (r ^ j * (2 : ℝ) ^ (-(j : ℝ))) * Real.log (p : ℝ) := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hp1, _⟩, hprime⟩, hlogj⟩ := hp
      have hlow : (2 : ℕ) ^ j ≤ p := by
        rw [← hlogj]
        exact Nat.pow_log_le_self 2 (by omega)
      have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := by
        have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
        exact Real.log_nonneg this
      have hdamp : (p : ℝ) ^ (-w) ≤ (2 : ℝ) ^ (-(w * (j : ℝ))) :=
        rpow_neg_le_block_rpow hlow (by linarith)
      have hsplit : (2 : ℝ) ^ (-(w * (j : ℝ))) = r ^ j * (2 : ℝ) ^ (-(j : ℝ)) := by
        rw [hrj, ← Real.rpow_add (by norm_num : (0 : ℝ) < (2 : ℝ))]
        congr 1
        ring
      calc Real.log (p : ℝ) * (p : ℝ) ^ (-w)
          ≤ Real.log (p : ℝ) * (2 : ℝ) ^ (-(w * (j : ℝ))) :=
            mul_le_mul_of_nonneg_left hdamp hlogp
        _ = (r ^ j * (2 : ℝ) ^ (-(j : ℝ))) * Real.log (p : ℝ) := by rw [hsplit]; ring
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
    have hnn : ∀ p ∈ Nat.primesLE (2 ^ (j + 1)),
        p ∉ Finset.filter (fun p => Nat.log 2 p = j)
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
    have hcoeff0 : (0 : ℝ) ≤ r ^ j * (2 : ℝ) ^ (-(j : ℝ)) := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hθ hcoeff0) (le_of_eq ?_)
    have hpow : ((2 ^ (j + 1) : ℕ) : ℝ) = (2 : ℝ) ^ ((j : ℝ) + 1) := by
      rw [show ((j : ℝ) + 1) = ((j + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      push_cast
      ring
    rw [hpow]
    have hcomb : (2 : ℝ) ^ (-(j : ℝ)) * (2 : ℝ) ^ ((j : ℝ) + 1) = 2 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < (2 : ℝ))]
      norm_num
    calc r ^ j * (2 : ℝ) ^ (-(j : ℝ)) * ((2 : ℝ) ^ ((j : ℝ) + 1) * Real.log 4)
        = (2 : ℝ) ^ (-(j : ℝ)) * (2 : ℝ) ^ ((j : ℝ) + 1) * (r ^ j * Real.log 4) := by ring
      _ = 2 * Real.log 4 * r ^ j := by rw [hcomb]; ring
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hgeo : HasSum (fun j : ℕ => r ^ j) (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr0.le hr1
  refine le_trans (hgeo.summable.sum_le_tsum (Finset.range (Nat.log 2 N + 1))
    (fun j _ => by positivity)) ?_
  rw [hgeo.tsum_eq]

end RHTower.Sieve
end
