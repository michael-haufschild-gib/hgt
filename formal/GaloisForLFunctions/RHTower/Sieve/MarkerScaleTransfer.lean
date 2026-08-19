import GaloisForLFunctions.RHTower.Sieve.GoodStartFibreWindow

/-!
# The marker-scale lifting device

An "almost all starts" statement transfers to "almost all markers" only as well as the markers are
spread over the starts.  If the markers are the primes near `√x`, each cofactor start carries `O(1)`
*integers* and hence a marker only with probability `1/log x`, so an exceptional set of starts of
density `ρ` can destroy a `ρ·log x` fraction of the markers.  Lifting the marker scale to
`√x·√(log x)` puts `≍ log x` integers — hence `≍ 1` primes — over each start, and the loss becomes
`√ρ` by Cauchy–Schwarz against the second moment of the per-start marker count.

Collected here are the two combinatorial halves of that device: the Cauchy–Schwarz transfer, and the
fact that above the lifted scale every start is realised by an integer outer factor, so that the
corpus's fibre statements apply to it.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The Cauchy–Schwarz transfer.**  The marker count over an exceptional set of starts is
controlled by the size of that set and the second moment of the per-start count. -/
theorem sq_sum_subset_le_card_mul_sumSq {ι : Type*} [DecidableEq ι] {S B : Finset ι}
    (hBS : B ⊆ S) (π : ι → ℝ) :
    (∑ i ∈ B, π i) ^ 2 ≤ (B.card : ℝ) * ∑ i ∈ S, (π i) ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ => (1 : ℝ)) π
  simp only [one_mul, one_pow] at hcs
  have hcard : (∑ _i ∈ B, (1 : ℝ)) = (B.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcard] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  exact Finset.sum_le_sum_of_subset_of_nonneg hBS (fun i _ _ => by positivity)

/-- **Every start is realised above the lifted scale.**  If `t(t+1) ≤ x` then some integer outer
factor has `t` as its fibre start. -/
theorem exists_start_preimage {x : ℝ} {t : ℕ} (ht : 1 ≤ t) (hx : ((t : ℝ) + 1) * (t : ℝ) ≤ x) :
    ∃ a : ℕ, 1 ≤ a ∧ x / ((t : ℝ) + 1) ≤ (a : ℝ) ∧ (a : ℝ) < x / (t : ℝ) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by linarith
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by positivity) hx
  set a : ℕ := ⌈x / ((t : ℝ) + 1)⌉₊ with ha
  have hlow : x / ((t : ℝ) + 1) ≤ (a : ℝ) := Nat.le_ceil _
  have hgap : x / (t : ℝ) - x / ((t : ℝ) + 1) = x / ((t : ℝ) * ((t : ℝ) + 1)) := by
    field_simp
    ring
  have hone : (1 : ℝ) ≤ x / ((t : ℝ) * ((t : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hx]
  have hhigh : (a : ℝ) < x / (t : ℝ) := by
    have hceil := Nat.ceil_lt_add_one (le_of_lt (div_pos hx0 ht1))
    rw [← ha] at hceil
    have : x / ((t : ℝ) + 1) + 1 ≤ x / (t : ℝ) := by
      rw [← sub_nonneg]
      have : x / (t : ℝ) - (x / ((t : ℝ) + 1) + 1) = x / ((t : ℝ) * ((t : ℝ) + 1)) - 1 := by
        rw [← hgap]; ring
      rw [this]
      linarith
    linarith
  have ha1 : 1 ≤ a := by
    refine Nat.one_le_ceil_iff.2 ?_
    positivity
  exact ⟨a, ha1, hlow, hhigh⟩

/-- **The realised outer factor has the prescribed start.** -/
theorem fibreStartIdx_eq_of_start_interval {x : ℝ} {t a : ℕ} (ht : 1 ≤ t) (ha : 1 ≤ a)
    (hlow : x / ((t : ℝ) + 1) ≤ (a : ℝ)) (hhigh : (a : ℝ) < x / (t : ℝ)) :
    fibreStartIdx x a = t := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hx0 : (0 : ℝ) < x := by
    have := mul_lt_mul_of_pos_right hhigh ht0
    rw [div_mul_cancel₀ _ (ne_of_gt ht0)] at this
    nlinarith [this, ha0, ht0]
  have hup : x / (a : ℝ) ≤ (t : ℝ) + 1 := by
    rw [div_le_iff₀ ha0]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < (t : ℝ) + 1)] at hlow
    linarith [hlow]
  have hdown : (t : ℝ) < x / (a : ℝ) := by
    rw [lt_div_iff₀ ha0]
    rw [lt_div_iff₀ ht0] at hhigh
    linarith [hhigh]
  have hceil : ⌈x / (a : ℝ)⌉₊ = t + 1 := by
    refine Nat.ceil_eq_iff (by omega) |>.2 ⟨?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      exact hup
  rw [fibreStartIdx, hceil]
  omega

end

end RHTower.Sieve
