import GaloisForLFunctions.RHTower.Sieve.PrimeBlockTwistBound
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange
import GaloisForLFunctions.RHTower.Sieve.PerronNearDiagonal
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The reciprocal-weighted prime cosine sum over a range, from its partial sums

Granville and Soundararajan's device for the pretentious distance discards every prime below a
cutoff and keeps only the tail, where the twisted prime sum has genuine cancellation.  The passage
from cancellation in `∑_{y<p≤u} p^{it}` to cancellation in `∑_{y<p≤z} cos(t log p)/p` is one Abel
summation against the reciprocal weight, and it costs a single logarithm:

    a uniform bound `|∑_{y<p≤u} p^{it}| ≤ ρ·u` for all `u ≤ z`
      ⟹  `|∑_{y<p≤z} cos(t log p)/p| ≤ ρ·(2 + log z)` .

So a relative saving better than `1/log z` in the twisted prime sum makes the tail cosine sum
bounded, which is exactly what the distance bound consumes.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **Abel summation against the reciprocal weight.**  A linear bound for the partial sums
gives a logarithmic bound for the reciprocal-weighted sum. -/
theorem abs_sum_div_le_of_partial_bound {a : ℕ → ℝ} (ha0 : a 0 = 0) {z : ℕ} (hz : 0 < z)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hA : ∀ i, i ≤ z → |∑ j ∈ Finset.range (i + 1), a j| ≤ ρ * (i : ℝ)) :
    |∑ i ∈ Finset.Icc 1 z, a i / (i : ℝ)| ≤ ρ * (2 + Real.log (z : ℝ)) := by
  classical
  have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hz0 : (0 : ℝ) < (z : ℝ) := by linarith
  rw [RHTower.abel_tail_identity a ha0 z hz]
  have hhead : |(∑ i ∈ Finset.range (z + 1), a i) / (z : ℝ)| ≤ ρ := by
    rw [abs_div, abs_of_pos hz0, div_le_iff₀ hz0]
    exact hA z le_rfl
  have hterm : ∀ i ∈ Finset.Icc 1 (z - 1),
      |(∑ j ∈ Finset.range (i + 1), a j) / ((i : ℝ) * ((i : ℝ) + 1))| ≤ ρ * (1 / (i : ℝ)) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have hi1 : 1 ≤ i := hi.1
    have hiz : i ≤ z := by omega
    have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
    have hi0 : (0 : ℝ) < (i : ℝ) := by linarith
    have hden : (0 : ℝ) < (i : ℝ) * ((i : ℝ) + 1) := by positivity
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
    have hbd := hA i hiz
    have hstep : ρ * (1 / (i : ℝ)) * ((i : ℝ) * ((i : ℝ) + 1)) = ρ * ((i : ℝ) + 1) := by
      field_simp
    rw [hstep]
    nlinarith [hbd, hρ, hi0]
  have htail : |∑ i ∈ Finset.Icc 1 (z - 1),
      (∑ j ∈ Finset.range (i + 1), a j) / ((i : ℝ) * ((i : ℝ) + 1))|
      ≤ ρ * (1 + Real.log (z : ℝ)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hρ
    have hsub : ∑ i ∈ Finset.Icc 1 (z - 1), 1 / ((i : ℕ) : ℝ) ≤ 1 + Real.log (z : ℝ) := by
      refine sum_inv_comp_le_one_add_log (φ := id) (L := z) ?_ ?_
      · intro x _ y _ h; exact h
      · intro x hx
        rw [Finset.mem_Icc] at hx
        rw [Finset.mem_Icc]
        exact ⟨hx.1, by omega⟩
    exact hsub
  have := abs_add (((∑ i ∈ Finset.range (z + 1), a i) / (z : ℝ)))
    (∑ i ∈ Finset.Icc 1 (z - 1), (∑ j ∈ Finset.range (i + 1), a j) / ((i : ℝ) * ((i : ℝ) + 1)))
  linarith [this, hhead, htail]

/-- The tail cosine weight: the cosine at the primes above the cutoff, zero elsewhere. -/
def primeCosTail (y : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  if i.Prime ∧ y < i then Real.cos (t * Real.log (i : ℝ)) else 0

theorem primeCosTail_zero (y : ℕ) (t : ℝ) : primeCosTail y t 0 = 0 := by
  rw [primeCosTail, if_neg]
  rintro ⟨h, -⟩
  exact absurd h (by norm_num)

/-- The partial sums of the tail weight are the prime cosine sums over the range. -/
theorem sum_range_primeCosTail (y : ℕ) (t : ℝ) (i : ℕ) :
    ∑ j ∈ Finset.range (i + 1), primeCosTail y t j
      = ∑ p ∈ primesRange y i, Real.cos (t * Real.log (p : ℝ)) := by
  classical
  refine (Finset.sum_subset ?_ ?_).symm
  · intro p hp
    rw [mem_primesRange] at hp
    rw [Finset.mem_range]
    omega
  · intro j _ hj
    rw [primeCosTail, if_neg]
    intro hcon
    exact hj (mem_primesRange.2 ⟨hcon.1, hcon.2, by
      have : j ∈ Finset.range (i + 1) := by
        by_contra hc
        exact hj (by
          exfalso
          exact hc (by
            rw [Finset.mem_range]
            omega))
      rw [Finset.mem_range] at this
      omega⟩)

end

end RHTower.Sieve
