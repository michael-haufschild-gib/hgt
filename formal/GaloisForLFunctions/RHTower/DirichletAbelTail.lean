import GaloisForLFunctions.RHTower.DirichletAbel
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The Dirichlet series as its Abel tail

Letting the truncation tend to infinity in summation by parts identifies a Dirichlet series with
the series of its partial sums against the increments of `n^{-s}`, provided the boundary term
vanishes and both series converge.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- **A Dirichlet series equals its Abel tail.** -/
theorem tsum_eq_abelTail {c : ℕ → ℂ} {s : ℂ}
    (hL : Summable fun i : ℕ => ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) * c i)
    (hR : Summable fun k : ℕ => coeffPartial c (k + 1)
      * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)))
    (hb : Tendsto (fun n : ℕ => (((n : ℝ)) : ℂ) ^ (-s) * coeffPartial c n) atTop (𝓝 0)) :
    (∑' i : ℕ, ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) * c i)
      = ∑' k : ℕ, coeffPartial c (k + 1)
          * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) := by
  have hLlim : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) * c i) atTop
      (𝓝 (∑' i : ℕ, ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) * c i)) := hL.hasSum.tendsto_sum_nat
  have hRlim : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n - 1), coeffPartial c (k + 1)
      * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s))) atTop
      (𝓝 (∑' k : ℕ, coeffPartial c (k + 1)
        * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)))) :=
    hR.hasSum.tendsto_sum_nat.comp (tendsto_sub_atTop_nat 1)
  have hsum : Tendsto (fun n : ℕ => (((n : ℝ)) : ℂ) ^ (-s) * coeffPartial c n
      + ∑ k ∈ Finset.range (n - 1), coeffPartial c (k + 1)
        * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s))) atTop
      (𝓝 (0 + ∑' k : ℕ, coeffPartial c (k + 1)
        * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)))) := hb.add hRlim
  rw [zero_add] at hsum
  refine tendsto_nhds_unique hLlim ?_
  exact hsum.congr fun n => (sum_eq_abelPartial c s n).symm

end

end RHTower
