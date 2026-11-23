import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # A summable majorant from finite interlacing

The drop across r consecutive positions of a decreasing sequence tending
to zero is summable, even when the sequence itself is not.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- The sum of r-step drops equals the first r entries. -/
theorem hasSum_shift_drop {a : ℕ → ℝ} (ha : Antitone a) (h0 : Tendsto a atTop (𝓝 0)) (r : ℕ) :
    HasSum (fun n => a n-a (n+r)) (∑ j ∈ Finset.range r, a j) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => sub_nonneg.mpr (ha (Nat.le_add_right n r)))]
  have hsum (N : ℕ) : (∑ n ∈ Finset.range N, (a n-a (n+r))) =
      (∑ j ∈ Finset.range r, a j)-∑ j ∈ Finset.range r, a (N+j) := by
    have hn := Finset.sum_range_add a N r
    have hr := Finset.sum_range_add a r N
    rw [Nat.add_comm r N] at hr
    rw [Finset.sum_sub_distrib]
    simp only [Nat.add_comm r] at hr
    linarith only [hn,hr]
  have ht (j : ℕ) : Tendsto (fun N => a (N+j)) atTop (𝓝 0) :=
    h0.comp (tendsto_add_atTop_nat j)
  have tail := tendsto_finsetSum (Finset.range r) (fun j _ => ht j)
  simp only [Finset.sum_const_zero] at tail
  simpa only [funext hsum,sub_zero] using
    (tendsto_const_nhds (x := ∑ j ∈ Finset.range r, a j)).sub tail

#print axioms hasSum_shift_drop

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
