import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The quadratic weight on the integer lattice

The weight `1/(1 + |j|)²` is summable over `ℤ`, its `ℝ≥0∞` total is finite, and therefore its
tails outside a finite band are arbitrarily small.  This is the `i`-independent part of every
band-split estimate on the frequency lattice.

Summability is obtained by comparison with the half-integer shifted series `1/|j + 1/2|²`, which
never meets its own singularity.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions

theorem abs_int_add_half_pos (j : ℤ) : 0 < |(j : ℝ) + 1 / 2| := by
  rw [abs_pos]
  intro h
  have h2 : (2 * j : ℤ) = -1 := by
    have hR : (2 * (j : ℝ)) = -1 := by linarith
    exact_mod_cast hR
  omega

/-- **The quadratic integer weight is summable.** -/
theorem summable_one_div_one_add_abs_sq :
    Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := by
  have hbase : Summable (fun j : ℤ => 1 / |(j : ℝ) + (1 / 2 : ℝ)| ^ (2 : ℝ)) :=
    (Real.summable_one_div_int_add_rpow (1 / 2) 2).mpr (by norm_num)
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hbase
  have hpos : 0 < |(j : ℝ) + 1 / 2| := abs_int_add_half_pos j
  have hle : |(j : ℝ) + 1 / 2| ≤ 1 + |(j : ℝ)| := by
    rcases abs_cases ((j : ℝ) + 1 / 2) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases abs_cases ((j : ℝ)) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
        rw [h1, h2] <;> linarith
  have hrpow : |(j : ℝ) + 1 / 2| ^ (2 : ℝ) = |(j : ℝ) + 1 / 2| ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hrpow]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact pow_le_pow_left₀ hpos.le hle 2

/-- The quadratic integer weight, valued in `ℝ≥0∞`. -/
noncomputable def intQuadWeight (j : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (1 + |(j : ℝ)|) ^ 2)

/-- The total quadratic weight is finite. -/
theorem tsum_intQuadWeight_ne_top : (∑' j : ℤ, intQuadWeight j) ≠ ⊤ := by
  have hsummable : Summable (fun j : ℤ => (1 / (1 + |(j : ℝ)|) ^ 2).toNNReal) := by
    rw [← NNReal.summable_coe]
    refine summable_one_div_one_add_abs_sq.congr fun j => ?_
    rw [Real.coe_toNNReal _ (by positivity)]
  have hrepr : (∑' j : ℤ, intQuadWeight j)
      = ∑' j : ℤ, (((1 / (1 + |(j : ℝ)|) ^ 2).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hrepr]
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hsummable

theorem tsum_const_mul_intQuadWeight_ne_top {C : ℝ≥0∞} (hC : C ≠ ⊤) :
    (∑' j : ℤ, C * intQuadWeight j) ≠ ⊤ := by
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top hC tsum_intQuadWeight_ne_top

/-- **Uniformly small tails.**  Outside a large enough finite band the weighted series
contributes at most `ε`. -/
theorem exists_finset_tsum_compl_intQuadWeight_le {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ S : Finset ℤ, ∑' j : {x : ℤ // x ∉ S}, C * intQuadWeight (j : ℤ) ≤ ε := by
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero (tsum_const_mul_intQuadWeight_ne_top hC)
  obtain ⟨S, hS⟩ := (ENNReal.tendsto_nhds_zero.mp htail ε hε).exists
  exact ⟨S, hS⟩

end GaloisForLFunctions
