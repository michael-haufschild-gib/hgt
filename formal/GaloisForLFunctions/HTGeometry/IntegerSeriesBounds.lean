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

/-! ## Escaping bands -/

/-- A symmetric band whose radius grows exhausts every finite set. -/
theorem tendsto_finsetIcc_atTop {b : ℕ → ℕ} (hb : Tendsto b atTop atTop) :
    Tendsto (fun I : ℕ => Finset.Icc (-(b I : ℤ)) (b I : ℤ)) atTop atTop := by
  rw [tendsto_atTop]
  intro S
  obtain ⟨M, hM⟩ := (S.image Int.natAbs).exists_le
  have hMle : ∀ x ∈ S, x.natAbs ≤ M := by
    intro x hx
    exact hM _ (Finset.mem_image_of_mem _ hx)
  filter_upwards [hb.eventually_ge_atTop M] with I hI
  intro x hx
  have hxabs : x.natAbs ≤ b I := le_trans (hMle x hx) hI
  have hb' : (x.natAbs : ℤ) ≤ (b I : ℤ) := by exact_mod_cast hxabs
  rw [Finset.mem_Icc]
  omega

/-- **A band escaping to infinity carries vanishing weight.** -/
theorem tendsto_tsum_far_of_ne_top {f : ℤ → ℝ≥0∞} (hf : (∑' j, f j) ≠ ⊤)
    {b : ℕ → ℕ} (hb : Tendsto b atTop atTop) :
    Tendsto (fun I : ℕ => ∑' j : ℤ, if (b I : ℤ) < |j| then f j else 0) atTop (nhds 0) := by
  have hcompl := ENNReal.tendsto_tsum_compl_atTop_zero hf
  have hcomp := hcompl.comp (tendsto_finsetIcc_atTop hb)
  refine hcomp.congr ?_
  intro I
  simp only [Function.comp_def]
  have hset : ∑' (x : {x : ℤ // x ∉ Finset.Icc (-(b I : ℤ)) ((b I : ℤ))}), f (x : ℤ)
      = ∑' j : ℤ,
        Set.indicator (((Finset.Icc (-(b I : ℤ)) ((b I : ℤ)) : Finset ℤ) : Set ℤ)ᶜ) f j :=
    tsum_subtype _ f
  rw [hset]
  refine tsum_congr fun j => ?_
  by_cases hj : (b I : ℤ) < |j|
  · rw [if_pos hj, Set.indicator_of_mem]
    simp only [Set.mem_compl_iff, Finset.coe_Icc, Set.mem_Icc, not_and_or]
    rcases abs_cases j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hj <;> omega
  · rw [if_neg hj, Set.indicator_of_notMem]
    simp only [Set.mem_compl_iff, Finset.coe_Icc, Set.mem_Icc, not_not]
    rcases abs_cases j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hj <;> omega

end GaloisForLFunctions
