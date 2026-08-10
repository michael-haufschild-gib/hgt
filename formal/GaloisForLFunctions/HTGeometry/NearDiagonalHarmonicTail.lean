import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The near-diagonal harmonic band

A weight `c/(I·|n|)` carried by the band `|n| < I` sums to `O(log I / I)` and therefore vanishes.
This is the second region of every near-diagonal tail estimate on the integer lattice: the first
region has a summable weight over an escaping band, this one has a harmonic weight over a band of
width `I` at height `1/I`.

Two auxiliary facts are recorded: a sum over `ℤ` of a function of `|n|` is at most twice the
corresponding sum over `ℕ`, and `(1 + log I)/I → 0`.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions

/-- A sum over `ℤ` of a function of `|n|` is at most twice the sum over `ℕ`. -/
theorem tsum_int_natAbs_le (g : ℕ → ℝ≥0∞) :
    ∑' n : ℤ, g n.natAbs ≤ 2 * ∑' k : ℕ, g k := by
  have hpos : (∑' n : ℤ, if 0 ≤ n then g n.toNat else 0) = ∑' k : ℕ, g k := by
    have hinj : Function.Injective (fun k : ℕ => (k : ℤ)) := by
      intro a b h
      simpa using h
    have hsupp : Function.support (fun n : ℤ => if 0 ≤ n then g n.toNat else 0)
        ⊆ Set.range (fun k : ℕ => (k : ℤ)) := by
      intro n hn
      simp only [Function.mem_support] at hn
      by_cases h : 0 ≤ n
      · exact ⟨n.toNat, by simpa using Int.toNat_of_nonneg h⟩
      · exact absurd (if_neg h) hn
    rw [← hinj.tsum_eq hsupp]
    exact tsum_congr fun k => by simp
  have hneg : (∑' n : ℤ, if n ≤ 0 then g (-n).toNat else 0) = ∑' k : ℕ, g k := by
    have hinj : Function.Injective (fun k : ℕ => -(k : ℤ)) := by
      intro a b h
      simp only [neg_inj] at h
      exact_mod_cast h
    have hsupp : Function.support (fun n : ℤ => if n ≤ 0 then g (-n).toNat else 0)
        ⊆ Set.range (fun k : ℕ => -(k : ℤ)) := by
      intro n hn
      simp only [Function.mem_support] at hn
      by_cases h : n ≤ 0
      · refine ⟨(-n).toNat, ?_⟩
        simp only [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n), neg_neg]
      · exact absurd (if_neg h) hn
    rw [← hinj.tsum_eq hsupp]
    exact tsum_congr fun k => by simp
  have hsplit : ∀ n : ℤ, g n.natAbs ≤
      (if 0 ≤ n then g n.toNat else 0) + (if n ≤ 0 then g (-n).toNat else 0) := by
    intro n
    by_cases h : 0 ≤ n
    · rw [if_pos h, show n.toNat = n.natAbs by omega]
      exact le_add_right le_rfl
    · rw [if_neg h, if_pos (by omega), show (-n).toNat = n.natAbs by omega, zero_add]
  calc ∑' n : ℤ, g n.natAbs
      ≤ ∑' n : ℤ, ((if 0 ≤ n then g n.toNat else 0) + (if n ≤ 0 then g (-n).toNat else 0)) :=
        ENNReal.tsum_le_tsum hsplit
    _ = (∑' n : ℤ, if 0 ≤ n then g n.toNat else 0) +
          ∑' n : ℤ, if n ≤ 0 then g (-n).toNat else 0 := ENNReal.tsum_add
    _ = (∑' k : ℕ, g k) + ∑' k : ℕ, g k := by rw [hpos, hneg]
    _ = 2 * ∑' k : ℕ, g k := by ring

/-- `(1 + log I)/I → 0`. -/
theorem tendsto_one_add_log_div_nat_atTop_zero :
    Tendsto (fun I : ℕ => (1 + Real.log (I : ℝ)) / (I : ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hnat : Tendsto (fun I : ℕ => Real.log (I : ℝ) / (I : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using hlog.comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun I : ℕ => 1 / (I : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsum := hone.add hnat
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with I hI
  have hIpos : (0 : ℝ) < (I : ℝ) := by exact_mod_cast hI
  field_simp

/-- The harmonic partial sum over `range I` is at most `1 + log I`. -/
theorem sum_range_one_div_le_one_add_log (I : ℕ) :
    ∑ k ∈ Finset.range I, 1 / (k : ℝ) ≤ 1 + Real.log (I : ℝ) := by
  have hsubset : Finset.range I ⊆ insert 0 (Finset.Icc 1 I) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨h, by omega⟩)
  have hnonneg : ∀ k ∈ insert 0 (Finset.Icc 1 I), k ∉ Finset.range I → 0 ≤ 1 / (k : ℝ) :=
    fun k _ _ => by positivity
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
  have hins : ∑ k ∈ insert 0 (Finset.Icc 1 I), 1 / (k : ℝ)
      = ∑ k ∈ Finset.Icc 1 I, 1 / (k : ℝ) := by
    rw [Finset.sum_insert (by simp)]
    norm_num
  rw [hins] at hle
  exact hle.trans (RHTower.Sieve.sum_Icc_one_div_le_one_add_log I)

/-- **The near-diagonal harmonic band vanishes** for every weight that beats the harmonic sum.
The band `|n| < I` at height `c/(w I · |n|)` sums to `2c(1 + log I)/w I`. -/
theorem tendsto_tsum_nearDiagonalWeighted_zero {c : ℝ} (hc : 0 ≤ c) {w : ℕ → ℝ}
    (hw : ∀ I : ℕ, 0 ≤ w I)
    (hlim : Tendsto (fun I : ℕ => (1 + Real.log (I : ℝ)) / w I) atTop (nhds 0)) :
    Tendsto (fun I : ℕ => ∑' n : ℤ,
      (if n.natAbs < I then ENNReal.ofReal (c / (w I * (n.natAbs : ℝ))) else 0))
      atTop (nhds 0) := by
  have hbound : ∀ I : ℕ, (∑' n : ℤ,
      (if n.natAbs < I then ENNReal.ofReal (c / (w I * (n.natAbs : ℝ))) else 0))
      ≤ ENNReal.ofReal (2 * (c * ((1 + Real.log (I : ℝ)) / w I))) := by
    intro I
    have hstep := tsum_int_natAbs_le
      (fun k : ℕ => if k < I then ENNReal.ofReal (c / (w I * (k : ℝ))) else 0)
    refine hstep.trans ?_
    have hfin : (∑' k : ℕ, if k < I then ENNReal.ofReal (c / (w I * (k : ℝ))) else 0)
        = ∑ k ∈ Finset.range I, ENNReal.ofReal (c / (w I * (k : ℝ))) := by
      rw [tsum_eq_sum (s := Finset.range I) (fun k hk => by
        rw [if_neg (by simpa using hk)])]
      exact Finset.sum_congr rfl fun k hk => by rw [if_pos (Finset.mem_range.mp hk)]
    rw [hfin]
    have hofReal : ∑ k ∈ Finset.range I, ENNReal.ofReal (c / (w I * (k : ℝ)))
        = ENNReal.ofReal (∑ k ∈ Finset.range I, c / (w I * (k : ℝ))) := by
      refine (ENNReal.ofReal_sum_of_nonneg (fun k _ => ?_)).symm
      exact div_nonneg hc (mul_nonneg (hw I) (Nat.cast_nonneg k))
    rw [hofReal, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have hterm : ∑ k ∈ Finset.range I, c / (w I * (k : ℝ))
        = c / w I * ∑ k ∈ Finset.range I, 1 / (k : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← div_div, div_eq_mul_one_div]
    have hharm := sum_range_one_div_le_one_add_log I
    have hIc : 0 ≤ c / w I := div_nonneg hc (hw I)
    have hkey : ∑ k ∈ Finset.range I, c / (w I * (k : ℝ))
        ≤ c * ((1 + Real.log (I : ℝ)) / w I) := by
      rw [hterm]
      refine (mul_le_mul_of_nonneg_left hharm hIc).trans (le_of_eq ?_)
      ring
    linarith [hkey]
  have hlimit : Tendsto
      (fun I : ℕ => ENNReal.ofReal (2 * (c * ((1 + Real.log (I : ℝ)) / w I))))
      atTop (nhds 0) := by
    have hreal : Tendsto (fun I : ℕ => 2 * (c * ((1 + Real.log (I : ℝ)) / w I)))
        atTop (nhds 0) := by
      have := (hlim.const_mul c).const_mul (2 : ℝ)
      simpa using this
    have hcont := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
    simpa [Function.comp_def] using hcont
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hlimit ε hε] with I hI
  exact (hbound I).trans hI

/-- **The near-diagonal harmonic band vanishes.** -/
theorem tendsto_tsum_nearDiagonal_zero {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun I : ℕ => ∑' n : ℤ,
      (if n.natAbs < I then ENNReal.ofReal (c / ((I : ℝ) * (n.natAbs : ℝ))) else 0))
      atTop (nhds 0) :=
  tendsto_tsum_nearDiagonalWeighted_zero hc (fun I => Nat.cast_nonneg I)
    tendsto_one_add_log_div_nat_atTop_zero

end GaloisForLFunctions
