import GaloisForLFunctions.RHTower.PrimeLagLandauPrimesOnly
import GaloisForLFunctions.RHTower.MertensSecondPrimeRecipSum
import GaloisForLFunctions.HTGeometry.HarmonicResidueShift

/-! # Prime powers have zero harmonic logarithmic density

Proper prime powers have summable reciprocal weights. The prime contribution
has only double-logarithmic growth, so the entire prime-power harmonic mass
vanishes after logarithmic normalization, including every fixed index shift.
-/

namespace RHTower
noncomputable section
open Filter GaloisForLFunctions
open scoped Topology

theorem summable_properPrimePow_reciprocal :
    Summable (fun n : ℕ => if IsProperPrimePow n then (n : ℝ)⁻¹ else 0) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ((summable_properPrimePow_log_rpow (x := 1) (by norm_num)).mul_left
    (Real.log 2)⁻¹).of_nonneg_of_le (fun n => by split_ifs <;> positivity) ?_
  intro n
  by_cases hn : IsProperPrimePow n
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1.one_lt
    have hb : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
    simp only [if_pos hn, properLogTerm, Real.rpow_neg_one]
    calc
      (n : ℝ)⁻¹ = ((Real.log 2)⁻¹ * Real.log 2) * (n : ℝ)⁻¹ := by rw [inv_mul_cancel₀ hlog.ne', one_mul]
      _ ≤ ((Real.log 2)⁻¹ * Real.log n) * (n : ℝ)⁻¹ := by gcongr
      _ = _ := mul_assoc _ _ _
  · simp [hn, properLogTerm]

theorem tendsto_primeRecipSum_div_log_succ :
    Tendsto (fun N : ℕ => primeRecipSum N / Real.log (N + 1)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (tendsto_primeRecipSum_sub_logLog.div_atTop hlog).add
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog)
  have hz : Tendsto (fun N : ℕ => primeRecipSum N / Real.log (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, sub_div, sub_add_cancel, zero_add] using h
  have ht := hz.mul (tendsto_log_nat_add_div_log_nat_add 0 1)
  rw [zero_mul] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  simp only [Nat.cast_zero, Nat.cast_one, add_zero]
  field_simp

theorem tendsto_primePow_reciprocal_sum_div_log :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, if IsPrimePow n then (n : ℝ)⁻¹ else 0) /
        Real.log (N + 1)) atTop (𝓝 0) := by
  have hproper := summable_properPrimePow_reciprocal.hasSum.tendsto_sum_nat
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1 : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hupper := tendsto_primeRecipSum_div_log_succ.add (hproper.div_atTop hlog)
  simp only [zero_add] at hupper
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards with N
    apply div_nonneg
    · exact Finset.sum_nonneg fun n _ => by split_ifs <;> positivity
    · exact Real.log_nonneg (by norm_cast; omega)
  · filter_upwards with N
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_cast; omega))
    have hsplit : (∑ n ∈ Finset.range N, if IsPrimePow n then (n : ℝ)⁻¹ else 0) =
        (∑ n ∈ Finset.range N, primeRecipWeight n) +
        ∑ n ∈ Finset.range N, if IsProperPrimePow n then (n : ℝ)⁻¹ else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hp : n.Prime
      · simp [primeRecipWeight, IsProperPrimePow, hp, hp.isPrimePow]
      · simp [primeRecipWeight, IsProperPrimePow, hp]
    rw [hsplit]
    apply add_le_add _ le_rfl
    change (∑ n ∈ Finset.range N, primeRecipWeight n) ≤ ∑ n ∈ Finset.Icc 0 N, primeRecipWeight n
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_range.mp hn).le⟩
    · intro n _ _
      dsimp [primeRecipWeight]
      split_ifs <;> positivity

theorem tendsto_primePow_reciprocal_shift_sum_div_log (k : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, if IsPrimePow (n + k) then ((n + k : ℕ) : ℝ)⁻¹ else 0) /
        Real.log (N + 1)) atTop (𝓝 0) :=
  tendsto_logResidue_shift tendsto_primePow_reciprocal_sum_div_log k

end
end RHTower
