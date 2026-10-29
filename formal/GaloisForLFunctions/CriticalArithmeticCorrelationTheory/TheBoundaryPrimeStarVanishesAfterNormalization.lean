import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OnlyTheBoundaryStarEntersAtTouching
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OverlapLengthControlsTheTouchingCrossError

/-!
# The boundary prime star has a vanishing norm budget

The divisor identity pays every weight in the single non-ratio boundary star.
The overlap left at its lag is quadratic in the atom width, so normalization
leaves a prime-source error tending to zero.
-/

noncomputable section

open MeasureTheory Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticEffectivityTheory

private theorem boundary_weight_mass_le (N : ℕ) :
    (∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
      if k * m = N + 1 then vonMangoldtAtom k else 0) ≤ Real.log (N + 1 : ℕ) := by
  classical
  have hpoint : ∀ k ∈ Icc 2 (N + 1), vonMangoldtAtom k ≤ ArithmeticFunction.vonMangoldt k := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k from (by have := (mem_Icc.mp hk).1; omega))
    have hs : 1 ≤ Real.sqrt k := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hk1
    rw [vonMangoldtAtom_eq (mem_Icc.mp hk).1]
    exact div_le_self ArithmeticFunction.vonMangoldt_nonneg hs
  have hfirst : (∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
      if k * m = N + 1 then vonMangoldtAtom k else 0) ≤
      ∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
        if k * m = N + 1 then ArithmeticFunction.vonMangoldt k else 0 := by
    apply sum_le_sum
    intro k hk
    apply sum_le_sum
    intro m hm
    split_ifs <;> [exact hpoint k hk; exact le_rfl]
  have h := sum_sum_vonMangoldt_le (Icc 2 (N + 1)) (Icc 1 N)
    (fun k hk => by have := (mem_Icc.mp hk).1; omega)
    (fun m hm => (mem_Icc.mp hm).1) (fun l => l = N + 1)
  have hsub : (((Icc 2 (N + 1) ×ˢ Icc 1 N).image fun p : ℕ × ℕ => p.1 * p.2).filter
      fun l => l = N + 1) ⊆ {N + 1} := by
    intro l hl
    exact mem_singleton.mpr (mem_filter.mp hl).2
  have hlast := sum_le_sum_of_subset_of_nonneg (f := fun l : ℕ => Real.log l) hsub
    (fun l _ _ => Real.log_natCast_nonneg l)
  simpa only [sum_singleton] using hfirst.trans (h.trans hlast)

/-- The actual boundary correction is controlled by one divisor logarithm. -/
theorem abs_nonRatioForm_at_touching_le {g : ℝ → ℝ} {N : ℕ} (hN : 2 ≤ N)
    (hsupp : ∀ u, u ∉ Set.Icc 0 (1 / (N : ℝ)) → g u = 0) (x : ℕ → ℝ) :
    |nonRatioForm g N x| ≤
      2 * |bumpCorr g (Real.log (N + 1 : ℕ) - Real.log N)| * Real.log (N + 1 : ℕ) *
        ∑ m ∈ Icc 1 N, x m ^ 2 := by
  let S : ℝ := ∑ m ∈ Icc 1 N, x m ^ 2
  have hS : 0 ≤ S := sum_nonneg fun m _ => sq_nonneg _
  have hNmem : N ∈ Icc 1 N := mem_Icc.mpr ⟨by omega, le_rfl⟩
  have hxN : x N ^ 2 ≤ S := single_le_sum (fun m _ => sq_nonneg _) hNmem
  have hpair : ∀ m ∈ Icc 1 N, |x N * x m| ≤ S := by
    intro m hm
    have hxm : x m ^ 2 ≤ S := single_le_sum (fun n _ => sq_nonneg _) hm
    rw [abs_mul]
    nlinarith only [sq_nonneg (|x N| - |x m|), sq_abs (x N), sq_abs (x m), hxN, hxm]
  have hsum : |∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
      if k * m = N + 1 then vonMangoldtAtom k * (x N * x m) else 0| ≤
      Real.log (N + 1 : ℕ) * S := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
          (if k * m = N + 1 then vonMangoldtAtom k else 0) * S := by
        apply sum_le_sum
        intro k hk
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro m hm
        split_ifs
        · rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg' k)]
          exact mul_le_mul_of_nonneg_left (hpair m hm) (vonMangoldtAtom_nonneg' k)
        · simp only [abs_zero, zero_mul, le_refl]
      _ = (∑ k ∈ Icc 2 (N + 1), ∑ m ∈ Icc 1 N,
          if k * m = N + 1 then vonMangoldtAtom k else 0) * S := by
        simp only [sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (boundary_weight_mass_le N) hS
  rw [nonRatioForm_eq_boundary_star hN hsupp x, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by dsimp only [S]; ring)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_nonRatioForm_at_touching_le
