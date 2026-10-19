import GaloisForLFunctions.BiScaleUncertainty.PrimeAnchorCompleteGraphError
import GaloisForLFunctions.BiScaleUncertainty.PrimeClockGraphTailTightness
import GaloisForLFunctions.RHTower.Sieve.GrahamMeanSquare

/-!
# Growing-horizon costs for arithmetic clock recovery

At a fixed cutoff the complete clock curve is uniformly bounded. Finite
multiples inversion therefore costs at most `B * N * sqrt N * H_N` per
unit coordinate error. Möbius and BV reference norms retain their harmonic
and logarithmic factors. No cancellation estimate is used.
-/

open Finset Set RHTower RHTower.Sieve RHTower.CHMDDoobGraph
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BiScaleUncertainty.PrimeAnchor
noncomputable section
set_option autoImplicit false

def harmonicBudget (N : ℕ) : ℝ := ∑ d ∈ Icc 1 N, (1 : ℝ) / d

theorem exists_curve_bound (k : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ t, ‖PrimeClock.curve k t‖ ≤ B := by
  obtain ⟨C, hC⟩ := (PrimeClock.isCompact_zero_range k).isBounded.exists_norm_le
  refine ⟨|C|+1, by positivity, fun t => ?_⟩
  have h := hC _ (mem_insert_of_mem _ ⟨t, rfl⟩)
  exact h.trans (by linarith [le_abs_self C])

theorem synthesis_norm_le_weighted (N k : ℕ) (c : ℕ → ℝ) (B : ℝ)
    (hB : ∀ t, ‖PrimeClock.curve k t‖ ≤ B) :
    ‖synthesis N k c‖ ≤ B * Real.sqrt N * ∑ d ∈ Icc 1 N, |c d| / d := by
  unfold synthesis
  calc
    _ ≤ ∑ d ∈ Icc 1 N, ‖c d • canonicalPrimeGraphClockAtom k N d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Icc 1 N, B * Real.sqrt N * (|c d| / d) := by
      apply sum_le_sum
      intro d _
      rw [norm_smul, Real.norm_eq_abs, PrimeClock.atom_norm]
      have h := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hB (Real.log ((N : ℝ) / d)))
          (div_nonneg (Real.sqrt_nonneg (N : ℝ)) (Nat.cast_nonneg d))) (abs_nonneg (c d))
      convert h using 1
      ring
    _ = _ := by rw [← mul_sum]

theorem inversionCost_one_le_harmonic (N k : ℕ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t, ‖PrimeClock.curve k t‖ ≤ B) :
    inversionCost N k (fun _ => 1) ≤ B * N * Real.sqrt N * harmonicBudget N := by
  unfold inversionCost harmonicBudget
  simp only [mul_one]
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  have hdpos : 0 < d := (mem_Icc.mp hd).1
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hA : (d : ℝ) * ‖canonicalPrimeGraphClockAtom k N d‖ ≤ B * Real.sqrt N := by
    rw [PrimeClock.atom_norm]
    calc
      _ = Real.sqrt N * ‖PrimeClock.curve k (Real.log ((N : ℝ) / d))‖ := by
        field_simp [hd0]
      _ ≤ Real.sqrt N * B := mul_le_mul_of_nonneg_left (hB _) (Real.sqrt_nonneg (N : ℝ))
      _ = _ := mul_comm _ _
  have hcount : (∑ m ∈ Icc 1 (N/d), |(μ m : ℝ)|) ≤ ((N/d : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ m ∈ Icc 1 (N/d), (1 : ℝ) := sum_le_sum fun m _ => abs_moebius_le_one m
      _ = _ := by simp
  have hS : (∑ m ∈ Icc 1 (N/d), |(μ m : ℝ)|) ≤ (N : ℝ) / d :=
    hcount.trans Nat.cast_div_le
  have h := mul_le_mul hA hS (sum_nonneg fun _ _ => abs_nonneg _)
    (mul_nonneg hB0 (Real.sqrt_nonneg (N : ℝ)))
  convert h using 1
  ring

theorem synthesis_norm_le_harmonic (N k : ℕ) (c : ℕ → ℝ) (A B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ t, ‖PrimeClock.curve k t‖ ≤ B)
    (hc : ∀ d ∈ Finset.Icc 1 N, |c d| ≤ A) :
    ‖synthesis N k c‖ ≤ B * Real.sqrt N * A * harmonicBudget N := by
  have hw : (∑ d ∈ Icc 1 N, |c d| / (d : ℝ)) ≤ A * harmonicBudget N := by
    unfold harmonicBudget
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    simpa only [mul_one_div] using
      div_le_div_of_nonneg_right (hc d hd) (Nat.cast_nonneg d)
  have hh := mul_le_mul_of_nonneg_left hw (mul_nonneg hB0 (Real.sqrt_nonneg (N : ℝ)))
  exact (synthesis_norm_le_weighted N k c B hB).trans (by simpa only [mul_assoc] using hh)

/-- One cutoff constant controls every horizon and both literal arithmetic families. -/
theorem exists_arithmetic_horizon_budget (k : ℕ) : ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ,
    inversionCost N k (fun _ => 1) ≤ B * N * Real.sqrt N * harmonicBudget N ∧
    ‖synthesis N k (fun d => (μ d : ℝ))‖ ≤ B * Real.sqrt N * harmonicBudget N ∧
    ∀ X : ℕ, 1 ≤ X → ‖synthesis N k (barbanVehovWeight X)‖ ≤
      B * Real.sqrt N * Real.log X * harmonicBudget N := by
  obtain ⟨B, hB0, hB⟩ := exists_curve_bound k
  refine ⟨B, hB0, fun N => ⟨inversionCost_one_le_harmonic N k B hB0.le hB, ?_, ?_⟩⟩
  · simpa only [mul_one] using synthesis_norm_le_harmonic N k (fun d => (μ d : ℝ))
      1 B hB0.le hB (fun d _ => abs_moebius_le_one d)
  · intro X hX
    exact synthesis_norm_le_harmonic N k (barbanVehovWeight X) (Real.log X) B hB0.le hB
      (fun _ _ => abs_barbanVehovWeight_le hX)

end
end GaloisForLFunctions.BiScaleUncertainty.PrimeAnchor
