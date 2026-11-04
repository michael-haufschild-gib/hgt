import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralUpwardRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.MangoldtIntervalMass

/-!
# Bounded profiles in the literal upward rows

The exact normalized coefficient is bounded by four times the offset
width, profile amplitude and logarithmic multiplier mass. Both signs
and both horizon cutoffs are retained.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- Every bounded profile has a literal upward row controlled by the strip width and its logarithmic multiplier width. -/
theorem abs_logarithmicUpwardProfileCoefficient_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N n : ℕ} (hn : n ∈ Icc 1 N) (hwidth : c / N ≤ 1)
    (hB : linearPrimeStrip c ≤ N)
    (hsep : 2 * c * Real.exp 1 * linearPrimeStrip c ≤ N)
    (F : ℕ → ℝ) {V : ℝ} (hV : 0 ≤ V) (hF : ∀ j, |F j| ≤ V) :
    |logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N F n| ≤
      4 * (linearPrimeStrip c : ℝ) * V *
        (|Real.log (2 * c * Real.exp 1)| + mertensWindowConstant + 1) := by
  have hn1 := (mem_Icc.mp hn).1
  have hN : 1 ≤ N := hn1.trans (mem_Icc.mp hn).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  let H : ℕ := ⌈(N : ℝ) / (c * Real.exp 1 * n)⌉₊
  let X : ℕ := ⌊((N : ℝ) + linearPrimeStrip c) / n⌋₊
  let W : ℝ := |Real.log (2 * c * Real.exp 1)| + mertensWindowConstant + 1
  have hH0 : (0 : ℝ) < H :=
    (div_pos hN0 (mul_pos (mul_pos hc (Real.exp_pos 1)) hn0)).trans_le (Nat.le_ceil _)
  have hH : 1 ≤ H := by exact_mod_cast hH0
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact add_nonneg (add_nonneg (abs_nonneg _) mertensWindowConstant_nonneg) zero_le_one
  have hlog : H ≤ X → Real.log X - Real.log H + mertensWindowConstant + 1 ≤ W := by
    intro hHX
    have h := (multiplier_interval_log_width hc hN hn1 hB hHX rfl rfl).2
    have h' := h.trans (le_abs_self (Real.log (2 * c * Real.exp 1)))
    dsimp only [W]
    linarith only [h']
  have hU : 0 ≤ 2 * ∫ u, φ u ^ 2 := mul_nonneg zero_le_two hM.le
  have hbound (T : ℕ → ℕ → ℕ) (K : ℕ → ℕ → ℝ)
      (hK : ∀ k ∈ Icc 1 (N + linearPrimeStrip c), ∀ h ∈ Icc 1 (linearPrimeStrip c),
        |K k h| ≤ 2 * ∫ u, φ u ^ 2)
      (hKs : ∀ k ∈ Icc 1 (N + linearPrimeStrip c), ∀ h ∈ Icc 1 (linearPrimeStrip c),
        K k h ≠ 0 → k ∈ Icc H X) :
      |∑ k ∈ Icc 1 (N + linearPrimeStrip c), (ArithmeticFunction.vonMangoldt k : ℝ) / k *
        ∑ h ∈ Icc 1 (linearPrimeStrip c), F (T k h) * K k h| ≤
      (linearPrimeStrip c : ℝ) * (V * (2 * ∫ u, φ u ^ 2)) * W := by
    apply double_mangoldt_supported_sum_le hH (fun k h => F (T k h) * K k h)
      (mul_nonneg hV hU) hW
    · intro k hk h hh
      rw [abs_mul]
      exact mul_le_mul (hF _) (hK k hk h hh) (abs_nonneg _) hV
    · intro k hk h hh hne
      apply hKs k hk h hh
      intro hz
      exact hne (by rw [hz, mul_zero])
    · exact hlog
  have hp : |positiveLiteralUpwardRow φ c (linearPrimeStrip c) N F n| ≤
      (linearPrimeStrip c : ℝ) * (V * (2 * ∫ u, φ u ^ 2)) * W := by
    exact hbound (fun k h => k * n + h) (fun k h => positiveLiteralUpwardKernel φ c N k h n)
      (fun k hk h hh => (abs_literalUpwardKernels_le_of_separation hφ hsupp hc hN
        (mem_Icc.mp hk).1 hh hn1 hwidth hsep).1)
      (fun k hk h hh hker => positiveLiteralUpwardKernel_support hφ hsupp hc hN
        (mem_Icc.mp hk).1 (mem_Icc.mp hh).1 hn1 hwidth hker)
  have hm : |negativeLiteralUpwardRow φ c (linearPrimeStrip c) N F n| ≤
      (linearPrimeStrip c : ℝ) * (V * (2 * ∫ u, φ u ^ 2)) * W := by
    exact hbound (fun k h => k * n - h) (fun k h => negativeLiteralUpwardKernel φ c N k h n)
      (fun k hk h hh => (abs_literalUpwardKernels_le_of_separation hφ hsupp hc hN
        (mem_Icc.mp hk).1 hh hn1 hwidth hsep).2)
      (fun k hk h hh hker => negativeLiteralUpwardKernel_support hφ hsupp hc hN
        (mem_Icc.mp hk).1 (mem_Icc.mp hh).1 hn1 hwidth hker)
  rw [logarithmicUpwardProfileCoefficient_eq_rows, abs_div, abs_of_pos hM]
  apply (div_le_iff₀ hM).mpr
  exact ((abs_add_le _ _).trans (add_le_add hp hm)).trans_eq (by dsimp only [W]; ring)

#print axioms abs_logarithmicUpwardProfileCoefficient_le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
