import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenGeometricTypeIIData

/-!
# Multiplicative real-scale support

Proposition 2.2 packages convolution factors by exact half-open real intervals.  These lemmas
compose such supports through Dirichlet convolution and remove redundant interval restrictions.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- An arithmetic function is supported on positive natural indices in `(L,U]`. -/
def MTRealScaleSupported (F : ArithmeticFunction ℂ) (L U : ℝ) : Prop :=
  ∀ {n : ℕ}, F n ≠ 0 → 0 < n ∧ L < (n : ℝ) ∧ (n : ℝ) ≤ U

theorem mtRealIntervalAF_scaleSupported
    (alpha : ℕ → ℂ) (L U : ℝ) :
    MTRealScaleSupported (mtRealIntervalAF alpha L U) L U := by
  intro n hn
  have hnPos : 0 < n := by
    by_contra h
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    simp [mtRealIntervalAF] at hn
  rw [mtRealIntervalAF_apply_of_pos _ _ _ hnPos] at hn
  by_cases hmem : L < (n : ℝ) ∧ (n : ℝ) ≤ U
  · exact ⟨hnPos, hmem⟩
  · simp [hmem] at hn

/-- Multiplicative interval supports multiply under Dirichlet convolution. -/
theorem MTRealScaleSupported.mul
    {F G : ArithmeticFunction ℂ} {L1 U1 L2 U2 : ℝ}
    (hF : MTRealScaleSupported F L1 U1)
    (hG : MTRealScaleSupported G L2 U2)
    (_hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) :
    MTRealScaleSupported (F * G) (L1 * L2) (U1 * U2) := by
  intro n hn
  rw [ArithmeticFunction.mul_apply] at hn
  obtain ⟨de, hde, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hFn : F de.1 ≠ 0 := by
    intro hzero
    simp [hzero] at hterm
  have hGn : G de.2 ≠ 0 := by
    intro hzero
    simp [hzero] at hterm
  have hFs := hF hFn
  have hGs := hG hGn
  have hprodNat : de.1 * de.2 = n := (Nat.mem_divisorsAntidiagonal.mp hde).1
  have hprodReal : (de.1 : ℝ) * (de.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast hprodNat
  have hlower : L1 * L2 < (de.1 : ℝ) * (de.2 : ℝ) := by
    calc
      L1 * L2 ≤ (de.1 : ℝ) * L2 :=
        mul_le_mul_of_nonneg_right hFs.2.1.le hL2
      _ < (de.1 : ℝ) * (de.2 : ℝ) :=
        mul_lt_mul_of_pos_left hGs.2.1 (by exact_mod_cast hFs.1)
  have hU1 : 0 ≤ U1 := (Nat.cast_nonneg de.1).trans hFs.2.2
  have hupper : (de.1 : ℝ) * (de.2 : ℝ) ≤ U1 * U2 :=
    mul_le_mul hFs.2.2 hGs.2.2 (Nat.cast_nonneg _) hU1
  exact ⟨hprodNat ▸ Nat.mul_pos hFs.1 hGs.1,
    by simpa [hprodReal] using hlower, by simpa [hprodReal] using hupper⟩

/-- A supported arithmetic function equals its own exact interval restriction. -/
theorem mtRealIntervalAF_coe_eq_of_scaleSupported
    {F : ArithmeticFunction ℂ} {L U : ℝ}
    (hF : MTRealScaleSupported F L U) :
    mtRealIntervalAF (fun n => F n) L U = F := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp [mtRealIntervalAF]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    rw [mtRealIntervalAF_apply_of_pos _ _ _ hnPos]
    by_cases hzero : F n = 0
    · simp [hzero]
    · have hs := hF hzero
      simp [hs.2.1, hs.2.2]

/-- Block indicators inherit any supplied exact real support. -/
theorem mtPrimeBlockAF_scaleSupported
    {S : Finset ℕ} {L U : ℝ}
    (hS : ∀ q ∈ S, L < (q : ℝ) ∧ (q : ℝ) ≤ U) :
    MTRealScaleSupported (mtPrimeBlockAF S) L U := by
  intro n hn
  have hnPos : 0 < n := by
    by_contra h
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    simp at hn
  rw [mtPrimeBlockAF_apply_of_pos S hnPos] at hn
  have hnMem : n ∈ S := by
    by_contra hnot
    simp [hnot] at hn
  exact ⟨hnPos, hS n hnMem⟩

theorem mtCoefficientConvolution_eq_arithmeticFunction_mul
    (F G : ArithmeticFunction ℂ) :
    mtCoefficientConvolution (fun n => F n) (fun n => G n) =
      fun n => (F * G) n := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [mtCoefficientConvolution]
  · rw [ArithmeticFunction.mul_apply]
    exact (Nat.sum_divisorsAntidiagonal (M := ℂ) (n := n)
      (fun d e => F d * G e)).symm

/-- Divisor-bounded arithmetic-function coefficients are closed under Dirichlet convolution. -/
theorem MTPolynomialDivisorBounded.arithmeticFunction_mul
    {F G : ArithmeticFunction ℂ}
    (hF : MTPolynomialDivisorBounded (fun n => F n))
    (hG : MTPolynomialDivisorBounded (fun n => G n)) :
    MTPolynomialDivisorBounded (fun n => (F * G) n) := by
  rw [← mtCoefficientConvolution_eq_arithmeticFunction_mul]
  exact hF.convolution hG

/-- Multiplication by a fixed scalar preserves a divisor bound. -/
theorem MTPolynomialDivisorBounded.smul
    {alpha : ℕ → ℂ} (halpha : MTPolynomialDivisorBounded alpha) (c : ℂ) :
    MTPolynomialDivisorBounded (fun n => c * alpha n) := by
  obtain ⟨C, hC, K, hbound⟩ := halpha
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, K, ?_⟩
  intro n hn
  rw [norm_mul]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (hbound hn) (norm_nonneg c)

end

end RHTower.Sieve
