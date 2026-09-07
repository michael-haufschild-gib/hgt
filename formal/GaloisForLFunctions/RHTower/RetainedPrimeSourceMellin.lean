import GaloisForLFunctions.RHTower.RetainedPrimeDivisorConvolution
import GaloisForLFunctions.RHTower.SquareRootSummatoryMellin

/-!
# Mellin representation of finite retained sources

The actual retained divisor convolution has summatory norm at most its finite
coordinate norm times `24*N^(3/2)`. The continuous square-root primitive
therefore has the exact completed-source Mellin transform on `Re s > 2`,
with absolute convergence and no assumed source-growth estimate.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped BigOperators
namespace RHTower

/-- Uniform summatory control of every finite retained-functional convolution.
The constant depends only on the finite coordinate norm, not on the cutoff. -/
lemma norm_sum_retainedPrimeDivisorConvolution_le
    (P : Finset ℕ) (y : Finset ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, retainedPrimeDivisorConvolution P y n‖ ≤
      (24 * ∑ R ∈ P.powerset, ‖y R‖) * (N : ℝ) ^ (3 / 2 : ℝ) := by
  let C : ℝ := ∑ R ∈ P.powerset, ‖y R‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  have hroot (d : ℕ) (hd : d ∈ Finset.Icc 1 N) :
      |primeFreeDivisorDefect (N / d)| ≤ 24 * Real.sqrt N := by
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdN := (Finset.mem_Icc.mp hd).2
    have hq : 1 ≤ N / d := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hdN)
    exact (abs_primeFreeDivisorDefect_le hq).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by
        exact_mod_cast Nat.div_le_self N d)) (by norm_num))
  have hex : (N : ℝ) ^ (3 / 2 : ℝ) = N * Real.sqrt N := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
      Real.rpow_add (by exact_mod_cast hN : (0 : ℝ) < N),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [sum_retainedPrimeDivisorConvolution, hex]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
        ‖retainedPrimeMobiusCoefficient P y d * (primeFreeDivisorDefect (N / d) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 N, C * (24 * Real.sqrt N) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (norm_retainedPrimeMobiusCoefficient_le P y d) (hroot d hd)
        (abs_nonneg _) hC
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel_right, nsmul_eq_mul]
      dsimp [C]
      ring

/-- Absolute Mellin transform of the actual retained convolution's continuous
square-root primitive, with its completed source expression. -/
lemma hasMellin_retainedPrimeSourcePrimitive
    (Q : Finset Nat.Primes) (y : Finset ℕ → ℂ) {s : ℂ} (hs : 2 < s.re) :
    HasMellin
      (squareRootSummatoryPrimitive
        (retainedPrimeDivisorConvolution (Q.image (fun p : Nat.Primes => (p : ℕ))) y)) (-s)
      (finiteDirichletDivisorMellin
        (retainedPrimeDirichletCoefficients (Q.image (fun p : Nat.Primes => (p : ℕ))) y)
        Q (2 * Real.eulerMascheroniConstant : ℂ) s) := by
  rw [← retainedPrimeDivisor_normalized_LSeries_eq_Mellin Q y hs]
  exact hasMellin_squareRootSummatoryPrimitive
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
    (norm_sum_retainedPrimeDivisorConvolution_le _ y) (by linarith) (by linarith)
    (LSeriesSummable_retainedPrimeDivisorConvolution _ y (by
      simp only [Complex.sub_re]; norm_num; linarith))

end RHTower
