import GaloisForLFunctions.RHTower.ChebyshevShortWindowLowerBound
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.SmoothedIdentity

/-! The normalized Cesàro formula at level one, with the Xi divisor counted with multiplicity. -/

open Complex Finset RHTower WindowedLandauTheory.HC
open ArithmeticFunction (vonMangoldt)
open GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

namespace QH.PrimeProgressions

private theorem levelOne_ramp {y : ℝ} (hy : 1 ≤ y) :
    An.sumLamChi (1 : DirichletCharacter ℂ 1) y =
      (y : ℂ) * ((∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n / (n : ℝ) : ℝ) : ℂ) -
        (Chebyshev.psi y : ℂ) := by
  have hψ : Chebyshev.psi y = ∑ n ∈ Icc 1 ⌊y⌋₊, vonMangoldt n := by
    rw [Chebyshev.psi_eq_sum_Icc]
    symm
    apply sum_subset
    · intro n hn
      exact mem_Icc.mpr ⟨Nat.zero_le n, (mem_Icc.mp hn).2⟩
    · intro n hn hnot
      simp only [mem_Icc] at hn hnot
      have hn0 : n = 0 := by omega
      simp [hn0]
  rw [sumLamChi_eq_ramp _ hy, hψ]
  push_cast
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun n _ => ?_
  have h₁ : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    rw [Subsingleton.elim (n : ZMod 1) 1, map_one]
  rw [twistedVM, h₁, one_mul]
  ring

theorem xiZeroKernel_eq_neg_lag {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    QH.zeroKernel y q.1 = -((y : ℂ) ^ ((q.1 : ℂ) - 1) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  rw [QH.zeroKernel, Complex.cpow_sub _ _ (ofReal_ne_zero.mpr hy.ne'), Complex.cpow_one]
  simp only [show (q.1 : ℂ) - 1 = -(1 - (q.1 : ℂ)) by ring, mul_neg, div_neg,
    neg_div, div_div, mul_comm ((q.1 : ℂ) * (1 - (q.1 : ℂ))) (y : ℂ)]

/-- The normalized principal ramp has an error of order `1 / y` after subtracting the main
logarithm, the constant and the multiplicity-weighted nontrivial zero contribution. -/
theorem principal_normalized_formula :
    ∀ y : ℝ, 2 ≤ y →
      ‖An.sumLamChi (1 : DirichletCharacter ℂ 1) y / (y : ℂ) - (-Real.eulerMascheroniConstant : ℂ) -
        ((Real.log y - 1 : ℝ) : ℂ) + ∑' q : XiZeroCopy, QH.zeroKernel y q.1‖ ≤
          (|Real.log (2 * Real.pi)| + 2) / y := by
  intro y hy
  have hy₁ : 1 < y := by linarith
  have hy₀ : 0 < y := by linarith
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.mpr hy₀.ne'
  have hsum : ∑' q : XiZeroCopy, QH.zeroKernel y q.1 = -(lagZeroSum y / (y : ℂ)) := by
    simp only [xiZeroKernel_eq_neg_lag hy₀, tsum_neg, lagZeroSum_div_eq hy₁.le]
  have hz := lag_explicit_formula hy₁
  change lagZeroSum y = _ at hz
  have he : An.sumLamChi (1 : DirichletCharacter ℂ 1) y / (y : ℂ) - (-Real.eulerMascheroniConstant : ℂ) -
      ((Real.log y - 1 : ℝ) : ℂ) - lagZeroSum y / (y : ℂ) =
        ((Real.log (2 * Real.pi) : ℂ) - trivialZeroSeries y) / (y : ℂ) := by
    rw [levelOne_ramp hy₁.le, hz]
    push_cast
    field_simp [hyc]
    ring
  rw [hsum, ← sub_eq_add_neg, he, norm_div, norm_real, Real.norm_of_nonneg hy₀.le]
  have htriv : ‖trivialZeroSeries y‖ ≤ 2 := by
    have hs := (summable_trivialZeroSeriesTerm hy₁.le).norm
    have hb : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
      have h := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
      exact_mod_cast (summable_nat_add_iff 1).mpr h
    exact (norm_tsum_le_tsum_norm hs).trans
      ((hs.tsum_le_tsum (norm_trivialZeroSeriesTerm_le hy₁.le) hb).trans efD_le_two)
  apply div_le_div_of_nonneg_right _ hy₀.le
  exact (norm_sub_le _ _).trans (add_le_add (by rw [norm_real, Real.norm_eq_abs]) htriv)

end QH.PrimeProgressions
