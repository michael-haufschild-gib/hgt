import GaloisForLFunctions.RHTower.SelbergDelangeConvolutionTransfer
import GaloisForLFunctions.RHTower.ZetaBinomialHalfFractionalPole

/-!
# Selberg--Delange assembly for the signed squarefree convolution half

This module assembles the exact signed convolution conclusion from the positive zeta-half
Wiener--Ikehara input and a summable hyperbola majorant.  The correction is the square-supported
coefficient system already shown to converge absolutely on `Re s > 1/2`.

The analytic Tauberian core is deliberately exposed as a named proposition rather than hidden as
an axiom: proving that proposition is precisely the remaining fractional Wiener--Ikehara theorem.
-/

open ArithmeticFunction Complex Filter Topology Set
open scoped BigOperators ArithmeticFunction.zeta ComplexOrder Moebius

noncomputable section

namespace RHTower

/-- Natural-number normalization `N / sqrt(log N)` for the order-`1/2` Selberg--Delange law. -/
def selbergDelangeHalfScale (N : ℕ) : ℂ :=
  ((((N : ℝ) / Real.sqrt (Real.log N)) : ℝ) : ℂ)

/-- Exact fixed-dilation form of fractional Wiener--Ikehara for the positive zeta half. -/
def ZetaBinomialHalfWienerIkehara : Prop :=
  ∀ d : ℕ, d ≠ 0 →
    Tendsto
      (fun N ↦ arithmeticSummatory zetaBinomialHalf (N / d) /
        selbergDelangeHalfScale N)
      atTop (𝓝 (((1 / Real.sqrt Real.pi : ℝ) : ℂ) / (d : ℂ)))

/-- The Möbius half and positive zeta half are exact convolution inverses. -/
theorem moebiusBinomialHalf_mul_zetaBinomialHalf :
    moebiusBinomialHalf * zetaBinomialHalf = 1 := by
  have hsq :
      (moebiusBinomialHalf * zetaBinomialHalf) *
          (moebiusBinomialHalf * zetaBinomialHalf) =
        (1 : ArithmeticFunction ℂ) := by
    calc
      (moebiusBinomialHalf * zetaBinomialHalf) *
          (moebiusBinomialHalf * zetaBinomialHalf) =
          (moebiusBinomialHalf * moebiusBinomialHalf) *
            (zetaBinomialHalf * zetaBinomialHalf) := by ring
      _ = (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) *
          ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) := by
        rw [moebiusBinomialHalf_mul_self, zetaBinomialHalf_mul_self]
      _ = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hhalf := convolutionHalf_unique (1 : ArithmeticFunction ℂ)
    (moebiusBinomialHalf * zetaBinomialHalf) (by simp) hsq
  have hone := convolutionHalf_unique (1 : ArithmeticFunction ℂ)
    (1 : ArithmeticFunction ℂ) (by simp) (by simp)
  exact hhalf.trans hone.symm

/-- The square-correction `L`-value at one has square `1 / ζ(2)`. -/
theorem LSeries_squareDilatedMoebiusBinomialHalf_one_sq_mul_riemannZeta_two :
    LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) *
        LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) *
          riemannZeta (2 : ℂ) = 1 := by
  have hc : LSeriesSummable squareDilatedMoebiusBinomialHalf (1 : ℂ) :=
    LSeriesSummable_squareDilatedMoebiusBinomialHalf (by norm_num)
  have hu : LSeriesSummable moebiusBinomialHalf (2 : ℂ) :=
    LSeriesSummable_moebiusBinomialHalf (by norm_num)
  have hz : LSeriesSummable ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
      (2 : ℂ) := by
    change LSeriesSummable (fun n ↦ ((ζ : ArithmeticFunction ℕ) n : ℂ)) (2 : ℂ)
    exact ArithmeticFunction.LSeriesSummable_zeta_iff.mpr (by norm_num)
  have hmu : LSeriesSummable
      ((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) (2 : ℂ) := by
    have hfun : (⇑(((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) : ℕ → ℂ) =
        (fun n ↦ (μ n : ℂ)) := by
      funext n
      simp [ArithmeticFunction.intCoe_apply]
    rw [hfun]
    exact LSeriesSummable_moebius_iff.mpr (by norm_num)
  have hmuZ :
      LSeries (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) (2 : ℂ) *
        riemannZeta (2 : ℂ) = 1 := by
    have hzeta :
        LSeries (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) (2 : ℂ) =
          riemannZeta (2 : ℂ) := by
      change LSeries (fun n ↦ ((ζ : ArithmeticFunction ℕ) n : ℂ)) (2 : ℂ) =
        riemannZeta (2 : ℂ)
      exact ArithmeticFunction.LSeries_zeta_eq_riemannZeta (by norm_num)
    calc
      LSeries (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) (2 : ℂ) *
          riemannZeta (2 : ℂ) =
          LSeries (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) (2 : ℂ) *
            LSeries (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) (2 : ℂ) := by
        rw [hzeta]
      _ = LSeries (fun n ↦
          ((((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) *
            ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) n)) (2 : ℂ) :=
        (ArithmeticFunction.LSeries_mul' hmu hz).symm
      _ = 1 := by
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
        rw [ArithmeticFunction.one_eq_delta, LSeries_delta]
        rfl
  calc
    LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) *
          LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) * riemannZeta (2 : ℂ) =
        (LSeries moebiusBinomialHalf (2 : ℂ) *
          LSeries moebiusBinomialHalf (2 : ℂ)) * riemannZeta (2 : ℂ) := by
      rw [squareDilatedMoebiusBinomialHalf, LSeries_mPart two_ne_zero]
      norm_num
    _ = LSeries (fun n ↦
        (moebiusBinomialHalf * moebiusBinomialHalf) n) (2 : ℂ) *
          riemannZeta (2 : ℂ) := by
      rw [ArithmeticFunction.LSeries_mul' hu hu]
    _ = LSeries (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℂ)) (2 : ℂ) *
          riemannZeta (2 : ℂ) := by rw [moebiusBinomialHalf_mul_self]
    _ = 1 := hmuZ

/-- The correction constant is the positive reciprocal square root of the real zeta value at two. -/
theorem LSeries_squareDilatedMoebiusBinomialHalf_one_eq_inv_sqrt_zeta_two :
    LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) =
      ((1 / Real.sqrt (riemannZeta (2 : ℂ)).re : ℝ) : ℂ) := by
  let U : ℂ := LSeries moebiusBinomialHalf (2 : ℂ)
  let B : ℂ := LSeries zetaBinomialHalf (2 : ℂ)
  have hu : LSeriesSummable moebiusBinomialHalf (2 : ℂ) :=
    LSeriesSummable_moebiusBinomialHalf (by norm_num)
  have hb : LSeriesSummable zetaBinomialHalf (2 : ℂ) :=
    LSeriesSummable_zetaBinomialHalf (by norm_num)
  have hUB : U * B = 1 := by
    calc
      U * B = LSeries (fun n ↦
          (moebiusBinomialHalf * zetaBinomialHalf) n) (2 : ℂ) := by
        dsimp [U, B]
        exact (ArithmeticFunction.LSeries_mul' hu hb).symm
      _ = LSeries (fun n ↦ (1 : ArithmeticFunction ℂ) n) (2 : ℂ) := by
        rw [moebiusBinomialHalf_mul_zetaBinomialHalf]
      _ = 1 := by
        rw [ArithmeticFunction.one_eq_delta, LSeries_delta]
        rfl
  have hBnonneg : 0 ≤ B := by
    exact LSeries_zetaBinomialHalf_nonneg (x := 2)
  have hBre0 : 0 ≤ B.re := (Complex.nonneg_iff.mp hBnonneg).1
  have hBim : B.im = 0 := (Complex.nonneg_iff.mp hBnonneg).2.symm
  have hBne : B ≠ 0 := by
    intro hB
    rw [hB, mul_zero] at hUB
    norm_num at hUB
  have hBreNe : B.re ≠ 0 := by
    intro h
    apply hBne
    apply Complex.ext
    · simpa using h
    · simpa using hBim
  have hBsq := LSeries_zetaBinomialHalf_sq (s := (2 : ℂ)) (by norm_num)
  have hBsqRe : B.re ^ 2 = (riemannZeta (2 : ℂ)).re := by
    change B * B = riemannZeta (2 : ℂ) at hBsq
    have hre := congrArg Complex.re hBsq
    simp only [Complex.mul_re] at hre
    rw [hBim] at hre
    simpa [pow_two] using hre
  have hsqrt : Real.sqrt (riemannZeta (2 : ℂ)).re = B.re := by
    rw [← hBsqRe, Real.sqrt_sq hBre0]
  have hBreal : B = (B.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hBim
  have hCU :
      LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ) = U := by
    rw [squareDilatedMoebiusBinomialHalf, LSeries_mPart two_ne_zero]
    norm_num [U]
  rw [hCU, eq_inv_of_mul_eq_one_left hUB, hBreal, ← hsqrt]
  push_cast
  rw [one_div]

/-- **Concrete signed Selberg--Delange assembly.**  Once fractional Wiener--Ikehara supplies the
positive zeta-half limit and a summable majorant controls the hyperbola array, the signed
squarefree half has the asserted main term.  No positivity assumption is made on the correction. -/
theorem tendsto_squarefreeConvolutionHalf_selbergDelange
    (hWI : ZetaBinomialHalfWienerIkehara)
    (bound : ℕ → ℝ)
    (hboundNonneg : ∀ d, 0 ≤ bound d)
    (hboundSummable : Summable bound)
    (hdominated : ∀ N d : ℕ, d ∈ Finset.Icc 1 N →
      ‖squareDilatedMoebiusBinomialHalf d *
          arithmeticSummatory zetaBinomialHalf (N / d) /
            selbergDelangeHalfScale N‖ ≤ bound d) :
    Tendsto
      (fun N ↦ arithmeticSummatory squarefreeConvolutionHalf N /
        selbergDelangeHalfScale N)
      atTop
      (𝓝 (((1 / Real.sqrt Real.pi : ℝ) : ℂ) *
        LSeries squareDilatedMoebiusBinomialHalf (1 : ℂ))) := by
  rw [squarefreeConvolutionHalf_eq_zetaBinomialHalf_mul_squareCorrection, mul_comm]
  exact tendsto_arithmeticSummatory_mul_div_of_dominated_LSeries
    squareDilatedMoebiusBinomialHalf zetaBinomialHalf selbergDelangeHalfScale
      ((1 / Real.sqrt Real.pi : ℝ) : ℂ) bound hboundNonneg hboundSummable hWI hdominated

/-- Explicit-constant form of the concrete signed Selberg--Delange assembly. -/
theorem tendsto_squarefreeConvolutionHalf_selbergDelange_explicit
    (hWI : ZetaBinomialHalfWienerIkehara)
    (bound : ℕ → ℝ)
    (hboundNonneg : ∀ d, 0 ≤ bound d)
    (hboundSummable : Summable bound)
    (hdominated : ∀ N d : ℕ, d ∈ Finset.Icc 1 N →
      ‖squareDilatedMoebiusBinomialHalf d *
          arithmeticSummatory zetaBinomialHalf (N / d) /
            selbergDelangeHalfScale N‖ ≤ bound d) :
    Tendsto
      (fun N ↦ arithmeticSummatory squarefreeConvolutionHalf N /
        selbergDelangeHalfScale N)
      atTop
      (𝓝 (((1 / (Real.sqrt Real.pi *
        Real.sqrt (riemannZeta (2 : ℂ)).re) : ℝ) : ℝ) : ℂ)) := by
  have h := tendsto_squarefreeConvolutionHalf_selbergDelange hWI bound
    hboundNonneg hboundSummable hdominated
  rw [LSeries_squareDilatedMoebiusBinomialHalf_one_eq_inv_sqrt_zeta_two] at h
  convert h using 1
  push_cast
  rw [one_div, one_div, one_div, mul_inv]

end RHTower
