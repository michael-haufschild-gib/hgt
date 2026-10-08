import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticGaussianShift
import GaloisForLFunctions.RHTower.ZetaLeftLineIdentities

/-!
# The actual signed arithmetic coefficients of the source contour

The coefficients are `(lambda₀ - Lambda) * 1 * 1`. Their Dirichlet series
is the pole-cleared zeta-square expression on its absolute half-plane.
The Gaussian chi transform applies to this literal signed sequence using
only summability supplied by full Weil positivity.
-/

open Complex MeasureTheory Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

def sourceSquareCoeff (lam : ℕ → ℝ) : ℕ → ℂ :=
  LSeries.convolution (LSeries.convolution
    (WeilHerglotz.lamC lam - fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 1) 1

@[simp] theorem sourceSquareCoeff_zero (lam : ℕ → ℝ) : sourceSquareCoeff lam 0 = 0 := by
  simp [sourceSquareCoeff, LSeries.convolution_def]

theorem sourceSquareCoeff_summable {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (sourceSquareCoeff lam) s := by
  have hlam : LSeriesSummable (WeilHerglotz.lamC lam) s := WeilHerglotz.summable_term_lamC hW hs
  exact ((hlam.sub
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)).convolution
      (LSeriesSummable_one_iff.mpr hs)).convolution (LSeriesSummable_one_iff.mpr hs)

theorem LSeries_sourceSquareCoeff {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) : LSeries (sourceSquareCoeff lam) s = sourceZetaSquare hW s := by
  have hlam : LSeriesSummable (WeilHerglotz.lamC lam) s := WeilHerglotz.summable_term_lamC hW hs
  have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h1 := LSeriesSummable_one_iff.mpr hs
  unfold sourceSquareCoeff
  rw [LSeries_convolution' ((hlam.sub hΛ).convolution h1) h1,
    LSeries_convolution' (hlam.sub hΛ) h1, LSeries_sub hlam hΛ,
    LSeries_one_eq_riemannZeta hs,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hD : zetaArchimedeanDatum s + 1 / (s - 1) - WeilSpectral.weilContinuation hW s =
      LSeries (WeilHerglotz.lamC lam) s := by
    rw [WeilSpectral.weilContinuation_eq hW hs, WeilHerglotz.weilFunction,
      zetaArchimedeanDatum]
    ring
  unfold sourceZetaSquare
  rw [hD]
  field_simp
  ring

theorem sourceZetaPairing_leftDual {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    sourceZetaPairing hW (1 - leftPt t) =
      zetaChi (leftPt t) * LSeries (sourceSquareCoeff lam) (1 - leftPt t) := by
  rw [LSeries_sourceSquareCoeff hW (by simp [leftPt]; norm_num)]
  unfold sourceZetaPairing sourceZetaSquare
  rw [sub_sub_cancel, riemannZeta_eq_of_mem_leftStrip (leftPt_mem_leftStrip t)]
  ring

theorem gaussWeight_one_sub (T : ℝ) (s : ℂ) : gaussWeight T (1 - s) = gaussWeight T s := by
  unfold gaussWeight
  congr 1
  ring

/-- Exact signed coefficient extraction from the actual right-line source contour. -/
theorem integral_sourceZetaPairing_eq_kernelSum {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      gaussWeight T ((3 / 2 : ℂ) + t * I)) =
      2 * Real.pi * ∑' n : ℕ, sourceSquareCoeff lam n * leftKernel T n := by
  have hi := integral_zetaChi_mul_LSeries
    (sourceSquareCoeff_summable hW (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num))
    hT (r := 1) (by norm_num)
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul, mul_one] at hi
  have he (t : ℝ) : sourceZetaPairing hW ((3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) *
      gaussWeight T ((3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) =
      zetaChi (leftPt t) * LSeries (sourceSquareCoeff lam) (1 - leftPt t) *
        gaussWeight T (leftPt t) := by
    have hp : (3 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - leftPt t := by
      simp only [leftPt, Complex.ofReal_neg]
      ring
    rw [hp, sourceZetaPairing_leftDual hW, gaussWeight_one_sub]
  have hneg := integral_neg_eq_self (fun t : ℝ => sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
    gaussWeight T ((3 / 2 : ℂ) + t * I))
  rw [← hneg]
  simp_rw [he]
  rw [hi]
  congr 1
  apply tsum_congr
  intro n
  split_ifs with hn
  · simp [hn]
  · rfl

end RHTower.WeilSingularArithmetic
