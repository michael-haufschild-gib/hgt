import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularArchimedean
import GaloisForLFunctions.RHTower.XiGuinandWeilSymmetricContour
import GaloisForLFunctions.RHTower.GammalessStripRigidity

/-!
# Complete bottom-edge value for the sharp rectangular Guinand--Weil test

Both terms in the Euler-line decomposition are absolutely integrable: the von Mangoldt L-series
is uniformly bounded on `Re s = 3/2`, while the Gamma term is handled in
`XiGuinandWeilRectangularArchimedean`.  Consequently the literal centered-Xi bottom edge may be
split without a regularity hypothesis.

After the symmetric contour is divided by `2 pi i`, the complete bottom edge is exactly the
normalized archimedean integral minus twice the finite critical-weight rectangular prime
autocorrelation.  This is the prime--Gamma source identity at the piecewise-linear rectangular
regularity required by the RH program.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

def rectangularEulerPrimeIntegrand (L a : ℝ) (xi : ℝ) : ℂ :=
  rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ (2 : ℕ) *
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (rectangularEulerArchPoint xi)

theorem continuous_rectangularEulerVonMangoldtLSeries :
    Continuous (fun xi : ℝ =>
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (rectangularEulerArchPoint xi)) := by
  let s : ℝ → ℂ := rectangularEulerArchPoint
  have hs : Continuous s := by
    change Continuous (fun xi : ℝ =>
      3 / 2 - ((2 * Real.pi * xi : ℝ) : ℂ) * I)
    fun_prop
  have habs : LSeries.abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ≤ 1 := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro y hy
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy)
  apply continuous_iff_continuousAt.mpr
  intro xi
  have hlt : LSeries.abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < (s xi).re := by
    rw [show (s xi).re = 3 / 2 by exact rectangularEulerArchPoint_re xi]
    exact lt_of_le_of_lt habs (by exact_mod_cast (show (1 : ℝ) < 3 / 2 by norm_num))
  exact (LSeries_hasDerivAt hlt).continuousAt.comp (hs.continuousAt)

theorem continuous_rectangularEulerPrimeIntegrand (L a : ℝ) :
    Continuous (rectangularEulerPrimeIntegrand L a) := by
  unfold rectangularEulerPrimeIntegrand
  have htransform : Continuous (fun xi : ℝ =>
      rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I)) :=
    (rectangularTwoEdgeTransform_differentiable L a).continuous.comp (by fun_prop)
  exact (htransform.pow 2).mul continuous_rectangularEulerVonMangoldtLSeries

noncomputable def rectangularEulerVonMangoldtBound : ℝ :=
  ∑' n : ℕ, ‖LSeries.term
    (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (3 / 2 : ℂ) n‖

theorem norm_rectangularEulerVonMangoldtLSeries_le (xi : ℝ) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (rectangularEulerArchPoint xi)‖ ≤ rectangularEulerVonMangoldtBound := by
  have hsum : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (rectangularEulerArchPoint xi) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by
      rw [rectangularEulerArchPoint_re]
      norm_num)
  have hnorm : Summable (fun n => ‖LSeries.term
      (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
      (rectangularEulerArchPoint xi) n‖) := summable_norm_iff.mpr hsum
  calc
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (rectangularEulerArchPoint xi)‖ ≤
        ∑' n, ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (rectangularEulerArchPoint xi) n‖ := norm_tsum_le_tsum_norm hnorm
    _ = rectangularEulerVonMangoldtBound := by
      unfold rectangularEulerVonMangoldtBound
      congr 1
      funext n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq,
        rectangularEulerArchPoint_re]
      norm_num

theorem integrable_rectangularEulerPrimeIntegrand (L a : ℝ) :
    Integrable (rectangularEulerPrimeIntegrand L a) := by
  let f : ℝ → ℂ := fun xi =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ (2 : ℕ)
  have hf : Integrable f := integrable_rectangularTwoEdgeTransform_eulerLine_sq L a
  have hmajor : Integrable (fun xi : ℝ =>
      |rectangularEulerVonMangoldtBound| * ‖f xi‖) :=
    hf.norm.const_mul |rectangularEulerVonMangoldtBound|
  refine hmajor.mono' (continuous_rectangularEulerPrimeIntegrand L a).aestronglyMeasurable ?_
  filter_upwards with xi
  change ‖f xi * LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (rectangularEulerArchPoint xi)‖ ≤
        |rectangularEulerVonMangoldtBound| * ‖f xi‖
  rw [norm_mul]
  calc
    ‖f xi‖ * ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
        (rectangularEulerArchPoint xi)‖ ≤
        ‖f xi‖ * |rectangularEulerVonMangoldtBound| :=
      mul_le_mul_of_nonneg_left
        ((norm_rectangularEulerVonMangoldtLSeries_le xi).trans
          (le_abs_self rectangularEulerVonMangoldtBound)) (norm_nonneg (f xi))
    _ = |rectangularEulerVonMangoldtBound| * ‖f xi‖ := mul_comm _ _

def rectangularBottomPrimeIntegrand (L a : ℝ) (x : ℝ) : ℂ :=
  xiRectangularTwoEdgeTransform L a ((x : ℂ) - I) ^ (2 : ℕ) *
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((3 / 2 : ℂ) + x * I)

theorem rectangularBottomPrimeIntegrand_scale (L a xi : ℝ) :
    rectangularBottomPrimeIntegrand L a ((-2 * Real.pi) * xi) =
      rectangularEulerPrimeIntegrand L a xi := by
  unfold rectangularBottomPrimeIntegrand rectangularEulerPrimeIntegrand
    rectangularEulerArchPoint xiRectangularTwoEdgeTransform
  congr 2
  · congr 2
    push_cast
    rw [mul_sub, Complex.I_mul_I]
    ring_nf
  ·
    push_cast
    ring_nf

theorem integrable_rectangularBottomPrimeIntegrand (L a : ℝ) :
    Integrable (rectangularBottomPrimeIntegrand L a) := by
  have hscaled : Integrable (fun xi : ℝ =>
      rectangularBottomPrimeIntegrand L a ((-2 * Real.pi) * xi)) := by
    simpa only [rectangularBottomPrimeIntegrand_scale] using
      integrable_rectangularEulerPrimeIntegrand L a
  exact (integrable_comp_mul_left_iff (rectangularBottomPrimeIntegrand L a)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)).mp hscaled

def rectangularBottomXiLogDerivIntegrand (L a : ℝ) (x : ℝ) : ℂ :=
  xiRectangularTwoEdgeTransform L a ((x : ℂ) - I) ^ (2 : ℕ) *
    logDeriv XiC ((x : ℂ) - I)

theorem rectangularBottomXiLogDerivIntegrand_eq (L a x : ℝ) :
    rectangularBottomXiLogDerivIntegrand L a x =
      -I * rectangularBottomPrimeIntegrand L a x +
        I * rectangularBottomArchIntegrand L a x := by
  have hbottom :=
    logDeriv_XiC_bottom_eq_primeArch (c := (1 : ℝ)) (by norm_num) x
  norm_num at hbottom
  have hthreeHalf : (3 / 2 : ℂ) = (((3 / 2 : ℝ) : ℂ)) := by norm_num
  rw [hthreeHalf] at hbottom
  rw [rectangularBottomXiLogDerivIntegrand, rectangularBottomPrimeIntegrand,
    rectangularBottomArchIntegrand, hbottom]
  rw [hthreeHalf]
  ring

theorem integrable_rectangularBottomXiLogDerivIntegrand (L a : ℝ) :
    Integrable (rectangularBottomXiLogDerivIntegrand L a) := by
  have hprime := (integrable_rectangularBottomPrimeIntegrand L a).const_mul (-I)
  have harch := (integrable_rectangularBottomArchIntegrand L a).const_mul I
  exact (hprime.add harch).congr
    (Filter.Eventually.of_forall fun x =>
      (rectangularBottomXiLogDerivIntegrand_eq L a x).symm)

def normalizedRectangularBottomXiContribution (L a : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    (2 * ∫ x : ℝ, rectangularBottomXiLogDerivIntegrand L a x)

theorem normalizedRectangularBottomXiContribution_eq_prime_add_arch
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    normalizedRectangularBottomXiContribution L a =
      -2 * (rectangularPrimeAutocorrelationSum L a : ℂ) +
        normalizedRectangularBottomArchContribution L a := by
  have hprimeInt := (integrable_rectangularBottomPrimeIntegrand L a).const_mul (-I)
  have harchInt := (integrable_rectangularBottomArchIntegrand L a).const_mul I
  have hsplit : (∫ x : ℝ, rectangularBottomXiLogDerivIntegrand L a x) =
      (∫ x : ℝ, -I * rectangularBottomPrimeIntegrand L a x) +
        ∫ x : ℝ, I * rectangularBottomArchIntegrand L a x := by
    rw [← MeasureTheory.integral_add hprimeInt harchInt]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      rectangularBottomXiLogDerivIntegrand_eq L a x)
  have hprime := normalized_rectangularBottomPrimeContribution_eq_neg_two_primeSum hL ha
  change (2 * Real.pi * I)⁻¹ *
      (2 * ∫ x : ℝ, -I * rectangularBottomPrimeIntegrand L a x) =
        -2 * (rectangularPrimeAutocorrelationSum L a : ℂ) at hprime
  change normalizedRectangularBottomXiContribution L a = _
  rw [normalizedRectangularBottomXiContribution, hsplit]
  change (2 * Real.pi * I)⁻¹ *
      (2 * ((∫ x : ℝ, -I * rectangularBottomPrimeIntegrand L a x) +
        ∫ x : ℝ, I * rectangularBottomArchIntegrand L a x)) = _
  rw [mul_add, mul_add]
  rw [hprime]
  rfl

end RHTower
