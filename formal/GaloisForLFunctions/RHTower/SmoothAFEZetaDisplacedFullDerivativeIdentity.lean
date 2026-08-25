import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDualCoefficientDerivative
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedPoleResidueDerivative

/-!
# Exact differentiated displaced Gaussian zeta AFE

The reflected coefficient derivative is identified with the negative of the
conductor-oriented weighted term derivative.  Absolute summability then
differentiates the complete reflected series and closes the exact height
derivative identity for the two-series Gaussian AFE.
-/

noncomputable section

namespace RHTower

open Complex Filter

theorem smoothAFEZetaDisplacedDualCoefficientHeightDerivative_eq_neg_weighted
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) (n : ℕ) :
    smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x tau n =
      -smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
        d x tau n := by
  have hcoeff :=
    hasDerivAt_smoothAFEZetaDualCoefficientGeneral_displaced
      hd hdquarter hx tau n
  have hweighted :=
    hasDerivAt_smoothAFEZetaDisplacedReflectedWeightedTerm
      hd hdquarter heta hetaquarter hx tau n
  have hfun : (fun u : ℝ => smoothAFEZetaDualCoefficientGeneral
      (displacedLinePt d u) x n) =
      fun u : ℝ => -smoothAFEZetaDisplacedReflectedWeightedTerm d x u n := by
    funext u
    simpa only [smoothAFEZetaDisplacedReflectedWeightedTerm,
      smoothAFEZetaDisplacedReflectedMainTerm] using
      smoothAFEZetaDualCoefficientGeneral_displaced_eq_neg_weight
        hx d u n
  rw [hfun] at hcoeff
  exact hcoeff.unique hweighted.neg

def smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField
    (d x tau : ℝ) : ℂ :=
  ∑' n : ℕ,
    smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm d x tau n

theorem hasDerivAt_smoothAFEZetaDisplacedReflectedWeightedSourceField
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) :
    HasDerivAt
      (fun u : ℝ => ∑' n : ℕ,
        smoothAFEZetaDisplacedReflectedWeightedTerm d x u n)
      (smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField
        d x tau) tau := by
  have hcoeff :=
    hasDerivAt_tsum_smoothAFEZetaDualCoefficientGeneral_displaced
      hd hdquarter hx tau
  have hfun : (fun u : ℝ => ∑' n : ℕ,
      smoothAFEZetaDualCoefficientGeneral (displacedLinePt d u) x n) =
      fun u : ℝ => -(∑' n : ℕ,
        smoothAFEZetaDisplacedReflectedWeightedTerm d x u n) := by
    funext u
    calc
      (∑' n : ℕ,
          smoothAFEZetaDualCoefficientGeneral (displacedLinePt d u) x n) =
          ∑' n : ℕ,
            (-smoothAFEZetaDisplacedReflectedWeightedTerm d x u n) := by
        apply tsum_congr
        intro n
        simpa only [smoothAFEZetaDisplacedReflectedWeightedTerm,
          smoothAFEZetaDisplacedReflectedMainTerm] using
          smoothAFEZetaDualCoefficientGeneral_displaced_eq_neg_weight
            hx d u n
      _ = -(∑' n : ℕ,
          smoothAFEZetaDisplacedReflectedWeightedTerm d x u n) := tsum_neg
  have hderiv :
      (∑' n : ℕ,
        smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x tau n) =
      -(∑' n : ℕ,
        smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
          d x tau n) := by
    calc
      (∑' n : ℕ,
          smoothAFEZetaDisplacedDualCoefficientHeightDerivative d x tau n) =
          ∑' n : ℕ,
            (-smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
              d x tau n) := by
        apply tsum_congr
        intro n
        exact smoothAFEZetaDisplacedDualCoefficientHeightDerivative_eq_neg_weighted
          hd hdquarter heta hetaquarter hx tau n
      _ = -(∑' n : ℕ,
          smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
            d x tau n) := tsum_neg
  rw [hfun, hderiv] at hcoeff
  unfold smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField
  have hneg := hcoeff.neg
  change HasDerivAt
    (fun u : ℝ => -(-(∑' n : ℕ,
      smoothAFEZetaDisplacedReflectedWeightedTerm d x u n)))
    (-(-(∑' n : ℕ,
      smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeTerm
        d x tau n))) tau at hneg
  simpa only [neg_neg] using hneg

/-- Exact height derivative source of the displaced two-series zeta AFE. -/
def smoothAFEZetaDisplacedHeightDerivativeSourceField
    (d x tau : ℝ) : ℂ :=
  smoothAFEZetaDisplacedDirectHeightDerivativeSourceField d x tau +
    smoothAFEZetaDisplacedReflectedWeightedHeightDerivativeSourceField
      d x tau -
    smoothAFEZetaDisplacedPoleResidueHeightDerivative d x tau

/-- Exact unconditional differentiated Gaussian AFE on every displaced line
`Re s = 1/2-d`, for `0 < d ≤ 1/4`. -/
theorem hasDerivAt_riemannZeta_displaced_eq_smoothAFE
    {d eta x : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) (tau : ℝ) :
    HasDerivAt (fun u : ℝ => riemannZeta (displacedLinePt d u))
      (smoothAFEZetaDisplacedHeightDerivativeSourceField d x tau) tau := by
  have hdhalf : d < 1 / 2 := hdquarter.trans_lt (by norm_num)
  have hdirect := hasDerivAt_smoothAFEZetaDisplacedDirectSourceField
    hdhalf hx tau
  have hreflected :=
    hasDerivAt_smoothAFEZetaDisplacedReflectedWeightedSourceField
      hd hdquarter heta hetaquarter hx tau
  have hpole := hasDerivAt_smoothAFEZetaShiftedPoleResidue_displaced
    hd hx tau
  have hsum := (hdirect.add hreflected).sub hpole
  have hfun : (fun u : ℝ => riemannZeta (displacedLinePt d u)) =
      fun u : ℝ =>
        smoothAFEZetaDisplacedDirectSourceField d x u +
          (∑' n : ℕ,
            smoothAFEZetaDisplacedReflectedWeightedTerm d x u n) -
          smoothAFEZetaShiftedPoleResidue (displacedLinePt d u) x := by
    funext u
    simpa only [smoothAFEZetaDisplacedDirectSourceField,
      smoothAFEZetaDisplacedDirectTerm,
      smoothAFEZetaDisplacedReflectedWeightedTerm,
      smoothAFEZetaDisplacedReflectedMainTerm] using
      riemannZeta_displaced_eq_two_tsum_smoothAFE_dualWeight
        hx hd hdhalf u
  rw [hfun]
  unfold smoothAFEZetaDisplacedHeightDerivativeSourceField
  exact hsum

end RHTower
