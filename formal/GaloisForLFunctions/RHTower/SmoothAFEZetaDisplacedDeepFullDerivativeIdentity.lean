import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepDualTsumDerivative
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDirectDisplacementDerivative
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedPoleResidueDisplacementDerivative

/-!
# Exact differentiated displaced AFE with a deep reflected edge

Differentiate the exact Gaussian AFE in the real displacement `d`.  The direct
edge contributes its logarithmic Dirichlet series, while the reflected edge is
represented on the coupled depth `4-d`; there its `chi` argument and Dirichlet
exponent are fixed.  Thus the complete reflected derivative has the absolutely
summable `(n+1)^(-9/2)` expansion, without `chi'` or `log(n+1)` losses.
-/

noncomputable section

open Complex Filter Set

namespace RHTower

def smoothAFEZetaDisplacedDeepDisplacementDerivativeSourceField
    (d x tau : ℝ) : ℂ :=
  smoothAFEZetaDisplacedDirectDisplacementDerivativeSourceField d x tau -
    (∑' n : ℕ, smoothAFEZetaDisplacedDeepCoefficientDerivative d x tau n) -
    smoothAFEZetaDisplacedPoleResidueDisplacementDerivative d x tau

/-- Exact unconditional displacement derivative of the Gaussian AFE. -/
theorem hasDerivAt_riemannZeta_displaced_eq_deep_smoothAFE
    {d x : ℝ} (hd : 0 < d) (hdq : d < 1 / 4) (hx : 0 < x)
    (tau : ℝ) :
    HasDerivAt
      (fun u : ℝ => riemannZeta (displacedLinePt u tau))
      (smoothAFEZetaDisplacedDeepDisplacementDerivativeSourceField d x tau) d := by
  have hdirect :=
    hasDerivAt_smoothAFEZetaDisplacedDirectSourceField_displacement
      hd hdq hx tau
  have hdual :=
    hasDerivAt_smoothAFEZetaDualMellinEdge_left_one_displaced_deep
      hx hd hdq tau
  have hpole :=
    hasDerivAt_smoothAFEZetaShiftedPoleResidue_displacement hd hx tau
  have hrhs := (hdirect.sub hdual).sub hpole
  have heq :
      (fun u : ℝ => riemannZeta (displacedLinePt u tau)) =ᶠ[nhds d]
        fun u : ℝ =>
          smoothAFEZetaDisplacedDirectSourceField u x tau -
            smoothAFEZetaDualMellinEdge (displacedLinePt u tau) x 1 -
            smoothAFEZetaShiftedPoleResidue (displacedLinePt u tau) x := by
    filter_upwards [(isOpen_Ioo.mem_nhds ⟨hd, hdq⟩)] with u hu
    have hre0 : 0 < (displacedLinePt u tau).re := by
      rw [displacedLinePt_re]
      norm_num at hu ⊢
      linarith
    have hre2 : (displacedLinePt u tau).re < 2 := by
      rw [displacedLinePt_re]
      norm_num at hu ⊢
      linarith
    have hs1 : displacedLinePt u tau ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      rw [displacedLinePt_re] at hre
      norm_num at hu hre
      linarith
    have hafe :=
      riemannZeta_eq_tsum_smoothAFECutoff_sub_dual_sub_residue_general
        hx hs1 hre0 hre2
    simpa only [smoothAFEZetaDisplacedDirectSourceField,
      smoothAFEZetaDisplacedDirectTerm, smoothAFEZetaDualMellinGeneral,
      smoothAFEZetaDualMellinEdge, neg_one_mul] using hafe
  unfold smoothAFEZetaDisplacedDeepDisplacementDerivativeSourceField
  exact hrhs.congr_of_eventuallyEq heq

/-- Closed analytic derivative form: the deep source is exactly `-ζ'`. -/
theorem smoothAFEZetaDisplacedDeepDisplacementDerivativeSourceField_eq_neg_deriv
    {d x : ℝ} (hd : 0 < d) (hdq : d < 1 / 4) (hx : 0 < x)
    (tau : ℝ) :
    smoothAFEZetaDisplacedDeepDisplacementDerivativeSourceField d x tau =
      -deriv riemannZeta (displacedLinePt d tau) := by
  have hafe :=
    hasDerivAt_riemannZeta_displaced_eq_deep_smoothAFE hd hdq hx tau
  have hs : HasDerivAt (fun u : ℝ => displacedLinePt u tau) (-1 : ℂ) d := by
    have hreal :=
      ((hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)).ofReal_comp
    simpa [displacedLinePt] using hreal.add_const ((tau : ℂ) * I)
  have hs1 : displacedLinePt d tau ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [displacedLinePt_re] at hre
    norm_num at hdq hre
    linarith
  have hz :=
    (differentiableAt_riemannZeta hs1).hasDerivAt.comp d hs
  have hz' : HasDerivAt
      (fun u : ℝ => riemannZeta (displacedLinePt u tau))
      (-deriv riemannZeta (displacedLinePt d tau)) d := by
    simpa [Function.comp_def] using hz
  exact hafe.unique hz'

/-- Equivalent positive formula for the complex derivative itself. -/
theorem deriv_riemannZeta_displaced_eq_neg_deep_smoothAFE
    {d x : ℝ} (hd : 0 < d) (hdq : d < 1 / 4) (hx : 0 < x)
    (tau : ℝ) :
    deriv riemannZeta (displacedLinePt d tau) =
      -smoothAFEZetaDisplacedDeepDisplacementDerivativeSourceField d x tau := by
  rw [smoothAFEZetaDisplacedDeepDisplacementDerivativeSourceField_eq_neg_deriv
    hd hdq hx tau, neg_neg]

end RHTower
