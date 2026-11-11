import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDetectorMomentErrorsAreSmall
import GaloisForLFunctions.RHTower.ZetaGateProductAFEHighBlock
import GaloisForLFunctions.RHTower.DyadicLawLowBlocks

/-!
# From a tapered detector moment to the actual block energy

The detector is analytic away from the zeta pole. Its nonnegative energy
is therefore dominated by its tapered integral whenever the taper lies
at positive height and equals one on the block.
-/

open Complex MeasureTheory Set
open RHTower RHTower.ZetaGateProductAFE GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The actual linear detector energy on an interval, with the matched mollifier. -/
def matchedDetectorBlockEnergy (N : ℕ) (d lam a v : ℝ) : ℝ :=
  ∫ t in a..v, ‖(riemannZeta (displacedLinePt d t) +
    (lam : ℂ) * deriv riemannZeta (displacedLinePt d t)) *
      edPoly (fun n => (linearDetectorWeights N d n : ℂ)) (Finset.Icc 1 N)
        (displacedLinePt d t)‖ ^ 2

/-- The block energy is dominated by the moment used in the exact main-term formula. -/
theorem matchedDetectorBlockEnergy_le_taper {p q η : ℝ}
    (hη : 0 < η) (hp : 1 ≤ p - η) (hpq : p ≤ q) (N : ℕ) (d lam : ℝ) :
    matchedDetectorBlockEnergy N d lam p q ≤
      ∫ t, blockWindow p q η t *
        ‖(riemannZeta (displacedLinePt d t) + (lam : ℂ) * deriv riemannZeta (displacedLinePt d t)) *
          edPoly (fun n => (linearDetectorWeights N d n : ℂ)) (Finset.Icc 1 N)
            (displacedLinePt d t)‖ ^ 2 := by
  apply intervalIntegral_le_window_integral hη hpq _ (fun _ => sq_nonneg _)
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt ((zero_lt_one.trans_le hp).trans_le ht.1)
  have hz : displacedLinePt d t ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [displacedLinePt, Complex.add_im, Complex.sub_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
      mul_zero, zero_add, add_zero, sub_zero, Complex.one_im] at hh
    exact ht0 hh
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hf := (analyticAt_levinsonMollifiedDetector (lam : ℂ)
    (fun n => (linearDetectorWeights N d n : ℂ)) hs hz).continuousAt
  have hg := (hf.comp (RHTower.continuous_displacedLinePt d).continuousAt).norm
  have hc := ((continuous_pow 2).continuousAt.comp hg).continuousWithinAt
    (s := Icc (p - η) (q + η))
  simpa only [levinsonMollifiedDetector, levinsonG, Function.comp_def, Pi.pow_apply] using hc

end GaloisForLFunctions.MultiscaleMollifiedZetaField
