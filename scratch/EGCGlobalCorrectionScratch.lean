import GaloisForLFunctions.RHTower.XiMeromorphicCauchyPairReflectionCorrectionNoGo
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.RHTower.XiGuinandWeilExplicitFormula

open Complex

namespace RHTower

private theorem egc_correction_eq_relative_term_difference
    (eps : ℝ) (w : ℂ) (q : XiZeroCopy) :
    meromorphicCauchyPairShiftResidueCorrection eps w (xiSpectralPoint q) =
      (eps / 2 : ℂ) *
        (xiRelativeResolventTerm (w + (eps : ℂ)) q -
          xiRelativeResolventTerm (w - (eps : ℂ)) q) := by
  unfold meromorphicCauchyPairShiftResidueCorrection xiRelativeResolventTerm
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem egc_correction_summable
    (eps : ℝ) (w : ℂ)
    (hp : XiC (w + (eps : ℂ)) ≠ 0)
    (hm : XiC (w - (eps : ℂ)) ≠ 0) :
    Summable (fun q : XiZeroCopy =>
      meromorphicCauchyPairShiftResidueCorrection eps w (xiSpectralPoint q)) := by
  have hP := summable_xiRelativeResolventTerm hp
  have hM := summable_xiRelativeResolventTerm hm
  apply ((hP.sub hM).mul_left (eps / 2 : ℂ)).congr
  intro q
  exact (egc_correction_eq_relative_term_difference eps w q).symm

theorem egc_correction_tsum_eq_relative_trace_difference
    (eps : ℝ) (w : ℂ)
    (hp : XiC (w + (eps : ℂ)) ≠ 0)
    (hm : XiC (w - (eps : ℂ)) ≠ 0) :
    (∑' q : XiZeroCopy,
      meromorphicCauchyPairShiftResidueCorrection eps w (xiSpectralPoint q)) =
      (eps / 2 : ℂ) *
        (xiRelativeResolventTrace (w + (eps : ℂ)) -
          xiRelativeResolventTrace (w - (eps : ℂ))) := by
  have hP := summable_xiRelativeResolventTerm hp
  have hM := summable_xiRelativeResolventTerm hm
  calc
    (∑' q : XiZeroCopy,
      meromorphicCauchyPairShiftResidueCorrection eps w (xiSpectralPoint q)) =
        ∑' q : XiZeroCopy,
          (eps / 2 : ℂ) *
            (xiRelativeResolventTerm (w + (eps : ℂ)) q -
              xiRelativeResolventTerm (w - (eps : ℂ)) q) := by
          apply tsum_congr
          intro q
          exact egc_correction_eq_relative_term_difference eps w q
    _ = (eps / 2 : ℂ) *
          ∑' q : XiZeroCopy,
            (xiRelativeResolventTerm (w + (eps : ℂ)) q -
              xiRelativeResolventTerm (w - (eps : ℂ)) q) := by
          rw [tsum_mul_left]
    _ = _ := by
          rw [hP.tsum_sub hM]
          rfl

theorem egc_correction_tsum_eq_continued_source_difference
    (eps : ℝ) (w : ℂ)
    (hp : XiExplicitAdmissible (w + (eps : ℂ)))
    (hm : XiExplicitAdmissible (w - (eps : ℂ))) :
    (∑' q : XiZeroCopy,
      meromorphicCauchyPairShiftResidueCorrection eps w (xiSpectralPoint q)) =
      (eps / 2 : ℂ) *
        (continuedPrimeArchSourceRelativeTrace (w + (eps : ℂ)) -
          continuedPrimeArchSourceRelativeTrace (w - (eps : ℂ))) := by
  rw [egc_correction_tsum_eq_relative_trace_difference eps w
    (XiC_ne_zero_of_admissible hp) (XiC_ne_zero_of_admissible hm)]
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hp.re_pos hp.ne_one hp.zeta_ne,
    continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hm.re_pos hm.ne_one hm.zeta_ne]

end RHTower
