import GaloisForLFunctions.RHTower.XiGuinandWeilExplicitFormula

/-!
# Complete shifted-pole residue row as a prime--archimedean source difference

The rational Cauchy pair creates two prescribed shifted-pole residues for each Xi zero copy.
Their complete multiplicity-counted row is summable at regular shifts and equals a finite
difference of the regulator-independent relative resolvent trace. On source-admissible shifts,
this is literally a difference of continued prime--archimedean source values. This is exact
cofactor accounting, not a sign or cofinal covariance bound.
-/

open Complex

namespace RHTower

noncomputable section

private def cauchyPairShiftResidueFormula (eps : ℝ) (w rho : ℂ) : ℂ :=
  -(eps : ℂ) / (2 * (rho - w - (eps : ℂ))) +
    (eps : ℂ) / (2 * (rho - w + (eps : ℂ)))

private theorem cauchyPairShiftResidueFormula_eq_relative_term_difference
    (eps : ℝ) (w : ℂ) (q : XiZeroCopy) :
    cauchyPairShiftResidueFormula eps w (xiSpectralPoint q) =
      (eps / 2 : ℂ) *
        (xiRelativeResolventTerm (w + (eps : ℂ)) q -
          xiRelativeResolventTerm (w - (eps : ℂ)) q) := by
  unfold cauchyPairShiftResidueFormula xiRelativeResolventTerm
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem tsum_cauchyPairShiftResidueFormula_eq_relativeTrace_private
    (eps : ℝ) (w : ℂ)
    (hp : XiC (w + (eps : ℂ)) ≠ 0)
    (hm : XiC (w - (eps : ℂ)) ≠ 0) :
    (∑' q : XiZeroCopy, cauchyPairShiftResidueFormula eps w (xiSpectralPoint q)) =
      (eps / 2 : ℂ) *
        (xiRelativeResolventTrace (w + (eps : ℂ)) -
          xiRelativeResolventTrace (w - (eps : ℂ))) := by
  have hP := summable_xiRelativeResolventTerm hp
  have hM := summable_xiRelativeResolventTerm hm
  calc
    (∑' q : XiZeroCopy, cauchyPairShiftResidueFormula eps w (xiSpectralPoint q)) =
        ∑' q : XiZeroCopy,
          (eps / 2 : ℂ) *
            (xiRelativeResolventTerm (w + (eps : ℂ)) q -
              xiRelativeResolventTerm (w - (eps : ℂ)) q) := by
          apply tsum_congr
          intro q
          exact cauchyPairShiftResidueFormula_eq_relative_term_difference eps w q
    _ = (eps / 2 : ℂ) *
          ∑' q : XiZeroCopy,
            (xiRelativeResolventTerm (w + (eps : ℂ)) q -
              xiRelativeResolventTerm (w - (eps : ℂ)) q) := by
          rw [tsum_mul_left]
    _ = _ := by
          rw [hP.tsum_sub hM]
          rfl

/-- The full Xi-copy row of the two prescribed EGC shifted residues is exactly a
relative-resolvent finite difference; no zero enumeration or finite exhaustion is chosen. -/
theorem tsum_cauchyPairShiftResidueFormula_eq_relativeTrace
    (eps : ℝ) (w : ℂ)
    (hp : XiC (w + (eps : ℂ)) ≠ 0)
    (hm : XiC (w - (eps : ℂ)) ≠ 0) :
    (∑' q : XiZeroCopy,
      (-(eps : ℂ) / (2 * (xiSpectralPoint q - w - (eps : ℂ))) +
        (eps : ℂ) / (2 * (xiSpectralPoint q - w + (eps : ℂ))))) =
      (eps / 2 : ℂ) *
        (xiRelativeResolventTrace (w + (eps : ℂ)) -
          xiRelativeResolventTrace (w - (eps : ℂ))) := by
  simpa only [cauchyPairShiftResidueFormula] using
    (tsum_cauchyPairShiftResidueFormula_eq_relativeTrace_private eps w hp hm)

/-- On two source-admissible shifts, the complete residue row is a literal
continued prime--archimedean finite difference. -/
theorem tsum_cauchyPairShiftResidueFormula_eq_continuedSource
    (eps : ℝ) (w : ℂ)
    (hp : XiExplicitAdmissible (w + (eps : ℂ)))
    (hm : XiExplicitAdmissible (w - (eps : ℂ))) :
    (∑' q : XiZeroCopy,
      (-(eps : ℂ) / (2 * (xiSpectralPoint q - w - (eps : ℂ))) +
        (eps : ℂ) / (2 * (xiSpectralPoint q - w + (eps : ℂ))))) =
      (eps / 2 : ℂ) *
        (continuedPrimeArchSourceRelativeTrace (w + (eps : ℂ)) -
          continuedPrimeArchSourceRelativeTrace (w - (eps : ℂ))) := by
  rw [tsum_cauchyPairShiftResidueFormula_eq_relativeTrace eps w
    (XiC_ne_zero_of_admissible hp) (XiC_ne_zero_of_admissible hm)]
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hp.re_pos hp.ne_one hp.zeta_ne,
    continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hm.re_pos hm.ne_one hm.zeta_ne]

end
end RHTower
