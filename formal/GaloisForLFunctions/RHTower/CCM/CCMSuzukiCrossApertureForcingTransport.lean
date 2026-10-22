import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilCrossApertureFormTransport
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaMovableCompletedCovarianceCCMBridge

/-!
# Cross-aperture transport of Suzuki's literal exponential forcing

On the retained form block, enlarging the literal Suzuki interval adds no forcing term.  The
zero-extended exponential is exactly the CCM polar profile, whose pairing with a retained form
vector is already aperture-invariant.  Thus a cross-aperture resolvent comparison can receive new
forcing only through genuinely new shell tests; it cannot attribute such forcing to the old block.
-/

open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The literal exponential source has identical pairing with every retained completed form
vector at two nested apertures.  This preserves the full polar normalization and does not estimate
the new shell. -/
theorem inner_suzukiTaExponential_formEmbedding_eq_of_val_eq
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) (c : ℝ)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b}
    (hvu : v.1 = u.1) :
    inner ℂ (suzukiTaExponentialL2 b c) (suzukiWeilIntervalFormEmbedding b v) =
      inner ℂ (suzukiTaExponentialL2 a c) (suzukiWeilIntervalFormEmbedding a u) := by
  have hJb : suzukiApertureZeroExtendL2 (suzukiWeilIntervalFormEmbedding b v) =
      (ccmArchimedeanFormToAperture b v : SoninL2) := by
    change ((suzukiApertureL2Equiv b)
      ((suzukiApertureL2Equiv b).symm (ccmArchimedeanFormToAperture b v)) : SoninL2) =
        (ccmArchimedeanFormToAperture b v : SoninL2)
    rw [(suzukiApertureL2Equiv b).apply_symm_apply]
  have hJa : suzukiApertureZeroExtendL2 (suzukiWeilIntervalFormEmbedding a u) =
      (ccmArchimedeanFormToAperture a u : SoninL2) := by
    change ((suzukiApertureL2Equiv a)
      ((suzukiApertureL2Equiv a).symm (ccmArchimedeanFormToAperture a u)) : SoninL2) =
        (ccmArchimedeanFormToAperture a u : SoninL2)
    rw [(suzukiApertureL2Equiv a).apply_symm_apply]
  rw [← inner_suzukiApertureZeroExtendL2,
    ← inner_suzukiApertureZeroExtendL2, hJb, hJa,
    suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector,
    suzukiApertureZeroExtendL2_exponential_eq_ccmPolarL2Vector]
  exact inner_ccmPolarApertureVector_eq_of_val_eq hab c hvu

end RHTower
