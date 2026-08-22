import GaloisForLFunctions.RHTower.SoninApertureFourierParityNoGo

/-!
# The Sonine carrier is Fourier invariant

For an even vector the cosine transform preserves the Sonine carrier: this is the corpus's
`evenFourierTransform_mem_evenCentralSoninCarrier` read in the ambient `L²(ℝ)`.  It is the
prerequisite for welding the two half-plane branches of the completed Mellin transform
(Burnol, arXiv:math/0203120, Thm. 2.1): the reflected branch is the branch of `𝓕 f`, which must
itself be a Sonine vector at the same aperture.

## Main results

* `fourierUnitary_mem_centralSoninCarrier`

The corpus already owns evenness preservation
(`SoninMixedPhysicalBlockNonvanishing.fourierUnitary_mem_evenSubspace`).
-/

noncomputable section

namespace RHTower

/-- **The Fourier transform preserves the Sonine carrier on even vectors.** -/
theorem fourierUnitary_mem_centralSoninCarrier {a : ℝ} {f : SoninL2} (hev : f ∈ evenSubspace)
    (hf : f ∈ centralSoninCarrier a) : fourierUnitary f ∈ centralSoninCarrier a := by
  have hF : (⟨f, hev⟩ : evenSubspace) ∈ evenCentralSoninCarrier a := by
    rw [evenCentralSoninCarrier, Submodule.mem_comap]
    exact hf
  have h := evenFourierTransform_mem_evenCentralSoninCarrier a hF
  rw [evenCentralSoninCarrier, Submodule.mem_comap, Submodule.subtype_apply] at h
  have hval : ((evenFourierTransform (⟨f, hev⟩ : evenSubspace) : evenSubspace) : SoninL2)
      = fourierUnitary f := coe_evenFourierTransform_apply _
  rw [hval] at h
  exact h

end RHTower
