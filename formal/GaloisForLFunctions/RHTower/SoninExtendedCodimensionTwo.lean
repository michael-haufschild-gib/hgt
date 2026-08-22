import GaloisForLFunctions.RHTower.SoninExtendedApertureChain

/-!
# Burnol's Proposition 4.5: the Sonine carrier has codimension two in the extended space

`RHTower/SoninBandCodimensionTwo` computes the dimension drop between the sum of the two bands and
the sum of their mean-zero halves.  Dualising that computation turns it into the literal statement
of Burnol's Proposition 4.5: `K_a` sits inside `L_a` with a two-dimensional orthogonal complement.

## Main results

* `meanZeroBand_eq` and `centralMeanZeroFourier_eq` — the mean-zero bands in band form
* `finrank_centralSoninExtendedCarrier_inf_orthogonal_carrier` — **Burnol's Proposition 4.5**
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

open GaloisForLFunctions.HTGeometry

theorem meanZeroBand_eq (a : ℝ) :
    meanZeroBand a = centralPhysicalForbidden a ⊓ (ℂ ∙ bandIndicator a)ᗮ := rfl

theorem centralMeanZeroFourier_eq (a : ℝ) :
    centralMeanZeroFourier a = centralFourierForbidden a ⊓ (ℂ ∙ fourierBandIndicator a)ᗮ := rfl

/-- **Burnol's Proposition 4.5.**  The orthogonal complement of the Sonine space `K_a` inside the
extended Sonine space `L_a` has dimension exactly two. -/
theorem finrank_centralSoninExtendedCarrier_inf_orthogonal_carrier {a : ℝ} (ha : 0 < a) :
    Module.finrank ℂ
      (centralSoninExtendedCarrier a ⊓ (centralSoninCarrier a)ᗮ : Submodule ℂ SoninL2) = 2 := by
  rw [orthogonal_centralSoninCarrier ha, centralSoninExtendedCarrier, meanZeroBand_eq,
    centralMeanZeroFourier_eq, inf_comm]
  exact finrank_soninBandComplement_eq_two ha

end RHTower

end
