import GaloisForLFunctions.RHTower.Deninger.DeningerQuotientNuclearCompleted
import GaloisForLFunctions.RHTower.Deninger.DeningerPoissonCokernel

/-!
# The cokernel of the Poisson operator is nuclear

The radial space is nuclear in the completed formulation, and quotients of completed-nuclear spaces
are completed-nuclear, so the cokernel of the Poisson operator carries a nuclear presentation: the
quotient family of the radial presentation by the range of the operator.

Together with the nuclearity of the two radial spaces and the exactness of the sequence, this is
the vector-space and nuclearity content of the card's `(4)`; the strictness of the sequence is what
still rests on Meyer's zeta estimate.

* `deningerMZetaFamily` : the quotient presentation of `M_ζ`.
* `deningerIsNuclearSpaceC_mZeta` : **`M_ζ` is nuclear.**
-/

open scoped Real SchwartzMap
open GaloisForLFunctions

noncomputable section

namespace RHTower

/-- The quotient presentation of the cokernel `M_ζ`. -/
def deningerMZetaFamily :
    SeminormFamily ℂ (deningerRadialCompat ⧸ LinearMap.range deningerPoissonLM)
      (Finset ℤ × (ℤ → ℕ)) :=
  fun i => deningerQuotientSeminorm (LinearMap.range deningerPoissonLM)
    (deningerRestrictSeminorm deningerRadialCompat
      (deningerPiFamily (fun _ : ℤ => (shiftedSeminorm : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ)) i))

/-- **The cokernel of the Poisson operator is a nuclear space.**  It is the quotient of the radial
space, which is nuclear, by the range of the operator. -/
theorem deningerIsNuclearSpaceC_mZeta : DeningerIsNuclearSpaceC deningerMZetaFamily :=
  deningerIsNuclearSpaceC_quotient_of_C _ (LinearMap.range deningerPoissonLM)
    deningerIsNuclearSpaceC_radialCompat

end RHTower

end
