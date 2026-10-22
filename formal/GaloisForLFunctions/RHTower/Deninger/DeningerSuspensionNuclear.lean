import GaloisForLFunctions.RHTower.Deninger.DeningerTestSpaceComplex
import GaloisForLFunctions.RHTower.Deninger.DeningerSmoothCharacterBasis
import GaloisForLFunctions.RHTower.Deninger.DeningerTensorNuclear

/-!
# The suspension of a test subspace is nuclear

A subspace of the locally constant test space is nuclear, the smooth periodic test space is
nuclear, and the projective tensor product of two nuclear spaces is nuclear.  So the tensor
product of a distinguished subspace of test functions with the smooth functions of a suspension
coordinate is nuclear.

* `deningerSuspension_isNuclearSpaceC` : **the suspension of a test subspace is nuclear.**
-/

namespace RHTower

section Suspension

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
variable {T : ℝ} [Fact (0 < T)]

/-- The additive group of the suspension tensor product, given explicitly to avoid an instance
diamond between the two additive monoid structures of a submodule. -/
local instance deningerSuspensionAddCommGroup (F : Submodule ℂ (DeningerTestSpaceC Y)) :
    AddCommGroup (TensorProduct ℂ ↥F ↥(DeningerSmoothPeriodic T)) :=
  @TensorProduct.addCommGroup ℂ _ ↥F ↥(DeningerSmoothPeriodic T) _ _ _ _

/-- **The suspension of a subspace of test functions is nuclear**: the projective tensor product
of a subspace of the locally constant test space with the smooth functions of the suspension
coordinate. -/
theorem deningerSuspension_isNuclearSpaceC (hT : 0 < T)
    (F : Submodule ℂ (DeningerTestSpaceC Y)) :
    DeningerIsNuclearSpaceC (fun ij : Seminorm ℂ (DeningerTestSpaceC Y) × ℕ =>
      deningerTensorSeminorm (deningerRestrictSeminorm F ij.1)
        (deningerSmoothSeminorm hT ij.2)) :=
  deningerIsNuclearSpaceC_tensor
    (fun p : Seminorm ℂ (DeningerTestSpaceC Y) => deningerRestrictSeminorm F p)
    (deningerSmoothSeminorm hT)
    (deningerTestSubspaceC_isNuclearSpace F)
    (deningerSmoothPeriodic_isNuclearSpace hT)

end Suspension

end RHTower
