import GaloisForLFunctions.RHTower.DeningerSmoothCoeffInjective
import GaloisForLFunctions.RHTower.DeningerNuclearTransportC

/-!
# The smooth periodic test space is nuclear

The coefficient map identifies the smooth periodic functions with a subspace of the Köthe space of
rapidly decreasing sequences: it is injective, and by construction it matches the coefficient
seminorms with the Köthe seminorms restricted to its image.  The Köthe space is nuclear, subspaces
of nuclear spaces are nuclear, and nuclearity transports along the identification.

Hence the smooth periodic test space, graded by the weighted sums of the moduli of its Fourier
coefficients, is a nuclear space — the smooth factor a suspension tensor product needs.

* `deningerSmoothSeminorm` : the coefficient seminorms of the smooth periodic space.
* `deningerSmoothPeriodic_isNuclearSpaceC` : **the smooth periodic test space is nuclear.**
-/

namespace RHTower

section SmoothNuclear

variable {T : ℝ} [Fact (0 < T)]

/-- **The coefficient seminorms of the smooth periodic test space**: the weighted sums of the
moduli of the Fourier coefficients. -/
noncomputable def deningerSmoothSeminorm (hT : 0 < T) (k : ℕ) :
    Seminorm ℂ (DeningerSmoothPeriodic T) :=
  (deningerKotheSeminorm deningerFourierWeights k).comp (deningerSmoothCoeff hT)

omit [Fact (0 < T)] in
theorem deningerSmoothSeminorm_apply (hT : 0 < T) (k : ℕ) (f : DeningerSmoothPeriodic T) :
    deningerSmoothSeminorm hT k f
      = deningerKotheSeminorm deningerFourierWeights k (deningerSmoothCoeff hT f) := rfl

/-- **The smooth periodic test space is nuclear** for its coefficient seminorms. -/
theorem deningerSmoothPeriodic_isNuclearSpaceC (hT : 0 < T) :
    DeningerIsNuclearSpaceC (deningerSmoothSeminorm hT) := by
  classical
  set A := deningerSmoothCoeff (T := T) hT with hA
  have hinj : Function.Injective A := deningerSmoothCoeff_injective hT
  set R : Submodule ℂ (DeningerKotheCarrier ℂ deningerFourierWeights) := LinearMap.range A with hR
  have hsub : DeningerIsNuclearSpaceC
      (fun k : ℕ => deningerRestrictSeminorm R (deningerKotheSeminorm deningerFourierWeights k)) :=
    deningerIsNuclearSpaceC_subspace _ R deningerFourierKothe_isNuclearSpace
  refine deningerIsNuclearSpaceC_of_linearEquiv (deningerSmoothSeminorm hT)
    (fun k : ℕ => deningerRestrictSeminorm R (deningerKotheSeminorm deningerFourierWeights k))
    (LinearEquiv.ofInjective A hinj) (fun k f => ?_) hsub
  rfl

end SmoothNuclear

end RHTower
