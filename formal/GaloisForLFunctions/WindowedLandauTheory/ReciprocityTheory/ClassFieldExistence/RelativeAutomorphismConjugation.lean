import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbelianDescentFromInvariantFactor
import Mathlib.Tactic.Group

/-! Conjugation in a Galois tower restricts to a homomorphism on the
automorphisms fixing the middle field. -/

noncomputable section

namespace GlobalTheory.Reciprocity

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Normal K L]

local notation "G" => Gal(L/K)
local notation "H" => Gal(M/L)
local notation "Γ" => Gal(M/K)
local notation "r" => (AlgEquiv.restrictNormalHom L : Γ →* G)

/-- Conjugation by an ambient automorphism on the relative Galois group. -/
def relativeAutConj (t : Γ) : H →* H :=
  let e := restrictionKernelEquiv K L M
  e.toMonoidHom.comp <| (MonoidHom.mk'
    (conjugateIn (r).ker t) (fun x y => Subtype.ext (by
      change t * (x.val * y.val) * t⁻¹ = t * x.val * t⁻¹ * (t * y.val * t⁻¹)
      group))).comp e.symm.toMonoidHom

theorem relativeAutConj_apply (t : Γ) (s : H) (x : M) :
    relativeAutConj K L M t s x = t (s (t.symm x)) := rfl

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.relativeAutConj
