import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicClosedNonunitalStrongLefschetz
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicTwistedRestrictionReal
import GaloisForLFunctions.RHTower.KRealCyclicCliffordTransgression

/-!
# Real and Clifford Lefschetz correspondences on literal CCM Definition 4.10

The exact Real-equivariant restriction descends through its closed range in
the globally unitized nonunital strong target.  Class-space translation is
Real-even on this literal quotient.  Multiplication by `i` is therefore its
canonical anti-Real Clifford transgression.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection

/-- Literal target translation commutes with its even Real involution. -/
theorem ccmRationalNonunitalStrongCyclicRightActionDegree_real
    (c : Section) (n : ℕ)
    (y : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalNonunitalStrongCyclicTargetKReal.real n).sigma
        (ccmRationalNonunitalStrongCyclicRightActionDegree c n y) =
      ccmRationalNonunitalStrongCyclicRightActionDegree c n
        ((ccmRationalNonunitalStrongCyclicTargetKReal.real n).sigma y) := by
  apply ccmRationalNonunitalStrongCyclicEmbeddingDegree_injective n
  rw [ccmRationalNonunitalStrongCyclicEmbedding_real,
    ccmRationalNonunitalStrongCyclicEmbedding_rightAction,
    ccmRationalNonunitalStrongCyclicEmbedding_rightAction,
    ccmRationalNonunitalStrongCyclicEmbedding_real]
  exact ccmRationalStrongCyclicRightActionDegree_real c n
    (ccmRationalNonunitalStrongCyclicEmbeddingDegree n y)

/-- Even Real cyclic structure on literal CCM Definition 4.10. -/
def ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal :
    CyclicModule.KReal false
      CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule :=
  ccmRationalAdelicReducedNonunitalStrongCyclicKRealHom.closedCokernelKReal
    ccmRationalNonunitalStrongCyclicTopology
    ccmRationalNonunitalStrongCyclicKRealTopology

@[simp]
theorem ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal_sigma_mkQ
    (n : ℕ) (y : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal.real n).sigma
        ((CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ y) =
      (CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ
        ((ccmRationalNonunitalStrongCyclicTargetKReal.real n).sigma y) :=
  rfl

/-- Literal closed-relative CCM Lefschetz correspondence is Real-even. -/
def ccmRationalAdelicClosedNonunitalStrongLefschetzKReal (c : Section) :
    CyclicModule.KRealHom
      ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal
      ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal where
  toHom := ccmRationalAdelicClosedNonunitalStrongLefschetz c
  real_naturality n q := by
    obtain ⟨y, rfl⟩ :=
      (CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ_surjective q
    change (CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ
        ((ccmRationalNonunitalStrongCyclicTargetKReal.real n).sigma
          (ccmRationalNonunitalStrongCyclicRightActionDegree c n y)) =
      (CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ
        (ccmRationalNonunitalStrongCyclicRightActionDegree c n
          ((ccmRationalNonunitalStrongCyclicTargetKReal.real n).sigma y))
    exact congrArg
      (CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ
      (ccmRationalNonunitalStrongCyclicRightActionDegree_real c n y)

/-- Canonical anti-Real Clifford transgression of literal CCM Lefschetz. -/
def ccmRationalAdelicClosedNonunitalStrongCliffordTransgression
    (c : Section) :
    CyclicModule.KRealAntiHom
      ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal
      ccmRationalAdelicClosedNonunitalStrongRelativeCyclicKReal :=
  (ccmRationalAdelicClosedNonunitalStrongLefschetzKReal c).cliffordTransgression

@[simp]
theorem ccmRationalAdelicClosedNonunitalStrongCliffordTransgression_mkQ
    (c : Section) (n : ℕ)
    (y : CCMRationalNonunitalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalAdelicClosedNonunitalStrongCliffordTransgression c).toHom.simplicial.app
        (.op (.mk n))
        ((CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ y) =
      Complex.I •
        (CCMRationalAdelicClosedNonunitalStrongRestrictionRange n).mkQ
          (ccmRationalNonunitalStrongCyclicRightActionDegree c n y) :=
  rfl

/-- Identity transgression squares to minus identity in every cyclic degree. -/
theorem ccmRationalAdelicClosedNonunitalStrongCliffordTransgression_one_sq
    (n : ℕ)
    (q :
      CCMRationalAdelicClosedNonunitalStrongRelativeCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicClosedNonunitalStrongCliffordTransgression 1).toHom.simplicial.app
        (.op (.mk n))
      ((ccmRationalAdelicClosedNonunitalStrongCliffordTransgression 1).toHom.simplicial.app
        (.op (.mk n)) q) = -q := by
  apply CyclicModule.KRealHom.cliffordTransgression_identity_sq
    (ccmRationalAdelicClosedNonunitalStrongLefschetzKReal 1)
  intro m y
  exact ccmRationalAdelicClosedNonunitalStrongLefschetz_one_degree m y

end GaloisForLFunctions.RHTower
