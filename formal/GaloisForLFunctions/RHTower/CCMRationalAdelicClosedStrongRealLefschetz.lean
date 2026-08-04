import GaloisForLFunctions.RHTower.CCMRationalAdelicClosedStrongLefschetz
import GaloisForLFunctions.RHTower.CCMRationalAdelicRestrictionReal
import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicRealContinuity
import GaloisForLFunctions.RHTower.CCMRationalStrongCyclicLefschetz
import GaloisForLFunctions.RHTower.KRealCyclicCliffordTransgression

/-!
# Real and Clifford Lefschetz correspondences on the exact closed CCM quotient

Real-equivariance of adelic restriction and continuity of target conjugation
descend the even Real structure through the closure of the genuine restriction
range.  Every exact CCM Lefschetz correspondence commutes with this descended
involution, and multiplication by `i` gives its canonical anti-Real Clifford
transgression on the literal Definition 4.10 quotient.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

private abbrev Section := CCMRationalClassSpaceSection

/-- Even Real cyclic structure on the exact closed relative CCM module. -/
def ccmRationalAdelicClosedStrongRelativeCyclicKReal :
    CyclicModule.KReal false
      CCMRationalAdelicClosedStrongRelativeCyclicModule :=
  ccmRationalAdelicReducedStrongCyclicKRealHom.closedCokernelKReal
    ccmRationalStrongCyclicTopology
    ccmRationalStrongCyclicKRealTopology

@[simp]
theorem ccmRationalAdelicClosedStrongRelativeCyclicKReal_sigma_mkQ
    (n : ℕ) (y : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalAdelicClosedStrongRelativeCyclicKReal.real n).sigma
        ((CCMRationalAdelicClosedStrongRestrictionRange n).mkQ y) =
      (CCMRationalAdelicClosedStrongRestrictionRange n).mkQ
        ((ccmRationalStrongCyclicTargetKReal.real n).sigma y) :=
  rfl

/-- **Exact Real CCM Lefschetz correspondence.** Every descended class-space
translation is Real-even on the literal closed relative cyclic module. -/
def ccmRationalAdelicClosedStrongLefschetzKReal (c : Section) :
    CyclicModule.KRealHom
      ccmRationalAdelicClosedStrongRelativeCyclicKReal
      ccmRationalAdelicClosedStrongRelativeCyclicKReal where
  toHom := ccmRationalAdelicClosedStrongLefschetz c
  real_naturality n q := by
    obtain ⟨y, rfl⟩ :=
      (CCMRationalAdelicClosedStrongRestrictionRange n).mkQ_surjective q
    change (CCMRationalAdelicClosedStrongRestrictionRange n).mkQ
        ((ccmRationalStrongCyclicTargetKReal.real n).sigma
          (ccmRationalStrongCyclicRightActionDegree c n y)) =
      (CCMRationalAdelicClosedStrongRestrictionRange n).mkQ
        (ccmRationalStrongCyclicRightActionDegree c n
          ((ccmRationalStrongCyclicTargetKReal.real n).sigma y))
    exact congrArg (CCMRationalAdelicClosedStrongRestrictionRange n).mkQ
      (ccmRationalStrongCyclicRightActionDegree_real c n y)

/-- Canonical anti-Real Clifford transgression of the exact closed-relative
Lefschetz correspondence. -/
def ccmRationalAdelicClosedStrongCliffordTransgression (c : Section) :
    CyclicModule.KRealAntiHom
      ccmRationalAdelicClosedStrongRelativeCyclicKReal
      ccmRationalAdelicClosedStrongRelativeCyclicKReal :=
  (ccmRationalAdelicClosedStrongLefschetzKReal c).cliffordTransgression

@[simp]
theorem ccmRationalAdelicClosedStrongCliffordTransgression_mkQ
    (c : Section) (n : ℕ)
    (y : CCMRationalStrongCyclicTarget.simplicial.degree n) :
    (ccmRationalAdelicClosedStrongCliffordTransgression c).toHom.simplicial.app
        (.op (.mk n))
        ((CCMRationalAdelicClosedStrongRestrictionRange n).mkQ y) =
      Complex.I • (CCMRationalAdelicClosedStrongRestrictionRange n).mkQ
        (ccmRationalStrongCyclicRightActionDegree c n y) :=
  rfl

/-- At the identity class, exact closed-relative transgression squares to
minus the identity in every cyclic degree. -/
theorem ccmRationalAdelicClosedStrongCliffordTransgression_one_sq
    (n : ℕ)
    (q : CCMRationalAdelicClosedStrongRelativeCyclicModule.simplicial.degree n) :
    (ccmRationalAdelicClosedStrongCliffordTransgression 1).toHom.simplicial.app
        (.op (.mk n))
      ((ccmRationalAdelicClosedStrongCliffordTransgression 1).toHom.simplicial.app
        (.op (.mk n)) q) = -q := by
  apply CyclicModule.KRealHom.cliffordTransgression_identity_sq
    (ccmRationalAdelicClosedStrongLefschetzKReal 1)
  intro m y
  exact ccmRationalAdelicClosedStrongLefschetz_one_degree m y

end GaloisForLFunctions.RHTower
