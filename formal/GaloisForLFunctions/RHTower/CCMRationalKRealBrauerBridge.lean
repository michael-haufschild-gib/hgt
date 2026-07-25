import GaloisForLFunctions.RHTower.CCMRationalQuaternionicMoritaFiber
import GaloisForLFunctions.RHTower.KRealKernelCokernel

/-!
# `K_R` bridge for the rational CCM Morita fiber

This file bundles the rational CCM sign-reflection as an odd object of Deninger's `K_R`.
It also bundles the induced endomorphism involution as an even `K_R` object and records that its
fixed points are precisely the endomorphisms commuting with the odd quaternionic generator.

Only algebraic function spaces and endomorphisms occur. No Hilbert completion, cyclic homology,
positivity, zero spectrum, or Riemann-hypothesis premise occurs.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- The algebraic rational CCM Morita fiber is an odd object of Deninger's `K_R`. -/
def ccmRationalMoritaKRealOdd :
    KRealStructure true (CCMRationalUnit → ℂ) where
  sigma := ccmRationalQuaternionicReflectionₛₗ
  sq f := by
    change ccmRationalQuaternionicReflection
      (ccmRationalQuaternionicReflection f) = -f
    exact ccmRationalQuaternionicReflection_sq f

/--
The endomorphism algebra of the odd rational CCM carrier has an even Real structure.
Its non-split quaternionic type is retained by the fixed algebra, not by the square.
-/
def ccmRationalEndomorphismKRealEven :
    KRealStructure false (Module.End ℂ (CCMRationalUnit → ℂ)) where
  sigma := ccmRationalEndomorphismRealStructureₛₗ
  sq T := by
    change ccmRationalEndomorphismRealStructure
      (ccmRationalEndomorphismRealStructure T) = T
    exact ccmRationalEndomorphismRealStructure_sq T

/-- Fixed points of the even endomorphism Real structure are the quaternionic-linear maps. -/
theorem ccmRationalEndomorphismKRealEven_fixed_iff
    (T : Module.End ℂ (CCMRationalUnit → ℂ)) :
    ccmRationalEndomorphismKRealEven.sigma T = T ↔
      ∀ f, T (ccmRationalMoritaKRealOdd.sigma f) =
        ccmRationalMoritaKRealOdd.sigma (T f) :=
  ccmRationalEndomorphismRealStructure_fixed_iff T

/-- Rational left scaling bundled as a complex-linear endomorphism. -/
def ccmRationalLeftScaleₗ (k : CCMRationalUnit) :
    Module.End ℂ (CCMRationalUnit → ℂ) where
  toFun := ccmRationalLeftScale k
  map_add' f g := by
    funext q
    rfl
  map_smul' z f := by
    funext q
    rfl

/-- Positive-sign rational scalings are morphisms of the odd `K_R` carrier. -/
def ccmRationalLeftScaleKRealMorphism
    (k : CCMRationalUnit) (hk : ccmRationalUnitSign k = 1) :
    KRealMorphism ccmRationalMoritaKRealOdd ccmRationalMoritaKRealOdd where
  map := ccmRationalLeftScaleₗ k
  commutes f := by
    change ccmRationalQuaternionicReflection (ccmRationalLeftScale k f) =
      ccmRationalLeftScale k (ccmRationalQuaternionicReflection f)
    rw [ccmRationalQuaternionicReflection_leftScale, hk]
    simp

end RHTower
end GaloisForLFunctions
