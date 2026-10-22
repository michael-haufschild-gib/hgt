import Mathlib.Algebra.Algebra.Unitization
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicBruhatSimpleTensorReal

/-!
# The nonunital rational Bruhat--Schwartz coefficient algebra

Connes--Consani--Marcolli use the pointwise nonunital algebra `𝒮(𝔸_ℚ)` as the coefficient
algebra of the adeles-class-space crossed product.  Its archimedean and finite-adele factors
already occur in the project as modules.  This file supplies their missing pointwise
multiplications and proves all ring and complex-scalar compatibility laws.

The absence of a unit is essential: a nonzero constant function is not Schwartz on `ℝ`, and
the cyclic module of the crossed product is formed only after adjoining a unit.  No completion,
trace formula, zero-spectrum statement, or positivity premise is used here.
-/

noncomputable section

open scoped SchwartzMap

namespace GaloisForLFunctions
namespace RHTower

/-! ## Archimedean Schwartz factor -/

/-- Pointwise product of two complex Schwartz functions. -/
def ccmRationalArchimedeanSchwartzMul
    (f g : CCMRationalArchimedeanSchwartz) :
    CCMRationalArchimedeanSchwartz :=
  SchwartzMap.smulLeftCLM ℂ (f : ℝ → ℂ) g

instance : Mul CCMRationalArchimedeanSchwartz :=
  ⟨ccmRationalArchimedeanSchwartzMul⟩

@[simp]
theorem ccmRationalArchimedeanSchwartz_mul_apply
    (f g : CCMRationalArchimedeanSchwartz) (x : ℝ) :
    (f * g) x = f x * g x := by
  exact SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth g x

instance : NonUnitalCommRing CCMRationalArchimedeanSchwartz where
  zero_mul f := by
    ext x
    simp
  mul_zero f := by
    ext x
    simp
  mul_assoc f g h := by
    ext x
    simp [mul_assoc]
  left_distrib f g h := by
    ext x
    simp [left_distrib]
  right_distrib f g h := by
    ext x
    simp [right_distrib]
  mul_comm f g := by
    ext x
    simp [mul_comm]

instance : SMulCommClass ℂ CCMRationalArchimedeanSchwartz
    CCMRationalArchimedeanSchwartz where
  smul_comm z f g := by
    ext x
    simp [mul_assoc, mul_comm, mul_left_comm]

instance : IsScalarTower ℂ CCMRationalArchimedeanSchwartz
    CCMRationalArchimedeanSchwartz where
  smul_assoc z f g := by
    ext x
    simp [mul_assoc]

/-! ## Finite-adele Bruhat factor -/

/-- Pointwise product of compactly supported locally constant functions. -/
def ccmRationalFiniteBruhatMul
    (f g : CCMRationalFiniteBruhatSchwartz) :
    CCMRationalFiniteBruhatSchwartz :=
  ⟨f.1 * g.1, HasCompactSupport.mul_left g.2⟩

instance : Mul CCMRationalFiniteBruhatSchwartz :=
  ⟨ccmRationalFiniteBruhatMul⟩

@[simp]
theorem ccmRationalFiniteBruhat_mul_apply
    (f g : CCMRationalFiniteBruhatSchwartz)
    (x : CCMRationalFiniteAdele) :
    (f * g).1 x = f.1 x * g.1 x :=
  rfl

instance : NonUnitalCommRing CCMRationalFiniteBruhatSchwartz where
  zero_mul f := by
    apply Subtype.ext
    ext x
    simp
  mul_zero f := by
    apply Subtype.ext
    ext x
    simp
  mul_assoc f g h := by
    apply Subtype.ext
    ext x
    simp [mul_assoc]
  left_distrib f g h := by
    apply Subtype.ext
    ext x
    simp [left_distrib]
  right_distrib f g h := by
    apply Subtype.ext
    ext x
    simp [right_distrib]
  mul_comm f g := by
    apply Subtype.ext
    ext x
    simp [mul_comm]

instance : SMulCommClass ℂ CCMRationalFiniteBruhatSchwartz
    CCMRationalFiniteBruhatSchwartz where
  smul_comm z f g := by
    apply Subtype.ext
    ext x
    simp [mul_assoc, mul_comm, mul_left_comm]

instance : IsScalarTower ℂ CCMRationalFiniteBruhatSchwartz
    CCMRationalFiniteBruhatSchwartz where
  smul_assoc z f g := by
    apply Subtype.ext
    ext x
    simp [mul_assoc]

/-! ## Reflection is multiplicative -/

/-- Archimedean sign-conjugation is multiplicative for the pointwise product. -/
theorem ccmRationalArchimedeanSchwartzReflection_mul
    (f g : CCMRationalArchimedeanSchwartz) :
    ccmRationalArchimedeanSchwartzReflection (f * g) =
      ccmRationalArchimedeanSchwartzReflection f *
        ccmRationalArchimedeanSchwartzReflection g := by
  ext x
  simp

/-- Finite-adele sign-conjugation is multiplicative for the pointwise product. -/
theorem ccmRationalFiniteBruhatReflection_mul
    (f g : CCMRationalFiniteBruhatSchwartz) :
    ccmRationalFiniteBruhatReflection (f * g) =
      ccmRationalFiniteBruhatReflection f *
        ccmRationalFiniteBruhatReflection g := by
  apply Subtype.ext
  ext x
  simp

end RHTower
end GaloisForLFunctions
