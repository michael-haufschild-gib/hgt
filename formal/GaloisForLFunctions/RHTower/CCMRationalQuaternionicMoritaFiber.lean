import Mathlib.Tactic
import Mathlib.Data.Sign.Basic
import Mathlib.Algebra.Module.LinearMap.Star

/-!
# Quaternionic sign-reflection on the rational CCM Morita fiber

For `K = ℚ`, the Connes--Consani--Marcolli Morita fiber is canonically indexed by `ℚˣ`.
The sign character and the fixed-point-free reflection `q ↦ -q` define

`(J f)(q) = sign(q) * conj (f (-q))`.

This file proves unconditionally that `J` is complex conjugate-linear, `J² = -1`, and rational
left scaling by `k` has covariance sign `sign(k)`.  It also proves the complementary no-go:
the induced Real structure on matrix kernels squares to `+1`, so passage from the Morita module
to its endomorphism algebra erases the quaternionic central sign.

Only algebraic function and kernel identities are formalized here.  No summability, cyclic
comparison, positivity, zero spectrum, or Riemann-hypothesis premise occurs.
-/

noncomputable section

namespace GaloisForLFunctions
namespace RHTower

/-- Nonzero rational indices in the canonical rational CCM Morita fiber. -/
abbrev CCMRationalUnit := ℚˣ

/-- Complex-valued sign character of a nonzero rational index. -/
def ccmRationalUnitSign (q : CCMRationalUnit) : ℂ :=
  (SignType.sign (q : ℚ) : ℂ)

theorem ccmRationalUnit_coe_ne_zero (q : CCMRationalUnit) : (q : ℚ) ≠ 0 :=
  Units.ne_zero q

@[simp]
theorem ccmRationalUnitSign_neg (q : CCMRationalUnit) :
    ccmRationalUnitSign (-q) = -ccmRationalUnitSign q := by
  simp [ccmRationalUnitSign, Left.sign_neg]

@[simp]
theorem ccmRationalUnitSign_star (q : CCMRationalUnit) :
    star (ccmRationalUnitSign q) = ccmRationalUnitSign q := by
  change (starRingEnd ℂ) (SignType.sign (q : ℚ) : ℂ) =
    (SignType.sign (q : ℚ) : ℂ)
  exact SignType.map_cast (starRingEnd ℂ) _

@[simp]
theorem ccmRationalUnitSign_sq (q : CCMRationalUnit) :
    ccmRationalUnitSign q * ccmRationalUnitSign q = 1 := by
  rcases lt_or_gt_of_ne (ccmRationalUnit_coe_ne_zero q) with hq | hq
  · simp [ccmRationalUnitSign, sign_neg hq]
  · simp [ccmRationalUnitSign, sign_pos hq]

@[simp]
theorem ccmRationalUnitSign_mul (q r : CCMRationalUnit) :
    ccmRationalUnitSign (q * r) = ccmRationalUnitSign q * ccmRationalUnitSign r := by
  simp [ccmRationalUnitSign, sign_mul]

@[simp]
theorem ccmRationalUnitSign_inv (q : CCMRationalUnit) :
    ccmRationalUnitSign q⁻¹ = ccmRationalUnitSign q := by
  have hmul : ccmRationalUnitSign q⁻¹ * ccmRationalUnitSign q = 1 := by
    rw [← ccmRationalUnitSign_mul]
    simp [ccmRationalUnitSign]
  calc
    ccmRationalUnitSign q⁻¹ =
        ccmRationalUnitSign q⁻¹ * (ccmRationalUnitSign q * ccmRationalUnitSign q) := by
          rw [ccmRationalUnitSign_sq, mul_one]
    _ = (ccmRationalUnitSign q⁻¹ * ccmRationalUnitSign q) *
        ccmRationalUnitSign q := by ring
    _ = ccmRationalUnitSign q := by rw [hmul, one_mul]

/--
Quaternionic sign-reflection on the algebraic rational CCM fiber.

On the Hilbert subspace `ℓ²(ℚˣ)` the same pointwise formula is antiunitary because negation
permutes indices and the sign has norm one.
-/
def ccmRationalQuaternionicReflection
    (f : CCMRationalUnit → ℂ) (q : CCMRationalUnit) : ℂ :=
  ccmRationalUnitSign q * star (f (-q))

theorem ccmRationalQuaternionicReflection_add
    (f g : CCMRationalUnit → ℂ) :
    ccmRationalQuaternionicReflection (f + g) =
      ccmRationalQuaternionicReflection f + ccmRationalQuaternionicReflection g := by
  funext q
  simp [ccmRationalQuaternionicReflection, mul_add]

theorem ccmRationalQuaternionicReflection_smul
    (z : ℂ) (f : CCMRationalUnit → ℂ) :
    ccmRationalQuaternionicReflection (z • f) =
      star z • ccmRationalQuaternionicReflection f := by
  funext q
  simp [ccmRationalQuaternionicReflection]
  ring

/-- The rational CCM sign-reflection is genuinely quaternionic: `J² = -1`. -/
theorem ccmRationalQuaternionicReflection_sq
    (f : CCMRationalUnit → ℂ) :
    ccmRationalQuaternionicReflection (ccmRationalQuaternionicReflection f) = -f := by
  funext q
  simp only [ccmRationalQuaternionicReflection, Pi.neg_apply, neg_neg]
  rw [star_mul, ccmRationalUnitSign_star, star_star, ccmRationalUnitSign_neg]
  calc
    ccmRationalUnitSign q * (f q * -ccmRationalUnitSign q) =
        -(ccmRationalUnitSign q * ccmRationalUnitSign q) * f q := by ring
    _ = -f q := by rw [ccmRationalUnitSign_sq]; simp

/-- The rational CCM quaternionic reflection bundled as a complex conjugate-linear map. -/
def ccmRationalQuaternionicReflectionₛₗ :
    (CCMRationalUnit → ℂ) →ₗ⋆[ℂ] (CCMRationalUnit → ℂ) where
  toFun := ccmRationalQuaternionicReflection
  map_add' := ccmRationalQuaternionicReflection_add
  map_smul' z f := by
    rw [ccmRationalQuaternionicReflection_smul]
    rfl

/-- Left regular rational scaling on the algebraic Morita fiber. -/
def ccmRationalLeftScale (k : CCMRationalUnit) (f : CCMRationalUnit → ℂ)
    (q : CCMRationalUnit) : ℂ :=
  f (k⁻¹ * q)

/-- Quaternionic reflection commutes or anticommutes with scaling according to rational sign. -/
theorem ccmRationalQuaternionicReflection_leftScale
    (k : CCMRationalUnit) (f : CCMRationalUnit → ℂ) :
    ccmRationalQuaternionicReflection (ccmRationalLeftScale k f) =
      ccmRationalUnitSign k •
        ccmRationalLeftScale k (ccmRationalQuaternionicReflection f) := by
  funext q
  simp only [ccmRationalQuaternionicReflection, ccmRationalLeftScale,
    Pi.smul_apply, smul_eq_mul]
  rw [show -(k⁻¹ * q) = k⁻¹ * (-q) by simp]
  rw [ccmRationalUnitSign_mul, ccmRationalUnitSign_inv]
  calc
    ccmRationalUnitSign q * star (f (k⁻¹ * -q)) =
        (ccmRationalUnitSign k * ccmRationalUnitSign k) *
          (ccmRationalUnitSign q * star (f (k⁻¹ * -q))) := by
            rw [ccmRationalUnitSign_sq, one_mul]
    _ = ccmRationalUnitSign k *
        (ccmRationalUnitSign k * ccmRationalUnitSign q *
          star (f (k⁻¹ * -q))) := by ring

/-- Kernel-level Real structure induced by quaternionic conjugation of the Morita module. -/
def ccmRationalKernelRealStructure
    (T : CCMRationalUnit → CCMRationalUnit → ℂ)
    (x y : CCMRationalUnit) : ℂ :=
  ccmRationalUnitSign x * ccmRationalUnitSign y * star (T (-x) (-y))

/--
Endomorphism erasure law: although the Morita-module reflection squares to `-1`, its induced
kernel Real structure squares to `+1`.
-/
theorem ccmRationalKernelRealStructure_sq
    (T : CCMRationalUnit → CCMRationalUnit → ℂ) :
    ccmRationalKernelRealStructure (ccmRationalKernelRealStructure T) = T := by
  funext x y
  simp only [ccmRationalKernelRealStructure, neg_neg]
  rw [star_mul, star_mul, ccmRationalUnitSign_star, ccmRationalUnitSign_star, star_star]
  rw [ccmRationalUnitSign_neg, ccmRationalUnitSign_neg]
  calc
    ccmRationalUnitSign x * ccmRationalUnitSign y *
        (T x y * ((-ccmRationalUnitSign y) * (-ccmRationalUnitSign x))) =
      (ccmRationalUnitSign x * ccmRationalUnitSign x) *
        (ccmRationalUnitSign y * ccmRationalUnitSign y) * T x y := by ring
    _ = T x y := by
      rw [ccmRationalUnitSign_sq, ccmRationalUnitSign_sq]
      simp

/-- Algebraic form of a single CCM rational Morita matrix monomial. -/
def ccmRationalMonomialKernel
    (k : CCMRationalUnit) (φ : CCMRationalUnit → ℂ)
    (x y : CCMRationalUnit) : ℂ :=
  if k = x * y⁻¹ then φ x else 0

/-- The coefficient twist induced on a monomial by quaternionic kernel conjugation. -/
def ccmRationalMonomialRealTwist
    (k : CCMRationalUnit) (φ : CCMRationalUnit → ℂ)
    (x : CCMRationalUnit) : ℂ :=
  ccmRationalUnitSign k * star (φ (-x))

/-- Quaternionic kernel conjugation preserves the CCM monomial support and adds its sign grade. -/
theorem ccmRationalKernelRealStructure_monomial
    (k : CCMRationalUnit) (φ : CCMRationalUnit → ℂ) :
    ccmRationalKernelRealStructure (ccmRationalMonomialKernel k φ) =
      ccmRationalMonomialKernel k (ccmRationalMonomialRealTwist k φ) := by
  funext x y
  simp only [ccmRationalKernelRealStructure, ccmRationalMonomialKernel,
    ccmRationalMonomialRealTwist]
  by_cases h : k = x * y⁻¹
  · have hneg : k = (-x) * (-y)⁻¹ := by simpa using h
    rw [if_pos h, if_pos hneg]
    have hsign := congrArg ccmRationalUnitSign h
    rw [ccmRationalUnitSign_mul, ccmRationalUnitSign_inv] at hsign
    rw [hsign]
  · have hneg : k ≠ (-x) * (-y)⁻¹ := by simpa using h
    rw [if_neg h, if_neg hneg]
    simp

end RHTower
end GaloisForLFunctions
