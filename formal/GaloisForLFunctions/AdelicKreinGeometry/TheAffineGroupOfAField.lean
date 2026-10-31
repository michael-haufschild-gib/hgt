import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The affine group of a field

The maps `x ↦ ax + b` of a field `K`, with slope `a = g.linear 1` and shift `b = g 0`
(`apply_eq_slopeOf`), the translations `x ↦ x + b` and the dilations `x ↦ ux`. Over `ℚ` these are
`ArithmeticPositiveDuality.AffineGroupQ`, `affSlope`, `affShift`, `translation` and `dilation`
definitionally.

* `slopeOf (gh) = slopeOf g · slopeOf h`, `shiftOf (gh) = slopeOf g · shiftOf h + shiftOf g`.
* `shiftOf (g⁻¹h) = (slopeOf g)⁻¹ (shiftOf h − shiftOf g)` (`shiftOf_inv_mul`).
* The translations form a homomorphic image of `(K, +)` (`translationHomOf`).
-/

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

variable {K : Type*} [Field K]

/-- The affine group `x ↦ ax + b` of `K`. -/
abbrev AffineGroupOf (K : Type*) [Field K] : Type _ := K ≃ᵃ[K] K

/-- The slope `a` of `x ↦ ax + b`. -/
def slopeOf (g : AffineGroupOf K) : K := g.linear 1

/-- The shift `b` of `x ↦ ax + b`. -/
def shiftOf (g : AffineGroupOf K) : K := g 0

theorem apply_eq_slopeOf (g : AffineGroupOf K) (x : K) : g x = slopeOf g * x + shiftOf g := by
  have h := congrFun g.toAffineMap.decomp x
  simp only [Pi.add_apply] at h
  have h2 : g.toAffineMap.linear x = x * g.linear 1 := by
    change g.linear x = _
    rw [← smul_eq_mul, ← g.linear.map_smul, smul_eq_mul, mul_one]
  rw [show g x = g.toAffineMap x from rfl, h, h2, slopeOf, shiftOf, mul_comm]
  rfl

theorem slopeOf_ne_zero (g : AffineGroupOf K) : slopeOf g ≠ 0 := by
  intro h
  have : g.linear 1 = g.linear 0 := by rw [map_zero]; exact h
  exact one_ne_zero (g.linear.injective this)

theorem affineOf_ext {g h : AffineGroupOf K} (h1 : slopeOf g = slopeOf h)
    (h2 : shiftOf g = shiftOf h) : g = h := by
  ext x; rw [apply_eq_slopeOf g, apply_eq_slopeOf h, h1, h2]

theorem slopeOf_mul (g h : AffineGroupOf K) : slopeOf (g * h) = slopeOf g * slopeOf h := by
  have e1 := apply_eq_slopeOf (g * h) 1
  have e0 := apply_eq_slopeOf (g * h) 0
  rw [AffineEquiv.coe_mul, Function.comp_apply, apply_eq_slopeOf h, apply_eq_slopeOf g] at e1 e0
  linear_combination -(e1 - e0)

theorem shiftOf_mul (g h : AffineGroupOf K) :
    shiftOf (g * h) = slopeOf g * shiftOf h + shiftOf g := by
  have e0 := apply_eq_slopeOf (g * h) 0
  rw [AffineEquiv.coe_mul, Function.comp_apply, apply_eq_slopeOf h, apply_eq_slopeOf g] at e0
  linear_combination -e0

theorem slopeOf_one : slopeOf (1 : AffineGroupOf K) = 1 := by
  have := apply_eq_slopeOf (1 : AffineGroupOf K) 1
  have h0 := apply_eq_slopeOf (1 : AffineGroupOf K) 0
  simp only [AffineEquiv.coe_one, id] at this h0
  linear_combination -this + h0

theorem shiftOf_one : shiftOf (1 : AffineGroupOf K) = 0 := by simp [shiftOf]

theorem slopeOf_inv (g : AffineGroupOf K) : slopeOf g⁻¹ = (slopeOf g)⁻¹ := by
  have := slopeOf_mul g g⁻¹
  rw [mul_inv_cancel, slopeOf_one] at this
  have hs := slopeOf_ne_zero g
  field_simp
  linear_combination -this

theorem shiftOf_inv (g : AffineGroupOf K) : shiftOf g⁻¹ = -shiftOf g / slopeOf g := by
  have h := shiftOf_mul g g⁻¹
  rw [mul_inv_cancel, shiftOf_one] at h
  have hs := slopeOf_ne_zero g
  field_simp
  linear_combination -h

theorem shiftOf_inv_mul (g h : AffineGroupOf K) :
    shiftOf (g⁻¹ * h) = (slopeOf g)⁻¹ * (shiftOf h - shiftOf g) := by
  have := slopeOf_ne_zero g
  rw [shiftOf_mul, slopeOf_inv, shiftOf_inv]
  field_simp
  ring

/-- The translation `x ↦ x + b`. -/
def translationOf (b : K) : AffineGroupOf K := AffineEquiv.constVAdd K K b

/-- The dilations `x ↦ ux`. -/
def dilationOf : Kˣ →* AffineGroupOf K := AffineEquiv.homothetyUnitsMulHom 0

theorem dilationOf_apply (u : Kˣ) (x : K) : dilationOf u x = u * x := by
  simp [dilationOf, AffineMap.homothety_apply]

theorem slopeOf_translationOf (b : K) : slopeOf (translationOf b) = 1 := by
  simp [slopeOf, translationOf]

theorem shiftOf_translationOf (b : K) : shiftOf (translationOf b) = b := by
  simp [shiftOf, translationOf]

theorem slopeOf_dilationOf (u : Kˣ) : slopeOf (dilationOf u) = u := by
  have := apply_eq_slopeOf (dilationOf u) 1
  rw [dilationOf_apply] at this
  have h0 := apply_eq_slopeOf (dilationOf u) 0
  rw [dilationOf_apply] at h0
  linear_combination -this + h0

theorem shiftOf_dilationOf (u : Kˣ) : shiftOf (dilationOf u) = 0 := by
  simp [shiftOf, dilationOf_apply]

theorem translationOf_zero : translationOf (0 : K) = 1 :=
  affineOf_ext (by rw [slopeOf_translationOf, slopeOf_one])
    (by rw [shiftOf_translationOf, shiftOf_one])

theorem translationOf_add (a b : K) :
    translationOf (a + b) = translationOf a * translationOf b :=
  affineOf_ext (by rw [slopeOf_mul, slopeOf_translationOf, slopeOf_translationOf, one_mul,
      slopeOf_translationOf])
    (by rw [shiftOf_mul, slopeOf_translationOf, shiftOf_translationOf, shiftOf_translationOf,
      shiftOf_translationOf, one_mul, add_comm])

/-- The translations as a homomorphism `(K, +) → Aff(K)`. -/
def translationHomOf : Multiplicative K →* AffineGroupOf K where
  toFun b := translationOf (Multiplicative.toAdd b)
  map_one' := translationOf_zero
  map_mul' b b' := by rw [toAdd_mul, translationOf_add]

end GaloisForLFunctions.AdelicKreinGeometry
