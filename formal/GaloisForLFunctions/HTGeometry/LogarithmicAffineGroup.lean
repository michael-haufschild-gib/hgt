import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

/-!
# The positive real affine group in logarithmic coordinates

Coordinates `(b,t)` represent `x ↦ exp(t) x + b`. Translations and positive
scalings form a semidirect product; the quotient formula records exactly when
two elements have the same translation coordinate. These algebraic formulas
require no continuity of a representation of the group.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The map `x ↦ exp(t) x + b`, in logarithmic slope coordinates. -/
@[ext] structure LogAffineGroup where
  shift : ℝ
  logScale : ℝ

namespace LogAffineGroup

instance : Mul LogAffineGroup := ⟨fun g h =>
  ⟨g.shift + Real.exp g.logScale * h.shift, g.logScale + h.logScale⟩⟩
instance : One LogAffineGroup := ⟨⟨0, 0⟩⟩
instance : Inv LogAffineGroup := ⟨fun g =>
  ⟨-Real.exp (-g.logScale) * g.shift, -g.logScale⟩⟩

@[simp] theorem shift_mul (g h : LogAffineGroup) :
    (g * h).shift = g.shift + Real.exp g.logScale * h.shift := rfl
@[simp] theorem logScale_mul (g h : LogAffineGroup) :
    (g * h).logScale = g.logScale + h.logScale := rfl
@[simp] theorem shift_one : (1 : LogAffineGroup).shift = 0 := rfl
@[simp] theorem logScale_one : (1 : LogAffineGroup).logScale = 0 := rfl
@[simp] theorem shift_inv (g : LogAffineGroup) :
    g⁻¹.shift = -Real.exp (-g.logScale) * g.shift := rfl
@[simp] theorem logScale_inv (g : LogAffineGroup) : g⁻¹.logScale = -g.logScale := rfl

instance : Group LogAffineGroup where
  mul_assoc g h k := by
    ext
    · simp only [shift_mul, logScale_mul, Real.exp_add]
      ring
    · simp only [logScale_mul]
      ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    ext
    · simp only [shift_mul, shift_inv, logScale_inv, shift_one]
      ring
    · simp

/-- Additive translation. -/
def translate (b : ℝ) : LogAffineGroup := ⟨b, 0⟩
/-- Positive dilation at logarithmic scale `t`. -/
def dilate (t : ℝ) : LogAffineGroup := ⟨0, t⟩

@[simp] theorem shift_translate (b : ℝ) : (translate b).shift = b := rfl
@[simp] theorem logScale_translate (b : ℝ) : (translate b).logScale = 0 := rfl
@[simp] theorem shift_dilate (t : ℝ) : (dilate t).shift = 0 := rfl
@[simp] theorem logScale_dilate (t : ℝ) : (dilate t).logScale = t := rfl

@[simp] theorem translate_zero : translate 0 = 1 := rfl
@[simp] theorem dilate_zero : dilate 0 = 1 := rfl

theorem translate_add (a b : ℝ) : translate (a + b) = translate a * translate b := by
  ext <;> simp

theorem dilate_add (s t : ℝ) : dilate (s + t) = dilate s * dilate t := by
  ext <;> simp

theorem dilate_translate (t b : ℝ) :
    dilate t * translate b * (dilate t)⁻¹ = translate (Real.exp t * b) := by
  ext <;> simp

/-- Quotients keep equal translation coordinates exactly equal. -/
theorem inv_mul_coordinates (g h : LogAffineGroup) :
    g⁻¹ * h = ⟨Real.exp (-g.logScale) * (h.shift - g.shift), h.logScale - g.logScale⟩ := by
  ext
  · simp only [shift_mul, shift_inv, logScale_inv]
    ring
  · simp only [logScale_mul, logScale_inv]
    ring

#print axioms inv_mul_coordinates
end LogAffineGroup
end GaloisForLFunctions.HTGeometry
