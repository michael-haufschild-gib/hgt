import GaloisForLFunctions.HTGeometry.RegularInertiaAmplification
import Mathlib.Tactic

/-!
# Character clocks and symmetric translations satisfy the q-Onsager relations

An additive character and translation by a fixed group element form a Weyl
pair. Adding each operator to its inverse gives a representation of the
q-Onsager relations, including the finite cyclic inertia operators.
-/

noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry
variable {G : Type*} [AddCommGroup G]

/-- Multiplication by a character and its inverse. -/
def characterCosineClock (χ : AddChar G ℂ) : Module.End ℂ (G → ℂ) where
  toFun f x := (χ x + χ (-x)) * f x
  map_add' f g := by ext x; simp only [Pi.add_apply]; ring
  map_smul' c f := by ext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The two oriented translations along a group element. -/
def symmetricTranslation (h : G) : Module.End ℂ (G → ℂ) where
  toFun f x := f (x + h) + f (x - h)
  map_add' f g := by ext x; simp only [Pi.add_apply]; ring
  map_smul' c f := by ext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem characterCosineClock_apply (χ : AddChar G ℂ) (f : G → ℂ) (x : G) :
    characterCosineClock χ f x = (χ x + χ (-x)) * f x := rfl

@[simp] theorem symmetricTranslation_apply (h : G) (f : G → ℂ) (x : G) :
    symmetricTranslation h f x = f (x + h) + f (x - h) := rfl

/-- The cubic affine Serre polynomial on linear operators. -/
def operatorSerre (q : ℂ) (A B : Module.End ℂ (G → ℂ)) : Module.End ℂ (G → ℂ) :=
  A ^ 3 * B - (q + 1 + q⁻¹) • (A ^ 2 * B * A) +
    (q + 1 + q⁻¹) • (A * B * A ^ 2) - B * A ^ 3

/-- The character clock satisfies the first q-Onsager relation for every translation. -/
theorem characterCosineClock_onsager (χ : AddChar G ℂ) (h : G) :
    operatorSerre (χ h) (characterCosineClock χ) (symmetricTranslation h) =
      (-(χ h - (χ h)⁻¹) ^ 2) •
        (characterCosineClock χ * symmetricTranslation h -
          symmetricTranslation h * characterCosineClock χ) := by
  ext f x
  have hq : χ h ≠ 0 := (χ.val_isUnit h).ne_zero
  have hx : χ x ≠ 0 := (χ.val_isUnit x).ne_zero
  simp only [operatorSerre, pow_succ, pow_zero, one_mul, Module.End.mul_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, Pi.sub_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, characterCosineClock_apply,
    symmetricTranslation_apply, AddChar.map_add_eq_mul, AddChar.map_sub_eq_div,
    AddChar.map_neg_eq_inv]
  field_simp [hq, hx]
  ring

private theorem translation_onsager_scalar (q u v a b c d : ℂ) (hq : q ≠ 0) :
    ((u * q ^ 3 + v / q ^ 3) * a + 3 * (u * q + v / q) * b +
      3 * (u / q + v * q) * c + (u / q ^ 3 + v * q ^ 3) * d) -
    (q + 1 + q⁻¹) *
      ((u * q ^ 2 + v / q ^ 2) * (a + b) + 2 * (u + v) * (b + c) +
        (u / q ^ 2 + v * q ^ 2) * (c + d)) +
    (q + 1 + q⁻¹) *
      ((u * q + v / q) * (a + 2 * b + c) +
        (u / q + v * q) * (b + 2 * c + d)) -
    (u + v) * (a + 3 * b + 3 * c + d) =
    (-(q - q⁻¹) ^ 2) *
      ((u * q + v / q) * b + (u / q + v * q) * c - (u + v) * (b + c)) := by
  field_simp [hq]
  ring

private theorem symmetricTranslation_sq_apply (h : G) (f : G → ℂ) (x : G) :
    (symmetricTranslation h ^ 2) f x =
      f (x + h + h) + 2 * f x + f (x - h - h) := by
  simp only [pow_two, Module.End.mul_apply, symmetricTranslation_apply,
    add_sub_cancel_right, sub_add_cancel]
  ring

private theorem symmetricTranslation_cube_apply (h : G) (f : G → ℂ) (x : G) :
    (symmetricTranslation h ^ 3) f x =
      f (x + h + h + h) + 3 * f (x + h) + 3 * f (x - h) + f (x - h - h - h) := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, pow_succ, Module.End.mul_apply,
    symmetricTranslation_sq_apply]
  simp only [symmetricTranslation_apply, add_sub_cancel_right, sub_add_cancel]
  ring

/-- Symmetric translation satisfies the reverse q-Onsager relation. -/
theorem symmetricTranslation_onsager (χ : AddChar G ℂ) (h : G) :
    operatorSerre (χ h) (symmetricTranslation h) (characterCosineClock χ) =
      (-(χ h - (χ h)⁻¹) ^ 2) •
        (symmetricTranslation h * characterCosineClock χ -
          characterCosineClock χ * symmetricTranslation h) := by
  ext f x
  have hq : χ h ≠ 0 := (χ.val_isUnit h).ne_zero
  have hh := translation_onsager_scalar (χ h) (χ x) (χ x)⁻¹
    (f (x + h + h + h)) (f (x + h)) (f (x - h)) (f (x - h - h - h)) hq
  simp only [operatorSerre, Module.End.mul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, symmetricTranslation_cube_apply,
    symmetricTranslation_sq_apply, characterCosineClock_apply, symmetricTranslation_apply,
    AddChar.map_add_eq_mul, AddChar.map_sub_eq_div, AddChar.map_neg_eq_inv]
  simp only [add_sub_cancel_right, sub_add_cancel]
  convert hh using 1 <;>
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv] <;> ring

/-- Existing finite cyclic inertia, in both orientations, is the translation generator. -/
theorem symmetricTranslation_eq_regularInertia (n : ℕ) [NeZero n] (f : ZMod n → ℂ) :
    symmetricTranslation (1 : ZMod n) f =
      Matrix.mulVec (HTGeometry.regularInertia n 1 + HTGeometry.regularInertia n (-1)) f := by
  rw [Matrix.add_mulVec]
  simp only [HTGeometry.regularInertia, Matrix.permMatrix_mulVec,
    HTGeometry.regularTranslation, Equiv.coe_addRight]
  ext x
  simp only [symmetricTranslation_apply, Pi.add_apply, Int.cast_one, Int.cast_neg,
    neg_neg, sub_eq_add_neg, Function.comp_apply]
  ring

/-- Fourier transformation exchanges the cyclic translation generator with the character clock. -/
theorem finiteCyclic_fourier_translation (n : ℕ) [NeZero n] (f : ZMod n → ℂ) :
    ZMod.dft (symmetricTranslation (1 : ZMod n) f) =
      characterCosineClock ZMod.stdAddChar (ZMod.dft f) := by
  rw [symmetricTranslation_eq_regularInertia, Matrix.add_mulVec, map_add]
  ext k
  simp only [Pi.add_apply, HTGeometry.regularInertia_dft,
    characterCosineClock_apply, HTGeometry.regularEigenvalue_def,
    Int.cast_one, Int.cast_neg, neg_neg, neg_one_mul, one_mul]
  ring

/-- The reverse Fourier exchange holds with the same two generators. -/
theorem finiteCyclic_fourier_clock (n : ℕ) [NeZero n] (f : ZMod n → ℂ) :
    ZMod.dft (characterCosineClock ZMod.stdAddChar f) =
      symmetricTranslation (1 : ZMod n) (ZMod.dft f) := by
  ext k
  simp only [ZMod.dft_apply, characterCosineClock_apply, symmetricTranslation_apply,
    smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [show -(j * (k + 1)) = -(j * k) + -j by ring,
    show -(j * (k - 1)) = -(j * k) + j by ring]
  simp only [AddChar.map_add_eq_mul]
  ring

/-- Every finite cyclic inertia space carries both q-Onsager relations. -/
theorem finiteCyclic_onsager (n : ℕ) [NeZero n] :
    operatorSerre (ZMod.stdAddChar (1 : ZMod n))
        (characterCosineClock ZMod.stdAddChar) (symmetricTranslation (1 : ZMod n)) =
      (-(ZMod.stdAddChar (1 : ZMod n) - (ZMod.stdAddChar (1 : ZMod n))⁻¹) ^ 2) •
        (characterCosineClock ZMod.stdAddChar * symmetricTranslation (1 : ZMod n) -
          symmetricTranslation (1 : ZMod n) * characterCosineClock ZMod.stdAddChar) ∧
    operatorSerre (ZMod.stdAddChar (1 : ZMod n))
        (symmetricTranslation (1 : ZMod n)) (characterCosineClock ZMod.stdAddChar) =
      (-(ZMod.stdAddChar (1 : ZMod n) - (ZMod.stdAddChar (1 : ZMod n))⁻¹) ^ 2) •
        (symmetricTranslation (1 : ZMod n) * characterCosineClock ZMod.stdAddChar -
          characterCosineClock ZMod.stdAddChar * symmetricTranslation (1 : ZMod n)) :=
  ⟨characterCosineClock_onsager _ _, symmetricTranslation_onsager _ _⟩

end GaloisForLFunctions.BiarithmeticGeometry

