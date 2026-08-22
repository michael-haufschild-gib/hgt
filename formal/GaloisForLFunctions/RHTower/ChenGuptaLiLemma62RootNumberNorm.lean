import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FunctionalEquation
import Mathlib.Analysis.Fourier.ZMod

/-!
# Chen--Gupta--Li Lemma 6.2: primitive Dirichlet root-number norm

Mathlib defines the root number by a normalized Gauss sum but does not expose
the norm-one theorem needed to make CGL's far-left functional estimate uniform
in the primitive character.  This module proves that fact directly from the
primitive Fourier-transform formula and Fourier inversion on `ZMod q`.
-/

open Complex LSeries
open scoped LSeries.notation ZMod

namespace RHTower

noncomputable section

private theorem cglLemma62_isPrimitive_inv {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    χ⁻¹.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv,
    (DirichletCharacter.isPrimitive_def χ).mp hχ]

/-- Conjugating the Gauss sum changes the primitive character into its inverse;
the additive-character sign is absorbed by the value at `-1`. -/
private theorem cglLemma62_star_gaussSum_eq_neg_one_mul_inv
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    star (gaussSum χ ZMod.stdAddChar) =
      χ (-1 : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  rw [star_gaussSum_eq]
  have hshift :
      (χ⁻¹) (-1 : ZMod q) * gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ =
        gaussSum χ⁻¹ ZMod.stdAddChar := by
    simpa [AddChar.inv_mulShift] using
      (gaussSum_mulShift χ⁻¹ ZMod.stdAddChar (-1 : (ZMod q)ˣ))
  have hsign : χ (-1 : ZMod q) * (χ⁻¹) (-1 : ZMod q) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel,
      MulChar.one_apply (isUnit_one.neg)]
  calc
    gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ =
        1 * gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ := by ring
    _ = (χ (-1 : ZMod q) * (χ⁻¹) (-1 : ZMod q)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹ := by rw [hsign]
    _ = χ (-1 : ZMod q) *
        ((χ⁻¹) (-1 : ZMod q) * gaussSum χ⁻¹ (ZMod.stdAddChar)⁻¹) := by
          ring
    _ = χ (-1 : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar := by rw [hshift]

/-- Fourier inversion at `-1` evaluates the product of a primitive Gauss sum
with its inverse-character counterpart. -/
private theorem cglLemma62_gaussSum_mul_neg_one_mul_inv_gaussSum_eq_card
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar *
        (χ (-1 : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) = (q : ℂ) := by
  have hχinv := cglLemma62_isPrimitive_inv χ hχ
  have hfourier :
      (𝓕 (𝓕 χ)) (-1 : ZMod q) = (q : ℂ) := by
    simpa using congrFun (ZMod.dft_dft χ) (-1 : ZMod q)
  have hχdft :
      𝓕 χ = fun k => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar := by
    funext k
    exact hχ.fourierTransform_eq_inv_mul_gaussSum k
  have hχinvdft :
      𝓕 χ⁻¹ = fun k => χ (-k) * gaussSum χ⁻¹ ZMod.stdAddChar := by
    funext k
    simpa using hχinv.fourierTransform_eq_inv_mul_gaussSum k
  have hdouble :
      (𝓕 (𝓕 χ)) (-1 : ZMod q) =
        gaussSum χ ZMod.stdAddChar *
          (χ (-1 : ZMod q) * gaussSum χ⁻¹ ZMod.stdAddChar) := by
    rw [hχdft, ZMod.dft_mul_const, ZMod.dft_comp_neg, hχinvdft]
    simp only [Pi.mul_apply, neg_neg, neg_one]
    ring
  exact hdouble.symm.trans hfourier

/-- **Primitive Dirichlet root numbers have norm one.**  This closes the
root-number factor in CGL's functional-equation bound without placing any
extra premise in the public theorem. -/
theorem cglLemma62_primitive_rootNumber_norm_one
    (P : CGLLemma62PrimitiveCharacter) : ‖P.character.rootNumber‖ = 1 := by
  letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
  let g : ℂ := gaussSum P.character ZMod.stdAddChar
  have hstar := cglLemma62_star_gaussSum_eq_neg_one_mul_inv P.character
  have hproduct :=
    cglLemma62_gaussSum_mul_neg_one_mul_inv_gaussSum_eq_card P.character P.primitive
  have hconj : g * Complex.conj g = (P.modulus.value : ℂ) := by
    change g * Complex.conj g = (P.modulus.value : ℂ)
    calc
      g * Complex.conj g = g * star g := by rfl
      _ = g * (P.character (-1 : ZMod P.modulus.value) *
          gaussSum P.character⁻¹ ZMod.stdAddChar) := by
            simpa [g] using congrArg (fun z => g * z) hstar
      _ = (P.modulus.value : ℂ) := by simpa [g] using hproduct
  have hnormSq : Complex.normSq g = (P.modulus.value : ℝ) := by
    rw [Complex.mul_conj] at hconj
    exact_mod_cast hconj
  have hnorm : ‖g‖ = (P.modulus.value : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      ‖g‖ = √(Complex.normSq g) := Complex.norm_def g
      _ = √(P.modulus.value : ℝ) := by rw [hnormSq]
      _ = (P.modulus.value : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  change ‖g / I ^ (if P.character.Even then 0 else 1) /
    (P.modulus.value : ℂ) ^ (1 / 2 : ℂ)‖ = 1
  rw [norm_div, norm_div, norm_pow, Complex.norm_I, one_pow,
    Complex.norm_natCast_cpow_of_pos P.modulus.positive, hnorm]
  exact div_self (Real.rpow_ne_zero_of_pos (by exact_mod_cast P.modulus.positive) _)

end

end RHTower
