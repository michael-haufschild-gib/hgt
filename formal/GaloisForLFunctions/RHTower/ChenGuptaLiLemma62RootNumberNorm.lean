import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FunctionalEquation
import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicFourierParseval

/-!
# Chen--Gupta--Li Lemma 6.2: primitive Dirichlet root-number norm

Mathlib defines the root number by a normalized Gauss sum but does not expose
the norm-one theorem needed to make CGL's far-left functional estimate uniform
in the primitive character.  This module proves that fact from the primitive
Fourier-transform formula and exact finite cyclic Parseval.
-/

open Complex LSeries
open scoped LSeries.notation ZMod

namespace RHTower

noncomputable section

/-- **Primitive Dirichlet root numbers have norm one.**  This closes the
root-number factor in CGL's functional-equation bound without placing any
extra premise in the public theorem. -/
theorem cglLemma62_primitive_rootNumber_norm_one
    (P : CGLLemma62PrimitiveCharacter) : ‖P.character.rootNumber‖ = 1 := by
  classical
  letI : NeZero P.modulus.value := ⟨Nat.ne_of_gt P.modulus.positive⟩
  let g : ℂ := gaussSum P.character ZMod.stdAddChar
  let C : ℝ := ∑ a : ZMod P.modulus.value, Complex.normSq (P.character a)
  have hCpos : 0 < C := by
    have hone : Complex.normSq (P.character (1 : ZMod P.modulus.value)) = 1 := by
      simp [Complex.normSq_eq_norm_sq]
    have hle : Complex.normSq (P.character (1 : ZMod P.modulus.value)) ≤ C := by
      exact Finset.single_le_sum
        (fun a _ => Complex.normSq_nonneg (P.character a)) (Finset.mem_univ _)
    linarith
  have hinvNorm (a : ZMod P.modulus.value) :
      Complex.normSq (P.character⁻¹ a) = Complex.normSq (P.character a) := by
    by_cases ha : IsUnit a
    · rw [← ha.unit_spec]
      simp only [Complex.normSq_eq_norm_sq]
      rw [DirichletCharacter.unit_norm_eq_one,
        DirichletCharacter.unit_norm_eq_one]
    · rw [MulChar.map_nonunit _ ha, MulChar.map_nonunit _ ha]
  have hinvSum :
      ∑ k : ZMod P.modulus.value, Complex.normSq (P.character⁻¹ (-k)) = C := by
    calc
      _ = ∑ k : ZMod P.modulus.value, Complex.normSq (P.character⁻¹ k) := by
        exact Finset.sum_equiv (Equiv.neg (ZMod P.modulus.value)) (by simp)
          (fun _ _ => rfl)
      _ = C := by
        simp only [C]
        exact Finset.sum_congr rfl (fun k _ => hinvNorm k)
  have hnormSq : Complex.normSq g = (P.modulus.value : ℝ) := by
    have hparse := GaloisForLFunctions.RHTower.fieldOneFiniteCyclicFourier_parseval
      P.modulus.value P.character
    simp_rw [P.primitive.fourierTransform_eq_inv_mul_gaussSum,
      Complex.normSq_mul] at hparse
    rw [← Finset.sum_mul, hinvSum] at hparse
    change C * Complex.normSq g = (P.modulus.value : ℝ) * C at hparse
    apply mul_left_cancel₀ hCpos.ne'
    calc
      C * Complex.normSq g = (P.modulus.value : ℝ) * C := hparse
      _ = C * (P.modulus.value : ℝ) := mul_comm _ _
  have hnorm : ‖g‖ = (P.modulus.value : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      ‖g‖ = √(Complex.normSq g) := Complex.norm_def g
      _ = √(P.modulus.value : ℝ) := by rw [hnormSq]
      _ = (P.modulus.value : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  change ‖g / I ^ (if P.character.Even then 0 else 1) /
    (P.modulus.value : ℂ) ^ (1 / 2 : ℂ)‖ = 1
  have hqpos : 0 < (P.modulus.value : ℝ) := by
    exact_mod_cast P.modulus.positive
  rw [norm_div, norm_div, norm_pow, Complex.norm_I, one_pow,
    Complex.norm_natCast_cpow_of_pos P.modulus.positive, hnorm]
  simpa using (div_self (Real.rpow_pos_of_pos hqpos (1 / 2 : ℝ)).ne')

end

end RHTower
