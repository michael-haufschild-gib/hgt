/-
Portions adapted from OpenAI's Gauss-sum formalization, Apache-2.0.
See LICENSE and NOTICE in this directory for source attribution.
-/
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheTorsionCharacteristics
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Sextic characters become quadratic

The two finite Fourier sums factor into two Gauss sums for every character
power. For a primitive additive character and two nontrivial multiplicative
characters, the normalized factor has norm one. A sextic character therefore
becomes its quadratic third power without a loss in size.

The fourth power is exceptional: its transformed character is trivial and
its zero-frequency term has cardinality `#Fˣ`. Keeping this term distinguishes
the completed transform from its restriction to nonzero arguments.

Cubing a cubic Gauss sum preserves its Jacobi-sum phase. This identity is the
local algebra behind conversion of Möbius coefficients into theta coefficients.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.MetaplecticMobiusDescent

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- Fourier transformation, inversion of the nonzero frequency, and the square
of the inverse character. The omitted zero frequency is kept explicit. -/
noncomputable def characterConversion (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ h : Fˣ,
    (∑ t : F, (χ ^ j) t * ψ (-(h * t))) * ((χ⁻¹) ^ 2) h *
      ψ (x * ((h⁻¹ : Fˣ) : F))

private theorem unit_fourier_coefficient (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (h : Fˣ) :
    (∑ t : F, χ t * ψ (-(h * t))) =
      χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) := by
  simpa only [gaussSum, AddChar.mulShift_apply, neg_one_mul, mul_neg]
    using gaussSum_mulShift_eq χ (ψ.mulShift (-1)) h

private theorem gaussSum_eq_units_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
  classical
  calc
    gaussSum χ ψ = ∑ x ∈ (Finset.univ : Finset F).erase 0, χ x * ψ x := by
      simpa only [gaussSum, MulChar.map_zero, zero_mul, add_zero] using
        (Finset.sum_erase_add (Finset.univ : Finset F)
          (fun x => χ x * ψ x) (Finset.mem_univ (0 : F))).symm
    _ = ∑ x : {x : F // x ≠ 0}, χ x * ψ x := by
      apply Finset.sum_subtype
      intro x
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    _ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
      exact (Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)).symm

private theorem inversion_gauss (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (x : F) :
    (∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
      ψ (x * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ (j + 2)) (ψ.mulShift x) := by
  classical
  calc
    _ = ∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) (h⁻¹)) *
        ψ (x * (h : F)) := by
      apply Fintype.sum_equiv (Equiv.inv Fˣ)
      intro h
      simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
    _ = ∑ h : Fˣ, (χ ^ (j + 2)) h * ψ (x * (h : F)) := by
      apply Finset.sum_congr rfl
      intro h _
      have he : (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2)⁻¹) = χ ^ (j + 2) := by group
      rw [← MulChar.inv_apply', he]
    _ = _ := by
      rw [gaussSum_eq_units_sum]
      rfl

/-- Exact conversion for every character power, including both exceptional
powers. No cancellation estimate or nontriviality premise is used. -/
theorem characterConversion_eq_gaussProduct (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (j : ℕ) (x : F) :
    characterConversion χ ψ j x = (Fintype.card F : ℂ)⁻¹ *
      gaussSum (χ ^ j) (ψ.mulShift (-1)) *
      gaussSum (χ ^ (j + 2)) (ψ.mulShift x) := by
  unfold characterConversion
  simp_rw [unit_fourier_coefficient]
  have hsum :
      (∑ h : Fˣ,
        ((χ ^ j)⁻¹ h * gaussSum (χ ^ j) (ψ.mulShift (-1))) *
          ((χ⁻¹) ^ 2) h * ψ (x * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        ∑ h : Fˣ, (((χ ^ j)⁻¹ * (χ⁻¹) ^ 2) h) *
          ψ (x * ((h⁻¹ : Fˣ) : F)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [MulChar.mul_apply]
    ring
  rw [hsum, inversion_gauss]
  ring

private theorem gaussSum_mulShift_any (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (x : F) :
    gaussSum χ (ψ.mulShift x) = χ⁻¹ x * gaussSum χ ψ := by
  by_cases hx : x = 0
  · subst x
    have he : ψ.mulShift (0 : F) = 1 := by ext t; simp
    rw [he, gaussSum_one_right hχ]
    rw [MulChar.map_zero, zero_mul]
  · simpa only [Units.val_mk0] using gaussSum_mulShift_eq χ ψ (Units.mk0 x hx)

/-- Away from the exceptional output character, conversion is a scalar
multiple of the inverse character with exponent `j + 2`. -/
theorem characterConversion_eq_character (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (j : ℕ) (h : χ ^ (j + 2) ≠ 1) (x : F) :
    characterConversion χ ψ j x =
      ((Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
        gaussSum (χ ^ (j + 2)) ψ) * (χ ^ (j + 2))⁻¹ x := by
  rw [characterConversion_eq_gaussProduct, gaussSum_mulShift_any _ _ h]
  ring

/-- A sextic character becomes a quadratic character after conversion. -/
theorem sextic_to_quadratic (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hχ3 : χ ^ 3 ≠ 1) (x : F) :
    characterConversion χ ψ 1 x =
      ((Fintype.card F : ℂ)⁻¹ * gaussSum χ (ψ.mulShift (-1)) *
        gaussSum (χ ^ 3) ψ) * (χ ^ 3) x := by
  have hinv : (χ ^ 3)⁻¹ = χ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_add] using hχ
  simpa only [pow_one, hinv] using characterConversion_eq_character χ ψ 1 hχ3 x

/-- The exceptional fourth power has an explicit zero-frequency contribution;
it cannot be replaced by the zero-extended trivial character. -/
theorem sextic_fourth_power_at_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) :
    characterConversion χ ψ 4 0 =
      (Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ 4) (ψ.mulShift (-1)) *
        (Nat.card Fˣ : ℂ) := by
  rw [characterConversion_eq_gaussProduct, show 4 + 2 = 6 from rfl, hχ]
  have he : ψ.mulShift (0 : F) = 1 := by ext t; simp
  rw [he, gaussSum_one_one]

/-- On nonzero arguments the same exceptional row is constant. -/
theorem sextic_fourth_power_off_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hψ : ψ.IsPrimitive) {x : F} (hx : x ≠ 0) :
    characterConversion χ ψ 4 x =
      -((Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ 4) (ψ.mulShift (-1))) := by
  rw [characterConversion_eq_gaussProduct, show 4 + 2 = 6 from rfl, hχ,
    gaussSum_one_left (hψ hx)]
  ring

private theorem norm_gaussSum_sq (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  rw [← Complex.normSq_eq_norm_sq,
    ArithmeticEffectivityTheory.normSq_gaussSum_eq_card hχ hψ]

/-- Both nontrivial Gauss factors have square-root size, so their normalized
product has norm one. The sextic-to-quadratic conversion loses no size. -/
theorem characterConversion_scalar_norm (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj : χ ^ j ≠ 1) (hj2 : χ ^ (j + 2) ≠ 1) :
    ‖(Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
      gaussSum (χ ^ (j + 2)) ψ‖ = 1 := by
  have hneg : (ψ.mulShift (-1)).IsPrimitive := by
    intro a ha
    rw [AddChar.mulShift_mulShift]
    exact hψ (mul_ne_zero (neg_ne_zero.mpr one_ne_zero) ha)
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : ‖(Fintype.card F : ℂ)⁻¹ * gaussSum (χ ^ j) (ψ.mulShift (-1)) *
      gaussSum (χ ^ (j + 2)) ψ‖ ^ 2 = 1 := by
    simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_pow,
      norm_gaussSum_sq _ _ hj hneg, norm_gaussSum_sq _ _ hj2 hψ]
    field_simp
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa only [one_pow] using hs)

/-- The nonexceptional conversion preserves the pointwise character modulus,
including its zero at the origin. -/
theorem norm_characterConversion (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj : χ ^ j ≠ 1) (hj2 : χ ^ (j + 2) ≠ 1)
    (x : F) : ‖characterConversion χ ψ j x‖ = ‖(χ ^ (j + 2))⁻¹ x‖ := by
  rw [characterConversion_eq_character _ _ _ hj2, norm_mul,
    characterConversion_scalar_norm χ ψ hψ j hj hj2, one_mul]

/-- The cubic Gauss sum retains a Jacobi-sum phase after cubing. -/
theorem cubic_gauss_cube (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (horder : orderOf χ = 3) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 3 = (Fintype.card F : ℂ) * jacobiSum χ χ := by
  have hχ : χ ≠ 1 := by
    intro h
    simp only [h, orderOf_one] at horder
    norm_num at horder
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have ho : orderOf χ ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa only [pow_two] using h)
    rw [horder] at ho
    norm_num at ho
  have hneg : χ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (n := 3) (by decide)
      (by simpa only [horder] using pow_orderOf_eq_one χ)
  have hj := jacobiSum_mul_nontrivial hχ2 ψ
  have hg := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ hψ
  simp only [horder, Nat.reduceSub, pow_two, hneg, one_mul] at hg
  calc
    _ = gaussSum χ ψ * (gaussSum χ ψ * gaussSum χ ψ) := by ring
    _ = gaussSum χ ψ * (gaussSum (χ * χ) ψ * jacobiSum χ χ) := by rw [hj]
    _ = _ := by rw [← mul_assoc, hg]

end GaloisForLFunctions.MetaplecticMobiusDescent

#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.characterConversion_eq_gaussProduct
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.sextic_to_quadratic
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.sextic_fourth_power_at_zero
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.sextic_fourth_power_off_zero
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.norm_characterConversion
#print axioms GaloisForLFunctions.MetaplecticMobiusDescent.cubic_gauss_cube
