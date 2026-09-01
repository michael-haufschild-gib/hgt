import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateEquation258Full
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicPrimitive

/-!
# Exact two-adic Tate-phase dichotomy for the Q8 source

The actual Q8 decomposition carrier at two is cyclic of order four, its
inertia restriction is quadratic, and its two Artin channels are inverse.
The remaining arithmetic identification must select one of the two primitive
quadratic angular characters of conductor eight.  This leaf closes the
analytic part without making that selection.

For every primitive quadratic angular character modulo eight and every
unramified radial phase `ρ`, the source/inverse Tate-phase product is exactly
`χ(-1)`.  Thus the radial order-four orientation cancels completely.  The
two explicit conductor-eight choices give signs `+1` and `-1`, respectively.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-- Primitive conductor-eight candidate attached to discriminant `8`. -/
def q8TwoAdicEvenPrimitiveTateCharacter :
    FieldOnePadicPrimitiveAngularCharacter 2 3 :=
  ⟨_root_.RHTower.quadraticCharacterEight, by
    simpa using _root_.RHTower.quadraticCharacterEight_isPrimitive⟩

/-- Primitive conductor-eight candidate attached to discriminant `-8`. -/
def q8TwoAdicOddPrimitiveTateCharacter :
    FieldOnePadicPrimitiveAngularCharacter 2 3 :=
  ⟨_root_.RHTower.quadraticCharacterEightPrime, by
    simpa using _root_.RHTower.quadraticCharacterEightPrime_isPrimitive⟩

/-- Same-additive Gauss square at conductor eight.  The proof uses the
independently proved primitive Gauss norm and additive-phase reversal, not a
finite evaluation of the sum. -/
theorem fieldOnePadicTwoQuadraticGaussSum_sq
    (χ : FieldOnePadicPrimitiveAngularCharacter 2 3)
    (hχquad : χ.1.IsQuadratic) :
    gaussSum χ.1 ZMod.stdAddChar ^ 2 =
      χ.1 (-1 : ZMod 8) * 8 := by
  let g : ℂ := gaussSum χ.1 ZMod.stdAddChar
  have hnorm :=
    normSq_gaussSum_fieldOnePadicPrimitiveAngularCharacter 2 3 χ
  have hconj : star g = gaussSum χ.1 ZMod.stdAddChar⁻¹ := by
    calc
      star g = gaussSum χ.1⁻¹ ZMod.stdAddChar⁻¹ := by
        exact star_gaussSum_eq χ.1 ZMod.stdAddChar
      _ = gaussSum χ.1 ZMod.stdAddChar⁻¹ := by rw [hχquad.inv]
  have hshift :
      χ.1 (-1 : ZMod 8) * gaussSum χ.1 ZMod.stdAddChar⁻¹ =
        gaussSum χ.1 ZMod.stdAddChar := by
    rw [ZMod.stdAddChar.inv_mulShift, ← Units.coe_neg_one]
    exact gaussSum_mulShift χ.1 ZMod.stdAddChar (-1)
  rw [← hconj] at hshift
  change g ^ 2 = χ.1 (-1 : ZMod 8) * 8
  calc
    g ^ 2 = g * g := pow_two g
    _ = (χ.1 (-1 : ZMod 8) * star g) * g := by rw [hshift]
    _ = χ.1 (-1 : ZMod 8) * (star g * g) := by ring
    _ = χ.1 (-1 : ZMod 8) * Complex.normSq g := by
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    _ = χ.1 (-1 : ZMod 8) * 8 := by
      norm_num at hnorm
      rw [show (Complex.normSq g : ℂ) = 8 by exact_mod_cast hnorm]

/-- Exact dyadic analytic reduction: inverse Artin channels cancel every
unramified radial orientation, leaving only the angular norm bit `χ(-1)`. -/
theorem fieldOnePadicTwoQuadraticTatePhase_mul_inverse_eq_negOne
    (χ : FieldOnePadicPrimitiveAngularCharacter 2 3)
    (hχquad : χ.1.IsQuadratic) (ρ : Circle) :
    fieldOnePadicRamifiedTatePhase 2 3 χ ρ *
        fieldOnePadicRamifiedTatePhase 2 3
          (fieldOnePadicPrimitiveAngularCharacterInv 2 3 χ) ρ⁻¹ =
      χ.1 (-1 : ZMod 8) := by
  have hχminus : χ.1 (-1 : ZMod 8) ≠ 0 := by
    rw [MulChar.apply_ne_zero_iff]
    exact ⟨-1, by simp⟩
  have hχinv : χ.1⁻¹ = χ.1 := hχquad.inv
  have hχObjInv :
      fieldOnePadicPrimitiveAngularCharacterInv 2 3 χ = χ := by
    exact Subtype.ext hχinv
  have hχminusSq : χ.1 (-1 : ZMod 8) ^ 2 = 1 := by
    rcases hχquad (-1 : ZMod 8) with hzero | hone | hneg
    · exact (hχminus hzero).elim
    · rw [hone]
      norm_num
    · rw [hneg]
      norm_num
  have hsqrt : ((Real.sqrt (8 : ℝ) : ℂ)⁻¹) ^ 2 = (8 : ℂ)⁻¹ := by
    rw [inv_pow]
    congr 1
    norm_cast
    rw [Real.sq_sqrt]
    norm_num
  have hgauss := fieldOnePadicTwoQuadraticGaussSum_sq χ hχquad
  simp only [fieldOnePadicRamifiedTatePhase,
    fieldOnePadicPrimitiveGaussPhase]
  norm_num only [Nat.reducePow]
  simp only [hχObjInv]
  rw [show (((ρ⁻¹ : Circle) : ℂ) ^ 3) = (((ρ : ℂ) ^ 3)⁻¹) by simp]
  rw [show χ.1 (-1 : ZMod 8) * (ρ : ℂ) ^ 3 *
          ((Real.sqrt (8 : ℝ) : ℂ)⁻¹ * gaussSum χ.1 ZMod.stdAddChar) *
          (χ.1 (-1 : ZMod 8) * ((ρ : ℂ) ^ 3)⁻¹ *
            ((Real.sqrt (8 : ℝ) : ℂ)⁻¹ * gaussSum χ.1 ZMod.stdAddChar)) =
        (χ.1 (-1 : ZMod 8) ^ 2) *
        (((ρ : ℂ) ^ 3) * ((ρ : ℂ) ^ 3)⁻¹) *
        (((Real.sqrt (8 : ℝ) : ℂ)⁻¹) ^ 2) *
        (gaussSum χ.1 ZMod.stdAddChar ^ 2) by ring]
  have hrho0 : (ρ : ℂ) ≠ 0 := by
    intro hzero
    have hnorm := Circle.norm_coe ρ
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hrho : ((ρ : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ hrho0
  rw [hχminusSq, mul_inv_cancel₀ hrho, one_mul, one_mul,
    hsqrt, hgauss]
  field_simp

theorem q8TwoAdicEvenPrimitiveTateCharacter_isQuadratic :
    q8TwoAdicEvenPrimitiveTateCharacter.1.IsQuadratic :=
  _root_.RHTower.quadraticCharacterEight_isQuadratic

theorem q8TwoAdicOddPrimitiveTateCharacter_isQuadratic :
    q8TwoAdicOddPrimitiveTateCharacter.1.IsQuadratic :=
  _root_.RHTower.quadraticCharacterEightPrime_isQuadratic

@[simp] theorem q8TwoAdicEvenPrimitiveTateCharacter_neg_one :
    q8TwoAdicEvenPrimitiveTateCharacter.1 (-1 : ZMod 8) = 1 := by
  have hneg : (-1 : ZMod 8) = (7 : ZMod 8) := by
    change ((-1 : ℤ) : ZMod 8) = ((7 : ℤ) : ZMod 8)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  rw [hneg]
  norm_num [q8TwoAdicEvenPrimitiveTateCharacter,
    _root_.RHTower.quadraticCharacterEight, ZMod.χ₈]

@[simp] theorem q8TwoAdicOddPrimitiveTateCharacter_neg_one :
    q8TwoAdicOddPrimitiveTateCharacter.1 (-1 : ZMod 8) = -1 := by
  have hneg : (-1 : ZMod 8) = (7 : ZMod 8) := by
    change ((-1 : ℤ) : ZMod 8) = ((7 : ℤ) : ZMod 8)
    rw [ZMod.intCast_eq_intCast_iff']
    norm_num
  rw [hneg]
  norm_num [q8TwoAdicOddPrimitiveTateCharacter,
    _root_.RHTower.quadraticCharacterEightPrime, ZMod.χ₈']

/-- Discriminant-eight candidate has dyadic source/inverse sign `+1`. -/
theorem q8TwoAdicEvenTatePhase_pair_eq_one (ρ : Circle) :
    fieldOnePadicRamifiedTatePhase 2 3
        q8TwoAdicEvenPrimitiveTateCharacter ρ *
      fieldOnePadicRamifiedTatePhase 2 3
        (fieldOnePadicPrimitiveAngularCharacterInv 2 3
          q8TwoAdicEvenPrimitiveTateCharacter) ρ⁻¹ = 1 := by
  rw [fieldOnePadicTwoQuadraticTatePhase_mul_inverse_eq_negOne
    q8TwoAdicEvenPrimitiveTateCharacter
    q8TwoAdicEvenPrimitiveTateCharacter_isQuadratic]
  exact q8TwoAdicEvenPrimitiveTateCharacter_neg_one

/-- Discriminant-minus-eight candidate has dyadic source/inverse sign `-1`. -/
theorem q8TwoAdicOddTatePhase_pair_eq_neg_one (ρ : Circle) :
    fieldOnePadicRamifiedTatePhase 2 3
        q8TwoAdicOddPrimitiveTateCharacter ρ *
      fieldOnePadicRamifiedTatePhase 2 3
        (fieldOnePadicPrimitiveAngularCharacterInv 2 3
          q8TwoAdicOddPrimitiveTateCharacter) ρ⁻¹ = -1 := by
  rw [fieldOnePadicTwoQuadraticTatePhase_mul_inverse_eq_negOne
    q8TwoAdicOddPrimitiveTateCharacter
    q8TwoAdicOddPrimitiveTateCharacter_isQuadratic]
  exact q8TwoAdicOddPrimitiveTateCharacter_neg_one

end


end GaloisForLFunctions.RHTower
