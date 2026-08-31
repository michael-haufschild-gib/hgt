import GaloisForLFunctions.RHTower.DeningerQ8ActualMonomialSourceLaw
import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateFunctionalEquation
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace RHTower

noncomputable section

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩

noncomputable def deningerQ8FiveResidueSourceEquiv :
    Multiplicative (ZMod 4) ≃* (ZMod 5)ˣ := by
  letI : IsCyclic (ZMod 5)ˣ := ZMod.isCyclic_units_prime (by norm_num)
  exact mulEquivOfCyclicCardEq (by norm_num [Nat.totient_prime Nat.prime_five])

noncomputable def deningerQ8FiveResidueQuarticChar : MulChar (ZMod 5) ℂ :=
  MulChar.ofUnitHom
    (q8OrderFourCharacter.comp deningerQ8FiveResidueSourceEquiv.symm.toMonoidHom)

theorem deningerQ8FiveResidueQuarticChar_sourceGenerator :
    deningerQ8FiveResidueQuarticChar
        (deningerQ8FiveResidueSourceEquiv (Multiplicative.ofAdd (1 : ZMod 4)) : ZMod 5) =
      Complex.I := by
  rw [deningerQ8FiveResidueQuarticChar, MulChar.ofUnitHom_coe]
  change ((q8OrderFourCharacter
    (deningerQ8FiveResidueSourceEquiv.symm
      (deningerQ8FiveResidueSourceEquiv (Multiplicative.ofAdd (1 : ZMod 4)))) : ℂˣ) : ℂ) = _
  rw [deningerQ8FiveResidueSourceEquiv.symm_apply_apply]
  rw [q8OrderFourCharacter_apply]
  rw [ZMod.val_one'' (by norm_num : 4 ≠ 1), pow_one]

theorem deningerQ8FiveResidueQuarticChar_ne_one :
    deningerQ8FiveResidueQuarticChar ≠ 1 := by
  intro h
  have he := congrArg
    (fun χ : MulChar (ZMod 5) ℂ =>
      χ (deningerQ8FiveResidueSourceEquiv (Multiplicative.ofAdd (1 : ZMod 4)) : ZMod 5)) h
  rw [deningerQ8FiveResidueQuarticChar_sourceGenerator] at he
  have him := congrArg Complex.im he
  norm_num at him

theorem deningerQ8FiveResidueQuarticChar_sq_ne_one :
    deningerQ8FiveResidueQuarticChar ^ 2 ≠ 1 := by
  intro h
  have he := congrArg
    (fun χ : MulChar (ZMod 5) ℂ =>
      χ (deningerQ8FiveResidueSourceEquiv (Multiplicative.ofAdd (1 : ZMod 4)) : ZMod 5)) h
  rw [deningerQ8FiveResidueQuarticChar.pow_apply_coe, MulChar.one_apply_coe] at he
  rw [deningerQ8FiveResidueQuarticChar_sourceGenerator, Complex.I_sq] at he
  norm_num at he

theorem deningerQ8FiveResidueQuarticChar_fourth_eq_one :
    deningerQ8FiveResidueQuarticChar ^ 4 = 1 := by
  apply MulChar.ext
  intro u
  rw [deningerQ8FiveResidueQuarticChar.pow_apply_coe, MulChar.one_apply_coe]
  rw [deningerQ8FiveResidueQuarticChar, MulChar.ofUnitHom_coe]
  have hu : (deningerQ8FiveResidueSourceEquiv.symm u) ^ 4 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    rw [nsmul_eq_mul]
    rw [ZMod.natCast_self, zero_mul]
  have hmap :
      (q8OrderFourCharacter.comp
          deningerQ8FiveResidueSourceEquiv.symm.toMonoidHom u) ^ 4 = 1 := by
    change q8OrderFourCharacter (deningerQ8FiveResidueSourceEquiv.symm u) ^ 4 = 1
    rw [← map_pow, hu, map_one]
  exact congrArg Units.val hmap

theorem deningerQ8FiveResidueQuarticChar_orderOf_eq_four :
    orderOf deningerQ8FiveResidueQuarticChar = 4 := by
  change orderOf deningerQ8FiveResidueQuarticChar = 2 ^ 2
  apply orderOf_eq_prime_pow
  · simpa using deningerQ8FiveResidueQuarticChar_sq_ne_one
  · simpa using deningerQ8FiveResidueQuarticChar_fourth_eq_one

def deningerQ8FroehlichSplitFiveGaussianPair : ℂ :=
  (5 : ℂ)⁻¹ *
    (gaussSum deningerQ8FiveResidueQuarticChar ZMod.stdAddChar *
      gaussSum deningerQ8FiveResidueQuarticChar⁻¹ ZMod.stdAddChar⁻¹)

theorem deningerQ8FiveResidueQuarticGaussProduct_eq_five :
    gaussSum deningerQ8FiveResidueQuarticChar ZMod.stdAddChar *
        gaussSum deningerQ8FiveResidueQuarticChar⁻¹ ZMod.stdAddChar⁻¹ = 5 := by
  simpa using gaussSum_mul_gaussSum_eq_card
    deningerQ8FiveResidueQuarticChar_ne_one (ZMod.isPrimitive_stdAddChar 5)

theorem deningerQ8FroehlichSplitFiveGaussianPair_eq_one :
    deningerQ8FroehlichSplitFiveGaussianPair = 1 := by
  rw [deningerQ8FroehlichSplitFiveGaussianPair,
    deningerQ8FiveResidueQuarticGaussProduct_eq_five]
  norm_num

noncomputable def deningerQ8FortyOneQuadraticChar : MulChar (ZMod 41) ℂ :=
  (quadraticChar (ZMod 41)).ringHomComp (Int.castRingHom ℂ)

theorem deningerQ8FortyOneQuadraticChar_ne_one :
    deningerQ8FortyOneQuadraticChar ≠ 1 := by
  rw [deningerQ8FortyOneQuadraticChar]
  apply (MulChar.ringHomComp_ne_one_iff Int.cast_injective).2
  apply quadraticChar_ne_one
  norm_num [ZMod.ringChar_zmod_n]

theorem deningerQ8FortyOneQuadraticChar_neg_one_eq_one :
    deningerQ8FortyOneQuadraticChar (-1) = 1 := by
  rw [deningerQ8FortyOneQuadraticChar, MulChar.ringHomComp_apply]
  have hneg : (-1 : ZMod 41) ≠ 0 := by norm_num
  have hq : quadraticChar (ZMod 41) (-1) = 1 :=
    (quadraticChar_one_iff_isSquare hneg).2 ⟨9, by
      change ((-1 : ℤ) : ZMod 41) = ((81 : ℤ) : ZMod 41)
      rw [ZMod.intCast_eq_intCast_iff']
      norm_num⟩
  rw [hq, map_one]

theorem deningerQ8FortyOneQuadraticGaussSum_sq_eq_fortyOne :
    gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar ^ 2 = 41 := by
  have h := gaussSum_sq deningerQ8FortyOneQuadraticChar_ne_one
    ((quadraticChar_isQuadratic (ZMod 41)).comp (Int.castRingHom ℂ))
    (ZMod.isPrimitive_stdAddChar 41)
  rw [deningerQ8FortyOneQuadraticChar_neg_one_eq_one, one_mul] at h
  simpa using h

set_option maxHeartbeats 2000000 in
theorem deningerQ8FortyOneQuadraticGaussSum_re_explicit :
    (gaussSum deningerQ8FortyOneQuadraticChar ZMod.stdAddChar).re =
      2 * (
        Real.cos (2 * Real.pi * 1 / 41) +
        Real.cos (2 * Real.pi * 2 / 41) -
        Real.cos (2 * Real.pi * 3 / 41) +
        Real.cos (2 * Real.pi * 4 / 41) +
        Real.cos (2 * Real.pi * 5 / 41) -
        Real.cos (2 * Real.pi * 6 / 41) -
        Real.cos (2 * Real.pi * 7 / 41) +
        Real.cos (2 * Real.pi * 8 / 41) +
        Real.cos (2 * Real.pi * 9 / 41) +
        Real.cos (2 * Real.pi * 10 / 41) -
        Real.cos (2 * Real.pi * 11 / 41) -
        Real.cos (2 * Real.pi * 12 / 41) -
        Real.cos (2 * Real.pi * 13 / 41) -
        Real.cos (2 * Real.pi * 14 / 41) -
        Real.cos (2 * Real.pi * 15 / 41) +
        Real.cos (2 * Real.pi * 16 / 41) -
        Real.cos (2 * Real.pi * 17 / 41) +
        Real.cos (2 * Real.pi * 18 / 41) -
        Real.cos (2 * Real.pi * 19 / 41) +
        Real.cos (2 * Real.pi * 20 / 41)) := by
  rw [gaussSum]
  change (∑ i : Fin 41,
    (deningerQ8FortyOneQuadraticChar i * ZMod.stdAddChar i).re) = _
  norm_num [deningerQ8FortyOneQuadraticChar, MulChar.ringHomComp_apply,
    quadraticChar, quadraticCharFun, ZMod.stdAddChar_coe, Fin.sum_univ_succ,
    Complex.exp_re]

end

end RHTower
