import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldNormKernel
import Mathlib.NumberTheory.MulChar.Basic

/-!
# Multiplicative characters descending through finite-field norms

The norm-one subgroup consists of powers of the base-field unit order.
A character killed by that order is trivial on the norm kernel, hence
descends uniquely through the surjective norm.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {K L R : Type*} [Field K] [Field L] [CommMonoidWithZero R]
    [Fintype K] [Finite L] [Algebra K L]

/-- Pullback by the finite-field norm gives a multiplicative character. -/
def finiteFieldNormCharacter (χ : MulChar K R) : MulChar L R :=
  { χ.toMonoidHom.comp (Algebra.norm K) with
    map_nonunit' := by
      intro x hx
      have hx0 : x = 0 := by
        by_contra h
        exact hx (isUnit_iff_ne_zero.mpr h)
      subst x
      change χ (Algebra.norm K (0 : L)) = 0
      rw [Algebra.norm_zero, χ.map_zero] }

/-- Norm pullback reflects equality of multiplicative characters. -/
theorem finiteFieldNormCharacter_injective :
    Function.Injective (finiteFieldNormCharacter (K := K) (L := L) (R := R)) := by
  intro χ ψ h
  apply MulChar.ext'
  intro a
  obtain ⟨x, rfl⟩ := FiniteField.norm_surjective K L a
  exact DFunLike.congr_fun h x

/-- Norm pullback preserves the trivial multiplicative character. -/
theorem finiteFieldNormCharacter_one :
    finiteFieldNormCharacter (K := K) (L := L) (1 : MulChar K R) = 1 := by
  apply MulChar.ext
  intro u
  let v := Units.map (Algebra.norm K (S := L)) u
  change (1 : MulChar K R) (v : K) = (1 : MulChar L R) (u : L)
  rw [MulChar.one_apply_coe, MulChar.one_apply_coe]

/-- Norm pullback preserves every character power. -/
theorem finiteFieldNormCharacter_pow (χ : MulChar K R) (a : ℕ) :
    finiteFieldNormCharacter (L := L) (χ ^ a) = (finiteFieldNormCharacter (L := L) χ) ^ a := by
  apply MulChar.ext
  intro u
  let v := Units.map (Algebra.norm K (S := L)) u
  change (χ ^ a) (v : K) = (finiteFieldNormCharacter (L := L) χ ^ a) (u : L)
  rw [MulChar.pow_apply_coe, MulChar.pow_apply_coe]
  rfl

private theorem norm_character_kernel (χ : MulChar L R)
    (hχ : χ ^ (Fintype.card K - 1) = 1) :
    (Units.map (Algebra.norm K (S := L))).ker ≤ χ.toUnitHom.ker := by
  rw [finiteField_norm_kernel_eq_power_range]
  rintro u ⟨v, rfl⟩
  change χ.toUnitHom (v ^ (Fintype.card K - 1)) = 1
  rw [map_pow]
  apply Units.ext
  change (χ (v : L)) ^ (Fintype.card K - 1) = 1
  rw [← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]

/-- Every character killed by the multiplicative order of the base field descends uniquely through the actual norm. -/
theorem finiteField_existsUnique_norm_character (χ : MulChar L R)
    (hχ : χ ^ (Fintype.card K - 1) = 1) :
    ∃! ψ : MulChar K R, finiteFieldNormCharacter (L := L) ψ = χ := by
  let ν := Units.map (Algebra.norm K (S := L))
  let E := MonoidHom.liftOfSurjective ν (FiniteField.unitsMap_norm_surjective K L)
    ⟨χ.toUnitHom, norm_character_kernel χ hχ⟩
  have hE : E.comp ν = χ.toUnitHom := MonoidHom.liftOfRightInverse_comp ..
  have hdesc : finiteFieldNormCharacter (L := L) (MulChar.ofUnitHom E) = χ := by
    apply MulChar.ext
    intro u
    change MulChar.ofUnitHom E (ν u : K) = χ (u : L)
    rw [MulChar.ofUnitHom_coe]
    exact congrArg Units.val (DFunLike.congr_fun hE u)
  refine ⟨MulChar.ofUnitHom E, hdesc, ?_⟩
  intro ψ hψ
  exact finiteFieldNormCharacter_injective (hψ.trans hdesc.symm)

/-- The image of norm pullback consists exactly of characters killed by the base-field multiplicative order. -/
theorem finiteField_norm_character_iff (χ : MulChar L R) :
    (∃ ψ : MulChar K R, finiteFieldNormCharacter (L := L) ψ = χ) ↔
      χ ^ (Fintype.card K - 1) = 1 := by
  constructor
  · rintro ⟨ψ, rfl⟩
    apply MulChar.ext
    intro u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    let a : K := Algebra.norm K (u : L)
    have ha : a ≠ 0 := (Units.map (Algebra.norm K (S := L)) u).ne_zero
    have hcard : Fintype.card K - 1 + 1 = Fintype.card K :=
      Nat.sub_add_cancel Fintype.card_pos
    have hp := FiniteField.pow_card a
    rw [← hcard, pow_succ] at hp
    have haorder : a ^ (Fintype.card K - 1) = 1 :=
      mul_right_cancel₀ ha (hp.trans (one_mul a).symm)
    change ψ a ^ (Fintype.card K - 1) = 1
    rw [← map_pow, haorder, map_one]
  · intro hχ
    exact (finiteField_existsUnique_norm_character χ hχ).exists

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
