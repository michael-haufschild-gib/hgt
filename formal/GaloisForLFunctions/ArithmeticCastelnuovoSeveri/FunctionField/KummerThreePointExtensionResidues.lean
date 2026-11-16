import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointConstantExtensions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialNormalizationResidues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.InertiaUnitCharacters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ResidueConstantCharacters

/-!
# Radical residues after extension of constants

Above a nonzero value of the three-point equation, the radical is a
valuation unit. If that value has a radical root in the new constants,
its residue is constant because every covering root of unity remains
in the constant field. The covering degree is unchanged throughout.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
    (E : Type*) [Field E] [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
    (c : Eˣ) (a : ℕ)
local notation "N" => primePowerKummerCyclicDegree p d n - 1 + 1
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a
local notation "z" => AdjoinRoot.root (kummerBranchFieldPolynomial c 0 a
  (primePowerKummerCyclicDegree p d n - 1))

/-- The radical is a valuation unit above every nonzero defining value over the extended constants. -/
theorem primePowerThreePointExtension_root_valuation_one
    (x : E) (hx : (kummerBranch c 0 a).eval x ≠ 0) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C x})] : w.valuation L z = 1 := by
  have hp : w.valuation L z ^ N = 1 := by
    rw [← map_pow, kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply]
    exact heightOne_polynomial_valuation_one_of_eval_ne_zero («L» := L) w x _ hx
  have h := valuation_balanced_radical (w.valuation L) («z» := z) (t := 1)
    («N» := N) (m := 0) (g := N) (Nat.succ_pos _) (dvd_refl _) (dvd_zero _)
    (by rw [map_one]; exact one_ne_zero) (by simpa only [pow_zero] using hp)
  simpa only [Nat.div_self (Nat.succ_pos _), Nat.zero_div, pow_one, pow_zero, div_one] using h

/-- The canonical radical represented in the actual finite-place valuation ring. -/
def primePowerThreePointExtensionPlaceRadical (w : HeightOneSpectrum B) :
    (w.valuation L).valuationSubring :=
  ⟨z, by
    change w.valuation L (algebraMap B L
      (primePowerThreePointExtensionIntegralRoot p d n E c a)) ≤ 1
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact w.intValuation_le_one _⟩

/-- A nonzero radical root in the extended constants makes the radical residue constant at every prime of that fiber. -/
theorem primePowerThreePointExtension_radical_residue_constant
    (x β : E) (hβ : β ≠ 0) (hpow : β ^ N = (kummerBranch c 0 a).eval x)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    ∃ t : E, IsLocalRing.residue _ (heightOnePolynomialConstantHom (K := E) («L» := L) w t) =
      IsLocalRing.residue _ (primePowerThreePointExtensionPlaceRadical p d n E c a w) := by
  let W := (w.valuation L).valuationSubring
  let φ := (IsLocalRing.residue W).comp (heightOnePolynomialConstantHom (K := E) («L» := L) w)
  let u := primePowerThreePointExtensionPlaceRadical p d n E c a w
  have hu : u ^ N = heightOnePolynomialHom (K := E) («L» := L) w (kummerBranch c 0 a) := by
    apply Subtype.ext
    exact (kummerBranchField_root_pow c 0 a (primePowerKummerCyclicDegree p d n - 1)).trans
      (IsScalarTower.algebraMap_apply E[X] (FractionRing E[X]) L _).symm
  have hres := congrArg (IsLocalRing.residue W) hu
  rw [map_pow, heightOnePolynomialResidue_eval (K := E) («L» := L) w x] at hres
  have hp : IsLocalRing.residue W u ^ N = φ β ^ N := by
    rw [← map_pow φ, hpow]
    exact hres
  exact exists_constant_of_power_eq φ (Nat.succ_pos _) (dvd_refl _)
    (primePowerThreePointExtension_primitiveRoots p d n E) hβ hp

omit [Fact p.Prime] [Algebra (SquareConstantField p (kummerSquareIndex d n)) E] in
/-- A prime quotient exhausted by constants supplies a literal radical root in the extended field. -/
theorem primePowerThreePointExtension_rationalPrime_root (x : E)
    (P : Ideal B) [P.IsPrime] [P.LiesOver (Ideal.span {X - C x})]
    (hsurj : Function.Surjective (algebraMap E (B ⧸ P))) :
    ∃ β : E, β ^ N = (kummerBranch c 0 a).eval x := by
  obtain ⟨β, hβ⟩ := hsurj (Ideal.Quotient.mk P (primePowerThreePointExtensionIntegralRoot p d n E c a))
  refine ⟨β, (algebraMap E (B ⧸ P)).injective ?_⟩
  rw [map_pow, hβ, ← map_pow, primePowerThreePointExtensionIntegralRoot_pow,
    linearPrime_quotient_polynomial x P]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
