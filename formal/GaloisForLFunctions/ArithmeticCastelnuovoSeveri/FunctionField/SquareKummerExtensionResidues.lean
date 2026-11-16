import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerConstantExtensions
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialNormalizationResidues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.InertiaUnitCharacters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ResidueConstantCharacters

/-!
# Radical residues over extended square constants

Above a nonzero value of the Kummer equation, the radical is a
valuation unit. If that value has a radical root in the new constants,
its residue is constant because every covering root of unity remains
in the constant field. The covering degree is unchanged throughout.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
    (E : Type*) [Field E] [Algebra (SquareConstantField p s) E]
    (c : Eˣ) (b R : ℕ)
local notation "N" => p ^ (s + 1) + 1
local notation "L" => SquareKummerExtensionField p s E c b R
local notation "B" => SquareKummerExtensionNormalization p s E c b R
local notation "z" => AdjoinRoot.root (kummerBranchFieldPolynomial c b R
  (p ^ (s + 1)))

/-- The radical is a valuation unit above every nonzero defining value over the extended constants. -/
theorem squareKummerExtension_root_valuation_one
    (x : E) (hx : (kummerBranch c b R).eval x ≠ 0) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C x})] : w.valuation L z = 1 := by
  have hp : w.valuation L z ^ N = 1 := by
    rw [← map_pow, kummerBranchField_root_pow, ← IsScalarTower.algebraMap_apply]
    exact heightOne_polynomial_valuation_one_of_eval_ne_zero («L» := L) w x _ hx
  have h := valuation_balanced_radical (w.valuation L) («z» := z) (t := 1)
    («N» := N) (m := 0) (g := N) (Nat.succ_pos _) (dvd_refl _) (dvd_zero _)
    (by rw [map_one]; exact one_ne_zero) (by simpa only [pow_zero] using hp)
  simpa only [Nat.div_self (Nat.succ_pos _), Nat.zero_div, pow_one, pow_zero, div_one] using h

/-- The canonical radical represented in the actual finite-place valuation ring. -/
def squareKummerExtensionPlaceRadical (w : HeightOneSpectrum B) :
    (w.valuation L).valuationSubring :=
  ⟨z, by
    change w.valuation L (algebraMap B L
      (squareKummerExtensionIntegralRoot p s E c b R)) ≤ 1
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact w.intValuation_le_one _⟩

/-- A nonzero radical root in the extended constants makes the radical residue constant at every prime of that fiber. -/
theorem squareKummerExtension_radical_residue_constant
    (x β : E) (hβ : β ≠ 0) (hpow : β ^ N = (kummerBranch c b R).eval x)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    ∃ t : E, IsLocalRing.residue _ (heightOnePolynomialConstantHom (K := E) («L» := L) w t) =
      IsLocalRing.residue _ (squareKummerExtensionPlaceRadical p s E c b R w) := by
  let W := (w.valuation L).valuationSubring
  let φ := (IsLocalRing.residue W).comp (heightOnePolynomialConstantHom (K := E) («L» := L) w)
  let u := squareKummerExtensionPlaceRadical p s E c b R w
  have hu : u ^ N = heightOnePolynomialHom (K := E) («L» := L) w (kummerBranch c b R) := by
    apply Subtype.ext
    exact (kummerBranchField_root_pow c b R (p ^ (s + 1))).trans
      (IsScalarTower.algebraMap_apply E[X] (FractionRing E[X]) L _).symm
  have hres := congrArg (IsLocalRing.residue W) hu
  rw [map_pow, heightOnePolynomialResidue_eval (K := E) («L» := L) w x] at hres
  have hp : IsLocalRing.residue W u ^ N = φ β ^ N := by
    rw [← map_pow φ, hpow]
    exact hres
  exact exists_constant_of_power_eq φ (Nat.succ_pos _) (dvd_refl _)
    (squareKummerExtension_primitiveRoots p s E) hβ hp

/-- A soluble nonzero fiber supplies a literal constant root equal to the radical residue. -/
theorem squareKummerExtension_exists_radical_residue
    (x β : E) (hβ : β ≠ 0) (hpow : β ^ N = (kummerBranch c b R).eval x)
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C x})] :
    ∃ γ : E, γ ^ N = (kummerBranch c b R).eval x ∧
      w.valuation L (z - algebraMap E L γ) < 1 := by
  let W := (w.valuation L).valuationSubring
  let f := heightOnePolynomialConstantHom (K := E) («L» := L) w
  let φ := (IsLocalRing.residue W).comp f
  let u := squareKummerExtensionPlaceRadical p s E c b R w
  obtain ⟨γ, hγ⟩ := squareKummerExtension_radical_residue_constant p s E c b R x β hβ hpow w
  have hu : u ^ N = heightOnePolynomialHom (K := E) («L» := L) w (kummerBranch c b R) := by
    apply Subtype.ext
    exact (kummerBranchField_root_pow c b R (p ^ (s + 1))).trans
      (IsScalarTower.algebraMap_apply E[X] (FractionRing E[X]) L _).symm
  refine ⟨γ, φ.injective ?_, ?_⟩
  · calc
      φ (γ ^ N) = (IsLocalRing.residue W u) ^ N := by
        rw [map_pow]
        exact congrArg (fun t => t ^ N) hγ
      _ = φ ((kummerBranch c b R).eval x) := by
        rw [← map_pow, hu, heightOnePolynomialResidue_eval (K := E) («L» := L) w x]
        rfl
  · have hz : IsLocalRing.residue W (u - f γ) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hγ.symm
    have hv := (w.valuation L).mem_maximalIdeal_iff.mp
      ((IsLocalRing.residue_eq_zero_iff W).mp hz)
    change w.valuation L (z - (f γ : L)) < 1 at hv
    rw [heightOnePolynomialConstantHom_coe] at hv
    exact hv

omit [Fact p.Prime] [Algebra (SquareConstantField p s) E] in
/-- A prime quotient exhausted by constants supplies a literal radical root in the extended field. -/
theorem squareKummerExtension_rationalPrime_root (x : E)
    (P : Ideal B) [P.IsPrime] [P.LiesOver (Ideal.span {X - C x})]
    (hsurj : Function.Surjective (algebraMap E (B ⧸ P))) :
    ∃ β : E, β ^ N = (kummerBranch c b R).eval x := by
  obtain ⟨β, hβ⟩ := hsurj (Ideal.Quotient.mk P (squareKummerExtensionIntegralRoot p s E c b R))
  refine ⟨β, (algebraMap E (B ⧸ P)).injective ?_⟩
  rw [map_pow, hβ, ← map_pow, squareKummerExtensionIntegralRoot_pow,
    linearPrime_quotient_polynomial x P]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
