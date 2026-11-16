import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionResidues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerBranchUnit

/-!
# The branch unit over extended constants

At the point one the quotient radical has valuation one and its gcd-th
power is the coefficient times the coordinate. A gcd-th root of the
coefficient in the constants therefore makes its residue constant.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
    (E : Type*) [Field E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
    (c : Eˣ) (a : ℕ)
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "N" => M - 1 + 1
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a

/-- The balanced branch radical is a valuation unit at every prime above one. -/
theorem primePowerThreePointExtension_branchUnit_valuation_one
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C (1 : E)})] :
    w.valuation L (kummerBranchUnitRoot c 0 a (M - 1)) = 1 := by
  let δ := Nat.gcd N a
  have hδ : 0 < δ := Nat.gcd_pos_of_pos_left a (Nat.succ_pos _)
  have hp := congrArg (w.valuation L) (kummerBranchUnitRoot_pow c 0 a (M - 1))
  rw [map_pow, map_mul, heightOne_valuation_constant w _ (Units.ne_zero c),
    heightOne_polynomial_valuation_one_of_eval_ne_zero («L» := L) w 1 X
      (by simpa only [eval_X] using (one_ne_zero : (1 : E) ≠ 0)), one_mul] at hp
  have h := valuation_balanced_radical (w.valuation L)
    (z := kummerBranchUnitRoot c 0 a (M - 1)) (t := 1) («N» := δ) (m := 0)
    hδ (dvd_refl δ) (dvd_zero δ)
    (by rw [map_one]; exact one_ne_zero) (by simpa only [pow_zero] using hp)
  simpa only [Nat.div_self hδ, Nat.zero_div, pow_one, pow_zero, div_one] using h

/-- The balanced radical represented in the actual valuation ring above one. -/
def primePowerThreePointExtensionBranchUnit
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C (1 : E)})] :
    (w.valuation L).valuationSubring :=
  ⟨kummerBranchUnitRoot c 0 a (M - 1),
    (primePowerThreePointExtension_branchUnit_valuation_one p d n E c a w).le⟩

/-- A constant gcd-th root of the coefficient makes the balanced radical residue constant. -/
theorem primePowerThreePointExtension_branchUnit_residue_constant
    (β : E) (hβ : β ≠ 0) (hpow : β ^ Nat.gcd N a = (c : E))
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {X - C (1 : E)})] :
    ∃ t : E, IsLocalRing.residue _ (heightOnePolynomialConstantHom (K := E) («L» := L) w t) =
      IsLocalRing.residue _ (primePowerThreePointExtensionBranchUnit p d n E c a w) := by
  let W := (w.valuation L).valuationSubring
  let f := heightOnePolynomialConstantHom (K := E) («L» := L) w
  let φ := (IsLocalRing.residue W).comp f
  let u := primePowerThreePointExtensionBranchUnit p d n E c a w
  have hu : u ^ Nat.gcd N a = f c * heightOnePolynomialHom (K := E) («L» := L) w X := by
    apply Subtype.ext
    change kummerBranchUnitRoot c 0 a (M - 1) ^ _ =
      (f c : L) * (heightOnePolynomialHom (K := E) («L» := L) w X : L)
    rw [kummerBranchUnitRoot_pow, heightOnePolynomialConstantHom_coe]
    rfl
  have hres := congrArg (IsLocalRing.residue W) hu
  rw [map_pow, map_mul, heightOnePolynomialResidue_coordinate (K := E) («L» := L) w 1,
    map_one, map_one, mul_one] at hres
  have hp : IsLocalRing.residue W u ^ Nat.gcd N a = φ β ^ Nat.gcd N a := by
    rw [← map_pow φ, hpow]
    exact hres
  exact exists_constant_of_power_eq φ (Nat.succ_pos _) (Nat.gcd_dvd_left _ _)
    (primePowerThreePointExtension_primitiveRoots p d n E) hβ hp

omit [Fact p.Prime] [Algebra (SquareConstantField p (kummerSquareIndex d n)) E] in
/-- Inverse-power coefficients always have the required gcd-th residue root. -/
theorem primePowerThreePointExtension_inversePower_residue_root (η : Eˣ) :
    ∃ β : E, β ≠ 0 ∧ β ^ Nat.gcd N a = (((η⁻¹) ^ a : Eˣ) : E) := by
  refine ⟨((η⁻¹ : Eˣ) : E) ^ (a / Nat.gcd N a),
    pow_ne_zero _ (Units.ne_zero _), ?_⟩
  change (((η⁻¹ : Eˣ) : E) ^ (a / Nat.gcd N a)) ^ Nat.gcd N a =
    ((η⁻¹ : Eˣ) : E) ^ a
  rw [← pow_mul, Nat.div_mul_cancel (Nat.gcd_dvd_right N a)]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
