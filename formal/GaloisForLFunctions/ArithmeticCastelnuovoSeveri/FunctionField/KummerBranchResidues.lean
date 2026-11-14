import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerBranchUnit
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPlaceResidues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ResidueConstantCharacters

/-!
# Constant residues of the quotient radical

Above a nonzero rational point, the quotient radical is a valuation
unit whose residue satisfies `u^δ=c a`. If `c a` is a `δ`-th power in
the constants, the split roots of unity force this residue to be
constant. The equation takes place in the actual residue field of
the Dedekind normalization.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- The quotient radical, as a unit of the adic valuation ring above a nonzero point. -/
def kummerBranchResidueUnit (a : SquareConstantField p s) (ha : a ≠ 0)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    (w.valuation (SquareKummerField p s c b R)).valuationSubring :=
  ⟨kummerBranchUnitRoot c b R (p ^ (s + 1)),
    (squareKummerBranchUnitRoot_valuation_one p s c b R a ha w).le⟩

/-- The quotient radical has constant residue whenever `c a` has a gcd-th root in the constants. -/
theorem kummerBranchResidueUnit_constant
    (a : SquareConstantField p s) (ha : a ≠ 0)
    (β : SquareConstantField p s) (hβ : β ≠ 0)
    (hpow : β ^ Nat.gcd (p ^ (s + 1) + 1) R = (c : SquareConstantField p s) * a)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    ∃ t : SquareConstantField p s,
      IsLocalRing.residue _ (kummerPlaceConstantHom p s c b R w t) =
        IsLocalRing.residue _ (kummerBranchResidueUnit p s c b R a ha w) := by
  let W := (w.valuation (SquareKummerField p s c b R)).valuationSubring
  let φ := (IsLocalRing.residue W).comp (kummerPlaceConstantHom p s c b R w)
  let u := kummerBranchResidueUnit p s c b R a ha w
  have hu : u ^ Nat.gcd (p ^ (s + 1) + 1) R =
      kummerPlaceConstantHom p s c b R w c * kummerPlacePolynomialHom p s c b R w X := by
    apply Subtype.ext
    change kummerBranchUnitRoot c b R (p ^ (s + 1)) ^ _ =
      (kummerPlaceConstantHom p s c b R w c : SquareKummerField p s c b R) *
        (kummerPlacePolynomialHom p s c b R w X : SquareKummerField p s c b R)
    rw [kummerBranchUnitRoot_pow, kummerPlaceConstantHom_coe]
    rfl
  have hres := congrArg (IsLocalRing.residue W) hu
  rw [map_pow, map_mul, kummerPlaceResidue_coordinate p s c b R w a] at hres
  have hp : (IsLocalRing.residue W u) ^ Nat.gcd (p ^ (s + 1) + 1) R = φ β ^ Nat.gcd (p ^ (s + 1) + 1) R := by
    rw [← map_pow φ, hpow, map_mul]
    exact hres
  exact exists_constant_of_power_eq φ (Nat.succ_pos _) (Nat.gcd_dvd_left _ _)
    (squareConstantField_primitiveRoots p s) hβ hp

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
