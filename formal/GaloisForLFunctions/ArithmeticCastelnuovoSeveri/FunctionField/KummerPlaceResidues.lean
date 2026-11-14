import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPlaceValuations

/-!
# Polynomial and constant residues at finite Kummer places

Polynomial functions land in every finite-place valuation ring. Above
`X-a`, the coordinate has residue equal to the constant `a`. These
canonical homomorphisms let the radical equation descend to the actual
residue field of the normalization.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))

/-- Polynomial functions land in the valuation ring of every finite place of the normalization. -/
def kummerPlacePolynomialHom : (SquareConstantField p s)[X] →+*
    (w.valuation (SquareKummerField p s c b R)).valuationSubring :=
  RingHom.codRestrict (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R))
    (w.valuation (SquareKummerField p s c b R)).valuationSubring.toSubring (fun f => by
      change w.valuation (SquareKummerField p s c b R)
        (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) f) ≤ 1
      rw [IsScalarTower.algebraMap_apply (SquareConstantField p s)[X]
        (SquareKummerNormalization p s c b R) (SquareKummerField p s c b R),
        HeightOneSpectrum.valuation_of_algebraMap]
      exact w.intValuation_le_one _)

/-- Constants in the adic valuation ring. -/
def kummerPlaceConstantHom : SquareConstantField p s →+*
    (w.valuation (SquareKummerField p s c b R)).valuationSubring :=
  (kummerPlacePolynomialHom p s c b R w).comp C

/-- The constant homomorphism is the canonical field embedding after taking underlying values. -/
theorem kummerPlaceConstantHom_coe (a : SquareConstantField p s) :
    (kummerPlaceConstantHom p s c b R w a : SquareKummerField p s c b R) =
      algebraMap (SquareConstantField p s) (SquareKummerField p s c b R) a := by
  exact (IsScalarTower.algebraMap_apply (SquareConstantField p s)
    (SquareConstantField p s)[X] (SquareKummerField p s c b R) a).symm

/-- Polynomial residues at a place above `X-a` send the coordinate to the constant `a`. -/
theorem kummerPlaceResidue_coordinate (a : SquareConstantField p s)
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    IsLocalRing.residue _ (kummerPlacePolynomialHom p s c b R w X) =
      IsLocalRing.residue _ (kummerPlaceConstantHom p s c b R w a) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (IsLocalRing.residue_eq_zero_iff _).mpr
  apply (w.valuation (SquareKummerField p s c b R)).mem_maximalIdeal_iff.mpr
  change w.valuation (SquareKummerField p s c b R)
    (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X -
      algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) (C a)) < 1
  rw [← map_sub, IsScalarTower.algebraMap_apply (SquareConstantField p s)[X]
    (SquareKummerNormalization p s c b R) (SquareKummerField p s c b R),
    HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact (Ideal.mem_of_liesOver w.asIdeal (Ideal.span {X - C a}) (X - C a)).mp
    (Ideal.subset_span (Set.mem_singleton _))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
