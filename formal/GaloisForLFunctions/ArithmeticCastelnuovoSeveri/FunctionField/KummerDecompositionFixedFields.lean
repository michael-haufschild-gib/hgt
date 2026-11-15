import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInertiaFixedFields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalIntermediateFields


/-!
# Rational decomposition fixed fields

The decomposition group contains inertia, so its fixed field lies in
the rational inertia fixed field at a branch place. Lüroth's theorem
then makes the decomposition fixed field rational over constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Actual inertia, embedded in the full Galois group, is contained in actual decomposition. -/
theorem squareKummer_inertia_le_decomposition
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R)) :
    squareKummerInertiaSubgroup p s c b R w ≤
      (w.valuation (SquareKummerField p s c b R)).valuationSubring.decompositionSubgroup
        (FractionRing (SquareConstantField p s)[X]) := by
  rintro σ ⟨τ, _, rfl⟩
  exact τ.property

/-- Lüroth's theorem makes the decomposition fixed field rational at every branch of multiplicity `R`. -/
def squareKummer_branch_decomposition_rationalEquiv
    (a : SquareConstantField p s) (hm : (kummerBranch c b R).rootMultiplicity a = R)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    FractionRing (SquareConstantField p s)[X] ≃ₐ[SquareConstantField p s]
      IntermediateField.fixedField
        ((w.valuation (SquareKummerField p s c b R)).valuationSubring.decompositionSubgroup
          (FractionRing (SquareConstantField p s)[X])) := by
  apply kummerIntermediateField_rationalEquiv c b R (p ^ (s + 1))
  rw [← squareKummer_branch_inertia_fixedField p s c b R a hm w]
  exact IntermediateField.fixedField_le (squareKummer_inertia_le_decomposition p s c b R w)

/-- Nonzero auxiliary-field branch places have rational decomposition fixed fields for every nonzero coefficient. -/
def squareKummer_primePowerBranch_decomposition_rationalEquiv (d : ℕ)
    (a : (KummerAuxiliaryField p s (d + 1))ˣ)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R))
    [w.asIdeal.LiesOver (Ideal.span
      {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)})] :
    FractionRing (SquareConstantField p s)[X] ≃ₐ[SquareConstantField p s]
      IntermediateField.fixedField
        ((w.valuation (SquareKummerField p s c (p ^ (d + 1) - 2) R)).valuationSubring.decompositionSubgroup
          (FractionRing (SquareConstantField p s)[X])) :=
  squareKummer_branch_decomposition_rationalEquiv p s c (p ^ (d + 1) - 2) R _
    (kummerBranch_primePower_rootMultiplicity p s c R d a) w

/-- Every nonzero auxiliary coordinate supports an actual place with rational decomposition fixed field. -/
theorem squareKummer_exists_primePowerBranch_decomposition_rational (d : ℕ)
    (a : (KummerAuxiliaryField p s (d + 1))ˣ) :
    ∃ w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R),
      w.asIdeal.LiesOver (Ideal.span
        {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}) ∧
      Nonempty (FractionRing (SquareConstantField p s)[X] ≃ₐ[SquareConstantField p s]
        IntermediateField.fixedField
          ((w.valuation (SquareKummerField p s c (p ^ (d + 1) - 2) R)).valuationSubring.decompositionSubgroup
            (FractionRing (SquareConstantField p s)[X]))) := by
  obtain ⟨w, hw⟩ := squareKummer_exists_primeAbove p s c (p ^ (d + 1) - 2) R
    (GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C
      (((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s))))
  change w.asIdeal.LiesOver (Ideal.span
    {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}) at hw
  letI := hw
  exact ⟨w, hw, ⟨squareKummer_primePowerBranch_decomposition_rationalEquiv p s c R d a w⟩⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
