import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalSubcover
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerExactRamification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerFixedFields

/-!
# Rational inertia fixed fields

The actual inertia subgroup at every finite prime fixes the radical
power dictated by its exact ramification index. At a branch of
multiplicity `R`, this is the quotient-radical subfield, explicitly
rational over the constants and of degree `gcd(N,R)` over the base.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- The actual inertia subgroup embedded in the full relative Galois group. -/
def squareKummerInertiaSubgroup
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R)) :
    Subgroup (SquareKummerField p s c b R ≃ₐ[FractionRing (SquareConstantField p s)[X]]
      SquareKummerField p s c b R) :=
  ((w.valuation (SquareKummerField p s c b R)).valuationSubring.inertiaSubgroup
    (FractionRing (SquareConstantField p s)[X])).map
      ((w.valuation (SquareKummerField p s c b R)).valuationSubring.decompositionSubgroup
        (FractionRing (SquareConstantField p s)[X])).subtype

/-- Embedding inertia into the full Galois group preserves its ramification cardinality. -/
theorem squareKummerInertiaSubgroup_card
    (π : (SquareConstantField p s)[X]) (hπ : Irreducible π)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {π})] :
    Nat.card (squareKummerInertiaSubgroup p s c b R w) =
      (Ideal.span {π}).ramificationIdx' w.asIdeal := by
  let W := (w.valuation (SquareKummerField p s c b R)).valuationSubring
  let F := FractionRing (SquareConstantField p s)[X]
  let e := (W.inertiaSubgroup F).equivMapOfInjective (W.decompositionSubgroup F).subtype
    Subtype.val_injective
  exact (Nat.card_congr e.toEquiv).symm.trans (squareKummer_inertia_card p s c b R π hπ w)

/-- Every finite inertia fixed field is the explicitly determined radical-power subfield. -/
theorem squareKummer_inertia_fixedField_eq_power
    (π : (SquareConstantField p s)[X]) (hπ : Irreducible π)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {π})] :
    IntermediateField.fixedField (squareKummerInertiaSubgroup p s c b R w) =
      kummerPowerSubfield c b R (p ^ (s + 1))
        ((p ^ (s + 1) + 1) / Nat.gcd (p ^ (s + 1) + 1) (multiplicity π (kummerBranch c b R))) := by
  rw [squareKummer_fixedField_eq_power, squareKummerInertiaSubgroup_card p s c b R π hπ w,
    squareKummer_finitePlace_ramification p s c b R π hπ w]

/-- At a point of multiplicity `R`, the inertia fixed field is the quotient-radical subcover. -/
theorem squareKummer_branch_inertia_fixedField
    (a : SquareConstantField p s) (hm : (kummerBranch c b R).rootMultiplicity a = R)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    IntermediateField.fixedField (squareKummerInertiaSubgroup p s c b R w) =
      kummerBranchUnitSubfield c b R (p ^ (s + 1)) := by
  rw [squareKummer_fixedField_eq_power,
    squareKummerInertiaSubgroup_card p s c b R (X - C a) (irreducible_X_sub_C a) w,
    squareKummer_rationalPlace_ramification p s c b R a w, hm, kummerBranchUnitSubfield_eq]

/-- The inertia fixed field at a branch of multiplicity `R` is explicitly rational over constants. -/
def squareKummer_branch_inertia_rationalEquiv
    (a : SquareConstantField p s) (hm : (kummerBranch c b R).rootMultiplicity a = R)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {X - C a})] :
    FractionRing (SquareConstantField p s)[X] ≃ₐ[SquareConstantField p s]
      IntermediateField.fixedField (squareKummerInertiaSubgroup p s c b R w) :=
  (kummerBranchUnitSubfield_rationalEquiv c b R (p ^ (s + 1))).trans
    ((IntermediateField.equivOfEq (squareKummer_branch_inertia_fixedField p s c b R a hm w).symm).restrictScalars
      (SquareConstantField p s))

/-- Rational inertia fixed fields at every nonzero prime-power branch, with multiplicity inputs discharged. -/
def squareKummer_primePowerBranch_inertia_rationalEquiv (d : ℕ)
    (a : (KummerAuxiliaryField p s (d + 1))ˣ)
    (w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R))
    [w.asIdeal.LiesOver (Ideal.span
      {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)})] :
    FractionRing (SquareConstantField p s)[X] ≃ₐ[SquareConstantField p s]
      IntermediateField.fixedField (squareKummerInertiaSubgroup p s c (p ^ (d + 1) - 2) R w) :=
  squareKummer_branch_inertia_rationalEquiv p s c (p ^ (d + 1) - 2) R _
    (kummerBranch_primePower_rootMultiplicity p s c R d a) w

/-- Every nonzero auxiliary-field point has an actual branch place with rational inertia fixed field. -/
theorem squareKummer_exists_primePowerBranch_inertia_rational (d : ℕ)
    (a : (KummerAuxiliaryField p s (d + 1))ˣ) :
    ∃ w : HeightOneSpectrum (SquareKummerNormalization p s c (p ^ (d + 1) - 2) R),
      w.asIdeal.LiesOver (Ideal.span
        {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}) ∧
      Nonempty (FractionRing (SquareConstantField p s)[X] ≃ₐ[SquareConstantField p s]
        IntermediateField.fixedField (squareKummerInertiaSubgroup p s c (p ^ (d + 1) - 2) R w)) := by
  obtain ⟨w, hw⟩ := squareKummer_exists_primeAbove p s c (p ^ (d + 1) - 2) R
    (GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C
      (((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s))))
  change w.asIdeal.LiesOver (Ideal.span
    {X - C ((a : KummerAuxiliaryField p s (d + 1)) : SquareConstantField p s)}) at hw
  letI := hw
  exact ⟨w, hw, ⟨squareKummer_primePowerBranch_inertia_rationalEquiv p s c R d a w⟩⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
