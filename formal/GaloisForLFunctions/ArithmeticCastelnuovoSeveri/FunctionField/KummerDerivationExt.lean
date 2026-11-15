import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerSeparatingPowerBasis

/-!
# Derivations determined by the separating coordinate

Frobenius coefficients have zero derivative. The coordinate power
expansion therefore determines every derivation from its value on the
original rational coordinate, for any target module.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Two derivations of the actual Kummer field agree if they agree on its rational coordinate. -/
theorem squareKummer_derivation_ext
    {M : Type*} [AddCommGroup M] [Module (SquareConstantField p s) M]
    [Module (SquareKummerField p s c b R) M]
    [IsScalarTower (SquareConstantField p s) (SquareKummerField p s c b R) M]
    (D₁ D₂ : Derivation (SquareConstantField p s) (SquareKummerField p s c b R) M)
    (h : D₁ (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X) =
      D₂ (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X)) : D₁ = D₂ := by
  apply Derivation.ext
  intro x
  obtain ⟨a, ha⟩ := squareKummer_coordinate_power_expansion p s c b R x
  rw [ha, derivation_uniformizer_power_expansion p D₁,
    derivation_uniformizer_power_expansion p D₂, h]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
