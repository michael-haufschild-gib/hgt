import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierExactness
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationDifferentialTransport

/-!
# Cartier commutes with function-field pullback

A field homomorphism carries a Frobenius parameter expansion to the
same expansion in the image parameter. The coordinate-independent
extraction formula then proves naturality on actual Kähler modules,
including inseparable maps whose differential pullback vanishes.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open GaloisForLFunctions.HTGeometry
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
    (c₁ c₂ : (SquareConstantField p s)ˣ) (b₁ R₁ b₂ R₂ : ℕ)

/-- Cartier extraction commutes with every constant-field homomorphism between the actual Kummer models. -/
theorem squareKummerCoordinateCartier_map
    (f : SquareKummerField p s c₁ b₁ R₁ →ₐ[SquareConstantField p s]
      SquareKummerField p s c₂ b₂ R₂)
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c₁ b₁ R₁)) :
    algHomKaehlerMap f (squareKummerCoordinateCartier p s c₁ b₁ R₁ ω) =
      squareKummerCoordinateCartier p s c₂ b₂ R₂ (algHomKaehlerMap f ω) := by
  classical
  let K := SquareConstantField p s
  let L₁ := SquareKummerField p s c₁ b₁ R₁
  let y := algebraMap K[X] L₁ X
  let j : Fin p := ⟨p - 1, Nat.sub_lt (Fact.out : p.Prime).pos Nat.zero_lt_one⟩
  obtain ⟨a, ha⟩ := squareKummer_differential_frobenius_expansion p s c₁ b₁ R₁ ω
  rw [ha, squareKummerCoordinateCartier_parameter_expansion p s c₁ b₁ R₁ y a j rfl,
    algHomKaehlerMap_smul, algHomKaehlerMap_D, map_sum]
  simp only [algHomKaehlerMap_smul, algHomKaehlerMap_D, map_pow]
  rw [squareKummerCoordinateCartier_parameter_expansion p s c₂ b₂ R₂ (f y)
    (fun i => f (a i)) j rfl]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
