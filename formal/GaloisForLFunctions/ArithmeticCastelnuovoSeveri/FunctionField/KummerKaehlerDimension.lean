import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerNormalization
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial


/-!
# Differentials of a separable Kummer function field

Localization identifies rational differentials with the ordinary derivative
coordinate. Separability transports this coordinate to the radical field,
whose differential module is one-dimensional with nonzero coordinate differential.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped TensorProduct nonZeroDivisors

/-- Differentials of a rational function field form a one-dimensional vector space. -/
def fractionRingPolynomialDifferentialEquiv (K : Type*) [Field K] :
    KaehlerDifferential K (FractionRing K[X]) ≃ₗ[FractionRing K[X]] FractionRing K[X] := by
  let F := FractionRing K[X]
  letI : Algebra.FormallyEtale K[X] F :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := F) K[X]⁰
  let e₀ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K K[X] F
  let e₁ := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl F F) (KaehlerDifferential.polynomialEquiv K)
  let e₂ := TensorProduct.AlgebraTensorModule.rid K[X] F F
  exact e₀.symm.trans (e₁.trans e₂)

/-- The rational-field differential coordinate is ordinary polynomial differentiation. -/
theorem fractionRingPolynomialDifferentialEquiv_D (K : Type*) [Field K] (f : K[X]) :
    fractionRingPolynomialDifferentialEquiv K
      (KaehlerDifferential.D K (FractionRing K[X]) (algebraMap K[X] (FractionRing K[X]) f)) =
      algebraMap K[X] (FractionRing K[X]) f.derivative := by
  dsimp only [fractionRingPolynomialDifferentialEquiv]
  rw [LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, KaehlerDifferential.polynomialEquiv_D,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]

/-- The one-dimensional differential module of the actual separable Kummer function field. -/
def squareKummerDifferentialEquiv
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)
      ≃ₗ[SquareKummerField p s c b R] SquareKummerField p s c b R := by
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let L := SquareKummerField p s c b R
  letI := squareKummer_isGalois p s c b R
  letI : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  let e₀ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F L
  let e₁ := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl L L) (fractionRingPolynomialDifferentialEquiv K)
  let e₂ := TensorProduct.AlgebraTensorModule.rid F L L
  exact e₀.symm.trans (e₁.trans e₂)

/-- Polynomial differentials retain their ordinary derivative in the Kummer differential coordinate. -/
theorem squareKummerDifferentialEquiv_D_polynomial
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (f : (SquareConstantField p s)[X]) :
    squareKummerDifferentialEquiv p s c b R
      (KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R)
        (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) f)) =
      algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) f.derivative := by
  dsimp only [squareKummerDifferentialEquiv]
  rw [IsScalarTower.algebraMap_apply (SquareConstantField p s)[X]
      (FractionRing (SquareConstantField p s)[X]) (SquareKummerField p s c b R),
    LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, fractionRingPolynomialDifferentialEquiv_D,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one,
    ← IsScalarTower.algebraMap_apply]

/-- The polynomial coordinate has nonzero differential in the actual Kummer field. -/
theorem squareKummer_coordinate_differential_ne_zero
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    KaehlerDifferential.D (SquareConstantField p s) (SquareKummerField p s c b R)
      (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X) ≠ 0 := by
  intro h
  have h' := congrArg (squareKummerDifferentialEquiv p s c b R) h
  rw [squareKummerDifferentialEquiv_D_polynomial, derivative_X, map_one, map_zero] at h'
  exact one_ne_zero h'

/-- The Kummer field has precisely one differential dimension over its constants. -/
theorem squareKummer_kaehler_finrank
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    Module.finrank (SquareKummerField p s c b R)
      (KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) = 1 := by
  rw [(squareKummerDifferentialEquiv p s c b R).finrank_eq, Module.finrank_self]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
