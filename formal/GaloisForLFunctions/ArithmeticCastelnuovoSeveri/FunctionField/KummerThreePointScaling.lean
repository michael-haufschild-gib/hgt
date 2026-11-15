import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointCyclic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralMonomials

/-!
# Explicit scaling in the three-point cyclic action

The three-point radical action sends `z` to `ζz`. Rational recovery of
the original coordinate then gives `y ↦ ζ^N y`, while the branch factor
is fixed. Reduced radical monomials therefore have their literal
radical character weights.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K] (c : Kˣ) (b R n : ℕ)
local notation "L" => KummerBranchField c b R n
local notation "T" => KummerThreePointField c b R n
local notation "F" => FractionRing K[X]

private theorem threePoint_index :
    (n + 1) * (b + 1) - 1 + 1 = (n + 1) * (b + 1) :=
  Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos b))

private def threePointScaling (ζ : K) (hζ : ζ ^ ((n + 1) * (b + 1)) = 1) : T ≃ₐ[F] T :=
  autAdjoinRootXPowSubC ((n + 1) * (b + 1) - 1 + 1)
    (algebraMap K[X] F (kummerBranch (c ^ (b + 1)) 0 (R * (b + 1))))
    (rootsOfUnity.mkOfPowEq (algebraMap K F ζ) (by
      rw [threePoint_index, ← map_pow, hζ, map_one]))

/-- Every full-degree root of unity acts on the original Kummer field through its three-point presentation. -/
def kummerThreePointScalingAut (ζ : K) (hζ : ζ ^ ((n + 1) * (b + 1)) = 1) : L ≃ₐ[K] L :=
  (kummerThreePointEquiv c b R n).symm.trans
    (((threePointScaling c b R n ζ hζ).restrictScalars K).trans (kummerThreePointEquiv c b R n))

/-- The transported three-point action multiplies the original radical by its chosen root of unity. -/
theorem kummerThreePointScalingAut_root (ζ : K) (hζ : ζ ^ ((n + 1) * (b + 1)) = 1) :
    kummerThreePointScalingAut c b R n ζ hζ
      (AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)) =
        algebraMap K L ζ * AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) := by
  let e := kummerThreePointEquiv c b R n
  let z := AdjoinRoot.root (kummerBranchFieldPolynomial (c ^ (b + 1)) 0
    (R * (b + 1)) ((n + 1) * (b + 1) - 1))
  have he : e z = AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) :=
    kummerThreePointHom_root c b R n
  have hz : threePointScaling c b R n ζ hζ z = algebraMap K T ζ * z := by
    change autAdjoinRootXPowSubC _ _ _ _ = _
    rw [autAdjoinRootXPowSubC_root, rootsOfUnity.coe_mkOfPowEq, Algebra.smul_def,
      ← IsScalarTower.algebraMap_apply K F T]
  change e (threePointScaling c b R n ζ hζ (e.symm _)) = _
  rw [← he, e.symm_apply_apply, hz, map_mul, e.commutes]

/-- The transported radical action fixes the three-point rational coordinate. -/
theorem kummerThreePointScalingAut_monomialCoordinate
    (ζ : K) (hζ : ζ ^ ((n + 1) * (b + 1)) = 1) :
    kummerThreePointScalingAut c b R n ζ hζ (kummerMonomialCoordinate c b R n) =
      kummerMonomialCoordinate c b R n := by
  let e := kummerThreePointEquiv c b R n
  let t := algebraMap K[X] T X
  have he : e t = kummerMonomialCoordinate c b R n := kummerThreePointHom_coordinate c b R n
  have ht : threePointScaling c b R n ζ hζ t = t := by
    dsimp only [t]
    rw [IsScalarTower.algebraMap_apply K[X] F T, AlgEquiv.commutes]
  change e (threePointScaling c b R n ζ hζ (e.symm _)) = _
  rw [← he, e.symm_apply_apply, ht]

/-- Rational recovery gives the original coordinate the covering-degree character. -/
theorem kummerThreePointScalingAut_coordinate
    (ζ : K) (hζ : ζ ^ ((n + 1) * (b + 1)) = 1) :
    kummerThreePointScalingAut c b R n ζ hζ (algebraMap K[X] L X) =
      (algebraMap K L ζ) ^ (n + 1) * algebraMap K[X] L X := by
  conv_lhs => rw [kummerBranchField_coordinate_recover]
  rw [map_div₀, map_pow, kummerThreePointScalingAut_root, map_mul,
    AlgEquiv.commutes, map_pow, map_sub, map_one,
    kummerThreePointScalingAut_monomialCoordinate, mul_pow, mul_div_assoc,
    ← kummerBranchField_coordinate_recover]

/-- The nonlinear branch factor is fixed by the full three-point cyclic action. -/
theorem kummerThreePointScalingAut_branchFactor
    (ζ : K) (hζ : ζ ^ ((n + 1) * (b + 1)) = 1) :
    kummerThreePointScalingAut c b R n ζ hζ (algebraMap K[X] L (1 - X ^ (b + 1))) =
      algebraMap K[X] L (1 - X ^ (b + 1)) := by
  have ht : algebraMap K[X] L (1 - X ^ (b + 1)) =
      1 - kummerMonomialCoordinate c b R n := by
    rw [map_sub, map_one, map_pow]
    rfl
  rw [ht, map_sub, map_one, kummerThreePointScalingAut_monomialCoordinate]

/-- Removing complete branch powers leaves the radical character of each reduced monomial unchanged. -/
theorem kummerThreePointScalingAut_integralMonomial
    (ζ : K) (hζ : ζ ^ ((n + 1) * (b + 1)) = 1) (i : ℕ) :
    kummerThreePointScalingAut c b R n ζ hζ (kummerIntegralMonomial c b R n i) =
      (algebraMap K L ζ) ^ i * kummerIntegralMonomial c b R n i := by
  rw [kummerIntegralMonomial, map_div₀, map_pow, kummerThreePointScalingAut_root,
    map_pow, kummerThreePointScalingAut_branchFactor, mul_pow, mul_div_assoc]
  rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
