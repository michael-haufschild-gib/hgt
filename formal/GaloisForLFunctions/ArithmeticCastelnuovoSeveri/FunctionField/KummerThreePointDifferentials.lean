import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointScaling
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.ValuationDifferentialTransport

/-!
# Differential characters of the three-point action

The full cyclic scaling multiplies `dy` by `ζ^N`. Together with the
literal radical weights, this gives weight `N(k+1)-i` to the monomial
differential `y^k dy/β_i` whenever that exponent is nonnegative.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open GaloisForLFunctions.HTGeometry
variable {K : Type*} [Field K] (c : Kˣ) (b R n : ℕ)
local notation "L" => KummerBranchField c b R n
local notation "dy" => KaehlerDifferential.D K L (algebraMap K[X] L X)

/-- The original coordinate differential has the covering-degree character. -/
theorem kummerThreePointScalingAut_differential
    (ζ : K) (hζ : ζ ^ ((n + 1) * (b + 1)) = 1) :
    algHomKaehlerMap (kummerThreePointScalingAut c b R n ζ hζ).toAlgHom dy =
      ζ ^ (n + 1) • dy := by
  rw [algHomKaehlerMap_D, kummerThreePointScalingAut_coordinate,
    ← map_pow, (KaehlerDifferential.D K L).leibniz,
    (KaehlerDifferential.D K L).map_algebraMap, smul_zero, add_zero,
    IsScalarTower.algebraMap_smul]

/-- Polynomial inverse-radical monomial differentials have the expected full cyclic character. -/
theorem kummerThreePointScalingAut_monomial_differential
    (ζ : K) (hζ : ζ ^ ((n + 1) * (b + 1)) = 1) (i k : ℕ)
    (hik : i ≤ (n + 1) * (k + 1)) :
    algHomKaehlerMap (kummerThreePointScalingAut c b R n ζ hζ).toAlgHom
      (((algebraMap K[X] L X) ^ k / kummerIntegralMonomial c b R n i) • dy) =
        ζ ^ ((n + 1) * (k + 1) - i) •
          (((algebraMap K[X] L X) ^ k / kummerIntegralMonomial c b R n i) • dy) := by
  let a := algebraMap K L ζ
  let y := algebraMap K[X] L X
  let β := kummerIntegralMonomial c b R n i
  let j := (n + 1) * (k + 1) - i
  have hζ0 : ζ ≠ 0 := by
    intro hzero
    have hpow := hζ
    rw [hzero, zero_pow (Nat.ne_of_gt (Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos b)))] at hpow
    exact zero_ne_one hpow
  have ha : a ≠ 0 := fun h => hζ0
    ((algebraMap K L).injective (h.trans (map_zero _).symm))
  have hbalance : a ^ j * a ^ i = (a ^ (n + 1)) ^ k * a ^ (n + 1) := by
    rw [← pow_add, Nat.sub_add_cancel hik, pow_mul, pow_succ]
  rw [algHomKaehlerMap_smul, map_div₀, map_pow, kummerThreePointScalingAut_coordinate,
    kummerThreePointScalingAut_integralMonomial, kummerThreePointScalingAut_differential]
  rw [← IsScalarTower.algebraMap_smul K L (ζ ^ (n + 1)),
    ← IsScalarTower.algebraMap_smul K L (ζ ^ ((n + 1) * (k + 1) - i)),
    map_pow, map_pow, smul_smul, smul_smul]
  change (((a ^ (n + 1) * y) ^ k / (a ^ i * β)) * a ^ (n + 1)) • dy =
    (a ^ j * (y ^ k / β)) • dy
  congr 1
  calc
    ((a ^ (n + 1) * y) ^ k / (a ^ i * β)) * a ^ (n + 1) =
        ((a ^ (n + 1)) ^ k * a ^ (n + 1) * y ^ k) / (a ^ i * β) := by
          rw [mul_pow, div_mul_eq_mul_div]
          congr 1
          ring
    _ = (a ^ i * (a ^ j * y ^ k)) / (a ^ i * β) := by
      rw [← hbalance]
      congr 1
      ring
    _ = (a ^ j * y ^ k) / β := mul_div_mul_left _ _ (pow_ne_zero i ha)
    _ = a ^ j * (y ^ k / β) := mul_div_assoc _ _ _

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
