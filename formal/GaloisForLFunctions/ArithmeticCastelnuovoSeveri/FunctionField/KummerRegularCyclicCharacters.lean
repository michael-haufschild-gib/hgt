import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointDifferentials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularMonomialBasis
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RegularDifferentialEquivalence

/-!
# The cyclic character basis of regular differentials

The full cyclic scaling acts on the actual function field and preserves
intrinsic regular differentials. In the explicit regular monomial basis,
its eigenvalues are the powers indexed by the full cyclic weights.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
open GaloisForLFunctions.HTGeometry
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
local notation "M" => (p ^ (s + 1) + 1) * (p ^ (d + 1) - 1)

private theorem fullScaling_degree :
    (p ^ (s + 1) + 1) * (p ^ (d + 1) - 2 + 1) = M := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  rw [show p ^ (d + 1) - 2 + 1 = p ^ (d + 1) - 1 by omega]

/-- Every full cyclic root of unity acts on the actual prime-power Kummer model. -/
def squareKummerCyclicScalingAut (ζ : K) (hζ : ζ ^ M = 1) : L ≃ₐ[K] L :=
  kummerThreePointScalingAut c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
    (p ^ (s + 1)) ζ (by rw [fullScaling_degree p s d]; exact hζ)

/-- Full cyclic scaling acts by linear equivalences on actual global regular differentials. -/
def squareKummerRegularScaling (ζ : K) (hζ : ζ ^ M = 1) :
    globalRegularDifferentials K L ≃ₗ[K] globalRegularDifferentials K L :=
  globalRegularDifferentialEquiv (squareKummerCyclicScalingAut p s c d r ζ hζ)

/-- The explicit regular monomial basis diagonalizes the full cyclic scaling action. -/
theorem squareKummerRegularScaling_basis (ζ : K) (hζ : ζ ^ M = 1)
    (a : SquareKummerRegularIndex p s d r) :
    squareKummerRegularScaling p s c d r ζ hζ (squareKummerRegularMonomialBasis p s c d r a) =
      ζ ^ squareKummerRegularWeight p s d r a • squareKummerRegularMonomialBasis p s c d r a := by
  have hi : a.1.val ≤ (p ^ (s + 1) + 1) * (a.2.val + 1) := by
    have h := Nat.mul_le_mul_left (p ^ (s + 1) + 1)
      (show 1 ≤ a.2.val + 1 by omega)
    rw [mul_one] at h
    exact a.1.isLt.le.trans h
  apply Subtype.ext
  change algHomKaehlerMap (squareKummerCyclicScalingAut p s c d r ζ hζ).toAlgHom
    (squareKummerRegularMonomialBasis p s c d r a).val =
      ζ ^ squareKummerRegularWeight p s d r a • (squareKummerRegularMonomialBasis p s c d r a).val
  rw [squareKummerRegularMonomialBasis_apply]
  exact kummerThreePointScalingAut_monomial_differential c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)) ζ
    (by rw [fullScaling_degree p s d]; exact hζ) a.1.val a.2.val hi

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
