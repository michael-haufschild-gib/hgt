import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularDifferentialEquiv
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRegularCharacterWeights
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.StdBasis

/-!
# A monomial basis of intrinsic regular differentials

The monomial bases of the bounded polynomial character spaces transport
through the global regularity equivalence. This yields a basis of the
actual regular Kähler differentials, with explicit inverse-radical
monomials as its vectors.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
local notation "β" => kummerIntegralMonomial c (p ^ (d + 1) - 2)
  (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))
local notation "dy" => KaehlerDifferential.D K L (algebraMap K[X] L X)

/-- Polynomial monomials in each character space give a basis of actual global regular differentials. -/
def squareKummerRegularMonomialBasis :
    Module.Basis (SquareKummerRegularIndex p s d r) K (globalRegularDifferentials K L) :=
  (Pi.basis (fun i : Fin (p ^ (s + 1) + 1) =>
    degreeLT.basis K (kummerDifferentialCutoff p s d r i.val))).map
      (squareKummerRegularDifferentialEquiv p s c d r)

/-- Each regular basis vector is the literal polynomial inverse-character differential. -/
theorem squareKummerRegularMonomialBasis_apply (a : SquareKummerRegularIndex p s d r) :
    (squareKummerRegularMonomialBasis p s c d r a).val =
      ((algebraMap K[X] L X) ^ a.2.val / β a.1.val) • dy := by
  classical
  rw [squareKummerRegularMonomialBasis, Module.Basis.map_apply, Pi.basis_apply]
  let coefficient : SquareKummerRegularCoefficientSpace p s d r :=
    Pi.single a.1 (degreeLT.basis K (kummerDifferentialCutoff p s d r a.1.val) a.2)
  change (∑ i : Fin (p ^ (s + 1) + 1),
    (algebraMap K[X] L (coefficient i : K[X]) / β i.val) • dy) = _
  dsimp only [coefficient]
  rw [Finset.sum_eq_single a.1]
  · rw [Pi.single_eq_same, degreeLT.basis_val, map_pow]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi, Submodule.coe_zero, map_zero, zero_div, zero_smul]
  · intro hi
    exact (hi (Finset.mem_univ _)).elim

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
