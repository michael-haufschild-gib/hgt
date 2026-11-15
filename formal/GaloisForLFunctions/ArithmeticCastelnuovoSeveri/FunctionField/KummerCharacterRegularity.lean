import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerReducedDifferentials
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityPolynomialOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIntegralMonomialOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDifferentialCutoffs
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Exact regularity of a radical character differential

Polynomial multiples of inverse reduced radical differentials are regular
at every finite place. At infinity, the exact pole orders give a strict
polynomial-degree cutoff. This classifies each character space using the
actual local Kähler images.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
open GaloisForLFunctions.HTGeometry
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ)

/-- Infinity gives the exact valuation of a polynomial inverse-character differential coefficient. -/
theorem squareKummer_characterForm_infinity_order
    (f : (SquareConstantField p s)[X]) (hf : f ≠ 0) (i : Fin (p ^ (s + 1) + 1)) :
    squareKummerInfinityValuation p s c d r
      (algebraMap (SquareConstantField p s)[X]
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) f /
        kummerIntegralMonomial c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
          (p ^ (s + 1)) i.val *
        squareKummerUniformizerDerivation p s c (p ^ (d + 1) - 2)
          (kummerExponent (p ^ (d + 1)) r) (squareKummerInfinityUniformizer p s c d r)
          (algebraMap (SquareConstantField p s)[X]
            (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X)) =
      WithZero.exp
        ((((p ^ (s + 1) + 1) * (f.natDegree + 1) + 1 : ℕ) : ℤ) -
          ((i.val + (p ^ (d + 1) - 1) *
            (i.val * kummerExponent (p ^ (d + 1)) r % (p ^ (s + 1) + 1)) : ℕ) : ℤ)) := by
  rw [map_mul, map_div₀, squareKummerInfinityValuation_polynomial p s c d r f hf,
    squareKummerInfinityValuation_integralMonomial, squareKummerInfinity_derivative_coordinate,
    ← WithZero.exp_sub, ← WithZero.exp_add]
  congr 1
  push_cast
  ring

/-- A single polynomial character form is globally regular precisely below its degree cutoff. -/
theorem squareKummer_characterForm_regular_iff
    (f : (SquareConstantField p s)[X]) (i : Fin (p ^ (s + 1) + 1)) :
    (algebraMap (SquareConstantField p s)[X]
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) f /
      kummerIntegralMonomial c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
        (p ^ (s + 1)) i.val) •
      KaehlerDifferential.D (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))
        (algebraMap (SquareConstantField p s)[X]
          (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X) ∈
      globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) ↔
      f = 0 ∨ f.natDegree < kummerDifferentialCutoff p s d r i.val := by
  by_cases hf : f = 0
  · subst f
    simp only [map_zero, zero_div, zero_smul, Submodule.zero_mem, true_or]
  let K := SquareConstantField p s
  let A := K[X]
  let b := p ^ (d + 1) - 2
  let R := kummerExponent (p ^ (d + 1)) r
  let L := SquareKummerField p s c b R
  let B := SquareKummerNormalization p s c b R
  let β := kummerIntegralMonomial c b R (p ^ (s + 1)) i.val
  have hfinite (w : HeightOneSpectrum B) :
      w.valuation L (algebraMap A L f / β * squareKummerUniformizerDerivation p s c b R
        (placeUniformizer L w) (algebraMap A L X)) ≤ 1 := by
    have hp : w.valuation L (algebraMap A L f) ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply A B L]
      exact w.valuation_le_one _
    have hβ := (squareKummer_coordinateForm_local_regular_iff p s c b R (w.valuation L)
      (heightOne_constants_mem w) (placeUniformizer L w) (placeUniformizer_valuation L w) β⁻¹).mp
        (squareKummer_inverseMonomial_differential_finite_regular p s d c R w i)
    rw [div_eq_mul_inv, mul_assoc]
    exact show algebraMap A L f * (β⁻¹ * squareKummerUniformizerDerivation p s c b R
      (placeUniformizer L w) (algebraMap A L X)) ∈ (w.valuation L).valuationSubring from mul_mem hp hβ
  rw [squareKummer_coordinateForm_global_regular_iff, or_iff_right hf]
  have hinfinity :
      squareKummerInfinityValuation p s c d r
        (algebraMap A L f / β * squareKummerUniformizerDerivation p s c b R
          (squareKummerInfinityUniformizer p s c d r) (algebraMap A L X)) ≤ 1 ↔
        f.natDegree < kummerDifferentialCutoff p s d r i.val := by
    rw [squareKummer_characterForm_infinity_order p s c d r f hf i,
      ← WithZero.exp_zero, WithZero.exp_le_exp, sub_nonpos,
      ← kummerDifferentialCutoff_iff p s d r i f.natDegree]
    norm_cast
  exact ⟨fun h => hinfinity.mp h.2, fun h => ⟨hfinite, hinfinity.mpr h⟩⟩

/-- Each regular character space is the bounded-degree polynomial space specified by its cutoff. -/
theorem squareKummer_characterForm_regular_iff_degreeLT
    (f : (SquareConstantField p s)[X]) (i : Fin (p ^ (s + 1) + 1)) :
    (algebraMap (SquareConstantField p s)[X]
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) f /
      kummerIntegralMonomial c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
        (p ^ (s + 1)) i.val) •
      KaehlerDifferential.D (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))
        (algebraMap (SquareConstantField p s)[X]
          (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X) ∈
      globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) ↔
      f ∈ degreeLT (SquareConstantField p s) (kummerDifferentialCutoff p s d r i.val) := by
  rw [squareKummer_characterForm_regular_iff, mem_degreeLT]
  by_cases hf : f = 0
  · subst f
    simp only [true_or, degree_zero, bot_lt_coe]
  · rw [or_iff_right hf]
    exact natDegree_lt_iff_degree_lt hf

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
