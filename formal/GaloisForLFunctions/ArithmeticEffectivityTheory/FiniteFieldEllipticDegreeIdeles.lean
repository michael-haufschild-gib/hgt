import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLoopCharacters
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticAdditiveDomain

/-!
# Actual elliptic degree ideles

The infinity simple pole and finite components one define an idele of
magnitude three. Its powers realize the degree parameters used by affine
Weyl characters inside the actual adelic unit group.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open Filter
open scoped WithZero WithZeroMulInt NNReal
noncomputable section

private theorem infinitySimplePole_one_ne_zero : infinitySimplePole 1 ≠ 0 := by
  intro h
  have hv := infinitySimplePole_valuation (show (1 : Constants) ≠ 0 from one_ne_zero)
  rw [h, map_zero] at hv
  exact WithZero.coe_ne_zero hv.symm

/-- A genuine idele with trivial finite components and one pole at infinity. -/
def ellipticDegreeOneIdele : Ideles :=
  ideleOfLocalUnits (fun _ => 1) (Units.mk0 (infinitySimplePole 1) infinitySimplePole_one_ne_zero)
    (Filter.Eventually.of_forall fun _ => map_one _)

/-- Degree `d` realized by an actual elliptic idele. -/
def ellipticDegreeIdele (d : ℕ) : Ideles := ellipticDegreeOneIdele ^ d

private theorem toNNReal_exp_one {q : ℝ≥0} (hq : q ≠ 0) :
    WithZeroMulInt.toNNReal hq (WithZero.exp (1 : ℤ)) = q := by
  rw [WithZeroMulInt.toNNReal_neg_apply hq
    (show WithZero.exp (1 : ℤ) ≠ 0 from WithZero.coe_ne_zero)]
  exact zpow_one q

/-- The actual normalized magnitude of the degree-one idele is three. -/
theorem ideleMagnitude_degreeOne : ideleMagnitude ellipticDegreeOneIdele = 3 := by
  change infinityCompletionMagnitude (infinitySimplePole 1) *
    (∏ᶠ v : FinitePlace, finiteCompletionMagnitude v 1) = 3
  simp only [map_one, finprod_one, mul_one]
  change WithZeroMulInt.toNNReal (by norm_num : (3 : ℝ≥0) ≠ 0)
    (Valued.v (infinitySimplePole 1)) = 3
  rw [infinitySimplePole_valuation (show (1 : Constants) ≠ 0 from one_ne_zero)]
  exact toNNReal_exp_one _

/-- The arithmetic degree parameter has exactly its predicted global magnitude. -/
theorem ideleMagnitude_degree (d : ℕ) : ideleMagnitude (ellipticDegreeIdele d) = 3 ^ d := by
  rw [ellipticDegreeIdele, map_pow, ideleMagnitude_degreeOne]

/-- The Weyl damping parameter is the logarithm of an actual idele magnitude. -/
theorem log_ideleMagnitude_degree (d : ℕ) :
    Real.log (ideleMagnitude (ellipticDegreeIdele d) : ℝ) = d * Real.log 3 := by
  rw [ideleMagnitude_degree]
  change Real.log ((3 : ℝ) ^ d) = d * Real.log 3
  exact Real.log_pow 3 d

/-- Every spectral character has the explicit degree value. -/
theorem ideleCharacter_degree (s : ℂ) (d : ℕ) :
    ideleCharacter s (ellipticDegreeIdele d) =
      Complex.exp (s * ((d * Real.log 3 : ℝ) : ℂ)) := by
  change Complex.exp (s * (Real.log (ideleMagnitude (ellipticDegreeIdele d) : ℝ) : ℂ)) = _
  rw [log_ideleMagnitude_degree]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ideleMagnitude_degree
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ideleCharacter_degree
