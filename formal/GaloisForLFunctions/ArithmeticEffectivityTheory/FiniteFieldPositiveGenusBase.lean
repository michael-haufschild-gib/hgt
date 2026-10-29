import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticDifferentials
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticZeta

/-!
# A positive-genus base function field with its arithmetic zeta function

The constants are `𝔽₃`, the curve is `Y²Z=X³−XZ²`, and the field is its actual
coordinate fraction field. Geometric genus is certified by the full space of regular
Kähler differentials on the two projective charts. The point-count zeta function has
a numerator of degree twice that genus, with precisely two roots counted with
multiplicity. Neither denominator pole cancels.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

/-- The zeta numerator degree agrees with the independently proved geometric genus. -/
theorem numerator_degree_eq_twice_genus : numerator.natDegree = 2 * geometricGenus := by
  rw [numerator_degree, geometricGenus_eq_one, Nat.mul_one]

/-- The arithmetic zeta function has `2g` zeros, counted with multiplicity. -/
theorem zeta_zero_count_eq_twice_genus : numerator.roots.card = 2 * geometricGenus := by
  rw [numerator_root_count, geometricGenus_eq_one, Nat.mul_one]

/-- A concrete finite-field function field, its positive geometric genus, and its actual
point-count zeta series. All algebraic, geometric, and counting inputs are discharged. -/
theorem positiveGenusBaseField_spec :
    Fintype.card Constants = 3 ∧
    curve.IsElliptic ∧
    Algebra.trdeg Constants FunctionField = 1 ∧
    Module.finrank Constants regularForms = 1 ∧
    0 < geometricGenus ∧
    numerator.natDegree = 2 * geometricGenus ∧
    numerator.roots.card = 2 * geometricGenus ∧
    PowerSeries.constantCoeff zeta = 1 ∧
    ArithmeticCastelnuovoSeveri.HasGhost zeta pointCountGhost ∧
    ((1 - PowerSeries.X) * (1 - PowerSeries.C 3 * PowerSeries.X)) * zeta =
      (numerator : PowerSeries ℂ) ∧
    ∀ T : ℂ, numerator.eval T = 0 →
      zetaFunction T = 0 ∧ ‖T‖ = (Real.sqrt 3)⁻¹ ∧ (1 - T) * (1 - 3 * T) ≠ 0 :=
  ⟨ZMod.card 3, inferInstance, functionField_trdeg_eq_one, geometricGenus_eq_one,
    geometricGenus_pos, numerator_degree_eq_twice_genus, zeta_zero_count_eq_twice_genus,
    zeta_constantCoeff, zeta_hasGhost, zeta_rational, fun T hT =>
      ⟨(numerator_root_is_zeta_zero T hT).1, numerator_zero_norm T hT,
        reciprocal_numerator_nonzero T hT⟩⟩

end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
