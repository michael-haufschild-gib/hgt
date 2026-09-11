import GaloisForLFunctions.HTGeometry.GomesTruncatedJetUnipotentExponential
import GaloisForLFunctions.HTGeometry.GomesFiniteFockTaylorLogarithm

/-!
# The literal finite logarithm of every actual unipotent symmetry

The existing finite logarithm polynomial applies to every member of the full
unipotent gauge subgroup. Its value lies in the complete nilpotent coordinate
space, with no restrictions on the geometric phase or jet horizon.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The existing finite logarithm evaluated on the increment of any actual unipotent symmetry. -/
def gomesTruncatedJetUnipotentLogarithm (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) : gomesTruncatedJetNilpotentSpace n z :=
  ⟨Polynomial.aeval (((gomesTruncatedJetInternalUnitsEquiv n z).symm u.val).val - 1)
    (gomesFiniteFockLogarithmPolynomial (n + 1)), by
    change gomesTruncatedJetAugmentation n z _ = 0
    have hu : gomesTruncatedJetAugmentation n z
        (((gomesTruncatedJetInternalUnitsEquiv n z).symm u.val).val) = 1 :=
      congrArg Units.val (show gomesTruncatedJetGaugeCharacter n z u.val = 1 from u.property)
    rw [← Polynomial.aeval_algHom_apply, map_sub, map_one, hu, sub_self,
      ← Polynomial.coeff_zero_eq_aeval_zero, gomesFiniteFockLogarithmPolynomial,
      PowerSeries.coeff_trunc, if_pos (Nat.succ_pos n),
      PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_log]⟩

/-- The logarithmic coordinate is the literal terminating matrix logarithm. -/
theorem gomesTruncatedJetUnipotentLogarithm_val (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) :
    (gomesTruncatedJetUnipotentLogarithm n z u).val.val =
      Polynomial.aeval (u.val.val.val - 1) (gomesFiniteFockLogarithmPolynomial (n + 1)) := by
  change (gomesTruncatedJetJointAlgebra n z).val
    (Polynomial.aeval (((gomesTruncatedJetInternalUnitsEquiv n z).symm u.val).val - 1)
      (gomesFiniteFockLogarithmPolynomial (n + 1))) = _
  rw [← Polynomial.aeval_algHom_apply]
  rfl

/-- Every actual logarithmic coordinate is a horizon-nilpotent matrix. -/
theorem gomesTruncatedJetUnipotentLogarithm_pow (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) :
    (gomesTruncatedJetUnipotentLogarithm n z u).val.val ^ (n + 1) = 0 :=
  gomesTruncatedJetNilpotentSpace_pow n z (gomesTruncatedJetUnipotentLogarithm n z u)

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
