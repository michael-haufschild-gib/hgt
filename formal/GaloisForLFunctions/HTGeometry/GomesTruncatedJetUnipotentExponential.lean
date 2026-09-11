import GaloisForLFunctions.HTGeometry.GomesTruncatedJetNilpotentSpace
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeSplitting
import GaloisForLFunctions.HTGeometry.GomesFiniteFockFormalLogarithm

/-!
# Exponentiating every nilpotent joint coordinate into the actual gauge group

The finite universal exponential is evaluated in the existing joint algebra.
Its augmentation is one, so it is an actual matrix unit in the unipotent gauge
subgroup for every phase and horizon.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- The finite universal exponential evaluated in the actual joint algebra. -/
def gomesTruncatedJetNilpotentExponential (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) : gomesTruncatedJetJointAlgebra n z :=
  Polynomial.aeval E.val (PowerSeries.trunc (n + 1) (PowerSeries.exp ℂ))

/-- The finite exponential is evaluated at exactly the original nilpotent matrix. -/
theorem gomesTruncatedJetNilpotentExponential_val (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    (gomesTruncatedJetNilpotentExponential n z E).val =
      Polynomial.aeval E.val.val (PowerSeries.trunc (n + 1) (PowerSeries.exp ℂ)) :=
  (Polynomial.aeval_algHom_apply (gomesTruncatedJetJointAlgebra n z).val E.val _).symm

/-- Every nilpotent coordinate exponentiates to scalar coordinate one. -/
theorem gomesTruncatedJetNilpotentExponential_augmentation (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    gomesTruncatedJetAugmentation n z (gomesTruncatedJetNilpotentExponential n z E) = 1 := by
  unfold gomesTruncatedJetNilpotentExponential
  rw [← Polynomial.aeval_algHom_apply, gomesTruncatedJetNilpotentSpace_augmentation,
    ← Polynomial.coeff_zero_eq_aeval_zero, PowerSeries.coeff_trunc,
    if_pos (Nat.succ_pos n), PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_exp]

/-- The finite exponential is always an actual invertible matrix. -/
theorem gomesTruncatedJetNilpotentExponential_isUnit (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    IsUnit (gomesTruncatedJetNilpotentExponential n z E).val := by
  rw [gomesTruncatedJetJointAlgebra_isUnit_iff, gomesTruncatedJetNilpotentExponential_augmentation]
  exact one_ne_zero

/-- The finite exponential packaged as an actual gauge transformation. -/
def gomesTruncatedJetNilpotentExponentialGauge (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) : gomesTruncatedJetGaugeGroup n z :=
  ⟨(gomesTruncatedJetNilpotentExponential_isUnit n z E).unit, by
    rw [gomesTruncatedJetGaugeGroup_mem_iff, IsUnit.unit_spec]
    exact (gomesTruncatedJetNilpotentExponential n z E).property⟩

/-- Packaging as a unit leaves the exponential matrix unchanged. -/
theorem gomesTruncatedJetNilpotentExponentialGauge_val (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    (gomesTruncatedJetNilpotentExponentialGauge n z E).val.val =
      (gomesTruncatedJetNilpotentExponential n z E).val :=
  (gomesTruncatedJetNilpotentExponential_isUnit n z E).unit_spec

/-- Every exponential gauge transformation lies in the scalar character kernel. -/
theorem gomesTruncatedJetNilpotentExponentialGauge_character (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    gomesTruncatedJetGaugeCharacter n z (gomesTruncatedJetNilpotentExponentialGauge n z E) = 1 := by
  apply Units.ext
  rw [gomesTruncatedJetGaugeCharacter_val, gomesTruncatedJetNilpotentExponentialGauge_val]
  exact gomesTruncatedJetNilpotentExponential_augmentation n z E

/-- Exponentiation into the entire actual unipotent gauge subgroup. -/
def gomesTruncatedJetUnipotentExponential (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) : gomesTruncatedJetUnipotentGroup n z :=
  ⟨gomesTruncatedJetNilpotentExponentialGauge n z E,
    gomesTruncatedJetNilpotentExponentialGauge_character n z E⟩

/-- The unipotent exponential acts by the literal finite exponential matrix. -/
theorem gomesTruncatedJetUnipotentExponential_val (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    (gomesTruncatedJetUnipotentExponential n z E).val.val.val =
      Polynomial.aeval E.val.val (PowerSeries.trunc (n + 1) (PowerSeries.exp ℂ)) := by
  rw [show (gomesTruncatedJetUnipotentExponential n z E).val =
      gomesTruncatedJetNilpotentExponentialGauge n z E from rfl,
    gomesTruncatedJetNilpotentExponentialGauge_val, gomesTruncatedJetNilpotentExponential_val]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
