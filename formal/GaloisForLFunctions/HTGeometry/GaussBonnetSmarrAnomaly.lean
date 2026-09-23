import GaloisForLFunctions.HTGeometry.GaussBonnetExtendedFirstLaw

/-!
# The fixed-reference logarithmic Smarr term

Apply dimensional scaling to the full first law and logarithmic entropy in
arXiv:2609.00025. At fixed entropy reference length, the usual model-A Smarr
combination misses exactly 4παT. The auxiliary reference conjugate restores
the exact identity. Model B obeys the ordinary homogeneous identity. The
extra term is nonzero on explicitly constructed positive-pressure,
positive-temperature states with positive coupling; no physical inequalities
are supplied as theorem premises.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbSmarrAResidual (P Q a l r : ℝ) : ℝ :=
  egbMass P Q a r - (2 * egbTemperatureA P Q a r * egbEntropyA a l r -
    2 * P * egbThermodynamicVolume r + Q * egbElectricPotential Q r +
      2 * a ^ (2 : ℕ) * egbCouplingConjugateA P Q a l r)

/-- The exact defect of the fixed-reference homogeneous Smarr expression. -/
theorem egbSmarrA_anomaly (P Q a l x : ℝ) :
    egbSmarrAResidual P Q a l (exp x) = 4 * Real.pi * a ^ (2 : ℕ) * egbTemperatureA P Q a (exp x) := by
  have hn : exp x ^ (2 : ℕ) + 2 * a ^ (2 : ℕ) ≠ 0 := by positivity
  unfold egbSmarrAResidual egbMass egbEntropyA egbCouplingConjugateA egbElectricPotential
    egbThermodynamicVolume egbTemperatureA
  field_simp
  ring

/-- Allowing the reference coordinate to scale restores the exact extended Smarr identity. -/
theorem egbSmarrA_with_reference_work (P Q a l x : ℝ) :
    egbMass P Q a (exp x) =
      2 * egbTemperatureA P Q a (exp x) * egbEntropyA a l (exp x) -
        2 * P * egbThermodynamicVolume (exp x) + Q * egbElectricPotential Q (exp x) +
        2 * a ^ (2 : ℕ) * egbCouplingConjugateA P Q a l (exp x) + egbReferenceConjugateA P Q a (exp x) := by
  have h := egbSmarrA_anomaly P Q a l x
  unfold egbSmarrAResidual egbReferenceConjugateA at *
  linarith

/-- Area entropy has no logarithmic scaling defect. -/
theorem egbSmarrB_homogeneous (P Q a x : ℝ) :
    egbMass P Q a (exp x) =
      2 * egbTemperatureB P Q a (exp x) * egbEntropyB (exp x) -
        2 * P * egbThermodynamicVolume (exp x) + Q * egbElectricPotential Q (exp x) +
        2 * a ^ (2 : ℕ) * egbCouplingConjugateB (exp x) := by
  unfold egbMass egbTemperatureB egbEntropyB egbThermodynamicVolume egbElectricPotential egbCouplingConjugateB
  field_simp
  ring

/-- The missing term vanishes exactly at zero coupling or zero temperature. -/
theorem egbSmarrA_anomaly_zero_iff (P Q a l x : ℝ) :
    egbSmarrAResidual P Q a l (exp x) = 0 ↔ a = 0 ∨ egbTemperatureA P Q a (exp x) = 0 := by
  rw [egbSmarrA_anomaly]
  simp [mul_eq_zero, Real.pi_ne_zero]

/-- Entropy normalization does not remove the Smarr defect. -/
theorem egbSmarrA_anomaly_reference_invariant (P Q a l c x : ℝ) :
    egbSmarrAResidual P Q a (l + c) (exp x) = egbSmarrAResidual P Q a l (exp x) := by
  rw [egbSmarrA_anomaly, egbSmarrA_anomaly]

theorem egbTemperatureA_pressure (T Q a x : ℝ) :
    egbTemperatureA (egbPressureA T Q a (exp x)) Q a (exp x) = T := by
  have hn : exp x ^ (2 : ℕ) + 2 * a ^ (2 : ℕ) ≠ 0 := by positivity
  unfold egbTemperatureA egbPressureA
  field_simp
  ring

theorem egbTemperatureB_pressure (T Q a x : ℝ) :
    egbTemperatureB (egbPressureB T Q a (exp x)) Q a (exp x) = T := by
  unfold egbTemperatureB egbPressureB
  field_simp
  ring

/-- A prescribed temperature that makes the model-A pressure positive for every charge and coupling. -/
def egbPositiveExternalTemperature (τ x : ℝ) : ℝ := 1 / (4 * Real.pi * exp x) + exp τ

theorem egbPositiveExternalTemperature_pos (τ x : ℝ) : 0 < egbPositiveExternalTemperature τ x := by
  unfold egbPositiveExternalTemperature
  positivity

theorem egbPressureA_positive_state (Q a τ x : ℝ) :
    0 < egbPressureA (egbPositiveExternalTemperature τ x) Q a (exp x) := by
  have he : egbPressureA (egbPositiveExternalTemperature τ x) Q a (exp x) =
      exp τ / (2 * exp x) + a ^ (2 : ℕ) * egbPositiveExternalTemperature τ x / exp x ^ (3 : ℕ) +
        (Q ^ (2 : ℕ) + a ^ (2 : ℕ)) / (8 * Real.pi * exp x ^ (4 : ℕ)) := by
    unfold egbPressureA egbPositiveExternalTemperature
    ring
  rw [he]
  have hT := egbPositiveExternalTemperature_pos τ x
  positivity

/-- Strictly positive defect on a family with all physical positivity conditions proved. -/
theorem egbSmarrA_positive_state_anomaly (Q b l τ x : ℝ) :
    0 < egbSmarrAResidual (egbPressureA (egbPositiveExternalTemperature τ x) Q (exp b) (exp x)) Q (exp b) l (exp x) := by
  rw [egbSmarrA_anomaly, egbTemperatureA_pressure]
  have hT := egbPositiveExternalTemperature_pos τ x
  positivity

/-- Positive-pressure, positive-temperature examples cannot satisfy the fixed-reference homogeneous formula. -/
theorem egbSmarrA_positive_state_exists (Q b l τ x : ℝ) :
    ∃ P : ℝ, 0 < P ∧ 0 < egbTemperatureA P Q (exp b) (exp x) ∧
      egbMass P Q (exp b) (exp x) ≠
        2 * egbTemperatureA P Q (exp b) (exp x) * egbEntropyA (exp b) l (exp x) -
          2 * P * egbThermodynamicVolume (exp x) + Q * egbElectricPotential Q (exp x) +
          2 * exp b ^ (2 : ℕ) * egbCouplingConjugateA P Q (exp b) l (exp x) := by
  refine ⟨egbPressureA (egbPositiveExternalTemperature τ x) Q (exp b) (exp x),
    egbPressureA_positive_state Q (exp b) τ x, ?_, ?_⟩
  · rw [egbTemperatureA_pressure]
    exact egbPositiveExternalTemperature_pos τ x
  · intro he
    have h := egbSmarrA_positive_state_anomaly Q b l τ x
    unfold egbSmarrAResidual at h
    rw [he, sub_self] at h
    exact lt_irrefl _ h

end GaloisForLFunctions.HTGeometry
