import GaloisForLFunctions.HTGeometry.QuantumStagHuntDecoherence

/-!
# Exact criticality laws for the decoherent quantum Stag Hunt

The square-lattice Ising threshold and the closed noise threshold from arXiv:2609.02957
are formalized without ambient hypotheses. Strictly positive inverse temperature is encoded
as the input type. The threshold is physical exactly above the noiseless critical inverse
temperature and makes both attenuated couplings hit Onsager's critical value.
-/

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry
noncomputable section

def squareIsingCriticalCoupling : ℝ := Real.log (1 + Real.sqrt 2) / 2

theorem squareIsingCriticalCoupling_pos : 0 < squareIsingCriticalCoupling := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hl : 0 < Real.log (1 + Real.sqrt 2) := Real.log_pos (by linarith)
  unfold squareIsingCriticalCoupling
  positivity

def phaseDampedCriticalInverseTemperature : ℝ := 4 * squareIsingCriticalCoupling / 3

theorem phaseDampedCriticalInverseTemperature_pos :
    0 < phaseDampedCriticalInverseTemperature := by
  unfold phaseDampedCriticalInverseTemperature
  positivity [squareIsingCriticalCoupling_pos]

/-- At the paper's phase-damped critical temperature, `beta J = kappa_c`. -/
theorem phaseDampedCriticalInverseTemperature_coupling :
    phaseDampedCriticalInverseTemperature * phaseDampedStagHuntInteraction 0 =
      squareIsingCriticalCoupling := by
  simp [phaseDampedCriticalInverseTemperature, phaseDampedStagHuntInteraction]
  ring

/-- Domain of strictly positive inverse temperatures. -/
structure StagHuntPositiveInverseTemperature where
  val : ℝ
  positive : 0 < val

instance : Coe StagHuntPositiveInverseTemperature ℝ :=
  ⟨StagHuntPositiveInverseTemperature.val⟩

/-- Fixed-temperature critical noise `1-sqrt(4 kappa_c/(3 beta))`. -/
def stagHuntCriticalNoise (beta : StagHuntPositiveInverseTemperature) : ℝ :=
  1 - Real.sqrt (phaseDampedCriticalInverseTemperature / (beta : ℝ))

/-- Critical noise has exactly the attenuation required to reach the Ising threshold. -/
theorem stagHuntCriticalNoise_attenuation_balance
    (beta : StagHuntPositiveInverseTemperature) :
    (beta : ℝ) * stagHuntPostADAttenuation (stagHuntCriticalNoise beta) =
      phaseDampedCriticalInverseTemperature := by
  have hx : 0 ≤ phaseDampedCriticalInverseTemperature / (beta : ℝ) :=
    div_nonneg phaseDampedCriticalInverseTemperature_pos.le beta.positive.le
  rw [stagHuntPostADAttenuation, stagHuntCriticalNoise]
  have hs := Real.sq_sqrt hx
  rw [show 1 - (1 - Real.sqrt
      (phaseDampedCriticalInverseTemperature / (beta : ℝ))) =
        Real.sqrt (phaseDampedCriticalInverseTemperature / (beta : ℝ)) by ring,
    hs]
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ phaseDampedCriticalInverseTemperature beta.positive.ne'

/-- The fixed-temperature threshold is physical exactly above the noiseless transition. -/
theorem stagHuntCriticalNoise_physical_iff
    (beta : StagHuntPositiveInverseTemperature) :
    0 ≤ stagHuntCriticalNoise beta ↔
      phaseDampedCriticalInverseTemperature ≤ (beta : ℝ) := by
  have hx : 0 ≤ phaseDampedCriticalInverseTemperature / (beta : ℝ) :=
    div_nonneg phaseDampedCriticalInverseTemperature_pos.le beta.positive.le
  have hs := Real.sq_sqrt hx
  constructor
  · intro h
    have hsqrt : Real.sqrt (phaseDampedCriticalInverseTemperature / (beta : ℝ)) ≤ 1 := by
      unfold stagHuntCriticalNoise at h
      linarith
    have hratio : phaseDampedCriticalInverseTemperature / (beta : ℝ) ≤ 1 := by
      nlinarith [Real.sqrt_nonneg (phaseDampedCriticalInverseTemperature / (beta : ℝ))]
    exact (div_le_one beta.positive).mp hratio
  · intro h
    have hratio : phaseDampedCriticalInverseTemperature / (beta : ℝ) ≤ 1 :=
      (div_le_one beta.positive).mpr h
    have hsqrt : Real.sqrt (phaseDampedCriticalInverseTemperature / (beta : ℝ)) ≤ 1 := by
      nlinarith [Real.sqrt_nonneg (phaseDampedCriticalInverseTemperature / (beta : ℝ))]
    unfold stagHuntCriticalNoise
    linarith

/-- Depolarization evaluated at the closed threshold has `beta J = kappa_c`. -/
theorem depolarizedStagHunt_criticalNoise_coupling
    (beta : StagHuntPositiveInverseTemperature) :
    (beta : ℝ) * depolarizedStagHuntInteraction (stagHuntCriticalNoise beta) =
      squareIsingCriticalCoupling := by
  rw [depolarizedStagHuntInteraction]
  rw [show (1 - stagHuntCriticalNoise beta) ^ (2 : ℕ) =
      stagHuntPostADAttenuation (stagHuntCriticalNoise beta) by rfl]
  have h := stagHuntCriticalNoise_attenuation_balance beta
  unfold phaseDampedCriticalInverseTemperature at h
  nlinarith

/-- Post-circuit amplitude damping has the identical coupling threshold. -/
theorem postDampedStagHunt_criticalNoise_coupling
    (beta : StagHuntPositiveInverseTemperature) :
    (beta : ℝ) * postDampedStagHuntInteraction (stagHuntCriticalNoise beta) =
      squareIsingCriticalCoupling := by
  rw [postDampedStagHuntInteraction]
  have h := stagHuntCriticalNoise_attenuation_balance beta
  unfold phaseDampedCriticalInverseTemperature at h
  nlinarith

end
end GaloisForLFunctions.HTGeometry
