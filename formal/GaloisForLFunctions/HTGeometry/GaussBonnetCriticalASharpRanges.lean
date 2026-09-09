import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalAJets
import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalAEOS

/-!
# Sharp critical observable ranges and their exact relation

The model-A critical family from arXiv:2609.00025 gives more than bounds:
every value in the stated compressibility and quartic-stiffness intervals
is attained. Eliminate the dimensionless coupling to link the two actual
observables by one fractional-linear identity. The endpoints are realized
at zero coupling and zero charge.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbCriticalAStiffness (θ : ℝ) : ℝ := 2 * (1 - 2 * egbCriticalAShape θ) / (1 + 2 * egbCriticalAShape θ)
def egbCriticalACompressibility (θ : ℝ) : ℝ := (3 - 2 * egbCriticalAShape θ) / 8

theorem egbCriticalAStiffness_observable (x θ l : ℝ) :
    iteratedDeriv 4 (egbCriticalALogGibbs x θ l) x / exp x = egbCriticalAStiffness θ := by
  rw [egbCriticalALogGibbs_fourth_derivative]
  unfold egbCriticalAStiffness
  have hb := (egbCriticalAShape_bounds θ).1
  field_simp

theorem egbCriticalACompressibility_observable (x θ : ℝ) :
    egbCriticalAPressure x θ * (2 * exp x) / egbCriticalATemperature x θ = egbCriticalACompressibility θ :=
  egbCriticalA_compressibility_ratio x θ

theorem egbCriticalAStiffness_lower_endpoint :
    2 * (1 - 2 * egbCriticalAMaxShape) / (1 + 2 * egbCriticalAMaxShape) = 2 * sqrt 3 - 2 := by
  have hd : 1 + 2 * egbCriticalAMaxShape ≠ 0 := by
    have hm := egbCriticalAMaxShape_bounds.1
    positivity
  apply (div_eq_iff hd).2
  unfold egbCriticalAMaxShape
  nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem egbCriticalAStiffness_bounds (θ : ℝ) :
    2 * sqrt 3 - 2 ≤ egbCriticalAStiffness θ ∧ egbCriticalAStiffness θ ≤ 2 := by
  have hb := egbCriticalAShape_bounds θ
  have hm := egbCriticalAMaxShape_bounds.1
  have hd : 0 < 1 + 2 * egbCriticalAShape θ := by linarith
  have hmD : 0 < 1 + 2 * egbCriticalAMaxShape := by positivity
  unfold egbCriticalAStiffness
  constructor
  · rw [← egbCriticalAStiffness_lower_endpoint, div_le_div_iff₀ hmD hd]
    nlinarith [hb.2]
  · rw [div_le_iff₀ hd]
    linarith [hb.1]

theorem egbCriticalACompressibility_bounds (θ : ℝ) :
    (6 - sqrt 3) / 12 ≤ egbCriticalACompressibility θ ∧ egbCriticalACompressibility θ ≤ 3 / 8 := by
  have hb := egbCriticalAShape_bounds θ
  unfold egbCriticalAMaxShape at hb
  unfold egbCriticalACompressibility
  constructor <;> nlinarith [hb.1, hb.2]

/-- Exact image of the actual dimensionless quartic stiffness. -/
theorem egbCriticalAStiffness_range (c : ℝ) :
    (∃ θ : ℝ, egbCriticalAStiffness θ = c) ↔ 2 * sqrt 3 - 2 ≤ c ∧ c ≤ 2 := by
  constructor
  · rintro ⟨θ, rfl⟩
    exact egbCriticalAStiffness_bounds θ
  · intro hc
    have hs : 0 < 2 * sqrt 3 - 2 := by
      nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), sqrt_nonneg (3 : ℝ)]
    have hc₀ : 0 < c := lt_of_lt_of_le hs hc.1
    have hd : 0 < 2 * c + 4 := by linarith
    have hm := egbCriticalAMaxShape_bounds.1
    have hmD : 0 < 1 + 2 * egbCriticalAMaxShape := by positivity
    have hmC : 2 * (1 - 2 * egbCriticalAMaxShape) / (1 + 2 * egbCriticalAMaxShape) ≤ c := by
      rw [egbCriticalAStiffness_lower_endpoint]
      exact hc.1
    have hcross := (div_le_iff₀ hmD).1 hmC
    have hb : 0 ≤ (2 - c) / (2 * c + 4) ∧ (2 - c) / (2 * c + 4) ≤ egbCriticalAMaxShape := by
      constructor
      · exact div_nonneg (by linarith [hc.2]) (le_of_lt hd)
      · rw [div_le_iff₀ hd]
        nlinarith
    obtain ⟨θ, he⟩ := (egbCriticalAShape_range ((2 - c) / (2 * c + 4))).2 hb
    refine ⟨θ, ?_⟩
    unfold egbCriticalAStiffness
    rw [he]
    have hB : 0 < 1 + 2 * ((2 - c) / (2 * c + 4)) := by linarith [hb.1]
    apply (div_eq_iff hB.ne').2
    field_simp
    ring

/-- Exact image of the pressure-volume-temperature critical ratio. -/
theorem egbCriticalACompressibility_range (z : ℝ) :
    (∃ θ : ℝ, egbCriticalACompressibility θ = z) ↔ (6 - sqrt 3) / 12 ≤ z ∧ z ≤ 3 / 8 := by
  constructor
  · rintro ⟨θ, rfl⟩
    exact egbCriticalACompressibility_bounds θ
  · intro hz
    have hb : 0 ≤ (3 - 8 * z) / 2 ∧ (3 - 8 * z) / 2 ≤ egbCriticalAMaxShape := by
      unfold egbCriticalAMaxShape
      constructor <;> linarith [hz.1, hz.2]
    obtain ⟨θ, he⟩ := (egbCriticalAShape_range ((3 - 8 * z) / 2)).2 hb
    refine ⟨θ, ?_⟩
    unfold egbCriticalACompressibility
    rw [he]
    ring

/-- Eliminating coupling links the two observables exactly. -/
theorem egbCriticalAStiffness_compressibility_identity (θ : ℝ) :
    egbCriticalAStiffness θ = (4 * egbCriticalACompressibility θ - 1) / (1 - 2 * egbCriticalACompressibility θ) := by
  have hb := (egbCriticalAShape_bounds θ).1
  have hd : 1 - 2 * ((3 - 2 * egbCriticalAShape θ) / 8) = (1 + 2 * egbCriticalAShape θ) / 4 := by ring
  unfold egbCriticalAStiffness egbCriticalACompressibility
  rw [hd]
  field_simp
  ring

/-- Same identity stated solely in terms of actual Gibbs derivatives and critical thermodynamic quantities. -/
theorem egbCriticalA_observable_relation (x θ l : ℝ) :
    iteratedDeriv 4 (egbCriticalALogGibbs x θ l) x / exp x =
      (4 * (egbCriticalAPressure x θ * (2 * exp x) / egbCriticalATemperature x θ) - 1) /
        (1 - 2 * (egbCriticalAPressure x θ * (2 * exp x) / egbCriticalATemperature x θ)) := by
  rw [egbCriticalAStiffness_observable, egbCriticalACompressibility_observable,
    egbCriticalAStiffness_compressibility_identity]

/-- Zero coupling attains both upper endpoints. -/
theorem egbCriticalA_zero_coupling_endpoints (x : ℝ) :
    egbCriticalACouplingRoot x 0 = 0 ∧ egbCriticalAStiffness 0 = 2 ∧ egbCriticalACompressibility 0 = 3 / 8 := by
  norm_num [egbCriticalACouplingRoot, egbCriticalAShape, egbCriticalAStiffness, egbCriticalACompressibility]

/-- The uncharged state attains both lower endpoints. -/
theorem egbCriticalA_zero_charge_endpoints (x : ℝ) :
    egbCriticalACharge x (Real.pi / 2) = 0 ∧ egbCriticalAStiffness (Real.pi / 2) = 2 * sqrt 3 - 2 ∧
      egbCriticalACompressibility (Real.pi / 2) = (6 - sqrt 3) / 12 := by
  have hb : egbCriticalAShape (Real.pi / 2) = egbCriticalAMaxShape := by simp [egbCriticalAShape]
  constructor
  · simp [egbCriticalACharge]
  constructor
  · simpa only [egbCriticalAStiffness, hb] using egbCriticalAStiffness_lower_endpoint
  · unfold egbCriticalACompressibility
    rw [hb]
    unfold egbCriticalAMaxShape
    ring

end GaloisForLFunctions.HTGeometry
