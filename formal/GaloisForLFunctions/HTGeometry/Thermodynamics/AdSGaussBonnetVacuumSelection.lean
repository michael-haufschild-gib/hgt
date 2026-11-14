import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetCylinder

/-!
# Neutral vacuum selection across couplings

The cylinder vacuum is convex although the black-hole potential is
concave. Its tangent source selects exactly one coupling. At the explicit
positive temperature `1/(100π)`, a sum-of-squares decomposition places
every neutral black hole above that selected vacuum. This distinguishes
the neutral ensemble from the charged endpoint competition.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

def physicalCoupling (θ : ℝ) : ℝ := (9 / 100) * Real.sin θ ^ 2

theorem physicalCoupling_bounds (θ : ℝ) :
    0 ≤ physicalCoupling θ ∧ physicalCoupling θ ≤ 9 / 100 := by
  unfold physicalCoupling
  constructor
  · positivity
  · nlinarith only [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]

theorem physical_eta_pos (θ : ℝ) : 0 < eta (physicalCoupling θ) := by
  unfold eta
  apply Real.sqrt_pos.mpr
  linarith only [(physicalCoupling_bounds θ).2]

theorem physical_eta_sq (θ : ℝ) :
    eta (physicalCoupling θ) ^ 2 = 1 - 4 * physicalCoupling θ := by
  unfold eta
  apply Real.sq_sqrt
  linarith only [(physicalCoupling_bounds θ).2]

theorem physical_beta_pos (θ : ℝ) : 0 < beta (physicalCoupling θ) := by
  unfold beta
  apply Real.sqrt_pos.mpr
  have h := physical_eta_pos θ
  positivity

theorem physical_beta_sq (θ : ℝ) :
    beta (physicalCoupling θ) ^ 2 = (1 + eta (physicalCoupling θ)) / 2 := by
  unfold beta
  apply Real.sq_sqrt
  have h := physical_eta_pos θ
  positivity

theorem physical_beta_sq_lower (θ : ℝ) : 9 / 10 ≤ beta (physicalCoupling θ) ^ 2 := by
  have he : 4 / 5 ≤ eta (physicalCoupling θ) := by
    by_contra h
    have hlt : eta (physicalCoupling θ) < 4 / 5 := lt_of_not_ge h
    have hp : 0 < (4 / 5 - eta (physicalCoupling θ)) * (4 / 5 + eta (physicalCoupling θ)) :=
      mul_pos (sub_pos.mpr hlt) (by have he := physical_eta_pos θ; positivity)
    nlinarith only [hp, physical_eta_sq θ, (physicalCoupling_bounds θ).2]
  linarith only [physical_beta_sq θ, he]

theorem physical_beta_half_le (θ : ℝ) : 1 / 2 ≤ beta (physicalCoupling θ) := by
  by_contra h
  have hlt : beta (physicalCoupling θ) < 1 / 2 := lt_of_not_ge h
  have hp : 0 < (1 / 2 - beta (physicalCoupling θ)) * (1 / 2 + beta (physicalCoupling θ)) :=
    mul_pos (sub_pos.mpr hlt) (by have hb := physical_beta_pos θ; positivity)
  nlinarith only [hp, physical_beta_sq_lower θ]

/-- The clock itself is an algebraic coordinate on the physical coupling interval. -/
theorem physicalCoupling_clock (θ : ℝ) :
    physicalCoupling θ = beta (physicalCoupling θ) ^ 2 - beta (physicalCoupling θ) ^ 4 := by
  have he : eta (physicalCoupling θ) = 2 * beta (physicalCoupling θ) ^ 2 - 1 := by
    linarith only [physical_beta_sq θ]
  have hs := physical_eta_sq θ
  rw [he] at hs
  nlinarith only [hs]

theorem vacuumEnergy_clock_polynomial (θ : ℝ) :
    vacuumEnergy (physicalCoupling θ) =
      (9 / 2) * beta (physicalCoupling θ) ^ 5 - (15 / 4) * beta (physicalCoupling θ) ^ 3 := by
  have he : eta (physicalCoupling θ) = 2 * beta (physicalCoupling θ) ^ 2 - 1 := by
    linarith only [physical_beta_sq θ]
  unfold vacuumEnergy
  rw [he]
  ring

def vacuumSource (θ : ℝ) : ℝ := -(45 / 8) * beta (physicalCoupling θ)
def controlledVacuum (z l : ℝ) : ℝ := vacuumEnergy l - z * l
def vacuumTangentFactor (θ φ : ℝ) : ℝ :=
  12 * beta (physicalCoupling θ) ^ 3 +
    9 * beta (physicalCoupling φ) * beta (physicalCoupling θ) ^ 2 +
    (6 * beta (physicalCoupling φ) ^ 2 - 10) * beta (physicalCoupling θ) +
    3 * beta (physicalCoupling φ) ^ 3 - 5 * beta (physicalCoupling φ)

theorem vacuumTangentFactor_pos (θ φ : ℝ) : 0 < vacuumTangentFactor θ φ := by
  have hb := physical_beta_pos θ
  have hc := physical_beta_pos φ
  have hb₂ : 0 ≤ beta (physicalCoupling θ) ^ 2 - 2 / 3 := by
    linarith only [physical_beta_sq_lower θ]
  have hc₂ : 0 ≤ beta (physicalCoupling φ) ^ 2 - 2 / 3 := by
    linarith only [physical_beta_sq_lower φ]
  have heq : vacuumTangentFactor θ φ =
      12 * beta (physicalCoupling θ) * (beta (physicalCoupling θ) ^ 2 - 2 / 3) +
      6 * beta (physicalCoupling θ) * (beta (physicalCoupling φ) ^ 2 - 2 / 3) +
      9 * beta (physicalCoupling φ) * (beta (physicalCoupling θ) ^ 2 - 2 / 3) +
      3 * beta (physicalCoupling φ) * (beta (physicalCoupling φ) ^ 2 - 2 / 3) +
      2 * beta (physicalCoupling θ) + 3 * beta (physicalCoupling φ) := by
    unfold vacuumTangentFactor
    ring
  rw [heq]
  positivity

/-- The tangent-line defect factors globally, with a strictly positive residual factor. -/
theorem controlledVacuum_gap (θ φ : ℝ) :
    controlledVacuum (vacuumSource φ) (physicalCoupling θ) -
        controlledVacuum (vacuumSource φ) (physicalCoupling φ) =
      (3 / 8) * (beta (physicalCoupling θ) - beta (physicalCoupling φ)) ^ 2 *
        vacuumTangentFactor θ φ := by
  have hθ := congrArg (fun l : ℝ => (-(45 / 8) * beta (physicalCoupling φ)) * l)
    (physicalCoupling_clock θ)
  have hφ := congrArg (fun l : ℝ => (-(45 / 8) * beta (physicalCoupling φ)) * l)
    (physicalCoupling_clock φ)
  unfold controlledVacuum vacuumSource
  rw [vacuumEnergy_clock_polynomial, vacuumEnergy_clock_polynomial]
  rw [hθ, hφ]
  unfold vacuumTangentFactor
  ring

theorem controlledVacuum_global_lower_bound (θ φ : ℝ) :
    controlledVacuum (vacuumSource φ) (physicalCoupling φ) ≤
      controlledVacuum (vacuumSource φ) (physicalCoupling θ) := by
  apply sub_nonneg.mp
  rw [controlledVacuum_gap]
  have h := vacuumTangentFactor_pos θ φ
  positivity

/-- A tangent source selects exactly its prescribed coupling, including interior couplings. -/
theorem controlledVacuum_unique_coupling (θ φ : ℝ) :
    controlledVacuum (vacuumSource φ) (physicalCoupling θ) =
        controlledVacuum (vacuumSource φ) (physicalCoupling φ) ↔
      physicalCoupling θ = physicalCoupling φ := by
  constructor
  · intro h
    have hg := controlledVacuum_gap θ φ
    rw [h, sub_self] at hg
    have hs : (beta (physicalCoupling θ) - beta (physicalCoupling φ)) ^ 2 = 0 := by
      have hprod := (mul_eq_zero.mp hg.symm).resolve_right (vacuumTangentFactor_pos θ φ).ne'
      exact (mul_eq_zero.mp hprod).resolve_left (by norm_num)
    have hb := sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp hs)
    rw [physicalCoupling_clock θ, physicalCoupling_clock φ, hb]
  · intro h
    rw [h]

/-- An explicit square decomposition separates every neutral black hole from its vacuum. -/
theorem neutral_low_temperature_gap (z θ u : ℝ) :
    cylinderPotential (1 / (100 * Real.pi)) z 0 (Real.exp u) (physicalCoupling θ) -
        controlledVacuum z (physicalCoupling θ) =
      3 * (beta (physicalCoupling θ) - 1 / 2) *
          (Real.exp u ^ 4 + Real.exp u ^ 2 + physicalCoupling θ) +
      (37 / 25) * Real.exp u ^ 4 + (34 / 25) * Real.exp u ^ 2 +
      (69 / 50) * physicalCoupling θ + (1 / 50) * (Real.exp u ^ 2 - Real.exp u) ^ 2 +
      (3 / 25) * physicalCoupling θ * (Real.exp u - 1) ^ 2 +
      (3 / 25) * (1 - physicalCoupling θ) * Real.exp u ^ 2 := by
  unfold cylinderPotential controlledVacuum energy entropy
  field_simp
  ring

theorem neutral_blackHole_above_vacuum (z θ u : ℝ) :
    controlledVacuum z (physicalCoupling θ) <
      cylinderPotential (1 / (100 * Real.pi)) z 0 (Real.exp u) (physicalCoupling θ) := by
  apply sub_pos.mp
  rw [neutral_low_temperature_gap]
  have hb : 0 ≤ beta (physicalCoupling θ) - 1 / 2 := sub_nonneg.mpr (physical_beta_half_le θ)
  have hl := (physicalCoupling_bounds θ).1
  have hu : 0 ≤ 1 - physicalCoupling θ := by linarith only [(physicalCoupling_bounds θ).2]
  positivity

/-- The selected vacuum beats every neutral black hole at every physical coupling and radius. -/
theorem neutral_selected_vacuum_global (φ θ u : ℝ) :
    controlledVacuum (vacuumSource φ) (physicalCoupling φ) <
      cylinderPotential (1 / (100 * Real.pi)) (vacuumSource φ) 0 (Real.exp u) (physicalCoupling θ) :=
  (controlledVacuum_global_lower_bound θ φ).trans_lt
    (neutral_blackHole_above_vacuum (vacuumSource φ) θ u)

theorem physicalCoupling_pi_six : physicalCoupling (Real.pi / 6) = 9 / 400 := by
  norm_num [physicalCoupling, Real.sin_pi_div_six]

/-- An explicit interior vacuum beats all neutral black holes in the full coupling window. -/
theorem neutral_interior_vacuum_global (θ u : ℝ) :
    controlledVacuum (-(45 / 8) * beta (9 / 400)) (9 / 400) <
      cylinderPotential (1 / (100 * Real.pi)) (-(45 / 8) * beta (9 / 400)) 0
        (Real.exp u) (physicalCoupling θ) := by
  have h := neutral_selected_vacuum_global (Real.pi / 6) θ u
  simpa only [vacuumSource, physicalCoupling_pi_six] using h

#print axioms controlledVacuum_unique_coupling
#print axioms neutral_low_temperature_gap
#print axioms neutral_selected_vacuum_global
#print axioms neutral_interior_vacuum_global

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet
