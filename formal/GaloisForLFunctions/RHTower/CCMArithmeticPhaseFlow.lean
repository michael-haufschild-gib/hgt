import GaloisForLFunctions.RHTower.CCMArithmeticPhaseAction

/-!
# A global conservative flow on the actual arithmetic phase orbit

The travel coordinate is onto and strictly increasing. Its inverse gives
global trajectories satisfying Newton and Euler--Lagrange equations, with
the energy conservation proved as a conclusion. The final existential
endpoint identifies the potential with actual restricted Weil quadratics.
-/

noncomputable section

open Filter Set
open scoped SchwartzMap

namespace RHTower

def arithmeticPhaseTravelIso (B : ℝ) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (arithmeticPhaseTravelTime B)
    (strictMono_arithmeticPhaseTravelTime B) (surjective_arithmeticPhaseTravelTime B)

def arithmeticPhaseTrajectory (B t : ℝ) : ℝ := (arithmeticPhaseTravelIso B).symm t

theorem arithmeticPhaseTravelTime_trajectory (B t : ℝ) :
    arithmeticPhaseTravelTime B (arithmeticPhaseTrajectory B t) = t :=
  (arithmeticPhaseTravelIso B).apply_symm_apply t

theorem arithmeticPhaseTrajectory_travelTime (B q : ℝ) :
    arithmeticPhaseTrajectory B (arithmeticPhaseTravelTime B q) = q :=
  (arithmeticPhaseTravelIso B).symm_apply_apply q

theorem arithmeticPhaseTrajectory_zero (B : ℝ) : arithmeticPhaseTrajectory B 0 = 0 := by
  simpa only [arithmeticPhaseTravelTime_zero] using arithmeticPhaseTrajectory_travelTime B 0

theorem continuous_arithmeticPhaseTrajectory (B : ℝ) : Continuous (arithmeticPhaseTrajectory B) :=
  (arithmeticPhaseTravelIso B).symm.toHomeomorph.continuous

theorem hasDerivAt_arithmeticPhaseTrajectory (B t : ℝ) :
    HasDerivAt (arithmeticPhaseTrajectory B) (arithmeticPhaseSpeed B (arithmeticPhaseTrajectory B t)) t := by
  have h := HasDerivAt.of_local_left_inverse (continuous_arithmeticPhaseTrajectory B).continuousAt
    (hasDerivAt_arithmeticPhaseTravelTime B (arithmeticPhaseTrajectory B t))
    (one_div_ne_zero (arithmeticPhaseSpeed_pos B _).ne')
    (Eventually.of_forall (arithmeticPhaseTravelTime_trajectory B))
  simpa only [one_div, inv_inv] using h

theorem hasDerivAt_arithmeticPhaseTrajectory_velocity (B t : ℝ) :
    HasDerivAt (deriv (arithmeticPhaseTrajectory B))
      (-B * Real.sin (arithmeticPhaseTrajectory B t)) t := by
  have he : deriv (arithmeticPhaseTrajectory B) =
      fun s => arithmeticPhaseSpeed B (arithmeticPhaseTrajectory B s) :=
    funext fun s => (hasDerivAt_arithmeticPhaseTrajectory B s).deriv
  rw [he]
  have h := (hasDerivAt_arithmeticPhaseSpeed B (arithmeticPhaseTrajectory B t)).comp t
    (hasDerivAt_arithmeticPhaseTrajectory B t)
  convert! h using 1
  have hv := (arithmeticPhaseSpeed_pos B (arithmeticPhaseTrajectory B t)).ne'
  field_simp

theorem arithmeticPhaseTrajectory_newton (B t : ℝ) :
    deriv (deriv (arithmeticPhaseTrajectory B)) t = -B * Real.sin (arithmeticPhaseTrajectory B t) :=
  (hasDerivAt_arithmeticPhaseTrajectory_velocity B t).deriv

theorem arithmeticPhaseTrajectory_energy (B t : ℝ) :
    arithmeticPhaseMechanicalEnergy B (arithmeticPhaseTrajectory B t)
      (deriv (arithmeticPhaseTrajectory B) t) = arithmeticPhaseEnergyLevel B := by
  rw [(hasDerivAt_arithmeticPhaseTrajectory B t).deriv]
  unfold arithmeticPhaseMechanicalEnergy
  rw [arithmeticPhaseSpeed_sq]
  ring

/-- Euler--Lagrange is verified for the constructed trajectory, not postulated. -/
theorem arithmeticPhaseTrajectory_euler_lagrange (B t : ℝ) :
    deriv (fun s => deriv (arithmeticPhaseLagrangian B (arithmeticPhaseTrajectory B s))
      (deriv (arithmeticPhaseTrajectory B) s)) t =
      deriv (fun q => arithmeticPhaseLagrangian B q (deriv (arithmeticPhaseTrajectory B) t))
        (arithmeticPhaseTrajectory B t) := by
  simp only [(hasDerivAt_arithmeticPhaseLagrangian_velocity _ _ _).deriv,
    (hasDerivAt_arithmeticPhaseLagrangian_position _ _ _).deriv, arithmeticPhaseTrajectory_newton]

def arithmeticPhaseFlow (B q t : ℝ) : ℝ :=
  arithmeticPhaseTrajectory B (t + arithmeticPhaseTravelTime B q)

theorem arithmeticPhaseFlow_zero (B q : ℝ) : arithmeticPhaseFlow B q 0 = q := by
  simp only [arithmeticPhaseFlow, zero_add, arithmeticPhaseTrajectory_travelTime]

/-- Time translations act globally on the constructed energy curve. -/
theorem arithmeticPhaseFlow_add (B q s t : ℝ) :
    arithmeticPhaseFlow B (arithmeticPhaseFlow B q s) t = arithmeticPhaseFlow B q (s + t) := by
  simp only [arithmeticPhaseFlow, arithmeticPhaseTravelTime_trajectory]
  congr 1
  ring

theorem hasDerivAt_arithmeticPhaseFlow (B q t : ℝ) :
    HasDerivAt (arithmeticPhaseFlow B q) (arithmeticPhaseSpeed B (arithmeticPhaseFlow B q t)) t := by
  convert! (hasDerivAt_arithmeticPhaseTrajectory B (t + arithmeticPhaseTravelTime B q)).comp t
    ((hasDerivAt_id t).add_const (arithmeticPhaseTravelTime B q)) using 1
  simp only [mul_one, arithmeticPhaseFlow]

theorem arithmeticPhaseFlow_energy (B q t : ℝ) :
    arithmeticPhaseMechanicalEnergy B (arithmeticPhaseFlow B q t)
      (deriv (arithmeticPhaseFlow B q) t) = arithmeticPhaseEnergyLevel B := by
  rw [(hasDerivAt_arithmeticPhaseFlow B q t).deriv]
  unfold arithmeticPhaseMechanicalEnergy
  rw [arithmeticPhaseSpeed_sq]
  ring

/-- An unconditional global conserved dynamics whose potential is the full arithmetic phase energy. -/
theorem exists_ccmArithmetic_phase_noether_flow :
    ∃ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a)
      (theta : 𝓢(ℝ, ℝ)) (B : ℝ), 0 < B ∧
      (∀ q : ℝ, ccmPhaseLocalizationEnergy u theta q =
        ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + arithmeticPhasePotential B q) ∧
      (∀ q t : ℝ, (deriv (arithmeticPhaseFlow B q) t) ^ 2 / 2 +
        ccmPhaseLocalizationEnergy u theta (arithmeticPhaseFlow B q t) =
          ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector + 2 * B + 1) ∧
      (∀ t : ℝ, deriv (deriv (arithmeticPhaseTrajectory B)) t =
        -deriv (ccmPhaseLocalizationEnergy u theta) (arithmeticPhaseTrajectory B t)) := by
  obtain ⟨a, u, theta, B, hB, _, _, _, he, hd⟩ := exists_ccmArithmetic_positive_phase_potential
  refine ⟨a, u, theta, B, hB, he, ?_, ?_⟩
  · intro q t
    rw [he]
    have h := arithmeticPhaseFlow_energy B q t
    unfold arithmeticPhaseMechanicalEnergy arithmeticPhaseEnergyLevel arithmeticPhasePotential at h
    rw [abs_of_pos hB] at h
    linarith
  · intro t
    rw [arithmeticPhaseTrajectory_newton, (hd _).deriv, neg_mul]

end RHTower
