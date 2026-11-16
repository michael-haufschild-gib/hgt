import GaloisForLFunctions.HTGeometry.HermiteHamiltonian
import GaloisForLFunctions.BlackHoleRingdown.Damping.ScalarModeSolutions

/-!
# Critical damping on the Hermite spectrum

The scalar cleaning law applies to the oscillator Hamiltonian with frequencies
`√(2π(2n+1))`. The ground mode is always the slowest. Critical damping of that mode
makes every Hermite mode have the same characteristic decay rate `√(2π)`.
The critically damped separated field also solves the Hamiltonian wave equation.
-/

noncomputable section
namespace GaloisForLFunctions
open BlackHoleRingdown

/-- Natural frequency of the `n`th Hermite Hamiltonian mode. -/
def hermiteModeFrequency (n : ℕ) : ℝ := Real.sqrt (2 * Real.pi * (2 * n + 1))

theorem hermiteModeFrequency_nonneg (n : ℕ) : 0 ≤ hermiteModeFrequency n :=
  Real.sqrt_nonneg _

theorem hermiteModeFrequency_sq (n : ℕ) :
    hermiteModeFrequency n ^ 2 = 2 * Real.pi * (2 * n + 1) := by
  exact Real.sq_sqrt (by positivity)

/-- The Hermite frequencies increase from a positive ground frequency. -/
theorem hermiteModeFrequency_mono : Monotone hermiteModeFrequency := by
  intro m n hmn
  apply Real.sqrt_le_sqrt
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- At every damping, the ground mode realizes the slowest rate of the entire spectrum. -/
theorem hermite_scalarDecayRate_isLeast (d : ℝ) :
    IsLeast (Set.range (fun n : ℕ => scalarDecayRate d (hermiteModeFrequency n)))
      (scalarDecayRate d (hermiteModeFrequency 0)) := by
  refine ⟨⟨0, rfl⟩, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact scalarDecayRate_mono_frequency d
    (a := ⟨hermiteModeFrequency 0, hermiteModeFrequency_nonneg 0⟩)
    (b := ⟨hermiteModeFrequency n, hermiteModeFrequency_nonneg n⟩)
    (hermiteModeFrequency_mono (Nat.zero_le n))

/-- One damping choice optimizes the slowest rate and equalizes all modal rates. -/
theorem hermite_critical_damping_all_modes (n : ℕ) :
    scalarDecayRate (hermiteModeFrequency 0) (hermiteModeFrequency n) =
      hermiteModeFrequency 0 := by
  unfold scalarDecayRate
  rw [abs_of_nonneg (hermiteModeFrequency_nonneg 0),
    Real.sqrt_eq_zero_of_nonpos, sub_zero]
  rw [hermiteModeFrequency_sq, hermiteModeFrequency_sq]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith only [Real.pi_pos, mul_nonneg Real.pi_pos.le hn]

/-- The optimal worst-mode rate is attained at the ground frequency. -/
theorem hermite_optimal_worst_decay :
    IsGreatest (Set.range (fun d : ℝ => scalarDecayRate d (hermiteModeFrequency 0)))
      (hermiteModeFrequency 0) := by
  simpa only [abs_of_nonneg (hermiteModeFrequency_nonneg 0)] using
    scalarDecayRate_isGreatest (hermiteModeFrequency 0)

/-- A critically damped Hermite field solves the exact Hamiltonian wave equation. -/
theorem criticalHermiteMode_ode (n : ℕ) (A B t : ℝ) :
    (deriv (deriv (criticalScalarMode (hermiteModeFrequency n) A B)) t : ℂ) •
        hermiteSchwartz n +
      (2 * hermiteModeFrequency n : ℂ) •
        ((deriv (criticalScalarMode (hermiteModeFrequency n) A B) t : ℂ) •
          hermiteSchwartz n) +
      hamiltonianCLM ((criticalScalarMode (hermiteModeFrequency n) A B t : ℂ) •
        hermiteSchwartz n) = 0 := by
  have h := criticalScalarMode_ode (hermiteModeFrequency n) A B t
  rw [abs_of_nonneg (hermiteModeFrequency_nonneg n), hermiteModeFrequency_sq] at h
  rw [map_smul, hamiltonianCLM_hermiteSchwartz, smul_smul, smul_smul,
    ← add_smul, ← add_smul]
  have hc : (deriv (deriv (criticalScalarMode (hermiteModeFrequency n) A B)) t : ℂ) +
      (2 * hermiteModeFrequency n : ℂ) *
        (deriv (criticalScalarMode (hermiteModeFrequency n) A B) t : ℂ) +
      (criticalScalarMode (hermiteModeFrequency n) A B t : ℂ) *
        (2 * (Real.pi : ℂ) * (2 * n + 1)) = 0 := by
    exact_mod_cast (by linarith only [h] :
      deriv (deriv (criticalScalarMode (hermiteModeFrequency n) A B)) t +
        2 * hermiteModeFrequency n * deriv (criticalScalarMode (hermiteModeFrequency n) A B) t +
        criticalScalarMode (hermiteModeFrequency n) A B t *
          (2 * Real.pi * (2 * n + 1)) = 0)
  rw [hc, zero_smul]

#print axioms hermite_scalarDecayRate_isLeast
#print axioms hermite_critical_damping_all_modes
#print axioms hermite_optimal_worst_decay
#print axioms criticalHermiteMode_ode

end GaloisForLFunctions
