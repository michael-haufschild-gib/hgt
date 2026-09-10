import GaloisForLFunctions.HTGeometry.FisherQubitSchrodingerClock

/-!
# Sharp orthogonalization time for the Fisher qubit clock

The Mandelstam--Tamm value in arXiv:2605.03958, equation (30), is attained
by the actual qubit Schrödinger trajectory. The earliest nonnegative
orthogonalization time is proved as an `IsLeast` statement, with no
orthogonality or nonzero-energy assumption supplied to the theorem.
-/
open scoped InnerProductSpace
noncomputable section
namespace HTGeometry

/-- Exact first distinguishable orthogonal state on the positive-frequency trajectory. -/
theorem fisherQubitClock_orthogonal_at_pi (logFrequency phase : ℝ) :
    inner ℂ (fisherQubitClockState (Real.exp logFrequency) phase 0)
      (fisherQubitClockState (Real.exp logFrequency) phase
        (Real.pi / Real.exp logFrequency)) = 0 := by
  rw [fisherQubitClock_overlap]
  have he : Real.exp logFrequency * (Real.pi / Real.exp logFrequency - 0) / 2 =
      Real.pi / 2 := by
    field_simp
    ring
  rw [he, Real.cos_pi_div_two, Complex.ofReal_zero]

/-- No earlier nonnegative time reaches an orthogonal state. -/
theorem fisherQubitClock_first_orthogonal_time (logFrequency phase : ℝ) :
    IsLeast {t : ℝ | 0 ≤ t ∧
      inner ℂ (fisherQubitClockState (Real.exp logFrequency) phase 0)
        (fisherQubitClockState (Real.exp logFrequency) phase t) = 0}
      (Real.pi / Real.exp logFrequency) := by
  constructor
  · exact ⟨(div_pos Real.pi_pos (Real.exp_pos _)).le,
      fisherQubitClock_orthogonal_at_pi logFrequency phase⟩
  · intro t ht
    by_contra h
    have hlt : t < Real.pi / Real.exp logFrequency := lt_of_not_ge h
    have hangle : Real.exp logFrequency * t / 2 < Real.pi / 2 := by
      have hh := (lt_div_iff₀ (Real.exp_pos logFrequency)).mp hlt
      nlinarith
    have hlo : -(Real.pi / 2) < Real.exp logFrequency * t / 2 := by
      have hn := mul_nonneg (Real.exp_pos logFrequency).le ht.1
      linarith [Real.pi_pos]
    have hp := Real.cos_pos_of_mem_Ioo ⟨hlo, hangle⟩
    have hz := ht.2
    rw [fisherQubitClock_overlap, sub_zero, Complex.ofReal_eq_zero] at hz
    linarith

/-- The first orthogonal state consumes exactly pi units of Fisher distance. -/
theorem fisherQubitClock_orthogonal_fisher_cost (logFrequency phase : ℝ) :
    (∫ t : ℝ in 0..(Real.pi / Real.exp logFrequency),
      Real.sqrt (fisherQubitClockInformation (Real.exp logFrequency) phase t)) = Real.pi := by
  rw [fisherQubitClock_integral, sub_zero, abs_of_pos (Real.exp_pos _)]
  field_simp

/-- The actual Hamiltonian standard deviation saturates the time--energy product. -/
theorem fisherQubitClock_mandelstam_tamm_equality (logFrequency phase : ℝ) :
    (Real.pi / Real.exp logFrequency) *
      ‖fisherQubitHamiltonianAction (Real.exp logFrequency)
        (fisherQubitClockState (Real.exp logFrequency) phase 0)‖ = Real.pi / 2 := by
  have hs := fisherQubitClock_speed_energy (Real.exp logFrequency) phase 0
  rw [fisherQubitClock_speed, abs_of_pos (Real.exp_pos _)] at hs
  have he : ‖fisherQubitHamiltonianAction (Real.exp logFrequency)
      (fisherQubitClockState (Real.exp logFrequency) phase 0)‖ = Real.exp logFrequency / 2 := by
    linarith
  rw [he]
  field_simp

end HTGeometry
