import GaloisForLFunctions.HTGeometry.ClockTwoSpeciesConformalTime
import GaloisForLFunctions.HTGeometry.ClockSlabProbe

/-!
# Quadratic inflation superpotential and conformal clock realization

The quadratic ansatz of arXiv:2609.02912, equation (2) and §4, generates a
quartic scalar potential, not a quadratic one. Its square completion gives
an unconditional lower bound. Independently, the same explicit quadratic
function can be used as the exponent of the corpus's cosmological conformal
chart; its clock potential and species recovery are then exact.
-/

open scoped ContDiff
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The paper's quadratic superpotential. -/
def inflationQuadraticW (m phi : ℝ) : ℝ := m ^ 2 * phi ^ 2 / 2

/-- Potential generated from the superpotential and its actual derivative. -/
def inflationReconstructedPotential (C kappa : ℝ) (W : ℝ → ℝ) (phi : ℝ) : ℝ :=
  C ^ 2 / kappa ^ 4 * (3 * kappa ^ 2 * W phi ^ 2 - 2 * deriv W phi ^ 2)

theorem hasDerivAt_inflationQuadraticW (m phi : ℝ) :
    HasDerivAt (inflationQuadraticW m) (m ^ 2 * phi) phi := by
  have h := (((hasDerivAt_id phi).pow 2).const_mul (m ^ 2)).div_const 2
  exact h.congr_deriv (by dsimp; ring)

theorem hasDerivAt_deriv_inflationQuadraticW (m phi : ℝ) :
    HasDerivAt (deriv (inflationQuadraticW m)) (m ^ 2) phi := by
  have h : deriv (inflationQuadraticW m) = fun phi => m ^ 2 * phi :=
    funext fun phi => (hasDerivAt_inflationQuadraticW m phi).deriv
  rw [h]
  simpa using (hasDerivAt_id phi).const_mul (m ^ 2)

/-- The generated scalar potential is exactly quartic minus quadratic. -/
theorem inflationReconstructedPotential_quadratic (C kappa m phi : ℝ) :
    inflationReconstructedPotential C kappa (inflationQuadraticW m) phi =
      C ^ 2 * m ^ 4 / kappa ^ 4 * (3 * kappa ^ 2 * phi ^ 4 / 4 - 2 * phi ^ 2) := by
  unfold inflationReconstructedPotential
  rw [(hasDerivAt_inflationQuadraticW m phi).deriv]
  unfold inflationQuadraticW
  ring

/-- Exact square completion; the identity even covers Lean's zero-coupling value. -/
theorem inflationReconstructedPotential_square_completion (C kappa m phi : ℝ) :
    inflationReconstructedPotential C kappa (inflationQuadraticW m) phi +
      4 * C ^ 2 * m ^ 4 / (3 * kappa ^ 6) =
        3 * C ^ 2 * m ^ 4 / (4 * kappa ^ 2) * (phi ^ 2 - 4 / (3 * kappa ^ 2)) ^ 2 := by
  rw [inflationReconstructedPotential_quadratic]
  by_cases hk : kappa = 0
  · simp [hk]
  · field_simp
    ring

/-- A global lower bound follows from the nonnegative square remainder. -/
theorem inflationReconstructedPotential_lower_bound (C kappa m phi : ℝ) :
    -(4 * C ^ 2 * m ^ 4 / (3 * kappa ^ 6)) ≤
      inflationReconstructedPotential C kappa (inflationQuadraticW m) phi := by
  have h := inflationReconstructedPotential_square_completion C kappa m phi
  have hn : 0 ≤ 3 * C ^ 2 * m ^ 4 / (4 * kappa ^ 2) *
      (phi ^ 2 - 4 / (3 * kappa ^ 2)) ^ 2 := by positivity
  linarith

/-- Sign is unchanged under reflection of the inflaton field. -/
theorem inflationReconstructedPotential_even (C kappa m phi : ℝ) :
    inflationReconstructedPotential C kappa (inflationQuadraticW m) (-phi) =
      inflationReconstructedPotential C kappa (inflationQuadraticW m) phi := by
  rw [inflationReconstructedPotential_quadratic, inflationReconstructedPotential_quadratic]
  ring

/-- The ansatz is a globally smooth conformal exponent. -/
theorem contDiff_inflationQuadraticW (m : ℝ) : ContDiff ℝ ∞ (inflationQuadraticW m) := by
  unfold inflationQuadraticW
  fun_prop

/-- Closed conformal-time clock potential for the same quadratic profile. -/
theorem conformalTimePotential_inflationQuadraticW (a massSq m t : ℝ) :
    conformalTimePotential (-1) a massSq (inflationQuadraticW m) t =
      massSq * Real.exp (m ^ 2 * t ^ 2) + a * m ^ 2 + a ^ 2 * m ^ 4 * t ^ 2 := by
  unfold conformalTimePotential
  rw [(hasDerivAt_inflationQuadraticW m t).deriv,
    (hasDerivAt_deriv_inflationQuadraticW m t).deriv]
  unfold inflationQuadraticW
  rw [show 2 * (m ^ 2 * t ^ 2 / 2) = m ^ 2 * t ^ 2 by ring]
  ring

/-- Two calibrated clock species recover the Gaussian-type conformal scale exactly. -/
theorem inflationQuadraticW_two_species_recovery (a massSq m t : ℝ) :
    conformalTimePotential (-1) a (massSq + 1) (inflationQuadraticW m) t -
      conformalTimePotential (-1) a massSq (inflationQuadraticW m) t =
        Real.exp (m ^ 2 * t ^ 2) := by
  rw [conformalTimePotential_inflationQuadraticW, conformalTimePotential_inflationQuadraticW]
  ring

/-- Every squared-mass clock has nonnegative potential at conformal weight one. -/
theorem inflationQuadraticW_clock_nonnegative (mass m t : ℝ) :
    0 ≤ conformalTimePotential (-1) 1 (mass ^ 2) (inflationQuadraticW m) t := by
  rw [conformalTimePotential_inflationQuadraticW]
  positivity

/-- The same formula is realized by the actual Lorentz metric chart, in every dimension. -/
theorem inflationQuadraticW_actual_metric_chart (n : ℕ) (a massSq m : ℝ)
    (x : Fin (n + 2) → ℝ) :
    (SmoothPseudoMetric.ofSignature (slabEps n) (slabEps_ne_zero n)).chart.conformalPotential
      a massSq (timeLift (inflationQuadraticW m)) x =
        massSq * Real.exp (m ^ 2 * (x 0) ^ 2) + a * m ^ 2 + a ^ 2 * m ^ 4 * (x 0) ^ 2 := by
  rw [conformalPotential_timeLift (slabEps n) (slabEps_ne_zero n)
    (contDiff_inflationQuadraticW m), slabEps_zero]
  norm_num only [inv_neg, inv_one]
  exact conformalTimePotential_inflationQuadraticW a massSq m (x 0)

end GaloisForLFunctions.HTGeometry
