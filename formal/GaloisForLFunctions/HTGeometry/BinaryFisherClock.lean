import GaloisForLFunctions.HTGeometry.ResponsePolarizationBinaryWitness

/-!
# A finite-budget Fisher clock with an unbounded calibrated reading

The binary escort curve already has an exact Fisher antiderivative. Applying
arXiv:2605.03958, equations (6) and (12), gives an injective clock on a bounded
interval, an exact logarithmic calibration, and a diverging calibration gain.
-/

open Filter Topology
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Clock reading reconstructed from the binary Fisher coordinate. -/
def binaryFisherClockReadout (s : ℝ) : ℝ := 2 * Real.log (Real.tan (s / 2))

/-- The complete real statistical parameter fits strictly inside a finite clock interval. -/
theorem binaryFisherClock_bounds (t : ℝ) :
    0 < binaryFisherCoordinate t ∧ binaryFisherCoordinate t < Real.pi := by
  constructor
  · unfold binaryFisherCoordinate
    exact mul_pos (by norm_num) (Real.arctan_pos.mpr (Real.exp_pos _))
  · unfold binaryFisherCoordinate
    linarith [Real.arctan_lt_pi_div_two (Real.exp (t / 2))]

theorem binaryFisherClock_strictMono : StrictMono binaryFisherCoordinate := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_binaryFisherCoordinate t).deriv]
  positivity

/-- Finite accumulated distinguishability still admits exact recovery of every finite label. -/
theorem binaryFisherClock_calibration (t : ℝ) :
    binaryFisherClockReadout (binaryFisherCoordinate t) = t := by
  unfold binaryFisherClockReadout binaryFisherCoordinate
  rw [show 2 * Real.arctan (Real.exp (t / 2)) / 2 = Real.arctan (Real.exp (t / 2)) by ring,
    Real.tan_arctan, Real.log_exp]
  ring

/-- The accumulated arc from any chosen origin reconstructs the original parameter. -/
theorem binaryFisherClock_integrated_calibration (a t : ℝ) :
    binaryFisherClockReadout (binaryFisherCoordinate a +
      ∫ s : ℝ in a..t, Real.sqrt (finiteTiltVariance binaryEscortWeight binaryEscortScore s)) = t := by
  rw [binary_fisher_interval]
  convert binaryFisherClock_calibration t using 1
  congr 1
  ring

/-- A bounded Fisher clock cannot have every real number as its raw reading. -/
theorem binaryFisherClock_not_surjective : ¬ Function.Surjective binaryFisherCoordinate := by
  intro h
  obtain ⟨t, ht⟩ := h 0
  have hp := (binaryFisherClock_bounds t).1
  rw [ht] at hp
  exact (lt_irrefl 0) hp

/-- Calibration becomes unbounded while its input approaches the finite Fisher endpoint. -/
theorem binaryFisherClock_calibrated_tendsto :
    Tendsto (fun t => binaryFisherClockReadout (binaryFisherCoordinate t)) atTop atTop := by
  simp only [binaryFisherClock_calibration]
  exact tendsto_id

/-- Exact local gain needed to convert distinguishability back to parameter change. -/
theorem binaryFisherClock_reciprocal_speed (t : ℝ) :
    (Real.sqrt (finiteTiltVariance binaryEscortWeight binaryEscortScore t))⁻¹ =
      2 * Real.cosh (t / 2) := by
  rw [binary_sqrt_variance, Real.cosh_eq, Real.exp_neg]
  have he : Real.exp t = Real.exp (t / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he]
  field_simp
  ring

/-- Constant finite gain cannot decode the whole bounded Fisher interval. -/
theorem binaryFisherClock_no_affine_calibration :
    ¬ ∃ A B : ℝ, ∀ t : ℝ, A * binaryFisherCoordinate t + B = t := by
  rintro ⟨A, B, h⟩
  have hlim : Tendsto (fun t : ℝ => A * binaryFisherCoordinate t + B) atTop
      (𝓝 (A * Real.pi + B)) :=
    (binaryFisherCoordinate_tendsto_atTop.const_mul A).add_const B
  have hid : (fun t : ℝ => A * binaryFisherCoordinate t + B) = id := funext h
  rw [hid] at hlim
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_id (A * Real.pi + B) hlim

end GaloisForLFunctions.HTGeometry
