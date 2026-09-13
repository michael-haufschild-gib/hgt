import GaloisForLFunctions.HTGeometry.QuantumBilinearNullActivation
import GaloisForLFunctions.HTGeometry.QuantumNullSpaceTransport

/-!
# Normalized pure-state infidelity and null activation

The denominator-normalized infidelity of arXiv:2609.07645 is defined on arbitrary
Hilbert-space vectors, proved invariant under independent nonzero complex rescalings,
and evaluated on the corpus's exact qubit curve. There it equals both squared angular
sine and rotating-null activation energy.
-/

set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Squared overlap normalized by both vector masses. Lean totalizes zero denominators. -/
def normalizedPureStateFidelity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u v : E) : ℝ :=
  ‖inner ℂ u v‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2)

/-- Paper's projective infidelity. -/
def normalizedPureStateInfidelity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (u v : E) : ℝ :=
  1 - normalizedPureStateFidelity u v

/-- Exact qubit-state overlap along the corpus's normalized real-amplitude curve. -/
theorem qgtQubitState_inner (s t : ℝ) :
    inner ℂ (HTGeometry.qgtQubitState s) (HTGeometry.qgtQubitState t) =
      (Real.cos (t - s) : ℂ) := by
  unfold HTGeometry.qgtQubitState
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    RCLike.inner_apply, Complex.conj_ofReal]
  norm_cast
  rw [Real.cos_sub]

theorem qgtQubit_normalizedPureStateFidelity (s t : ℝ) :
    normalizedPureStateFidelity (HTGeometry.qgtQubitState s) (HTGeometry.qgtQubitState t) =
      Real.cos (t - s) ^ 2 := by
  unfold normalizedPureStateFidelity
  rw [qgtQubitState_inner, HTGeometry.qgtQubitState_norm_sq,
    HTGeometry.qgtQubitState_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, one_mul, div_one]

theorem qgtQubit_normalizedPureStateInfidelity (s t : ℝ) :
    normalizedPureStateInfidelity (HTGeometry.qgtQubitState s) (HTGeometry.qgtQubitState t) =
      Real.sin (t - s) ^ 2 := by
  rw [normalizedPureStateInfidelity, qgtQubit_normalizedPureStateFidelity]
  nlinarith [Real.sin_sq_add_cos_sq (t - s)]

/-- Infidelity of the qubit curve is exactly the rotating-panel null activation. -/
theorem qgtQubit_infidelity_eq_null_activation (s t : ℝ) :
    normalizedPureStateInfidelity (HTGeometry.qgtQubitState s) (HTGeometry.qgtQubitState t) =
      ‖HTGeometry.rotatingObservation t (HTGeometry.rotatingNullDirection s)‖ ^ 2 := by
  rw [qgtQubit_normalizedPureStateInfidelity, HTGeometry.rotatingObservation_null_energy]

set_option maxHeartbeats 800000 in
/-- Normalized fidelity is invariant under independent projective rescalings. -/
theorem normalizedPureStateFidelity_smul_units
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c d : ℂˣ) (u v : E) :
    normalizedPureStateFidelity ((c : ℂ) • u) ((d : ℂ) • v) =
      normalizedPureStateFidelity u v := by
  unfold normalizedPureStateFidelity
  simp only [inner_smul_left, inner_smul_right, norm_mul, norm_smul]
  rw [starRingEnd_apply, norm_star]
  have hc : ‖(c : ℂ)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (Units.norm_pos c))
  have hd : ‖(d : ℂ)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt (Units.norm_pos d))
  calc
    (‖(d : ℂ)‖ * (‖(c : ℂ)‖ * ‖inner ℂ u v‖)) ^ 2 /
        ((‖(c : ℂ)‖ * ‖u‖) ^ 2 * (‖(d : ℂ)‖ * ‖v‖) ^ 2) =
      (‖(c : ℂ)‖ ^ 2 * ‖(d : ℂ)‖ ^ 2) * ‖inner ℂ u v‖ ^ 2 /
        ((‖(c : ℂ)‖ ^ 2 * ‖(d : ℂ)‖ ^ 2) * (‖u‖ ^ 2 * ‖v‖ ^ 2)) := by
          congr 1 <;> ring
    _ = ‖inner ℂ u v‖ ^ 2 / (‖u‖ ^ 2 * ‖v‖ ^ 2) :=
      mul_div_mul_left _ _ (mul_ne_zero hc hd)

/-- Normalized infidelity inherits projective rescaling invariance. -/
theorem normalizedPureStateInfidelity_smul_units
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (c d : ℂˣ) (u v : E) :
    normalizedPureStateInfidelity ((c : ℂ) • u) ((d : ℂ) • v) =
      normalizedPureStateInfidelity u v := by
  simp [normalizedPureStateInfidelity, normalizedPureStateFidelity_smul_units]

end
end GaloisForLFunctions.HTGeometry
