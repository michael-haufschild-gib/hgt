import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.PowerTransfer
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.TraceObstruction
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.DyadicTrace

/-! # Temperature-dependent upper bounds from the ordinary fourth trace -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- Squared occupation response calibrated by the fourth trace of the propagator. -/
def fourthTraceExponent : GibbsExponent := ⟨2,show (0:ℝ) < 2 by norm_num⟩

theorem reading_at_two {r : ℕ} (b : SpectralBand r) (β : GibbsExponent) (he : β.val = 2) :
    relativeReading (powerResponse β) b = relativeReading quadraticResponse b := by
  simp only [relativeReading,spectralDrop,powerResponse,he,Real.rpow_two,quadraticResponse]

theorem traceLoss_nonneg {r : ℕ} (P : Projection) (hd : MissingDimension P r) (hc : Conserving (projected P)) :
    0 ≤ traceLoss (projected P) := by
  rw [← quadratic_physicalReading P hd hc]
  exact (relativeReading_bounds _ _).1

/-- At real part σ between zero and two, the power 2/σ controls the entire complex readout. -/
theorem matched_trace_control (r : ℕ) {z : ℂ} (hz : 0 < z.re) (h₂ : z.re ≤ 2) :
    traceControlsAt r z (2/z.re) ((‖z‖/z.re)^(2/z.re) * (r:ℝ)^(2/z.re-1)) := by
  let β : GibbsExponent := ⟨z.re,hz⟩
  let q : Ici (1:ℝ) := ⟨2/z.re,show 1 ≤ 2/z.re from (one_le_div hz).mpr h₂⟩
  have hs : (scaledExponent β q).val = 2 := by
    change z.re*(2/z.re) = 2
    rw [mul_comm,div_mul_cancel₀ _ hz.ne']
  intro P hd hc
  let b := physicalSpectrum P hd hc
  have hcost := detector_power_transfer β q (hotEdge r) b
  rw [reference_error_eq_reading,reference_error_eq_reading,reading_at_two b _ hs] at hcost
  have hb : relativeReading quadraticResponse b = traceLoss (projected P) := quadratic_physicalReading P hd hc
  rw [hb] at hcost
  have h := Real.rpow_le_rpow (norm_nonneg _) (relativePartition_norm_le b β le_rfl) (zero_le_one.trans q.property)
  have hf : 0 ≤ ‖z‖/β.val := div_nonneg (norm_nonneg _) hz.le
  rw [Real.mul_rpow hf (relativeReading_bounds _ b).1] at h
  exact (h.trans (mul_le_mul_of_nonneg_left hcost (Real.rpow_nonneg hf _))).trans_eq (mul_assoc _ _ _).symm

/-- At and beyond inverse temperature two the complex readout is Lipschitz in the trace deficit. -/
theorem linear_trace_control (r : ℕ) {z : ℂ} (hz : 2 ≤ z.re) : traceControlsAt r z 1 (‖z‖/2) := by
  intro P hd hc
  let b := physicalSpectrum P hd hc
  have h := relativePartition_norm_le b fourthTraceExponent hz
  rw [reading_at_two b _ rfl,show relativeReading quadraticResponse b = traceLoss (projected P)
    from quadratic_physicalReading P hd hc] at h
  rw [Real.rpow_one]
  exact h

/-- Uniform boundedness at fixed rank raises an admissible positive power to every larger power. -/
theorem trace_control_raise {r : ℕ} {z : ℂ} (hz : 0 < z.re) {p q K : ℝ}
    (hp : 0 < p) (hq : p ≤ q) (h : traceControlsAt r z p K) : ∃ C : ℝ, traceControlsAt r z q C := by
  let β : GibbsExponent := ⟨z.re,hz⟩
  let B := ‖z‖/β.val * relativeHead (powerResponse β) r
  refine ⟨B^(q-p)*K,?_⟩
  intro P hd hc
  let b := physicalSpectrum P hd hc
  let X := ‖relativePartition b z‖
  have hx : 0 ≤ X := norm_nonneg _
  have hB : X ≤ B := (relativePartition_norm_le b β le_rfl).trans
    (mul_le_mul_of_nonneg_left (relativeReading_bounds _ b).2 (div_nonneg (norm_nonneg _) hz.le))
  have hsplit : X^q = X^(q-p)*X^p := by
    by_cases h₀ : X = 0
    · rw [h₀,Real.zero_rpow (hp.trans_le hq).ne',Real.zero_rpow hp.ne',mul_zero]
    · rw [← Real.rpow_add (lt_of_le_of_ne hx (Ne.symm h₀)),sub_add_cancel]
  change X^q ≤ _
  rw [hsplit,mul_assoc]
  exact mul_le_mul (Real.rpow_le_rpow hx hB (sub_nonneg.mpr hq)) (h P hd hc)
    (Real.rpow_nonneg hx _) (Real.rpow_nonneg (hx.trans hB) _)

#print axioms matched_trace_control
#print axioms linear_trace_control
#print axioms trace_control_raise

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
