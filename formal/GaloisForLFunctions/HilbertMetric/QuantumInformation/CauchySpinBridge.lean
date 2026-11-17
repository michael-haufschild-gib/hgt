import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyDephasing
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinInstrumentPinching

/-!
# Two-rate Cauchy dephasing as a spin channel

Common logarithmic shifts preserve the channel. In two dimensions its
Cauchy coherence is the exact multiplier of the two-Kraus spin filter,
equivalently a convex mixture of identity and Pauli phase flip.
-/

noncomputable section
open Matrix
open scoped ComplexConjugate
namespace GaloisForLFunctions.HilbertMetric.CauchyDephasing
open HTGeometry.SchafferExl

/-- Common logarithmic rate shifts leave all coherences unchanged. -/
theorem coherence_add_const (s t c : ℝ) :
    coherence (s + c) (t + c) = coherence s t := by
  rw [coherence_eq_cosh_inv, coherence_eq_cosh_inv]
  congr 2
  ring

/-- The normalized inverse Jordan channel depends only on rate differences. -/
theorem channel_add_const {n : ℕ} (r : Fin n → ℝ) (c : ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    channel (fun i => r i + c) A = channel r A := by
  ext i j
  simp only [channel, coherence_add_const]

/-- The Cauchy coherence is exactly the multiplier of a positive spin filter. -/
theorem spinFilterCoherence_exp (s t : ℝ) :
    spinFilterCoherence (Real.exp ((s - t) / 2) : ℂ) = coherence s t := by
  rw [spinFilterCoherence_eq, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), coherence_eq_cosh_inv, Real.cosh_eq, Real.exp_neg]
  field_simp [Real.exp_ne_zero] <;> ring

/-- Two-rate Cauchy dephasing is the existing explicit two-Kraus spin channel. -/
theorem two_rate_channel_eq_spinFilter (s t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    channel ![s, t] A =
      (spinFilterChannel (Real.exp ((s - t) / 2) : ℂ)).evolveMatrix A := by
  rw [spinFilterChannel_entries, spinFilterCoherence_exp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [channel, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      coherence_self, coherence_symm t s, Complex.ofReal_one, one_mul]

/-- The two-rate channel is an exact mixture of identity and Pauli phase flip. -/
theorem two_rate_channel_phaseFlip (s t : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    channel ![s, t] A = (((1 + coherence s t) / 2 : ℝ) : ℂ) • A +
      (((1 - coherence s t) / 2 : ℝ) : ℂ) •
        (QuantumAlg.pauliZ * A * QuantumAlg.pauliZ) := by
  rw [two_rate_channel_eq_spinFilter, spinFilterChannel_phaseFlip]
  simp only [spinFilterIdentityWeight, spinFilterPhaseFlipWeight, spinFilterCoherence_exp]

#print axioms channel_add_const
#print axioms spinFilterCoherence_exp
#print axioms two_rate_channel_eq_spinFilter
#print axioms two_rate_channel_phaseFlip
end GaloisForLFunctions.HilbertMetric.CauchyDephasing
