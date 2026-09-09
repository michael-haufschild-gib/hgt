import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinInstrument
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinProjectiveMetric
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinPinching

/-!
# Forgotten spin-filter outcomes, phase-flip mixtures, and exact pinching

Application of Schaffer–Exl, arXiv:2609.04530, through the constructed conditional
spin instrument and the corpus's existing two-outcome pinching. The complete Kraus
channel has a real coherence multiplier with absolute value at most one, and is an
explicit convex mixture of identity and Pauli phase flip. Its measured populations
are invariant. Under constructed positive damping it converges, on every input
matrix, to the existing Z pinching rather than the selected conditional trajectory.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Real coherence multiplier when the explicit two-outcome instrument is not conditioned. -/
def spinFilterCoherence (k : ℂ) : ℝ := 2 * spinChartScale k ^ 2 * k.re

/-- Rational form of the complete channel's exact coherence multiplier. -/
theorem spinFilterCoherence_eq (k : ℂ) :
    spinFilterCoherence k = 2 * k.re / (1 + ‖k‖ ^ 2) := by
  rw [spinFilterCoherence, spinChartScale_sq]
  ring

/-- Exact matrix action on arbitrary inputs, preserving populations and scaling coherences. -/
theorem spinFilterChannel_entries (k : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinFilterChannel k).evolveMatrix ρ =
      !![ρ 0 0, (spinFilterCoherence k : ℂ) * ρ 0 1;
        (spinFilterCoherence k : ℂ) * ρ 1 0, ρ 1 1] := by
  have hc := spinChartScale_complex_identity k
  have hr : (k.re : ℂ) * 2 = k + conj k := by
    apply Complex.ext <;> simp
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [FiniteRectangularKrausChannel.evolveMatrix, spinFilterChannel, Fin.sum_univ_two,
      spinFilterSelected, spinFilterComplement, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      spinFilterCoherence]
  · linear_combination ρ 0 0 * hc
  · linear_combination -(spinChartScale k : ℂ) ^ 2 * ρ 0 1 * hr
  · linear_combination -(spinChartScale k : ℂ) ^ 2 * ρ 1 0 * hr
  · linear_combination ρ 1 1 * hc

/-- The complete channel is an exact affine interpolation of identity and the corpus's pinching. -/
theorem spinFilterChannel_dephasing (k : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinFilterChannel k).evolveMatrix ρ =
      (spinFilterCoherence k : ℂ) • ρ + (1 - (spinFilterCoherence k : ℂ)) • spinZPinch ρ := by
  rw [spinFilterChannel_entries, spinZPinch_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> ring

/-- Complete positivity has an explicit scalar boundary: the coherence lies in the unit interval in absolute value. -/
theorem spinFilterCoherence_abs_le_one (k : ℂ) : |spinFilterCoherence k| ≤ 1 := by
  rw [spinFilterCoherence_eq, abs_le]
  have hd : 0 < 1 + ‖k‖ ^ 2 := by positivity
  have hn : k.re ^ 2 + k.im ^ 2 = ‖k‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq k
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (k.re + 1), sq_nonneg k.im]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (k.re - 1), sq_nonneg k.im]

/-- Explicit weights for identity and Pauli phase flip. -/
def spinFilterIdentityWeight (k : ℂ) : ℝ := (1 + spinFilterCoherence k) / 2

def spinFilterPhaseFlipWeight (k : ℂ) : ℝ := (1 - spinFilterCoherence k) / 2

/-- Both phase-flip mixture weights are nonnegative and exactly normalized. -/
theorem spinFilterPhaseFlip_weights (k : ℂ) :
    0 ≤ spinFilterIdentityWeight k ∧ 0 ≤ spinFilterPhaseFlipWeight k ∧
      spinFilterIdentityWeight k + spinFilterPhaseFlipWeight k = 1 := by
  have h := abs_le.mp (spinFilterCoherence_abs_le_one k)
  unfold spinFilterIdentityWeight spinFilterPhaseFlipWeight
  constructor
  · linarith [h.1]
  constructor
  · linarith [h.2]
  · ring

/-- Forgetting the selected outcome gives an actual convex mixture of two fixed unitary conjugations. -/
theorem spinFilterChannel_phaseFlip (k : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinFilterChannel k).evolveMatrix ρ =
      (spinFilterIdentityWeight k : ℂ) • ρ +
        (spinFilterPhaseFlipWeight k : ℂ) • (QuantumAlg.pauliZ * ρ * QuantumAlg.pauliZ) := by
  rw [spinFilterChannel_entries]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinFilterIdentityWeight, spinFilterPhaseFlipWeight, QuantumAlg.pauliZ,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.smul_apply] <;> ring

/-- The complete channel preserves the existing measured state at every time and multiplier. -/
theorem spinFilterChannel_pinch_invariant (k : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    spinZPinch ((spinFilterChannel k).evolveMatrix ρ) = spinZPinch ρ := by
  rw [spinFilterChannel_entries, spinZPinch_entries, spinZPinch_entries]
  simp

/-- Positive damping removes the complete channel's coherence multiplier. -/
theorem spinFilterCoherence_flow_tendsto_zero (s : ℝ) :
    Tendsto (fun t : ℝ => spinFilterCoherence
      (Complex.exp (spinPlaneRate (Real.exp s) * (t : ℂ)))) atTop (nhds 0) := by
  have he : Tendsto (fun t : ℝ => Complex.exp (spinPlaneRate (Real.exp s) * (t : ℂ)))
      atTop (nhds 0) := by
    have h := spinPlaneFlow_positive_tendsto_zero s 1
    unfold spinPlaneFlow at h
    simpa only [mul_one] using h
  have hr := Complex.continuous_re.continuousAt.tendsto.comp he
  have hd : Tendsto (fun t : ℝ => 1 +
      ‖Complex.exp (spinPlaneRate (Real.exp s) * (t : ℂ))‖ ^ 2) atTop (nhds 1) := by
    simpa using (he.norm.pow 2).const_add 1
  have h := (hr.const_mul 2).div hd one_ne_zero
  convert h using 1
  · funext t
    rw [spinFilterCoherence_eq]
    rfl
  · simp

/-- With outcomes forgotten, the same instrument converges to the existing Z pinching of every input. -/
theorem spinFilterChannel_flow_tendsto_pinch (s : ℝ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    Tendsto (fun t : ℝ =>
      (spinFilterChannel (Complex.exp (spinPlaneRate (Real.exp s) * (t : ℂ)))).evolveMatrix ρ)
      atTop (nhds (spinZPinch ρ)) := by
  have hq := (spinFilterCoherence_flow_tendsto_zero s).ofReal
  have h := (hq.smul (tendsto_const_nhds (x := ρ))).add
    (((tendsto_const_nhds (x := (1 : ℂ))).sub hq).smul (tendsto_const_nhds (x := spinZPinch ρ)))
  simpa only [spinFilterChannel_dephasing, Complex.ofReal_zero, zero_smul, sub_zero,
    one_smul, zero_add] using h

end
end GaloisForLFunctions.HTGeometry.SchafferExl
