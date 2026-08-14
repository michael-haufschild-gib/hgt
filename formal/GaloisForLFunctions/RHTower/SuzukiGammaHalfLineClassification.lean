import GaloisForLFunctions.HTGeometry.FrequencyPropagator
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Classification of homogeneous Gamma solutions on a frequency half-line

On a positive frequency half-line the Gamma equation in logarithmic normal form reads

`f' = [-1/(2η) + (i/2)(r(η) I - T)] f`,

whose coefficient is the logarithmic derivative of `η^{-1/2}Q(η)` for the Gamma transport
`Q(η) = exp((i/2)∫₀^η r) exp(-iηT/2)`.  Consequently every solution is `η^{-1/2}Q(η)c` for a single
channel vector `c`, and the channel vector is unique.  The proof is the exact integrating factor:
`η^{1/2}Q(η)^{-1}f(η)` has vanishing derivative, so it is constant on the connected half-line.
-/

open Complex Set

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The Gamma transport `Q(η) = exp((i/2)∫₀^η r) exp(-iηT/2)`, the zero-frequency propagator. -/
def gammaTransport (Rint : ℝ → ℝ) (T : X →L[ℂ] X) (η : ℝ) : X →L[ℂ] X :=
  freqPropagator 0 Rint T η

/-- The inverse Gamma transport. -/
def gammaTransportInv (Rint : ℝ → ℝ) (T : X →L[ℂ] X) (η : ℝ) : X →L[ℂ] X :=
  freqPropagator 0 (fun x => -Rint x) (-T) η

variable {Rint : ℝ → ℝ} {T : X →L[ℂ] X}

theorem gammaTransport_mul_inv (η : ℝ) :
    gammaTransport Rint T η * gammaTransportInv Rint T η = 1 := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  rw [gammaTransport, gammaTransportInv, freqPropagator, freqPropagator, smul_mul_smul_comm]
  have hscal : gammaPhase 0 Rint η * gammaPhase 0 (fun x => -Rint x) η = 1 := by
    rw [gammaPhase, gammaPhase, ← Complex.exp_add]
    have h : ((η * 0 + Rint η / 2 : ℝ) : ℂ) * I + ((η * 0 + -Rint η / 2 : ℝ) : ℂ) * I = 0 := by
      push_cast; ring
    rw [h, Complex.exp_zero]
  have hop : opPhase T η * opPhase (-T) η = 1 := by
    have hneg : opPhase (-T) η = NormedSpace.exp (-(η • ((-I / 2 : ℂ) • T))) := by
      rw [opPhase, smul_neg, smul_neg]
    rw [opPhase, hneg, ← NormedSpace.exp_add_of_commute ((Commute.refl _).neg_right),
      add_neg_cancel, NormedSpace.exp_zero]
  rw [hscal, hop, one_smul]

theorem gammaTransportInv_mul (η : ℝ) :
    gammaTransportInv Rint T η * gammaTransport Rint T η = 1 := by
  letI : NormedAlgebra ℚ (X →L[ℂ] X) := .restrictScalars ℚ ℂ _
  rw [gammaTransport, gammaTransportInv, freqPropagator, freqPropagator, smul_mul_smul_comm]
  have hscal : gammaPhase 0 (fun x => -Rint x) η * gammaPhase 0 Rint η = 1 := by
    rw [gammaPhase, gammaPhase, ← Complex.exp_add]
    have h : ((η * 0 + -Rint η / 2 : ℝ) : ℂ) * I + ((η * 0 + Rint η / 2 : ℝ) : ℂ) * I = 0 := by
      push_cast; ring
    rw [h, Complex.exp_zero]
  have hop : opPhase (-T) η * opPhase T η = 1 := by
    have hneg : opPhase (-T) η = NormedSpace.exp (-(η • ((-I / 2 : ℂ) • T))) := by
      rw [opPhase, smul_neg, smul_neg]
    have hcomm : Commute (-(η • ((-I / 2 : ℂ) • T))) (η • ((-I / 2 : ℂ) • T)) :=
      (Commute.refl _).neg_left
    rw [hneg, opPhase, ← NormedSpace.exp_add_of_commute hcomm, neg_add_cancel,
      NormedSpace.exp_zero]
  rw [hscal, hop, one_smul]

@[simp] theorem gammaTransport_apply_inv_apply (η : ℝ) (v : X) :
    gammaTransport Rint T η (gammaTransportInv Rint T η v) = v := by
  have h := gammaTransport_mul_inv (Rint := Rint) (T := T) η
  have := congrArg (fun S : X →L[ℂ] X => S v) h
  simpa using this

omit [CompleteSpace X] in
/-- The transported symbol commutes with the inverse transport. -/
theorem commute_shiftedSymbolOp_gammaTransportInv (c : ℝ) (η : ℝ) :
    shiftedSymbolOp c T * gammaTransportInv Rint T η
      = gammaTransportInv Rint T η * shiftedSymbolOp c T := by
  have hT : Commute T (opPhase (-T) η) := by
    have h := (commute_opPhase (-T) η).neg_left
    rwa [neg_neg] at h
  have hB : Commute (shiftedSymbolOp c T) (opPhase (-T) η) := by
    rw [shiftedSymbolOp]
    exact ((Commute.one_left _).smul_left _).sub_left (hT.smul_left _)
  have hfull : Commute (shiftedSymbolOp c T) (gammaTransportInv Rint T η) := by
    rw [gammaTransportInv, freqPropagator]
    exact hB.smul_right _
  exact hfull

/-- The inverse transport solves the adjoint transport equation. -/
theorem hasDerivAt_gammaTransportInv {r : ℝ → ℝ} {η : ℝ} (hRint : HasDerivAt Rint (r η) η) :
    HasDerivAt (gammaTransportInv Rint T)
      (-(I • (shiftedSymbolOp (r η / 2) T * gammaTransportInv Rint T η))) η := by
  have h := hasDerivAt_freqPropagator (L := 0) (Rint := fun x => -Rint x) (r := fun x => -r x)
    (η := η) (-T) hRint.neg
  have hop : shiftedSymbolOp (0 + -r η / 2) (-T) = -shiftedSymbolOp (r η / 2) T := by
    rw [shiftedSymbolOp, shiftedSymbolOp, zero_add, smul_neg, sub_neg_eq_add, neg_sub]
    have hc : (((-r η / 2 : ℝ)) : ℂ) = -(((r η / 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [hc, neg_smul]
    abel
  rw [hop] at h
  have hval : I • (-shiftedSymbolOp (r η / 2) T * freqPropagator 0 (fun x => -Rint x) (-T) η)
      = -(I • (shiftedSymbolOp (r η / 2) T
          * freqPropagator 0 (fun x => -Rint x) (-T) η)) := by
    rw [neg_mul, smul_neg]
  rw [hval] at h
  exact h

end

end GaloisForLFunctions.RHTower
