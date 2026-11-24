import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.ModeMargin.Growth

/-! # Doubly exponential growth of the derivative phase horizon -/
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- A fixed power of the Hilbert dimension bounds the base-two logarithm of
the phase-filling time, uniformly in the chain length. -/
theorem derivativePhaseHorizon_double_upper :
    ∃ c : ℕ, ∀ k : ℕ, derivativePhaseHorizon k ≤ (2:ℝ)^((2^(k+3):ℕ)^c) := by
  let D (k : ℕ) := 2^(k+3)
  let S (k : ℕ) := phaseClockModes (prefixPhaseEnergyEquiv k) (1/80)
  let F (k : ℕ) := nonconstantPacketIndexSet (phaseCubeFourierCutoff (D k-1) (1/80)) (D k-1)
  have h := LogPolynomialInDimension.twoPow ((PolynomialInDimension.const 128).mul PolynomialInDimension.dim.square)
  have hcount (k : ℕ) := fixed_radius_phase_packet_envelope (D := D k) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide : (2:ℕ) ≠ 0)))
    (prefixPhaseEnergyEquiv k)
  have hF := h.mono (f := fun k => ((F k).card : ℝ)) (fun _ => Nat.cast_nonneg _) (fun k => by exact_mod_cast (hcount k).1)
  have hS := h.mono (f := fun k => ((S k).card : ℝ)) (fun _ => Nat.cast_nonneg _) (fun k => by exact_mod_cast (hcount k).2.1)
  have hG := ((LogPolynomialInDimension.const 8).mul (hF.add (LogPolynomialInDimension.const 1))).mul
    (inverse_margin_log_polynomial (fun k => (S k).card) hS)
  apply LogPolynomialInDimension.bound
  change LogPolynomialInDimension (fun k => 8*(((F k).card:ℝ)+1)/prefixModeMargin k (S k).card)
  simpa only [div_eq_mul_inv,Nat.cast_one,Nat.cast_ofNat] using hG

#print axioms derivativePhaseHorizon_double_upper
end
end GaloisForLFunctions.HTGeometry.SpectralJets
