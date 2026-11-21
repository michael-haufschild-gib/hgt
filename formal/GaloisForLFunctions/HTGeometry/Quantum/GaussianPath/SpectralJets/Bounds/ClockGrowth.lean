import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.ScaleGrowth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock

/-! # Doubly exponential growth of the derivative phase horizon -/
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

private theorem inverse_margin (u v C : ℝ) (k B L : ℕ) :
    ((((1/2:ℝ)^k/u)^B/C)*(((1/2:ℝ)^k/v)^L))⁻¹ = C*((2:ℝ)^k*u)^B*((2:ℝ)^k*v)^L := by
  simp only [div_eq_mul_inv,mul_inv_rev,← inv_pow,inv_inv,one_mul]
  ac_rfl

private theorem inverse_margin_log_polynomial (count : ℕ → ℕ)
    (hcount : LogPolynomialInDimension (fun k => (count k:ℝ))) :
    LogPolynomialInDimension (fun k => (prefixModeMargin k (count k))⁻¹) := by
  let D (k : ℕ) := 2^(k+3)
  let L (k : ℕ) := D k-2
  let B := prefixDetectorDegree
  let hD := LogPolynomialInDimension.natCast PolynomialInDimension.dim
  let hL := LogPolynomialInDimension.natCast polynomial_jet_order
  let h₁ := LogPolynomialInDimension.const 1
  let h₂ := LogPolynomialInDimension.const 2
  have hk : PolynomialInDimension (fun k => k) := PolynomialInDimension.sites.mono fun _ => Nat.le_add_right _ _
  let hₖ := LogPolynomialInDimension.twoPow hk
  have hprice : LogPolynomialInDimension (fun k => (modeStripPrice (D k) (L k) (count k):ℝ)) := by
    have h := ((((LogPolynomialInDimension.const 16).mul hcount).mul hD).mul hL).mul jetIntervals_log_polynomial
    simpa only [modeStripPrice,Nat.cast_mul,Nat.cast_ofNat,D,L] using h
  let hC := h₁.add (responseCap_log_polynomial.mul hD).abs
  let hu := h₁.add (h₂.mul (LogPolynomialInDimension.natCast polynomial_detector_degree))
  let hv := h₁.add hprice
  have h := (hC.mul ((hₖ.mul hu).pow polynomial_detector_degree)).mul ((hₖ.mul hv).pow polynomial_jet_order)
  have he (k : ℕ) : (prefixModeMargin k (count k))⁻¹ =
      (1+|pathResponseCap (k+3) (L k) (((k+3:ℕ):ℝ)^2)*(D k:ℝ)|)*
        ((2:ℝ)^k*(1+2*(B k:ℝ)))^(B k)*((2:ℝ)^k*(1+(modeStripPrice (D k) (L k) (count k):ℝ)))^(L k) :=
    inverse_margin _ _ _ _ _ _
  simpa only [he,L,D,B,Nat.cast_one,Nat.cast_ofNat] using h

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
