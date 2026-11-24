import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.ScaleGrowth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock

/-! # Growth of the inverse frequency margin for finite mode families -/
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

private theorem inverse_margin (u v C : ℝ) (k B L : ℕ) :
    ((((1/2:ℝ)^k/u)^B/C)*(((1/2:ℝ)^k/v)^L))⁻¹ = C*((2:ℝ)^k*u)^B*((2:ℝ)^k*v)^L := by
  simp only [div_eq_mul_inv,mul_inv_rev,← inv_pow,inv_inv,one_mul]
  ac_rfl

/-- A packet with logarithmic cardinality polynomial in dimension retains an inverse
frequency margin of the same growth class. -/
theorem inverse_margin_log_polynomial (count : ℕ → ℕ)
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

#print axioms inverse_margin_log_polynomial
end
end GaloisForLFunctions.HTGeometry.SpectralJets
