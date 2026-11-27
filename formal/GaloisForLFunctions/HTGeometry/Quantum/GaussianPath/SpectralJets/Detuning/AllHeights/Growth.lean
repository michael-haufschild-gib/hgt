import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.ModeHeights
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.ModeMargin.Growth

/-! # Growth of the inverse all-height detuning margin -/
namespace GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
noncomputable section

private theorem inverse_height (k h : ℕ) :
    let D := 2^(k+3)
    let count := (4*(h+1)+1)^D
    (heightMargin k h)⁻¹=(prefixModeMargin k count)⁻¹*(4*((h:ℝ)+1))^(D-2) := by
  intro D count
  let L := D-2
  let P := modeStripPrice D L count
  have he : (((2^(k+2)*(h+1)*(1+P):ℕ):ℝ))⁻¹=prefixStripRatio k count/(4*((h:ℝ)+1)) := by
    change _=((1/2:ℝ)^k/(1+(P:ℝ)))/(4*((h:ℝ)+1))
    push_cast
    rw [one_div_pow,pow_add]
    norm_num only [Nat.reducePow,one_div]
    field_simp
  change (prefixModeAmplitude k*((((2^(k+2)*(h+1)*(1+P):ℕ):ℝ))⁻¹)^L)⁻¹=
    (prefixModeAmplitude k*(prefixStripRatio k count)^L)⁻¹*(4*((h:ℝ)+1))^L
  rw [he]
  simp only [div_eq_mul_inv,mul_pow,mul_inv_rev,←inv_pow,inv_inv]
  ring

/-- A single deterministic prefactor controls arbitrarily large integer
heights with exponent (D+1)(D−2). -/
theorem inverse_height_polynomial (k h : ℕ) :
    let D := 2^(k+3)
    (heightMargin k h)⁻¹ ≤ (heightMargin k 0)⁻¹*((h:ℝ)+1)^((D+1)*(D-2)) := by
  intro D
  let L := D-2
  let u := h+1
  let P := modeStripPrice D L
  let den (j : ℕ) := 2^(k+2)*(j+1)*(1+P ((4*(j+1)+1)^D))
  have he (j : ℕ) : (heightMargin k j)⁻¹=(den j:ℝ)^L*(prefixModeAmplitude k)⁻¹ := by
    change (prefixModeAmplitude k*((den j:ℝ)⁻¹)^L)⁻¹=_
    rw [mul_inv_rev,←inv_pow,inv_inv]
  have hc : (4*u+1)^D ≤ 5^D*u^D := by
    rw [←Nat.mul_pow]
    exact Nat.pow_le_pow_left (by dsimp only [u]; omega) _
  have hP : P ((4*u+1)^D) ≤ P (5^D)*u^D := by
    have hp : P ((4*u+1)^D) ≤ P (5^D*u^D) := by
      dsimp only [P,modeStripPrice]
      gcongr
    apply hp.trans_eq
    dsimp only [P,modeStripPrice]
    ring
  have h1 : 1 ≤ u^D := Nat.one_le_pow _ _ (by dsimp only [u]; omega)
  have hsum : 1+P ((4*u+1)^D) ≤ (1+P (5^D))*u^D := by
    rw [Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add h1 hP
  have hd : den h ≤ den 0*u^(D+1) := by
    apply (Nat.mul_le_mul_left (2^(k+2)*u) hsum).trans_eq
    simp only [den,Nat.zero_add,Nat.mul_one,pow_succ]
    ring
  have hd' : (den h:ℝ) ≤ (den 0:ℝ)*((h:ℝ)+1)^(D+1) := by exact_mod_cast hd
  rw [he,he,pow_mul]
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hd' L)
    (inv_nonneg.mpr (prefixModeAmplitude_pos k).le)).trans_eq
  rw [mul_pow]
  ring

/-- Any height schedule with logarithm polynomial in Hilbert dimension has
a detuning floor whose reciprocal also has polynomial logarithm. -/
theorem inverse_height_log_polynomial (h : ℕ → ℕ) (hh : LogPolynomialInDimension fun k => (h k:ℝ)) :
    LogPolynomialInDimension (fun k => (heightMargin k (h k))⁻¹) := by
  let D (k : ℕ) := 2^(k+3)
  let count (k : ℕ) := (4*(h k+1)+1)^(D k)
  let h₁ := LogPolynomialInDimension.const 1
  let h₄ := LogPolynomialInDimension.const 4
  have hc : LogPolynomialInDimension (fun k => (count k:ℝ)) := by
    simpa only [count,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,D] using
      ((h₄.mul (hh.add h₁)).add h₁).pow PolynomialInDimension.dim
  have hfinal := (inverse_margin_log_polynomial count hc).mul ((h₄.mul (hh.add h₁)).pow polynomial_jet_order)
  simpa only [inverse_height,count,D,Nat.cast_ofNat,Nat.cast_one] using hfinal

#print axioms inverse_height_log_polynomial
end
end GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
