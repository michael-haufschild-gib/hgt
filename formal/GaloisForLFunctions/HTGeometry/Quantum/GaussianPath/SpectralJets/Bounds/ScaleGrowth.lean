import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.Growth
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.PrefixResponse
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.GaussianStrip

/-! # Size of the Gaussian response and the spectral line-cut count -/
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

theorem polynomial_jet_order : PolynomialInDimension (fun k => 2^(k+3)-2) :=
  PolynomialInDimension.dim.mono fun _ => Nat.sub_le _ _

private theorem polynomial_labels : PolynomialInDimension (fun k => Fintype.card (ChainLabel (k+3))) := by
  let hd := PolynomialInDimension.dim.square
  apply hd.mono
  intro k
  have h := Fintype.card_le_of_injective (fun v : ChainLabel (k+3) => v.val) Subtype.val_injective
  simp only [Fintype.card_fun,Fintype.card_option,Fintype.card_fin] at h
  have he : (4:ℕ)^(k+3) = (2^(k+3):ℕ)^2 := calc
    _ = (2^2:ℕ)^(k+3) := rfl
    _ = 2^(2*(k+3)) := (pow_mul _ _ _).symm
    _ = 2^((k+3)*2) := by rw [Nat.mul_comm 2]
    _ = _ := pow_mul _ _ _
  exact h.trans_eq he

theorem polynomial_detector_degree : PolynomialInDimension prefixDetectorDegree :=
  PolynomialInDimension.dim.mul ((PolynomialInDimension.const 2).mul
    ((PolynomialInDimension.const 1).add (((PolynomialInDimension.const 2).mul polynomial_jet_order).mul
      PolynomialInDimension.dim)))

/-- The Cramer response constant grows at most exponentially in a fixed power
of the Hilbert-space dimension. -/
theorem responseCap_log_polynomial : LogPolynomialInDimension
    (fun k : ℕ => pathResponseCap (k+3) (2^(k+3)-2) (((k+3:ℕ):ℝ)^2)) := by
  let D (k : ℕ) := 2^(k+3)
  let L (k : ℕ) := D k-2
  let T (k : ℕ) := (((k+3:ℕ):ℝ)^2)
  let R (k : ℕ) := pathBoxRadius (k+3) (T k) + (L k:ℝ) + 3
  let K (k : ℕ) := pencilCap (k+3) (R k)
  let d := PolynomialInDimension.dim
  let l := polynomial_jet_order
  let twoL := (PolynomialInDimension.const 2).mul l
  let hd := LogPolynomialInDimension.natCast d
  let hl := LogPolynomialInDimension.natCast l
  let hcount := LogPolynomialInDimension.natCast polynomial_labels
  let h₁ := LogPolynomialInDimension.const 1
  let hT := (LogPolynomialInDimension.natCast PolynomialInDimension.sites).pow (PolynomialInDimension.const 2)
  let hJ := LogPolynomialInDimension.factorial d
  have hR : LogPolynomialInDimension R := by
    simpa only [R,T,L,D,pathBoxRadius,Nat.cast_one,Nat.cast_ofNat] using
      ((hT.add ((hd.add h₁).mul (hcount.mul hT))).add hl).add (LogPolynomialInDimension.const 3)
  have hK : LogPolynomialInDimension K := by
    simpa only [K,pencilCap,Nat.cast_one] using hJ.mul (((hcount.add h₁).mul hR).pow d)
  let hM := (hR.mul (((LogPolynomialInDimension.const 2).add ((LogPolynomialInDimension.const 4).mul hl)).pow l)).mul
    (hK.pow twoL)
  simpa only [pathResponseCap,K,R,T,L,D,Nat.cast_one,Nat.cast_ofNat] using
    ((h₁.add (hd.mul (hK.pow twoL))).mul hJ).mul ((h₁.add (hd.mul (hd.mul hM))).pow d)

/-- The algebraic number of line intervals enters multiplicatively in the
sublevel estimate, and its logarithm is polynomial in dimension. -/
theorem jetIntervals_log_polynomial :
    LogPolynomialInDimension (fun k : ℕ => (jetLineIntervals (2^(k+3)) (2^(k+3)-2) : ℝ)) := by
  let d := PolynomialInDimension.dim
  let l := polynomial_jet_order
  let one := PolynomialInDimension.const 1
  let two := PolynomialInDimension.const 2
  let b := (two.mul l).mul d
  let z := (d.add ((two.mul d).mul d)).add one
  let j := ((one.add (one.add b)).add (d.mul b)).add one
  have h := ((LogPolynomialInDimension.natCast (d.mul (b.add (two.mul d)))).add
    ((LogPolynomialInDimension.const 2).mul (((LogPolynomialInDimension.natCast z).pow d).mul
      (LogPolynomialInDimension.natCast j)))).add (LogPolynomialInDimension.const 1)
  simpa only [jetLineIntervals,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,Nat.cast_ofNat] using h

#print axioms responseCap_log_polynomial
#print axioms jetIntervals_log_polynomial
end
end GaloisForLFunctions.HTGeometry.SpectralJets
