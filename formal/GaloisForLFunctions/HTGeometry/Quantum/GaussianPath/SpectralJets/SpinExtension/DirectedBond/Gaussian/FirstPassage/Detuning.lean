import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.Gaussian.TypicalRank
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.FiniteMargin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.Probability.OrderPrice

/-! # Finite-mode detuning with a linear derivative order -/
open Matrix MvPolynomial MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- Degree of the integral detector using the first terminal derivative. -/
def detectorDegree (n : ℕ) : ℕ := 2^(n+1)*(2*(1+2*(2*n+1)*2^(n+1)))

/-- Finite-mode margin with the directed detector on N=n+1 spins. -/
def detuningMargin (n count : ℕ) (T η : ℝ) : ℝ := floorAtOrder (n+1) (2*n+1) count T η

/-- Simultaneous lower tails of every balanced frequency in the finite list.
The power of the confidence parameter is 2D(1+2LD)+L with L=2N−1. -/
theorem gaussian_box_detuning (n : ℕ) (S : Finset (Fin (2^(n+1))→ℤ))
    {T η : ℝ} (hT : 0≤T) (hη : 0<η) (hη' : η≤1) :
    let N := n+1
    let μ := Measure.pi fun _ : Coordinates N => gaussianReal 0 1
    μ ({x | ∀ i, |x i|≤T} ∩ smallBalancedMode N S (detuningMargin n S.card T η)) ≤
      ENNReal.ofReal η+ENNReal.ofReal η := by
  obtain ⟨rows,hw,hn,_,_⟩ := low_order_detector_tail n
  exact box_margin_of_detector (n+1) (2*n+1) rows hw hn S hT hη hη'

#print axioms gaussian_box_detuning
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
