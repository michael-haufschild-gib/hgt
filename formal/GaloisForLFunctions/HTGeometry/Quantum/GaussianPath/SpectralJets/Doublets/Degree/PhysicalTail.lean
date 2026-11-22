import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.Degree.TraceBound
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.PhysicalTraceWitness
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.IntegralSublevel

/-! # Finite-size lower tail for a physical longitudinal response determinant -/
open MvPolynomial MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

/-- With N=n+2 spins and D energies, the trace determinant has D/2 rows of
even order L=N−1 rounded up. The degree bound is (D/2)(2L+1)D. -/
def traceDegreeBound (n : ℕ) : ℕ :=
  let D := 2^(n+2)
  let L := n+1+(n+1)%2
  2^(n+1)*(2*L*D+D)

theorem physicalTrace_degree (n : ℕ) (k : Fin (2^(n+1)) → Fin (2^(n+2))) :
    (physicalTrace n k).totalDegree ≤ traceDegreeBound n := by
  let L := n+1+(n+1)%2
  let D := 2^(n+2)
  calc
    _ ≤ 2^(n+1)*((1+2*L*D)+D-1) := fieldTraceMinor_degree _
      (pencil_degree (integralGenerators (n+2))) (spinCoefficient (n+2)) L
      (physicalWords n) (fun j => (maskWord_length _).le) k
    _ = _ := by
      unfold traceDegreeBound
      apply congrArg (2^(n+1)*·)
      change (1+2*L*D+D)-1 = 2*L*D+D
      rw [Nat.add_assoc 1,Nat.add_comm 1 (2*L*D+D),Nat.add_sub_cancel]

/-- A deterministic trace minor on each physical prefix has an absolute Gaussian
small-value bound at every scale, with no normalization by its coefficients. -/
theorem physicalTrace_lower_tail (n : ℕ) :
    ∃ k, ∀ {r : ℝ}, 0<r → r≤1 →
      (centredProductGaussian (Coordinates (n+2)) 1)
        {x | ‖eval₂Hom GaussianInt.toComplex (fun i => (x i : ℂ)) (physicalTrace n k)‖ <
          r^(traceDegreeBound n)} ≤ ENNReal.ofReal (2*(traceDegreeBound n:ℝ)*r) := by
  obtain ⟨k,hk⟩ := physicalTrace_nonzero n
  exact ⟨k,fun hr hr' => gaussianInt_sublevel_of_degree_le _ _ (physicalTrace_degree n k) hk hr hr'⟩

#print axioms physicalTrace_lower_tail
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
