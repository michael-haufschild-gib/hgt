import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.ResponseWeights.OrientedCovariance
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.GaussianLaw

/-! # Recovering every coupling from the signed flux of scalar-entry pairs -/
open Matrix Filter Topology MeasureTheory Real Set
namespace GaloisForLFunctions.HTGeometry.FirstGate.ResponseWeights
noncomputable section
open EmptyVisitFlux

/-- Weight each incoming face by the difference of the two local Pauli
expectations, higher minus lower energy. Its exact long-time flux gives the
physical coupling, with the same normalization for every site and bond. -/
theorem gaussian_local_coupling_flux : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
    let n := k+1
    let N := n+2
    let D := 2^N
    let p := pathPauliDisorderShell ω n
    let E := fun i => -(isSelfAdjoint_pathHamiltonian p).isHermitian.eigenvalues i
    ∀ r : Icc (0:ℝ) (1/2), ∀ l : PathLabel n,
      let z := localMean p l
      Tendsto (fun T : ℝ => ∑ ij : (Fin N→Bool) × (Fin N→Bool),
        (z ij.2-z ij.1)*(((markedDates E ij.1 ij.2 r (forwardUnitArc r) T).card:ℝ)/T)) atTop
        (𝓝 ((r:ℝ)^(D-2)*((D:ℝ)^2*p l)/(2*π))) := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hω k
  intro n N D p E r l z
  have hi := maximallyProjectiveEnergy_neg (hω k)
  have h := tendsto_finsetSum (Finset.univ : Finset ((Fin N→Bool) × (Fin N→Bool))) fun ij _ =>
    (tendsto_const_nhds (x := z ij.2-z ij.1)).mul
      (markedDates_rate E hi ij.1 ij.2 r _ (Or.inr rfl))
  have he : (∑ ij : (Fin N→Bool) × (Fin N→Bool), (z ij.2-z ij.1)*
      ((r:ℝ)^(D-2)*(max 0 (E ij.1-E ij.2)/(2*π)))) =
      (r:ℝ)^(D-2)*((D:ℝ)^2*p l)/(2*π) := by
    have hs := incoming_local_response p l
    calc
      _ = (r:ℝ)^(D-2)*(∑ ij : (Fin N→Bool) × (Fin N→Bool),
          max 0 (E ij.1-E ij.2)*(z ij.2-z ij.1))/(2*π) := by
        rw [Finset.mul_sum,Finset.sum_div]
        apply Finset.sum_congr rfl
        intro ij _
        ring
      _ = _ := by rw [hs]; simp [D,N]
  rw [←he]
  simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,D] using h

#print axioms gaussian_local_coupling_flux
end
end GaloisForLFunctions.HTGeometry.FirstGate.ResponseWeights
