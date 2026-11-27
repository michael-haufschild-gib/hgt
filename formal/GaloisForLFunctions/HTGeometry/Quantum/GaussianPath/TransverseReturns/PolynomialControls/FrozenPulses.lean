import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.PolynomialControls.PulseDeadline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.TransverseReturns.PolynomialControls.PulsePrecision
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GaussianLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.ExtremePair.Origin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.CrossingDeadline

/-! # A hierarchy of quadratic-budget precision bounds at the original crossing -/
open Real Set MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
open PrecisionReturns SpectralFilling.ReplicaOrders
noncomputable section

/-- At every fixed pulse order p=j+2 the budget is quadratic in prefix
length, and the upper precision exponent of the actual first elapsed
wait from σ is D−3+1/p. All orders concern the same selected origin. -/
theorem gaussian_high_order_first_wait :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D : ℕ := 2^K
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget K
      let σ := ReturnExcursions.Iterated.crossing H P 0
      ∀ j : ℕ,
        let p := j+2
        let S := 3^j*(Fintype.card (PathLabel (k+1))+1)^2*9
        ∃ B>(0:ℝ), ∃ C>(0:ℝ), ∀ ε ∈ Ioc 0 B,
          (firstVisit H σ S ε-σ)^p*ε^(p*(D-3)+1) ≤ C := by
  obtain ⟨_,_,hcross⟩ := gaussian_replica_crossing_deadline
  filter_upwards [gaussian_gap_clock,gaussian_path_all_prefixes_maximally_projective,hcross]
    with ω hclock hg hcross
  filter_upwards [hcross] with k hσ
  intro K D u H P σ j p S
  have hre := (hσ 0).1.1
  change 0 ≤ σ ∧ 9/80 ≤ orbitCircuitDistance H P σ at hre
  have hwidth := PassageMoments.ExtremePair.width_at_origin H P hre.1
  have hprod : 0 < σ*circuitHamiltonianSpectralWidth H := by linarith only [hwidth,hre.2]
  have hσ' : 0 < σ := lt_of_le_of_ne hre.1 (fun he => by rw [←he,zero_mul] at hprod; exact hprod.false)
  obtain ⟨e,hgap,_⟩ := hclock k
  let z : Fin (2^K-3+3) := ⟨2,by omega⟩
  have hz₀ : z ≠ 0 := by intro he; have h := congrArg Fin.val he; change 2=0 at h; omega
  have hz₁ : z ≠ 1 := by intro he; have h := congrArg Fin.val he; simp only [z,Fin.val_one] at h; omega
  have hinj := (hg k).injective
  obtain ⟨B,hB,h⟩ := high_order_path_deadline u (e.symm 0) (e.symm 1) (e.symm z) j
    (sub_pos.mp hgap) (hinj.ne (e.symm.injective.ne hz₀)) (hinj.ne (e.symm.injective.ne hz₁))
  obtain ⟨T,hT,hd⟩ := h σ
  exact ⟨B,hB,T^p*((2:ℝ)^p*(2*B))^(p*(D-3)+1),by positivity,
    pulse_precision (by dsimp only [p]; omega) H hσ' hB hT hd⟩

#print axioms gaussian_high_order_first_wait
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
