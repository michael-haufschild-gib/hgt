import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PassageMoments.ExtremePair.Origin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.CrossingDeadline

/-! # A uniform precision bound for the original frozen-chain excursion -/
open Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair
open PrecisionReturns SpectralFilling.ReplicaOrders
noncomputable section

/-- At the original near-Hilbert crossing the first subsequent visit has
a prefix-independent relative prefactor for every positive tolerance.
Two energy levels are synchronized exactly, irrespective of the budget. -/
theorem gaussian_first_visit_from_crossing :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let H : selfAdjoint (Register K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget K
      let σ := ReturnExcursions.Iterated.crossing H P 0
      ∀ s : ℕ, ∀ ε > (0:ℝ),
        firstVisit H σ s ε ≤ (1+80*π/9)*σ*(⌈2*π/ε⌉₊:ℝ)^(2^K-2) := by
  obtain ⟨_,_,h⟩ := gaussian_replica_crossing_deadline
  filter_upwards [h] with ω hw
  filter_upwards [hw] with k hk
  intro K H P σ s ε hε
  have hc := (hk 0).1.1
  change 0≤σ ∧ 9/80≤orbitCircuitDistance H P σ at hc
  let W := circuitHamiltonianSpectralWidth H
  have hW := width_at_origin H P hc.1
  have hnum : (9/40:ℝ)≤σ*W := by linarith only [hc.2,hW]
  have hprod : 0<σ*W := lt_of_lt_of_le (by norm_num : (0:ℝ)<9/40) hnum
  have hs : 0<σ := lt_of_le_of_ne hc.1 (fun h => by rw [←h,zero_mul] at hprod; exact hprod.false)
  have hw' : 0<W := pos_of_mul_pos_right hprod hs.le
  have hp : 2*π/W ≤ (80*π/9)*σ := by
    apply (div_le_iff₀ hw').mpr
    have h := mul_le_mul_of_nonneg_left hnum (show 0≤80*π/9 by positivity)
    linarith only [h]
  let Q := ⌈2*π/ε⌉₊
  have hQ : 0<Q := Nat.ceil_pos.mpr (div_pos two_pi_pos hε)
  have htol : 2*π/(Q:ℝ) ≤ ε := (div_le_iff₀ (Nat.cast_pos.mpr hQ)).mpr
    (by rw [mul_comm ε]; exact (div_le_iff₀ hε).mp (Nat.le_ceil (2*π/ε)))
  have hhit := firstVisit_isLeast H σ s (div_pos two_pi_pos (Nat.cast_pos.mpr hQ))
  obtain ⟨ha,z,hz,C,hC,he⟩ := hhit.1
  have hmono := (firstVisit_isLeast H σ s hε).2 ⟨ha,z,hz,C,hC,he.trans htol⟩
  have hbound := first_visit_by_extreme_period H hs hw' s hQ
  have hsum : σ+2*π/W ≤ (1+80*π/9)*σ := by linarith only [hp]
  exact hmono.trans (hbound.trans (mul_le_mul_of_nonneg_right hsum (by positivity)))

#print axioms gaussian_first_visit_from_crossing
end
end GaloisForLFunctions.HTGeometry.PassageMoments.ExtremePair
