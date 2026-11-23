import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldApproximation

/-! # Squared coupling mass for nearly isolated longitudinal spins -/
open Finset
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

/-- The reference retains the complement and places one unit field on
each selected spin. At most 21 coefficients per spin change. -/
def fieldReference {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2))) : PathShell n :=
  WithLp.toLp 2 (pathPacketReferenceCoeff Sᶜ S u (longitudinalPacket S 1))

theorem fieldReference_generator {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2))) :
    pathHamiltonian (fieldReference u S)=pathHamiltonianPacketReference Sᶜ S u (longitudinalPacket S 1) := by
  rw [pathHamiltonian_eq_sum,pathHamiltonianPacketReference_eq_sum]
  rfl

theorem fieldReference_energy {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2)))
    {δ : ℝ} (hs : ∀ i ∈ S, isolatedLongitudinalSite u 1 δ i) :
    ∑ l : PathLabel n, (u l-fieldReference u S l)^2 ≤ 21*(S.card:ℝ)*δ^2 := by
  classical
  let W := S.biUnion pathIncidentLabels
  obtain ⟨hc,hz⟩ := isolated_field_coefficient_bounds u S 1 δ hs
  have hoff (l : PathLabel n) (_ : l ∈ univ) (hl : l ∉ W) : (u l-fieldReference u S l)^2=0 := by
    rw [show u l-fieldReference u S l=0 from abs_eq_zero.mp (hz l hl),zero_pow (by decide : 2 ≠ 0)]
  rw [←sum_subset (subset_univ W) hoff]
  have hon (l : PathLabel n) (hl : l ∈ W) : (u l-fieldReference u S l)^2 ≤ δ^2 := by
    rw [←sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hc l hl) 2
  apply (sum_le_sum hon).trans
  rw [sum_const,nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast pathIncident_union_card S

#print axioms fieldReference_energy
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
