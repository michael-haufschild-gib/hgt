import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.AntipodalError.Deletion
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.EnergyMesh.ClippedChord

/-! # The squared distance deficit of sparse gates after the first full turn -/

open Filter Finset MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.AntipodalError
open EnergyMesh ThermodynamicEdges
noncomputable section

private theorem padded_mass {I : Type*} [Fintype I] (u : I → ℝ) {N B : ℝ}
    (hs : ∀ S : Finset I, S.Nonempty →
      (∑ i ∈ S, |u i|)^2 ≤ 4*(S.card:ℝ)^2*log (B*N/S.card))
    (L : Finset I) {k : ℕ} (hk : 0 < k) (hL : L.card ≤ k) (hcap : k ≤ Fintype.card I) :
    (∑ i ∈ L, |u i|) ≤ 2*(k:ℝ)*sqrt (log (B*N/k)) := by
  obtain ⟨M,hm,hcard⟩ := exists_superset_card_eq hL hcap
  have hh := hs M (card_pos.mp (hcard ▸ hk))
  rw [hcard] at hh
  apply (sum_le_sum_of_subset_of_nonneg hm (fun i _ _ => abs_nonneg (u i))).trans
  apply (sq_le_sq₀ (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).mp
  have hlog : log (B*N/k) ≤ (sqrt (log (B*N/k)))^2 := by
    rw [Real.sq_sqrt']; exact le_max_left _ _
  exact hh.trans ((mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4*(k:ℝ)^2)).trans_eq (by ring))

/-- Beyond a full bandwidth turn, both the spectral mesh and the deleted
coefficient mass enter quadratically into the deficit from distance two.
This includes the first such date and permits draw-dependent gate budgets. -/
theorem gaussian_antipodal_deficit :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := ((n+2:ℕ):ℝ)
      let H := shellOperator (pathPauliDisorderShell ω n)
      let W := circuitHamiltonianSpectralWidth H
      ∀ s : ℕ, let k := max 1 (42*s)
        k ≤ Fintype.card (PathLabel n) → ∀ t : ℝ, 0 ≤ t → 2*π ≤ t*W →
          4-(orbitCircuitDistance H s t)^2 ≤
            (t*(42*sqrt (log (A*N))+4*(k:ℝ)*sqrt (log (B*N/k))))^2 := by
  obtain ⟨A,hA,hcover⟩ := gaussian_energy_cover
  obtain ⟨B,hB,hmass⟩ := gaussian_subset_mass
  refine ⟨A,B,hA,hB,?_⟩
  filter_upwards [hcover,hmass] with ω hc hm
  filter_upwards [hc,hm] with n hc hm
  intro N H W s k hcap t ht hfull
  let q := 42*sqrt (log (A*N))
  let m := (k:ℝ)*sqrt (log (B*N/k))
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hmean : 0 ≤ m := by dsimp only [m]; positivity
  obtain ⟨L,hL,he⟩ := circuit_deficit_advantage (pathPauliDisorderShell ω n) s t
  have hmass := padded_mass _ hm L (lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..))
    (hL.trans (le_max_right ..)) hcap
  have hscalar := saturated_scalar_deficit H hq ht hfull hc
  change gateDeficit H 0 t ≤ t*q at hscalar
  rw [abs_of_nonneg ht] at he
  have hprod := mul_le_mul_of_nonneg_left hmass (mul_nonneg zero_le_two ht)
  have hbound : gateDeficit H s t ≤ t*(q+4*m) := by
    change gateDeficit H s t ≤ gateDeficit H 0 t+_ at he
    dsimp only [m]
    linarith only [he,hscalar,hprod]
  have hsq := pow_le_pow_left₀ (sqrt_nonneg _) hbound 2
  change (sqrt (4-(orbitCircuitDistance H s t)^2))^2 ≤ _ at hsq
  apply le_trans _ hsq
  rw [Real.sq_sqrt']; exact le_max_left _ _

#print axioms gaussian_antipodal_deficit
end
end GaloisForLFunctions.HTGeometry.FirstAscent.AntipodalError
