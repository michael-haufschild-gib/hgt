import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.UnshiftedScalar
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.HardNeighbor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialDeadline

/-! # Inverse-time field intervals of opposite physical complexity on the original chain -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
noncomputable section
private abbrev Reg (k : ℕ) := Matrix (Fin (k+3)→Bool) (Fin (k+3)→Bool) ℂ

/-- On every sufficiently long prefix of one Gaussian draw, at every
sufficiently late date, changing just the terminal Z coefficient by at
most C/T reaches both a scalar neighborhood and a near-Hilbert hard
neighborhood. Both tolerate a further change of 1/(400T) on either side. -/
theorem gaussian_physical_inverse_time_neighbors :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let H (z : ℝ) : selfAdjoint (Reg k) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
      ∃ C : ℝ, 0<C ∧ ∀ᶠ T : ℝ in atTop, ∃ u∈Icc (0:ℝ) (C/T), ∃ v∈Icc (0:ℝ) (C/T),
        (∀ z : ℝ, T*|z-u| ≤ 1/400 → orbitCircuitDistance (H z) 0 T ≤ 1/10) ∧
        (∀ z : ℝ, T*|z-v| ≤ 1/400 → 1/10 < orbitCircuitDistance (H z) P T) := by
  have heps : (1/400:ℝ)∈Ioo (0:ℝ) (Real.sqrt 2) := ⟨by norm_num,by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]⟩
  obtain ⟨_,hcross⟩ := ReturnExcursions.gaussian_initial_crossing_short_return_tradeoff
  filter_upwards [gaussian_unshifted_inverse_scalar (1/400) heps,hcross] with ω hs hσ
  filter_upwards [hσ] with k hk
  intro P H
  obtain ⟨σ,hdate,he,_,_,_⟩ := hk
  have hσ0 := (by positivity : (0:ℝ) < 2^(k+3-10*(k+3).sqrt)).trans hdate
  have he' : orbitCircuitDistance (H 0) P σ=9/80 := by
    simpa only [orbitCircuitDistance,H,boundaryHamiltonian,Complex.ofReal_zero,zero_smul,add_zero] using he
  obtain ⟨M,hM,hscalar⟩ := hs k
  have hnear (T : ℝ) (ht : (M:ℝ)^2≤T) := hscalar T ht
  obtain ⟨C,hC,hpair⟩ := hard_neighbors_of_crossing ω k P 0 σ M hσ0 (by exact_mod_cast hM) he'
    (fun T ht => by simpa only [zero_add] using hnear T ht)
  refine ⟨C,hC,?_⟩
  filter_upwards [hpair,eventually_gt_atTop (0:ℝ)] with T hh ht
  obtain ⟨⟨u,hu,hlo⟩,v,hv,hhi⟩ := hh
  rw [zero_add] at hu hv
  refine ⟨u,hu,v,hv,?_,?_⟩
  · intro z hz
    have h := field_distance_le ω k 0 z u T
    change orbitCircuitDistance (H z) 0 T ≤ orbitCircuitDistance (H u) 0 T+ |T| * |z-u| at h
    rw [abs_of_pos ht] at h
    change orbitCircuitDistance (H u) 0 T ≤ 1/20 at hlo
    linarith only [hz,h,hlo]
  · intro z hz
    have h := field_distance_le ω k P v z T
    change orbitCircuitDistance (H v) P T ≤ orbitCircuitDistance (H z) P T+ |T| * |v-z| at h
    rw [abs_of_pos ht,abs_sub_comm v z] at h
    change 21/200 < orbitCircuitDistance (H v) P T at hhi
    linarith only [hz,h,hhi]

#print axioms gaussian_physical_inverse_time_neighbors
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
