import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.BlockSites

/-! # Positive density of nearly isolated longitudinal fields -/
open MeasureTheory Filter Set
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Every fixed tolerance has a deterministic positive density of sites whose
onsite and both incident edges approximate one isolated Z field. -/
theorem gaussian_path_eventual_isolated_sites (q η : ℝ) (hη : 0 < η) :
    ∃ p : ℝ, 0 < p ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∃ S : Finset (Fin (n+2)), p*((n+2:ℕ):ℝ) ≤ S.card ∧
        ∀ s ∈ S, isolatedLongitudinalSite (pathPauliDisorderShell ω n) q η s := by
  classical
  let lo i := isolatedFieldBlockCenter q i-η
  let hi i := isolatedFieldBlockCenter q i+η
  obtain ⟨p,hp,hblocks⟩ := gaussian_pauli_block_positive_density lo hi
    (fun i => by dsimp [lo,hi]; linarith)
  refine ⟨p/3,by positivity,?_⟩
  filter_upwards [hblocks] with ω hω
  have hN : Tendsto (fun n : ℕ => (n+2)/2) atTop atTop := by
    rw [tendsto_atTop]
    intro m
    exact eventually_atTop.2 ⟨2*m,fun n hn => by omega⟩
  filter_upwards [hN.eventually hω] with n hn
  let m := (n+2)/2
  let A := (Finset.range m).filter (fun j => ∀ i, pathPauliBlock ω j i ∈ Icc (lo i) (hi i))
  have hmj (j : {j // j ∈ A}) : j.val < m := Finset.mem_range.mp (Finset.mem_filter.mp j.2).1
  let g : {j // j ∈ A} ↪ Fin (n+2) := {
    toFun := fun j => ⟨2*j.val+1,by have := hmj j; dsimp [m] at this; omega⟩
    inj' := by intro i j h; apply Subtype.ext; have he := congrArg Fin.val h
               change 2*i.val+1=2*j.val+1 at he; omega }
  let S := A.attach.map g
  have hcard : S.card = A.card := by simp [S]
  refine ⟨S,?_,?_⟩
  · rw [hcard]
    have hm : ((n+2:ℕ):ℝ) ≤ 3*(m:ℝ) := by exact_mod_cast (by dsimp [m]; omega : n+2 ≤ 3*m)
    change p*(m:ℝ) ≤ A.card at hn
    linarith only [mul_le_mul_of_nonneg_left hm hp.le,hn]
  intro s hs
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hs
  apply isolated_odd_site_of_block ω q η (j := j.val) rfl
  intro i
  have hb := (Finset.mem_filter.mp j.2).2 i
  change isolatedFieldBlockCenter q i-η ≤ _ ∧ _ ≤ isolatedFieldBlockCenter q i+η at hb
  exact abs_le.mpr ⟨by linarith only [hb.1],by linarith only [hb.2]⟩

#print axioms gaussian_path_eventual_isolated_sites
end
end GaloisForLFunctions.HTGeometry
