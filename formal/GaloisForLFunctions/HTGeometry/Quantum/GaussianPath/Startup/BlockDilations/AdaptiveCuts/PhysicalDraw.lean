import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.BufferedOwners
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.Baseline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.TypicalBuffers

/-! # Typical membership in the adaptively selected physical event -/

open MeasureTheory Finset Filter Set Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n N : ℕ}

private def bufferBoxes (hN : 0<N) (w : ℝ) : Set (PathLabel n→ℝ) :=
  ⋂ b : fullBuffers n N, ⋃ j : Fin N, ⋂ k : Fin 9, {z | |z (bondLabels (n:=n) hN b j k)|≤w/3}

private theorem mem_bufferBoxes (hN : 0<N) (w : ℝ) (z : PathLabel n→ℝ) :
    z∈bufferBoxes hN w ↔ ∀ b : fullBuffers n N, ∃ j : Fin N,
      ∀ k : Fin 9, |z (bondLabels (n:=n) hN b j k)|≤w/3 := by
  simp only [bufferBoxes,Set.mem_iInter,Set.mem_iUnion,Set.mem_setOf_eq]

/-- Each buffer contains a candidate in the box of radius w/3.
Consequently its least-energy bond has every coordinate bounded by w. -/
def adaptiveDraw (hN : 0<N) (F E w R : ℝ) : Set (PathLabel n→ℝ) :=
  cutBounds ∅ F E w R ∩ bufferBoxes (n:=n) hN w

theorem measurable_adaptiveDraw (hN : 0<N) (F E w R : ℝ) :
    MeasurableSet (adaptiveDraw (n:=n) hN F E w R) :=
  (measurable_cutBounds ..).inter <| MeasurableSet.iInter fun b => MeasurableSet.iUnion fun j =>
    MeasurableSet.iInter fun k => measurableSet_le
      (measurable_pi_apply (bondLabels (n:=n) hN b j k)).abs measurable_const

/-- The box condition controls the selected seams, even in the presence of ties. -/
theorem adaptive_cut_bounds (hN : 0<N) {w : ℝ} (hw : 0≤w) (F E R : ℝ)
    (z : PathLabel n→ℝ) (p : fullBuffers n N→Fin N)
    (hp : z∈ownerCell (bondLabels (n:=n) hN) p)
    (hz : z∈adaptiveDraw (n:=n) hN F E w R) :
    z∈cutBounds (cutLabels (bufferedOwner (n:=n) hN p)) F E w R := by
  refine ⟨⟨hz.1.1.1,?_⟩,hz.1.2⟩
  rw [bufferedOwner_cut (n:=n) hN p]
  intro l hl
  obtain ⟨⟨b,k⟩,_,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨j,hj⟩ := (mem_bufferBoxes hN w z).mp hz.2 b
  exact (minimum_bond_coordinate (bondLabels (n:=n) hN b) z (p b) j
    (div_nonneg hw (by norm_num : (0:ℝ)≤3)) (hp b) hj k).trans_eq (by ring)

private theorem actual_bond (ω : PathPauliDisorder) (hN : 0<N) (b : fullBuffers n N)
    (j : Fin N) (k : Fin 9) :
    pathPauliDisorderShell ω n (bondLabels (n:=n) hN b j k)=ω (candidateIndex (3*N*b.val) (j,k)) := by
  change ω (b.val*(3*N)+3*j.val,_) = ω (3*N*b.val+3*j.val,_)
  rw [Nat.mul_comm b.val]

private theorem physical_mem (ω : PathPauliDisorder) (hN : 0<N) {F E δ R : ℝ}
    (hfield : F≤∑ i : Fin (n+2), |pathPauliDisorderShell ω n (.inl (i,2))|)
    (henergy : ‖pathPauliDisorderShell ω n‖^2≤E)
    (hcap : ∀ l : PathLabel n, |pathPauliDisorderShell ω n l|≤R)
    (hw : ∀ b : fullBuffers n N, ∃ j : Fin N,
      (fun k => ω (candidateIndex (3*N*b.val) (j,k)))∈weakBond δ) :
    (fun l => pathPauliDisorderShell ω n l)∈adaptiveDraw (n:=n) hN F E (3*δ) R := by
  let z := fun l => pathPauliDisorderShell ω n l
  have hbulk : z∈drawBounds ∅ F E 0 :=
    ⟨⟨hfield,(total_energy z).symm.trans_le henergy⟩,by simp [energyOn]⟩
  refine ⟨⟨⟨hbulk,by simp⟩,hcap⟩,(mem_bufferBoxes hN (3*δ) z).mpr ?_⟩
  intro b
  obtain ⟨j,hj⟩ := hw b
  refine ⟨j,fun k => ?_⟩
  change |pathPauliDisorderShell ω n (bondLabels (n:=n) hN b j k)|≤3*δ/3
  rw [actual_bond (n:=n) ω hN b j k]
  exact (abs_le.mpr (hj k (Set.mem_univ _))).trans_eq (by ring)

/-- All selected seams and all incident coordinates satisfy their
caps on the same frozen prefix as the longitudinal and energy bounds. -/
theorem gaussian_adaptive_draw :
    ∃ u v : ℝ, 0<u ∧ 0<v ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let q := sizeRoot (n+2)
      let N := q^62
      ∀ hN : 0<N, (fun l => pathPauliDisorderShell ω n l) ∈
        adaptiveDraw (n:=n) hN (u*K) (v*K) (3*((q:ℝ)^6)⁻¹) q := by
  obtain ⟨u,v,hu,hv,hm⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨u,v,hu,hv,?_⟩
  filter_upwards [hm,gaussian_all_weak_buffers] with ω hm hw
  filter_upwards [hm,hw] with n hm hw
  intro K q N hN
  exact physical_mem (n:=n) (N:=N) ω hN (δ:=((q:ℝ)^6)⁻¹) hm.1 hm.2 hw.2 hw.1

#print axioms measurable_adaptiveDraw
#print axioms gaussian_adaptive_draw
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
