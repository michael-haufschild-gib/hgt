import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PhysicalTransfer
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.TypicalBuffers

/-! # Typical membership in the adaptively selected physical event -/

open MeasureTheory Finset Filter Set Real
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n N : ℕ}

theorem measurable_adaptiveDraw (hN : 0<N) (F E w R : ℝ) :
    MeasurableSet (adaptiveDraw (n:=n) hN F E w R) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  let L := bondLabels (n:=n) hN
  let Z p := cutBounds (cutLabels (bufferedOwner hN p)) F E w R
  have he : adaptiveDraw hN F E w R=⋃ p, ownerCell L p ∩ Z p := by
    ext z
    constructor
    · intro h
      exact mem_iUnion.mpr ⟨owners L z,(ownerCell_iff ..).mpr rfl,h⟩
    · intro h
      obtain ⟨p,hp,hz⟩ := mem_iUnion.mp h
      change z∈Z (owners L z)
      rwa [←(ownerCell_iff L p z).mp hp]
  rw [he]
  exact MeasurableSet.iUnion fun p => (measurable_ownerCell L p).inter (measurable_cutBounds ..)

private theorem actual_bond (ω : PathPauliDisorder) (hN : 0<N) (b : fullBuffers n N)
    (j : Fin N) (k : Fin 9) :
    pathPauliDisorderShell ω n (bondLabels hN b j k)=ω (candidateIndex (3*N*b.val) (j,k)) := by
  change ω (b.val*(3*N)+3*j.val,_) = ω (3*N*b.val+3*j.val,_)
  rw [Nat.mul_comm b.val]

/-- All selected seams and all incident coordinates satisfy their
caps on the same frozen prefix as the longitudinal and energy bounds. -/
theorem gaussian_adaptive_draw :
    ∃ u v : ℝ, 0<u ∧ 0<v ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let q := sizeRoot (n+2)
      let N := q^62
      ∀ hN : 0<N, (fun l => pathPauliDisorderShell ω n l) ∈
        adaptiveDraw hN (u*K) (v*K) (3*((q:ℝ)^6)⁻¹) q := by
  obtain ⟨u,v,hu,hv,hm⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨u,v,hu,hv,?_⟩
  filter_upwards [hm,gaussian_all_weak_buffers] with ω hm hw
  filter_upwards [hm,hw] with n hm hw
  intro K q N hN
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  let z := fun l => pathPauliDisorderShell ω n l
  let L := bondLabels (n:=n) hN
  let p := owners L z
  have hmin := (ownerCell_iff L p z).mpr rfl
  change z∈cutBounds (cutLabels (bufferedOwner hN p)) (u*K) (v*K) (3*((q:ℝ)^6)⁻¹) q
  refine ⟨⟨⟨⟨hm.1,(total_energy z).symm.trans_le hm.2⟩,by simp [energyOn]⟩,?_⟩,hw.2⟩
  rw [bufferedOwner_cut]
  rintro l hl
  obtain ⟨⟨b,k⟩,_,rfl⟩ := mem_image.mp hl
  obtain ⟨j,hj⟩ := hw.1 b
  apply minimum_bond_coordinate (L b) z (p b) j (by positivity) (hmin b) _ k
  intro d
  rw [show z (L b j d)=_ from actual_bond ω hN b j d]
  exact abs_le.mpr (hj d (Set.mem_univ _))

#print axioms measurable_adaptiveDraw
#print axioms gaussian_adaptive_draw
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
