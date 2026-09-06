import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspAlgebra

/-!
# The cusp algebra selected by observations lost under retraction

Intersect the smallest invariant observation space with the kernel of the final
ring retraction. This canonically defined lost space has dimension three and is
exactly the span of the decay modes. Its generated unital algebra is the actual
cusp observation algebra. No choice of eigenfunctions enters its definition.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set


def cubicDecayObservationMap : (Fin 3 → ℝ) →ₗ[ℝ] (cubicProbeSection → ℝ) where
  toFun c g := c 0*cubicDecayMode 0 g.val+c 1*cubicDecayMode 1 g.val+c 2*cubicDecayMode 2 g.val
  map_add' c d := by ext g; simp; ring
  map_smul' k c := by ext g; simp; ring

def cubicLostObservationSpace : Submodule ℝ (cubicProbeSection → ℝ) :=
  cubicInvariantHull ⊓ (cubicSectionPullback ⟨0,by constructor <;> simp⟩).ker

theorem cubicDecayObservationMap_extended (c : Fin 3 → ℝ) :
    cubicDecayObservationMap c=
      cubicExtendedObservationMap ![c 0,0,0,0,c 1+c 0/2,c 2-c 0/4] := by
  ext g
  change _=cubicExtendedReadout (c 0) 0 0 0 (c 1+c 0/2) (c 2-c 0/4) g.val
  rw [cubicExtendedReadout_split _ _ _ _ _ _ g.property]
  dsimp only
  rw [cubicDecayReadout_spectral _ _ _ g.property]
  simp [cubicReadout,cubicDecayObservationMap]

theorem cubicDecayObservationMap_injective : Function.Injective cubicDecayObservationMap := by
  intro c d h
  rw [cubicDecayObservationMap_extended,cubicDecayObservationMap_extended] at h
  have he := cubicExtendedObservationMap_injective h
  have h0 := congrFun he 0
  have h4 := congrFun he 4
  have h5 := congrFun he 5
  change c 0=d 0 at h0
  change c 1+c 0/2=d 1+d 0/2 at h4
  change c 2-c 0/4=d 2-d 0/4 at h5
  have h1 : c 1=d 1 := by linarith
  have h2 : c 2=d 2 := by linarith
  ext i
  fin_cases i
  all_goals first | exact h0 | exact h1 | exact h2

theorem cubicDecayObservationMap_lost (c : Fin 3 → ℝ) :
    cubicDecayObservationMap c ∈ cubicLostObservationSpace := by
  constructor
  · rw [cubicInvariantHull_eq,cubicDecayObservationMap_extended]
    exact ⟨_,rfl⟩
  · change cubicSectionPullback ⟨0,by constructor <;> simp⟩ (cubicDecayObservationMap c)=0
    ext g
    change c 0*cubicDecayMode 0 (cubicFlow 0 g.val)+
      c 1*cubicDecayMode 1 (cubicFlow 0 g.val)+c 2*cubicDecayMode 2 (cubicFlow 0 g.val)=0
    simp [cubicDecayMode_spectrum]

theorem cubicLostObservationSpace_range : cubicLostObservationSpace=cubicDecayObservationMap.range := by
  apply le_antisymm
  · rintro f ⟨hW,hzero⟩
    rw [cubicInvariantHull_eq] at hW
    rcases hW with ⟨c,rfl⟩
    change cubicSectionPullback ⟨0,by constructor <;> simp⟩ (cubicExtendedObservationMap c)=0 at hzero
    have he : EqOn (cubicExtendedReadout 0 (c 1) (c 2) (c 3) 0 0) (fun _ => 0) cubicProbeSection := by
      intro g hg
      have hz := congrFun hzero ⟨g,hg⟩
      change cubicExtendedReadout (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (cubicFlow 0 g)=0 at hz
      have hf := cubicExtendedReadout_flow ⟨0,by constructor <;> simp⟩ (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) hg
      dsimp only at hf
      simpa using hf.symm.trans hz
    have hk := (cubicExtendedReadout_kernel _ _ _ _ _ _).mp he
    have hB : c 1=0 := hk.2.1
    have hC : c 2=0 := hk.2.2.1
    have hD : c 3=0 := hk.2.2.2.1
    refine ⟨![c 0,c 4-c 0/2,c 5+c 0/4],?_⟩
    rw [cubicDecayObservationMap_extended]
    apply congrArg cubicExtendedObservationMap
    ext i
    fin_cases i <;> simp [hB,hC,hD]
  · rintro f ⟨c,rfl⟩
    exact cubicDecayObservationMap_lost c

theorem cubicLostObservationSpace_finrank : Module.finrank ℝ cubicLostObservationSpace=3 := by
  rw [cubicLostObservationSpace_range]
  exact (LinearMap.finrank_range_of_inj cubicDecayObservationMap_injective).trans
    (Module.finrank_fin_fun (R := ℝ))

def cubicCanonicalLossAlgebra : Subalgebra ℝ (cubicProbeSection → ℝ) :=
  Algebra.adjoin ℝ (cubicLostObservationSpace : Set (cubicProbeSection → ℝ))

theorem cubicCanonicalLossAlgebra_eq : cubicCanonicalLossAlgebra=cubicDecayObservationAlgebra := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    intro f hf
    rw [cubicLostObservationSpace_range] at hf
    rcases hf with ⟨c,rfl⟩
    have h0 : (fun g : cubicProbeSection => cubicDecayMode 0 g.val) ∈ cubicDecayObservationAlgebra :=
      Algebra.subset_adjoin (by left; rfl)
    have h1 : (fun g : cubicProbeSection => cubicDecayMode 1 g.val) ∈ cubicDecayObservationAlgebra :=
      Algebra.subset_adjoin (by right; left; rfl)
    have h2 : (fun g : cubicProbeSection => cubicDecayMode 2 g.val) ∈ cubicDecayObservationAlgebra :=
      Algebra.subset_adjoin (by right; right; rfl)
    exact cubicDecayObservationAlgebra.add_mem
      (cubicDecayObservationAlgebra.add_mem (cubicDecayObservationAlgebra.smul_mem h0 (c 0))
        (cubicDecayObservationAlgebra.smul_mem h1 (c 1)))
      (cubicDecayObservationAlgebra.smul_mem h2 (c 2))
  · apply Algebra.adjoin_le
    intro f hf
    rcases hf with rfl | rfl | rfl
    · apply Algebra.subset_adjoin
      simpa [cubicDecayObservationMap] using cubicDecayObservationMap_lost ![1,0,0]
    · apply Algebra.subset_adjoin
      simpa [cubicDecayObservationMap] using cubicDecayObservationMap_lost ![0,1,0]
    · apply Algebra.subset_adjoin
      simpa [cubicDecayObservationMap] using cubicDecayObservationMap_lost ![0,0,1]

theorem cubicCanonicalLossAlgebra_cusp :
    cubicCuspAlgebra.map cubicPolynomialObservation=cubicCanonicalLossAlgebra := by
  rw [cubicCanonicalLossAlgebra_eq]
  exact cubicDecayObservationAlgebra_presentation

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
