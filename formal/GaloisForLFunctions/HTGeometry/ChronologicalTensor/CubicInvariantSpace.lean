import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicExtended
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The minimal invariant space of cubic observations

The original and extended coefficient maps embed in functions on the actual
physical section. Intersecting all flow-invariant subspaces containing the
original observations gives exactly the extended space. The half-flow recovery
forces the additional mode. The two actual dimensions are five and six.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set


def cubicObservationMap : (Fin 5 → ℝ) →ₗ[ℝ] (cubicProbeSection → ℝ) where
  toFun c g := cubicReadout (c 0) (c 1) (c 2) (c 3) (c 4) g.val
  map_add' c d := by ext g; simp [cubicReadout]; ring
  map_smul' k c := by ext g; simp [cubicReadout]; ring

def cubicExtendedObservationMap : (Fin 6 → ℝ) →ₗ[ℝ] (cubicProbeSection → ℝ) where
  toFun c g := cubicExtendedReadout (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) g.val
  map_add' c d := by ext g; simp [cubicExtendedReadout,cubicReadout]; ring
  map_smul' k c := by ext g; simp [cubicExtendedReadout,cubicReadout]; ring

def cubicObservationSpace : Submodule ℝ (cubicProbeSection → ℝ) := cubicObservationMap.range

def cubicFlowObservationSpace : Submodule ℝ (cubicProbeSection → ℝ) := cubicExtendedObservationMap.range

def cubicSectionPullback (q : Icc (0:ℝ) 1) :
    (cubicProbeSection → ℝ) →ₗ[ℝ] (cubicProbeSection → ℝ) where
  toFun f g := f ⟨cubicFlow q g.val,cubicFlow_preserves q q.property g.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cubicInvariantSpaces : Set (Submodule ℝ (cubicProbeSection → ℝ)) :=
  {S | cubicObservationSpace ≤ S ∧ ∀ q : Icc (0:ℝ) 1, MapsTo (cubicSectionPullback q) S S}

def cubicInvariantHull : Submodule ℝ (cubicProbeSection → ℝ) := sInf cubicInvariantSpaces

def cubicLostCubicObservation (g : cubicProbeSection) : ℝ := cubicDecayMode 2 g.val

theorem cubicObservationMap_injective : Function.Injective cubicObservationMap := by
  intro c d h
  have hz : EqOn (cubicReadout (c 0-d 0) (c 1-d 1) (c 2-d 2) (c 3-d 3) (c 4-d 4))
      (fun _ => 0) cubicProbeSection := by
    intro g hg
    have he := congrFun h ⟨g,hg⟩
    change cubicReadout (c 0) (c 1) (c 2) (c 3) (c 4) g=
      cubicReadout (d 0) (d 1) (d 2) (d 3) (d 4) g at he
    dsimp only
    unfold cubicReadout at *
    linear_combination he
  rcases (cubicReadout_section_kernel _ _ _ _ _).mp hz with ⟨h0,h1,h2,h3,h4⟩
  ext i
  fin_cases i
  all_goals first | exact sub_eq_zero.mp h0 | exact sub_eq_zero.mp h1 |
    exact sub_eq_zero.mp h2 | exact sub_eq_zero.mp h3 | exact sub_eq_zero.mp h4

theorem cubicExtendedObservationMap_injective : Function.Injective cubicExtendedObservationMap := by
  intro c d h
  have hz : EqOn (cubicExtendedReadout (c 0-d 0) (c 1-d 1) (c 2-d 2)
      (c 3-d 3) (c 4-d 4) (c 5-d 5)) (fun _ => 0) cubicProbeSection := by
    intro g hg
    have he := congrFun h ⟨g,hg⟩
    change cubicExtendedReadout (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) g=
      cubicExtendedReadout (d 0) (d 1) (d 2) (d 3) (d 4) (d 5) g at he
    dsimp only
    unfold cubicExtendedReadout cubicReadout at *
    linear_combination he
  rcases (cubicExtendedReadout_kernel _ _ _ _ _ _).mp hz with ⟨h0,h1,h2,h3,h4,h5⟩
  ext i
  fin_cases i
  all_goals first | exact sub_eq_zero.mp h0 | exact sub_eq_zero.mp h1 |
    exact sub_eq_zero.mp h2 | exact sub_eq_zero.mp h3 | exact sub_eq_zero.mp h4 |
    exact sub_eq_zero.mp h5

theorem cubicObservationSpace_le_flowSpace : cubicObservationSpace ≤ cubicFlowObservationSpace := by
  rintro f ⟨c,rfl⟩
  refine ⟨![c 0,c 1,c 2,c 3,c 4,0],?_⟩
  ext g
  simp [cubicExtendedObservationMap,cubicObservationMap,cubicExtendedReadout]

theorem cubicFlowObservationSpace_invariant (q : Icc (0:ℝ) 1) :
    MapsTo (cubicSectionPullback q) cubicFlowObservationSpace cubicFlowObservationSpace := by
  rintro f ⟨c,rfl⟩
  refine ⟨![q.val*c 0,c 1,c 2,c 3,q.val^2*c 4+q.val*(1-q.val)*c 0/2,
    q.val^3*c 5-q.val*(1-q.val^2)*c 0/4],?_⟩
  ext g
  exact (cubicExtendedReadout_flow q (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) g.property).symm

theorem cubicObservationSpace_le_hull : cubicObservationSpace ≤ cubicInvariantHull := by
  intro f hf
  apply Submodule.mem_sInf.mpr
  intro S hS
  exact hS.1 hf

theorem cubicLostCubicObservation_mem_hull : cubicLostCubicObservation ∈ cubicInvariantHull := by
  apply Submodule.mem_sInf.mpr
  intro S hS
  let fA : cubicProbeSection → ℝ := fun g => cubicDecayReadout 1 0 0 g.val
  let fE : cubicProbeSection → ℝ := fun g => cubicDecayMode 1 g.val
  have hA : fA ∈ cubicObservationSpace := by
    refine ⟨![1,0,0,0,0],?_⟩
    ext g
    exact cubicDecayReadout_pairing 1 0 g.property
  have hE : fE ∈ cubicObservationSpace := by
    refine ⟨![0,0,0,0,1],?_⟩
    ext g
    change cubicReadout 0 0 0 0 1 g.val=cubicDecayMode 1 g.val
    rw [cubicDecayReadout_pairing 0 1 g.property]
    simp [cubicDecayReadout,cubicDecayMode]
  let q : Icc (0:ℝ) 1 := ⟨1/2,by constructor <;> linarith⟩
  have hcomb := S.smul_mem (32/3 : ℝ)
    (S.sub_mem (S.add_mem (S.smul_mem (1/2 : ℝ) (hS.1 hA))
      (S.smul_mem (1/8 : ℝ) (hS.1 hE))) (hS.2 q (hS.1 hA)))
  have he : (32/3 : ℝ) • ((1/2 : ℝ) • fA+(1/8 : ℝ) • fE-cubicSectionPullback q fA)=
      cubicLostCubicObservation := by
    ext g
    change (32/3)*((1/2)*cubicDecayReadout 1 0 0 g.val+(1/8)*cubicDecayMode 1 g.val-
      cubicDecayReadout 1 0 0 (cubicFlow (1/2) g.val))=cubicDecayMode 2 g.val
    exact (cubicDecayReadout_recover_cubic g.property).symm
  rwa [he] at hcomb

theorem cubicInvariantHull_eq : cubicInvariantHull=cubicFlowObservationSpace := by
  apply le_antisymm
  · exact sInf_le ⟨cubicObservationSpace_le_flowSpace,cubicFlowObservationSpace_invariant⟩
  · rintro f ⟨c,rfl⟩
    have hbase : cubicObservationMap ![c 0,c 1,c 2,c 3,c 4] ∈ cubicInvariantHull :=
      cubicObservationSpace_le_hull ⟨![c 0,c 1,c 2,c 3,c 4],rfl⟩
    have h := cubicInvariantHull.add_mem hbase
      (cubicInvariantHull.smul_mem (c 5) cubicLostCubicObservation_mem_hull)
    convert h using 1
    ext g
    simp [cubicExtendedObservationMap,cubicObservationMap,cubicExtendedReadout,
      cubicLostCubicObservation,cubicDecayMode]

theorem cubicObservationSpace_finrank : Module.finrank ℝ cubicObservationSpace=5 := by
  exact (LinearMap.finrank_range_of_inj cubicObservationMap_injective).trans
    (Module.finrank_fin_fun (R := ℝ))

theorem cubicInvariantHull_finrank : Module.finrank ℝ cubicInvariantHull=6 := by
  rw [cubicInvariantHull_eq]
  exact (LinearMap.finrank_range_of_inj cubicExtendedObservationMap_injective).trans
    (Module.finrank_fin_fun (R := ℝ))

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
