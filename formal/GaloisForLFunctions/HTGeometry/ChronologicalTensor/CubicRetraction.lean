import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicComplex

/-!
# Strong deformation of the cubic norming complex

Transfer the middle gap equally to the two outer gaps. This continuous
homotopy preserves the physical sparse unit complex, ends with middle gap
zero, and fixes that subcomplex throughout. The maps form a retraction and
an actual mathlib HomotopyRel, not merely a pointwise interpolation formula.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set

def cubicRingSection : Set (Fin 5 → ℝ) := {g ∈ cubicProbeSection | g 2=0}

def cubicCollapse (t : ℝ) (g : Fin 5 → ℝ) : Fin 5 → ℝ :=
  ![g 0+t*g 2/2,g 1,(1-t)*g 2,g 3,g 4+t*g 2/2]

theorem cubicCollapse_zero (g : Fin 5 → ℝ) : cubicCollapse 0 g=g := by
  ext q
  fin_cases q <;> simp [cubicCollapse]

theorem cubicCollapse_fixed (t : ℝ) :
    Set.EqOn (cubicCollapse t) id cubicRingSection := by
  intro g hg
  ext q
  fin_cases q <;> simp [cubicCollapse,hg.2]

theorem cubicCollapse_preserves :
    ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (cubicCollapse t) cubicProbeSection cubicProbeSection := by
  intro t ht g hg
  rcases hg with ⟨hnn,hsum,h01,h12,h23,h34⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro q
    fin_cases q
    · exact add_nonneg (hnn 0) (div_nonneg (mul_nonneg ht.1 (hnn 2)) (by positivity))
    · exact hnn 1
    · exact mul_nonneg (sub_nonneg.mpr ht.2) (hnn 2)
    · exact hnn 3
    · exact add_nonneg (hnn 4) (div_nonneg (mul_nonneg ht.1 (hnn 2)) (by positivity))
  · change (g 0+t*g 2/2)+g 1+(1-t)*g 2+g 3+(g 4+t*g 2/2)=1
    linarith only [hsum]
  · change (g 0+t*g 2/2)*g 1=0
    linear_combination h01+t/2*h12
  · change g 1*((1-t)*g 2)=0
    linear_combination (1-t)*h12
  · change (1-t)*g 2*g 3=0
    linear_combination (1-t)*h23
  · change g 3*(g 4+t*g 2/2)=0
    linear_combination h34+t/2*h23

theorem cubicCollapse_ends : MapsTo (cubicCollapse 1) cubicProbeSection cubicRingSection := by
  intro g hg
  refine ⟨cubicCollapse_preserves 1 ⟨zero_le_one,le_rfl⟩ hg,?_⟩
  simp [cubicCollapse]

theorem cubicCollapse_continuous :
    Continuous (fun p : ℝ × (Fin 5 → ℝ) => cubicCollapse p.1 p.2) := by
  apply continuous_pi
  intro q
  fin_cases q <;> simp only [cubicCollapse]
  all_goals fun_prop

def cubicRetraction : C(cubicProbeSection,cubicRingSection) where
  toFun g := ⟨cubicCollapse 1 g,cubicCollapse_ends g.property⟩
  continuous_toFun := (cubicCollapse_continuous.comp
    (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

def cubicRingInclusion : C(cubicRingSection,cubicProbeSection) where
  toFun g := ⟨g.val,g.property.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem cubicRetraction_section :
    cubicRetraction.comp cubicRingInclusion=ContinuousMap.id cubicRingSection := by
  apply ContinuousMap.ext
  intro g
  apply Subtype.ext
  exact cubicCollapse_fixed 1 g.property

def cubicRetractionHomotopy :
    (ContinuousMap.id cubicProbeSection).HomotopyRel
      (cubicRingInclusion.comp cubicRetraction) {g | g.val 2=0} where
  toFun p := ⟨cubicCollapse p.1.val p.2.val,
    cubicCollapse_preserves p.1.val p.1.property p.2.property⟩
  continuous_toFun := (cubicCollapse_continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left g := Subtype.ext (cubicCollapse_zero g.val)
  map_one_left _ := rfl
  prop' t g hg := Subtype.ext (cubicCollapse_fixed t.val ⟨g.property,hg⟩)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
