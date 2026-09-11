import GaloisForLFunctions.HTGeometry.KukolTubePotentialBregman
import GaloisForLFunctions.HTGeometry.KukolJointFamilyMinimum

/-!
# Quantitative cost of incompatible canonical parameters

Application of Kukol, *Extended Future Tube Conjecture for Unipotent Subgroups*,
arXiv:2609.10214.

This derived application combines the orbit-potential curvature with a weighted
inner-product identity to bound joint excess by separation of the individual minima.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ]

/-- The joint compromise cost bounds the curvature-weighted separation of the two canonical parameters. -/
theorem kukolTubeMinimumValue_joint_separation (W : Submodule ℝ E)
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (anchor : ι)
    (v' : κ → KukolLightCone E) (r' s' : κ → ℝ) (z' : κ → E) (anchor' : κ) :
    let a := kukolTubeMinimizer W v r s z anchor
    let b := kukolTubeMinimizer W v' r' s' z' anchor'
    let c := kukolTubeCurvature v r s z a
    let d := kukolTubeCurvature v' r' s' z' b
    c*d/(c+d)*‖a-b‖^2 ≤
      kukolTubeMinimumValue W (Sum.elim v v') (Sum.elim r r') (Sum.elim s s') (Sum.elim z z')
        (Sum.inl anchor)-
        (kukolTubeMinimumValue W v r s z anchor+kukolTubeMinimumValue W v' r' s' z' anchor') := by
  dsimp only
  let a := kukolTubeMinimizer W v r s z anchor
  let b := kukolTubeMinimizer W v' r' s' z' anchor'
  let c := kukolTubeCurvature v r s z a
  let d := kukolTubeCurvature v' r' s' z' b
  let x := kukolTubeMinimizer W (Sum.elim v v') (Sum.elim r r')
    (Sum.elim s s') (Sum.elim z z') (Sum.inl anchor)
  have hx : x ∈ kukolConstrainedTubeDomain W v r s z ∩ kukolConstrainedTubeDomain W v' r' s' z' := by
    simpa only [kukolConstrainedTubeDomain_sum_family] using
      (kukolTubeMinimizer_spec W (Sum.elim v v') (Sum.elim r r')
        (Sum.elim s s') (Sum.elim z z') (Sum.inl anchor)).1
  have ha := kukolTubeMinimizer_spec W v r s z anchor
  have hb := kukolTubeMinimizer_spec W v' r' s' z' anchor'
  have hc : 0 < c := kukolTubeCurvature_pos v r s z anchor ⟨a,ha.1.1⟩
  have hd : 0 < d := kukolTubeCurvature_pos v' r' s' z' anchor' ⟨b,hb.1.1⟩
  have haBound := kukolTubeMinimum_distance_bound W v r s z anchor ⟨x,hx.1⟩
  have hbBound := kukolTubeMinimum_distance_bound W v' r' s' z' anchor' ⟨x,hx.2⟩
  have hid : (c+d)*(c*‖x-a‖^2+d*‖x-b‖^2)-c*d*‖a-b‖^2 =
      ‖c • (x-a)+d • (x-b)‖^2 := by
    simp only [← real_inner_self_eq_norm_sq,inner_add_left,inner_add_right,
      inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,RCLike.conj_to_real,
      real_inner_comm b a,real_inner_comm x a,real_inner_comm x b]
    ring
  have hsep : c*d/(c+d)*‖a-b‖^2 ≤ c*‖x-a‖^2+d*‖x-b‖^2 := by
    rw [div_mul_eq_mul_div,div_le_iff₀ (add_pos hc hd)]
    nlinarith [sq_nonneg ‖c • (x-a)+d • (x-b)‖]
  change c*‖x-a‖^2 ≤ kukolTubePotential v r s z x-kukolTubeMinimumValue W v r s z anchor at haBound
  change d*‖x-b‖^2 ≤ kukolTubePotential v' r' s' z' x-kukolTubeMinimumValue W v' r' s' z' anchor' at hbBound
  change c*d/(c+d)*‖a-b‖^2 ≤
    kukolTubePotential (Sum.elim v v') (Sum.elim r r') (Sum.elim s s') (Sum.elim z z') x-_
  rw [kukolTubePotential_sum_family]
  linarith

end GaloisForLFunctions.HTGeometry
