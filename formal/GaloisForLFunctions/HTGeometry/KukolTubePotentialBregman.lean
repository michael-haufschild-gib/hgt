import GaloisForLFunctions.HTGeometry.KukolTubePotentialMomentum

/-!
# Quantitative curvature of future-tube orbit potentials

Application of Kukol, *Extended Future Tube Conjecture for Unipotent Subgroups*,
arXiv:2609.10214.

These quantitative consequences are derived from the orbit quadratics used in
Proposition 3.2 and the potential in Section 4. The exact remainder, injectivity,
and distance estimates are extensions derived here, rather than named paper statements.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact translation formula retaining the positive quadratic curvature. -/
theorem kukolTubeMargin_increment (v : KukolLightCone E) (r s : ℝ) (z u w : E) :
    kukolTubeMargin v r s z w = kukolTubeMargin v r s z u-
      2*inner ℝ (kukolOrbitCoefficient r v.1 • u-kukolOrbitDrift r v.1 v.2.2 z) (w-u)-
      kukolOrbitCoefficient r v.1*‖w-u‖^2 := by
  simp only [kukolTubeMargin_quadratic,← real_inner_self_eq_norm_sq,
    inner_sub_left,inner_sub_right,inner_smul_left,RCLike.conj_to_real,real_inner_comm w u]
  ring

/-- The first-order remainder is an exact sum of two nonnegative terms. -/
theorem kukolTubeReciprocal_bregman_identity (v : KukolLightCone E) (r s : ℝ) (z : E)
    (u w : {u : E | 0 < kukolTubeMargin v r s z u}) :
    1/kukolTubeMargin v r s z w-1/kukolTubeMargin v r s z u-
      2*inner ℝ (kukolTubeForceComponent v r s z u) (w.val-u.val) =
      (kukolTubeMargin v r s z w-kukolTubeMargin v r s z u)^2/
        ((kukolTubeMargin v r s z u)^2*kukolTubeMargin v r s z w)+
      kukolOrbitCoefficient r v.1*‖w.val-u.val‖^2/(kukolTubeMargin v r s z u)^2 := by
  have hu : kukolTubeMargin v r s z u ≠ 0 := (show 0 < kukolTubeMargin v r s z u from u.property).ne'
  have hw : kukolTubeMargin v r s z w ≠ 0 := (show 0 < kukolTubeMargin v r s z w from w.property).ne'
  have hid : 1/kukolTubeMargin v r s z w-1/kukolTubeMargin v r s z u+
      (kukolTubeMargin v r s z w-kukolTubeMargin v r s z u)/(kukolTubeMargin v r s z u)^2 =
      (kukolTubeMargin v r s z w-kukolTubeMargin v r s z u)^2/
        ((kukolTubeMargin v r s z u)^2*kukolTubeMargin v r s z w) := by
    field_simp
    ring
  have hinc := kukolTubeMargin_increment v r s z u.val w.val
  have hlin : (kukolTubeMargin v r s z w-kukolTubeMargin v r s z u)/(kukolTubeMargin v r s z u)^2 =
      -2*inner ℝ (kukolTubeForceComponent v r s z u) (w.val-u.val)-
      kukolOrbitCoefficient r v.1*‖w.val-u.val‖^2/(kukolTubeMargin v r s z u)^2 := by
    conv_lhs => rw [hinc]
    simp only [kukolTubeForceComponent,inner_smul_left,RCLike.conj_to_real]
    ring
  linarith

variable [Fintype ι]

/-- A positive, explicit curvature modulus at each admissible parameter. -/
def kukolTubeCurvature (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (u : E) : ℝ :=
  ∑ i,kukolOrbitCoefficient (r i) (v i).1/(kukolTubeMargin (v i) (r i) (s i) (z i) u)^2

theorem kukolTubeCurvature_pos (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (anchor : ι) (u : kukolTubeDomain v r s z) : 0 < kukolTubeCurvature v r s z u := by
  have hp (i : ι) : 0 < kukolOrbitCoefficient (r i) (v i).1/
      (kukolTubeMargin (v i) (r i) (s i) (z i) u)^2 :=
    div_pos (kukolOrbitCoefficient_pos _ _) (sq_pos_of_pos (u.property i))
  exact (hp anchor).trans_le (Finset.single_le_sum (fun i _ => (hp i).le) (Finset.mem_univ anchor))

/-- The full potential has an explicit quadratic lower bound above every tangent plane. -/
theorem kukolTubePotential_quadratic_support (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (u w : kukolTubeDomain v r s z) :
    kukolTubePotential v r s z u+2*inner ℝ (kukolTubeForce v r s z u) (w.val-u.val)+
      kukolTubeCurvature v r s z u*‖w.val-u.val‖^2 ≤ kukolTubePotential v r s z w := by
  have hterm (i : ι) : 1/kukolTubeMargin (v i) (r i) (s i) (z i) u+
      2*inner ℝ (kukolTubeForceComponent (v i) (r i) (s i) (z i) u) (w.val-u.val)+
      (kukolOrbitCoefficient (r i) (v i).1/(kukolTubeMargin (v i) (r i) (s i) (z i) u)^2)*
        ‖w.val-u.val‖^2 ≤ 1/kukolTubeMargin (v i) (r i) (s i) (z i) w := by
    have h := kukolTubeReciprocal_bregman_identity (v i) (r i) (s i) (z i)
      ⟨u.val,u.property i⟩ ⟨w.val,w.property i⟩
    have hp : 0 ≤ (kukolTubeMargin (v i) (r i) (s i) (z i) w-
        kukolTubeMargin (v i) (r i) (s i) (z i) u)^2 /
        ((kukolTubeMargin (v i) (r i) (s i) (z i) u)^2*
          kukolTubeMargin (v i) (r i) (s i) (z i) w) :=
      div_nonneg (sq_nonneg _) (mul_pos (sq_pos_of_pos (u.property i)) (w.property i)).le
    rw [mul_div_right_comm] at h
    linarith
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  simpa only [kukolTubePotential,kukolTubeForce,kukolTubeCurvature,
    sum_inner,Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib] using h

/-- The force is quantitatively strictly monotone throughout the whole admissible domain. -/
theorem kukolTubeForce_strong_monotonicity (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (u w : kukolTubeDomain v r s z) :
    (kukolTubeCurvature v r s z u+kukolTubeCurvature v r s z w)*‖w.val-u.val‖^2 ≤
      2*inner ℝ (kukolTubeForce v r s z w-kukolTubeForce v r s z u) (w.val-u.val) := by
  have h := kukolTubePotential_quadratic_support v r s z u w
  have h' := kukolTubePotential_quadratic_support v r s z w u
  rw [norm_sub_rev u.val w.val] at h'
  have hi : inner ℝ (kukolTubeForce v r s z w) (u.val-w.val) =
      -inner ℝ (kukolTubeForce v r s z w) (w.val-u.val) := by
    simp [inner_sub_right]
  rw [hi] at h'
  simp only [inner_sub_left]
  nlinarith

/-- Distinct admissible parameters cannot have the same momentum vector. -/
theorem kukolTubeForce_injOn (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E)
    (anchor : ι) : Set.InjOn (kukolTubeForce v r s z) (kukolTubeDomain v r s z) := by
  intro u hu w hw he
  have h := kukolTubeForce_strong_monotonicity v r s z ⟨u,hu⟩ ⟨w,hw⟩
  simp only [he,sub_self,inner_zero_left,mul_zero] at h
  have hc := add_pos (kukolTubeCurvature_pos v r s z anchor ⟨u,hu⟩)
    (kukolTubeCurvature_pos v r s z anchor ⟨w,hw⟩)
  by_contra huw
  have hn : 0 < ‖w-u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huw)))
  exact (not_lt_of_ge h) (mul_pos hc hn)

variable [FiniteDimensional ℝ E]

/-- Potential excess controls squared distance to the canonical subgroup representative. -/
theorem kukolTubeMinimum_distance_bound (W : Submodule ℝ E)
    (v : ι → KukolLightCone E) (r s : ι → ℝ) (z : ι → E) (anchor : ι)
    (w : kukolConstrainedTubeDomain W v r s z) :
    kukolTubeCurvature v r s z (kukolTubeMinimizer W v r s z anchor)*
      ‖w.val-kukolTubeMinimizer W v r s z anchor‖^2 ≤
      kukolTubePotential v r s z w-kukolTubeMinimumValue W v r s z anchor := by
  have hu := kukolTubeMinimizer_spec W v r s z anchor
  have h := kukolTubePotential_quadratic_support v r s z ⟨_,hu.1.1⟩ ⟨w.val,w.property.1⟩
  have ho := (W.mem_orthogonal' _).mp (kukolTubeMinimizer_force_orthogonal W v r s z anchor)
    (w.val-kukolTubeMinimizer W v r s z anchor) (W.sub_mem w.property.2 hu.1.2)
  rw [ho,mul_zero,add_zero] at h
  exact (le_sub_iff_add_le).mpr (by simpa only [kukolTubeMinimumValue,add_comm] using h)

end GaloisForLFunctions.HTGeometry
