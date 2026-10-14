import GaloisForLFunctions.HTGeometry.UnitGramResolvent
import GaloisForLFunctions.HTGeometry.PaperCoordinateCompression

/-! # Actual prefix Gram inverses converge strongly

For the literal prefix projection `P_N`, the operator
`1 + (G P_N)* (G P_N)` is `1 + P_N G*G P_N`. Its inverse is uniformly
contractive and converges strongly to the inverse of `1 + G*G`.
Composing with `P_N` gives the inverse extended by zero off the prefix.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem unitGramOperator_prefix (G : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    unitGramOperator (G ∘L paperCoordinateProjection N) =
      1 + paperCoordinateCompression (adjoint G ∘L G) N := by
  change 1 + adjoint (G ∘L paperCoordinateProjection N) ∘L
      (G ∘L paperCoordinateProjection N) =
    1 + paperCoordinateProjection N ∘L (adjoint G ∘L G) ∘L paperCoordinateProjection N
  rw [adjoint_comp, adjoint_paperCoordinateProjection]
  simp only [ContinuousLinearMap.comp_assoc]

def prefixGramResolvent (G : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    VecSeq E →L[ℂ] VecSeq E := unitGramResolvent (G ∘L paperCoordinateProjection N)

def prefixGramInverse (G : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    VecSeq E →L[ℂ] VecSeq E := prefixGramResolvent G N ∘L paperCoordinateProjection N

theorem norm_prefixGramResolvent_apply_le (G : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) (x : VecSeq E) :
    ‖prefixGramResolvent G N x‖ ≤ ‖x‖ := norm_unitGramResolvent_apply_le _ _

theorem norm_prefixGramResolvent_le (G : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    ‖prefixGramResolvent G N‖ ≤ 1 := norm_unitGramResolvent_le _

theorem norm_prefixGramInverse_apply_le (G : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) (x : VecSeq E) :
    ‖prefixGramInverse G N x‖ ≤ ‖x‖ :=
  (norm_prefixGramResolvent_apply_le G N _).trans (norm_paperCoordinateProjection_apply_le N x)

theorem norm_prefixGramInverse_le (G : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    ‖prefixGramInverse G N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using norm_prefixGramInverse_apply_le G N x

theorem prefixGramInverse_equation (G : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) (x : VecSeq E) :
    (1 + paperCoordinateCompression (adjoint G ∘L G) N) (prefixGramInverse G N x) =
      paperCoordinateProjection N x := by
  rw [← unitGramOperator_prefix]
  exact unitGramOperator_resolvent_apply _ _

theorem prefixGramResolvent_coordinate_outside (G : VecSeq E →L[ℂ] VecSeq E)
    (N : ℕ) (x : VecSeq E) (i : ℕ) (hi : ¬ i < N) :
    prefixGramResolvent G N x i = x i := by
  have h := congrArg (fun y : VecSeq E => y i)
    (unitGramOperator_resolvent_apply (G ∘L paperCoordinateProjection N) x)
  rw [unitGramOperator_prefix] at h
  change prefixGramResolvent G N x i +
    paperCoordinateCompression (adjoint G ∘L G) N (prefixGramResolvent G N x) i = x i at h
  simpa only [
    paperCoordinateCompression, ContinuousLinearMap.comp_apply,
    paperCoordinateProjection_coordinate, if_neg hi, add_zero] using h

theorem prefixGramInverse_coordinate_outside (G : VecSeq E →L[ℂ] VecSeq E)
    (N : ℕ) (x : VecSeq E) (i : ℕ) (hi : ¬ i < N) :
    prefixGramInverse G N x i = 0 := by
  change prefixGramResolvent G N (paperCoordinateProjection N x) i = 0
  rw [prefixGramResolvent_coordinate_outside G N _ i hi,
    paperCoordinateProjection_coordinate, if_neg hi]

theorem tendsto_unitGramOperator_prefix (G : VecSeq E →L[ℂ] VecSeq E) (x : VecSeq E) :
    Tendsto (fun N => unitGramOperator (G ∘L paperCoordinateProjection N) x) atTop
      (𝓝 (unitGramOperator G x)) := by
  simp only [unitGramOperator_prefix, add_apply]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).add
    (tendsto_paperCoordinateCompression (adjoint G ∘L G) x)

theorem tendsto_prefixGramResolvent (G : VecSeq E →L[ℂ] VecSeq E) (x : VecSeq E) :
    Tendsto (fun N => prefixGramResolvent G N x) atTop (𝓝 (unitGramResolvent G x)) :=
  unitGramResolvent_strong_limit _ G (tendsto_unitGramOperator_prefix G) x

theorem tendsto_prefixGramInverse (G : VecSeq E →L[ℂ] VecSeq E) (x : VecSeq E) :
    Tendsto (fun N => prefixGramInverse G N x) atTop (𝓝 (unitGramResolvent G x)) := by
  have hres : Tendsto (fun N => paperCoordinateProjection N x -
      unitGramOperator (G ∘L paperCoordinateProjection N) (unitGramResolvent G x)) atTop (𝓝 0) := by
    simpa only [unitGramOperator_resolvent_apply, sub_self] using
      (tendsto_paperCoordinateProjection x).sub
        (tendsto_unitGramOperator_prefix G (unitGramResolvent G x))
  have heq (N : ℕ) : prefixGramInverse G N x - unitGramResolvent G x =
      prefixGramResolvent G N (paperCoordinateProjection N x -
        unitGramOperator (G ∘L paperCoordinateProjection N) (unitGramResolvent G x)) := by
    rw [map_sub]
    change _ = prefixGramInverse G N x -
      unitGramResolvent (G ∘L paperCoordinateProjection N)
        (unitGramOperator (G ∘L paperCoordinateProjection N) (unitGramResolvent G x))
    rw [unitGramResolvent_operator_apply]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
    (by simpa only [norm_zero] using hres.norm)
  rw [heq]
  exact norm_prefixGramResolvent_apply_le G N _

end
end GaloisForLFunctions.HTGeometry
