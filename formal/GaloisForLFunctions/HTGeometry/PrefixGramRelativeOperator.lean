import GaloisForLFunctions.HTGeometry.PrefixGramResolvent
import GaloisForLFunctions.RHTower.StrongTraceNormMultiplierLimit
import GaloisForLFunctions.RHTower.TraceNormLimit
import Mathlib.Tactic.NoncommRing

/-! # Trace-norm convergence of actual relative Gram sections

The inverse of the reference prefix Gram operator acts on the literal
two-sided compression of the Gram difference. Uniformly contractive strong
inverse convergence upgrades to trace-norm convergence through that fixed
trace-class difference.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap _root_.RHTower Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def prefixGramRelativeOperator (G H : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    VecSeq E →L[ℂ] VecSeq E :=
  prefixGramInverse H N ∘L (unitGramOperator G - unitGramOperator H) ∘L
    paperCoordinateProjection N

theorem prefixGramRelativeOperator_schatten (G H : VecSeq E →L[ℂ] VecSeq E)
    (h : MemSchattenClass 1 (unitGramOperator G - unitGramOperator H)) (N : ℕ) :
    MemSchattenClass 1 (prefixGramRelativeOperator G H N) := by
  unfold prefixGramRelativeOperator
  exact memSchattenClass_one_comp_right
    (memSchattenClass_one_comp_left h (prefixGramInverse H N)) (paperCoordinateProjection N)

theorem prefixGramRelativeOperator_equation (G H : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    unitGramOperator (H ∘L paperCoordinateProjection N) * prefixGramRelativeOperator G H N =
      unitGramOperator (G ∘L paperCoordinateProjection N) -
        unitGramOperator (H ∘L paperCoordinateProjection N) := by
  have he : unitGramOperator (H ∘L paperCoordinateProjection N) *
      prefixGramInverse H N = paperCoordinateProjection N := by
    apply ContinuousLinearMap.ext
    intro x
    exact unitGramOperator_resolvent_apply (H ∘L paperCoordinateProjection N)
      (paperCoordinateProjection N x)
  change unitGramOperator (H ∘L paperCoordinateProjection N) *
      ((prefixGramInverse H N * (unitGramOperator G - unitGramOperator H)) *
        paperCoordinateProjection N) = _
  rw [← mul_assoc, ← mul_assoc, he, unitGramOperator_prefix, unitGramOperator_prefix]
  change paperCoordinateProjection N * ((1 + adjoint G * G) - (1 + adjoint H * H)) *
      paperCoordinateProjection N =
    (1 + paperCoordinateProjection N * (adjoint G * G) * paperCoordinateProjection N) -
      (1 + paperCoordinateProjection N * (adjoint H * H) * paperCoordinateProjection N)
  noncomm_ring

theorem prefixGramRelativeOperator_eq_resolvent_sub
    (G H : VecSeq E →L[ℂ] VecSeq E) (N : ℕ) :
    prefixGramRelativeOperator G H N = prefixGramResolvent H N *
      (unitGramOperator (G ∘L paperCoordinateProjection N) -
        unitGramOperator (H ∘L paperCoordinateProjection N)) := by
  rw [← prefixGramRelativeOperator_equation, ← mul_assoc]
  change _ = (unitGramResolvent (H ∘L paperCoordinateProjection N) *
    unitGramOperator (H ∘L paperCoordinateProjection N)) * _
  rw [unitGramResolvent_mul_operator, one_mul]

theorem tendsto_traceNorm_prefixGramRelativeOperator
    (G H : VecSeq E →L[ℂ] VecSeq E)
    (h : MemSchattenClass 1 (unitGramOperator G - unitGramOperator H)) :
    Tendsto (fun N => traceNorm (VecSeq E) (prefixGramRelativeOperator G H N -
      unitGramResolvent H ∘L (unitGramOperator G - unitGramOperator H))) atTop (𝓝 0) := by
  let D := unitGramOperator G - unitGramOperator H
  let L := fun N => (prefixGramInverse H N - unitGramResolvent H) ∘L D
  let R := fun N => D ∘L (paperCoordinateProjection N - 1)
  have hL (N : ℕ) : MemSchattenClass 1 (L N) := memSchattenClass_one_comp_left h _
  have hR (N : ℕ) : MemSchattenClass 1 (R N) := memSchattenClass_one_comp_right h _
  have htL : Tendsto (fun N => traceNorm (VecSeq E) (L N)) atTop (𝓝 0) :=
    traceNorm_comp_tendsto_of_strong_tendsto_of_uniform_bound h.one_isTraceClass 1 zero_le_one
      (Eventually.of_forall (norm_prefixGramInverse_le H)) (tendsto_prefixGramInverse H)
  have htR : Tendsto (fun N => traceNorm (VecSeq E) (R N)) atTop (𝓝 0) := by
    apply traceNorm_comp_right_tendsto_of_adjoint_strong_tendsto_of_uniform_bound
      h.one_isTraceClass 1 zero_le_one
      (Eventually.of_forall norm_paperCoordinateProjection_le)
    intro x
    simp only [adjoint_paperCoordinateProjection, adjoint_one]
    change Tendsto (fun N => paperCoordinateProjection N x) atTop (𝓝 x)
    exact tendsto_paperCoordinateProjection x
  have ht : Tendsto (fun N => traceNorm (VecSeq E) (R N) + traceNorm (VecSeq E) (L N))
      atTop (𝓝 0) := by simpa only [add_zero] using htR.add htL
  apply squeeze_zero (fun _ => traceNorm_nonneg _) (fun N => ?_) ht
  have he : prefixGramRelativeOperator G H N - unitGramResolvent H ∘L D =
      prefixGramInverse H N ∘L R N + L N := by
    change (prefixGramInverse H N * D) * paperCoordinateProjection N -
        unitGramResolvent H * D =
      prefixGramInverse H N * (D * (paperCoordinateProjection N - 1)) +
        (prefixGramInverse H N - unitGramResolvent H) * D
    noncomm_ring
  rw [he]
  have hKR := memSchattenClass_one_comp_left (hR N) (prefixGramInverse H N)
  refine (traceNorm_add_le (hKR.isCompactOperator one_pos) ((hL N).isCompactOperator one_pos)
    hKR.one_summable_approxNumber (hL N).one_summable_approxNumber).trans ?_
  apply add_le_add ?_ le_rfl
  exact (traceNorm_comp_left_le (hR N).one_summable_approxNumber _).trans
    ((mul_le_mul_of_nonneg_right (norm_prefixGramInverse_le H N) (traceNorm_nonneg _)).trans_eq
      (one_mul _))

end
end GaloisForLFunctions.HTGeometry
