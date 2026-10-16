import GaloisForLFunctions.RHTower.CHMDInfiniteCriticalModes

/-!
# Canonical removal of the exact CHMD critical band

The full signed radical is a closed infinite-dimensional subspace of the actual
graph. Its graph-orthogonal projection is simultaneously orthogonal in source
and edge coordinates. Removing it preserves every signed pairing and the
primitive condition. No primitive positivity is asserted.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph

def signedRadical : Submodule ℝ SourceGraph where
  carrier := {p | ∀ q, sourcePair p q = 0}
  zero_mem' := by intro q; simp [sourcePair]
  add_mem' := by
    intro p q hp hq r
    rw [sourcePair_add_left, hp r, hq r, zero_add]
  smul_mem' := by
    intro c p hp q
    rw [sourcePair_smul_left, hp q, mul_zero]

theorem isClosed_signedRadical : IsClosed (signedRadical : Set SourceGraph) := by
  have he : (signedRadical : Set SourceGraph) = ⋂ q : SourceGraph, {p : SourceGraph | sourcePair p q = 0} := by
    ext p
    simp [signedRadical]
  rw [he]
  apply isClosed_iInter
  intro q
  exact isClosed_eq (continuous_sourcePair.comp (continuous_id.prodMk continuous_const)) continuous_const

instance complete_signedRadical : CompleteSpace signedRadical := by
  letI : IsClosed (signedRadical : Set SourceGraph) := isClosed_signedRadical
  exact IsClosed.completeSpace_coe

theorem radical_inner_eq_two_source {k : SourceGraph} (hk : k ∈ signedRadical) (q : SourceGraph) :
    ⟪k, q⟫_ℝ = 2 * ⟪k.val.fst, q.val.fst⟫_ℝ := by
  have he := hk q
  change ⟪k.val.snd, q.val.snd⟫_ℝ - ⟪k.val.fst, q.val.fst⟫_ℝ = 0 at he
  change ⟪k.val.fst, q.val.fst⟫_ℝ + ⟪k.val.snd, q.val.snd⟫_ℝ = _
  linarith

theorem radical_primitive {k : SourceGraph} (hk : k ∈ signedRadical) :
    ⟪k.val.fst, (constantLift 1).val.fst⟫_ℝ = 0 := by
  have he := hk (constantLift 1)
  rw [sourcePair_symm, sourcePair_ground, neg_eq_zero] at he
  rwa [real_inner_comm] at he

theorem radical_norm_sq {k : SourceGraph} (hk : k ∈ signedRadical) :
    ‖k‖^2 = 2 * ‖k.val.fst‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using radical_inner_eq_two_source hk k

def criticalProjection : SourceGraph →L[ℝ] SourceGraph := signedRadical.starProjection

def reducedSource : SourceGraph →L[ℝ] SourceGraph :=
  ContinuousLinearMap.id ℝ SourceGraph - criticalProjection

theorem criticalProjection_mem (p : SourceGraph) : criticalProjection p ∈ signedRadical :=
  (signedRadical.orthogonalProjectionOnto p).property

theorem reducedSource_mem (p : SourceGraph) : reducedSource p ∈ signedRadicalᗮ :=
  Submodule.sub_starProjection_mem_orthogonal p

/-- The critical projection is orthogonal in the original source mass. -/
theorem projection_source_orthogonal (p : SourceGraph) :
    ⟪(criticalProjection p).val.fst, (reducedSource p).val.fst⟫_ℝ = 0 := by
  have hh := Submodule.inner_right_of_mem_orthogonal (criticalProjection_mem p) (reducedSource_mem p)
  rw [radical_inner_eq_two_source (criticalProjection_mem p)] at hh
  linarith

/-- The same decomposition is orthogonal for the full arithmetic jump energy. -/
theorem projection_edge_orthogonal (p : SourceGraph) :
    ⟪(criticalProjection p).val.snd, (reducedSource p).val.snd⟫_ℝ = 0 := by
  have hh := criticalProjection_mem p (reducedSource p)
  change ⟪(criticalProjection p).val.snd, (reducedSource p).val.snd⟫_ℝ -
    ⟪(criticalProjection p).val.fst, (reducedSource p).val.fst⟫_ℝ = 0 at hh
  rwa [projection_source_orthogonal, sub_zero] at hh

/-- Removal of the whole exact radical preserves every signed mixed pairing. -/
theorem sourcePair_reduced (p q : SourceGraph) :
    sourcePair (reducedSource p) (reducedSource q) = sourcePair p q := by
  change sourcePair (p-criticalProjection p) (q-criticalProjection q) = _
  rw [sourcePair_sub_left, criticalProjection_mem p _, sub_zero, sourcePair_symm,
    sourcePair_sub_left, criticalProjection_mem q _, sub_zero, sourcePair_symm]

theorem sourceEnergy_reduced (p : SourceGraph) : sourceEnergy (reducedSource p) = sourceEnergy p := by
  simpa only [sourcePair_self] using sourcePair_reduced p p

/-- After the full critical band is removed, no further signed radical remains. -/
theorem reduced_nondegenerate {r : SourceGraph} (hr : r ∈ signedRadicalᗮ)
    (h : ∀ q ∈ signedRadicalᗮ, sourcePair r q = 0) : r = 0 := by
  have hk : r ∈ signedRadical := by
    intro q
    have hh := h (reducedSource q) (reducedSource_mem q)
    change sourcePair r (q-criticalProjection q) = 0 at hh
    rw [sourcePair_symm, sourcePair_sub_left, criticalProjection_mem q _, sub_zero,
      sourcePair_symm] at hh
    exact hh
  have hh := Submodule.inner_right_of_mem_orthogonal hk hr
  exact (inner_self_eq_zero.mp hh)

theorem reducedSource_primitive_pair (p : SourceGraph) :
    ⟪(reducedSource p).val.fst, (constantLift 1).val.fst⟫_ℝ =
      ⟪p.val.fst, (constantLift 1).val.fst⟫_ℝ := by
  change ⟪p.val.fst-(criticalProjection p).val.fst, (constantLift 1).val.fst⟫_ℝ = _
  rw [inner_sub_left, radical_primitive (criticalProjection_mem p), sub_zero]

theorem source_mass_decomposition (p : SourceGraph) :
    ‖p.val.fst‖^2 = ‖(criticalProjection p).val.fst‖^2 + ‖(reducedSource p).val.fst‖^2 := by
  have hp : (criticalProjection p).val.fst + (reducedSource p).val.fst = p.val.fst := by
    change (criticalProjection p).val.fst + (p.val.fst-(criticalProjection p).val.fst) = _
    abel
  rw [← hp, norm_add_sq_real, projection_source_orthogonal]
  ring

def criticalBandSequence (n : ℕ) : signedRadical :=
  ⟨CHMDThetaTranslate.sequence n,
    CHMDThetaTranslate.critical_radical (CHMDThetaTranslate.shifts n) (CHMDThetaTranslate.shifts_admissible n)⟩

theorem criticalBandSequence_linearIndependent : LinearIndependent ℝ criticalBandSequence :=
  LinearIndependent.of_comp signedRadical.subtype CHMDThetaTranslate.sequence_linearIndependent

/-- Canonical, unconditional decomposition into the exact critical band and its complement. -/
theorem exact_critical_band_decomposition (p : SourceGraph) :
    ∃ k r : SourceGraph, k ∈ signedRadical ∧ r ∈ signedRadicalᗮ ∧ p = k+r ∧
      ⟪k.val.fst, r.val.fst⟫_ℝ = 0 ∧ ⟪k.val.snd, r.val.snd⟫_ℝ = 0 ∧
      sourceEnergy p = sourceEnergy r ∧
      ⟪p.val.fst, (constantLift 1).val.fst⟫_ℝ = ⟪r.val.fst, (constantLift 1).val.fst⟫_ℝ := by
  refine ⟨criticalProjection p, reducedSource p, criticalProjection_mem p, reducedSource_mem p,
    ?_, projection_source_orthogonal p, projection_edge_orthogonal p,
    (sourceEnergy_reduced p).symm, (reducedSource_primitive_pair p).symm⟩
  change p = criticalProjection p + (p-criticalProjection p)
  abel

end RHTower.CHMDDoobGraph
