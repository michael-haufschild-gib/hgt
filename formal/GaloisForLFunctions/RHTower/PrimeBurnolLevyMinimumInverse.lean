import GaloisForLFunctions.RHTower.PrimeBurnolLevyInverseGraph
import GaloisForLFunctions.HTGeometry.ClosedHyperplaneInverse

/-! Canonical closed minimum-norm recovery on the dense range, including nonzero drift. -/

open Complex Set Filter MeasureTheory Topology
open scoped NNReal ComplexOrder InnerProductSpace
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry
namespace BurnolLevyData
variable (D : BurnolLevyData)

def recoverySpace (t : ℝ≥0) : Submodule ℂ BurnolHalfLineL2 := (D.evolution t).kerᗮ

def recoveryRestriction (t : ℝ≥0) : D.recoverySpace t →L[ℂ] BurnolHalfLineL2 :=
  (D.evolution t).comp (D.recoverySpace t).subtypeL

theorem recoveryRestriction_injective (t : ℝ≥0) : Function.Injective (D.recoveryRestriction t) := by
  intro x y hxy
  have hk : (x : BurnolHalfLineL2) - (y : BurnolHalfLineL2) ∈ (D.evolution t).ker := by
    change D.evolution t ((x : BurnolHalfLineL2) - (y : BurnolHalfLineL2)) = 0
    change D.evolution t (x : BurnolHalfLineL2) = D.evolution t (y : BurnolHalfLineL2) at hxy
    rw [map_sub, hxy, sub_self]
  have ho : (x : BurnolHalfLineL2) - (y : BurnolHalfLineL2) ∈ (D.evolution t).kerᗮ :=
    (D.recoverySpace t).sub_mem x.property y.property
  have hi := (Submodule.mem_orthogonal _ _).mp ho _ hk
  exact Subtype.ext (sub_eq_zero.mp (inner_self_eq_zero.mp hi))

theorem recoveryRestriction_range (t : ℝ≥0) :
    (D.recoveryRestriction t).range = (D.evolution t).range := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(v : BurnolHalfLineL2), rfl⟩
  · rintro ⟨v, rfl⟩
    let P := (D.evolution t).ker.starProjection
    have hP : D.evolution t (P v) = 0 := (D.evolution t).ker.starProjection_apply_mem v
    refine ⟨⟨v - P v, Submodule.sub_starProjection_mem_orthogonal
      (K := (D.evolution t).ker) v⟩, ?_⟩
    change D.evolution t (v - P v) = D.evolution t v
    rw [map_sub, hP, sub_zero]

def minimumNormInverse (t : ℝ≥0) : BurnolHalfLineL2 →ₗ.[ℂ] BurnolHalfLineL2 :=
  closedHyperplaneInverse (D.recoverySpace t) (D.recoveryRestriction t)

theorem minimumNormInverse_domain (t : ℝ≥0) :
    (D.minimumNormInverse t).domain = (D.evolution t).range := by
  rw [minimumNormInverse, closedHyperplaneInverse_domain, D.recoveryRestriction_range]

theorem minimumNormInverse_isClosed (t : ℝ≥0) : (D.minimumNormInverse t).IsClosed :=
  closedHyperplaneInverse_isClosed (D.recoverySpace t)
    (Submodule.isClosed_orthogonal _) (D.recoveryRestriction t) (D.recoveryRestriction_injective t)

theorem minimumNormInverse_dense_domain (t : ℝ≥0) :
    Dense ((D.minimumNormInverse t).domain : Set BurnolHalfLineL2) := by
  rw [D.minimumNormInverse_domain]
  exact D.dense_evolution_range t

theorem minimumNormInverse_graph_mem_iff (t : ℝ≥0) (u v : BurnolHalfLineL2) :
    (u, v) ∈ (D.minimumNormInverse t).graph ↔
      D.evolution t v = u ∧ v ∈ D.recoverySpace t := by
  change (u, v) ∈ (closedGraphTransform (D.recoverySpace t) (D.recoveryRestriction t)
    (D.recoverySpace t).subtypeL).graph ↔ _
  rw [closedGraphTransform_graph _ _ _ (D.recoveryRestriction_injective t)]
  constructor
  · rintro ⟨x, hx⟩
    have hu : D.evolution t (x : BurnolHalfLineL2) = u := congrArg Prod.fst hx
    have hv : (x : BurnolHalfLineL2) = v := congrArg Prod.snd hx
    exact ⟨by simpa only [hv] using hu, hv ▸ x.property⟩
  · rintro ⟨hu, hv⟩
    exact ⟨⟨v, hv⟩, Prod.ext hu rfl⟩

theorem minimumNormInverse_graph_iff_backward (t : ℝ≥0) (u v : BurnolHalfLineL2) :
    (u, v) ∈ (D.minimumNormInverse t).graph ↔
      (u, v) ∈ D.backwardPrimeGraph t ∧ v ∈ D.recoverySpace t := by
  rw [D.minimumNormInverse_graph_mem_iff, D.backwardPrimeGraph_mem_iff]

theorem minimumNormInverse_solves (t : ℝ≥0) (u : (D.minimumNormInverse t).domain) :
    D.evolution t (D.minimumNormInverse t u) = u ∧
      D.minimumNormInverse t u ∈ D.recoverySpace t := by
  apply (D.minimumNormInverse_graph_mem_iff t _ _).mp
  exact (LinearPMap.mem_graph_iff (D.minimumNormInverse t)).mpr ⟨u, rfl, rfl⟩

/-- Every competing preimage has exactly the additional squared norm of its lost component. -/
theorem minimumNormInverse_pythagoras (t : ℝ≥0) (u : (D.minimumNormInverse t).domain)
    (v : BurnolHalfLineL2) (hv : D.evolution t v = u) :
    ‖v‖ ^ 2 = ‖D.minimumNormInverse t u‖ ^ 2 + ‖v - D.minimumNormInverse t u‖ ^ 2 := by
  obtain ⟨hu, ho⟩ := D.minimumNormInverse_solves t u
  have hk : v - D.minimumNormInverse t u ∈ (D.evolution t).ker := by
    change D.evolution t (v - D.minimumNormInverse t u) = 0
    rw [map_sub, hv, hu, sub_self]
  have hi : inner ℂ (D.minimumNormInverse t u) (v - D.minimumNormInverse t u) = 0 :=
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal _ _).mp ho _ hk)
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi
  have he : D.minimumNormInverse t u + (v - D.minimumNormInverse t u) = v := by abel
  simpa only [he, pow_two] using h

theorem minimumNormInverse_minimal (t : ℝ≥0) (u : (D.minimumNormInverse t).domain)
    (v : BurnolHalfLineL2) (hv : D.evolution t v = u) :
    ‖D.minimumNormInverse t u‖ ≤ ‖v‖ := by
  have h := D.minimumNormInverse_pythagoras t u v hv
  nlinarith [norm_nonneg v, norm_nonneg (D.minimumNormInverse t u),
    sq_nonneg ‖v - D.minimumNormInverse t u‖]

theorem minimumNormInverse_unique_minimizer (t : ℝ≥0) (u : (D.minimumNormInverse t).domain)
    (v : BurnolHalfLineL2) (hv : D.evolution t v = u)
    (hmin : ‖v‖ ≤ ‖D.minimumNormInverse t u‖) : v = D.minimumNormInverse t u := by
  have h := D.minimumNormInverse_pythagoras t u v hv
  have hn : ‖v - D.minimumNormInverse t u‖ = 0 := by
    nlinarith [norm_nonneg v, norm_nonneg (D.minimumNormInverse t u),
      norm_nonneg (v - D.minimumNormInverse t u)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end BurnolLevyData
end RHTower
