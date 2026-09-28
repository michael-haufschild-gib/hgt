/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import GaloisForLFunctions.HTGeometry.LoopOpenCoverDecomposition
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Simply connected real spheres

Every unit sphere in `ℝ^(n+3)` is simply connected. Complements of antipodal
points are contractible stereographic charts, and their intersection is
path connected. The project-local open-cover loop decomposition supplies
the van Kampen step.

The stereographic-cover argument is adapted from DifferentialGeometry's
`Topology/FundamentalGroup/Sphere.lean` (Apache-2.0), generalized from its
explicit two- and three-sphere instances to every dimension at least two.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A punctured unit sphere is homeomorphic to the orthogonal hyperplane at
the removed unit vector. -/
def sphereComplementPointHomeomorph (v : sphere (0 : E) 1) :
    ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ (ℝ ∙ (v : E))ᗮ := by
  rw [← stereographic_source (norm_eq_of_mem_sphere v)]
  exact (stereographic (norm_eq_of_mem_sphere v)).toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ _)

/-- Puncturing a real unit sphere leaves a contractible space. -/
theorem sphereComplementPoint_contractible (v : sphere (0 : E) 1) :
    ContractibleSpace ({v}ᶜ : Set (sphere (0 : E) 1)) :=
  (sphereComplementPointHomeomorph v).contractibleSpace

private theorem sphereComplementAntipodes_pathConnected (v : sphere (0 : E) 1)
    (hrank : 1 < Module.rank ℝ ((ℝ ∙ (v : E))ᗮ)) :
    IsPathConnected ({v}ᶜ ∩ {-v}ᶜ : Set (sphere (0 : E) 1)) := by
  let proj := stereographic (norm_eq_of_mem_sphere v)
  have himage : proj.toPartialEquiv.symm '' (proj.target \ {0}) =
      {v}ᶜ ∩ {-v}ᶜ := by
    rw [Set.image_sdiff_of_injOn, proj.toPartialEquiv.symm_image_target_eq_source,
      Set.image_singleton]
    rotate_left
    · exact proj.toPartialEquiv.symm.injOn
    · exact Set.singleton_subset_iff.mpr (by rw [stereographic_target]; trivial)
    rw [stereographic_source]
    have hsouth : proj.toPartialEquiv.symm 0 = -v := by
      calc
        proj.toPartialEquiv.symm 0 = proj.toPartialEquiv.symm (proj (-v)) := by
          rw [stereographic_apply_neg]
        _ = -v := proj.left_inv (by
          rw [stereographic_source]
          exact (ne_neg_of_mem_unit_sphere ℝ v).symm)
    rw [hsouth]
    rfl
  rw [← himage]
  apply IsPathConnected.image'
  · rw [stereographic_target]
    have hset : (Set.univ \ {0} : Set ((ℝ ∙ (v : E))ᗮ)) = {0}ᶜ := by
      ext x
      simp
    rw [hset]
    exact isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : (ℝ ∙ (v : E))ᗮ)
  · exact proj.continuousOn_invFun.mono Set.sdiff_subset

private theorem sphereSimplyConnected_of_orthogonal_rank
    (v : sphere (0 : E) 1) (hrank : 1 < Module.rank ℝ ((ℝ ∙ (v : E))ᗮ))
    [PathConnectedSpace (sphere (0 : E) 1)] :
    SimplyConnectedSpace (sphere (0 : E) 1) := by
  let c : Bool → Set (sphere (0 : E) 1) := fun b => if b then {v}ᶜ else {-v}ᶜ
  have hcSimply : ∀ b, IsSimplyConnected (c b) := by
    intro b
    cases b
    · letI := sphereComplementPoint_contractible (-v)
      exact inferInstanceAs (SimplyConnectedSpace ({-v}ᶜ : Set (sphere (0 : E) 1)))
    · letI := sphereComplementPoint_contractible v
      exact inferInstanceAs (SimplyConnectedSpace ({v}ᶜ : Set (sphere (0 : E) 1)))
  have hcInter : ∀ b d, IsPathConnected (c b ∩ c d) := by
    intro b d
    cases b <;> cases d
    · simpa only [c, Bool.false_eq_true, ↓reduceIte, inter_self] using
        (hcSimply false).isPathConnected
    · simpa only [c, Bool.false_eq_true, ↓reduceIte, Set.inter_comm] using
        sphereComplementAntipodes_pathConnected v hrank
    · exact sphereComplementAntipodes_pathConnected v hrank
    · simpa only [c, ↓reduceIte, inter_self] using (hcSimply true).isPathConnected
  obtain ⟨a, ha⟩ := (hcInter true false).nonempty
  have hbase : ∀ b, a ∈ c b := by intro b; cases b; exact ha.2; exact ha.1
  have hnull (p : Path a a) : p.Homotopic (Path.refl a) := by
    apply basedLoop_nullhomotopic_of_openCover
      (c := c) (fun b => by cases b <;> exact isOpen_compl_singleton)
      ?_ hcInter hcSimply hbase p
    intro x _
    by_cases hx : x = v
    · apply Set.mem_iUnion.mpr
      refine ⟨false, ?_⟩
      change x ≠ -v
      simpa only [hx] using ne_neg_of_mem_unit_sphere ℝ v
    · exact Set.mem_iUnion.mpr ⟨true, hx⟩
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, fun x p => ?_⟩
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x a
  apply Path.Homotopic.Quotient.exact
  change Path.Homotopic.Quotient.mk p = (1 : FundamentalGroup _ x)
  apply e.injective
  rw [map_one]
  induction e (Path.Homotopic.Quotient.mk p) using Path.Homotopic.Quotient.ind with
  | mk q => exact Path.Homotopic.Quotient.eq.mpr (hnull q)

/-- The unit sphere in real dimension `n+3` is simply connected. -/
instance realSphereSimplyConnectedSpace (n : ℕ) :
    SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) := by
  let v : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  have htotal : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 3))) := by
    rw [← Module.finrank_eq_rank']
    simp only [finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < n + 3 by omega)
  letI : PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere htotal 0 (by norm_num : (0 : ℝ) ≤ 1))
  apply sphereSimplyConnected_of_orthogonal_rank v
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
    ⟨by simp⟩
  have hfin : Module.finrank ℝ ((ℝ ∙ (v : EuclideanSpace ℝ (Fin (n + 3))))ᗮ) = n + 2 :=
    Submodule.finrank_orthogonal_span_singleton (n := n + 2)
      (ne_zero_of_mem_unit_sphere v)
  rw [← Module.finrank_eq_rank', hfin]
  exact_mod_cast (show 1 < n + 2 by omega)

/-- Stereographic manifold charts give local path connectedness of real spheres. -/
instance realSphereLocallyPathConnectedSpace (n : ℕ) :
    LocallyPathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) :=
  ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (n + 2))) _

/-- Any two paths on a real sphere of dimension at least two are homotopic
with fixed endpoints. -/
theorem realSphere_paths_homotopic (n : ℕ)
    {x y : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1} (p q : Path x y) :
    p.Homotopic q :=
  SimplyConnectedSpace.paths_homotopic p q

/-- Every loop on a real sphere of dimension at least two contracts. -/
theorem realSphere_loop_nullhomotopic (n : ℕ)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) (p : Path x x) :
    p.Homotopic (Path.refl x) :=
  realSphere_paths_homotopic n p (Path.refl x)

end

end GaloisForLFunctions.HTGeometry
