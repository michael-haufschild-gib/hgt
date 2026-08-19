import Mathlib

/-!
# Commuting orthogonal projections and the energy of their common intersection

For a family of closed subspaces whose orthogonal projections commute pairwise, the squared
distance of a vector to the intersection of the whole family is bounded by the sum of the squared
distances to the individual members.

Three steps:

* the product of two commuting orthogonal projections is the orthogonal projection onto the
  intersection;
* consequently a finite intersection satisfies `‖x - P_{M ⊓ N}x‖² = ‖x - P_M x‖² + ‖P_M(x - P_N x)‖²`,
  which telescopes over a `Finset` into the finite energy bound;
* an antitone family of closed subspaces has strongly convergent orthogonal projections, with
  limit the projection onto the intersection — obtained from the monotone statement in mathlib by
  passing to orthogonal complements.

For a *non*-commuting pair the bound is false (two lines meeting at a small angle in the plane
intersect in `0` while both individual distances are small), so the commutation hypothesis is
essential and not a technical convenience.
-/

namespace GaloisForLFunctions.HTGeometry

open Submodule Filter Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A closed submodule of a complete inner-product space has an orthogonal projection. -/
theorem hasOrthogonalProjection_of_isClosed [CompleteSpace E] {K : Submodule 𝕜 E}
    (h : IsClosed (K : Set E)) : K.HasOrthogonalProjection := by
  haveI : CompleteSpace K := h.completeSpace_coe
  infer_instance

/-- The projection onto the whole space is the identity. -/
theorem starProjection_top_apply (x : E) : (⊤ : Submodule 𝕜 E).starProjection x = x := by
  rw [Submodule.starProjection_top]; rfl

/-- Orthogonal projections onto equal submodules agree. -/
theorem starProjection_congr {K K' : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [K'.HasOrthogonalProjection] (h : K = K') (x : E) :
    K.starProjection x = K'.starProjection x := by
  subst h; rfl

/-- **The product of two commuting orthogonal projections is the projection onto the
intersection.** -/
theorem starProjection_inf_of_commute {M N : Submodule 𝕜 E}
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection] [(M ⊓ N).HasOrthogonalProjection]
    (hcomm : ∀ y : E, M.starProjection (N.starProjection y) =
      N.starProjection (M.starProjection y)) (x : E) :
    (M ⊓ N).starProjection x = M.starProjection (N.starProjection x) := by
  refine eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · refine Submodule.mem_inf.mpr ⟨M.starProjection_apply_mem _, ?_⟩
    rw [hcomm]
    exact N.starProjection_apply_mem _
  · intro w hw
    obtain ⟨hwM, hwN⟩ := Submodule.mem_inf.mp hw
    have h1 : inner 𝕜 (x - N.starProjection x) w = 0 := N.starProjection_inner_eq_zero x w hwN
    have h2 : inner 𝕜 (N.starProjection x - M.starProjection (N.starProjection x)) w = 0 :=
      M.starProjection_inner_eq_zero _ w hwM
    have hsplit : x - M.starProjection (N.starProjection x)
        = (x - N.starProjection x)
          + (N.starProjection x - M.starProjection (N.starProjection x)) := by abel
    rw [hsplit, inner_add_left, h1, h2, add_zero]

/-- **Pythagoras for a commuting pair.**  The defect energy of the intersection splits exactly. -/
theorem norm_sub_starProjection_inf_sq_le {M N : Submodule 𝕜 E}
    [M.HasOrthogonalProjection] [N.HasOrthogonalProjection] [(M ⊓ N).HasOrthogonalProjection]
    (hcomm : ∀ y : E, M.starProjection (N.starProjection y) =
      N.starProjection (M.starProjection y)) (x : E) :
    ‖x - (M ⊓ N).starProjection x‖ ^ 2
      ≤ ‖x - M.starProjection x‖ ^ 2 + ‖x - N.starProjection x‖ ^ 2 := by
  have hproj := starProjection_inf_of_commute (M := M) (N := N) hcomm x
  have hsplit : x - M.starProjection (N.starProjection x)
      = (x - M.starProjection x) + M.starProjection (x - N.starProjection x) := by
    rw [map_sub]; abel
  have hperp : inner 𝕜 (x - M.starProjection x) (M.starProjection (x - N.starProjection x)) = 0 :=
    M.starProjection_inner_eq_zero x _ (M.starProjection_apply_mem _)
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (𝕜 := 𝕜) (x - M.starProjection x) (M.starProjection (x - N.starProjection x)) hperp
  have hle : ‖M.starProjection (x - N.starProjection x)‖ ≤ ‖x - N.starProjection x‖ :=
    norm_starProjection_apply_le M _
  have hsq : ‖M.starProjection (x - N.starProjection x)‖ ^ 2 ≤ ‖x - N.starProjection x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [hproj, hsplit]
  calc ‖(x - M.starProjection x) + M.starProjection (x - N.starProjection x)‖ ^ 2
      = ‖x - M.starProjection x‖ ^ 2 + ‖M.starProjection (x - N.starProjection x)‖ ^ 2 := by
        simp only [pow_two]; exact hpyth
    _ ≤ ‖x - M.starProjection x‖ ^ 2 + ‖x - N.starProjection x‖ ^ 2 := by linarith

section Family

variable {ι : Type*} [DecidableEq ι]

/-- The orthogonal projection onto a finite intersection commutes with every member projection. -/
theorem starProjection_finsetInf_comm (M : ι → Submodule 𝕜 E)
    [∀ i, (M i).HasOrthogonalProjection]
    [∀ F : Finset ι, (F.inf M).HasOrthogonalProjection]
    (hcomm : ∀ i j, ∀ y : E, (M i).starProjection ((M j).starProjection y)
      = (M j).starProjection ((M i).starProjection y))
    (F : Finset ι) :
    ∀ (j : ι) (x : E), (F.inf M).starProjection ((M j).starProjection x)
      = (M j).starProjection ((F.inf M).starProjection x) := by
  induction F using Finset.induction with
  | empty =>
      intro j x
      have h : (∅ : Finset ι).inf M = ⊤ := Finset.inf_empty
      rw [starProjection_congr h, starProjection_congr h, starProjection_top_apply,
        starProjection_top_apply]
  | @insert a s _ha ih =>
      intro j x
      have hEq : (insert a s).inf M = M a ⊓ s.inf M := Finset.inf_insert
      haveI hinst : (M a ⊓ s.inf M).HasOrthogonalProjection := by
        have h : ((insert a s).inf M).HasOrthogonalProjection := inferInstance
        rwa [hEq] at h
      have hcomm' : ∀ y : E, (M a).starProjection ((s.inf M).starProjection y)
          = (s.inf M).starProjection ((M a).starProjection y) := fun y => (ih a y).symm
      have key : ∀ z : E, ((insert a s).inf M).starProjection z
          = (M a).starProjection ((s.inf M).starProjection z) := by
        intro z
        rw [starProjection_congr hEq z]
        exact starProjection_inf_of_commute hcomm' z
      rw [key, key, ih j, hcomm a j]

/-- **Finite energy bound.**  The defect energy of a finite commuting intersection is at most the
sum of the individual defect energies. -/
theorem norm_sub_starProjection_finsetInf_sq_le (M : ι → Submodule 𝕜 E)
    [∀ i, (M i).HasOrthogonalProjection]
    [∀ F : Finset ι, (F.inf M).HasOrthogonalProjection]
    (hcomm : ∀ i j, ∀ y : E, (M i).starProjection ((M j).starProjection y)
      = (M j).starProjection ((M i).starProjection y))
    (F : Finset ι) (x : E) :
    ‖x - (F.inf M).starProjection x‖ ^ 2 ≤ ∑ i ∈ F, ‖x - (M i).starProjection x‖ ^ 2 := by
  induction F using Finset.induction with
  | empty =>
      have h : (∅ : Finset ι).inf M = ⊤ := Finset.inf_empty
      rw [starProjection_congr h, starProjection_top_apply]
      simp
  | @insert a s ha ih =>
      have hEq : (insert a s).inf M = M a ⊓ s.inf M := Finset.inf_insert
      haveI hinst : (M a ⊓ s.inf M).HasOrthogonalProjection := by
        have h : ((insert a s).inf M).HasOrthogonalProjection := inferInstance
        rwa [hEq] at h
      have hcomm' : ∀ y : E, (M a).starProjection ((s.inf M).starProjection y)
          = (s.inf M).starProjection ((M a).starProjection y) := fun y =>
        (starProjection_finsetInf_comm M hcomm s a y).symm
      have hpair := norm_sub_starProjection_inf_sq_le (M := M a) (N := s.inf M) hcomm' x
      rw [starProjection_congr hEq x, Finset.sum_insert ha]
      linarith

end Family

section Antitone

variable [CompleteSpace E]

/-- **Antitone families of closed subspaces have strongly convergent projections.**  The limit is
the projection onto the intersection.  This is the mathlib monotone statement read through
orthogonal complements. -/
theorem starProjection_tendsto_iInf_of_antitone {κ : Type*} [Preorder κ]
    (U : κ → Submodule 𝕜 E) [∀ i, (U i).HasOrthogonalProjection]
    [(⨅ i, U i).HasOrthogonalProjection] (hU : Antitone U) (x : E) :
    Tendsto (fun i => (U i).starProjection x) atTop (𝓝 ((⨅ i, U i).starProjection x)) := by
  have hV : Monotone fun i => (U i)ᗮ := fun i j hij => Submodule.orthogonal_le (hU hij)
  have hkey : (⨆ i, (U i)ᗮ)ᗮ = ⨅ i, U i := by
    rw [← Submodule.iInf_orthogonal]
    exact iInf_congr fun i => Submodule.orthogonal_orthogonal (U i)
  have hclosure : (⨆ i, (U i)ᗮ).topologicalClosure = (⨅ i, U i)ᗮ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hkey]
  haveI hinst : (⨆ i, (U i)ᗮ).topologicalClosure.HasOrthogonalProjection := by
    rw [hclosure]; infer_instance
  have hstep := Submodule.starProjection_tendsto_closure_iSup (fun i => (U i)ᗮ) hV x
  have hcompl : ∀ (K : Submodule 𝕜 E) [K.HasOrthogonalProjection],
      Kᗮ.starProjection x = x - K.starProjection x := by
    intro K _
    have h := Submodule.starProjection_orthogonal K
    have h2 := congrArg (fun T : E →L[𝕜] E => T x) h
    simp only [FunLike.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.coe_id', id_eq] at h2
    exact h2
  have hlim : (⨆ i, (U i)ᗮ).topologicalClosure.starProjection x
      = x - (⨅ i, U i).starProjection x := by
    rw [starProjection_congr hclosure x, hcompl]
  rw [hlim] at hstep
  have h2 : Tendsto (fun i => x - ((U i)ᗮ).starProjection x) atTop
      (𝓝 (x - (x - (⨅ i, U i).starProjection x))) := tendsto_const_nhds.sub hstep
  have h3 : (fun i => x - ((U i)ᗮ).starProjection x) = fun i => (U i).starProjection x := by
    funext i
    rw [hcompl]
    abel
  rw [h3] at h2
  simpa using h2


/-- **Commuting-family energy bound.**  If the projections onto a family of closed subspaces
commute pairwise and every finite subfamily has total defect energy at most `C`, then the defect
energy of the full intersection is at most `C`. -/
theorem norm_sub_starProjection_iInf_sq_le {ι : Type*} [DecidableEq ι] (M : ι → Submodule 𝕜 E)
    [∀ i, (M i).HasOrthogonalProjection]
    [∀ F : Finset ι, (F.inf M).HasOrthogonalProjection]
    [(⨅ i, M i).HasOrthogonalProjection]
    (hcomm : ∀ i j, ∀ y : E, (M i).starProjection ((M j).starProjection y)
      = (M j).starProjection ((M i).starProjection y))
    {C : ℝ} (x : E)
    (hC : ∀ F : Finset ι, ∑ i ∈ F, ‖x - (M i).starProjection x‖ ^ 2 ≤ C) :
    ‖x - (⨅ i, M i).starProjection x‖ ^ 2 ≤ C := by
  have hinf : (⨅ F : Finset ι, F.inf M) = ⨅ i, M i := by
    refine le_antisymm (le_iInf fun i => ?_) (le_iInf fun F => Finset.le_inf fun i _ => iInf_le _ i)
    refine le_trans (iInf_le _ ({i} : Finset ι)) ?_
    simp
  haveI hinst : (⨅ F : Finset ι, F.inf M).HasOrthogonalProjection := by
    rw [hinf]; infer_instance
  have hanti : Antitone (fun F : Finset ι => F.inf M) := fun F G h => Finset.inf_mono h
  have htend := starProjection_tendsto_iInf_of_antitone (fun F : Finset ι => F.inf M) hanti x
  rw [starProjection_congr hinf x] at htend
  have hnorm : Tendsto (fun F : Finset ι => ‖x - (F.inf M).starProjection x‖ ^ 2) atTop
      (𝓝 (‖x - (⨅ i, M i).starProjection x‖ ^ 2)) :=
    ((tendsto_const_nhds.sub htend).norm).pow 2
  refine le_of_tendsto hnorm (Filter.Eventually.of_forall fun F => ?_)
  exact le_trans (norm_sub_starProjection_finsetInf_sq_le M hcomm F x) (hC F)

end Antitone

end GaloisForLFunctions.HTGeometry
