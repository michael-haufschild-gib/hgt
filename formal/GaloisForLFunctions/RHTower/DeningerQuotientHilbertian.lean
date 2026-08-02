import GaloisForLFunctions.RHTower.DeningerQuotientProjection
import GaloisForLFunctions.RHTower.DeningerHilbertianEmbedding

/-!
# The quotient of a Hilbertian seminorm

For a Hilbertian seminorm `p = ‖A ·‖` the quotient seminorm by a submodule `N` is the distance in
`ℓ²` from `A x` to the closure `M` of `A(N)`, that is the norm of `A x` minus its orthogonal
projection onto `M`.  So the quotient seminorm is Hilbertian as well, realized by the same `ℓ²`
through the complementary projection.

The realization of the completed quotient has range inside the range of the ambient realization —
the complementary projection moves `A x` by an element of `M`, which already lies there — so the
ambient realization inverts it and supplies the bounded section that the quotient criterion needs.

* `deningerQuotientImage` : the closure of `A(N)` in `ℓ²`.
* `deningerQuotientSeminorm_eq_norm_sub_starProjection` : **the quotient seminorm is the distance
  to that closure.**
* `deningerQuotient_hilbertian` : **the quotient of a Hilbertian seminorm is Hilbertian.**
-/

namespace RHTower

open UniformSpace ContinuousLinearMap Metric

section QuotientHilbertian

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable {κ : Type} {p : Seminorm 𝕜 E} {A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2}

/-- The closure in `ℓ²` of the image of the submodule. -/
noncomputable def deningerQuotientImage (N : Submodule 𝕜 E)
    (A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2) : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2) :=
  (N.map A).topologicalClosure

theorem deningerQuotientImage_isClosed (N : Submodule 𝕜 E)
    (A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2) :
    IsClosed ((deningerQuotientImage N A : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2)) :
      Set (lp (fun _ : κ => 𝕜) 2)) :=
  (N.map A).isClosed_topologicalClosure

theorem deningerQuotientImage_coe (N : Submodule 𝕜 E)
    (A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2) :
    ((deningerQuotientImage N A : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2)) :
        Set (lp (fun _ : κ => 𝕜) 2))
      = closure ((N.map A : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2)) :
        Set (lp (fun _ : κ => 𝕜) 2)) := rfl

instance deningerQuotientImage_completeSpace (N : Submodule 𝕜 E)
    (A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2) :
    CompleteSpace (deningerQuotientImage N A) :=
  (deningerQuotientImage_isClosed N A).completeSpace_coe

instance deningerQuotientImage_hasOrthogonalProjection (N : Submodule 𝕜 E)
    (A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2) :
    (deningerQuotientImage N A).HasOrthogonalProjection :=
  inferInstance

/-! ## The quotient seminorm is a distance in `ℓ²` -/

theorem deningerQuotient_range_eq (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) (x : E) :
    (Set.range fun y : DeningerQuotientReps N (Submodule.Quotient.mk x) => p (y : E))
      = Set.range fun w : (N.map A : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2)) =>
        ‖A x - (w : lp (fun _ : κ => 𝕜) 2)‖ := by
  ext r
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    have hmem : y - x ∈ N := by
      have h := Submodule.Quotient.eq N |>.mp hy
      exact h
    refine ⟨⟨-A (y - x), ?_⟩, ?_⟩
    · exact Submodule.neg_mem _ ⟨y - x, hmem, rfl⟩
    · show ‖A x - (-A (y - x))‖ = p y
      rw [hA y]
      congr 1
      rw [map_sub]
      abel
  · rintro ⟨⟨w, hw⟩, rfl⟩
    obtain ⟨n, hn, rfl⟩ := hw
    refine ⟨⟨x - n, ?_⟩, ?_⟩
    · refine (Submodule.Quotient.eq N).mpr ?_
      have : x - n - x = -n := by abel
      rw [this]
      exact Submodule.neg_mem _ hn
    · show p (x - n) = ‖A x - A n‖
      rw [hA (x - n), map_sub]

theorem deningerQuotientSeminorm_eq_infDist (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) (x : E) :
    deningerQuotientSeminorm N p (Submodule.Quotient.mk x)
      = infDist (A x) ((N.map A : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2)) :
        Set (lp (fun _ : κ => 𝕜) 2)) := by
  rw [deningerQuotientSeminorm_apply, deningerQuotientFun, infDist_eq_iInf]
  show sInf (Set.range fun y : DeningerQuotientReps N (Submodule.Quotient.mk x) => p (y : E))
    = sInf (Set.range fun w : (N.map A : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2)) =>
      dist (A x) (w : lp (fun _ : κ => 𝕜) 2))
  have hdist : (fun w : (N.map A : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2)) =>
      dist (A x) (w : lp (fun _ : κ => 𝕜) 2))
      = fun w : (N.map A : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2)) =>
        ‖A x - (w : lp (fun _ : κ => 𝕜) 2)‖ := by
    funext w
    rw [dist_eq_norm]
  rw [hdist, deningerQuotient_range_eq N hA x]

/-- **The quotient seminorm is the distance to the closure of the image**, that is the norm of the
complementary orthogonal projection. -/
theorem deningerQuotientSeminorm_eq_norm_sub_starProjection (N : Submodule 𝕜 E)
    (hA : ∀ x, p x = ‖A x‖) (x : E) :
    deningerQuotientSeminorm N p (Submodule.Quotient.mk x)
      = ‖A x - (deningerQuotientImage N A).starProjection (A x)‖ := by
  rw [deningerQuotientSeminorm_eq_infDist N hA x]
  have hclosure : infDist (A x) ((N.map A : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2)) :
      Set (lp (fun _ : κ => 𝕜) 2))
      = infDist (A x) ((deningerQuotientImage N A : Submodule 𝕜 (lp (fun _ : κ => 𝕜) 2)) :
        Set (lp (fun _ : κ => 𝕜) 2)) := by
    rw [deningerQuotientImage_coe, infDist_closure]
  rw [hclosure, infDist_eq_iInf]
  have hmin : ‖A x - (deningerQuotientImage N A).starProjection (A x)‖
      = ⨅ w : (deningerQuotientImage N A), ‖A x - (w : lp (fun _ : κ => 𝕜) 2)‖ := by
    refine ((deningerQuotientImage N A).norm_eq_iInf_iff_inner_eq_zero
      ((deningerQuotientImage N A).starProjection_apply_mem (A x))).mpr ?_
    intro w hw
    have hperp := (deningerQuotientImage N A).sub_starProjection_mem_orthogonal (A x)
    have h := (Submodule.mem_orthogonal _ _).mp hperp w hw
    exact inner_eq_zero_symm.mp h
  rw [hmin]
  refine iInf_congr fun w => ?_
  rw [dist_eq_norm]

/-! ## The quotient of a Hilbertian seminorm is Hilbertian -/

theorem deningerQuotientHilbertian_ker_le (N : Submodule 𝕜 E)
    (A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2) :
    N ≤ LinearMap.ker
      (((ContinuousLinearMap.id 𝕜 (lp (fun _ : κ => 𝕜) 2)
        - (deningerQuotientImage N A).starProjection).toLinearMap).comp A) := by
  intro n hn
  have hmem : A n ∈ deningerQuotientImage N A := by
    refine Submodule.le_topologicalClosure _ ?_
    exact ⟨n, hn, rfl⟩
  show (ContinuousLinearMap.id 𝕜 (lp (fun _ : κ => 𝕜) 2)
    - (deningerQuotientImage N A).starProjection) (A n) = 0
  have hfix : (deningerQuotientImage N A).starProjection (A n) = A n := by
    have h := (deningerQuotientImage N A).starProjection_mem_subspace_eq_self ⟨A n, hmem⟩
    exact h
  show A n - (deningerQuotientImage N A).starProjection (A n) = 0
  rw [hfix, sub_self]

/-- The `ℓ²` realization of the quotient of a Hilbertian seminorm. -/
noncomputable def deningerQuotientHilbertianMap (N : Submodule 𝕜 E)
    (A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2) : (E ⧸ N) →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2 :=
  Submodule.liftQ N
    (((ContinuousLinearMap.id 𝕜 (lp (fun _ : κ => 𝕜) 2)
      - (deningerQuotientImage N A).starProjection).toLinearMap).comp A)
    (deningerQuotientHilbertian_ker_le N A)

@[simp] theorem deningerQuotientHilbertianMap_mk (N : Submodule 𝕜 E)
    (A : E →ₗ[𝕜] lp (fun _ : κ => 𝕜) 2) (x : E) :
    deningerQuotientHilbertianMap N A (Submodule.Quotient.mk x)
      = A x - (deningerQuotientImage N A).starProjection (A x) := rfl

/-- **The quotient of a Hilbertian seminorm is Hilbertian.** -/
theorem deningerQuotient_hilbertian (N : Submodule 𝕜 E) (hA : ∀ x, p x = ‖A x‖) :
    DeningerIsHilbertianSeminorm (deningerQuotientSeminorm N p) := by
  refine ⟨κ, deningerQuotientHilbertianMap N A, fun z => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N z
  rw [deningerQuotientSeminorm_eq_norm_sub_starProjection N hA x,
    deningerQuotientHilbertianMap_mk]

end QuotientHilbertian

end RHTower
