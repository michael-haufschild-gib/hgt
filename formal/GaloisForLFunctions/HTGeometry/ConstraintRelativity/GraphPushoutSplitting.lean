import GaloisForLFunctions.HTGeometry.ConstraintRelativity.UnitQuotientPullbackSplitting

/-!
# Continuous scalar graph-pushout splitting

For a continuous scalar functional on a subspace, this file realizes its pushout with the ambient
space as a quotient by the graph relation. Hahn--Banach extends that functional to the ambient
space; the extension gives a continuous linear equivalence from the pushout to the product of the
ambient quotient and scalar target. No completeness or closed-subspace assertion is made here.
-/

namespace HTGeometry.ConstraintRelativity

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Relation defining scalar pushout of `N ↪ E` and `ℓ : N → 𝕜`. -/
def graphPushoutRelationMap (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) :
    N →L[𝕜] E × 𝕜 :=
  N.subtypeL.prod (-ℓ)

/-- Graph relation imposed in scalar pushout. -/
def graphPushoutRelation (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) :
    Submodule 𝕜 (E × 𝕜) :=
  LinearMap.range (graphPushoutRelationMap N ℓ : N →ₗ[𝕜] E × 𝕜)

/-- Quotient model for scalar graph pushout. -/
abbrev graphPushout (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) :=
  (E × 𝕜) ⧸ graphPushoutRelation N ℓ

/-- Map out of graph pushout induced by ambient extension `L` of `ℓ`. -/
def graphPushoutForwardPre (N : Submodule 𝕜 E) (L : E →L[𝕜] 𝕜) :
    E × 𝕜 →L[𝕜] (E ⧸ N) × 𝕜 :=
  ((quotientCLM N).comp (ContinuousLinearMap.fst 𝕜 E 𝕜)).prod
    ((ContinuousLinearMap.snd 𝕜 E 𝕜) +
      L.comp (ContinuousLinearMap.fst 𝕜 E 𝕜))

lemma graphPushoutRelation_le_forwardKer
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) :
    graphPushoutRelation N ℓ ≤
      LinearMap.ker (graphPushoutForwardPre N L : E × 𝕜 →ₗ[𝕜] (E ⧸ N) × 𝕜) := by
  rintro _ ⟨n, rfl⟩
  change (Submodule.Quotient.mk (n : E), -ℓ n + L n) = 0
  rw [Prod.mk_eq_zero]
  exact ⟨(Submodule.Quotient.mk_eq_zero N).mpr n.2, by rw [hL]; abel⟩

/-- Forward map from graph pushout to quotient times scalar target. -/
def graphPushoutForward
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) : graphPushout N ℓ →L[𝕜] (E ⧸ N) × 𝕜 :=
  (graphPushoutRelation N ℓ).liftQL (graphPushoutForwardPre N L)
    (graphPushoutRelation_le_forwardKer N ℓ L hL)

@[simp] lemma graphPushoutForward_mk
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) (x : E × 𝕜) :
    graphPushoutForward N ℓ L hL (Submodule.Quotient.mk x) =
      graphPushoutForwardPre N L x := rfl

@[simp] lemma graphPushoutForwardPre_apply
    (N : Submodule 𝕜 E) (L : E →L[𝕜] 𝕜) (x : E) (c : 𝕜) :
    graphPushoutForwardPre N L (x, c) = (Submodule.Quotient.mk x, c + L x) := rfl

/-- Ambient representative for quotient class, corrected by ambient extension. -/
def graphPushoutBasePre
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜) :
    E →L[𝕜] graphPushout N ℓ :=
  (graphPushoutRelation N ℓ).mkQL.comp
    ((ContinuousLinearMap.id 𝕜 E).prod (-L))

lemma graphPushoutBasePre_ker
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) :
    N ≤ LinearMap.ker (graphPushoutBasePre N ℓ L : E →ₗ[𝕜] graphPushout N ℓ) := by
  intro x hx
  change Submodule.Quotient.mk (x, -L x) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨⟨x, hx⟩, ?_⟩
  change (x, -ℓ ⟨x, hx⟩) = (x, -L x)
  congr 1
  simpa using congrArg Neg.neg (hL ⟨x, hx⟩).symm

/-- Quotient-coordinate component of inverse pushout map. -/
def graphPushoutBase
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) :
    (E ⧸ N) →L[𝕜] graphPushout N ℓ :=
  N.liftQL (graphPushoutBasePre N ℓ L) (graphPushoutBasePre_ker N ℓ L hL)

@[simp] lemma graphPushoutBase_mk
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) (x : E) :
    graphPushoutBase N ℓ L hL (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x, -L x) := rfl

/-- Scalar-coordinate component of inverse pushout map. -/
def graphPushoutScalar
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) :
    𝕜 →L[𝕜] graphPushout N ℓ :=
  (graphPushoutRelation N ℓ).mkQL.comp
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id 𝕜 𝕜) (0, 1))

@[simp] lemma graphPushoutScalar_apply
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (c : 𝕜) :
    graphPushoutScalar N ℓ c = Submodule.Quotient.mk ((0 : E), c) := by
  change Submodule.Quotient.mk (c • (0, 1)) = Submodule.Quotient.mk ((0 : E), c)
  congr 1
  ext <;> simp

/-- Inverse map from quotient times scalar target into graph pushout. -/
def graphPushoutBackward
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) :
    (E ⧸ N) × 𝕜 →L[𝕜] graphPushout N ℓ :=
  (graphPushoutBase N ℓ L hL).comp (ContinuousLinearMap.fst 𝕜 (E ⧸ N) 𝕜) +
    (graphPushoutScalar N ℓ).comp (ContinuousLinearMap.snd 𝕜 (E ⧸ N) 𝕜)

@[simp] lemma graphPushoutBackward_apply_mk
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) (x : E) (c : 𝕜) :
    graphPushoutBackward N ℓ L hL (Submodule.Quotient.mk x, c) =
      Submodule.Quotient.mk (x, c - L x) := by
  simp only [graphPushoutBackward, add_apply,
    ContinuousLinearMap.comp_apply, graphPushoutScalar_apply]
  change graphPushoutBase N ℓ L hL (Submodule.Quotient.mk x) +
    Submodule.Quotient.mk ((0 : E), c) = Submodule.Quotient.mk (x, c - L x)
  rw [graphPushoutBase_mk, ← Submodule.Quotient.mk_add]
  congr 1
  ext
  · simp
  · simp [sub_eq_add_neg, add_comm]

@[simp] lemma graphPushoutBackward_forward_mk
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) (x : E) (c : 𝕜) :
    graphPushoutBackward N ℓ L hL
      (graphPushoutForward N ℓ L hL (Submodule.Quotient.mk (x, c))) =
    Submodule.Quotient.mk (x, c) := by
  rw [graphPushoutForward_mk, graphPushoutForwardPre_apply,
    graphPushoutBackward_apply_mk]
  change Submodule.Quotient.mk (x, c + L x - L x) = Submodule.Quotient.mk (x, c)
  rw [add_sub_cancel_right]

/-- Backward and forward continuous maps are mutual inverses. -/
theorem graphPushoutBackward_comp_forward
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) :
    (graphPushoutBackward N ℓ L hL).comp (graphPushoutForward N ℓ L hL) =
      ContinuousLinearMap.id 𝕜 (graphPushout N ℓ) := by
  apply ContinuousLinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H x =>
      rcases x with ⟨x, c⟩
      exact graphPushoutBackward_forward_mk N ℓ L hL x c

/-- Forward and backward continuous maps are mutual inverses. -/
theorem graphPushoutForward_comp_backward
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) :
    (graphPushoutForward N ℓ L hL).comp (graphPushoutBackward N ℓ L hL) =
      ContinuousLinearMap.id 𝕜 ((E ⧸ N) × 𝕜) := by
  apply ContinuousLinearMap.ext
  rintro ⟨q, c⟩
  induction q using Submodule.Quotient.induction_on with
  | H x =>
      rw [ContinuousLinearMap.comp_apply, graphPushoutBackward_apply_mk,
        graphPushoutForward_mk, graphPushoutForwardPre_apply]
      change (Submodule.Quotient.mk x, c - L x + L x) = (Submodule.Quotient.mk x, c)
      rw [sub_add_cancel]

/-- Continuous graph-pushout identification induced by ambient extension of `ℓ`. -/
def graphPushoutEquiv
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) :
    graphPushout N ℓ ≃L[𝕜] (E ⧸ N) × 𝕜 :=
  ContinuousLinearEquiv.mk
    (LinearEquiv.ofLinear
      (graphPushoutForward N ℓ L hL).toLinearMap
      (graphPushoutBackward N ℓ L hL).toLinearMap
      (congrArg ContinuousLinearMap.toLinearMap
        (graphPushoutForward_comp_backward N ℓ L hL))
      (congrArg ContinuousLinearMap.toLinearMap
        (graphPushoutBackward_comp_forward N ℓ L hL)))
    (graphPushoutForward N ℓ L hL).continuous
    (graphPushoutBackward N ℓ L hL).continuous

@[simp] theorem graphPushoutEquiv_apply
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜)
    (hL : ∀ n : N, L n = ℓ n) (x : graphPushout N ℓ) :
    graphPushoutEquiv N ℓ L hL x = graphPushoutForward N ℓ L hL x := rfl

/-- Hahn--Banach supplies ambient extension required by graph-pushout equivalence. -/
noncomputable def graphPushoutExtension (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) : E →L[𝕜] 𝕜 :=
  (exists_extension_norm_eq N ℓ).choose

theorem graphPushoutExtension_restrict
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) (n : N) :
    graphPushoutExtension N ℓ n = ℓ n :=
  (exists_extension_norm_eq N ℓ).choose_spec.1 n

/-- Every continuous scalar graph pushout splits as quotient times scalar target. -/
noncomputable def graphPushoutHahnBanachEquiv
    (N : Submodule 𝕜 E) (ℓ : N →L[𝕜] 𝕜) :
    graphPushout N ℓ ≃L[𝕜] (E ⧸ N) × 𝕜 :=
  graphPushoutEquiv N ℓ (graphPushoutExtension N ℓ)
    (graphPushoutExtension_restrict N ℓ)

end

end HTGeometry.ConstraintRelativity
