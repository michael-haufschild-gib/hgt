import GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionProperLaw

open Set Topology Complex QuotientAddGroup

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def markedTranslationSource : MultipleGammaPeriodSource × ℂ → ℂ := Prod.snd

def markedTranslationTarget (p : MultipleGammaPeriodSource →+ ℂ) :
    MultipleGammaPeriodSource × ℂ → ℂ := fun nz => nz.2 + p nz.1

def markedTranslationIdentity (z : ℂ) : MultipleGammaPeriodSource × ℂ := (0, z)

def markedTranslationInverse (p : MultipleGammaPeriodSource →+ ℂ)
    (a : MultipleGammaPeriodSource × ℂ) : MultipleGammaPeriodSource × ℂ :=
  (-a.1, markedTranslationTarget p a)

def markedTranslationCompose (a b : MultipleGammaPeriodSource × ℂ) :
    MultipleGammaPeriodSource × ℂ := (a.1 + b.1, a.2)

theorem markedTranslationTarget_compose_of_composable
    (p : MultipleGammaPeriodSource →+ ℂ) (a b : MultipleGammaPeriodSource × ℂ)
    (h : markedTranslationSource b = markedTranslationTarget p a) :
    markedTranslationTarget p (markedTranslationCompose a b) = markedTranslationTarget p b := by
  rcases a with ⟨n, z⟩
  rcases b with ⟨k, w⟩
  simp only [markedTranslationSource, markedTranslationTarget, markedTranslationCompose,
    map_add] at h ⊢
  rw [h]
  abel

@[simp] theorem markedTranslationSource_identity (z : ℂ) :
    markedTranslationSource (markedTranslationIdentity z) = z := rfl

@[simp] theorem markedTranslationTarget_identity
    (p : MultipleGammaPeriodSource →+ ℂ) (z : ℂ) :
    markedTranslationTarget p (markedTranslationIdentity z) = z := by
  simp [markedTranslationTarget, markedTranslationIdentity]

@[simp] theorem markedTranslationSource_inverse
    (p : MultipleGammaPeriodSource →+ ℂ) (a : MultipleGammaPeriodSource × ℂ) :
    markedTranslationSource (markedTranslationInverse p a) = markedTranslationTarget p a := rfl

@[simp] theorem markedTranslationTarget_inverse
    (p : MultipleGammaPeriodSource →+ ℂ) (a : MultipleGammaPeriodSource × ℂ) :
  markedTranslationTarget p (markedTranslationInverse p a) = markedTranslationSource a := by
  simp [markedTranslationTarget, markedTranslationInverse, markedTranslationSource, map_neg]

@[simp] theorem markedTranslationCompose_identity_source
    (a : MultipleGammaPeriodSource × ℂ) :
    markedTranslationCompose (markedTranslationIdentity (markedTranslationSource a)) a = a := by
  rcases a with ⟨n, z⟩
  simp [markedTranslationCompose, markedTranslationIdentity, markedTranslationSource]

@[simp] theorem markedTranslationCompose_identity_target
    (p : MultipleGammaPeriodSource →+ ℂ) (a : MultipleGammaPeriodSource × ℂ) :
    markedTranslationCompose a (markedTranslationIdentity (markedTranslationTarget p a)) = a := by
  rcases a with ⟨n, z⟩
  simp [markedTranslationCompose, markedTranslationIdentity]

theorem markedTranslationCompose_assoc
    (a b c : MultipleGammaPeriodSource × ℂ) :
    markedTranslationCompose (markedTranslationCompose a b) c =
      markedTranslationCompose a (markedTranslationCompose b c) := by
  rcases a with ⟨n, z⟩
  rcases b with ⟨k, w⟩
  rcases c with ⟨l, v⟩
  simp [markedTranslationCompose, add_assoc]

@[simp] theorem markedTranslationCompose_inverse_right
    (p : MultipleGammaPeriodSource →+ ℂ) (a : MultipleGammaPeriodSource × ℂ) :
    markedTranslationCompose a (markedTranslationInverse p a) =
      markedTranslationIdentity (markedTranslationSource a) := by
  rcases a with ⟨n, z⟩
  simp [markedTranslationCompose, markedTranslationInverse, markedTranslationIdentity,
    markedTranslationSource]

@[simp] theorem markedTranslationCompose_inverse_left
    (p : MultipleGammaPeriodSource →+ ℂ) (a : MultipleGammaPeriodSource × ℂ) :
    markedTranslationCompose (markedTranslationInverse p a) a =
      markedTranslationIdentity (markedTranslationTarget p a) := by
  rcases a with ⟨n, z⟩
  simp [markedTranslationCompose, markedTranslationInverse, markedTranslationIdentity]

theorem markedTranslation_structureMaps_continuous (p : MultipleGammaPeriodSource →+ ℂ) :
    Continuous markedTranslationSource ∧ Continuous (markedTranslationTarget p) ∧
      Continuous markedTranslationIdentity ∧ Continuous (markedTranslationInverse p) ∧
      Continuous (fun ab : (MultipleGammaPeriodSource × ℂ) ×
        (MultipleGammaPeriodSource × ℂ) => markedTranslationCompose ab.1 ab.2) := by
  have hp : Continuous p := continuous_of_discreteTopology
  constructor
  · exact continuous_snd
  constructor
  · exact continuous_snd.add (hp.comp continuous_fst)
  constructor
  · exact continuous_const.prodMk continuous_id
  constructor
  · exact continuous_fst.neg.prodMk
      (continuous_snd.add (hp.comp continuous_fst))
  · exact (continuous_fst.comp continuous_fst).add
      (continuous_fst.comp continuous_snd) |>.prodMk (continuous_snd.comp continuous_fst)

abbrev markedTranslationCoarseOrbitGroup (p : MultipleGammaPeriodSource →+ ℂ) :=
  ℂ ⧸ p.range

def MarkedTranslationSameOrbit (p : MultipleGammaPeriodSource →+ ℂ) (x y : ℂ) : Prop :=
  ∃ n, y = x + p n

theorem markedTranslation_sameOrbit_iff_coarseQuotient_eq
    (p : MultipleGammaPeriodSource →+ ℂ) (x y : ℂ) :
    MarkedTranslationSameOrbit p x y ↔
      (y : markedTranslationCoarseOrbitGroup p) = x := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    calc
      y = x + (y - x) := by abel
      _ = x + p n := by rw [← hn]

def markedTranslationReflectionHomeomorph (c : ℂ) : ℂ ≃ₜ ℂ where
  toFun z := c - z
  invFun z := c - z
  left_inv z := by
    change c - (c - z) = z
    abel
  right_inv z := by
    change c - (c - z) = z
    abel
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

def markedTranslationArrowReflectionHomeomorph (c : ℂ) :
    (MultipleGammaPeriodSource × ℂ) ≃ₜ (MultipleGammaPeriodSource × ℂ) where
  toFun a := (-a.1, c - a.2)
  invFun a := (-a.1, c - a.2)
  left_inv a := by ext <;> simp
  right_inv a := by ext <;> simp
  continuous_toFun := continuous_fst.neg.prodMk (continuous_const.sub continuous_snd)
  continuous_invFun := continuous_fst.neg.prodMk (continuous_const.sub continuous_snd)

structure MarkedTranslationTopologicalGroupoidAutomorphism
    (p : MultipleGammaPeriodSource →+ ℂ) where
  objectHomeomorph : ℂ ≃ₜ ℂ
  arrowHomeomorph : (MultipleGammaPeriodSource × ℂ) ≃ₜ
    (MultipleGammaPeriodSource × ℂ)
  map_source : ∀ a, markedTranslationSource (arrowHomeomorph a) =
    objectHomeomorph (markedTranslationSource a)
  map_target : ∀ a, markedTranslationTarget p (arrowHomeomorph a) =
    objectHomeomorph (markedTranslationTarget p a)
  map_identity : ∀ z, arrowHomeomorph (markedTranslationIdentity z) =
    markedTranslationIdentity (objectHomeomorph z)
  map_inverse : ∀ a, arrowHomeomorph (markedTranslationInverse p a) =
    markedTranslationInverse p (arrowHomeomorph a)
  map_compose : ∀ a b, arrowHomeomorph (markedTranslationCompose a b) =
    markedTranslationCompose (arrowHomeomorph a) (arrowHomeomorph b)

def markedTranslationReflectionAutomorphism
    (p : MultipleGammaPeriodSource →+ ℂ) (c : ℂ) :
    MarkedTranslationTopologicalGroupoidAutomorphism p where
  objectHomeomorph := markedTranslationReflectionHomeomorph c
  arrowHomeomorph := markedTranslationArrowReflectionHomeomorph c
  map_source a := rfl
  map_target a := by
    simp [markedTranslationTarget, markedTranslationArrowReflectionHomeomorph,
      markedTranslationReflectionHomeomorph, map_neg]
    abel
  map_identity z := by simp [markedTranslationArrowReflectionHomeomorph,
    markedTranslationIdentity, markedTranslationReflectionHomeomorph]
  map_inverse a := by
    ext
    · simp [markedTranslationArrowReflectionHomeomorph, markedTranslationInverse]
    · simp [markedTranslationArrowReflectionHomeomorph, markedTranslationInverse,
        markedTranslationTarget, map_neg]
      abel
  map_compose a b := by
    apply Prod.ext
    · simp [markedTranslationArrowReflectionHomeomorph, markedTranslationCompose]
      abel
    · simp [markedTranslationArrowReflectionHomeomorph, markedTranslationCompose]

theorem markedTranslationReflectionAutomorphism_involutive_objects
    (p : MultipleGammaPeriodSource →+ ℂ) (c z : ℂ) :
    (markedTranslationReflectionAutomorphism p c).objectHomeomorph
        ((markedTranslationReflectionAutomorphism p c).objectHomeomorph z) = z := by
  simp [markedTranslationReflectionAutomorphism, markedTranslationReflectionHomeomorph]

theorem markedTranslationReflectionAutomorphism_involutive_arrows
    (p : MultipleGammaPeriodSource →+ ℂ) (c : ℂ)
    (a : MultipleGammaPeriodSource × ℂ) :
    (markedTranslationReflectionAutomorphism p c).arrowHomeomorph
        ((markedTranslationReflectionAutomorphism p c).arrowHomeomorph a) = a := by
  simp [markedTranslationReflectionAutomorphism, markedTranslationArrowReflectionHomeomorph]

/-! ## Exact real-span form of the general conservation theorem -/

abbrev integralPeriodRealSpan {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : IntegralPeriodSource N →+ V) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range p)

noncomputable def integralMarkedPeriodExcess
    {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : IntegralPeriodSource N →+ V) : ℤ :=
  (integralPeriodImageRank p : ℤ) - Module.finrank ℝ (integralPeriodRealSpan p)

/-- General period-action conservation law with `d` literally the real-span dimension. -/
theorem periodActionConservationRealSpan
    {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : IntegralPeriodSource N →+ V) :
    integralMarkedPeriodExcess p + integralPeriodKernelRank p =
      (N : ℤ) - Module.finrank ℝ (integralPeriodRealSpan p) := by
  exact periodActionConservationLaw p (Module.finrank ℝ (integralPeriodRealSpan p))

/-- Literal real-span conservation equation is invariant under integral source-basis changes. -/
theorem periodActionConservationRealSpan_sourceBasisInvariant
    {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : IntegralPeriodSource N →+ V)
    (e : IntegralPeriodSource N ≃+ IntegralPeriodSource N) :
    integralMarkedPeriodExcess (p.comp e.toAddMonoidHom) +
        integralPeriodKernelRank (p.comp e.toAddMonoidHom) =
      integralMarkedPeriodExcess p + integralPeriodKernelRank p := by
  have hrange : Set.range (p.comp e.toAddMonoidHom) = Set.range p := by
    ext v
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨e.symm n, by simp⟩
  rw [periodActionConservationRealSpan, periodActionConservationRealSpan]
  change (N : ℤ) - Module.finrank ℝ
      (Submodule.span ℝ (Set.range (p.comp e.toAddMonoidHom))) =
    (N : ℤ) - Module.finrank ℝ (Submodule.span ℝ (Set.range p))
  rw [hrange]

/-- Literal real-span conservation equation is invariant under invertible real-linear target
coordinate changes. -/
theorem periodActionConservationRealSpan_targetCoordinatesInvariant
    {N : ℕ} {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℝ V] [Module ℝ W]
    (p : IntegralPeriodSource N →+ V) (e : V ≃ₗ[ℝ] W) :
    integralMarkedPeriodExcess (e.toAddEquiv.toAddMonoidHom.comp p) +
        integralPeriodKernelRank (e.toAddEquiv.toAddMonoidHom.comp p) =
      integralMarkedPeriodExcess p + integralPeriodKernelRank p := by
  have hspan :
      integralPeriodRealSpan (e.toAddEquiv.toAddMonoidHom.comp p) =
        (integralPeriodRealSpan p).map e.toLinearMap := by
    unfold integralPeriodRealSpan
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [periodActionConservationRealSpan, periodActionConservationRealSpan, hspan,
    e.finrank_map_eq]

/-! ## Theorem 2.1 and Corollary 2.2, collected without proxies -/

structure FiniteMultipleGammaLawstackConclusions (m : ℕ+) : Prop where
  stabilizer : ∀ z, markedTranslationStabilizer (finiteMultipleGammaPeriodMap m) z =
    (finiteMultipleGammaPeriodMap m).ker
  coarseOrbit : ∀ x y, MarkedTranslationSameOrbit (finiteMultipleGammaPeriodMap m) x y ↔
    (y : markedTranslationCoarseOrbitGroup (finiteMultipleGammaPeriodMap m)) = x
  kernel : (finiteMultipleGammaPeriodMap m).ker = ⊥
  image : finiteMultipleGammaPeriodSubgroup m =
    complexAxisPeriodSubgroup (finiteMultipleGammaRealPeriods m) multipleGammaIntegerPeriods
  closure : (finiteMultipleGammaPeriodSubgroup m).topologicalClosure =
    complexAxisPeriodSubgroup ⊤ multipleGammaIntegerPeriods
  excess : markedPeriodExcess (finiteMultipleGammaPeriodMap m) = 1
  actionNonproper : ¬ IsProperMap (markedActionGraph (finiteMultipleGammaPeriodMap m))
  coarseNotT1 : ¬ T1Space (ℂ ⧸ finiteMultipleGammaPeriodSubgroup m)
  coarseNotT2 : ¬ T2Space (ℂ ⧸ finiteMultipleGammaPeriodSubgroup m)
  hausdorffObserverCircle : Nonempty
    (finiteMultipleGammaHausdorffObserver m ≃ₜ+ AddCircle (1 : ℝ))
  reflectionAutomorphism : Nonempty
    (MarkedTranslationTopologicalGroupoidAutomorphism (finiteMultipleGammaPeriodMap m))
  depthEqualsExcess : multipleEllipticGammaTransverseDADepth
      (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) =
    markedPeriodExcess (finiteMultipleGammaPeriodMap m)
  depthOne : multipleEllipticGammaTransverseDADepth
      (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) = 1
  productReflection : ∀ z, multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m)
      (finiteMultipleGammaReflectionCenter m - z) =
    (multipleEllipticGammaProduct (finiteMultipleGammaFunctionPeriods m) z)⁻¹
  lawRankComplementarity : ∀ z, multipleEllipticGammaTransverseDADepth
        (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) +
      markedStabilizerRank (finiteMultipleGammaPeriodMap m) z = 1

theorem finiteMultipleGammaLawstackConclusions (m : ℕ+) :
    FiniteMultipleGammaLawstackConclusions m where
  stabilizer z := markedTranslationStabilizer_eq_ker _ z
  coarseOrbit x y := markedTranslation_sameOrbit_iff_coarseQuotient_eq _ x y
  kernel := finiteMultipleGammaPeriodMap_ker m
  image := finiteMultipleGammaPeriodSubgroup_eq_axes m
  closure := finiteMultipleGammaPeriodSubgroup_topologicalClosure m
  excess := finiteMultipleGammaMarkedPeriodExcess_eq_one m
  actionNonproper := finiteMultipleGammaAction_not_proper m
  coarseNotT1 := finiteMultipleGammaCoarseQuotient_not_t1Space m
  coarseNotT2 := finiteMultipleGammaCoarseQuotient_not_t2Space m
  hausdorffObserverCircle := ⟨finiteMultipleGammaHausdorffObserverEquivAddCircle m⟩
  reflectionAutomorphism := ⟨markedTranslationReflectionAutomorphism
    (finiteMultipleGammaPeriodMap m) (finiteMultipleGammaReflectionCenter m)⟩
  depthEqualsExcess := finiteMultipleGammaDADepth_eq_markedPeriodExcess m
  depthOne := finiteMultipleGammaTransverseDADepth m
  productReflection := finiteMultipleGammaProduct_reflection_at_actionCenter m
  lawRankComplementarity := finiteMultipleGammaDADepth_add_stabilizerRank m

structure BoundaryMultipleGammaLawstackConclusions : Prop where
  stabilizer : ∀ z, markedTranslationStabilizer boundaryMultipleGammaPeriodMap z =
    boundaryMultipleGammaPeriodMap.ker
  coarseOrbit : ∀ x y, MarkedTranslationSameOrbit boundaryMultipleGammaPeriodMap x y ↔
    (y : markedTranslationCoarseOrbitGroup boundaryMultipleGammaPeriodMap) = x
  kernel : boundaryMultipleGammaPeriodMap.ker =
    AddSubgroup.zmultiples boundaryMultipleGammaRelation
  image : boundaryMultipleGammaPeriodSubgroup =
    complexAxisPeriodSubgroup multipleGammaIntegerPeriods multipleGammaIntegerPeriods
  excess : markedPeriodExcess boundaryMultipleGammaPeriodMap = 0
  coarseTorus : Nonempty (boundaryMultipleGammaCoarseQuotient ≃ₜ+
    (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))
  coarseCompact : CompactSpace boundaryMultipleGammaCoarseQuotient
  coarseT2 : T2Space boundaryMultipleGammaCoarseQuotient
  stabilizerZ : ∀ z, Nonempty
    (markedTranslationStabilizer boundaryMultipleGammaPeriodMap z ≃+ ℤ)
  effectiveProper : ProperVAdd BoundaryEffectiveSource ℂ
  effectiveCocompact : CompactSpace (ℂ ⧸ boundaryEffectivePeriodMap.range)
  reflectionAutomorphism : Nonempty
    (MarkedTranslationTopologicalGroupoidAutomorphism boundaryMultipleGammaPeriodMap)
  depthEqualsExcess : multipleEllipticGammaTransverseDADepth
      boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos =
    markedPeriodExcess boundaryMultipleGammaPeriodMap
  depthZero : multipleEllipticGammaTransverseDADepth
      boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos = 0
  productReflection : ∀ z, multipleEllipticGammaProduct boundaryMultipleGammaFunctionPeriods
      (boundaryMultipleGammaReflectionCenter - z) =
    (multipleEllipticGammaProduct boundaryMultipleGammaFunctionPeriods z)⁻¹
  lawRankComplementarity : ∀ z, multipleEllipticGammaTransverseDADepth
        boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos +
      markedStabilizerRank boundaryMultipleGammaPeriodMap z = 1

theorem boundaryMultipleGammaLawstackConclusions :
    BoundaryMultipleGammaLawstackConclusions where
  stabilizer z := markedTranslationStabilizer_eq_ker _ z
  coarseOrbit x y := markedTranslation_sameOrbit_iff_coarseQuotient_eq _ x y
  kernel := boundaryMultipleGammaPeriodMap_ker
  image := boundaryMultipleGammaPeriodSubgroup_eq_axes
  excess := boundaryMultipleGammaMarkedPeriodExcess_eq_zero
  coarseTorus := ⟨boundaryMultipleGammaCoarseQuotientEquivTorus⟩
  coarseCompact := boundaryMultipleGammaCoarseQuotient_compactSpace
  coarseT2 := boundaryMultipleGammaCoarseQuotient_t2Space
  stabilizerZ z := ⟨boundaryMultipleGammaStabilizerZEquiv z⟩
  effectiveProper := boundaryEffectiveAction_proper
  effectiveCocompact := boundaryEffectiveQuotient_compactSpace
  reflectionAutomorphism := ⟨markedTranslationReflectionAutomorphism
    boundaryMultipleGammaPeriodMap boundaryMultipleGammaReflectionCenter⟩
  depthEqualsExcess := boundaryMultipleGammaDADepth_eq_markedPeriodExcess
  depthZero := boundaryMultipleGammaTransverseDADepth
  productReflection := boundaryMultipleGammaProduct_reflection_at_actionCenter
  lawRankComplementarity := boundaryMultipleGammaDADepth_add_stabilizerRank

/-- Corollary 2.2 for the entire finite-to-boundary marked collection. -/
theorem multipleGammaCofinalLawRankComplementarity :
    (∀ (m : ℕ+) (z : ℂ), multipleEllipticGammaTransverseDADepth
          (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) +
        markedStabilizerRank (finiteMultipleGammaPeriodMap m) z = 1) ∧
      (∀ z : ℂ, multipleEllipticGammaTransverseDADepth
          boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos +
        markedStabilizerRank boundaryMultipleGammaPeriodMap z = 1) := by
  exact ⟨finiteMultipleGammaDADepth_add_stabilizerRank,
    boundaryMultipleGammaDADepth_add_stabilizerRank⟩

end
end GaloisForLFunctions.HTGeometry
