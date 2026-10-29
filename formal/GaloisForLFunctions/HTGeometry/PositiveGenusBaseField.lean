import GaloisForLFunctions.HTGeometry.EllipticPlaneSubfield
import GaloisForLFunctions.HTGeometry.EllipticReparamCurrent
import GaloisForLFunctions.HTGeometry.TranscendenceDegreeOneVariable

/-!
# A complex function field of genus one

The meromorphic function field of `ℂ / (ℤ + iℤ)` is a concrete complex field of
transcendence degree one. Its geometric genus is the dimension of global holomorphic
one-forms, proved to be one by elliptic Liouville.

The finite-field elliptic function field and its point-count zeta function are constructed in
`ArithmeticEffectivityTheory.FiniteFieldPositiveGenusBase`.

Forms are represented on the covering plane by holomorphic maps into its complex cotangent
space. Translation invariance is precisely descent: the derivative of every deck translation
is the identity. Thus regularity is imposed everywhere on the compact quotient, including
at poles of the Weierstrass coordinates. Evaluation at `(0, 1)` identifies these forms with
`ℂ`, with inverse `c ↦ c dz`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The compact curve presented by a lattice covering of the complex plane. -/
abbrev EllipticBaseCurve (L : PeriodPair) := ℂ ⧸ L.lattice.toAddSubgroup

instance ellipticBaseCurve_compactSpace (L : PeriodPair) : CompactSpace (EllipticBaseCurve L) where
  isCompact_univ := by
    have h := IsZLattice.isCompact_range_of_periodic L.lattice
      (QuotientAddGroup.mk : ℂ → EllipticBaseCurve L) QuotientAddGroup.continuous_mk
      (fun z p hp => by
        apply QuotientAddGroup.eq.mpr
        change -(z + p) + z ∈ L.lattice
        simpa only [neg_add_rev, add_assoc, neg_add_cancel, add_zero]
          using L.lattice.neg_mem hp)
    rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at h

/-- The lattice quotient is covered by complex translation charts. -/
theorem ellipticBaseCurve_isCovering (L : PeriodPair) :
    IsCoveringMap (QuotientAddGroup.mk : ℂ → EllipticBaseCurve L) := by
  letI : DiscreteTopology L.lattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology L.lattice)
  exact (AddSubgroup.isAddQuotientCoveringMap_of_comm L.lattice.toAddSubgroup
    DiscreteTopology.isDiscrete).isCoveringMap

/-- Global holomorphic one-forms in the translation charts of the quotient curve. -/
def ellipticHolomorphicDifferentials (L : PeriodPair) :
    Submodule ℂ (ℂ → ℂ →L[ℂ] ℂ) where
  carrier := {ω | Differentiable ℂ ω ∧ ∀ p ∈ L.lattice, Function.Periodic ω p}
  zero_mem' := ⟨differentiable_const _, fun _ _ _ => rfl⟩
  add_mem' := fun ⟨hω, hωp⟩ ⟨hη, hηp⟩ =>
    ⟨hω.add hη, fun p hp z => congrArg₂ (· + ·) (hωp p hp z) (hηp p hp z)⟩
  smul_mem' := fun c _ ⟨hω, hωp⟩ =>
    ⟨hω.const_smul c, fun p hp z => congrArg (c • ·) (hωp p hp z)⟩

/-- The translation-invariant differential `c dz`. -/
def ellipticConstantDifferential (L : PeriodPair) (c : ℂ) :
    ellipticHolomorphicDifferentials L :=
  ⟨fun _ => c • ContinuousLinearMap.id ℂ ℂ,
    differentiable_const _, fun _ _ _ => rfl⟩

/-- The pullback by a deck translation fixes a descended form, including its tangent argument. -/
theorem ellipticHolomorphicDifferential_pullback (L : PeriodPair)
    (ω : ellipticHolomorphicDifferentials L) (p : L.lattice) (z v : ℂ) :
    ω.val (z + p) (fderiv ℂ (fun w : ℂ => w + p) z v) = ω.val z v := by
  have h : HasFDerivAt (fun w : ℂ => w + p) (ContinuousLinearMap.id ℂ ℂ) z :=
    (hasFDerivAt_id z).add_const (p : ℂ)
  rw [h.fderiv]
  exact congrArg (fun a : ℂ →L[ℂ] ℂ => a v) (ω.property.2 p p.property z)

/-- The form `dz` has neither zeros nor poles on the quotient. -/
theorem ellipticConstantDifferential_one_nonzero (L : PeriodPair) (z : ℂ) :
    (ellipticConstantDifferential L 1).val z ≠ 0 := by
  intro h
  have := congrArg (fun a : ℂ →L[ℂ] ℂ => a 1) h
  exact one_ne_zero (by simpa only [ellipticConstantDifferential, one_smul,
    ContinuousLinearMap.id_apply, zero_apply] using this)

/-- Compactness bounds every holomorphic coefficient; Liouville makes the form constant. -/
theorem ellipticHolomorphicDifferential_constant (L : PeriodPair)
    (ω : ellipticHolomorphicDifferentials L) (z w : ℂ) : ω.val z = ω.val w :=
  ω.property.1.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice ω.val ω.property.1.continuous
      (fun z p hp => ω.property.2 p hp z)).isBounded z w

/-- Evaluation at a tangent vector recovers the coefficient of `dz`. -/
theorem ellipticHolomorphicDifferential_apply (L : PeriodPair)
    (ω : ellipticHolomorphicDifferentials L) (z v : ℂ) :
    ω.val z v = v * ω.val 0 1 := by
  rw [ellipticHolomorphicDifferential_constant L ω z 0]
  simpa only [smul_eq_mul, mul_one] using (ω.val 0).map_smul v (1 : ℂ)

/-- Every holomorphic one-form is a unique multiple of the nowhere-zero form `dz`. -/
def ellipticDifferentialEquiv (L : PeriodPair) :
    ellipticHolomorphicDifferentials L ≃ₗ[ℂ] ℂ where
  toFun ω := ω.val 0 1
  invFun := ellipticConstantDifferential L
  left_inv ω := by
    apply Subtype.ext
    funext z
    apply ContinuousLinearMap.ext
    intro v
    change ω.val 0 1 * v = ω.val z v
    exact (mul_comm _ _).trans (ellipticHolomorphicDifferential_apply L ω z v).symm
  right_inv c := by change c * 1 = c; exact mul_one c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance (L : PeriodPair) : FiniteDimensional ℂ (ellipticHolomorphicDifferentials L) :=
  Module.Finite.equiv (ellipticDifferentialEquiv L).symm

/-- Geometric genus, defined by global holomorphic differentials on the quotient curve. -/
def ellipticGeometricGenus (L : PeriodPair) : ℕ :=
  Module.finrank ℂ (ellipticHolomorphicDifferentials L)

theorem ellipticGeometricGenus_eq_one (L : PeriodPair) : ellipticGeometricGenus L = 1 :=
  (ellipticDifferentialEquiv L).finrank_eq.trans (Module.finrank_self ℂ)

/-- Coefficients of holomorphic differentials embed in the meromorphic function field. -/
def ellipticDifferentialCoefficient (L : PeriodPair) :
    ellipticHolomorphicDifferentials L →ₗ[ℂ] ellipticSubfield L :=
  (Algebra.linearMap ℂ (ellipticSubfield L)).comp (ellipticDifferentialEquiv L).toLinearMap

theorem ellipticDifferentialCoefficient_injective (L : PeriodPair) :
    Function.Injective (ellipticDifferentialCoefficient L) :=
  (algebraMap ℂ (ellipticSubfield L)).injective.comp (ellipticDifferentialEquiv L).injective

/-- The coefficient map is the actual meromorphic germ of `z ↦ ω(z)(1)`. -/
theorem ellipticDifferentialCoefficient_rep (L : PeriodPair)
    (ω : ellipticHolomorphicDifferentials L) :
    (ellipticDifferentialCoefficient L ω : MeromorphicPlane) =
      ofMeromorphic (fun z => ω.val z 1)
        (fun z => ((ω.property.1.clm_apply (differentiable_const 1)).analyticAt z).meromorphicAt) := by
  change ofMeromorphic (fun _ => ω.val 0 1)
    (fun z => MeromorphicAt.const (ω.val 0 1) z) = _
  apply (ofMeromorphic_eq_iff _ _).mpr
  intro z
  exact Filter.Eventually.of_forall fun w =>
    congrArg (fun a : ℂ →L[ℂ] ℂ => a 1) (ellipticHolomorphicDifferential_constant L ω 0 w)

/-- Meromorphic coefficients of globally regular one-forms, in the frame `dz`. -/
def ellipticRegularDifferentials (L : PeriodPair) : Submodule ℂ (ellipticSubfield L) :=
  (ellipticDifferentialCoefficient L).range

/-- Regularity means holomorphy at every point, expressed in the meromorphic field. -/
theorem mem_ellipticRegularDifferentials_iff (L : PeriodPair) (x : ellipticSubfield L) :
    x ∈ ellipticRegularDifferentials L ↔
      ∃ (f : ℂ → ℂ) (hf : Differentiable ℂ f),
        ofMeromorphic f (fun z => (hf.analyticAt z).meromorphicAt) = (x : MeromorphicPlane) := by
  constructor
  · rintro ⟨ω, rfl⟩
    exact ⟨fun z => ω.val z 1, ω.property.1.clm_apply (differentiable_const 1),
      (ellipticDifferentialCoefficient_rep L ω).symm⟩
  · rintro ⟨f, hf, hfx⟩
    have hper : ∀ p ∈ L.lattice, Function.Periodic f p := by
      intro p hp z
      have h := x.property p hp
      rw [← hfx, planeTranslate_ofMeromorphic] at h
      have heq := (ofMeromorphic_eq_iff _ _).mp h z
      have hshift : ContinuousAt (fun w : ℂ => f (w + p)) z :=
        (hf.continuous.comp (continuous_id.add continuous_const)).continuousAt
      exact tendsto_nhds_unique (hshift.continuousWithinAt.tendsto.congr' heq)
        (hf.continuous.continuousAt.continuousWithinAt.tendsto)
    have hconst (z : ℂ) : f z = f 0 :=
      hf.apply_eq_apply_of_bounded
        (IsZLattice.isCompact_range_of_periodic L.lattice f hf.continuous
          (fun z p hp => hper p hp z)).isBounded z 0
    refine ⟨ellipticConstantDifferential L (f 0), ?_⟩
    apply Subtype.ext
    change ofMeromorphic (fun _ => f 0 * 1) (fun z => MeromorphicAt.const (f 0 * 1) z) = _
    rw [← hfx]
    apply (ofMeromorphic_eq_iff _ _).mpr
    intro z
    exact Filter.Eventually.of_forall fun w => (mul_one (f 0)).trans (hconst w).symm

/-- Regular field differentials and their holomorphic representatives are linearly equivalent. -/
def ellipticRegularDifferentialEquiv (L : PeriodPair) :
    ellipticHolomorphicDifferentials L ≃ₗ[ℂ] ellipticRegularDifferentials L :=
  LinearEquiv.ofInjective (ellipticDifferentialCoefficient L)
    (ellipticDifferentialCoefficient_injective L)

instance ellipticRegularDifferentials_finiteDimensional (L : PeriodPair) :
    FiniteDimensional ℂ (ellipticRegularDifferentials L) :=
  Module.Finite.equiv (ellipticRegularDifferentialEquiv L)

theorem ellipticRegularDifferentials_finrank (L : PeriodPair) :
    Module.finrank ℂ (ellipticRegularDifferentials L) = 1 :=
  (ellipticRegularDifferentialEquiv L).symm.finrank_eq.trans (ellipticGeometricGenus_eq_one L)

/-- The Weierstrass coordinate as an element of the elliptic field itself. -/
def ellipticCoordinateX (L : PeriodPair) : ellipticSubfield L :=
  ⟨weierstrassPElement L, weierstrassPElement_mem L⟩

/-- The derivative coordinate as an element of the elliptic field itself. -/
def ellipticCoordinateY (L : PeriodPair) : ellipticSubfield L :=
  ⟨derivWeierstrassPElement L, derivWeierstrassPElement_mem L⟩

/-- The two coordinates satisfy the Weierstrass equation inside the field. -/
theorem ellipticCoordinates_relation (L : PeriodPair) :
    ellipticCoordinateY L ^ 2 = 4 * ellipticCoordinateX L ^ 3 -
      algebraMap ℂ (ellipticSubfield L) L.g₂ * ellipticCoordinateX L -
      algebraMap ℂ (ellipticSubfield L) L.g₃ :=
  Subtype.ext (weierstrass_relation_plane L)

theorem ellipticCoordinateX_transcendental (L : PeriodPair) :
    Transcendental ℂ (ellipticCoordinateX L) := by
  apply transcendental_iff.mpr
  intro P hP
  by_contra hne
  apply eval_weierstrassP_ne_zero L hne
  have h := congrArg (ellipticSubfield L).val hP
  rw [← Polynomial.aeval_algHom_apply, map_zero] at h
  change Polynomial.aeval (weierstrassPElement L) P = 0 at h
  rwa [weierstrassPElement, aeval_ofMeromorphic] at h

/-- These two elements generate the whole field, not merely a subfield of elliptic functions. -/
theorem ellipticCoordinates_generate (L : PeriodPair) :
    IntermediateField.adjoin ℂ {ellipticCoordinateX L, ellipticCoordinateY L} = ⊤ := by
  apply IntermediateField.map_injective (ellipticSubfield L).val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
    IntermediateField.fieldRange_val]
  simp only [Set.image_insert_eq, Set.image_singleton]
  exact (ellipticSubfield_eq_adjoin L).symm

/-- The cubic relation makes the field algebraic over the polynomial ring in `℘`. -/
theorem ellipticField_isAlgebraic_coordinate (L : PeriodPair) :
    Algebra.IsAlgebraic (Algebra.adjoin ℂ {ellipticCoordinateX L}) (ellipticSubfield L) := by
  let B := Algebra.adjoin ℂ {ellipticCoordinateX L}
  let x : B := ⟨ellipticCoordinateX L, Algebra.subset_adjoin (Set.mem_singleton _)⟩
  let a : B := 4 * x ^ 3 - algebraMap ℂ B L.g₂ * x - algebraMap ℂ B L.g₃
  have hx : IsAlgebraic B (ellipticCoordinateX L) := isAlgebraic_algebraMap x
  have hy : IsAlgebraic B (ellipticCoordinateY L) := by
    apply IsAlgebraic.of_pow (n := 2) (Nat.zero_lt_succ 1)
    have h : ellipticCoordinateY L ^ 2 = algebraMap B (ellipticSubfield L) a :=
      ellipticCoordinates_relation L
    rw [h]
    exact isAlgebraic_algebraMap a
  have hc (c : ℂ) : IsAlgebraic B (algebraMap ℂ (ellipticSubfield L) c) := by
    rw [IsScalarTower.algebraMap_apply ℂ B (ellipticSubfield L)]
    exact isAlgebraic_algebraMap (algebraMap ℂ B c)
  constructor
  intro z
  have hz : z ∈ IntermediateField.adjoin ℂ {ellipticCoordinateX L, ellipticCoordinateY L} := by
    rw [ellipticCoordinates_generate]
    trivial
  exact IntermediateField.adjoin_induction ℂ
    (fun w hw => by
      rcases Set.mem_insert_iff.mp hw with rfl | hw
      · exact hx
      · exact Set.mem_singleton_iff.mp hw ▸ hy)
    hc (fun _ _ _ _ h₁ h₂ => h₁.add h₂) (fun _ _ h => h.inv)
    (fun _ _ _ _ h₁ h₂ => h₁.mul h₂) hz

/-- The transcendental coordinate and algebraic extension give transcendence degree one. -/
theorem ellipticField_trdeg_eq_one (L : PeriodPair) :
    Algebra.trdeg ℂ (ellipticSubfield L) = 1 := by
  letI := ellipticField_isAlgebraic_coordinate L
  exact trdeg_eq_one_of_transcendental (ellipticCoordinateX L)
    (ellipticCoordinateX_transcendental L)

/-- The real basis `1,i` supplies a concrete lattice without any hypotheses. -/
def squarePeriodPair : PeriodPair where
  ω₁ := 1
  ω₂ := Complex.I
  indep := by
    rw [← Complex.coe_basisOneI]
    exact Complex.basisOneI.linearIndependent

/-- The meromorphic function field of the square complex torus. -/
abbrev PositiveGenusBaseField := ↥(ellipticSubfield squarePeriodPair)

/-- Its global holomorphic differentials, as meromorphic coefficients multiplying `dz`. -/
abbrev PositiveGenusBaseDifferentials := ellipticHolomorphicDifferentials squarePeriodPair

theorem positiveGenusBaseField_genus_eq_one : ellipticGeometricGenus squarePeriodPair = 1 :=
  ellipticGeometricGenus_eq_one squarePeriodPair

theorem positiveGenusBaseField_genus_pos : 0 < ellipticGeometricGenus squarePeriodPair := by
  rw [positiveGenusBaseField_genus_eq_one]
  exact Nat.zero_lt_one

/-- A concrete function field with transcendence degree one and a one-dimensional space of
globally regular differentials. All lattice and analytic inputs are discharged. -/
theorem positiveGenusBaseField_spec :
    Algebra.trdeg ℂ PositiveGenusBaseField = 1 ∧
      Module.finrank ℂ (ellipticRegularDifferentials squarePeriodPair) = 1 ∧
      0 < ellipticGeometricGenus squarePeriodPair :=
  ⟨ellipticField_trdeg_eq_one squarePeriodPair,
    ellipticRegularDifferentials_finrank squarePeriodPair, positiveGenusBaseField_genus_pos⟩

end

end GaloisForLFunctions.HTGeometry
