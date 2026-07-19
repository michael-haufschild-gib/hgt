import GaloisForLFunctions.HTGeometry.AnalyticDirichletObservableGrassmannCompleteLattice
import GaloisForLFunctions.HTGeometry.PrimeProfileInvariantGrassmannRepresentation

/-!
# Uniform prime-clock annihilators at inverse limits

The prime-profile Grassmann representation preserves binary intersections.  This file proves the
missing nonempty arbitrary-intersection law and combines it with the invariant-Grassmann Kolchin
correspondence.  Differential algebraicity over an inverse-limit carrier field is equivalent to
one nonzero finite clock certificate working at every stage.  Pointwise differential algebraicity
only supplies a possibly different certificate at each stage.

The distinction is sharp.  A concrete scalar-replicated prime profile has a free complete clock
orbit.  The invariant spans of its successive clock tails have zero intersection; the source is
differentially algebraic over every tail field but hypertranscendental over their intersection.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Set
open scoped Differential

noncomputable section

set_option maxHeartbeats 1200000

/-! ## Complete meets in the prime-profile Grassmann representation -/

/-- Every element of a represented prime-profile Grassmann field already lies in the field of a
finite-dimensional source subspace contained in the original source subspace. -/
theorem exists_finiteDimensional_source_of_mem_primeProfileGrassmannField
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (z : arithmeticFunctionFractionField)
    (hz : z ∈ primeProfileGrassmannField W) :
    ∃ U : Submodule ℂ PrimeProfileClockQuotient,
      U ≤ W ∧ FiniteDimensional ℂ U ∧ z ∈ primeProfileGrassmannField U := by
  unfold primeProfileGrassmannField primeProfileStaticField at hz
  obtain ⟨T, hT, hzT⟩ := IntermediateField.exists_finset_of_mem_adjoin hz
  classical
  let index : {z // z ∈ T} → PrimeProfileGrassmannIndex W := fun t =>
    Classical.choose (hT t.2)
  have hindex : ∀ t : {z // z ∈ T},
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (primeProfileGrassmannSource W (index t)) = t.1 := fun t =>
    Classical.choose_spec (hT t.2)
  let source : {z // z ∈ T} → PrimeProfileClockQuotient := fun t =>
    ((Module.Basis.ofVectorSpace ℂ W (index t) : W) : PrimeProfileClockQuotient)
  let U : Submodule ℂ PrimeProfileClockQuotient :=
    Submodule.span ℂ (Set.range source)
  have hUW : U ≤ W := by
    rw [Submodule.span_le]
    rintro q ⟨t, rfl⟩
    exact (Module.Basis.ofVectorSpace ℂ W (index t)).2
  have hTU : IntermediateField.adjoin finitePrimeCoefficientField (T : Set _) ≤
      primeProfileGrassmannField U := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    let t : {z // z ∈ T} := ⟨y, hy⟩
    rw [← hindex t]
    apply (primeProfileCarrier_mem_grassmannField_iff U
      (primeProfileGrassmannSource W (index t))
      (primeProfileGrassmannSource_supportedOnPositivePrimePowers W (index t))).mpr
    rw [primeProfileClockClass_grassmannSource]
    apply Submodule.subset_span
    exact ⟨t, rfl⟩
  refine ⟨U, hUW, ?_, hTU hzT⟩
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range source)

/-- Finite source intersections are transported to finite intersections of prime-profile
Grassmann fields. -/
theorem primeProfileGrassmannField_finset_inf
    {ι : Type*}
    (U : Submodule ℂ PrimeProfileClockQuotient)
    (W : ι → Submodule ℂ PrimeProfileClockQuotient) (S : Finset ι) :
    primeProfileGrassmannField (U ⊓ (⨅ i ∈ S, W i)) =
      primeProfileGrassmannField U ⊓
        (⨅ i ∈ S, primeProfileGrassmannField (W i)) := by
  classical
  induction S using Finset.induction_on generalizing U with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.iInf_insert, Finset.iInf_insert, ← inf_assoc, ih,
        ← primeProfileGrassmannField_inf U (W i), inf_assoc]

/-- **Complete prime-profile Grassmann meet law.** Every nonempty intersection of represented
prime-profile fields is exactly the field represented by the intersection of the source
subspaces. -/
theorem primeProfileGrassmannField_iInf
    {ι : Type*} [Nonempty ι]
    (W : ι → Submodule ℂ PrimeProfileClockQuotient) :
    (⨅ i, primeProfileGrassmannField (W i)) =
      primeProfileGrassmannField (⨅ i, W i) := by
  apply le_antisymm
  · intro z hz
    let i0 : ι := Classical.choice inferInstance
    have hzall : ∀ i, z ∈ primeProfileGrassmannField (W i) := by
      intro i
      exact (iInf_le (fun i => primeProfileGrassmannField (W i)) i) hz
    obtain ⟨U, hUW, hUfin, hzU⟩ :=
      exists_finiteDimensional_source_of_mem_primeProfileGrassmannField
        (W i0) z (hzall i0)
    letI : FiniteDimensional ℂ U := hUfin
    obtain ⟨S, hS⟩ :=
      exists_finset_inf_eq_iInf_inside_finiteDimensional U W
    have hzFiniteFields : z ∈
        primeProfileGrassmannField U ⊓
          (⨅ i ∈ S, primeProfileGrassmannField (W i)) := by
      refine ⟨hzU, ?_⟩
      apply IntermediateField.mem_sInf.mpr
      rintro F ⟨i, rfl⟩
      apply IntermediateField.mem_sInf.mpr
      rintro F ⟨hi, rfl⟩
      exact hzall i
    rw [← primeProfileGrassmannField_finset_inf U W S] at hzFiniteFields
    rw [← hS] at hzFiniteFields
    apply (primeProfileGrassmannField_le_iff
      (U ⊓ ⨅ i, W i) (⨅ i, W i)).2 inf_le_right
    exact hzFiniteFields
  · apply le_iInf
    intro i
    exact (primeProfileGrassmannField_le_iff (⨅ j, W j) (W i)).2 (iInf_le W i)

/-! ## Uniform clock certificates -/

/-- The finite clock-certificate space for a source over a quotient subspace. -/
def primeProfileClockCertificateSpace
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (f : ArithmeticFunction ℂ) : Submodule ℂ (Unit × Nat →₀ ℂ) :=
  W.comap (Finsupp.linearCombination ℂ
    (primeProfileClockJetFamily (fun _ : Unit => f)))

@[simp]
theorem mem_primeProfileClockCertificateSpace_iff
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (f : ArithmeticFunction ℂ) (a : Unit × Nat →₀ ℂ) :
    a ∈ primeProfileClockCertificateSpace W f ↔
      a.sum (fun ik z => z •
        primeProfileClockJetFamily (fun _ : Unit => f) ik) ∈ W := by
  simp [primeProfileClockCertificateSpace, Finsupp.linearCombination_apply]

/-- Polynomial-clock saturation is exactly the existence of a nonzero finite clock certificate. -/
theorem primeProfileClockSaturatedIn_iff_certificate
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (f : ArithmeticFunction ℂ) :
    PrimeProfileClockSaturatedIn W f ↔
      ∃ a : Unit × Nat →₀ ℂ,
        a ≠ 0 ∧ a ∈ primeProfileClockCertificateSpace W f := by
  simp only [PrimeProfileClockSaturatedIn,
    mem_primeProfileClockCertificateSpace_iff]

/-- Clock certificates commute exactly with arbitrary source intersections. -/
theorem primeProfileClockCertificateSpace_iInf
    {ι : Type*} (W : ι → Submodule ℂ PrimeProfileClockQuotient)
    (f : ArithmeticFunction ℂ) :
    primeProfileClockCertificateSpace (⨅ i, W i) f =
      ⨅ i, primeProfileClockCertificateSpace (W i) f := by
  ext a
  simp [primeProfileClockCertificateSpace, Submodule.mem_iInf]

/-- Arbitrary intersections of clock-invariant source subspaces remain clock-invariant. -/
theorem PrimeProfileClockInvariant.iInf
    {ι : Type*} (W : ι → Submodule ℂ PrimeProfileClockQuotient)
    (hW : ∀ i, PrimeProfileClockInvariant (W i)) :
    PrimeProfileClockInvariant (⨅ i, W i) := by
  intro q hq
  apply (Submodule.mem_iInf _).2
  intro i
  exact hW i q ((Submodule.mem_iInf _).1 hq i)

/-- **Uniform-annihilator inverse-limit law.** Differential algebraicity over a nonempty
intersection of invariant represented fields is equivalent to one nonzero finite clock
certificate that works in every source subspace simultaneously. -/
theorem differentialAlgebraic_over_primeProfileGrassmannField_iInf_iff_uniformCertificate
    {ι : Type*} [Nonempty ι]
    (W : ι → Submodule ℂ PrimeProfileClockQuotient)
    (hW : ∀ i, PrimeProfileClockInvariant (W i))
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f) :
    GaloisForLFunctions.DifferentialAlgebraicOver
        (⨅ i, primeProfileGrassmannField (W i))
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) ↔
      ∃ a : Unit × Nat →₀ ℂ, a ≠ 0 ∧
        ∀ i, a ∈ primeProfileClockCertificateSpace (W i) f := by
  rw [primeProfileGrassmannField_iInf W,
    differentialAlgebraic_fractionPrimeProfile_over_grassmannField_iff
      (⨅ i, W i) (PrimeProfileClockInvariant.iInf W hW) f hfsupport,
    primeProfileClockSaturatedIn_iff_certificate,
    primeProfileClockCertificateSpace_iInf]
  simp only [Submodule.mem_iInf]

/-- Stagewise differential algebraicity permits the clock certificate to depend on the stage. -/
theorem differentialAlgebraic_over_every_primeProfileGrassmannField_iff_pointwiseCertificate
    {ι : Type*}
    (W : ι → Submodule ℂ PrimeProfileClockQuotient)
    (hW : ∀ i, PrimeProfileClockInvariant (W i))
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f) :
    (∀ i, GaloisForLFunctions.DifferentialAlgebraicOver
        (primeProfileGrassmannField (W i))
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f)) ↔
      ∀ i, ∃ a : Unit × Nat →₀ ℂ, a ≠ 0 ∧
        a ∈ primeProfileClockCertificateSpace (W i) f := by
  apply forall_congr'
  intro i
  rw [differentialAlgebraic_fractionPrimeProfile_over_grassmannField_iff
    (W i) (hW i) f hfsupport,
    primeProfileClockSaturatedIn_iff_certificate]

/-! ## The sharp free-tail fracture -/

/-- Tail span of a sequence, beginning at clock depth `n`. -/
def linearIndependentTailSpan
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (x : Nat → M) (n : Nat) : Submodule K M :=
  Submodule.span K (Set.range fun k => x (n + k))

/-- A linearly independent sequence has no nonzero vector in all of its successive tail spans. -/
theorem linearIndependentTailSpan_iInf_eq_bot
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (x : Nat → M) (hx : LinearIndependent K x) :
    (⨅ n, linearIndependentTailSpan x n) = ⊥ := by
  apply le_antisymm
  · intro q hq
    have hqSpan : q ∈ Submodule.span K (Set.range x) := by
      have hq0 := (Submodule.mem_iInf _).1 hq 0
      simpa [linearIndependentTailSpan] using hq0
    let qSpan : Submodule.span K (Set.range x) := ⟨q, hqSpan⟩
    have hcoords : ∀ k, hx.repr qSpan k = 0 := by
      intro k
      let coordSpan : Submodule.span K (Set.range x) →ₗ[K] K :=
        (Finsupp.lapply k K).comp hx.repr
      let coord : M →ₗ[K] K :=
        Classical.choose (LinearMap.exists_extend coordSpan)
      have hcoord_ext : ∀ y : Submodule.span K (Set.range x),
          coord y = coordSpan y := by
        intro y
        have h := LinearMap.congr_fun
          (Classical.choose_spec (LinearMap.exists_extend coordSpan)) y
        simpa [coord] using h
      have hgenerator : ∀ j,
          coord (x (k + 1 + j)) = 0 := by
        intro j
        let y : Submodule.span K (Set.range x) :=
          ⟨x (k + 1 + j), Submodule.subset_span (Set.mem_range_self _)⟩
        rw [show coord (x (k + 1 + j)) = coordSpan y by
          simpa [y] using hcoord_ext y]
        have hrepr := hx.repr_eq_single (k + 1 + j) y rfl
        simp [coordSpan, hrepr]
      have htail := (Submodule.mem_iInf _).1 hq (k + 1)
      have hzero : coord q = 0 := by
        refine Submodule.span_induction htail ?_ ?_ ?_ ?_
        · rintro y ⟨j, rfl⟩
          exact hgenerator j
        · exact map_zero coord
        · intro y z hy hz
          rw [map_add, hy, hz, add_zero]
        · intro c y hy
          rw [map_smul, hy, smul_zero]
      have hqcoord := hcoord_ext qSpan
      change coord q = hx.repr qSpan k at hqcoord
      exact hqcoord ▸ hzero
    have hrepr : hx.repr qSpan = 0 := by
      ext k
      exact hcoords k
    have hcomb := hx.linearCombination_repr qSpan
    rw [hrepr, map_zero] at hcomb
    simpa [qSpan] using hcomb.symm
  · exact bot_le

/-- The scalar valuation profile constantly equal to one. -/
def primeClockUnitValuationProfile : Nat → ℂ := fun _ => 1

/-- Its positive-prime-power replication. -/
def primeClockUnitSource : ArithmeticFunction ℂ :=
  scalarReplicatedPrimeProfile primeClockUnitValuationProfile

theorem primeClockUnitSource_supportedOnPositivePrimePowers :
    PrimeProfileSupportedOnPositivePrimePowers primeClockUnitSource :=
  scalarReplicatedPrimeProfile_supportedOnPositivePrimePowers _

/-- The complete prime-clock orbit of the explicit unit valuation source is free. -/
theorem primeClockUnitSource_clockOrbit_linearIndependent :
    LinearIndependent ℂ (fun n : Nat =>
      primeProfileClockClass (primeProfileRotatedLogJet n primeClockUnitSource)) := by
  have hprofile : LinearIndependent ℂ
      (fun _ : Unit => primeClockUnitValuationProfile) := by
    rw [linearIndependent_unique_iff]
    intro hzero
    have h := congrFun hzero 0
    simp [primeClockUnitValuationProfile] at h
  have hclock : PrimeProfileClockIndependent
      (fun _ : Unit => primeClockUnitSource) := by
    apply (scalarReplicatedPrimeProfile_clockIndependent_iff
      (fun _ : Unit => primeClockUnitValuationProfile)).2
    exact hprofile
  have hsub := hclock.comp (fun n : Nat => ((), n)) (by
    intro m n h
    exact congrArg Prod.snd h)
  simpa [PrimeProfileClockIndependent, primeProfileClockJetFamily] using hsub

/-- The invariant source subspace generated by the clock orbit from depth `n` onward. -/
def primeClockUnitTailSubspace (n : Nat) :
    Submodule ℂ PrimeProfileClockQuotient :=
  linearIndependentTailSpan
    (fun k : Nat =>
      primeProfileClockClass (primeProfileRotatedLogJet k primeClockUnitSource)) n

/-- Every clock tail is invariant under the descended logarithmic clock. -/
theorem primeClockUnitTailSubspace_invariant (n : Nat) :
    PrimeProfileClockInvariant (primeClockUnitTailSubspace n) := by
  intro q hq
  unfold primeClockUnitTailSubspace linearIndependentTailSpan at hq ⊢
  refine Submodule.span_induction hq ?_ ?_ ?_ ?_
  · rintro y ⟨k, rfl⟩
    rw [primeProfileQuotientClock_clockClass,
      primeProfileRotatedLogJet_one_comp]
    apply Submodule.subset_span
    exact ⟨k + 1, by simp [Nat.add_assoc]⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

/-- The successive invariant clock tails have zero common source sector. -/
theorem primeClockUnitTailSubspace_iInf_eq_bot :
    (⨅ n, primeClockUnitTailSubspace n) = ⊥ := by
  exact linearIndependentTailSpan_iInf_eq_bot _
    primeClockUnitSource_clockOrbit_linearIndependent

/-- The represented tail fields have the represented zero source field as their exact inverse
limit. -/
theorem primeClockUnitTailField_iInf :
    (⨅ n, primeProfileGrassmannField (primeClockUnitTailSubspace n)) =
      primeProfileGrassmannField ⊥ := by
  rw [primeProfileGrassmannField_iInf, primeClockUnitTailSubspace_iInf_eq_bot]

/-- The unit source is differentially algebraic over every one of its invariant tail fields. -/
theorem primeClockUnitSource_differentialAlgebraic_over_tailField (n : Nat) :
    GaloisForLFunctions.DifferentialAlgebraicOver
        (primeProfileGrassmannField (primeClockUnitTailSubspace n))
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          primeClockUnitSource) := by
  apply (differentialAlgebraic_fractionPrimeProfile_over_grassmannField_iff
    (primeClockUnitTailSubspace n) (primeClockUnitTailSubspace_invariant n)
    primeClockUnitSource primeClockUnitSource_supportedOnPositivePrimePowers).2
  unfold PrimeProfileClockSaturatedIn
  let a : Unit × Nat →₀ ℂ := Finsupp.single ((), n) 1
  refine ⟨a, Finsupp.single_ne_zero.mpr one_ne_zero, ?_⟩
  have hjet : primeProfileClockJetFamily (fun _ : Unit => primeClockUnitSource) ((), n) ∈
      primeClockUnitTailSubspace n := by
    apply Submodule.subset_span
    exact ⟨0, by simp [primeClockUnitTailSubspace, linearIndependentTailSpan,
      primeProfileClockJetFamily]⟩
  simpa [a] using hjet

/-- The unit source is hypertranscendental over the represented zero source field. -/
theorem primeClockUnitSource_not_differentialAlgebraic_over_bottomGrassmannField :
    ¬ GaloisForLFunctions.DifferentialAlgebraicOver
        (primeProfileGrassmannField ⊥)
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          primeClockUnitSource) := by
  intro hDA
  have hsat :=
    (differentialAlgebraic_fractionPrimeProfile_over_grassmannField_iff
      (⊥ : Submodule ℂ PrimeProfileClockQuotient)
      (by
        intro q hq
        simpa using hq)
      primeClockUnitSource primeClockUnitSource_supportedOnPositivePrimePowers).1 hDA
  rcases hsat with ⟨a, ha, hzero⟩
  have hcomb : Finsupp.linearCombination ℂ
      (primeProfileClockJetFamily (fun _ : Unit => primeClockUnitSource)) a = 0 := by
    simpa [Finsupp.linearCombination_apply] using hzero
  have ha0 : a = 0 :=
    (show PrimeProfileClockIndependent (fun _ : Unit => primeClockUnitSource) from by
      simpa [PrimeProfileClockIndependent, primeProfileClockJetFamily] using
        primeClockUnitSource_clockOrbit_linearIndependent.comp
          (fun ik : Unit × Nat => ik.2) (by
            rintro ⟨u, m⟩ ⟨v, n⟩ h
            exact Prod.ext (Subsingleton.elim _ _) h)).finsuppLinearCombination_injective
      (by simpa using hcomb)
  exact ha ha0

/-- **Strict Kolchin inverse-limit fracture.** The explicit prime-supported unit source is
differentially algebraic over every invariant tail field but hypertranscendental over their exact
intersection. -/
theorem primeClockUnitSource_inverseLimit_Kolchin_fracture :
    (∀ n, GaloisForLFunctions.DifferentialAlgebraicOver
        (primeProfileGrassmannField (primeClockUnitTailSubspace n))
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          primeClockUnitSource)) ∧
      ¬ GaloisForLFunctions.DifferentialAlgebraicOver
        (⨅ n, primeProfileGrassmannField (primeClockUnitTailSubspace n))
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          primeClockUnitSource) := by
  constructor
  · exact primeClockUnitSource_differentialAlgebraic_over_tailField
  · rw [primeClockUnitTailField_iInf]
    exact primeClockUnitSource_not_differentialAlgebraic_over_bottomGrassmannField

end

end GaloisForLFunctions.HTGeometry

