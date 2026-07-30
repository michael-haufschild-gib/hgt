import GaloisForLFunctions.HTGeometry.PrimeClockCompletionCorrespondence
import GaloisForLFunctions.HTGeometry.DifferentialIndependentObservableFactorization

/-!
# The invariant Grassmann representation of prime-profile fields

The static prime-tail matroid represents every complex subspace of the prime-clock quotient by an
embedded carrier field.  This representation preserves and reflects order, intersections, and
composita.  The rotated logarithmic clock descends to the quotient; its invariant subspaces are
exactly the subspaces realized by complete clock modules, and their Grassmann fields are already
differential fields.  Thus the source-generated differential fields form the invariant locus of
the full prime-profile Grassmann representation.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Set
open scoped Differential

noncomputable section

set_option maxHeartbeats 1200000

/-! ## The static Grassmann representation -/

/-- Index of a Hamel basis of an arbitrary prime-profile quotient subspace. -/
abbrev PrimeProfileGrassmannIndex
    (W : Submodule ℂ PrimeProfileClockQuotient) :=
  Module.Basis.ofVectorSpaceIndex ℂ W

/-- Positive-prime-power representative of one vector in the canonical Hamel basis of `W`. -/
def primeProfileGrassmannSource
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (i : PrimeProfileGrassmannIndex W) : ArithmeticFunction ℂ :=
  primeProfileClockRepresentative
    ((Module.Basis.ofVectorSpace ℂ W i : W) : PrimeProfileClockQuotient)

@[simp]
theorem primeProfileClockClass_grassmannSource
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (i : PrimeProfileGrassmannIndex W) :
    primeProfileClockClass (primeProfileGrassmannSource W i) =
      ((Module.Basis.ofVectorSpace ℂ W i : W) : PrimeProfileClockQuotient) := by
  exact primeProfileClockClass_representative _

theorem primeProfileGrassmannSource_supportedOnPositivePrimePowers
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (i : PrimeProfileGrassmannIndex W) :
    PrimeProfileSupportedOnPositivePrimePowers (primeProfileGrassmannSource W i) :=
  primeProfileClockRepresentative_supportedOnPositivePrimePowers _

/-- The represented basis classes span exactly the prescribed quotient subspace. -/
theorem primeProfileStaticSubmodule_grassmannSource
    (W : Submodule ℂ PrimeProfileClockQuotient) :
    primeProfileStaticSubmodule (primeProfileGrassmannSource W) = W := by
  let b := Module.Basis.ofVectorSpace ℂ W
  unfold primeProfileStaticSubmodule
  rw [show Set.range (fun i : PrimeProfileGrassmannIndex W =>
      primeProfileClockClass (primeProfileGrassmannSource W i)) =
      W.subtype '' Set.range b by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨b i, Set.mem_range_self i, by simp [b]⟩
    · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp [b]⟩,
    ← Submodule.map_span, b.span_eq, Submodule.map_top,
    Submodule.range_subtype]

/-- The represented basis classes are linearly independent in the ambient quotient. -/
theorem linearIndependent_primeProfileClockClass_grassmannSource
    (W : Submodule ℂ PrimeProfileClockQuotient) :
    LinearIndependent ℂ
      (fun i : PrimeProfileGrassmannIndex W =>
        primeProfileClockClass (primeProfileGrassmannSource W i)) := by
  let b := Module.Basis.ofVectorSpace ℂ W
  have hb := b.linearIndependent.map' W.subtype W.ker_subtype
  simpa only [b, primeProfileClockClass_grassmannSource] using! hb

/-- The embedded field represented by an arbitrary subspace of the prime-profile quotient. -/
def primeProfileGrassmannField
    (W : Submodule ℂ PrimeProfileClockQuotient) :
    IntermediateField finitePrimeCoefficientField arithmeticFunctionFractionField :=
  primeProfileStaticField (primeProfileGrassmannSource W)

/-- Every presentation generates the Grassmann field of its order-zero quotient span. -/
theorem primeProfileStaticField_eq_grassmannField_of_span
    {I : Type*} (c : I → ArithmeticFunction ℂ)
    (hcsupport : ∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i))
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (hspan : primeProfileStaticSubmodule c = W) :
    primeProfileStaticField c = primeProfileGrassmannField W := by
  apply le_antisymm
  · unfold primeProfileStaticField
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    apply carrier_mem_primeProfileStaticField_of_clockClass_mem
      (primeProfileGrassmannSource W)
      (primeProfileGrassmannSource_supportedOnPositivePrimePowers W)
      (c i) (hcsupport i)
    rw [primeProfileStaticSubmodule_grassmannSource W, ← hspan]
    apply Submodule.subset_span
    exact Set.mem_range_self i
  · unfold primeProfileGrassmannField primeProfileStaticField
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    apply carrier_mem_primeProfileStaticField_of_clockClass_mem
      c hcsupport (primeProfileGrassmannSource W i)
      (primeProfileGrassmannSource_supportedOnPositivePrimePowers W i)
    rw [hspan, primeProfileClockClass_grassmannSource]
    exact (Module.Basis.ofVectorSpace ℂ W i).2

/-- Carrier membership in a represented field is exactly membership of its quotient class in the
represented subspace. -/
theorem primeProfileCarrier_mem_grassmannField_iff
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f) :
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f ∈
        primeProfileGrassmannField W ↔
      primeProfileClockClass f ∈ W := by
  unfold primeProfileGrassmannField
  rw [carrier_mem_primeProfileStaticField_iff_clockClass_mem
    (primeProfileGrassmannSource W)
    (primeProfileGrassmannSource_supportedOnPositivePrimePowers W)
    (linearIndependent_primeProfileClockClass_grassmannSource W)
    f hfsupport,
    primeProfileStaticSubmodule_grassmannSource W]

/-- The Grassmann field construction preserves and reflects arbitrary subspace inclusion. -/
theorem primeProfileGrassmannField_le_iff
    (U W : Submodule ℂ PrimeProfileClockQuotient) :
    primeProfileGrassmannField U ≤ primeProfileGrassmannField W ↔ U ≤ W := by
  constructor
  · intro hfield q hq
    have hcarrierU :
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
            (primeProfileClockRepresentative q) ∈ primeProfileGrassmannField U :=
      (primeProfileCarrier_mem_grassmannField_iff U
        (primeProfileClockRepresentative q)
        (primeProfileClockRepresentative_supportedOnPositivePrimePowers q)).mpr (by
          simpa only [primeProfileClockClass_representative] using hq)
    have hcarrierW := hfield hcarrierU
    have hqW := (primeProfileCarrier_mem_grassmannField_iff W
      (primeProfileClockRepresentative q)
      (primeProfileClockRepresentative_supportedOnPositivePrimePowers q)).mp hcarrierW
    simpa only [primeProfileClockClass_representative] using hqW
  · intro hUW
    unfold primeProfileGrassmannField primeProfileStaticField
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    apply (primeProfileCarrier_mem_grassmannField_iff W
      (primeProfileGrassmannSource U i)
      (primeProfileGrassmannSource_supportedOnPositivePrimePowers U i)).mpr
    rw [primeProfileClockClass_grassmannSource]
    exact hUW (Module.Basis.ofVectorSpace ℂ U i).2

/-- Equality of represented fields is exactly equality of quotient subspaces. -/
theorem primeProfileGrassmannField_eq_iff
    (U W : Submodule ℂ PrimeProfileClockQuotient) :
    primeProfileGrassmannField U = primeProfileGrassmannField W ↔ U = W := by
  constructor
  · intro h
    apply le_antisymm
    · exact (primeProfileGrassmannField_le_iff U W).mp h.le
    · exact (primeProfileGrassmannField_le_iff W U).mp h.ge
  · intro h
    exact congrArg primeProfileGrassmannField h

/-- Choice-free carrier pullback recovers an arbitrary represented quotient subspace. -/
theorem primeProfileCarrierPullback_grassmannField
    (W : Submodule ℂ PrimeProfileClockQuotient) :
    primeProfileCarrierPullback (primeProfileGrassmannField W) =
      (W : Set PrimeProfileClockQuotient) := by
  ext q
  unfold primeProfileCarrierPullback
  constructor
  · rintro ⟨f, hfsupport, hclass, hfield⟩
    rw [← hclass]
    exact (primeProfileCarrier_mem_grassmannField_iff W f hfsupport).mp hfield
  · intro hq
    refine ⟨primeProfileClockRepresentative q,
      primeProfileClockRepresentative_supportedOnPositivePrimePowers q,
      primeProfileClockClass_representative q, ?_⟩
    apply (primeProfileCarrier_mem_grassmannField_iff W
      (primeProfileClockRepresentative q)
      (primeProfileClockRepresentative_supportedOnPositivePrimePowers q)).mpr
    simpa only [primeProfileClockClass_representative] using! hq

/-- A complement to `U` can be chosen inside any ambient subspace `V` containing it. -/
theorem exists_primeProfileSubmodule_complement_of_le
    (U V : Submodule ℂ PrimeProfileClockQuotient) (hUV : U ≤ V) :
    ∃ Q : Submodule ℂ PrimeProfileClockQuotient,
      Q ≤ V ∧ Disjoint U Q ∧ U ⊔ Q = V := by
  let U' : Submodule ℂ V := U.comap V.subtype
  obtain ⟨Q', hQ'⟩ := Submodule.exists_isCompl U'
  let Q : Submodule ℂ PrimeProfileClockQuotient := Q'.map V.subtype
  have hQV : Q ≤ V := by
    rintro x ⟨q, hq, rfl⟩
    exact q.2
  have hUQ : Disjoint U Q := by
    rw [Submodule.disjoint_def]
    intro x hxU hxQ
    obtain ⟨q, hq, hqx⟩ := hxQ
    subst x
    have hqU' : q ∈ U' := hxU
    have hqzero : q = 0 :=
      (Submodule.disjoint_def.mp hQ'.disjoint) q hqU' hq
    exact congrArg Subtype.val hqzero
  refine ⟨Q, hQV, hUQ, ?_⟩
  apply le_antisymm
  · exact sup_le hUV hQV
  · intro x hxV
    let xv : V := ⟨x, hxV⟩
    have hxsum : xv ∈ U' ⊔ Q' := by
      rw [hQ'.codisjoint.eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, q, hq, huq⟩ := Submodule.mem_sup.mp hxsum
    apply Submodule.mem_sup.mpr
    refine ⟨u.1, ?_, q.1, ?_, ?_⟩
    · exact hu
    · exact ⟨q, hq, rfl⟩
    · exact congrArg Subtype.val huq

/-- **Prime-profile Grassmann meet law.**  Intersection of represented carrier fields is exactly
the field represented by the intersection of their quotient subspaces. -/
theorem primeProfileGrassmannField_inf
    (U W : Submodule ℂ PrimeProfileClockQuotient) :
    primeProfileGrassmannField U ⊓ primeProfileGrassmannField W =
      primeProfileGrassmannField (U ⊓ W) := by
  let A := U ⊓ W
  obtain ⟨B, hBU, hAB, hABsup⟩ :=
    exists_primeProfileSubmodule_complement_of_le A U inf_le_left
  obtain ⟨C, hCW, hAC, hACsup⟩ :=
    exists_primeProfileSubmodule_complement_of_le A W inf_le_right
  have hUC : Disjoint U C := by
    rw [Submodule.disjoint_def]
    intro z hzU hzC
    have hzW : z ∈ W := hCW hzC
    have hzA : z ∈ A := ⟨hzU, hzW⟩
    exact (Submodule.disjoint_def.mp hAC) z hzA hzC
  have hABC : Disjoint (A ⊔ B) C := by
    rw [hABsup]
    exact hUC
  have hBC : Disjoint B C := hABC.mono_left le_sup_right
  have hA_BC : Disjoint A (B ⊔ C) :=
    hAB.disjoint_sup_right_of_disjoint_sup_left hABC
  let cA := primeProfileGrassmannSource A
  let cB := primeProfileGrassmannSource B
  let cC := primeProfileGrassmannSource C
  have hspanA : primeProfileStaticSubmodule cA = A := by
    simpa only [cA] using primeProfileStaticSubmodule_grassmannSource A
  have hspanB : primeProfileStaticSubmodule cB = B := by
    simpa only [cB] using primeProfileStaticSubmodule_grassmannSource B
  have hspanC : primeProfileStaticSubmodule cC = C := by
    simpa only [cC] using primeProfileStaticSubmodule_grassmannSource C
  have hcA : LinearIndependent ℂ (fun i => primeProfileClockClass (cA i)) := by
    simpa only [cA] using linearIndependent_primeProfileClockClass_grassmannSource A
  have hcB : LinearIndependent ℂ (fun i => primeProfileClockClass (cB i)) := by
    simpa only [cB] using linearIndependent_primeProfileClockClass_grassmannSource B
  have hcC : LinearIndependent ℂ (fun i => primeProfileClockClass (cC i)) := by
    simpa only [cC] using linearIndependent_primeProfileClockClass_grassmannSource C
  have hcBC : LinearIndependent ℂ
      (Sum.elim (fun i => primeProfileClockClass (cB i))
        (fun i => primeProfileClockClass (cC i))) :=
    hcB.sum_type hcC (by
      rw [show Submodule.span ℂ
          (Set.range (fun i => primeProfileClockClass (cB i))) = B by
        simpa only [primeProfileStaticSubmodule] using hspanB,
        show Submodule.span ℂ
          (Set.range (fun i => primeProfileClockClass (cC i))) = C by
        simpa only [primeProfileStaticSubmodule] using hspanC]
      exact hBC)
  have hspanBC : Submodule.span ℂ
      (Set.range (Sum.elim (fun i => primeProfileClockClass (cB i))
        (fun i => primeProfileClockClass (cC i)))) = B ⊔ C := by
    rw [Set.Sum.elim_range, Submodule.span_union]
    change primeProfileStaticSubmodule cB ⊔ primeProfileStaticSubmodule cC = B ⊔ C
    rw [hspanB, hspanC]
  have hcABC : LinearIndependent ℂ
      (Sum.elim (fun i => primeProfileClockClass (cA i))
        (Sum.elim (fun i => primeProfileClockClass (cB i))
          (fun i => primeProfileClockClass (cC i)))) :=
    hcA.sum_type hcBC (by
      change Disjoint
        (Submodule.span ℂ (Set.range (fun i => primeProfileClockClass (cA i))))
        (Submodule.span ℂ (Set.range
          (Sum.elim (fun i => primeProfileClockClass (cB i))
            (fun i => primeProfileClockClass (cC i)))))
      rw [show Submodule.span ℂ
          (Set.range (fun i => primeProfileClockClass (cA i))) = A by
        simpa only [primeProfileStaticSubmodule] using hspanA,
        hspanBC]
      exact hA_BC)
  let profile := Sum.elim cA (Sum.elim cB cC)
  have hprofileSupport : ∀ z,
      PrimeProfileSupportedOnPositivePrimePowers (profile z) := by
    intro z
    rcases z with i | z
    · exact primeProfileGrassmannSource_supportedOnPositivePrimePowers A i
    · rcases z with i | i
      · exact primeProfileGrassmannSource_supportedOnPositivePrimePowers B i
      · exact primeProfileGrassmannSource_supportedOnPositivePrimePowers C i
  have hprofileClass :
      (fun z => primeProfileClockClass (profile z)) =
        Sum.elim (fun i => primeProfileClockClass (cA i))
          (Sum.elim (fun i => primeProfileClockClass (cB i))
            (fun i => primeProfileClockClass (cC i))) := by
    funext z
    rcases z with i | z
    · rfl
    · rcases z with i | i <;> rfl
  have hAI : AlgebraicIndependent finitePrimeCoefficientField
      (fun z => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (profile z)) := by
    apply (algebraicIndependent_fractionPrimeProfiles_iff_clockClassIndependent_arbitrary
      profile hprofileSupport).mpr
    rw [hprofileClass]
    exact hcABC
  let aCarrier := fun i => algebraMap (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField (cA i)
  let bCarrier := fun i => algebraMap (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField (cB i)
  let cCarrier := fun i => algebraMap (ArithmeticFunction ℂ)
    arithmeticFunctionFractionField (cC i)
  have hcarrierFamily :
      (fun z => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (profile z)) =
        Sum.elim aCarrier (Sum.elim bCarrier cCarrier) := by
    funext z
    rcases z with i | z
    · rfl
    · rcases z with i | i <;> rfl
  have hAIcarrier : AlgebraicIndependent finitePrimeCoefficientField
      (Sum.elim aCarrier (Sum.elim bCarrier cCarrier)) := by
    rw [← hcarrierFamily]
    exact hAI
  have hmeet := algebraicIndependent_threeBlock_adjoin_inf
    aCarrier bCarrier cCarrier hAIcarrier
  have hspanAB : primeProfileStaticSubmodule (Sum.elim cA cB) = U := by
    unfold primeProfileStaticSubmodule
    have hfamily :
        (fun i => primeProfileClockClass (Sum.elim cA cB i)) =
          Sum.elim (fun i => primeProfileClockClass (cA i))
            (fun i => primeProfileClockClass (cB i)) := by
      funext i
      rcases i with i | i <;> rfl
    rw [hfamily, Set.Sum.elim_range, Submodule.span_union]
    rw [show Submodule.span ℂ (Set.range (fun i => primeProfileClockClass (cA i))) = A by
      simpa only [primeProfileStaticSubmodule] using hspanA,
      show Submodule.span ℂ (Set.range (fun i => primeProfileClockClass (cB i))) = B by
      simpa only [primeProfileStaticSubmodule] using hspanB,
      hABsup]
  have hspanAC : primeProfileStaticSubmodule (Sum.elim cA cC) = W := by
    unfold primeProfileStaticSubmodule
    have hfamily :
        (fun i => primeProfileClockClass (Sum.elim cA cC i)) =
          Sum.elim (fun i => primeProfileClockClass (cA i))
            (fun i => primeProfileClockClass (cC i)) := by
      funext i
      rcases i with i | i <;> rfl
    rw [hfamily, Set.Sum.elim_range, Submodule.span_union]
    rw [show Submodule.span ℂ (Set.range (fun i => primeProfileClockClass (cA i))) = A by
      simpa only [primeProfileStaticSubmodule] using hspanA,
      show Submodule.span ℂ (Set.range (fun i => primeProfileClockClass (cC i))) = C by
      simpa only [primeProfileStaticSubmodule] using hspanC,
      hACsup]
  have hfieldAB := primeProfileStaticField_eq_grassmannField_of_span
    (Sum.elim cA cB)
    (fun z => by
      rcases z with i | i
      · exact primeProfileGrassmannSource_supportedOnPositivePrimePowers A i
      · exact primeProfileGrassmannSource_supportedOnPositivePrimePowers B i)
    U hspanAB
  have hfieldAC := primeProfileStaticField_eq_grassmannField_of_span
    (Sum.elim cA cC)
    (fun z => by
      rcases z with i | i
      · exact primeProfileGrassmannSource_supportedOnPositivePrimePowers A i
      · exact primeProfileGrassmannSource_supportedOnPositivePrimePowers C i)
    W hspanAC
  have hfieldA : primeProfileStaticField cA = primeProfileGrassmannField A := by
    simp [cA, primeProfileGrassmannField]
  have hmeetStatic :
      primeProfileStaticField (Sum.elim cA cB) ⊓
          primeProfileStaticField (Sum.elim cA cC) =
        primeProfileStaticField cA := by
    have hABcarrier :
        (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (Sum.elim cA cB i)) =
          Sum.elim aCarrier bCarrier := by
      funext i
      rcases i with i | i <;> rfl
    have hACcarrier :
        (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (Sum.elim cA cC i)) =
          Sum.elim aCarrier cCarrier := by
      funext i
      rcases i with i | i <;> rfl
    simpa only [primeProfileStaticField, hABcarrier, hACcarrier, aCarrier] using hmeet
  rw [hfieldAB, hfieldAC, hfieldA] at hmeetStatic
  simpa only [A] using hmeetStatic

/-- **Prime-profile Grassmann compositum law.**  Field compositum is exactly represented by
subspace sum. -/
theorem primeProfileGrassmannField_sup
    (U W : Submodule ℂ PrimeProfileClockQuotient) :
    primeProfileGrassmannField U ⊔ primeProfileGrassmannField W =
      primeProfileGrassmannField (U ⊔ W) := by
  let cU := primeProfileGrassmannSource U
  let cW := primeProfileGrassmannSource W
  have hspan : primeProfileStaticSubmodule (Sum.elim cU cW) = U ⊔ W := by
    unfold primeProfileStaticSubmodule
    have hfamily :
        (fun i => primeProfileClockClass (Sum.elim cU cW i)) =
          Sum.elim (fun i => primeProfileClockClass (cU i))
            (fun i => primeProfileClockClass (cW i)) := by
      funext i
      rcases i with i | i <;> rfl
    rw [hfamily, Set.Sum.elim_range, Submodule.span_union]
    rw [show Submodule.span ℂ (Set.range (fun i => primeProfileClockClass (cU i))) = U by
      simpa only [cU, primeProfileStaticSubmodule] using
        primeProfileStaticSubmodule_grassmannSource U,
      show Submodule.span ℂ (Set.range (fun i => primeProfileClockClass (cW i))) = W by
      simpa only [cW, primeProfileStaticSubmodule] using
        primeProfileStaticSubmodule_grassmannSource W]
  have hfield := primeProfileStaticField_eq_grassmannField_of_span
    (Sum.elim cU cW)
    (fun z => by
      rcases z with i | i
      · exact primeProfileGrassmannSource_supportedOnPositivePrimePowers U i
      · exact primeProfileGrassmannSource_supportedOnPositivePrimePowers W i)
    (U ⊔ W) hspan
  have hsum :
      primeProfileStaticField (Sum.elim cU cW) =
        primeProfileStaticField cU ⊔ primeProfileStaticField cW := by
    unfold primeProfileStaticField
    have hfamily :
        (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (Sum.elim cU cW i)) =
          Sum.elim
            (fun i => algebraMap (ArithmeticFunction ℂ)
              arithmeticFunctionFractionField (cU i))
            (fun i => algebraMap (ArithmeticFunction ℂ)
              arithmeticFunctionFractionField (cW i)) := by
      funext i
      rcases i with i | i <;> rfl
    rw [hfamily, Set.Sum.elim_range, IntermediateField.adjoin_union]
  rw [hsum] at hfield
  simpa only [cU, cW, primeProfileGrassmannField] using hfield

/-! ## The clock-invariant locus -/

/-- Coordinatewise multiplication by the rotated logarithmic prime clock. -/
def rotatedPrimePowerClockLinearMap :
    (PrimePowerClockIndex → ℂ) →ₗ[ℂ] (PrimePowerClockIndex → ℂ) where
  toFun a x := rotatedPrimePowerClockWeight x * a x
  map_add' a b := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' z a := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem rotatedPrimePowerClockLinearMap_maps_rayLocal :
    rayLocalSubmodule primePowerClockRay ≤
      (rayLocalSubmodule primePowerClockRay).comap rotatedPrimePowerClockLinearMap := by
  intro a ha
  apply ha.subset
  rintro p ⟨x, hxp, hclock⟩
  refine ⟨x, hxp, ?_⟩
  intro hzero
  apply hclock
  simp [rotatedPrimePowerClockLinearMap, hzero]

/-- The rotated logarithmic clock descended to the quotient by finite prime rays. -/
def primeProfileQuotientClock :
    PrimeProfileClockQuotient →ₗ[ℂ] PrimeProfileClockQuotient :=
  Submodule.mapQ
    (rayLocalSubmodule primePowerClockRay)
    (rayLocalSubmodule primePowerClockRay)
    rotatedPrimePowerClockLinearMap
    rotatedPrimePowerClockLinearMap_maps_rayLocal

/-- The descended clock advances the quotient class of a profile by one logarithmic jet. -/
@[simp]
theorem primeProfileQuotientClock_clockClass
    (f : ArithmeticFunction ℂ) :
    primeProfileQuotientClock (primeProfileClockClass f) =
      primeProfileClockClass (primeProfileRotatedLogJet 1 f) := by
  unfold primeProfileQuotientClock primeProfileClockClass
  change (rayLocalSubmodule primePowerClockRay).mkQ
      (rotatedPrimePowerClockLinearMap (primePowerCoordinateProfile f)) =
    (rayLocalSubmodule primePowerClockRay).mkQ
      (primePowerCoordinateProfile (primeProfileRotatedLogJet 1 f))
  congr 1
  funext x
  simp [rotatedPrimePowerClockLinearMap,
    primePowerCoordinateProfile_primeProfileRotatedLogJet]

theorem primeProfileRotatedLogJet_one_comp
    (n : ℕ) (f : ArithmeticFunction ℂ) :
    primeProfileRotatedLogJet 1 (primeProfileRotatedLogJet n f) =
      primeProfileRotatedLogJet (n + 1) f := by
  ext m
  simp only [primeProfileRotatedLogJet_apply, pow_succ]
  ring

/-- A quotient subspace is clock-invariant when it is stable under the descended logarithmic
clock. -/
def PrimeProfileClockInvariant
    (W : Submodule ℂ PrimeProfileClockQuotient) : Prop :=
  ∀ q ∈ W, primeProfileQuotientClock q ∈ W

theorem PrimeProfileClockInvariant.inf
    {U W : Submodule ℂ PrimeProfileClockQuotient}
    (hU : PrimeProfileClockInvariant U)
    (hW : PrimeProfileClockInvariant W) :
    PrimeProfileClockInvariant (U ⊓ W) := by
  intro q hq
  exact ⟨hU q hq.1, hW q hq.2⟩

theorem PrimeProfileClockInvariant.sup
    {U W : Submodule ℂ PrimeProfileClockQuotient}
    (hU : PrimeProfileClockInvariant U)
    (hW : PrimeProfileClockInvariant W) :
    PrimeProfileClockInvariant (U ⊔ W) := by
  intro q hq
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hq
  rw [map_add]
  exact Submodule.add_mem _
    ((show U ≤ U ⊔ W from le_sup_left) (hU u hu))
    ((show W ≤ U ⊔ W from le_sup_right) (hW w hw))

/-- Clock invariance propagates from a source class to every logarithmic jet class. -/
theorem PrimeProfileClockInvariant.jet_mem
    {W : Submodule ℂ PrimeProfileClockQuotient}
    (hW : PrimeProfileClockInvariant W)
    (f : ArithmeticFunction ℂ)
    (hf : primeProfileClockClass f ∈ W) (n : ℕ) :
    primeProfileClockClass (primeProfileRotatedLogJet n f) ∈ W := by
  induction n with
  | zero => simpa [primeProfileRotatedLogJet] using! hf
  | succ n ih =>
      have hnext := hW _ ih
      rw [primeProfileQuotientClock_clockClass,
        primeProfileRotatedLogJet_one_comp] at hnext
      simpa only [Nat.succ_eq_add_one] using hnext

/-- Every complete source clock module is invariant under the descended clock. -/
theorem primeProfileClockSubmodule_invariant
    {I : Type*} (c : I → ArithmeticFunction ℂ) :
    PrimeProfileClockInvariant (primeProfileClockSubmodule c) := by
  intro q hq
  unfold primeProfileClockSubmodule at hq ⊢
  refine Submodule.span_induction (hx := hq) ?_ ?_ ?_ ?_
  · rintro _ ⟨⟨i, n⟩, rfl⟩
    rw [primeProfileClockJetFamily,
      primeProfileQuotientClock_clockClass,
      primeProfileRotatedLogJet_one_comp]
    apply Submodule.subset_span
    exact ⟨(i, n + 1), rfl⟩
  · rw [primeProfileQuotientClock.map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro z x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ z hx

/-- The represented basis presentation of an invariant subspace has complete clock module exactly
equal to that subspace. -/
theorem primeProfileClockSubmodule_grassmannSource
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (hW : PrimeProfileClockInvariant W) :
    primeProfileClockSubmodule (primeProfileGrassmannSource W) = W := by
  apply le_antisymm
  · rw [primeProfileClockSubmodule, Submodule.span_le]
    rintro _ ⟨⟨i, n⟩, rfl⟩
    apply hW.jet_mem
    rw [primeProfileClockClass_grassmannSource]
    exact (Module.Basis.ofVectorSpace ℂ W i).2
  · calc
      W = primeProfileStaticSubmodule (primeProfileGrassmannSource W) :=
        (primeProfileStaticSubmodule_grassmannSource W).symm
      _ ≤ primeProfileClockSubmodule (primeProfileGrassmannSource W) := by
        unfold primeProfileStaticSubmodule primeProfileClockSubmodule
        apply Submodule.span_mono
        rintro _ ⟨i, rfl⟩
        refine ⟨(i, 0), ?_⟩
        simp [primeProfileClockJetFamily]

/-- The represented basis field of an invariant subspace is already the differential field
generated by that basis. -/
theorem differentialAdjoin_grassmannSource_eq_grassmannField
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (hW : PrimeProfileClockInvariant W) :
    GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (primeProfileGrassmannSource W i))) =
      primeProfileGrassmannField W := by
  apply le_antisymm
  · unfold GaloisForLFunctions.differentialAdjoin
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, n, rfl⟩
    rw [differentialJet_algebraMap_primeProfileRotatedLogJet]
    apply (primeProfileCarrier_mem_grassmannField_iff W
      (primeProfileRotatedLogJet n (primeProfileGrassmannSource W i))
      (primeProfileRotatedLogJet_supportedOnPositivePrimePowers
        (primeProfileGrassmannSource W i)
        (primeProfileGrassmannSource_supportedOnPositivePrimePowers W i) n)).mpr
    apply hW.jet_mem
    rw [primeProfileClockClass_grassmannSource]
    exact (Module.Basis.ofVectorSpace ℂ W i).2
  · unfold primeProfileGrassmannField primeProfileStaticField
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact GaloisForLFunctions.subset_differentialAdjoin
      finitePrimeCoefficientField _ (Set.mem_range_self i)

/-- Every invariant quotient subspace is realized by positive-prime-power sources, and every
source presentation produces an invariant subspace. -/
theorem primeProfileClockInvariant_realization
    (W : Submodule ℂ PrimeProfileClockQuotient) :
    PrimeProfileClockInvariant W ↔
      ∃ (I : Type) (c : I → ArithmeticFunction ℂ),
        (∀ i, PrimeProfileSupportedOnPositivePrimePowers (c i)) ∧
        primeProfileClockSubmodule c = W := by
  constructor
  · intro hW
    exact ⟨↥(PrimeProfileGrassmannIndex W), primeProfileGrassmannSource W,
      primeProfileGrassmannSource_supportedOnPositivePrimePowers W,
      primeProfileClockSubmodule_grassmannSource W hW⟩
  · rintro ⟨I, c, hc, rfl⟩
    exact primeProfileClockSubmodule_invariant c

/-- On the invariant Grassmannian, field inclusion is exactly invariant-subspace inclusion. -/
theorem primeProfileInvariantGrassmannField_le_iff
    (U W : Submodule ℂ PrimeProfileClockQuotient)
    (_hU : PrimeProfileClockInvariant U)
    (_hW : PrimeProfileClockInvariant W) :
    primeProfileGrassmannField U ≤ primeProfileGrassmannField W ↔ U ≤ W :=
  primeProfileGrassmannField_le_iff U W

/-- Relative differential independence over an invariant Grassmann field is quotient clock
independence. -/
theorem differentialIndependent_fractionPrimeProfiles_over_grassmannField_iff
    {H : Type*}
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (hW : PrimeProfileClockInvariant W)
    (g : H → ArithmeticFunction ℂ)
    (hgsupport : ∀ h, PrimeProfileSupportedOnPositivePrimePowers (g h)) :
    GaloisForLFunctions.DifferentialIndependent (primeProfileGrassmannField W)
        (fun h => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (g h)) ↔
      LinearIndependent ℂ (W.mkQ ∘ primeProfileClockJetFamily g) := by
  have h :=
    differentialIndependent_fractionPrimeProfiles_relative_iff_clockQuotientIndependent_arbitrary
      (primeProfileGrassmannSource W) g
      (primeProfileGrassmannSource_supportedOnPositivePrimePowers W) hgsupport
  rw [differentialAdjoin_grassmannSource_eq_grassmannField W hW,
    PrimeProfileRelativeClockIndependent,
    primeProfileClockSubmodule_grassmannSource W hW] at h
  exact h

/-- Polynomial saturation of one source class in an invariant quotient subspace. -/
def PrimeProfileClockSaturatedIn
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (f : ArithmeticFunction ℂ) : Prop :=
  ∃ a : Unit × Nat →₀ ℂ, a ≠ 0 ∧
    a.sum (fun ik z => z •
      primeProfileClockJetFamily (fun _ : Unit => f) ik) ∈ W

/-- **Invariant-Grassmann Kolchin law.**  Pulling differential algebraicity back to source classes
is exactly polynomial-clock saturation in the represented invariant subspace. -/
theorem differentialAlgebraic_fractionPrimeProfile_over_grassmannField_iff
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (hW : PrimeProfileClockInvariant W)
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f) :
    GaloisForLFunctions.DifferentialAlgebraicOver (primeProfileGrassmannField W)
        (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) ↔
      PrimeProfileClockSaturatedIn W f := by
  have h := differentialAlgebraic_fractionPrimeProfile_iff_intrinsicClockSaturated
    (primeProfileGrassmannSource W)
    (primeProfileGrassmannSource_supportedOnPositivePrimePowers W)
    f hfsupport
  rw [differentialAdjoin_grassmannSource_eq_grassmannField W hW] at h
  unfold PrimeProfileIntrinsicClockSaturatedOver at h
  unfold PrimeProfileClockSaturatedIn
  rw [primeProfileClockSubmodule_grassmannSource W hW] at h
  exact h

/-- The meet of invariant Grassmann fields is represented by invariant-subspace intersection. -/
theorem primeProfileInvariantGrassmannField_inf
    (U W : Submodule ℂ PrimeProfileClockQuotient)
    (_hU : PrimeProfileClockInvariant U)
    (_hW : PrimeProfileClockInvariant W) :
    primeProfileGrassmannField U ⊓ primeProfileGrassmannField W =
      primeProfileGrassmannField (U ⊓ W) :=
  primeProfileGrassmannField_inf U W

/-- The compositum of invariant Grassmann fields is represented by invariant-subspace sum. -/
theorem primeProfileInvariantGrassmannField_sup
    (U W : Submodule ℂ PrimeProfileClockQuotient)
    (_hU : PrimeProfileClockInvariant U)
    (_hW : PrimeProfileClockInvariant W) :
    primeProfileGrassmannField U ⊔ primeProfileGrassmannField W =
      primeProfileGrassmannField (U ⊔ W) :=
  primeProfileGrassmannField_sup U W

end

end GaloisForLFunctions.HTGeometry
