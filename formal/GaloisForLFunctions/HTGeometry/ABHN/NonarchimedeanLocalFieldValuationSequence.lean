/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.FiniteEtale
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldCohomology
import GaloisForLFunctions.HTGeometry.ABHN.ContinuousGaloisCohomology
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldBrauer
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2NormQuotient
import GaloisForLFunctions.HTGeometry.TameInertiaRigidity
import GaloisForLFunctions.HTGeometry.LocalRamificationOrderLaw
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.LocalRing.Etale
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.IrreducibleRing
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.Dedekind
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Split valuation sequence for nonarchimedean local fields

The intrinsic value group of a nonarchimedean local field is isomorphic to `ℤᵐ⁰`.  Transporting
its valuation along that isomorphism and choosing a uniformizer gives a closed split sequence
of field units.  This is a local-class-field-theory prerequisite, not a reciprocity map or a
calculation of the local Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial
open TensorProduct
open scoped ValuativeRel WithZero WithZeroMulInt Valued

attribute [local instance] Ideal.Quotient.field

universe u v

/-- The canonical valuation relation on the fraction field of a discrete valuation ring. -/
@[reducible] noncomputable def discreteValuationRingFractionFieldValuativeRel
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] : ValuativeRel F :=
  ValuativeRel.ofValuation ((IsDiscreteValuationRing.maximalIdeal A).valuation F)

/-- The valuation topology induced by a specified valuation relation on a DVR fraction field. -/
@[reducible] noncomputable def discreteValuationRingFractionFieldTopology
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [ValuativeRel F] : TopologicalSpace F :=
  ValuativeRel.topologicalSpace F

/-- A discrete valuation ring is the integer ring of the canonical valuation on its fraction
field.  This identifies the integral model with the valuation ring that underlies the resulting
local field. -/
noncomputable def discreteValuationRingFractionFieldIntegerEquiv
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    A ≃+* ((IsDiscreteValuationRing.maximalIdeal A).valuation F).integer :=
  IsDiscreteValuationRing.equivValuationSubring

/-- Every valuation-zero unit in the fraction field of a discrete valuation ring comes from an
integral unit.  This transfers a local norm statement proved on integral units to the valuation
kernel of the fraction field. -/
theorem discreteValuationRingFractionField_tameValHom_ker_unitsMap_surjective
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (a : Fˣ)
    (h : a ∈ (tameValHom ((IsDiscreteValuationRing.maximalIdeal A).valuation F)).ker) :
    ∃ b : Aˣ, Units.map (algebraMap A F) b = a := by
  let v : Valuation F (WithZero (Multiplicative ℤ)) :=
    (IsDiscreteValuationRing.maximalIdeal A).valuation F
  let e : A ≃+* v.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring
  have e_coe (x : A) : ((e x : v.valuationSubring) : F) = algebraMap A F x := by
    rfl
  obtain ⟨b, hb⟩ := tameValHom_ker_unitsMap_surjective v a h
  refine ⟨Units.map e.symm.toMonoidHom b, ?_⟩
  apply Units.ext
  rw [← hb]
  change algebraMap A F (e.symm (b : v.valuationSubring)) = (b : F)
  rw [← e_coe]
  exact congrArg Subtype.val (e.apply_symm_apply (b : v.valuationSubring))

/-- The image in a fraction field of an irreducible of a discrete valuation ring has tame
integer valuation one. -/
theorem discreteValuationRingFractionField_irreducible_tameVal
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] {π : A} (hπ : Irreducible π) :
    Multiplicative.toAdd (tameValHom ((IsDiscreteValuationRing.maximalIdeal A).valuation F)
      (Units.mk0 (algebraMap A F π) (by
        intro h
        apply hπ.ne_zero
        apply (IsFractionRing.injective A F)
        simpa using h))) = 1 := by
  have hπF : algebraMap A F π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    apply (IsFractionRing.injective A F)
    simpa using h
  have hcoe : ((tameUnzero ((IsDiscreteValuationRing.maximalIdeal A).valuation F)
      (Units.mk0 (algebraMap A F π) hπF) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero]
    simp only [Units.val_mk0]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDiscreteValuationRing.intValuation_maximalIdeal,
      IsDiscreteValuationRing.addVal_uniformizer hπ]
    simp
  have hun : tameUnzero ((IsDiscreteValuationRing.maximalIdeal A).valuation F)
      (Units.mk0 (algebraMap A F π) hπF) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_inj.1 hcoe
  rw [tameValHom_toAdd, hun]
  simp

/-- The fraction-field extension of a discrete-valuation-ring automorphism preserves the
canonical discrete valuation.  Thus an integral Galois lift cannot change the valuation part of
a local norm. -/
theorem discreteValuationRingFractionField_valuation_ringEquiv
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (e : A ≃+* A) (x : F) :
    (IsDiscreteValuationRing.maximalIdeal A).valuation F
      (IsFractionRing.ringEquivOfRingEquiv e x) =
    (IsDiscreteValuationRing.maximalIdeal A).valuation F x := by
  have h_int (a : A) :
      (IsDiscreteValuationRing.maximalIdeal A).intValuation (e a) =
        (IsDiscreteValuationRing.maximalIdeal A).intValuation a := by
    rw [IsDiscreteValuationRing.intValuation_maximalIdeal,
      IsDiscreteValuationRing.intValuation_maximalIdeal]
    congr 2
    exact addVal_ringEquiv e a
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  have hfield : IsFractionRing.ringEquivOfRingEquiv e
      ((algebraMap A F) a / (algebraMap A F) b) =
      (algebraMap A F) (e a) / (algebraMap A F) (e b) := by
    rw [div_eq_mul_inv, map_mul, map_inv₀,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    simp only [div_eq_mul_inv]
  rw [hfield, Valuation.map_div, Valuation.map_div]
  simp only [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [h_int a, h_int b]

/-- A fraction-field scalar extension preserves the canonical DVR valuation when its integral
map has ramification index one.  This is the field-level form of unramifiedness. -/
theorem discreteValuationRingFractionField_valuation_liftAlgebra
    {A B F E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [Field E] [Algebra B E] [IsFractionRing B E] [Algebra A B]
    [Algebra A E] [IsScalarTower A B E] [Algebra F E] [IsScalarTower A F E]
    (hadd : ∀ a : A, a ≠ 0 →
      IsDiscreteValuationRing.addVal B (algebraMap A B a) =
        IsDiscreteValuationRing.addVal A a) (x : F) :
    (IsDiscreteValuationRing.maximalIdeal B).valuation E (algebraMap F E x) =
      (IsDiscreteValuationRing.maximalIdeal A).valuation F x := by
  have h_int (a : A) (ha : a ≠ 0) :
      (IsDiscreteValuationRing.maximalIdeal B).intValuation (algebraMap A B a) =
        (IsDiscreteValuationRing.maximalIdeal A).intValuation a := by
    rw [IsDiscreteValuationRing.intValuation_maximalIdeal,
      IsDiscreteValuationRing.intValuation_maximalIdeal]
    congr 2
    exact hadd a ha
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hfield : algebraMap F E
      ((algebraMap A F) a / (algebraMap A F) b) =
      (algebraMap B E) ((algebraMap A B) a) /
        (algebraMap B E) ((algebraMap A B) b) := by
    rw [div_eq_mul_inv, map_mul, map_inv₀,
      ← IsScalarTower.algebraMap_apply A F E,
      ← IsScalarTower.algebraMap_apply A F E,
      IsScalarTower.algebraMap_apply A B E,
      IsScalarTower.algebraMap_apply A B E]
    simp only [div_eq_mul_inv]
  rw [hfield, Valuation.map_div, Valuation.map_div]
  simp only [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [h_int a ha, h_int b (nonZeroDivisors.ne_zero hb)]

/-- Passing from a discrete valuation ring to the integer ring of its fraction-field valuation
preserves the residue field. -/
noncomputable def discreteValuationRingFractionFieldResidueFieldEquiv
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    IsLocalRing.ResidueField A ≃+*
      IsLocalRing.ResidueField ((IsDiscreteValuationRing.maximalIdeal A).valuation F).integer :=
  IsLocalRing.ResidueField.mapEquiv (discreteValuationRingFractionFieldIntegerEquiv A F)

/-- Finiteness of the residue field passes from a discrete valuation ring to the canonical
integer ring in its fraction field. -/
theorem discreteValuationRingFractionFieldIntegerResidueField_finite
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Finite (IsLocalRing.ResidueField A)] :
    Finite (IsLocalRing.ResidueField ((IsDiscreteValuationRing.maximalIdeal A).valuation F).integer) :=
  Finite.of_surjective (discreteValuationRingFractionFieldResidueFieldEquiv A F)
    (discreteValuationRingFractionFieldResidueFieldEquiv A F).surjective

/-- The canonical DVR fraction-field topology is valuative. -/
theorem discreteValuationRingFractionField_isValuativeTopology
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
    letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
    IsValuativeTopology F := by
  infer_instance

/-- The canonical DVR fraction-field topology makes inversion and field operations continuous. -/
theorem discreteValuationRingFractionField_isTopologicalDivisionRing
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
    letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
    IsTopologicalDivisionRing F := by
  letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
  letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
  letI := IsTopologicalAddGroup.rightUniformSpace F
  letI := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

/-- The canonical valuation on a DVR fraction field is nontrivial. -/
theorem discreteValuationRingFractionField_isNontrivial
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
    ValuativeRel.IsNontrivial F := by
  letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
  let v : Valuation F ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation F
  letI : v.Compatible := .ofValuation v
  letI : v.IsRankOneDiscrete := by
    change ((IsDiscreteValuationRing.maximalIdeal A).valuation F).IsRankOneDiscrete
    infer_instance
  letI : v.RankOne := Valuation.IsRankOneDiscrete.rankOne v
    (show (1 : NNReal) < 2 from one_lt_two)
  exact (ValuativeRel.isNontrivial_iff_isNontrivial v).mpr inferInstance

/-- The canonical valuation on a DVR fraction field has rank at most one. -/
theorem discreteValuationRingFractionField_isRankLeOne
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
    ValuativeRel.IsRankLeOne F := by
  letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
  let v : Valuation F ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation F
  letI : v.Compatible := .ofValuation v
  exact ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean v

/-- The canonical valuation on a DVR fraction field is discrete. -/
theorem discreteValuationRingFractionField_isDiscrete
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
    ValuativeRel.IsDiscrete F := by
  letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
  let v : Valuation F ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation F
  letI : v.Compatible := .ofValuation v
  exact ValuativeRel.IsDiscrete.of_compatible_withZeroMulInt v

/-- For the canonical valuation topology on a DVR fraction field, local compactness is exactly
the remaining condition needed to obtain a nonarchimedean local field. -/
theorem discreteValuationRingFractionField_isNonarchimedeanLocalField_iff
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
    letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
    IsNonarchimedeanLocalField F ↔ LocallyCompactSpace F := by
  letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
  letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
  constructor
  · intro h
    letI : IsNonarchimedeanLocalField F := h
    infer_instance
  · intro h
    letI : LocallyCompactSpace F := h
    exact
      { toIsValuativeTopology := discreteValuationRingFractionField_isValuativeTopology A F
        toLocallyCompactSpace := h
        toIsNontrivial := discreteValuationRingFractionField_isNontrivial A F }

/-- For a compatible discrete integral-valued valuation, the topology inherited by its valuation
ring is the maximal-ideal adic topology.  Concretely, powers of the maximal ideal are valuation
balls around zero, and these balls are cofinal among valuative neighborhoods. -/
theorem valuationInteger_isAdic_of_discrete
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsValuativeTopology F] (v : Valuation F ℤᵐ⁰) [v.Compatible]
    [IsDiscreteValuationRing v.integer] :
    IsAdic (IsLocalRing.maximalIdeal v.integer) := by
  rw [isAdic_iff]
  constructor
  · intro n
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.integer
    have hπF : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    rw [hπ.maximalIdeal_pow_eq_setOf_le_v_coe_pow]
    change IsOpen (Subtype.val ⁻¹' {x : F | v x ≤ v (π : F) ^ n})
    apply IsOpen.preimage continuous_subtype_val
    have hrad : v.restrict ((π : F) ^ n) ≠ 0 := by
      apply ne_of_gt
      rw [v.restrict_pos_iff]
      exact v.pos_iff.mpr (pow_ne_zero n hπF)
    have hopen := v.isOpen_closedBall hrad
    convert hopen using 1
    ext x
    change v x ≤ v (π : F) ^ n ↔ v.restrict x ≤ v.restrict ((π : F) ^ n)
    rw [v.restrict_le_iff]
    rw [map_pow]
  · intro s hs
    rw [mem_nhds_subtype] at hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨γ, hγ⟩ := v.mem_nhds_iff.mp ht
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.integer
    have hπlt : v (π : F) < 1 := Valuation.integer.v_irreducible_lt_one hπ
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hπlt
      (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass v))) γ)
    refine ⟨n, ?_⟩
    rw [hπ.maximalIdeal_pow_eq_setOf_le_v_coe_pow]
    intro y hy
    apply hts
    apply hγ
    have hy' : v.restrict (y : F) < γ := by
      rw [v.restrict_lt_iff_lt_embedding]
      exact lt_of_le_of_lt hy hn
    simpa using hy'

/-- Algebraic maximal-ideal completeness gives completeness of the valuation ring for the
compatible valuative uniformity. -/
theorem valuationInteger_completeSpace_of_isAdicComplete
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsValuativeTopology F] (v : Valuation F ℤᵐ⁰) [v.Compatible]
    [IsDiscreteValuationRing v.integer]
    [IsAdicComplete (IsLocalRing.maximalIdeal v.integer) v.integer] :
    letI : UniformSpace v.integer := IsTopologicalAddGroup.rightUniformSpace v.integer
    letI : IsUniformAddGroup v.integer :=
      isUniformAddGroup_of_addCommGroup (G := v.integer)
    CompleteSpace v.integer := by
  letI : UniformSpace v.integer := IsTopologicalAddGroup.rightUniformSpace v.integer
  letI : IsUniformAddGroup v.integer :=
    isUniformAddGroup_of_addCommGroup (G := v.integer)
  have h : IsAdic (IsLocalRing.maximalIdeal v.integer) :=
    valuationInteger_isAdic_of_discrete F v
  exact (h.isAdicComplete_iff.mp inferInstance).1

/-- A rank-one discrete valued field is complete when its valuation ring is algebraically
maximal-ideal complete.  This transfers the integral adic-completeness input to the valued
fraction field without adding a local-compactness assumption. -/
theorem valuation_completeSpace_of_isAdicComplete
    (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsValuativeTopology F] (v : Valuation F ℤᵐ⁰) [v.Compatible]
    [v.IsRankOneDiscrete] [IsDiscreteValuationRing v.integer]
    [IsAdicComplete (IsLocalRing.maximalIdeal v.integer) v.integer] :
    letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
    CompleteSpace F := by
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  letI : Valued F ℤᵐ⁰ :=
    { v := v
      toUniformSpace := inferInstance
      toIsUniformAddGroup := inferInstance
      is_topological_valuation := fun s => v.mem_nhds_zero_iff s }
  letI : v.RankOne := Valuation.IsRankOneDiscrete.rankOne v
    (show (1 : NNReal) < 2 from one_lt_two)
  let uO : UniformSpace v.integer := inferInstance
  letI : UniformSpace v.integer := uO
  letI : IsUniformAddGroup v.integer := inferInstance
  have huO : IsTopologicalAddGroup.rightUniformSpace v.integer = uO :=
    IsUniformAddGroup.rightUniformSpace_eq
  have hcomplete : CompleteSpace v.integer := by
    change @CompleteSpace v.integer uO
    rw [← huO]
    exact valuationInteger_completeSpace_of_isAdicComplete F v
  rw [NormedField.completeSpace_iff_isComplete_closedBall]
  rw [← Valued.toNormedField.setOf_mem_integer_eq_closedBall]
  exact completeSpace_coe_iff_isComplete.mp hcomplete

/-- Adic completeness transports across a ring equivalence from a local ring to a valuation
ring, with their respective maximal ideals. -/
theorem isAdicComplete_valuationInteger_of_ringEquiv
    (A F : Type*) [CommRing A] [IsLocalRing A] [Field F]
    (v : Valuation F ℤᵐ⁰) (e : A ≃+* v.integer)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    IsAdicComplete (IsLocalRing.maximalIdeal v.integer) v.integer := by
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
  exact (IsAdicComplete.congr_ringEquiv _ e).mpr inferInstance

/-- The canonical fraction-field valuation of an adically complete DVR is complete for its
valuative uniformity.  This is the analytic completion bridge from integral local algebra to a
complete rank-one valued field. -/
theorem discreteValuationRingFractionField_completeSpace_of_isAdicComplete
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
    letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
    letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
    CompleteSpace F := by
  letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
  letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let v : Valuation F ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation F
  letI : v.Compatible := .ofValuation v
  letI : v.IsRankOneDiscrete := by
    change ((IsDiscreteValuationRing.maximalIdeal A).valuation F).IsRankOneDiscrete
    infer_instance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass v)) := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    exact ⟨Valuation.IsRankOneDiscrete.generator v,
      Valuation.IsRankOneDiscrete.generator_mem_valueGroup v,
      Valuation.IsRankOneDiscrete.generator_ne_one v⟩
  letI : IsDiscreteValuationRing v.integer := by
    change IsDiscreteValuationRing v.valuationSubring
    infer_instance
  let e : A ≃+* v.integer := IsDiscreteValuationRing.equivValuationSubring
  letI : IsAdicComplete (IsLocalRing.maximalIdeal v.integer) v.integer :=
    isAdicComplete_valuationInteger_of_ringEquiv A F v e
  exact valuation_completeSpace_of_isAdicComplete F v

/-- Finiteness of residue fields transports across a ring equivalence of local rings. -/
theorem finite_residueField_of_ringEquiv
    (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) [Finite (IsLocalRing.ResidueField A)] :
    Finite (IsLocalRing.ResidueField B) := by
  let ebar := Ideal.quotientEquiv (IsLocalRing.maximalIdeal A)
    (IsLocalRing.maximalIdeal B) e (IsLocalRing.map_ringEquiv_maximalIdeal e).symm
  letI : Finite (A ⧸ IsLocalRing.maximalIdeal A) := by
    change Finite (IsLocalRing.ResidueField A)
    infer_instance
  exact Finite.of_surjective ebar ebar.surjective

/-- A DVR with finite residue field has locally compact canonical fraction field as soon as it is
maximal-ideal adically complete.  This is the local-field analytic bridge required before a
local invariant or reciprocity construction can be attached. -/
theorem discreteValuationRingFractionField_locallyCompactSpace_of_isAdicComplete_of_finiteResidueField
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Finite (IsLocalRing.ResidueField A)] :
    letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
    letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
    letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
    letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
    LocallyCompactSpace F := by
  letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
  letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let v : Valuation F ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation F
  letI : v.Compatible := .ofValuation v
  letI : v.IsRankOneDiscrete := by
    change ((IsDiscreteValuationRing.maximalIdeal A).valuation F).IsRankOneDiscrete
    infer_instance
  letI : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass v)) := by
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    exact ⟨Valuation.IsRankOneDiscrete.generator v,
      Valuation.IsRankOneDiscrete.generator_mem_valueGroup v,
      Valuation.IsRankOneDiscrete.generator_ne_one v⟩
  letI : IsDiscreteValuationRing v.integer := by
    change IsDiscreteValuationRing v.valuationSubring
    infer_instance
  let e : A ≃+* v.integer := IsDiscreteValuationRing.equivValuationSubring
  letI : Finite (IsLocalRing.ResidueField v.integer) :=
    finite_residueField_of_ringEquiv A v.integer e
  letI : IsAdicComplete (IsLocalRing.maximalIdeal v.integer) v.integer :=
    isAdicComplete_valuationInteger_of_ringEquiv A F v e
  letI : Valued F ℤᵐ⁰ :=
    { v := v
      toUniformSpace := inferInstance
      toIsUniformAddGroup := inferInstance
      is_topological_valuation := fun s => v.mem_nhds_zero_iff s }
  letI : v.RankOne := Valuation.IsRankOneDiscrete.rankOne v
    (show (1 : NNReal) < 2 from one_lt_two)
  letI : CompleteSpace F :=
    discreteValuationRingFractionField_completeSpace_of_isAdicComplete A F
  letI : ProperSpace F :=
    Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  infer_instance

/-- A maximal-ideal adically complete DVR with finite residue field has a nonarchimedean local
fraction field for its canonical discrete valuation topology. -/
theorem discreteValuationRingFractionField_isNonarchimedeanLocalField_of_isAdicComplete_of_finiteResidueField
    (A F : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Finite (IsLocalRing.ResidueField A)] :
    letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
    letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
    IsNonarchimedeanLocalField F := by
  letI : ValuativeRel F := discreteValuationRingFractionFieldValuativeRel A F
  letI : TopologicalSpace F := discreteValuationRingFractionFieldTopology A F
  letI : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  letI : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  exact
    (discreteValuationRingFractionField_isNonarchimedeanLocalField_iff A F).mpr
      (discreteValuationRingFractionField_locallyCompactSpace_of_isAdicComplete_of_finiteResidueField A F)

/-- The valuation of a nonarchimedean local field, normalized to values in `ℤᵐ⁰`. -/
noncomputable def nonarchimedeanLocalFieldIntValuation
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Valuation K ℤᵐ⁰ :=
  Valuation.map (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidWithZeroHom
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.monotone
    (ValuativeRel.valuation K)

/-- The normalized local-field valuation realizes every integer value. -/
theorem nonarchimedeanLocalFieldIntValuation_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Surjective (nonarchimedeanLocalFieldIntValuation K) := by
  intro n
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm n)
  refine ⟨x, ?_⟩
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    (ValuativeRel.valuation K x) = n
  rw [hx]
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).apply_symm_apply n

/-- The normalized and intrinsic valuations have the same valuation subring. -/
theorem nonarchimedeanLocalFieldIntValuation_mem_valuationSubring_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K) :
    x ∈ (nonarchimedeanLocalFieldIntValuation K).valuationSubring ↔ x ∈ 𝒪[K] := by
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
    (ValuativeRel.valuation K x) ≤ 1 ↔ ValuativeRel.valuation K x ≤ 1
  rw [← (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).map_one]
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toOrderIso.le_iff_le

/-- The underlying valuation subrings of the normalized and intrinsic local valuations coincide. -/
theorem nonarchimedeanLocalFieldIntValuationSubring_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (nonarchimedeanLocalFieldIntValuation K).valuationSubring.toSubring = 𝒪[K] := by
  ext x
  exact nonarchimedeanLocalFieldIntValuation_mem_valuationSubring_iff K x

/-- The residue field of the normalized local valuation is the intrinsic local residue field. -/
noncomputable def nonarchimedeanLocalFieldIntValuationResidueFieldEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsLocalRing.ResidueField (nonarchimedeanLocalFieldIntValuation K).valuationSubring ≃+*
      𝓀[K] :=
  IsLocalRing.ResidueField.mapEquiv
    (RingEquiv.subringCongr (nonarchimedeanLocalFieldIntValuationSubring_eq K))

/-- The residue field of the normalized local valuation is finite. -/
noncomputable instance nonarchimedeanLocalFieldIntValuationFiniteResidueField
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Finite (IsLocalRing.ResidueField (nonarchimedeanLocalFieldIntValuation K).valuationSubring) :=
  Finite.of_equiv 𝓀[K] (nonarchimedeanLocalFieldIntValuationResidueFieldEquiv K).toEquiv.symm

/-- A chosen uniformizer for the normalized valuation of a nonarchimedean local field. -/
noncomputable def nonarchimedeanLocalFieldUniformizer
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : K :=
  (nonarchimedeanLocalFieldIntValuation_surjective K (WithZero.exp (-1 : ℤ))).choose

/-- The selected uniformizer has normalized valuation `-1`. -/
theorem nonarchimedeanLocalFieldUniformizer_valuation
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    nonarchimedeanLocalFieldIntValuation K (nonarchimedeanLocalFieldUniformizer K) =
      WithZero.exp (-1 : ℤ) :=
  (nonarchimedeanLocalFieldIntValuation_surjective K (WithZero.exp (-1 : ℤ))).choose_spec

/-- The selected local-field uniformizer is nonzero. -/
theorem nonarchimedeanLocalFieldUniformizer_ne_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : nonarchimedeanLocalFieldUniformizer K ≠ 0 := by
  intro h
  have hval := nonarchimedeanLocalFieldUniformizer_valuation K
  rw [h, map_zero] at hval
  exact absurd hval.symm (by simp [WithZero.exp])

/-- The selected local-field uniformizer as a unit. -/
noncomputable def nonarchimedeanLocalFieldUniformizerUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  Units.mk0 (nonarchimedeanLocalFieldUniformizer K)
    (nonarchimedeanLocalFieldUniformizer_ne_zero K)

/-- The local-field uniformizer maps to `1` under the tame integer valuation. -/
theorem nonarchimedeanLocalFieldUniformizer_tameVal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Multiplicative.toAdd (tameValHom (nonarchimedeanLocalFieldIntValuation K)
      (nonarchimedeanLocalFieldUniformizerUnit K)) = 1 := by
  have hcoe : ((tameUnzero (nonarchimedeanLocalFieldIntValuation K)
      (nonarchimedeanLocalFieldUniformizerUnit K) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero]
    exact nonarchimedeanLocalFieldUniformizer_valuation K
  have hun : tameUnzero (nonarchimedeanLocalFieldIntValuation K)
      (nonarchimedeanLocalFieldUniformizerUnit K) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_inj.1 hcoe
  rw [tameValHom_toAdd, hun]
  simp

/-- Residue data from the normalized valuation of a nonarchimedean local field. -/
noncomputable def nonarchimedeanLocalFieldResidueData
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ResidueData K
      (IsLocalRing.ResidueField (nonarchimedeanLocalFieldIntValuation K).valuationSubring) :=
  residueDataOfValuation (nonarchimedeanLocalFieldIntValuation K)
    (nonarchimedeanLocalFieldUniformizerUnit K)
    (nonarchimedeanLocalFieldUniformizer_tameVal K)

/-- The normalized valuation of a nonarchimedean local field is surjective. -/
theorem nonarchimedeanLocalFieldValuation_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Surjective (nonarchimedeanLocalFieldResidueData K).val :=
  residueDataValuation_surjective _

/-- Valuation-zero units are exactly the kernel of the normalized local-field valuation. -/
theorem nonarchimedeanLocalFieldValuation_exact
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Function.Exact
      (MonoidHom.toAdditive (nonarchimedeanLocalFieldResidueData K).val.ker.subtype)
      (MonoidHom.toAdditive (nonarchimedeanLocalFieldResidueData K).val) :=
  residueDataValuation_exact _

/-- A nonarchimedean local field modulo valuation-zero units has integer value group. -/
noncomputable def nonarchimedeanLocalFieldQuotientKerValuationEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Kˣ ⧸ (nonarchimedeanLocalFieldResidueData K).val.ker ≃* Multiplicative ℤ :=
  residueDataQuotientKerValuationEquiv _

/-- The valuation ring of a nonarchimedean local field is adically complete. -/
theorem nonarchimedeanLocalField_isAdicComplete
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : IsAdicComplete 𝓂[K] 𝒪[K] := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

/-- A finite module over a Noetherian adically complete ring is adically complete.  Completion
commutes with finite modules, and completeness of the base identifies the resulting tensor
product with the original module. -/
theorem adicComplete_of_finiteModule_of_baseAdicComplete
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) [Module.Finite R M] [IsNoetherianRing R] [IsAdicComplete I R] :
    IsAdicComplete I M := by
  let e : AdicCompletion I R ⊗[R] M ≃ₗ[R] M :=
    (TensorProduct.congr (AdicCompletion.ofLinearEquiv I R).symm
      (LinearEquiv.refl R M)).trans (TensorProduct.lid R M)
  have he : ∀ q : AdicCompletion I R ⊗[R] M,
      AdicCompletion.ofTensorProduct I M q = AdicCompletion.of I M (e q) := by
    intro q
    induction q using TensorProduct.induction_on with
    | zero => simp [e]
    | add q q' hq hq' => simp [map_add, hq, hq']
    | tmul r x =>
      simp only [AdicCompletion.ofTensorProduct_tmul, e, LinearEquiv.trans_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.lid_tmul]
      rw [← AdicCompletion.of_ofLinearEquiv_symm I r]
      simp only [AdicCompletion.ofLinearEquiv_symm_of]
      change (algebraMap R (AdicCompletion I R) ((AdicCompletion.ofLinearEquiv I R).symm r)) •
          AdicCompletion.of I M x = _
      rw [IsScalarTower.algebraMap_smul]
      exact ((AdicCompletion.of I M).map_smul _ _).symm
  apply AdicCompletion.of_bijective_iff.mp
  constructor
  · intro x y hxy
    have h : (1 : AdicCompletion I R) ⊗ₜ[R] x = 1 ⊗ₜ[R] y := by
      rw [← AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of I M x,
        ← AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of I M y, hxy]
    calc
      x = e ((1 : AdicCompletion I R) ⊗ₜ[R] x) := by
        change x = (AdicCompletion.ofLinearEquiv I R).symm 1 • x
        rw [show (1 : AdicCompletion I R) = AdicCompletion.of I R 1 by rfl,
          AdicCompletion.ofLinearEquiv_symm_of]
        simp
      _ = e ((1 : AdicCompletion I R) ⊗ₜ[R] y) := congrArg e h
      _ = y := by
        change (AdicCompletion.ofLinearEquiv I R).symm 1 • y = y
        rw [show (1 : AdicCompletion I R) = AdicCompletion.of I R 1 by rfl,
          AdicCompletion.ofLinearEquiv_symm_of]
        simp
  · intro z
    obtain ⟨q, hq⟩ :=
      (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M).surjective z
    exact ⟨e q, (he q).symm.trans hq⟩

/-- An algebraically adically complete ring is complete for its canonical adic topology. -/
theorem completeSpace_of_isAdicComplete_adicTopology
    (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    letI : WithIdeal R := ⟨I⟩
    CompleteSpace R := by
  letI : WithIdeal R := ⟨I⟩
  have hI : IsAdic I := rfl
  exact (hI.isAdicComplete_iff.mp inferInstance).1

/-- An algebraically adically complete ring is Hausdorff for its canonical adic topology. -/
theorem t2Space_of_isAdicComplete_adicTopology
    (R : Type u) [CommRing R] (I : Ideal R) [IsAdicComplete I R] :
    letI : WithIdeal R := ⟨I⟩
    T2Space R := by
  letI : WithIdeal R := ⟨I⟩
  have hI : IsAdic I := rfl
  exact (hI.isAdicComplete_iff.mp inferInstance).2

/-- The valuation ring of a nonarchimedean local field is Henselian. -/
theorem nonarchimedeanLocalField_henselianRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : HenselianRing 𝒪[K] 𝓂[K] := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

/-- A simple root modulo the maximal ideal of a nonarchimedean local field lifts to an integral
root.  This is the Hensel-lifting input needed to construct unramified local extensions from
separable residue-field polynomials. -/
theorem nonarchimedeanLocalField_hensel_lift
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic) (a₀ : 𝒪[K])
    (hroot : Ideal.Quotient.mk 𝓂[K] (f.eval a₀) = 0)
    (hsimple : Ideal.Quotient.mk 𝓂[K] (f.derivative.eval a₀) ≠ 0) :
    ∃ a : 𝒪[K], f.IsRoot a ∧ a - a₀ ∈ 𝓂[K] := by
  letI : HenselianRing 𝒪[K] 𝓂[K] := nonarchimedeanLocalField_henselianRing K
  apply HenselianRing.is_henselian f hf a₀
  · exact Ideal.Quotient.eq_zero_iff_mem.mp hroot
  · exact Ne.isUnit hsimple

/-- A simple root in the residue field of a nonarchimedean local field lifts to an integral root.
This is the residue-polynomial form of Hensel lifting used in unramified-extension constructions. -/
theorem nonarchimedeanLocalField_hensel_lift_residue_root
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (a₀ : 𝒪[K] ⧸ 𝓂[K])
    (hroot : aeval a₀ f = 0)
    (hsimple : aeval a₀ f.derivative ≠ 0) :
    ∃ a : 𝒪[K], f.IsRoot a ∧ Ideal.Quotient.mk 𝓂[K] a = a₀ := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a₀
  have hroot' : Ideal.Quotient.mk 𝓂[K] (f.eval b) = 0 := by
    simpa only [aeval_def, ← Ideal.Quotient.algebraMap_eq, eval₂_at_apply] using hroot
  have hsimple' : Ideal.Quotient.mk 𝓂[K] (f.derivative.eval b) ≠ 0 := by
    simpa only [aeval_def, ← Ideal.Quotient.algebraMap_eq, eval₂_at_apply] using hsimple
  obtain ⟨a, ha, hab⟩ := nonarchimedeanLocalField_hensel_lift K f hf b hroot' hsimple'
  exact ⟨a, ha, Ideal.Quotient.eq.mpr hab⟩

/-- Every element of the finite residue field has a Teichmüller lift: an integral lift fixed by
the `q`-power Frobenius, where `q` is the residue-field cardinality.  These representatives are
the coefficient layer used in constructions of unramified local extensions. -/
theorem nonarchimedeanLocalField_exists_teichmuller_lift
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : 𝓀[K]) :
    ∃ a : 𝒪[K], Ideal.Quotient.mk 𝓂[K] a = x ∧ a ^ Nat.card 𝓀[K] = a := by
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  let f : Polynomial 𝒪[K] := X ^ Nat.card 𝓀[K] - X
  have hf : f.Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card 𝓀[K])
  have hroot : aeval x f = 0 := by
    change Polynomial.eval₂ (algebraMap 𝒪[K] 𝓀[K]) x f = 0
    dsimp [f]
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]
  have hsimple : aeval x f.derivative ≠ 0 := by
    change Polynomial.eval₂ (algebraMap 𝒪[K] 𝓀[K]) x f.derivative ≠ 0
    dsimp [f]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_X_pow, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, map_natCast, sub_ne_zero]
    rw [Polynomial.eval₂_natCast, Nat.card_eq_fintype_card, Nat.cast_card_eq_zero, zero_mul,
      Polynomial.eval₂_one]
    exact zero_ne_one
  obtain ⟨a, ha, hres⟩ :=
    nonarchimedeanLocalField_hensel_lift_residue_root K f hf x hroot hsimple
  refine ⟨a, hres, ?_⟩
  change f.eval a = 0 at ha
  dsimp [f] at ha
  exact sub_eq_zero.mp (by simpa only [eval_sub, eval_pow, eval_X] using ha)

/-- Every nonzero residue class has a unit Teichmüller lift.  The lift has order dividing
`q - 1`, the order of the residue-unit group. -/
theorem nonarchimedeanLocalField_exists_teichmuller_unit_lift
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : 𝓀[K]ˣ) :
    ∃ a : 𝒪[K]ˣ, Ideal.Quotient.mk 𝓂[K] (a : 𝒪[K]) = (x : 𝓀[K]) ∧
      a ^ (Nat.card 𝓀[K] - 1) = 1 := by
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  obtain ⟨a, ha, hpow⟩ :=
    nonarchimedeanLocalField_exists_teichmuller_lift K (x : 𝓀[K])
  have ha' : IsLocalRing.residue 𝒪[K] a ≠ 0 := by
    change Ideal.Quotient.mk 𝓂[K] a ≠ 0
    rw [ha]
    exact x.ne_zero
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit a).mp ha'
  have hpow' : u ^ Nat.card 𝓀[K] = u := by
    apply Units.ext
    change (u : 𝒪[K]) ^ Nat.card 𝓀[K] = u
    simpa only [hu] using hpow
  refine ⟨u, ?_, ?_⟩
  · change Ideal.Quotient.mk 𝓂[K] (u : 𝒪[K]) = (x : 𝓀[K])
    rw [hu]
    exact ha
  · have hcard : Nat.card 𝓀[K] - 1 + 1 = Nat.card 𝓀[K] := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr Fintype.card_pos)
    calc
      u ^ (Nat.card 𝓀[K] - 1) = u ^ (Nat.card 𝓀[K] - 1) * 1 := (mul_one _).symm
      _ = u ^ (Nat.card 𝓀[K] - 1) * (u * u⁻¹) := by rw [mul_inv_cancel]
      _ = (u ^ (Nat.card 𝓀[K] - 1) * u) * u⁻¹ := by rw [mul_assoc]
      _ = u ^ (Nat.card 𝓀[K] - 1 + 1) * u⁻¹ := by rw [pow_succ]
      _ = u ^ Nat.card 𝓀[K] * u⁻¹ := by rw [hcard]
      _ = u * u⁻¹ := by rw [hpow']
      _ = 1 := mul_inv_cancel u

/-- A Frobenius-fixed integral lift of a residue element is unique.  This upgrades the preceding
existence theorem from arbitrary representatives to the canonical Teichmüller representative. -/
theorem nonarchimedeanLocalField_teichmuller_roots_eq_of_residue_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {a b : 𝒪[K]}
    (ha : a ^ Nat.card 𝓀[K] = a) (hb : b ^ Nat.card 𝓀[K] = b)
    (hres : Ideal.Quotient.mk 𝓂[K] a = Ideal.Quotient.mk 𝓂[K] b) : a = b := by
  letI : Fintype 𝓀[K] := Fintype.ofFinite _
  let f : Polynomial 𝒪[K] := X ^ Nat.card 𝓀[K] - X
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := f)
  · change f.eval a = 0
    dsimp [f]
    rw [eval_sub, eval_pow, eval_X, ha, sub_self]
  · change f.eval b = 0
    dsimp [f]
    rw [eval_sub, eval_pow, eval_X, hb, sub_self]
  · rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hres, sub_self]
  · apply IsLocalRing.notMem_maximalIdeal.mp
    intro hmem
    have hzero : Ideal.Quotient.mk 𝓂[K] (f.derivative.eval a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    dsimp [f] at hzero
    simp only [derivative_sub, derivative_X, derivative_X_pow, eval_sub, eval_mul, eval_pow,
      eval_X] at hzero
    rw [Nat.card_eq_fintype_card, C_eq_natCast, eval_natCast, eval_one] at hzero
    rw [map_sub, map_mul] at hzero
    have hcardzero : Ideal.Quotient.mk 𝓂[K] (Fintype.card 𝓀[K] : 𝒪[K]) = 0 := by
      change (Fintype.card 𝓀[K] : 𝓀[K]) = 0
      exact Nat.cast_card_eq_zero _
    rw [hcardzero, zero_mul, map_one, zero_sub] at hzero
    exact neg_ne_zero.mpr (one_ne_zero : (1 : 𝓀[K]) ≠ 0) hzero

/-- The canonical Teichmüller lift of a residue-field element. -/
noncomputable def nonarchimedeanLocalFieldTeichmullerLift
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : 𝓀[K] → 𝒪[K] :=
  fun x => (nonarchimedeanLocalField_exists_teichmuller_lift K x).choose

/-- The Teichmüller lift is a section of reduction modulo the maximal ideal. -/
theorem nonarchimedeanLocalFieldTeichmullerLift_residue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : 𝓀[K]) :
    Ideal.Quotient.mk 𝓂[K] (nonarchimedeanLocalFieldTeichmullerLift K x) = x :=
  (nonarchimedeanLocalField_exists_teichmuller_lift K x).choose_spec.1

/-- Every Teichmüller lift is fixed by the residue-cardinality Frobenius. -/
theorem nonarchimedeanLocalFieldTeichmullerLift_pow_card
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : 𝓀[K]) :
    (nonarchimedeanLocalFieldTeichmullerLift K x) ^ Nat.card 𝓀[K] =
      nonarchimedeanLocalFieldTeichmullerLift K x :=
  (nonarchimedeanLocalField_exists_teichmuller_lift K x).choose_spec.2

/-- The Teichmüller lift preserves `1`. -/
theorem nonarchimedeanLocalFieldTeichmullerLift_one
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    nonarchimedeanLocalFieldTeichmullerLift K 1 = 1 := by
  apply nonarchimedeanLocalField_teichmuller_roots_eq_of_residue_eq K
  · exact nonarchimedeanLocalFieldTeichmullerLift_pow_card K 1
  · simp
  · rw [nonarchimedeanLocalFieldTeichmullerLift_residue K 1, map_one]
    rfl

/-- The canonical Teichmüller lift is multiplicative. -/
theorem nonarchimedeanLocalFieldTeichmullerLift_mul
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : 𝓀[K]) :
    nonarchimedeanLocalFieldTeichmullerLift K (x * y) =
      nonarchimedeanLocalFieldTeichmullerLift K x *
        nonarchimedeanLocalFieldTeichmullerLift K y := by
  apply nonarchimedeanLocalField_teichmuller_roots_eq_of_residue_eq K
  · exact nonarchimedeanLocalFieldTeichmullerLift_pow_card K (x * y)
  · rw [mul_pow, nonarchimedeanLocalFieldTeichmullerLift_pow_card,
      nonarchimedeanLocalFieldTeichmullerLift_pow_card]
  · rw [nonarchimedeanLocalFieldTeichmullerLift_residue K (x * y), map_mul,
      nonarchimedeanLocalFieldTeichmullerLift_residue K x,
      nonarchimedeanLocalFieldTeichmullerLift_residue K y]
    rfl

/-- Multiplicative Teichmüller section of reduction on the whole residue field. -/
noncomputable def nonarchimedeanLocalFieldTeichmullerLiftMonoidHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : 𝓀[K] →* 𝒪[K] where
  toFun := nonarchimedeanLocalFieldTeichmullerLift K
  map_one' := nonarchimedeanLocalFieldTeichmullerLift_one K
  map_mul' := nonarchimedeanLocalFieldTeichmullerLift_mul K

/-- Teichmüller section restricted to residue-field units. -/
noncomputable def nonarchimedeanLocalFieldTeichmullerUnitHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : 𝓀[K]ˣ →* 𝒪[K]ˣ :=
  Units.map (nonarchimedeanLocalFieldTeichmullerLiftMonoidHom K)

/-- Reduction composed with the Teichmüller unit section is the identity on residue units. -/
theorem nonarchimedeanLocalFieldTeichmullerUnitHom_residue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : 𝓀[K]ˣ) :
    Ideal.Quotient.mk 𝓂[K]
      ((nonarchimedeanLocalFieldTeichmullerUnitHom K x : 𝒪[K]ˣ) : 𝒪[K]) = (x : 𝓀[K]) := by
  change Ideal.Quotient.mk 𝓂[K] (nonarchimedeanLocalFieldTeichmullerLift K (x : 𝓀[K])) =
    (x : 𝓀[K])
  exact nonarchimedeanLocalFieldTeichmullerLift_residue K (x : 𝓀[K])

/-- Reduction of units from the valuation ring to its residue field. -/
noncomputable def nonarchimedeanLocalFieldReductionUnits
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : 𝒪[K]ˣ →* 𝓀[K]ˣ :=
  Units.map (Ideal.Quotient.mk 𝓂[K]).toMonoidHom

/-- Principal units of a nonarchimedean local field, defined as the kernel of reduction. -/
noncomputable def nonarchimedeanLocalFieldPrincipalUnitGroup
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Subgroup 𝒪[K]ˣ :=
  (nonarchimedeanLocalFieldReductionUnits K).ker

/-- Reduction after the Teichmüller section is the identity on residue units. -/
theorem nonarchimedeanLocalFieldReductionUnits_teichmuller
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : 𝓀[K]ˣ) :
    nonarchimedeanLocalFieldReductionUnits K
      (nonarchimedeanLocalFieldTeichmullerUnitHom K x) = x := by
  apply Units.ext
  exact nonarchimedeanLocalFieldTeichmullerUnitHom_residue K x

/-- Every integral unit is a Teichmüller lift of its residue times a principal unit.  This is the
unit decomposition that isolates the finite residue contribution from the principal-unit layer
in local norm computations. -/
theorem nonarchimedeanLocalField_unit_decompose
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (u : 𝒪[K]ˣ) :
    ∃ ε : nonarchimedeanLocalFieldPrincipalUnitGroup K,
      u = nonarchimedeanLocalFieldTeichmullerUnitHom K
        (nonarchimedeanLocalFieldReductionUnits K u) * ε := by
  let ε := (nonarchimedeanLocalFieldTeichmullerUnitHom K
    (nonarchimedeanLocalFieldReductionUnits K u))⁻¹ * u
  have hε : ε ∈ nonarchimedeanLocalFieldPrincipalUnitGroup K := by
    change nonarchimedeanLocalFieldReductionUnits K ε = 1
    dsimp [ε]
    rw [map_mul, map_inv,
      nonarchimedeanLocalFieldReductionUnits_teichmuller K
        (nonarchimedeanLocalFieldReductionUnits K u), inv_mul_cancel]
  refine ⟨⟨ε, hε⟩, ?_⟩
  change u = nonarchimedeanLocalFieldTeichmullerUnitHom K
    (nonarchimedeanLocalFieldReductionUnits K u) * ε
  dsimp [ε]
  rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- Reduction on integral units is onto, split by the Teichmüller section. -/
theorem nonarchimedeanLocalFieldReductionUnits_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Function.Surjective (nonarchimedeanLocalFieldReductionUnits K) := by
  intro x
  exact ⟨nonarchimedeanLocalFieldTeichmullerUnitHom K x,
    nonarchimedeanLocalFieldReductionUnits_teichmuller K x⟩

/-- Integral units modulo principal units are canonically the finite residue-unit group. -/
noncomputable def nonarchimedeanLocalFieldUnitsModPrincipalUnitsEquivResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    𝒪[K]ˣ ⧸ nonarchimedeanLocalFieldPrincipalUnitGroup K ≃* 𝓀[K]ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective (nonarchimedeanLocalFieldReductionUnits K)
    (nonarchimedeanLocalFieldReductionUnits_surjective K)

/-- A unit is principal exactly when its displacement from `1` belongs to the maximal ideal.
This is the concrete ideal presentation used when Hensel lifting attacks the remaining
principal-unit norm problem. -/
theorem nonarchimedeanLocalField_mem_principalUnitGroup_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (u : (ValuativeRel.valuation K).integerˣ) :
    u ∈ nonarchimedeanLocalFieldPrincipalUnitGroup K ↔
      (u : (ValuativeRel.valuation K).integer) - 1 ∈
        IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer := by
  change nonarchimedeanLocalFieldReductionUnits K u = 1 ↔
    (u : (ValuativeRel.valuation K).integer) - 1 ∈
      IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer
  constructor
  · intro hu
    have hu' := congrArg Units.val hu
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
      (u : (ValuativeRel.valuation K).integer) = 1 at hu'
    exact Ideal.Quotient.mk_eq_one_iff_sub_mem _ |>.mp hu'
  · intro hu
    apply Units.ext
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer)
      (u : (ValuativeRel.valuation K).integer) = 1
    exact Ideal.Quotient.mk_eq_one_iff_sub_mem _ |>.mpr hu

/-- Every principal unit has a uniformizer-coordinate presentation `1 + bπ`.  This is the
concrete identification of the first principal-unit quotient with the residue-field direction. -/
theorem nonarchimedeanLocalField_principalUnit_uniformizer_factor
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (u : nonarchimedeanLocalFieldPrincipalUnitGroup K) :
    ∃ π b : (ValuativeRel.valuation K).integer,
      Irreducible π ∧ π ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer ∧
        ((u : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) =
          1 + b * π := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (ValuativeRel.valuation K).integer
  have hπmem : π ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have hu : ((u : (ValuativeRel.valuation K).integerˣ) :
      (ValuativeRel.valuation K).integer) - 1 ∈
        IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer :=
    (nonarchimedeanLocalField_mem_principalUnitGroup_iff K (u :
      (ValuativeRel.valuation K).integerˣ)).mp u.2
  have huspan : ((u : (ValuativeRel.valuation K).integerˣ) :
      (ValuativeRel.valuation K).integer) - 1 ∈ Ideal.span {π} := by
    rw [← hπ.maximalIdeal_eq]
    exact hu
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp huspan
  refine ⟨π, b, hπ, hπmem, ?_⟩
  calc
    ((u : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) =
        1 + (((u : (ValuativeRel.valuation K).integerˣ) :
          (ValuativeRel.valuation K).integer) - 1) := by ring
    _ = 1 + b * π := by rw [← hb]

/-- The principal unit represented by `1 + x` for a maximal-ideal element `x`. -/
noncomputable def nonarchimedeanLocalFieldPrincipalUnitOfMem
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (x : {x : (ValuativeRel.valuation K).integer // x ∈
      IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer}) :
    nonarchimedeanLocalFieldPrincipalUnitGroup K := by
  have hxnonunits : -(x : (ValuativeRel.valuation K).integer) ∈
      nonunits (ValuativeRel.valuation K).integer := by
    rw [← IsLocalRing.mem_maximalIdeal]
    exact (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer).neg_mem x.2
  have hunit : IsUnit (1 + (x : (ValuativeRel.valuation K).integer)) := by
    simpa using IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      (-(x : (ValuativeRel.valuation K).integer)) hxnonunits
  refine ⟨hunit.unit, ?_⟩
  apply (nonarchimedeanLocalField_mem_principalUnitGroup_iff K hunit.unit).mpr
  change (1 + (x : (ValuativeRel.valuation K).integer)) - 1 ∈
    IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer
  rw [add_sub_cancel_left]
  exact x.2

/-- Principal units are canonically the maximal ideal through `u ↦ u - 1` and `x ↦ 1 + x`.
The transport is an equivalence of types; multiplication on principal units corresponds to the
nonlinear law `(x, y) ↦ x + y + xy` on the ideal. -/
noncomputable def nonarchimedeanLocalFieldPrincipalUnitEquivMaximalIdeal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    nonarchimedeanLocalFieldPrincipalUnitGroup K ≃
      {x : (ValuativeRel.valuation K).integer // x ∈
        IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer} where
  toFun u := ⟨((u : (ValuativeRel.valuation K).integerˣ) :
      (ValuativeRel.valuation K).integer) - 1,
    (nonarchimedeanLocalField_mem_principalUnitGroup_iff K u).mp u.2⟩
  invFun := nonarchimedeanLocalFieldPrincipalUnitOfMem K
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    change 1 + (((u : (ValuativeRel.valuation K).integerˣ) :
      (ValuativeRel.valuation K).integer) - 1) =
        ((u : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer)
    abel
  right_inv x := by
    apply Subtype.ext
    change (((nonarchimedeanLocalFieldPrincipalUnitOfMem K x :
      nonarchimedeanLocalFieldPrincipalUnitGroup K) :
        (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1 = x.1
    simp only [nonarchimedeanLocalFieldPrincipalUnitOfMem, IsUnit.unit_spec]
    abel

/-- The `n`th principal-unit congruence subgroup: units congruent to `1` modulo `𝔪ⁿ`. -/
noncomputable def nonarchimedeanLocalFieldPrincipalUnitFiltration
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    Subgroup (ValuativeRel.valuation K).integerˣ :=
  (Units.map (Ideal.Quotient.mk
    ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n)).toMonoidHom).ker

/-- Membership in `Uⁿ` is the concrete congruence `u - 1 ∈ 𝔪ⁿ`. -/
theorem nonarchimedeanLocalField_mem_principalUnitFiltration_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (u : (ValuativeRel.valuation K).integerˣ) :
    u ∈ nonarchimedeanLocalFieldPrincipalUnitFiltration K n ↔
      (u : (ValuativeRel.valuation K).integer) - 1 ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n := by
  simp only [nonarchimedeanLocalFieldPrincipalUnitFiltration, MonoidHom.mem_ker, Units.ext_iff]
  change Ideal.Quotient.mk
    ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n)
      (u : (ValuativeRel.valuation K).integer) = 1 ↔ _
  exact Ideal.Quotient.mk_eq_one_iff_sub_mem _

/-- The first congruence subgroup is the principal-unit group. -/
theorem nonarchimedeanLocalField_principalUnitFiltration_one
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    nonarchimedeanLocalFieldPrincipalUnitFiltration K 1 =
      nonarchimedeanLocalFieldPrincipalUnitGroup K := by
  ext u
  rw [nonarchimedeanLocalField_mem_principalUnitFiltration_iff,
    nonarchimedeanLocalField_mem_principalUnitGroup_iff]
  simp

/-- Higher congruence subgroups are nested: `Uⁿ⁺¹ ≤ Uⁿ`. -/
theorem nonarchimedeanLocalField_principalUnitFiltration_antitone
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Antitone (nonarchimedeanLocalFieldPrincipalUnitFiltration K) := by
  intro m n hmn u hu
  rw [nonarchimedeanLocalField_mem_principalUnitFiltration_iff] at hu ⊢
  exact Ideal.pow_le_pow_right hmn hu

/-- Two integral units agree modulo `𝔪ⁿ` exactly when their quotient belongs to `Uⁿ`. -/
theorem nonarchimedeanLocalField_unit_div_mem_principalUnitFiltration_iff_sub_mem
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ)
    (u v : (ValuativeRel.valuation K).integerˣ) :
    u⁻¹ * v ∈ nonarchimedeanLocalFieldPrincipalUnitFiltration K n ↔
      (v : (ValuativeRel.valuation K).integer) - (u : (ValuativeRel.valuation K).integer) ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n := by
  rw [nonarchimedeanLocalField_mem_principalUnitFiltration_iff]
  constructor
  · intro huv
    have hmul : (u : (ValuativeRel.valuation K).integer) *
        (((u⁻¹ * v : (ValuativeRel.valuation K).integerˣ) :
          (ValuativeRel.valuation K).integer) - 1) ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n :=
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n).mul_mem_left _ huv
    have hmul_eq : (u : (ValuativeRel.valuation K).integer) *
        (((u⁻¹ * v : (ValuativeRel.valuation K).integerˣ) :
          (ValuativeRel.valuation K).integer) - 1) =
        (v : (ValuativeRel.valuation K).integer) - (u : (ValuativeRel.valuation K).integer) := by
      change (u : (ValuativeRel.valuation K).integer) *
          (((u⁻¹ : (ValuativeRel.valuation K).integerˣ) :
            (ValuativeRel.valuation K).integer) *
            (v : (ValuativeRel.valuation K).integer) - 1) =
          (v : (ValuativeRel.valuation K).integer) - (u : (ValuativeRel.valuation K).integer)
      rw [mul_sub, ← mul_assoc, Units.mul_inv, one_mul, mul_one]
    rwa [hmul_eq] at hmul
  · intro huv
    have hmul : ((u⁻¹ : (ValuativeRel.valuation K).integerˣ) :
        (ValuativeRel.valuation K).integer) *
        ((v : (ValuativeRel.valuation K).integer) -
          (u : (ValuativeRel.valuation K).integer)) ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n :=
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n).mul_mem_left _ huv
    convert hmul using 1
    change ((u⁻¹ : (ValuativeRel.valuation K).integerˣ) :
      (ValuativeRel.valuation K).integer) * (v : (ValuativeRel.valuation K).integer) - 1 =
      ((u⁻¹ : (ValuativeRel.valuation K).integerˣ) :
        (ValuativeRel.valuation K).integer) *
        ((v : (ValuativeRel.valuation K).integer) -
          (u : (ValuativeRel.valuation K).integer))
    rw [mul_sub, Units.inv_mul]

/-- Every element of the `n`th principal-unit filtration has a uniformizer-coordinate
presentation `1 + bπⁿ`. -/
theorem nonarchimedeanLocalField_principalUnitFiltration_uniformizer_factor
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) (u : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
    ∃ π b : (ValuativeRel.valuation K).integer,
      Irreducible π ∧ π ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer ∧
        ((u : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) =
          1 + b * π ^ n := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (ValuativeRel.valuation K).integer
  have hπmem : π ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have hu : ((u : (ValuativeRel.valuation K).integerˣ) :
      (ValuativeRel.valuation K).integer) - 1 ∈
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ n :=
    (nonarchimedeanLocalField_mem_principalUnitFiltration_iff K n (u :
      (ValuativeRel.valuation K).integerˣ)).mp u.2
  have huspan : ((u : (ValuativeRel.valuation K).integerˣ) :
      (ValuativeRel.valuation K).integer) - 1 ∈ Ideal.span {π ^ n} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow] at hu
    exact hu
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp huspan
  refine ⟨π, b, hπ, hπmem, ?_⟩
  calc
    ((u : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) =
        1 + (((u : (ValuativeRel.valuation K).integerˣ) :
          (ValuativeRel.valuation K).integer) - 1) := by ring
    _ = 1 + b * π ^ n := by rw [← hb]

/-- The first-order additive coordinate on `Uⁿ`: `u` is sent to `u - 1` modulo `𝔪ⁿ⁺¹`.
For `n > 0`, quadratic terms land in `𝔪ⁿ⁺¹`, so this is a multiplicative homomorphism into the
additive quotient (written with `Multiplicative`). -/
noncomputable def nonarchimedeanLocalFieldPrincipalUnitLinearization
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n) :
    nonarchimedeanLocalFieldPrincipalUnitFiltration K n →*
      Multiplicative ((ValuativeRel.valuation K).integer ⧸
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1)) where
  toFun u := Multiplicative.ofAdd (Ideal.Quotient.mk
    ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
      (((u : (ValuativeRel.valuation K).integerˣ) :
        (ValuativeRel.valuation K).integer) - 1))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1)) (1 - 1) = 0
    simp
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
        ((((u * v : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
          (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1) =
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
        ((((u : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
          (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1) +
      Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
        ((((v : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
          (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1)
    let I : Ideal (ValuativeRel.valuation K).integer :=
      IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer
    have hu : (((u : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
        (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1 ∈ I ^ n :=
      (nonarchimedeanLocalField_mem_principalUnitFiltration_iff K n u).mp u.2
    have hv : (((v : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
        (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1 ∈ I ^ n :=
      (nonarchimedeanLocalField_mem_principalUnitFiltration_iff K n v).mp v.2
    have hprod : ((((u : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
        (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1) *
        ((((v : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
          (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1) ∈
          I ^ (n + n) := by
      simpa [pow_add] using Ideal.mul_mem_mul hu hv
    have h1n : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn)
    have hpow : I ^ (n + n) ≤ I ^ (n + 1) :=
      Ideal.pow_le_pow_right (Nat.add_le_add_left h1n n)
    have hzero : Ideal.Quotient.mk (I ^ (n + 1))
        (((((u : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
          (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1) *
          ((((v : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
            (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hpow hprod)
    let q := Ideal.Quotient.mk (I ^ (n + 1))
    let a : (ValuativeRel.valuation K).integer :=
      ((u : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer)
    let b : (ValuativeRel.valuation K).integer :=
      ((v : (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer)
    change q
        ((((u * v : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
          (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1) =
      q ((((u : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
        (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1) +
      q ((((v : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
        (ValuativeRel.valuation K).integerˣ) : (ValuativeRel.valuation K).integer) - 1)
    change q (a * b - 1) = q (a - 1) + q (b - 1)
    change q ((a - 1) * (b - 1)) = 0 at hzero
    calc
      q (a * b - 1) = q ((a - 1) + (b - 1) + (a - 1) * (b - 1)) := by
        congr 1
        ring
      _ = q (a - 1) + q (b - 1) + q ((a - 1) * (b - 1)) := by
        rw [map_add, map_add]
      _ = q (a - 1) + q (b - 1) := by
        change _ + _ + Ideal.Quotient.mk (I ^ (n + 1)) _ = _ + _
        rw [hzero, add_zero]

/-- The linearization kernel is exactly the next principal-unit congruence subgroup. -/
theorem nonarchimedeanLocalField_mem_principalUnitLinearization_ker_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n)
    (u : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
    u ∈ (nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn).ker ↔
      (u : (ValuativeRel.valuation K).integerˣ) ∈
        nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1) := by
  change nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn u = 1 ↔ _
  rw [nonarchimedeanLocalField_mem_principalUnitFiltration_iff]
  constructor
  · intro hu
    have hu' := congrArg Multiplicative.toAdd hu
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
      (((u : (ValuativeRel.valuation K).integerˣ) :
        (ValuativeRel.valuation K).integer) - 1) = 0 at hu'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hu'
  · intro hu
    apply Multiplicative.toAdd.injective
    change Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1))
      (((u : (ValuativeRel.valuation K).integerˣ) :
        (ValuativeRel.valuation K).integer) - 1) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hu

/-- Additive presentation of first-order principal-unit linearization. -/
noncomputable def nonarchimedeanLocalFieldPrincipalUnitLinearizationAdd
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n) :
    Additive (nonarchimedeanLocalFieldPrincipalUnitFiltration K n) →+
      (ValuativeRel.valuation K).integer ⧸
        (IsLocalRing.maximalIdeal (ValuativeRel.valuation K).integer) ^ (n + 1) :=
  (nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn).toAdditive

/-- Successive principal-unit congruence groups are exact under first-order linearization. -/
theorem nonarchimedeanLocalFieldPrincipalUnitLinearization_exact
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n) :
    Function.Exact
      (Subgroup.inclusion
        (nonarchimedeanLocalField_principalUnitFiltration_antitone K (Nat.le_succ n))).toAdditive
      (nonarchimedeanLocalFieldPrincipalUnitLinearizationAdd K n hn) := by
  intro u
  change (nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn u.toMul = 1) ↔
    ∃ v, (Subgroup.inclusion
      (nonarchimedeanLocalField_principalUnitFiltration_antitone K (Nat.le_succ n))).toAdditive v = u
  constructor
  · intro hu
    have huKer : u.toMul ∈
        (nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn).ker := hu
    have hu' : ((u.toMul : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
        (ValuativeRel.valuation K).integerˣ) ∈
        nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1) :=
      (nonarchimedeanLocalField_mem_principalUnitLinearization_ker_iff K n hn u.toMul).mp huKer
    exact ⟨Additive.ofMul ⟨((u.toMul : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
      (ValuativeRel.valuation K).integerˣ), hu'⟩, rfl⟩
  · rintro ⟨v, hv⟩
    have hker : (Subgroup.inclusion
        (nonarchimedeanLocalField_principalUnitFiltration_antitone K (Nat.le_succ n))) v.toMul ∈
        (nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn).ker :=
      (nonarchimedeanLocalField_mem_principalUnitLinearization_ker_iff K n hn
        ((Subgroup.inclusion
          (nonarchimedeanLocalField_principalUnitFiltration_antitone K (Nat.le_succ n))) v.toMul)).mpr
          v.toMul.2
    change nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn
      ((Subgroup.inclusion
        (nonarchimedeanLocalField_principalUnitFiltration_antitone K (Nat.le_succ n))) v.toMul) = 1 at hker
    have hv' : (Subgroup.inclusion
        (nonarchimedeanLocalField_principalUnitFiltration_antitone K (Nat.le_succ n))) v.toMul =
        u.toMul := by
      simpa using congrArg Additive.toMul hv
    rw [hv'] at hker
    exact hker

/-- Every monic residue-field polynomial has a monic lift to the valuation ring of the same
degree.  This supplies the defining polynomials used to construct candidate unramified
extensions from finite residue-field extensions. -/
theorem nonarchimedeanLocalField_exists_monic_residuePolynomial_lift
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (g : Polynomial 𝓀[K]) (hg : g.Monic) :
    ∃ f : Polynomial 𝒪[K], f.Monic ∧ f.map (Ideal.Quotient.mk 𝓂[K]) = g ∧
      f.natDegree = g.natDegree := by
  have hlifts : g ∈ Polynomial.lifts (Ideal.Quotient.mk 𝓂[K]) :=
    Polynomial.map_surjective _ Ideal.Quotient.mk_surjective g
  obtain ⟨f, hf, hdegree, hmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hg
  exact ⟨f, hmonic, hf, hdegree⟩

/-- Reducing a root algebra modulo the extended maximal ideal is the root algebra of the
reduced polynomial. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootReductionEquivOfMapEq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K])
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) :
    (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) 𝓂[K]) ≃ₐ[𝒪[K]] AdjoinRoot g := by
  let e₁ : (AdjoinRoot f ⧸ Ideal.map (AdjoinRoot.of f) 𝓂[K]) ≃ₐ[𝒪[K]]
      AdjoinRoot (f.map (Ideal.Quotient.mk 𝓂[K])) :=
    AdjoinRoot.quotEquivQuotMap f 𝓂[K]
  let e₂ : AdjoinRoot (f.map (Ideal.Quotient.mk 𝓂[K])) ≃ₐ[𝒪[K]] AdjoinRoot g :=
    AdjoinRoot.algEquivOfEq 𝒪[K] _ g hfg
  exact e₁.trans e₂

/-- If the reduced polynomial is irreducible, the extension of the base maximal ideal to its
lifted root algebra is maximal. -/
theorem nonarchimedeanLocalFieldAdjoinRootMapMaximalIdealIsMaximal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K])
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    (Ideal.map (AdjoinRoot.of f) 𝓂[K]).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  letI : Fact (Irreducible g) := ⟨hg⟩
  exact (nonarchimedeanLocalFieldAdjoinRootReductionEquivOfMapEq K f g hfg).toMulEquiv.isField
    (Field.toIsField _)

/-- An irreducible residue polynomial lifts to a prime monic polynomial over the valuation ring
of a nonarchimedean local field. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_isPrime
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) : Prime f := by
  have hnil : nilradical 𝒪[K] = ⊥ := nilradical_eq_bot_iff.mpr inferInstance
  letI : (nilradical 𝒪[K]).IsPrime := hnil ▸ Ideal.isPrime_bot
  have hmap : Irreducible (f.map (Ideal.Quotient.mk 𝓂[K])) := by
    rw [hfg]
    exact hg
  have hirr : Irreducible f :=
    hf.irreducible_of_irreducible_map_of_isPrime_nilradical
      (Ideal.Quotient.mk 𝓂[K]) f hmap
  exact hirr.prime

/-- An irreducible residue polynomial stays irreducible after a monic lift to the valuation
ring of a nonarchimedean local field.  Consequently its root algebra is a domain, so this
finite étale local algebra has a genuine fraction field. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_isDomain
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) : IsDomain (AdjoinRoot f) :=
  AdjoinRoot.isDomain_of_prime (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)

/-- A monic lift of an irreducible residue polynomial has positive degree. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) : f.degree ≠ 0 := by
  have hpos : 0 < f.natDegree := by
    rw [← hf.natDegree_map (Ideal.Quotient.mk 𝓂[K]), hfg]
    exact hg.natDegree_pos
  intro h
  apply hpos.ne'
  rw [Polynomial.degree_eq_natDegree hf.ne_zero] at h
  exact WithBot.coe_eq_zero.mp h

/-- The fraction field of the lifted root algebra is finite-dimensional over the fraction field
of the local valuation ring.  The displayed local scalar structures are explicit because
Mathlib deliberately does not register fraction-field lift structures globally. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (AdjoinRoot f)).mpr ?_
      change Function.Injective <|
        AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Module.IsTorsionFree 𝒪[K] (AdjoinRoot f) :=
    AdjoinRoot.noZeroSMulDivisors_of_prime_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg)
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  infer_instance

/-- The fraction field of a monic irreducible residue lift has degree exactly the degree of its
defining polynomial over the fraction field of the valuation ring. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_finrank
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    Module.finrank (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) = f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Algebra.IsAlgebraic 𝒪[K] (AdjoinRoot f) :=
    Algebra.IsAlgebraic.of_finite 𝒪[K] (AdjoinRoot f)
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing 𝒪[K] (FractionRing 𝒪[K])
    (AdjoinRoot f) (FractionRing (AdjoinRoot f))]
  exact (AdjoinRoot.isAdjoinRootMonic f hf).finrank

/-- The fraction field of a lifted irreducible residue polynomial is a finite-dimensional field
extension of the original nonarchimedean local field.  This transports the preceding fraction
field construction along the canonical identification `FractionRing 𝒪[K] ≃ₐ[𝒪[K]] K`. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    FiniteDimensional K (FractionRing (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  apply Module.Finite.of_equiv_equiv (FractionRing.algEquiv (A := 𝒪[K]) K).toRingEquiv
    (RingEquiv.refl (FractionRing (AdjoinRoot f)))
  apply IsFractionRing.ringHom_ext (A := 𝒪[K])
  intro r
  simp only [RingHom.comp_apply]
  change (algebraMap K (FractionRing (AdjoinRoot f)))
    ((FractionRing.algEquiv (A := 𝒪[K]) K) (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)) = _
  rw [(FractionRing.algEquiv (A := 𝒪[K]) K).commutes]
  change IsFractionRing.lift hg₀ (algebraMap 𝒪[K] K r) =
    IsFractionRing.lift hg₀ (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)
  rw [IsFractionRing.lift_algebraMap]
  rw [IsFractionRing.lift_algebraMap]

/-- The fraction field of a monic irreducible residue lift has degree exactly the degree of its
defining polynomial over the original nonarchimedean local field. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_finrankOverBase
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    Module.finrank K (FractionRing (AdjoinRoot f)) = f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  have hfinrank : Module.finrank (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) =
      f.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K f hf g hfg hg
  rw [← hfinrank]
  symm
  apply Algebra.finrank_eq_of_equiv_equiv (FractionRing.algEquiv (A := 𝒪[K]) K).toRingEquiv
    (RingEquiv.refl (FractionRing (AdjoinRoot f)))
  apply IsFractionRing.ringHom_ext (A := 𝒪[K])
  intro r
  simp only [RingHom.comp_apply]
  change (algebraMap K (FractionRing (AdjoinRoot f)))
    ((FractionRing.algEquiv (A := 𝒪[K]) K) (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)) = _
  rw [(FractionRing.algEquiv (A := 𝒪[K]) K).commutes]
  change IsFractionRing.lift hg₀ (algebraMap 𝒪[K] K r) =
    IsFractionRing.lift hg₀ (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)
  rw [IsFractionRing.lift_algebraMap]
  rw [IsFractionRing.lift_algebraMap]

/-- The defining polynomial of an irreducible residue lift stays irreducible over the local
field. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionPolynomial_irreducible
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) : Irreducible (f.map (algebraMap 𝒪[K] K)) :=
  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (K := K) hf).mp
    (nonarchimedeanLocalFieldAdjoinRoot_isPrime K f hf g hfg hg).irreducible

/-- The defining polynomial of an irreducible residue lift is separable over the local field.
Its derivative cannot vanish after scalar extension: reduction would otherwise give a vanishing
derivative for the irreducible polynomial over the finite residue field. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionPolynomial_separable
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) : (f.map (algebraMap 𝒪[K] K)).Separable := by
  have hirr := nonarchimedeanLocalFieldAdjoinRootFractionPolynomial_irreducible K f hf g hfg hg
  apply (Polynomial.separable_iff_derivative_ne_zero hirr).mpr
  intro hzero
  have hderivative : f.derivative = 0 := by
    apply (Polynomial.map_eq_zero_iff (IsFractionRing.injective 𝒪[K] K)).mp
    rw [← Polynomial.derivative_map]
    exact hzero
  have hgzero : g.derivative = 0 := by
    calc
      g.derivative = (f.map (Ideal.Quotient.mk 𝓂[K])).derivative :=
        congrArg Polynomial.derivative hfg.symm
      _ = f.derivative.map (Ideal.Quotient.mk 𝓂[K]) := Polynomial.derivative_map f _
      _ = 0 := by rw [hderivative, Polynomial.map_zero]
  letI : PerfectField 𝓀[K] := inferInstance
  exact (Polynomial.separable_iff_derivative_ne_zero hg).mp
    (PerfectField.separable_of_irreducible hg) hgzero

/-- The fraction field of an irreducible residue-polynomial lift is separable over the base
local field. Every fraction is rational in the lifted root, while that root is annihilated by
the separable fraction polynomial. This is the finite separable extension layer needed before
one can address normality and lift the residue Frobenius to a local-field automorphism. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_isSeparable
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    Algebra.IsSeparable K (FractionRing (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  let α : FractionRing (AdjoinRoot f) :=
    algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) (AdjoinRoot.root f)
  have hcomm : (algebraMap K (FractionRing (AdjoinRoot f))).comp (algebraMap 𝒪[K] K) =
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (algebraMap 𝒪[K] (AdjoinRoot f)) := by
    ext r
    change IsFractionRing.lift hg₀ (algebraMap 𝒪[K] K r) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hmap (q : Polynomial 𝒪[K]) :
      algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) (AdjoinRoot.mk f q) =
        Polynomial.aeval α (q.map (algebraMap 𝒪[K] K)) := by
    rw [← AdjoinRoot.aeval_eq q]
    exact Polynomial.map_aeval_eq_aeval_map hcomm q (AdjoinRoot.root f)
  have hroot : Polynomial.aeval α (f.map (algebraMap 𝒪[K] K)) = 0 := by
    rw [← hmap f]
    simp
  have hαsep : IsSeparable K α := by
    change (minpoly K α).Separable
    exact (nonarchimedeanLocalFieldAdjoinRootFractionPolynomial_separable K f hf g hfg hg).of_dvd
      (minpoly.dvd K α hroot)
  let S : IntermediateField K (FractionRing (AdjoinRoot f)) := IntermediateField.adjoin K {α}
  have hmem : ∀ b : AdjoinRoot f,
      algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) b ∈ S := by
    intro b
    induction b using AdjoinRoot.induction_on with
    | _ q =>
      rw [IntermediateField.mem_adjoin_simple_iff]
      refine ⟨q.map (algebraMap 𝒪[K] K), 1, ?_⟩
      rw [hmap q]
      simp
  have hgen : S = ⊤ := by
    rw [eq_top_iff]
    intro z hz
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (AdjoinRoot f) z
    rw [← hab]
    exact S.div_mem (hmem a) (hmem b)
  letI : Algebra.IsSeparable K S :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K
      (FractionRing (AdjoinRoot f))).mpr hαsep
  let e : S ≃ₐ[K] (FractionRing (AdjoinRoot f)) :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  exact AlgEquiv.Algebra.isSeparable e

/-- A monic lift of an irreducible residue polynomial has local root algebra.  Its unique
maximal ideal is the extension of the maximal ideal of the valuation ring. -/
theorem nonarchimedeanLocalFieldAdjoinRootIsLocalRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) : IsLocalRing (AdjoinRoot f) := by
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Algebra.IsIntegral 𝒪[K] (AdjoinRoot f) :=
    Algebra.IsIntegral.of_finite 𝒪[K] (AdjoinRoot f)
  let m : Ideal (AdjoinRoot f) := Ideal.map (AdjoinRoot.of f) 𝓂[K]
  have hm : m.IsMaximal := nonarchimedeanLocalFieldAdjoinRootMapMaximalIdealIsMaximal K f g hfg hg
  refine IsLocalRing.of_unique_max_ideal ⟨m, hm, ?_⟩
  intro P hP
  letI : P.IsMaximal := hP
  have hunder : (P.comap (algebraMap 𝒪[K] (AdjoinRoot f))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hunder_eq : P.comap (algebraMap 𝒪[K] (AdjoinRoot f)) = 𝓂[K] :=
    IsLocalRing.eq_maximalIdeal hunder
  apply (hm.eq_of_le hP.ne_top ?_).symm
  change Ideal.map (algebraMap 𝒪[K] (AdjoinRoot f)) 𝓂[K] ≤ P
  rw [Ideal.map_le_iff_le_comap, ← hunder_eq]

/-- The residue field of the local root algebra of a monic lift of an irreducible residue
polynomial is canonically the root field of that residue polynomial. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootResidueFieldEquivOfMapEq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsLocalRing (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    IsLocalRing.ResidueField (AdjoinRoot f) ≃ₐ[𝒪[K]] AdjoinRoot g := by
  letI : IsLocalRing (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  let hm : (Ideal.map (AdjoinRoot.of f) 𝓂[K]).IsMaximal :=
    nonarchimedeanLocalFieldAdjoinRootMapMaximalIdealIsMaximal K f g hfg hg
  change (AdjoinRoot f ⧸ IsLocalRing.maximalIdeal (AdjoinRoot f)) ≃ₐ[𝒪[K]] AdjoinRoot g
  rw [← IsLocalRing.eq_maximalIdeal hm]
  exact nonarchimedeanLocalFieldAdjoinRootReductionEquivOfMapEq K f g hfg

/-- A monic lift of a monic irreducible residue polynomial gives a finite étale local algebra
over the valuation ring.  This is the finite-étale lifting bridge from a prescribed finite
residue extension to a concrete local algebra; the preceding fraction-field theorems promote
its irreducible lifts to finite field extensions of the local field. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_etale
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    Algebra.Etale 𝒪[K] (AdjoinRoot f) := by
  letI : Module.Free 𝒪[K] (AdjoinRoot f) := hf.free_adjoinRoot
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : IsLocalRing (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  have hmap : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] (AdjoinRoot f)) =
      IsLocalRing.maximalIdeal (AdjoinRoot f) := by
    change (Ideal.map (AdjoinRoot.of f) 𝓂[K]) = IsLocalRing.maximalIdeal (AdjoinRoot f)
    exact IsLocalRing.eq_maximalIdeal
      (nonarchimedeanLocalFieldAdjoinRootMapMaximalIdealIsMaximal K f g hfg hg)
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap 𝒪[K] (AdjoinRoot f))).out 2 0).mp (le_of_eq hmap)
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Module.Finite 𝓀[K] (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite 𝓀[K]
  let e := nonarchimedeanLocalFieldAdjoinRootResidueFieldEquivOfMapEq K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Finite.of_surjective e.symm e.symm.surjective
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Algebra.IsAlgebraic.of_finite 𝓀[K] _
  letI : Algebra.IsSeparable 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI : Algebra.FormallyUnramified 𝒪[K] (AdjoinRoot f) :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmap
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- A monic lift of an irreducible residue polynomial is finite étale over the valuation ring of
the local field.  This packages its finite unramified integral extension structure. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_finiteEtale
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    Algebra.FiniteEtale 𝒪[K] (AdjoinRoot f) := by
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Algebra.Etale 𝒪[K] (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_etale K f hf g hgmonic hfg hg
  infer_instance

/-- The defining root of a finite unramified lift is simple already over the integral root
algebra: the derivative of its defining polynomial is a unit.  This derives the concrete
simple-root certificate from the finite-etale local algebra structure and will be used when
lifting residue-field conjugates by Hensel's lemma. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_derivative_isUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    IsUnit ((f.derivative.map (AdjoinRoot.of f)).eval (AdjoinRoot.root f)) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Algebra.Etale 𝒪[K] (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_etale K f hf g hgmonic hfg hg
  have hfracirr :=
    nonarchimedeanLocalFieldAdjoinRootFractionPolynomial_irreducible K f hf g hfg hg
  have hfirr : Irreducible f :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map hf).mpr hfracirr
  have hunit := IsLocalRing.isUnit_aeval_derivative_minpoly_of_adjoin_eq_top
    (IsAdjoinRoot.adjoin_root_eq_top (AdjoinRoot.isAdjoinRoot f))
  have hminpoly : minpoly 𝒪[K] (AdjoinRoot.root f) = f := by
    rw [← AdjoinRoot.isAdjoinRoot_root_eq_root]
    exact IsAdjoinRootMonic.minpoly_eq (AdjoinRoot.isAdjoinRootMonic f hf) hfirr
  rw [AdjoinRoot.isAdjoinRoot_root_eq_root, hminpoly] at hunit
  simpa only [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq, Polynomial.derivative_map,
    ← Polynomial.eval_map] using hunit

/-- The map from the base valuation ring to a monic irreducible lift is local.  Hence it induces
the canonical extension map between their residue fields. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_isLocalHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) := by
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  have hmap : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] (AdjoinRoot f)) =
      IsLocalRing.maximalIdeal (AdjoinRoot f) := by
    change (Ideal.map (AdjoinRoot.of f) 𝓂[K]) = IsLocalRing.maximalIdeal (AdjoinRoot f)
    exact IsLocalRing.eq_maximalIdeal
      (nonarchimedeanLocalFieldAdjoinRootMapMaximalIdealIsMaximal K f g hfg hg)
  exact ((IsLocalRing.local_hom_TFAE (algebraMap 𝒪[K] (AdjoinRoot f))).out 2 0).mp
    (le_of_eq hmap)

/-- A finite unramified root lift transports the base maximal ideal onto its own maximal ideal.
This is the ideal-theoretic form of unramifiedness used to compare higher unit filtrations. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_map_maximalIdeal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    𝓂[K].map (algebraMap 𝒪[K] (AdjoinRoot f)) = IsLocalRing.maximalIdeal (AdjoinRoot f) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  change Ideal.map (AdjoinRoot.of f) 𝓂[K] = IsLocalRing.maximalIdeal (AdjoinRoot f)
  exact IsLocalRing.eq_maximalIdeal
    (nonarchimedeanLocalFieldAdjoinRootMapMaximalIdealIsMaximal K f g hfg hg)

/-- The residue extension carried by a finite unramified root lift is Galois.  This promotes
the prior residue-field identification to the Galois layer needed for unramified Frobenius. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueField_isGalois
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    IsGalois 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  let e := nonarchimedeanLocalFieldAdjoinRootResidueFieldEquivOfMapEq K f hf g hfg hg
  letI : Finite (AdjoinRoot g) := by
    letI : Module.Finite 𝓀[K] (AdjoinRoot g) := hgmonic.finite_adjoinRoot
    exact Module.finite_of_finite 𝓀[K]
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Finite.of_surjective e.symm e.symm.surjective
  infer_instance

/-- The defining residue polynomial of an unramified root lift splits in the lifted residue
field.  The root algebra identification transports its distinguished root, and normality of the
finite residue extension supplies all conjugates. This is the residue-level input for lifting
the complete Frobenius orbit by Hensel's lemma. -/
theorem nonarchimedeanLocalFieldAdjoinRootResiduePolynomial_splits
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    (g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)))).Splits := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  let e := nonarchimedeanLocalFieldAdjoinRootResidueFieldEquivOfMapEq K f hf g hfg hg
  let x : IsLocalRing.ResidueField (AdjoinRoot f) := e.symm (AdjoinRoot.root g)
  have hcomm : algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) =
      e.symm.toRingEquiv.toRingHom.comp (algebraMap 𝓀[K] (AdjoinRoot g)) := by
    ext r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    change algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))
      (IsLocalRing.residue 𝒪[K] a) =
      e.symm (algebraMap 𝓀[K] (AdjoinRoot g) (IsLocalRing.residue 𝒪[K] a))
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    change IsLocalRing.residue (AdjoinRoot f) (algebraMap 𝒪[K] (AdjoinRoot f) a) =
      e.symm (algebraMap 𝓀[K] (AdjoinRoot g) (algebraMap 𝒪[K] 𝓀[K] a))
    rw [← IsScalarTower.algebraMap_apply 𝒪[K] 𝓀[K] (AdjoinRoot g)]
    change algebraMap (AdjoinRoot f) (IsLocalRing.ResidueField (AdjoinRoot f))
      (algebraMap 𝒪[K] (AdjoinRoot f) a) =
      e.symm (algebraMap 𝒪[K] (AdjoinRoot g) a)
    rw [← IsScalarTower.algebraMap_apply 𝒪[K] (AdjoinRoot f)
      (IsLocalRing.ResidueField (AdjoinRoot f))]
    exact (e.symm.commutes a).symm
  have hroot : Polynomial.aeval x g = 0 := by
    change Polynomial.aeval (e.symm.toRingEquiv.toRingHom (AdjoinRoot.root g)) g = 0
    have hcomm' : (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))).comp
        (RingHom.id 𝓀[K]) =
        e.symm.toRingEquiv.toRingHom.comp (algebraMap 𝓀[K] (AdjoinRoot g)) := by
      simpa using hcomm
    have h := Polynomial.map_aeval_eq_aeval_map hcomm' g (AdjoinRoot.root g)
    simpa only [Polynomial.map_id, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero] using h.symm
  have hminpoly : minpoly 𝓀[K] x = g := by
    exact (minpoly.eq_of_irreducible_of_monic hg hroot hgmonic).symm
  letI : IsGalois 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_isGalois K f hf g hgmonic hfg hg
  letI : Normal 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) := IsGalois.to_normal
  have hsplit : ((minpoly 𝓀[K] x).map
      (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)))).Splits :=
    Normal.splits' x
  simpa only [hminpoly] using hsplit

/-- The Galois group of the residue extension carried by a finite unramified root lift is
cyclic.  Its distinguished generator is the residue arithmetic Frobenius. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueField_isCyclic
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    IsCyclic Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  let e := nonarchimedeanLocalFieldAdjoinRootResidueFieldEquivOfMapEq K f hf g hfg hg
  letI : Finite (AdjoinRoot g) := by
    letI : Module.Finite 𝓀[K] (AdjoinRoot g) := hgmonic.finite_adjoinRoot
    exact Module.finite_of_finite 𝓀[K]
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Finite.of_surjective e.symm e.symm.surjective
  infer_instance

/-- A finite unramified root algebra over a nonarchimedean local valuation ring is complete for
its maximal-ideal adic topology.  Thus its fraction field is supplied with the integral
completeness prerequisite for the local-field extension layer. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_isAdicComplete
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    IsAdicComplete (IsLocalRing.maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : IsAdicComplete 𝓂[K] 𝒪[K] := nonarchimedeanLocalField_isAdicComplete K
  have hcomplete : IsAdicComplete 𝓂[K] (AdjoinRoot f) :=
    adicComplete_of_finiteModule_of_baseAdicComplete 𝒪[K] (AdjoinRoot f) 𝓂[K]
  have hmap : (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] (AdjoinRoot f)) =
      IsLocalRing.maximalIdeal (AdjoinRoot f) := by
    change (Ideal.map (AdjoinRoot.of f) 𝓂[K]) = IsLocalRing.maximalIdeal (AdjoinRoot f)
    exact IsLocalRing.eq_maximalIdeal
      (nonarchimedeanLocalFieldAdjoinRootMapMaximalIdealIsMaximal K f g hfg hg)
  rw [← hmap]
  let hhaus : IsHausdorff ((IsLocalRing.maximalIdeal 𝒪[K]).map
      (algebraMap 𝒪[K] (AdjoinRoot f))) (AdjoinRoot f) :=
    IsHausdorff.map_algebraMap_iff.mpr hcomplete.1
  let hprec : IsPrecomplete ((IsLocalRing.maximalIdeal 𝒪[K]).map
      (algebraMap 𝒪[K] (AdjoinRoot f))) (AdjoinRoot f) :=
    IsPrecomplete.map_algebraMap_iff.mpr hcomplete.2
  exact { haus' := hhaus.haus', prec' := hprec.prec' }

/-- A finite unramified root algebra is complete and Hausdorff for its canonical maximal-ideal
adic uniform structure.  This turns its algebraic adic completeness into the topological input
used by the local-field extension layer. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_completeSpace_t2Space_adicTopology
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : WithIdeal (AdjoinRoot f) := ⟨IsLocalRing.maximalIdeal (AdjoinRoot f)⟩
    CompleteSpace (AdjoinRoot f) ∧ T2Space (AdjoinRoot f) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : WithIdeal (AdjoinRoot f) := ⟨IsLocalRing.maximalIdeal (AdjoinRoot f)⟩
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isAdicComplete K f hf g hfg hg
  exact ⟨completeSpace_of_isAdicComplete_adicTopology (AdjoinRoot f)
      (IsLocalRing.maximalIdeal (AdjoinRoot f)),
    t2Space_of_isAdicComplete_adicTopology (AdjoinRoot f)
      (IsLocalRing.maximalIdeal (AdjoinRoot f))⟩

/-- The finite unramified lift is Henselian at its maximal ideal.  This transfers the root-lifting
mechanism from the base local field to every finite unramified integral extension constructed
above. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_henselianRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    HenselianRing (AdjoinRoot f) (IsLocalRing.maximalIdeal (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isAdicComplete K f hf g hfg hg
  infer_instance

/-- A simple residue root over a finite unramified lift has a root in that lift.  This is the
iteration form of Hensel lifting needed to build successive unramified local extensions. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_hensel_lift
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    ∀ (p : Polynomial (AdjoinRoot f)) (_ : p.Monic) (a₀ : AdjoinRoot f),
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AdjoinRoot f)) (p.eval a₀) = 0 →
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AdjoinRoot f)) (p.derivative.eval a₀) ≠ 0 →
      ∃ a : AdjoinRoot f, p.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal (AdjoinRoot f) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : HenselianRing (AdjoinRoot f) (IsLocalRing.maximalIdeal (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_henselianRing K f hf g hfg hg
  intro p hp a₀ hroot hsimple
  apply HenselianRing.is_henselian p hp a₀
  · exact Ideal.Quotient.eq_zero_iff_mem.mp hroot
  · exact Ne.isUnit hsimple

/-- A monic polynomial over a domain splits when its separable reduction already splits and each
reduced root has a lift with the same residue.  The finite root count makes the lifts distinct,
so they exhaust the degree of the original polynomial. -/
theorem polynomial_splits_of_split_reduction_and_root_lifts
    {B R : Type*} [CommRing B] [IsDomain B] [Field R]
    (φ : B →+* R) (p : Polynomial B) (hp : p.Monic)
    (hsep : (p.map φ).Separable) (hsplit : (p.map φ).Splits)
    (hlift : ∀ x : R, (p.map φ).IsRoot x →
      ∃ a : B, p.IsRoot a ∧ φ a = x) : p.Splits := by
  classical
  let q : Polynomial R := p.map φ
  let S : Finset R := q.roots.toFinset
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq0 : q ≠ 0 := by
    simpa only [q] using (hp.map φ).ne_zero
  have hS_card : S.card = q.natDegree := by
    calc
      S.card = q.roots.card := by
        dsimp only [S]
        exact Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)
      _ = q.natDegree := Polynomial.splits_iff_card_roots.mp hsplit
  have hq_natDegree : q.natDegree = p.natDegree := by
    simpa only [q] using hp.natDegree_map φ
  have hLifts : ∀ x : S, ∃ a : B, p.IsRoot a ∧ φ a = x := by
    intro x
    apply hlift x
    apply (q.mem_roots hq0).mp
    simpa only [S, Multiset.mem_toFinset] using x.property
  choose F hFroot hFres using hLifts
  let T : Finset B := S.attach.image F
  have hF_injective : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    calc
      (x : R) = φ (F x) := (hFres x).symm
      _ = φ (F y) := congrArg φ hxy
      _ = (y : R) := hFres y
  have hT_card : T.card = S.card := by
    dsimp only [T]
    calc
      (S.attach.image F).card = S.attach.card :=
        Finset.card_image_of_injOn (fun x _ y _ hxy => hF_injective hxy)
      _ = S.card := Finset.card_attach
  have hTroots : ∀ a ∈ T, p.eval a = 0 := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨x, -, rfl⟩
    exact hFroot x
  have hT_natDegree : T.card = p.natDegree :=
    hT_card.trans (hS_card.trans hq_natDegree)
  have hroots : p.roots = T.val :=
    p.roots_eq_of_natDegree_le_card_of_ne_zero hTroots hT_natDegree.ge hp0
  apply Polynomial.splits_iff_card_roots.mpr
  rw [hroots]
  change T.card = p.natDegree
  exact hT_natDegree

/-- A field generated by one root of a polynomial that already splits in it is normal.  This
packages the splitting-field argument used to pass from integral root lifting to a normal
fraction-field extension. -/
theorem normal_of_splits_and_adjoin_root_eq_top
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (p : Polynomial K) (α : L)
    (hp : (p.map (algebraMap K L)) ≠ 0)
    (hroot : Polynomial.aeval α p = 0)
    (hsplit : (p.map (algebraMap K L)).Splits)
    (hgen : IntermediateField.adjoin K {α} = ⊤) : Normal K L := by
  letI : Polynomial.IsSplittingField K L p := by
    apply isSplittingField_iff_intermediateField.mpr
    refine ⟨hsplit, ?_⟩
    apply top_unique
    rw [← hgen]
    apply IntermediateField.adjoin_simple_le_iff.mpr
    apply IntermediateField.subset_adjoin
    apply Polynomial.mem_rootSet'.mpr
    exact ⟨hp, hroot⟩
  exact Normal.of_isSplittingField p

/-- Every simple root of the defining residue polynomial in the lifted residue field has a
root-lift in the unramified integral algebra. The reduction compatibility is explicit, so this
turns each residue conjugate into a genuine conjugate root before the remaining root-counting
step that proves fraction-field normality. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueConjugate
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ x : IsLocalRing.ResidueField (AdjoinRoot f),
      Polynomial.aeval x (g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)))) = 0 →
      ∃ a : AdjoinRoot f, (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).IsRoot a ∧
        IsLocalRing.residue (AdjoinRoot f) a = x := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  let p : Polynomial (AdjoinRoot f) := f.map (algebraMap 𝒪[K] (AdjoinRoot f))
  have hp : p.Monic := hf.map _
  have hcoeff : (IsLocalRing.residue (AdjoinRoot f)).comp
      (algebraMap 𝒪[K] (AdjoinRoot f)) =
      (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))).comp
        (IsLocalRing.residue 𝒪[K]) := by
    ext a
    change IsLocalRing.residue (AdjoinRoot f) (algebraMap 𝒪[K] (AdjoinRoot f) a) =
      algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))
        (IsLocalRing.residue 𝒪[K] a)
    exact (IsLocalRing.ResidueField.algebraMap_residue a).symm
  have hreduce : p.map (IsLocalRing.residue (AdjoinRoot f)) =
      g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) := by
    calc
      p.map (IsLocalRing.residue (AdjoinRoot f)) =
          f.map ((IsLocalRing.residue (AdjoinRoot f)).comp
            (algebraMap 𝒪[K] (AdjoinRoot f))) := by
        simp only [p, Polynomial.map_map]
      _ = f.map ((algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))).comp
          (IsLocalRing.residue 𝒪[K])) := by rw [hcoeff]
      _ = (f.map (IsLocalRing.residue 𝒪[K])).map
          (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) := by
        rw [Polynomial.map_map]
      _ = g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) := by
        change (f.map (Ideal.Quotient.mk 𝓂[K])).map _ = _
        rw [hfg]
        rfl
  letI : PerfectField 𝓀[K] := inferInstance
  have hgsep : g.Separable := PerfectField.separable_of_irreducible hg
  intro x hx
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective x
  have hroot' : Polynomial.aeval x (p.map (IsLocalRing.residue (AdjoinRoot f))) = 0 := by
    rw [hreduce]
    exact hx
  have hsimple : Polynomial.aeval x ((g.map
      (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)))).derivative) ≠ 0 :=
    (Polynomial.separable_map _).mpr hgsep |>.aeval_derivative_ne_zero hx
  have hsimple' : Polynomial.aeval x
      ((p.map (IsLocalRing.residue (AdjoinRoot f))).derivative) ≠ 0 := by
    rw [hreduce]
    exact hsimple
  have hroot : IsLocalRing.residue (AdjoinRoot f) (p.eval a₀) = 0 := by
    rw [← ha₀] at hroot'
    change (p.map (IsLocalRing.residue (AdjoinRoot f))).eval
      (IsLocalRing.residue (AdjoinRoot f) a₀) = 0 at hroot'
    rw [Polynomial.eval_map] at hroot'
    have heval : IsLocalRing.residue (AdjoinRoot f) (p.eval a₀) =
        Polynomial.eval₂ (IsLocalRing.residue (AdjoinRoot f))
          (IsLocalRing.residue (AdjoinRoot f) a₀) p := by
      exact Polynomial.hom_eval₂ p (RingHom.id (AdjoinRoot f))
        (IsLocalRing.residue (AdjoinRoot f)) a₀
    rw [heval]
    exact hroot'
  have hsimple₀ : IsLocalRing.residue (AdjoinRoot f)
      (p.derivative.eval a₀) ≠ 0 := by
    rw [← ha₀] at hsimple'
    rw [Polynomial.derivative_map] at hsimple'
    change (p.derivative.map (IsLocalRing.residue (AdjoinRoot f))).eval
      (IsLocalRing.residue (AdjoinRoot f) a₀) ≠ 0 at hsimple'
    rw [Polynomial.eval_map] at hsimple'
    have heval : IsLocalRing.residue (AdjoinRoot f) (p.derivative.eval a₀) =
        Polynomial.eval₂ (IsLocalRing.residue (AdjoinRoot f))
          (IsLocalRing.residue (AdjoinRoot f) a₀) p.derivative := by
      exact Polynomial.hom_eval₂ p.derivative (RingHom.id (AdjoinRoot f))
        (IsLocalRing.residue (AdjoinRoot f)) a₀
    rw [heval]
    exact hsimple'
  obtain ⟨a, ha, haa₀⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_hensel_lift K f hf g hfg hg p hp a₀ hroot hsimple₀
  refine ⟨a, ha, ?_⟩
  exact (Ideal.Quotient.eq.mpr haa₀).trans ha₀

/-- The residue of the distinguished integral root is a root of the transported residue
polynomial.  This exposes the input to which residue Frobenius is applied before Hensel lifting. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_residue_root_isRoot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    Polynomial.aeval (IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f))
      (g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)))) = 0 := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  have hcoeff : (IsLocalRing.residue (AdjoinRoot f)).comp
      (algebraMap 𝒪[K] (AdjoinRoot f)) =
      (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))).comp
        (IsLocalRing.residue 𝒪[K]) := by
    ext a
    exact (IsLocalRing.ResidueField.algebraMap_residue a).symm
  change (g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)))).eval
      (IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f)) = 0
  have hreduce : (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).map
      (IsLocalRing.residue (AdjoinRoot f)) =
      g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) := by
    calc
      (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).map
          (IsLocalRing.residue (AdjoinRoot f)) =
          f.map ((IsLocalRing.residue (AdjoinRoot f)).comp
            (algebraMap 𝒪[K] (AdjoinRoot f))) := by
              rw [Polynomial.map_map]
      _ = f.map ((algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))).comp
            (IsLocalRing.residue 𝒪[K])) := by rw [hcoeff]
      _ = (f.map (IsLocalRing.residue 𝒪[K])).map
          (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) := by
              rw [Polynomial.map_map]
      _ = g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) := by
            change (f.map (Ideal.Quotient.mk 𝓂[K])).map _ = _
            rw [hfg]
            rfl
  rw [← hreduce, Polynomial.eval_map]
  have hroot : (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).eval (AdjoinRoot.root f) = 0 := by
    change (f.map (AdjoinRoot.of f)).eval (AdjoinRoot.root f) = 0
    exact AdjoinRoot.isRoot_root f
  have heval : IsLocalRing.residue (AdjoinRoot f)
      ((f.map (algebraMap 𝒪[K] (AdjoinRoot f))).eval (AdjoinRoot.root f)) =
      Polynomial.eval₂ (IsLocalRing.residue (AdjoinRoot f))
        (IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f))
        (f.map (algebraMap 𝒪[K] (AdjoinRoot f))) := by
    exact Polynomial.hom_eval₂ (f.map (algebraMap 𝒪[K] (AdjoinRoot f)))
      (RingHom.id (AdjoinRoot f)) (IsLocalRing.residue (AdjoinRoot f)) (AdjoinRoot.root f)
  rw [← heval, hroot, map_zero]

/-- Every residue-field automorphism carries the reduced distinguished root to another root of
the transported residue polynomial.  Combined with Hensel lifting, this supplies the target for
an integral lift of each residue Galois automorphism. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_residue_root_apply_gal_isRoot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ σ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]),
      Polynomial.aeval (σ (IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f)))
        (g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)))) = 0 := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro σ
  have hmap : (algebraMap (IsLocalRing.ResidueField (AdjoinRoot f))
      (IsLocalRing.ResidueField (AdjoinRoot f))).comp
      (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) =
      algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) := by
    ext a
    simp
  have hroot : Polynomial.aeval
      (IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f)) g = 0 := by
    rw [Polynomial.aeval_eq_aeval_map
      (φ := algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) hmap g]
    exact nonarchimedeanLocalFieldAdjoinRoot_residue_root_isRoot K f hf g hfg hg
  rw [← Polynomial.aeval_eq_aeval_map
    (φ := algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) hmap g]
  rw [Polynomial.aeval_algHom_apply, hroot, map_zero]

/-- A residue conjugate of the distinguished root lifts to an integral algebra endomorphism of
the unramified root algebra.  This is the root-level input for lifting residue Frobenius to the
unramified fraction field. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueConjugateAlgHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ x : IsLocalRing.ResidueField (AdjoinRoot f),
      Polynomial.aeval x (g.map (algebraMap 𝓀[K]
        (IsLocalRing.ResidueField (AdjoinRoot f)))) = 0 →
      ∃ φ : AdjoinRoot f →ₐ[𝒪[K]] AdjoinRoot f,
        IsLocalRing.residue (AdjoinRoot f) (φ (AdjoinRoot.root f)) = x := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro x hx
  obtain ⟨a, ha, hres⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_liftResidueConjugate K f hf g hfg hg x hx
  refine ⟨AdjoinRoot.liftAlgHom f (Algebra.ofId 𝒪[K] (AdjoinRoot f)) a ?_, ?_⟩
  · change Polynomial.eval₂ (algebraMap 𝒪[K] (AdjoinRoot f)) a f = 0
    rw [← Polynomial.eval_map]
    exact ha
  · rw [AdjoinRoot.liftAlgHom_root]
    exact hres

/-- Every residue-field Galois automorphism has an integral lift on the distinguished root.
This packages the Hensel root lift as the first half of a lift from residue Frobenius to an
unramified field automorphism; proving the resulting endomorphism invertible remains separate. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ σ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]),
      ∃ φ : AdjoinRoot f →ₐ[𝒪[K]] AdjoinRoot f,
        IsLocalRing.residue (AdjoinRoot f) (φ (AdjoinRoot.root f)) =
          σ (IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f)) := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro σ
  apply nonarchimedeanLocalFieldAdjoinRoot_liftResidueConjugateAlgHom K f hf g hfg hg
  exact nonarchimedeanLocalFieldAdjoinRoot_residue_root_apply_gal_isRoot K f hf g hfg hg σ

/-- The integral lift of a residue Galois automorphism is compatible with reduction on every
element of the root algebra.  Thus the Hensel lift is an actual lift of residue action, not only
a root-level coincidence. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgHom_commutes_residue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ σ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]),
      ∃ φ : AdjoinRoot f →ₐ[𝒪[K]] AdjoinRoot f, ∀ b : AdjoinRoot f,
        IsLocalRing.residue (AdjoinRoot f) (φ b) =
          σ (IsLocalRing.residue (AdjoinRoot f) b) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro σ
  obtain ⟨φ, hφ⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgHom K f hf g hfg hg σ
  let E := IsLocalRing.ResidueField (AdjoinRoot f)
  let A := 𝒪[K]
  let k := IsLocalRing.ResidueField A
  letI : Algebra A k := RingHom.toAlgebra (IsLocalRing.residue A)
  letI : Algebra A E := RingHom.toAlgebra ((algebraMap k E).comp (IsLocalRing.residue A))
  let resAlg : AdjoinRoot f →ₐ[A] E :=
    { toRingHom := IsLocalRing.residue (AdjoinRoot f)
      commutes' := by
        intro a
        change IsLocalRing.residue (AdjoinRoot f) (algebraMap A (AdjoinRoot f) a) =
          algebraMap k E (IsLocalRing.residue A a)
        exact (IsLocalRing.ResidueField.algebraMap_residue a).symm }
  let sigmaAlg : E →ₐ[A] E :=
    { toRingHom := σ.toRingHom
      commutes' := by
        intro a
        change σ (algebraMap k E (IsLocalRing.residue A a)) =
          algebraMap k E (IsLocalRing.residue A a)
        exact σ.commutes _ }
  have heq : resAlg.comp φ = sigmaAlg.comp resAlg := by
    apply AdjoinRoot.algHom_ext
    change IsLocalRing.residue (AdjoinRoot f) (φ (AdjoinRoot.root f)) =
      σ (IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f))
    exact hφ
  refine ⟨φ, ?_⟩
  intro b
  exact DFunLike.congr_fun heq b

/-- Every residue-field Galois automorphism lifts to an integral algebra automorphism of a finite
unramified root lift. Inverse residue lifts compose to roots with the same reduction as the
distinguished root; its unit derivative makes Hensel root uniqueness identify those composites
with the identity. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ σ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]),
      ∃ φ : AdjoinRoot f ≃ₐ[𝒪[K]] AdjoinRoot f, ∀ b : AdjoinRoot f,
        IsLocalRing.residue (AdjoinRoot f) (φ b) =
          σ (IsLocalRing.residue (AdjoinRoot f) b) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro σ
  obtain ⟨φ, hφ⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgHom_commutes_residue K f hf g hfg hg σ
  obtain ⟨ψ, hψ⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgHom_commutes_residue K f hf g hfg hg σ⁻¹
  have hroot : (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).eval (AdjoinRoot.root f) = 0 := by
    exact AdjoinRoot.isRoot_root f
  have himage (θ : AdjoinRoot f →ₐ[𝒪[K]] AdjoinRoot f) :
      (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).eval (θ (AdjoinRoot.root f)) = 0 := by
    have hroot_aeval : Polynomial.aeval (AdjoinRoot.root f) f = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact hroot
    calc
      (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).eval (θ (AdjoinRoot.root f)) =
          Polynomial.aeval (θ (AdjoinRoot.root f)) f := by
        rw [Polynomial.aeval_def, Polynomial.eval_map]
      _ = θ (Polynomial.aeval (AdjoinRoot.root f) f) :=
        Polynomial.aeval_algHom_apply θ (AdjoinRoot.root f) f
      _ = 0 := by rw [hroot_aeval]; exact θ.map_zero
  have hderiv :
      IsUnit ((f.map (algebraMap 𝒪[K] (AdjoinRoot f))).derivative.eval (AdjoinRoot.root f)) := by
    simpa only [Polynomial.derivative_map, AdjoinRoot.algebraMap_eq] using
      nonarchimedeanLocalFieldAdjoinRoot_derivative_isUnit K f hf g hgmonic hfg hg
  have hφψres :
      IsLocalRing.residue (AdjoinRoot f) (φ (ψ (AdjoinRoot.root f))) =
        IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f) := by
    rw [hφ, hψ]
    simp
  have hφψnonunit : ¬ IsUnit (AdjoinRoot.root f - φ (ψ (AdjoinRoot.root f))) := by
    intro hu
    have hne : IsLocalRing.residue (AdjoinRoot f)
        (AdjoinRoot.root f - φ (ψ (AdjoinRoot.root f))) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu
    rw [map_sub, hφψres] at hne
    exact hne (sub_self _)
  have hφψroot : AdjoinRoot.root f = φ (ψ (AdjoinRoot.root f)) :=
    IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hroot (himage (φ.comp ψ)) hφψnonunit hderiv
  have hψφres :
      IsLocalRing.residue (AdjoinRoot f) (ψ (φ (AdjoinRoot.root f))) =
        IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f) := by
    rw [hψ, hφ]
    simp
  have hψφnonunit : ¬ IsUnit (AdjoinRoot.root f - ψ (φ (AdjoinRoot.root f))) := by
    intro hu
    have hne : IsLocalRing.residue (AdjoinRoot f)
        (AdjoinRoot.root f - ψ (φ (AdjoinRoot.root f))) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu
    rw [map_sub, hψφres] at hne
    exact hne (sub_self _)
  have hψφroot : AdjoinRoot.root f = ψ (φ (AdjoinRoot.root f)) :=
    IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hroot (himage (ψ.comp φ)) hψφnonunit hderiv
  have hφψ : φ.comp ψ = AlgHom.id 𝒪[K] (AdjoinRoot f) := by
    apply AdjoinRoot.algHom_ext
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hφψroot.symm
  have hψφ : ψ.comp φ = AlgHom.id 𝒪[K] (AdjoinRoot f) := by
    apply AdjoinRoot.algHom_ext
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hψφroot.symm
  refine ⟨AlgEquiv.ofAlgHom φ ψ hφψ hψφ, ?_⟩
  exact hφ

/-- A compatible integral lift of a fixed residue Galois automorphism is unique. Composing one
lift with the inverse of another acts trivially after reduction; simple-root uniqueness then
makes that composite the identity on the root algebra. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquiv_unique
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ σ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]),
      ∀ φ ψ : AdjoinRoot f ≃ₐ[𝒪[K]] AdjoinRoot f,
        (∀ b : AdjoinRoot f, IsLocalRing.residue (AdjoinRoot f) (φ b) =
          σ (IsLocalRing.residue (AdjoinRoot f) b)) →
        (∀ b : AdjoinRoot f, IsLocalRing.residue (AdjoinRoot f) (ψ b) =
          σ (IsLocalRing.residue (AdjoinRoot f) b)) →
        φ = ψ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro σ φ ψ hφ hψ
  let θ : AdjoinRoot f ≃ₐ[𝒪[K]] AdjoinRoot f := ψ.symm.trans φ
  have hroot : (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).eval (AdjoinRoot.root f) = 0 := by
    exact AdjoinRoot.isRoot_root f
  have himage (η : AdjoinRoot f →ₐ[𝒪[K]] AdjoinRoot f) :
      (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).eval (η (AdjoinRoot.root f)) = 0 := by
    have hroot_aeval : Polynomial.aeval (AdjoinRoot.root f) f = 0 := by
      rw [Polynomial.aeval_def, ← Polynomial.eval_map]
      exact hroot
    calc
      (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).eval (η (AdjoinRoot.root f)) =
          Polynomial.aeval (η (AdjoinRoot.root f)) f := by
        rw [Polynomial.aeval_def, Polynomial.eval_map]
      _ = η (Polynomial.aeval (AdjoinRoot.root f) f) :=
        Polynomial.aeval_algHom_apply η (AdjoinRoot.root f) f
      _ = 0 := by rw [hroot_aeval]; exact η.map_zero
  have hderiv :
      IsUnit ((f.map (algebraMap 𝒪[K] (AdjoinRoot f))).derivative.eval (AdjoinRoot.root f)) := by
    simpa only [Polynomial.derivative_map, AdjoinRoot.algebraMap_eq] using
      nonarchimedeanLocalFieldAdjoinRoot_derivative_isUnit K f hf g hgmonic hfg hg
  have hψsymm (b : AdjoinRoot f) :
      IsLocalRing.residue (AdjoinRoot f) (ψ.symm b) =
        σ⁻¹ (IsLocalRing.residue (AdjoinRoot f) b) := by
    calc
      IsLocalRing.residue (AdjoinRoot f) (ψ.symm b) =
          σ⁻¹ (σ (IsLocalRing.residue (AdjoinRoot f) (ψ.symm b))) := by simp
      _ = σ⁻¹ (IsLocalRing.residue (AdjoinRoot f) (ψ (ψ.symm b))) := by rw [hψ]
      _ = σ⁻¹ (IsLocalRing.residue (AdjoinRoot f) b) := by rw [ψ.apply_symm_apply]
  have hθres (b : AdjoinRoot f) :
      IsLocalRing.residue (AdjoinRoot f) (θ b) =
        IsLocalRing.residue (AdjoinRoot f) b := by
    change IsLocalRing.residue (AdjoinRoot f) (φ (ψ.symm b)) = _
    rw [hφ, hψsymm]
    simp
  have hθnonunit : ¬ IsUnit (AdjoinRoot.root f - θ (AdjoinRoot.root f)) := by
    intro hu
    have hne : IsLocalRing.residue (AdjoinRoot f)
        (AdjoinRoot.root f - θ (AdjoinRoot.root f)) ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu
    rw [map_sub, hθres] at hne
    exact hne (sub_self _)
  have hθroot : AdjoinRoot.root f = θ (AdjoinRoot.root f) :=
    IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub hroot (himage θ.toAlgHom) hθnonunit hderiv
  have hθid : θ.toAlgHom = AlgHom.id 𝒪[K] (AdjoinRoot f) := by
    apply AdjoinRoot.algHom_ext
    change θ (AdjoinRoot.root f) = AdjoinRoot.root f
    exact hθroot.symm
  apply AlgEquiv.ext
  intro b
  have h := DFunLike.congr_fun hθid (ψ b)
  change (ψ.symm.trans φ) (ψ b) = ψ b at h
  simpa using h

/-- The canonical integral lift chosen from existence and uniqueness. The following compatibility
and multiplication lemmas show this choice is in fact independent of arbitrary representatives. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ _ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]),
      AdjoinRoot f ≃ₐ[𝒪[K]] AdjoinRoot f := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro σ
  exact Classical.choose
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquiv K f hf g hgmonic hfg hg σ)

/-- The chosen integral lift acts on every residue class by the prescribed residue Galois
automorphism. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice_spec
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ (σ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K])) (b : AdjoinRoot f),
      IsLocalRing.residue (AdjoinRoot f)
          (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice
            K f hf g hgmonic hfg hg σ b) =
        σ (IsLocalRing.residue (AdjoinRoot f) b) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro σ b
  change IsLocalRing.residue (AdjoinRoot f)
      (Classical.choose
        (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquiv K f hf g hgmonic hfg hg σ) b) = _
  exact (Classical.choose_spec
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquiv K f hf g hgmonic hfg hg σ)) b

/-- Uniqueness upgrades the chosen lifts to a multiplicative assignment. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice_mul
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ σ τ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]),
      nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice K f hf g hgmonic hfg hg
          (σ * τ) =
        nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice K f hf g hgmonic hfg hg σ *
          nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice K f hf g hgmonic hfg hg τ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro σ τ
  apply nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquiv_unique K f hf g hgmonic hfg hg
  · exact fun b =>
      nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice_spec
        K f hf g hgmonic hfg hg (σ * τ) b
  · intro b
    rw [AlgEquiv.mul_apply]
    rw [nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice_spec
      K f hf g hgmonic hfg hg σ]
    rw [nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice_spec
      K f hf g hgmonic hfg hg τ]
    rfl

/-- Residue Galois action embeds multiplicatively into automorphisms of the finite unramified
integral root algebra. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) →*
      (AdjoinRoot f ≃ₐ[𝒪[K]] AdjoinRoot f) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  exact MonoidHom.mk'
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice K f hf g hgmonic hfg hg)
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice_mul K f hf g hgmonic hfg hg)

/-- The integral Galois lift commutes with reduction on every element. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom_commutes_residue
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ (σ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K])) (b : AdjoinRoot f),
      IsLocalRing.residue (AdjoinRoot f)
          (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom
            K f hf g hgmonic hfg hg σ b) =
        σ (IsLocalRing.residue (AdjoinRoot f) b) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  exact nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivChoice_spec K f hf g hgmonic hfg hg

/-- Reduction detects distinct residue Galois automorphisms, so the integral Galois lift is
injective. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom_injective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    Function.Injective
      (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom K f hf g hgmonic hfg hg) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective x
  subst x
  calc
    σ (IsLocalRing.residue (AdjoinRoot f) b) =
        IsLocalRing.residue (AdjoinRoot f)
          (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom
            K f hf g hgmonic hfg hg σ b) :=
      (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom_commutes_residue
        K f hf g hgmonic hfg hg σ b).symm
    _ = IsLocalRing.residue (AdjoinRoot f)
          (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom
            K f hf g hgmonic hfg hg τ b) := by rw [h]
    _ = τ (IsLocalRing.residue (AdjoinRoot f) b) :=
      nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom_commutes_residue
        K f hf g hgmonic hfg hg τ b

/-- The integral Galois lift extends functorially to an injective homomorphism into the Galois
group of fraction fields over `FractionRing 𝒪[K]`. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) →*
      Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  exact (IsFractionRing.fieldEquivOfAlgEquivHom (A := 𝒪[K]) (B := AdjoinRoot f)
    (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))).comp
      (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom K f hf g hgmonic hfg hg)

/-- On integral elements, the fraction-field lift is exactly the localization of the integral
Galois lift. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_algebraMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    ∀ (σ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K])) (b : AdjoinRoot f),
      nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom K f hf g hgmonic hfg hg σ
          (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) b) =
        algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))
          (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom
            K f hf g hgmonic hfg hg σ b) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  intro σ b
  exact IsFractionRing.fieldEquivOfAlgEquiv_algebraMap (FractionRing 𝒪[K])
    (FractionRing (AdjoinRoot f)) (FractionRing (AdjoinRoot f))
      (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom
        K f hf g hgmonic hfg hg σ) b

/-- The fraction-field Galois lift is injective: equality on the generic fibre implies equality
on the embedded integral root algebra, hence equality after reduction. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_injective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    Function.Injective
      (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom K f hf g hgmonic hfg hg) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  intro σ τ h
  apply nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom_injective K f hf g hgmonic hfg hg
  apply AlgEquiv.ext
  intro b
  apply (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f)))
  rw [← nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_algebraMap
    K f hf g hgmonic hfg hg σ b]
  rw [h]
  rw [nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_algebraMap
    K f hf g hgmonic hfg hg τ b]

/-- The unramified subgroup of fraction-field Galois automorphisms obtained from residue action
is cyclic. This is a precise cyclicity statement for the canonical Frobenius-lift image; it does
not yet assert that every fraction-field automorphism preserves the integral model. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_range_isCyclic
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    IsCyclic
      (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom
        K f hf g hgmonic hfg hg).range := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  letI : IsCyclic Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_isCyclic K f hf g hgmonic hfg hg
  exact isCyclic_of_surjective
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom
      K f hf g hgmonic hfg hg).rangeRestrict
    (MonoidHom.rangeRestrict_surjective
      (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom
        K f hf g hgmonic hfg hg))

/- Inactive source-order draft retained as provenance; the dependency-ordered declarations
appear below the pre-existing Galois and residue-cardinality lemmas. -/
/-
/-- The unramified fraction-field extension is Galois already over the fraction field of its
valuation ring. This transports the `K`-Galois structure along `FractionRing 𝒪[K] ≃ₐ[𝒪[K]] K`. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : IsGalois K (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K f hf g hgmonic hfg hg
  let e := FractionRing.algEquiv 𝒪[K] K
  have hforward :
      (algebraMap K (FractionRing (AdjoinRoot f))).comp e.toRingEquiv.toRingHom =
        (RingEquiv.refl (FractionRing (AdjoinRoot f))).toRingHom.comp
          (algebraMap (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))) := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[K])
    intro r
    simp only [RingHom.comp_apply]
    change (algebraMap K (FractionRing (AdjoinRoot f)))
      (e (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)) = _
    rw [e.commutes]
    change IsFractionRing.lift hg₀ (algebraMap 𝒪[K] K r) =
      IsFractionRing.lift hg₀ (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)
    rw [IsFractionRing.lift_algebraMap]
    rw [IsFractionRing.lift_algebraMap]
  refine IsGalois.of_equiv_equiv (f := e.symm.toRingEquiv)
    (g := RingEquiv.refl (FractionRing (AdjoinRoot f))) ?_
  ext x
  have hx := DFunLike.congr_fun hforward (e.symm x)
  simpa [e] using hx.symm

/-- The fraction-field Galois lift is surjective. Its source and target have the same cardinality:
both are the residue degree of the monic unramified lift. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    Function.Surjective
      (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom K f hf g hgmonic hfg hg) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
  letI : IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K f hf g hgmonic hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  letI := Fintype.ofFinite Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K])
  letI := Fintype.ofFinite Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K])
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨
    nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_injective
      K f hf g hgmonic hfg hg, ?_⟩).surjective
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  calc
    Nat.card Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) = f.natDegree :=
      nonarchimedeanLocalFieldAdjoinRootResidueField_natCard_algEquiv K f hf g hgmonic hfg hg
    _ = Module.finrank (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      (nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K f hf g hfg hg).symm
    _ = Nat.card Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) :=
      (IsGalois.card_aut_eq_finrank _ _).symm

/-- The full Galois group of a finite unramified fraction-field lift is cyclic. Its Frobenius
description comes from the now-surjective residue-to-fraction-field Galois lift. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    IsCyclic Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : IsCyclic Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_isCyclic K f hf g hgmonic hfg hg
  exact isCyclic_of_surjective
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom K f hf g hgmonic hfg hg)
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_surjective
      K f hf g hgmonic hfg hg)

/-- A residue-field Galois automorphism lifts through the unramified integral model to a Galois
automorphism of its fraction field over the fraction field of the base valuation ring. The field
automorphism extends the integral lift, so it records both generic-fibre and residue action. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_liftResidueGal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    ∀ σ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]),
      ∃ τ : Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]),
        ∃ φ : AdjoinRoot f ≃ₐ[𝒪[K]] AdjoinRoot f,
          (∀ b : AdjoinRoot f, τ (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) b) =
            algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) (φ b)) ∧
          ∀ b : AdjoinRoot f, IsLocalRing.residue (AdjoinRoot f) (φ b) =
            σ (IsLocalRing.residue (AdjoinRoot f) b) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  intro σ
  obtain ⟨φ, hφ⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquiv K f hf g hgmonic hfg hg σ
  refine ⟨IsFractionRing.fieldEquivOfAlgEquiv (FractionRing 𝒪[K])
    (FractionRing (AdjoinRoot f)) (FractionRing (AdjoinRoot f)) φ, φ, ?_, hφ⟩
  intro b
  exact IsFractionRing.fieldEquivOfAlgEquiv_algebraMap (FractionRing 𝒪[K])
    (FractionRing (AdjoinRoot f)) (FractionRing (AdjoinRoot f)) φ b

-/

/-- In a finite unramified root lift, the integral defining polynomial splits in the lifted
integral algebra.  Each residue conjugate lifts by Hensel, and separability makes these lifts
distinct; this is the integral precursor to normality of the fraction-field extension. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_definingPolynomial_splits
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).Splits := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  let p : Polynomial (AdjoinRoot f) := f.map (algebraMap 𝒪[K] (AdjoinRoot f))
  have hp : p.Monic := hf.map _
  have hcoeff : (IsLocalRing.residue (AdjoinRoot f)).comp
      (algebraMap 𝒪[K] (AdjoinRoot f)) =
      (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))).comp
        (IsLocalRing.residue 𝒪[K]) := by
    ext a
    change IsLocalRing.residue (AdjoinRoot f) (algebraMap 𝒪[K] (AdjoinRoot f) a) =
      algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))
        (IsLocalRing.residue 𝒪[K] a)
    exact (IsLocalRing.ResidueField.algebraMap_residue a).symm
  have hreduce : p.map (IsLocalRing.residue (AdjoinRoot f)) =
      g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) := by
    calc
      p.map (IsLocalRing.residue (AdjoinRoot f)) =
          f.map ((IsLocalRing.residue (AdjoinRoot f)).comp
            (algebraMap 𝒪[K] (AdjoinRoot f))) := by
        simp only [p, Polynomial.map_map]
      _ = f.map ((algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))).comp
          (IsLocalRing.residue 𝒪[K])) := by rw [hcoeff]
      _ = (f.map (IsLocalRing.residue 𝒪[K])).map
          (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) := by
        rw [Polynomial.map_map]
      _ = g.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) := by
        change (f.map (Ideal.Quotient.mk 𝓂[K])).map _ = _
        rw [hfg]
        rfl
  letI : PerfectField 𝓀[K] := inferInstance
  have hgsep : g.Separable := PerfectField.separable_of_irreducible hg
  apply polynomial_splits_of_split_reduction_and_root_lifts
    (IsLocalRing.residue (AdjoinRoot f)) p hp
  · rw [hreduce]
    exact (Polynomial.separable_map _).mpr hgsep
  · rw [hreduce]
    exact nonarchimedeanLocalFieldAdjoinRootResiduePolynomial_splits K f hf g hgmonic hfg hg
  · intro x hx
    apply nonarchimedeanLocalFieldAdjoinRoot_liftResidueConjugate K f hf g hfg hg x
    rw [← hreduce]
    exact hx

/-- The fraction field of a finite unramified root lift is normal over the base local field.
The integral splitting theorem survives localization, and the localized distinguished root still
generates the whole fraction field, so the extension is its splitting field. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_normal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    Normal K (FractionRing (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  let p : Polynomial (AdjoinRoot f) := f.map (algebraMap 𝒪[K] (AdjoinRoot f))
  let q : Polynomial K := f.map (algebraMap 𝒪[K] K)
  let α : FractionRing (AdjoinRoot f) :=
    algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) (AdjoinRoot.root f)
  have hcomm : (algebraMap K (FractionRing (AdjoinRoot f))).comp (algebraMap 𝒪[K] K) =
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (algebraMap 𝒪[K] (AdjoinRoot f)) := by
    ext r
    change IsFractionRing.lift hg₀ (algebraMap 𝒪[K] K r) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hfracmap : q.map (algebraMap K (FractionRing (AdjoinRoot f))) =
      p.map (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))) := by
    calc
      q.map (algebraMap K (FractionRing (AdjoinRoot f))) =
          f.map ((algebraMap K (FractionRing (AdjoinRoot f))).comp (algebraMap 𝒪[K] K)) := by
        simp only [q, Polynomial.map_map]
      _ = f.map ((algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (algebraMap 𝒪[K] (AdjoinRoot f))) := by rw [hcomm]
      _ = p.map (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))) := by
        simp only [p, Polynomial.map_map]
  have hintegral : p.Splits :=
    nonarchimedeanLocalFieldAdjoinRoot_definingPolynomial_splits K f hf g hgmonic hfg hg
  have hsplit : (q.map (algebraMap K (FractionRing (AdjoinRoot f)))).Splits := by
    rw [hfracmap]
    exact hintegral.map _
  have hmap (r : Polynomial 𝒪[K]) :
      algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) (AdjoinRoot.mk f r) =
        Polynomial.aeval α (r.map (algebraMap 𝒪[K] K)) := by
    rw [← AdjoinRoot.aeval_eq r]
    exact Polynomial.map_aeval_eq_aeval_map hcomm r (AdjoinRoot.root f)
  have hroot : Polynomial.aeval α q = 0 := by
    rw [← hmap f]
    simp
  let S : IntermediateField K (FractionRing (AdjoinRoot f)) := IntermediateField.adjoin K {α}
  have hmem : ∀ b : AdjoinRoot f,
      algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) b ∈ S := by
    intro b
    induction b using AdjoinRoot.induction_on with
    | _ r =>
      rw [IntermediateField.mem_adjoin_simple_iff]
      refine ⟨r.map (algebraMap 𝒪[K] K), 1, ?_⟩
      rw [hmap r]
      simp
  have hgen : S = ⊤ := by
    rw [eq_top_iff]
    intro z hz
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (AdjoinRoot f) z
    rw [← hab]
    exact S.div_mem (hmem a) (hmem b)
  have hqmonic : q.Monic := hf.map _
  exact normal_of_splits_and_adjoin_root_eq_top q α (hqmonic.map _).ne_zero hroot hsplit hgen

/-- A finite unramified root lift gives a finite Galois extension of the base local field.  The
separable and normal halves are proved independently above: residue separability controls the
first, while lifted splitting and localization control the second. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    IsGalois K (FractionRing (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : Algebra.IsSeparable K (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isSeparable K f hf g hfg hg
  letI : Normal K (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_normal K f hf g hgmonic hfg hg
  exact IsGalois.mk

/-- In a finite normal field extension, the Galois action carries any chosen root of a monic
irreducible polynomial to any other root lying in the extension.  This is the field-level
conversion from Hensel-lifted conjugate roots to genuine Galois automorphisms. -/
theorem finiteNormal_irreducibleRoot_exists_gal_apply {K L : Type u} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Normal K L] (p : Polynomial K)
    (hp : Irreducible p) (hpm : p.Monic) (x y : L)
    (hx : Polynomial.aeval x p = 0) (hy : Polynomial.aeval y p = 0) :
    ∃ σ : Gal(L/K), σ x = y := by
  have hmin : p = minpoly K x :=
    minpoly.eq_of_irreducible_of_monic hp hx hpm
  apply minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic x)
  rw [← hmin]
  exact hy

/-- Every integral root of the lifted unramified polynomial is the image of the distinguished
fraction-field root under a base-field Galois automorphism.  Together with
`liftResidueGalAlgHom`, this turns each residue conjugate selected by Hensel lifting into an
actual automorphism of the unramified fraction field. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_exists_gal_apply_root
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    ∀ a : AdjoinRoot f, (f.map (algebraMap 𝒪[K] (AdjoinRoot f))).eval a = 0 →
      ∃ σ : Gal(FractionRing (AdjoinRoot f) / K),
        σ (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))
          (AdjoinRoot.root f)) =
          algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) a := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : FiniteDimensional K (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K f hf g hfg hg
  letI : Normal K (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_normal K f hf g hgmonic hfg hg
  intro a ha
  let q : Polynomial K := f.map (algebraMap 𝒪[K] K)
  let α : FractionRing (AdjoinRoot f) :=
    algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) (AdjoinRoot.root f)
  let β : FractionRing (AdjoinRoot f) :=
    algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) a
  have hcomm : (algebraMap K (FractionRing (AdjoinRoot f))).comp (algebraMap 𝒪[K] K) =
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (algebraMap 𝒪[K] (AdjoinRoot f)) := by
    ext r
    change IsFractionRing.lift hg₀ (algebraMap 𝒪[K] K r) = _
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hmap (r : Polynomial 𝒪[K]) :
      algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) (AdjoinRoot.mk f r) =
        Polynomial.aeval α (r.map (algebraMap 𝒪[K] K)) := by
    rw [← AdjoinRoot.aeval_eq r]
    exact Polynomial.map_aeval_eq_aeval_map hcomm r (AdjoinRoot.root f)
  have hα : Polynomial.aeval α q = 0 := by
    rw [← hmap f]
    simp
  have hβ : Polynomial.aeval β q = 0 := by
    change Polynomial.aeval
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) a)
      (f.map (algebraMap 𝒪[K] K)) = 0
    rw [← Polynomial.map_aeval_eq_aeval_map hcomm f a]
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, ha, map_zero]
  exact finiteNormal_irreducibleRoot_exists_gal_apply q
    (nonarchimedeanLocalFieldAdjoinRootFractionPolynomial_irreducible K f hf g hfg hg)
    (hf.map _) α β hα hβ

/-- Residue Galois action lifts to a fraction-field Galois automorphism on the distinguished
root, through an integral Hensel lift.  The witness records its integral image and its exact
residue, which is the root-level unramified Frobenius compatibility needed by local norms. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_liftResidueGalRoot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    ∀ σ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]),
      ∃ τ : Gal(FractionRing (AdjoinRoot f) / K), ∃ a : AdjoinRoot f,
        τ (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))
          (AdjoinRoot.root f)) =
          algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f)) a ∧
        IsLocalRing.residue (AdjoinRoot f) a =
          σ (IsLocalRing.residue (AdjoinRoot f) (AdjoinRoot.root f)) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  intro σ
  have hroot := nonarchimedeanLocalFieldAdjoinRoot_residue_root_apply_gal_isRoot
    K f hf g hfg hg σ
  obtain ⟨a, ha, hres⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_liftResidueConjugate K f hf g hfg hg _ hroot
  obtain ⟨τ, hτ⟩ :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_exists_gal_apply_root
      K f hf g hgmonic hfg hg a ha
  exact ⟨τ, a, hτ, hres⟩

/-- A monic irreducible lift has residue degree equal to the degree of its defining polynomial.
Together with its DVR property, this is the unramified degree calculation at the integral level. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueField_finrank
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    Module.finrank 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) = f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Algebra.Etale 𝒪[K] (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_etale K f hf g hgmonic hfg hg
  rw [← IsLocalRing.finrank_eq_finrank_residueField]
  exact (AdjoinRoot.isAdjoinRootMonic f hf).finrank

/-- The residue Galois group of a finite unramified root lift has order its residue degree.
This identifies the size of the cyclic Frobenius quotient with the degree of the lifted
irreducible polynomial. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueField_natCard_algEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    Nat.card Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) = f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  let e := nonarchimedeanLocalFieldAdjoinRootResidueFieldEquivOfMapEq K f hf g hfg hg
  letI : Finite (AdjoinRoot g) := by
    letI : Module.Finite 𝓀[K] (AdjoinRoot g) := hgmonic.finite_adjoinRoot
    exact Module.finite_of_finite 𝓀[K]
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Finite.of_surjective e.symm e.symm.surjective
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  letI : IsGalois 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_isGalois K f hf g hgmonic hfg hg
  calc
    Nat.card Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) =
        Module.finrank 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
      IsGalois.card_aut_eq_finrank _ _
    _ = f.natDegree :=
      nonarchimedeanLocalFieldAdjoinRootResidueField_finrank K f hf g hgmonic hfg hg

/-- A monic lift of a monic irreducible residue polynomial is itself a discrete valuation ring.
The root algebra is finite and formally unramified over the base DVR, hence Dedekind; its
previously established locality and nonzero maximal ideal then force the DVR structure. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    IsDiscreteValuationRing (AdjoinRoot f) := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : Module.Finite 𝒪[K] (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : Algebra.Etale 𝒪[K] (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_etale K f hf g hgmonic hfg hg
  letI : IsDedekindDomain 𝒪[K] :=
    ((IsDiscreteValuationRing.TFAE 𝒪[K]
      (IsDiscreteValuationRing.not_isField 𝒪[K])).out 0 2).mp
      (inferInstance : IsDiscreteValuationRing 𝒪[K])
  letI : IsDedekindDomain (AdjoinRoot f) :=
    isDedekindDomain.of_formallyUnramified 𝒪[K] (AdjoinRoot f)
  have hdegree : f.degree ≠ 0 :=
    nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hπmem : π ∈ 𝓂[K] := by
    rw [hπ.maximalIdeal_eq]
    exact Submodule.mem_span_singleton_self π
  have hmap_nonzero : Ideal.map (AdjoinRoot.of f) 𝓂[K] ≠ ⊥ := by
    intro hz
    have hmem : AdjoinRoot.of f π ∈ Ideal.map (AdjoinRoot.of f) 𝓂[K] :=
      Ideal.mem_map_of_mem (AdjoinRoot.of f) hπmem
    have himage : AdjoinRoot.of f π = 0 := by
      rw [hz] at hmem
      exact hmem
    exact hπ.ne_zero <|
      AdjoinRoot.of.injective_of_degree_ne_zero hdegree (by simpa using himage)
  have hmax : (Ideal.map (AdjoinRoot.of f) 𝓂[K]).IsMaximal :=
    nonarchimedeanLocalFieldAdjoinRootMapMaximalIdealIsMaximal K f g hfg hg
  have hnotfield : ¬ IsField (AdjoinRoot f) := by
    apply IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr
    rw [← IsLocalRing.eq_maximalIdeal hmax]
    exact hmap_nonzero
  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnotfield).out 2 0).mp
    (inferInstance : IsDedekindDomain (AdjoinRoot f))

/-- Every fraction-field automorphism obtained by lifting residue Galois preserves the canonical
extension valuation.  This is the unramifiedness input in the valuation-of-norm calculation. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_preserves_valuation
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    ∀ (τ : Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]))
      (x : FractionRing (AdjoinRoot f)),
      (IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))
        (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom
          K f hf g hgmonic hfg hg τ x) =
      (IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f)) x := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  intro τ x
  change (IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))
      (IsFractionRing.ringEquivOfRingEquiv
        (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom
          K f hf g hgmonic hfg hg τ).toRingEquiv x) = _
  exact discreteValuationRingFractionField_valuation_ringEquiv
    (AdjoinRoot f) (FractionRing (AdjoinRoot f))
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom
      K f hf g hgmonic hfg hg τ).toRingEquiv x

/-- A finite unramified root lift has ramification index one: its integral algebra map preserves
the discrete valuation order of every nonzero element. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_addVal_algebraMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    ∀ a : 𝒪[K], a ≠ 0 →
      IsDiscreteValuationRing.addVal (AdjoinRoot f) (AdjoinRoot.of f a) =
        IsDiscreteValuationRing.addVal 𝒪[K] a := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hmax : IsLocalRing.maximalIdeal (AdjoinRoot f) =
      Ideal.span {AdjoinRoot.of f π} := by
    rw [← nonarchimedeanLocalFieldAdjoinRoot_map_maximalIdeal K f hf g hfg hg,
      hπ.maximalIdeal_eq, Ideal.map_span]
    simp
  have hπB : Irreducible (AdjoinRoot.of f π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax
  intro a ha
  rw [addVal_map_eq_mul_ramification (AdjoinRoot.of f) hπ 1
    (IsDiscreteValuationRing.addVal_uniformizer hπB) a ha]
  simp

/-- The valuation on the fraction field of a finite unramified lift restricts exactly to the
canonical valuation on the base fraction field. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_valuation_algebraMap
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    ∀ x : FractionRing 𝒪[K],
      (IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))
        (algebraMap (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) x) =
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation
        (FractionRing 𝒪[K]) x := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  intro x
  exact discreteValuationRingFractionField_valuation_liftAlgebra
    (nonarchimedeanLocalFieldAdjoinRoot_addVal_algebraMap K f hf g hgmonic hfg hg) x

/-- The fraction field of a finite unramified lift carries the canonical rank-one discrete
valuation associated to the maximal ideal of its DVR of integers. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionFieldValuation
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    Valuation (FractionRing (AdjoinRoot f)) ℤᵐ⁰ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  exact (IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
    (FractionRing (AdjoinRoot f))

/-- The integral root algebra is exactly the valuation ring inside its fraction field for the
canonical lifted valuation. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionFieldValuationSubringEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    AdjoinRoot f ≃+* ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).valuationSubring := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  exact IsDiscreteValuationRing.equivValuationSubring

/-- The integral root algebra is the integer ring of the canonical valuation on its fraction
local field. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    AdjoinRoot f ≃+* ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  exact discreteValuationRingFractionFieldIntegerEquiv (AdjoinRoot f) (FractionRing (AdjoinRoot f))

/-- The residue field of the integral root algebra is canonically the residue field of the
integer ring of its fraction local field. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionFieldResidueFieldEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    IsLocalRing.ResidueField (AdjoinRoot f) ≃+*
      IsLocalRing.ResidueField ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  exact discreteValuationRingFractionFieldResidueFieldEquiv
    (AdjoinRoot f) (FractionRing (AdjoinRoot f))

/-- The canonical residue field of a finite unramified fraction local field is made an algebra
over the base residue field by transporting the integral residue extension along the canonical
residue-field equivalence. -/
@[reducible] noncomputable def
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    Algebra 𝓀[K] E := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  let e := nonarchimedeanLocalFieldAdjoinRootFractionFieldResidueFieldEquiv
    K f hf g hgmonic hfg hg
  exact RingHom.toAlgebra (e.toRingHom.comp
    (algebraMap 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))))

/-- The integral and canonical residue fields of a finite unramified fraction local field are
algebra-equivalent over the base residue field. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    IsLocalRing.ResidueField (AdjoinRoot f) ≃ₐ[𝓀[K]] E := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Algebra 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  let e := nonarchimedeanLocalFieldAdjoinRootFractionFieldResidueFieldEquiv
    K f hf g hgmonic hfg hg
  exact AlgEquiv.ofRingEquiv (f := e) fun _ => rfl

/-- The canonical valuation residue field of a finite unramified fraction local field is Galois
over the base residue field. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_isGalois
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    IsGalois 𝓀[K] E := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Algebra 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  letI : IsGalois 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_isGalois K f hf g hgmonic hfg hg
  exact IsGalois.of_algEquiv
    (nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgEquiv
      K f hf g hgmonic hfg hg)

/-- The canonical valuation on the lifted fraction field is rank-one discrete. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldValuation_isRankOneDiscrete
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).IsRankOneDiscrete := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  exact IsDiscreteValuationRing.isRankOneDiscrete (AdjoinRoot f) (FractionRing (AdjoinRoot f))

/-- The residue field of a monic irreducible lift is finite.  Together with the preceding DVR
theorem, this is the finite residue-field input for its arithmetic Frobenius. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueField_finite
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    Finite (IsLocalRing.ResidueField (AdjoinRoot f)) := by
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Module.Finite 𝓀[K] (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite 𝓀[K]
  let e := nonarchimedeanLocalFieldAdjoinRootResidueFieldEquivOfMapEq K f hf g hfg hg
  exact Finite.of_surjective e.symm e.symm.surjective

/-- The unramified fraction-field extension is Galois over the fraction field of its valuation
ring. This transports the established `K`-Galois structure along `FractionRing 𝒪[K] ≃ₐ[𝒪[K]] K`. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : IsGalois K (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K f hf g hgmonic hfg hg
  let e := FractionRing.algEquiv 𝒪[K] K
  have hforward :
      (algebraMap K (FractionRing (AdjoinRoot f))).comp e.toRingEquiv.toRingHom =
        (RingEquiv.refl (FractionRing (AdjoinRoot f))).toRingHom.comp
          (algebraMap (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))) := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[K])
    intro r
    simp only [RingHom.comp_apply]
    change (algebraMap K (FractionRing (AdjoinRoot f)))
      (e (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)) = _
    rw [e.commutes]
    change IsFractionRing.lift hg₀ (algebraMap 𝒪[K] K r) =
      IsFractionRing.lift hg₀ (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)
    rw [IsFractionRing.lift_algebraMap]
    rw [IsFractionRing.lift_algebraMap]
  refine IsGalois.of_equiv_equiv (f := e.symm.toRingEquiv)
    (g := RingEquiv.refl (FractionRing (AdjoinRoot f))) ?_
  ext x
  have hx := DFunLike.congr_fun hforward (e.symm x)
  simpa [e] using hx.symm

/-- The fraction-field Galois lift is surjective: source and target have the same cardinality,
namely the residue degree of the monic unramified lift. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_surjective
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    Function.Surjective
      (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom K f hf g hgmonic hfg hg) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
  letI : IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K f hf g hgmonic hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  letI := Fintype.ofFinite Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K])
  letI := Fintype.ofFinite Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K])
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨
    nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_injective
      K f hf g hgmonic hfg hg, ?_⟩).surjective
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  calc
    Nat.card Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) = f.natDegree :=
      nonarchimedeanLocalFieldAdjoinRootResidueField_natCard_algEquiv K f hf g hgmonic hfg hg
    _ = Module.finrank (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      (nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K f hf g hfg hg).symm
    _ = Nat.card Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) :=
      (IsGalois.card_aut_eq_finrank _ _).symm

/-- Every Galois automorphism of a finite unramified fraction-field lift preserves its canonical
extension valuation.  Surjectivity of the integral residue lift transfers this from lifted
residue automorphisms to the complete field Galois group. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_gal_preserves_valuation
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    ∀ (σ : Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]))
      (x : FractionRing (AdjoinRoot f)),
      (IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f)) (σ x) =
      (IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f)) x := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  intro σ x
  obtain ⟨τ, hτ⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_surjective
      K f hf g hgmonic hfg hg σ
  rw [← hτ]
  exact nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_preserves_valuation
    K f hf g hgmonic hfg hg τ x

/-- The extension valuation of a field norm in a finite unramified lift is the residue degree
times the valuation of its input (multiplicatively, the degree-th power). -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_valuation_norm
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    ∀ x : FractionRing (AdjoinRoot f),
      (IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))
        (algebraMap (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))
          (Algebra.norm (FractionRing 𝒪[K]) x)) =
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f)) x) ^ f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
  letI : IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing
      K f hf g hgmonic hfg hg
  intro x
  have hnorm := valuation_algebraMap_norm_eq_pow_of_gal_invariant
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f)))
    (nonarchimedeanLocalFieldAdjoinRootFractionField_gal_preserves_valuation
      K f hf g hgmonic hfg hg) x
  rw [hnorm, nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K f hf g hfg hg]

/-- The additive valuation of a field norm in a finite unramified lift is divisible by the
unramified degree.  Together with norm-surjectivity on valuation-zero units, this isolates the
entire unramified norm quotient in the valuation lattice. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_tameValHom_norm
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    ∀ x : (FractionRing (AdjoinRoot f))ˣ,
      tameValHom ((IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation
        (FractionRing 𝒪[K]))
        (Units.map (Algebra.norm (FractionRing 𝒪[K])) x) =
      (tameValHom ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))) x) ^ f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  intro x
  have hval :
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation
        (FractionRing 𝒪[K])
        (Algebra.norm (FractionRing 𝒪[K]) (x : FractionRing (AdjoinRoot f))) =
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f)) (x : FractionRing (AdjoinRoot f))) ^ f.natDegree := by
    calc
      (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation
          (FractionRing 𝒪[K])
          (Algebra.norm (FractionRing 𝒪[K]) (x : FractionRing (AdjoinRoot f))) =
        (IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
          (FractionRing (AdjoinRoot f))
          (algebraMap (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))
            (Algebra.norm (FractionRing 𝒪[K]) (x : FractionRing (AdjoinRoot f)))) := by
          symm
          exact nonarchimedeanLocalFieldAdjoinRootFractionField_valuation_algebraMap
            K f hf g hgmonic hfg hg _
      _ = _ := nonarchimedeanLocalFieldAdjoinRootFractionField_valuation_norm
        K f hf g hgmonic hfg hg x
  exact tameValHom_norm_eq_pow_of_valuation
    ((IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation (FractionRing 𝒪[K]))
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))) f.natDegree x hval

/-- The valuation modulo the unramified degree is a closed invariant of the cyclic local norm
quotient.  It is the finite-degree precursor of the nonarchimedean local Brauer invariant; this
definition does not yet assert that it is an isomorphism onto `ℤ/nℤ`. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionField_normQuotientValuationInvariant
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
    Additive (FractionRing 𝒪[K])ˣ ⧸
      cyclicGaloisH2BaseNormImage (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) →+
        ZMod f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  exact cyclicGaloisH2BaseNormQuotient_tameValModNat
    (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f))
    ((IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation (FractionRing 𝒪[K]))
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))) f.natDegree
    (nonarchimedeanLocalFieldAdjoinRootFractionField_tameValHom_norm
      K f hf g hgmonic hfg hg)

/-- The full Galois group of a finite unramified fraction-field lift is cyclic. The canonical
Frobenius description comes from the surjective residue-to-fraction-field Galois lift. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    IsCyclic Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : IsCyclic Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_isCyclic K f hf g hgmonic hfg hg
  exact isCyclic_of_surjective
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom K f hf g hgmonic hfg hg)
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_surjective
      K f hf g hgmonic hfg hg)

/-- The explicit fraction-field unit quotient by norms in a finite unramified lift is killed by
its residue degree. This is the local cyclic-parameter torsion bound before any comparison of
the quotient with a local Brauer invariant. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_normQuotient_degree_nsmul_eq_zero
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) := nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
      change Function.Injective <| AdjoinRoot.of f
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
    letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
        (FractionRing (AdjoinRoot f))).mpr ?_
      change Function.Injective <|
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
    letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
    letI : Algebra K (FractionRing (AdjoinRoot f)) := by
      let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
        (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
      have hg₀ : Function.Injective g₀ :=
        (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
    letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
    letI : IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K f hf g hgmonic hfg hg
    letI : IsCyclic Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K f hf g hgmonic hfg hg
    ∀ z : Additive (FractionRing 𝒪[K])ˣ ⧸
      cyclicGaloisH2BaseNormImage (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)),
      f.natDegree • z = 0 := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot f))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : FiniteDimensional (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K f hf g hfg hg
  letI : IsGalois (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K f hf g hgmonic hfg hg
  letI : IsCyclic Gal(FractionRing (AdjoinRoot f) / FractionRing 𝒪[K]) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K f hf g hgmonic hfg hg
  intro z
  rw [← nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K f hf g hfg hg]
  exact cyclicGaloisH2BaseNormQuotient_finrank_nsmul_eq_zero
    (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot f)) z

/-- The residue field of a finite unramified root lift has cardinality `q^n`, where `q` is the
cardinality of the base residue field and `n` is the degree of the lift. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueField_natCard
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    Nat.card (IsLocalRing.ResidueField (AdjoinRoot f)) =
      Nat.card 𝓀[K] ^ f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain (K := K) (f := f) (hf := hf) (g := g)
      (hfg := hfg) (hg := hg)
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing (K := K) (f := f) (hf := hf) (g := g)
      (hfg := hfg) (hg := hg)
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom (K := K) (f := f) (hf := hf) (g := g)
      (hfg := hfg) (hg := hg)
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := 𝓀[K])]
  rw [nonarchimedeanLocalFieldAdjoinRootResidueField_finrank K f hf g hgmonic hfg hg]

/-- The canonical integer ring of every finite unramified fraction local field has finite
residue field. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    Finite (IsLocalRing.ResidueField ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  exact discreteValuationRingFractionFieldIntegerResidueField_finite
    (AdjoinRoot f) (FractionRing (AdjoinRoot f))

/-- The canonical valuation residue extension of a finite unramified fraction local field has
cyclic Galois group over the base residue field. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_isCyclic
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    IsCyclic Gal(E / 𝓀[K]) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Algebra 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  letI : Finite (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  letI : IsGalois 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_isGalois
      K f hf g hgmonic hfg hg
  infer_instance

/-- The Galois group of the canonical valuation residue extension has exactly the unramified
degree of the lifted root polynomial. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_natCard_algEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    Nat.card Gal(E / 𝓀[K]) = f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Algebra 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  letI : Finite (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    Module.Finite.of_finite
  letI : IsGalois 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_isGalois
      K f hf g hgmonic hfg hg
  calc
    Nat.card Gal(IsLocalRing.ResidueField
        ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
          (FractionRing (AdjoinRoot f))).integer / 𝓀[K]) =
        Module.finrank 𝓀[K] (IsLocalRing.ResidueField
          ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
            (FractionRing (AdjoinRoot f))).integer) :=
      IsGalois.card_aut_eq_finrank _ _
    _ = Module.finrank 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
      (nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgEquiv
        K f hf g hgmonic hfg hg).toLinearEquiv.finrank_eq.symm
    _ = f.natDegree :=
      nonarchimedeanLocalFieldAdjoinRootResidueField_finrank K f hf g hgmonic hfg hg

/-- The canonical valuation residue extension of a finite unramified fraction local field has
degree equal to the lifted root degree. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finrank
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    Module.finrank 𝓀[K] E = f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  let E := IsLocalRing.ResidueField
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer
  letI : Algebra 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  exact (nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgEquiv
    K f hf g hgmonic hfg hg).toLinearEquiv.finrank_eq.symm.trans
      (nonarchimedeanLocalFieldAdjoinRootResidueField_finrank K f hf g hgmonic hfg hg)

/-- Arithmetic Frobenius on the canonical residue extension of a finite unramified local
field. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    Gal(E / 𝓀[K]) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Algebra 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  letI : Finite (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    Algebra.IsAlgebraic.of_finite 𝓀[K] _
  letI := Fintype.ofFinite 𝓀[K]
  exact FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K]
    (IsLocalRing.ResidueField ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer)

/-- Arithmetic Frobenius acts by the base residue cardinality power. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    ∀ x : E,
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius
        K f hf g hgmonic hfg hg x = x ^ Nat.card 𝓀[K] := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  let E := IsLocalRing.ResidueField
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer
  letI : Algebra 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  letI : Finite (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    Algebra.IsAlgebraic.of_finite 𝓀[K] _
  letI := Fintype.ofFinite 𝓀[K]
  change ∀ x : E, (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] E) x =
    x ^ Nat.card 𝓀[K]
  intro x
  rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply]
  rw [Fintype.card_eq_nat_card]

/-- Arithmetic Frobenius has order equal to the unramified residue degree. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius_orderOf
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    orderOf (nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius
      K f hf g hgmonic hfg hg) = f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Algebra 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  letI : Finite (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] (IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer) :=
    Algebra.IsAlgebraic.of_finite 𝓀[K] _
  letI := Fintype.ofFinite 𝓀[K]
  change orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K]
    (IsLocalRing.ResidueField ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer)) = f.natDegree
  rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  exact nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finrank
    K f hf g hgmonic hfg hg

/-- Every residue automorphism is a bounded power of arithmetic Frobenius. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius_exists_pow_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (σ :
      letI : IsDomain (AdjoinRoot f) :=
        nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
      letI : IsLocalRing (AdjoinRoot f) :=
        nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
      letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
        nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
      letI : IsDiscreteValuationRing (AdjoinRoot f) :=
        nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
      let E := IsLocalRing.ResidueField
        ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
          (FractionRing (AdjoinRoot f))).integer
      letI : Algebra 𝓀[K] E :=
        nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
          K f hf g hgmonic hfg hg
      Gal(E / 𝓀[K])) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    ∃ i < f.natDegree,
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius
        K f hf g hgmonic hfg hg ^ i = σ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  let E := IsLocalRing.ResidueField
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer
  letI : Algebra 𝓀[K] E :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  letI : Finite E :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] E := Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] E := Algebra.IsAlgebraic.of_finite 𝓀[K] _
  letI := Fintype.ofFinite 𝓀[K]
  obtain ⟨⟨i, hi⟩, hσ⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow 𝓀[K] E).surjective σ
  refine ⟨i, ?_, hσ⟩
  rwa [nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finrank
    K f hf g hgmonic hfg hg] at hi

/-- Arithmetic Frobenius generates the canonical residue Galois group. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius_zpowers_eq_top
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    Subgroup.zpowers
        (nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius
          K f hf g hgmonic hfg hg) = ⊤ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  let E := IsLocalRing.ResidueField
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer
  letI : Algebra 𝓀[K] E :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  apply le_antisymm le_top
  intro σ _
  obtain ⟨i, -, hσ⟩ :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius_exists_pow_eq
      K f hf g hgmonic hfg hg σ
  rw [← hσ]
  exact (Subgroup.zpowers _).pow_mem (by simp) i

/-- Finite unramified reciprocity on the canonical valuation residue extension: its Galois group
is the cyclic group of the residue degree, generated by arithmetic Frobenius. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueGaloisZModEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    Multiplicative (ZMod f.natDegree) ≃* Gal(E / 𝓀[K]) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  let E := IsLocalRing.ResidueField
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer
  letI : Algebra 𝓀[K] E :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  letI : Finite E :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] E := Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] E := Algebra.IsAlgebraic.of_finite 𝓀[K] _
  let ζ := nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius
    K f hf g hgmonic hfg hg
  have hζtop : Subgroup.zpowers ζ = ⊤ := by
    simpa [ζ] using
      (nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius_zpowers_eq_top
        K f hf g hgmonic hfg hg)
  refine zmodMulEquivOfGenerator (g := ζ) ?_ ?_
  · intro σ
    rw [hζtop]
    trivial
  · exact nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_natCard_algEquiv
      K f hf g hgmonic hfg hg

/-- Canonical finite unramified reciprocity sends `1 mod n` to arithmetic Frobenius. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueGaloisZModEquiv_apply_one
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueGaloisZModEquiv
        K f hf g hgmonic hfg hg (Multiplicative.ofAdd (1 : ZMod f.natDegree)) =
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius
        K f hf g hgmonic hfg hg := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  simp [nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueGaloisZModEquiv]

/-- The canonical finite unramified residue extension satisfies the cyclic norm sequence.
This is the residue-field quotient of local norm reciprocity. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius_fullNormSequence
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Algebra 𝓀[K] E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
        K f hf g hgmonic hfg hg
    Function.Injective (cyclicGaloisBaseUnitsMap (K := 𝓀[K]) (L := E)) ∧
      Function.Exact (cyclicGaloisBaseUnitsMap (K := 𝓀[K]) (L := E))
        (cyclicGaloisAdditiveCoboundary
          (nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius
            K f hf g hgmonic hfg hg)) ∧
      Function.Exact (cyclicGaloisAdditiveCoboundary
        (nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius
          K f hf g hgmonic hfg hg))
        (cyclicGaloisAdditiveNormUnits 𝓀[K] E) ∧
      Function.Surjective (cyclicGaloisAdditiveNormUnits 𝓀[K] E) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  let E := IsLocalRing.ResidueField
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer
  letI : Algebra 𝓀[K] E :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueAlgebra
      K f hf g hgmonic hfg hg
  letI : Finite E :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  apply finiteField_cyclicGaloisFullNormSequence
  intro σ
  rw [nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueFrobenius_zpowers_eq_top
    K f hf g hgmonic hfg hg]
  trivial

/-- The canonical valuation residue field of a finite unramified fraction local field has
cardinality `q^n`, with `q` the base residue cardinality and `n` the extension degree. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_natCard
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Finite E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
        K f hf g hgmonic hfg hg
    Nat.card E = Nat.card 𝓀[K] ^ f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  let e := nonarchimedeanLocalFieldAdjoinRootFractionFieldResidueFieldEquiv
    K f hf g hgmonic hfg hg
  exact (Nat.card_congr e.toEquiv).symm.trans
    (nonarchimedeanLocalFieldAdjoinRootResidueField_natCard K f hf g hgmonic hfg hg)

/-- Units of the canonical valuation residue field of a finite unramified fraction local field
form a cyclic group.  This is the finite quotient used by unramified Frobenius and norms. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueUnitGroup_isCyclic
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Finite E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
        K f hf g hgmonic hfg hg
    IsCyclic Eˣ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  let E := IsLocalRing.ResidueField
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer
  letI : Finite E :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  infer_instance

/-- The canonical valuation residue unit group of a finite unramified fraction local field has
cardinality `q^n - 1`, with `q` the base residue cardinality and `n` the extension degree. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueUnitGroup_natCard
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    let E := IsLocalRing.ResidueField
      ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer
    letI : Finite E :=
      nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
        K f hf g hgmonic hfg hg
    Nat.card Eˣ = Nat.card 𝓀[K] ^ f.natDegree - 1 := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  let E := IsLocalRing.ResidueField
    ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer
  letI : Finite E :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  change Nat.card Eˣ = Nat.card 𝓀[K] ^ f.natDegree - 1
  rw [Nat.card_units]
  rw [nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_natCard
    K f hf g hgmonic hfg hg]

/-- Every Brauer class over the canonical valuation residue field of a finite unramified
fraction local field is split.  This transfers the finite-residue Brauer vanishing from the
integral lift to the local field's own integer ring. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_brauerGroup_eq_split
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    ∀ x : BrauerGroup.{u, u}
      (IsLocalRing.ResidueField ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
        (FractionRing (AdjoinRoot f))).integer),
      x = brauerSplitClass
        (IsLocalRing.ResidueField ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
          (FractionRing (AdjoinRoot f))).integer) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : Finite (IsLocalRing.ResidueField ((IsDiscreteValuationRing.maximalIdeal (AdjoinRoot f)).valuation
      (FractionRing (AdjoinRoot f))).integer) :=
    nonarchimedeanLocalFieldAdjoinRootFractionFieldIntegerResidueField_finite
      K f hf g hgmonic hfg hg
  intro x
  exact finiteField_brauerGroup_eq_split _ x

/-- The fraction field of a finite unramified root lift is itself a nonarchimedean local field
for the canonical valuation coming from the lifted DVR.  This upgrades the preceding integral
adic-completeness and finite-residue results to the actual local-field extension layer. -/
theorem nonarchimedeanLocalFieldAdjoinRootFractionField_isNonarchimedeanLocalField
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsDiscreteValuationRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
    letI : ValuativeRel (FractionRing (AdjoinRoot f)) :=
      discreteValuationRingFractionFieldValuativeRel (AdjoinRoot f) (FractionRing (AdjoinRoot f))
    letI : TopologicalSpace (FractionRing (AdjoinRoot f)) :=
      discreteValuationRingFractionFieldTopology (AdjoinRoot f) (FractionRing (AdjoinRoot f))
    IsNonarchimedeanLocalField (FractionRing (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg
  letI : IsAdicComplete (IsLocalRing.maximalIdeal (AdjoinRoot f)) (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isAdicComplete K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  exact discreteValuationRingFractionField_isNonarchimedeanLocalField_of_isAdicComplete_of_finiteResidueField
    (AdjoinRoot f) (FractionRing (AdjoinRoot f))

/-- The nonzero residue classes of a monic irreducible lift form a cyclic group.  A chosen
generator is the finite residue-field counterpart of an unramified Frobenius datum. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueUnitGroup_isCyclic
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    IsCyclic ((IsLocalRing.ResidueField (AdjoinRoot f))ˣ) := by
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Module.Finite 𝓀[K] (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite 𝓀[K]
  let e := nonarchimedeanLocalFieldAdjoinRootResidueFieldEquivOfMapEq K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Finite.of_surjective e.symm e.symm.surjective
  infer_instance

/-- The relative arithmetic Frobenius of the residue extension induced by a monic irreducible
lift.  It fixes the base residue field and acts by its cardinality power map. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootResidueFrobenius
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Algebra.IsAlgebraic.of_finite 𝓀[K] _
  letI := Fintype.ofFinite 𝓀[K]
  exact FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K]
    (IsLocalRing.ResidueField (AdjoinRoot f))

/-- The relative residue Frobenius is the cardinality power map of the base residue field. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ x : IsLocalRing.ResidueField (AdjoinRoot f),
      nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K f hf g hgmonic hfg hg x =
        x ^ Nat.card 𝓀[K] := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Algebra.IsAlgebraic.of_finite 𝓀[K] _
  letI := Fintype.ofFinite 𝓀[K]
  intro x
  change x ^ Fintype.card 𝓀[K] = x ^ Nat.card 𝓀[K]
  rw [Fintype.card_eq_nat_card]

/-- The residue Frobenius has order exactly the residue degree of the lift.  Thus it generates
the cyclic Galois group of the finite residue extension. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_orderOf
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    orderOf (nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K f hf g hgmonic hfg hg) =
      f.natDegree := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Algebra.IsAlgebraic.of_finite 𝓀[K] _
  letI := Fintype.ofFinite 𝓀[K]
  change orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K]
    (IsLocalRing.ResidueField (AdjoinRoot f))) = f.natDegree
  rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  exact nonarchimedeanLocalFieldAdjoinRootResidueField_finrank K f hf g hgmonic hfg hg

/-- Every automorphism of the lifted residue extension is a power of relative Frobenius, with
exponent strictly below the residue degree. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_exists_pow_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g)
    (σ :
      letI : IsDomain (AdjoinRoot f) :=
        nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
      letI : IsLocalRing (AdjoinRoot f) :=
        nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
      letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
        nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
      Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K])) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∃ i < f.natDegree,
      nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K f hf g hgmonic hfg hg ^ i = σ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Algebra.IsAlgebraic.of_finite 𝓀[K] _
  letI := Fintype.ofFinite 𝓀[K]
  obtain ⟨⟨i, hi⟩, hσ⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow 𝓀[K]
      (IsLocalRing.ResidueField (AdjoinRoot f))).surjective σ
  refine ⟨i, ?_, hσ⟩
  rwa [nonarchimedeanLocalFieldAdjoinRootResidueField_finrank K f hf g hgmonic hfg hg] at hi

/-- Relative residue Frobenius generates the whole Galois group of the finite residue extension.
This packages the finite unramified quotient in the form used by arithmetic Frobenius and local
reciprocity. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_zpowers_eq_top
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    Subgroup.zpowers
        (nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K f hf g hgmonic hfg hg) = ⊤ := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  apply le_antisymm le_top
  intro σ _
  obtain ⟨i, -, hσ⟩ :=
    nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_exists_pow_eq K f hf g hgmonic hfg hg σ
  rw [← hσ]
  exact (Subgroup.zpowers _).pow_mem (by simp) i

/-- For a `Type`-valued finite unramified lift, residue arithmetic Frobenius gives the full
cyclic norm sequence: base units embed, the Frobenius coboundary has norm kernel, and the
residue norm is surjective.  This is the finite unramified quotient of local norm reciprocity,
before the separate passage from residue units to local-field units. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_fullNormSequence
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    Function.Injective (cyclicGaloisBaseUnitsMap (K := 𝓀[K])
      (L := IsLocalRing.ResidueField (AdjoinRoot f))) ∧
      Function.Exact (cyclicGaloisBaseUnitsMap (K := 𝓀[K])
        (L := IsLocalRing.ResidueField (AdjoinRoot f)))
        (cyclicGaloisAdditiveCoboundary
          (nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K f hf g hgmonic hfg hg)) ∧
      Function.Exact (cyclicGaloisAdditiveCoboundary
        (nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K f hf g hgmonic hfg hg))
        (cyclicGaloisAdditiveNormUnits 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) ∧
      Function.Surjective
        (cyclicGaloisAdditiveNormUnits 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  apply finiteField_cyclicGaloisFullNormSequence
  intro σ
  rw [nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_zpowers_eq_top K f hf g hgmonic hfg hg]
  trivial

/-- For a `Type`-valued finite unramified lift, degree-two Galois cohomology of residue-field
units vanishes.  This is the cohomological finite-residue input to the local Brauer-invariant
sequence; it does not claim the still-missing comparison with a local Brauer group. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueField_H2_eq_zero
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ z : groupCohomology
      (Rep.ofAlgebraAutOnUnits 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f))) 2, z = 0 := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  intro z
  exact finiteField_H2_eq_zero z

/-- For a `Type`-valued finite unramified lift, continuous degree-two Galois cohomology of
residue-field units vanishes.  This is the continuous finite-residue input to the local
Brauer-invariant sequence; transporting it to the fraction field remains a separate theorem. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueField_continuousH2_eq_zero
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    ∀ z : continuousGaloisUnitCohomology 2 𝓀[K]
      (IsLocalRing.ResidueField (AdjoinRoot f)), z = 0 := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  intro z
  exact finiteField_continuousGaloisH2_eq_zero z

/-- The residue Brauer group of every finite unramified root lift is trivial: every residue
Brauer class is split.  This is the zero residue term used before constructing local invariants
for the fraction field. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueField_brauerGroup_eq_split
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    ∀ x : BrauerGroup.{u, u} (IsLocalRing.ResidueField (AdjoinRoot f)),
      x = brauerSplitClass (IsLocalRing.ResidueField (AdjoinRoot f)) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  intro x
  exact finiteField_brauerGroup_eq_split _ x

/-- Finite-level unramified reciprocity: the residue Galois group of the lifted extension is
identified with the cyclic group of its residue degree, with arithmetic Frobenius as generator. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootResidueGaloisZModEquiv
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    Multiplicative (ZMod f.natDegree) ≃*
      Gal(IsLocalRing.ResidueField (AdjoinRoot f) / 𝓀[K]) := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K f hf g hgmonic hfg hg
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Module.Finite.of_finite
  letI : Algebra.IsAlgebraic 𝓀[K] (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Algebra.IsAlgebraic.of_finite 𝓀[K] _
  let ζ := nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K f hf g hgmonic hfg hg
  have hζtop : Subgroup.zpowers ζ = ⊤ := by
    simpa [ζ] using
      (nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_zpowers_eq_top K f hf g hgmonic hfg hg)
  refine zmodMulEquivOfGenerator (g := ζ) ?_ ?_
  · intro σ
    rw [hζtop]
    trivial
  · exact nonarchimedeanLocalFieldAdjoinRootResidueField_natCard_algEquiv K f hf g hgmonic hfg hg

/-- The finite-level reciprocity equivalence sends `1` to arithmetic residue Frobenius. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueGaloisZModEquiv_apply_one
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsDomain (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
    nonarchimedeanLocalFieldAdjoinRootResidueGaloisZModEquiv K f hf g hgmonic hfg hg
        (Multiplicative.ofAdd (1 : ZMod f.natDegree)) =
      nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K f hf g hgmonic hfg hg := by
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K f hf g hfg hg
  simp [nonarchimedeanLocalFieldAdjoinRootResidueGaloisZModEquiv]

/-- The absolute Frobenius automorphism of the finite residue field of a monic irreducible lift.
This is the residue-field automorphism which an arithmetic Frobenius lift must induce. -/
noncomputable def nonarchimedeanLocalFieldAdjoinRootResidueAbsoluteFrobenius
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    IsLocalRing.ResidueField (AdjoinRoot f) ≃+* IsLocalRing.ResidueField (AdjoinRoot f) := by
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Module.Finite 𝓀[K] (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite 𝓀[K]
  let e := nonarchimedeanLocalFieldAdjoinRootResidueFieldEquivOfMapEq K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Finite.of_surjective e.symm e.symm.surjective
  exact frobeniusEquiv _ (ringExpChar (IsLocalRing.ResidueField (AdjoinRoot f)))

/-- The residue absolute Frobenius is the expected power map. -/
theorem nonarchimedeanLocalFieldAdjoinRootResidueAbsoluteFrobenius_apply
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hgmonic : g.Monic)
    (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g) (hg : Irreducible g) :
    letI : IsLocalRing (AdjoinRoot f) :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
    ∀ x : IsLocalRing.ResidueField (AdjoinRoot f),
      nonarchimedeanLocalFieldAdjoinRootResidueAbsoluteFrobenius K f hf g hgmonic hfg hg x =
        x ^ ringExpChar (IsLocalRing.ResidueField (AdjoinRoot f)) := by
  letI : IsLocalRing (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K f hf g hfg hg
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Module.Finite 𝓀[K] (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite 𝓀[K]
  let e := nonarchimedeanLocalFieldAdjoinRootResidueFieldEquivOfMapEq K f hf g hfg hg
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Finite.of_surjective e.symm e.symm.surjective
  intro x
  exact frobeniusEquiv_def _ _ x

/-- For every positive degree, the finite residue field has a monic irreducible polynomial of
that degree.  This supplies the residue data for a degree-`n` unramified lift. -/
theorem nonarchimedeanLocalField_exists_monic_irreducible_residuePolynomial_of_natDegree
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ g : Polynomial 𝓀[K], g.Monic ∧ Irreducible g ∧ g.natDegree = n := by
  letI : Fact (ringChar 𝓀[K]).Prime :=
    ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩
  let E := FiniteField.Extension 𝓀[K] (ringChar 𝓀[K]) n
  letI : Algebra 𝓀[K] E := inferInstance
  letI : Module.Finite 𝓀[K] E := inferInstance
  letI : Finite E := inferInstance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_bot 𝓀[K] E
  refine ⟨minpoly 𝓀[K] α, minpoly.monic (IsIntegral.of_finite 𝓀[K] α),
    minpoly.irreducible (IsIntegral.of_finite 𝓀[K] α), ?_⟩
  rw [(Field.primitive_element_iff_minpoly_natDegree_eq 𝓀[K] α).mp hα]
  exact FiniteField.finrank_extension 𝓀[K] (ringChar 𝓀[K]) n

/-- Every positive degree occurs as the degree of a monic lift whose root algebra is a finite
formally unramified DVR over the local valuation ring.  This is the integral existence part of
the unramified-extension construction. -/
theorem nonarchimedeanLocalField_exists_finiteUnramifiedDVRLift_of_natDegree
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K]), ∃ hf : f.Monic, g.Monic ∧
      ∃ hg : Irreducible g, ∃ hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g, f.natDegree = n ∧
      letI : IsDomain (AdjoinRoot f) :=
        nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
      IsDiscreteValuationRing (AdjoinRoot f) := by
  obtain ⟨g, hgmonic, hg, hgdegree⟩ :=
    nonarchimedeanLocalField_exists_monic_irreducible_residuePolynomial_of_natDegree K n
  obtain ⟨f, hf, hfg, hdegree⟩ :=
    nonarchimedeanLocalField_exists_monic_residuePolynomial_lift K g hgmonic
  refine ⟨f, g, hf, hgmonic, hg, hfg, hdegree.trans hgdegree, ?_⟩
  exact nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K f hf g hgmonic hfg hg

/-- Every positive degree has a concrete unramified root presentation whose fraction field is
Galois over the given nonarchimedean local field.  This upgrades the existing integral DVR-lift
supply by the splitting and normality argument for the fraction field. -/
theorem nonarchimedeanLocalField_exists_unramifiedGaloisLift_of_natDegree
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K]) (hf : f.Monic), g.Monic ∧
      ∃ hg : Irreducible g, ∃ hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g, f.natDegree = n ∧
      letI : IsDomain (AdjoinRoot f) :=
        nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
      letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
        refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
        change Function.Injective <| AdjoinRoot.of f
        exact AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
      letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
        refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
          (FractionRing (AdjoinRoot f))).mpr ?_
        change Function.Injective <|
          (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
        exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
      letI : Algebra K (FractionRing (AdjoinRoot f)) := by
        let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
          (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
        have hg₀ : Function.Injective g₀ :=
          (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
            (AdjoinRoot.of.injective_of_degree_ne_zero
              (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
        exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
      FiniteDimensional K (FractionRing (AdjoinRoot f)) ∧
        IsGalois K (FractionRing (AdjoinRoot f)) ∧
        Module.finrank K (FractionRing (AdjoinRoot f)) = n := by
  obtain ⟨f, g, hf, hgmonic, hg, hfg, hdegree, hDVR⟩ :=
    nonarchimedeanLocalField_exists_finiteUnramifiedDVRLift_of_natDegree K n
  refine ⟨f, g, hf, hgmonic, hg, hfg, hdegree, ?_⟩
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot f) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] (AdjoinRoot f)).mpr ?_
    change Function.Injective <| AdjoinRoot.of f
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot f)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot f))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
    exact (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot f) :=
    (algebraMap (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp (AdjoinRoot.of f)
  have hg₀ : Function.Injective g₀ :=
    (IsFractionRing.injective (AdjoinRoot f) (FractionRing (AdjoinRoot f))).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg))
  letI : Algebra K (FractionRing (AdjoinRoot f)) := RingHom.toAlgebra (IsFractionRing.lift hg₀)
  letI : FiniteDimensional K (FractionRing (AdjoinRoot f)) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K f hf g hfg hg
  refine ⟨inferInstance, ?_, ?_⟩
  · exact nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K f hf g hgmonic hfg hg
  · exact (nonarchimedeanLocalFieldAdjoinRootFractionField_finrankOverBase K f hf g hfg hg).trans
      hdegree

/-- Every positive degree occurs as the residue degree of a concrete nonarchimedean local field
obtained from a finite unramified DVR lift.  This is the finite-level extension supply used
before passing to an unramified reciprocity limit. -/
theorem nonarchimedeanLocalField_exists_finiteUnramifiedLocalFieldLift_of_natDegree
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K]), ∃ hf : f.Monic, g.Monic ∧
      ∃ hg : Irreducible g, ∃ hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g, f.natDegree = n ∧
      letI : IsDomain (AdjoinRoot f) :=
        nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
      ∃ hDVR : IsDiscreteValuationRing (AdjoinRoot f),
        letI : IsDiscreteValuationRing (AdjoinRoot f) := hDVR
        letI : ValuativeRel (FractionRing (AdjoinRoot f)) :=
          discreteValuationRingFractionFieldValuativeRel (AdjoinRoot f) (FractionRing (AdjoinRoot f))
        letI : TopologicalSpace (FractionRing (AdjoinRoot f)) :=
          discreteValuationRingFractionFieldTopology (AdjoinRoot f) (FractionRing (AdjoinRoot f))
        IsNonarchimedeanLocalField (FractionRing (AdjoinRoot f)) := by
  obtain ⟨f, g, hf, hgmonic, hg, hfg, hdegree, hDVR⟩ :=
    nonarchimedeanLocalField_exists_finiteUnramifiedDVRLift_of_natDegree K n
  refine ⟨f, g, hf, hgmonic, hg, hfg, hdegree, hDVR, ?_⟩
  letI : IsDomain (AdjoinRoot f) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K f hf g hfg hg
  letI : IsDiscreteValuationRing (AdjoinRoot f) := hDVR
  exact nonarchimedeanLocalFieldAdjoinRootFractionField_isNonarchimedeanLocalField
    K f hf g hgmonic hfg hg

/-- Every monic residue polynomial admits a same-degree monic lift whose root algebra is finite
and free over the valuation ring and whose reduction is the prescribed residue root algebra.
This is the algebra-presentation part of an unramified-extension construction. -/
theorem nonarchimedeanLocalField_exists_finite_free_residuePolynomial_lift
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (g : Polynomial 𝓀[K]) (hg : g.Monic) :
    ∃ f : Polynomial 𝒪[K], f.Monic ∧ f.map (Ideal.Quotient.mk 𝓂[K]) = g ∧
      f.natDegree = g.natDegree ∧ Module.Free 𝒪[K] (AdjoinRoot f) ∧
      Module.Finite 𝒪[K] (AdjoinRoot f) := by
  obtain ⟨f, hf, hmap, hdegree⟩ :=
    nonarchimedeanLocalField_exists_monic_residuePolynomial_lift K g hg
  exact ⟨f, hf, hmap, hdegree, hf.free_adjoinRoot, hf.finite_adjoinRoot⟩

/-- Chosen finite extension of the residue field of degree `n`.  This is only a residue-field
extension; promoting it to an unramified extension of `K` additionally requires a chosen
monogenic presentation and an identification of the lifted root algebra as a valuation ring. -/
noncomputable abbrev nonarchimedeanLocalFieldResidueExtension
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] : Type := by
  letI : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩
  exact FiniteField.Extension 𝓀[K] (ringChar 𝓀[K]) n

/-- The chosen degree-`n` residue extension has vector-space degree `n`. -/
theorem nonarchimedeanLocalFieldResidueExtension_finrank
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    Module.finrank 𝓀[K] (nonarchimedeanLocalFieldResidueExtension K n) = n := by
  letI : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩
  exact FiniteField.finrank_extension 𝓀[K] (ringChar 𝓀[K]) n

/-- The residue cardinality of the chosen degree-`n` extension is `q^n`. -/
theorem nonarchimedeanLocalFieldResidueExtension_natCard
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    Nat.card (nonarchimedeanLocalFieldResidueExtension K n) = Nat.card 𝓀[K] ^ n := by
  letI : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩
  exact FiniteField.natCard_extension 𝓀[K] (ringChar 𝓀[K]) n

/-- The Galois group of the chosen residue extension is cyclic. -/
theorem nonarchimedeanLocalFieldResidueExtension_isCyclic
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    IsCyclic Gal(nonarchimedeanLocalFieldResidueExtension K n / 𝓀[K]) := by
  infer_instance

/-- Arithmetic Frobenius in the selected residue extension. -/
noncomputable def nonarchimedeanLocalFieldResidueExtensionFrobenius
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    Gal(nonarchimedeanLocalFieldResidueExtension K n / 𝓀[K]) := by
  letI : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩
  exact FiniteField.Extension.frob 𝓀[K] (ringChar 𝓀[K]) n

/-- Every automorphism of the selected residue extension is a power of arithmetic Frobenius. -/
theorem nonarchimedeanLocalFieldResidueExtension_exists_frobenius_pow_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n]
    (g : Gal(nonarchimedeanLocalFieldResidueExtension K n / 𝓀[K])) :
    ∃ i < n, nonarchimedeanLocalFieldResidueExtensionFrobenius K n ^ i = g := by
  letI : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K])⟩
  exact FiniteField.Extension.exists_frob_pow_eq 𝓀[K] (ringChar 𝓀[K]) n g

/-- The valuation ring of a nonarchimedean local field is a Henselian local ring. -/
theorem nonarchimedeanLocalField_henselianLocalRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : HenselianLocalRing 𝒪[K] := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup (G := K)
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ ha₀ hderivative
  exact HenselianRing.is_henselian f hf a₀ ha₀
    (hderivative.map (Ideal.Quotient.mk _))

end GaloisForLFunctions.HTGeometry.ABHN
