/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import GaloisForLFunctions.HTGeometry.ABHN.FiniteEtale
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
open scoped ValuativeRel WithZero WithZeroMulInt

attribute [local instance] Ideal.Quotient.field

universe u

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
