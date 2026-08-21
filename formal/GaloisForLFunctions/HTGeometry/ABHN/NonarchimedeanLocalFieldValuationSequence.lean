/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Henselian

/-!
# Split valuation sequence for nonarchimedean local fields

The intrinsic value group of a nonarchimedean local field is isomorphic to `ℤᵐ⁰`.  Transporting
its valuation along that isomorphism and choosing a uniformizer gives a closed split sequence
of field units.  This is a local-class-field-theory prerequisite, not a reciprocity map or a
calculation of the local Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

universe u

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

/-- The valuation ring of a nonarchimedean local field is Henselian. -/
theorem nonarchimedeanLocalField_henselianRing
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : HenselianRing 𝒪[K] 𝓂[K] := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

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
