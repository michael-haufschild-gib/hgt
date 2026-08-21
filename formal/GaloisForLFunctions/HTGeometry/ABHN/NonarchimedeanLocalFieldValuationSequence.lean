/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.LocalValuationSequence
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Split valuation sequence for nonarchimedean local fields

The intrinsic value group of a nonarchimedean local field is isomorphic to `ℤᵐ⁰`.  Transporting
its valuation along that isomorphism and choosing a uniformizer gives a closed split sequence
of field units.  This is a local-class-field-theory prerequisite, not a reciprocity map or a
calculation of the local Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open Polynomial
open scoped ValuativeRel WithZero WithZeroMulInt

attribute [local instance] Ideal.Quotient.field

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
residue extension to a concrete local algebra; passing from this algebra to an unramified field
extension is a separate fraction-field step. -/
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

/-- Every monic residue polynomial admits a same-degree monic lift whose root algebra is finite
and free over the valuation ring and whose reduction is the prescribed residue root algebra.
This is the algebra-presentation part of an unramified-extension construction; showing that this
algebra is the valuation ring of a field extension still requires the finite étale lifting bridge. -/
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
extension; promoting it to an unramified extension of `K` requires the still-missing lifting
theorem for finite étale algebras over complete valuation rings. -/
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
