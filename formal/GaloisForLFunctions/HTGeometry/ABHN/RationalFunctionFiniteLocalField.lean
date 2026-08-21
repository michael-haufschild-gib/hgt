import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces
import GaloisForLFunctions.HTGeometry.ABHN.RationalFiniteLocalField
import GaloisForLFunctions.HTGeometry.MilnorKTameResidueFinite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# Finite places of rational function fields are local fields

This file proves the local-field package at every finite place of `F(t)`, for `F` finite.
The key missing transport is that completion preserves the finite residue field: density supplies
a pre-completion representative modulo the maximal ideal.  This is local input for the
nonarchimedean invariant map in Albert--Brauer--Hasse--Noether.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped Polynomial ValuativeRel WithZero WithZeroMulInt

universe u

/-- The integral ring of a finite `F(t)`-adic completion is canonically its valued-integer ring. -/
noncomputable def rationalFunctionAdicCompletionIntegersEquivValuedInteger
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    v.adicCompletionIntegers (RatFunc F) ≃+*
      (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer := by
  let h := HeightOneSpectrum.adicCompletionIntegers.integers (RatFunc F) v
  let f : v.adicCompletionIntegers (RatFunc F) →+*
      (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer :=
    (algebraMap (v.adicCompletionIntegers (RatFunc F)) (v.adicCompletion (RatFunc F))).codRestrict _
      (fun x => h.map_le_one x)
  refine RingEquiv.ofBijective f ?_
  constructor
  · intro x y hxy
    exact h.hom_inj (congrArg Subtype.val hxy)
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := h.exists_of_le_one hx
    exact ⟨y, Subtype.ext hy⟩

/-- The residue ring of every finite place of `F(t)` is finite. -/
theorem finite_rationalFunctionPlace_quotient
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    Finite (F[X] ⧸ v.asIdeal) := by
  classical
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal v.asIdeal).principal
  have hp0 : p ≠ 0 := by
    intro hp0
    apply v.ne_bot
    simp [hp, hp0]
  let q : F[X] := p * Polynomial.C p.leadingCoeff⁻¹
  have hq : q.Monic := Polynomial.monic_mul_leadingCoeff_inv hp0
  have hqv : Ideal.span ({q} : Set F[X]) = v.asIdeal := by
    calc
      Ideal.span ({q} : Set F[X]) = Ideal.span ({p} : Set F[X]) :=
        Ideal.span_singleton_mul_right_unit
          (Polynomial.isUnit_C.mpr (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp0)).isUnit) p
      _ = v.asIdeal := hp.symm
  letI : Module.Finite F (F[X] ⧸ Ideal.span ({q} : Set F[X])) := hq.finite_quotient
  haveI : Finite (F[X] ⧸ Ideal.span ({q} : Set F[X])) := Module.finite_of_finite F
  exact Finite.of_equiv (F[X] ⧸ Ideal.span ({q} : Set F[X]))
    (Ideal.quotientEquivAlgOfEq F hqv).toEquiv

noncomputable instance rationalFunctionFinitePlaceQuotientFinite
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    Finite (F[X] ⧸ v.asIdeal) :=
  finite_rationalFunctionPlace_quotient F v

/-- The completed valuation extends the finite-place valuation of `F(t)`. -/
noncomputable instance rationalFunctionAdicCompletionValuationHasExtension
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    (v.valuation (RatFunc F)).HasExtension
      (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰) where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    simp only [Valuation.comap_apply]
    change (v.valuation (RatFunc F)) x ≤ 1 ↔
      Valued.v (↑x : v.adicCompletion (RatFunc F)) ≤ 1
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x]

/-- Reduction from the pre-completion valuation ring onto the completed residue field is onto. -/
theorem rationalFunctionAdicCompletion_residueField_map_surjective
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    Function.Surjective <|
      IsLocalRing.ResidueField.map
        (algebraMap (v.valuation (RatFunc F)).integer
          (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective
    (R := (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer) z
  have hball : IsOpen {a : v.adicCompletion (RatFunc F) | Valued.v.restrict a < 1} :=
    Valued.isOpen_ball (v.adicCompletion (RatFunc F)) 1
  have hpreimage : IsOpen {a : v.adicCompletion (RatFunc F) |
      Valued.v.restrict (a - x) < 1} :=
    hball.preimage (continuous_id.sub continuous_const)
  obtain ⟨y, hy⟩ :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (RatFunc F) v |>.mem_nhds
      (hpreimage.mem_nhds (show Valued.v.restrict
        ((x : v.adicCompletion (RatFunc F)) - x) < 1 by simp))
  change Valued.v.restrict ((↑y : v.adicCompletion (RatFunc F)) - x) < 1 at hy
  have hy_lt : Valued.v ((↑y : v.adicCompletion (RatFunc F)) - x) < 1 := by
    exact (Valued.v).restrict_lt_one_iff.mp hy
  have hy_comp : Valued.v (↑y : v.adicCompletion (RatFunc F)) ≤ 1 := by
    calc
      Valued.v (↑y : v.adicCompletion (RatFunc F)) =
          Valued.v (x + ((↑y : v.adicCompletion (RatFunc F)) - x)) := by
        congr 1
        abel
      _ ≤ max (Valued.v (x : v.adicCompletion (RatFunc F)))
          (Valued.v ((↑y : v.adicCompletion (RatFunc F)) - x)) :=
        Valued.v.map_add _ _
      _ ≤ 1 := max_le x.2 (le_of_lt hy_lt)
  have hy_integer : (v.valuation (RatFunc F)) y ≤ 1 := by
    rw [← IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v y]
    exact hy_comp
  let y' : (v.valuation (RatFunc F)).integer := ⟨y, hy_integer⟩
  refine ⟨IsLocalRing.residue _ y', ?_⟩
  rw [IsLocalRing.ResidueField.map_residue]
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal]
  change ¬ IsUnit ((algebraMap (v.valuation (RatFunc F)).integer
    (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer y') - x)
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change Valued.v (
    ((algebraMap (v.valuation (RatFunc F)).integer
      (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer y' :
      (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer) :
        v.adicCompletion (RatFunc F)) - (x : v.adicCompletion (RatFunc F))) < 1
  rw [Valuation.HasExtension.val_algebraMap]
  change Valued.v ((algebraMap (RatFunc F) (v.adicCompletion (RatFunc F)) y) - x) < 1
  simpa only [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
    Algebra.algebraMap_self, RingHom.id_apply, Function.comp_apply] using hy_lt

/-- The residue field of every finite completion of `F(t)` is finite. -/
noncomputable instance rationalFunctionAdicCompletionFiniteResidueField
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    Finite (IsLocalRing.ResidueField
      ((Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer)) := by
  letI : Finite (F[X] ⧸ v.asIdeal) := finite_rationalFunctionPlace_quotient F v
  letI : Finite (IsLocalRing.ResidueField ((v.valuation (RatFunc F)).valuationSubring)) :=
    finite_residueField_valuationSubring (RatFunc F) v
  let e : (v.valuation (RatFunc F)).valuationSubring ≃+*
      (v.valuation (RatFunc F)).integer := RingEquiv.subringCongr rfl
  letI : Finite (IsLocalRing.ResidueField ((v.valuation (RatFunc F)).integer)) :=
    Finite.of_equiv (IsLocalRing.ResidueField ((v.valuation (RatFunc F)).valuationSubring))
      (IsLocalRing.ResidueField.mapEquiv e).toEquiv
  apply Finite.of_surjective
    (IsLocalRing.ResidueField.map
      (algebraMap (v.valuation (RatFunc F)).integer
        (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer))
  exact rationalFunctionAdicCompletion_residueField_map_surjective F v

/-- The completed valued-integer ring at a finite `F(t)`-place is a DVR. -/
noncomputable instance rationalFunctionAdicCompletionValuedIntegerDVR
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    IsDiscreteValuationRing
      (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).integer :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (rationalFunctionAdicCompletionIntegersEquivValuedInteger F v)

noncomputable instance rationalFunctionAdicCompletionRankOne
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 from one_lt_two)

noncomputable instance rationalFunctionAdicCompletionNormedField
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    NormedField (v.adicCompletion (RatFunc F)) :=
  Valued.toNormedField (v.adicCompletion (RatFunc F)) ℤᵐ⁰

/-- Complete DVR with finite residue field is proper, hence locally compact. -/
noncomputable instance rationalFunctionAdicCompletionProperSpace
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    ProperSpace (v.adicCompletion (RatFunc F)) :=
  Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

noncomputable instance rationalFunctionAdicCompletionValuativeRel
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    ValuativeRel (v.adicCompletion (RatFunc F)) :=
  .ofValuation (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰)

instance rationalFunctionAdicCompletionValuationCompatible
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    (Valued.v : Valuation (v.adicCompletion (RatFunc F)) ℤᵐ⁰).Compatible :=
  .ofValuation _

/-- Every finite completion of `F(t)` is a nonarchimedean local field. -/
noncomputable instance rationalFunctionAdicCompletionIsNonarchimedeanLocalField
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    IsNonarchimedeanLocalField (v.adicCompletion (RatFunc F)) :=
  isNonarchimedeanLocalField_of_valued_of_locallyCompact
    (v.adicCompletion (RatFunc F)) ℤᵐ⁰

/-- The finite branch of the packaged completion retains its adic topology. -/
noncomputable instance rationalFunctionFinitePlaceCompletionTopologicalSpace
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    TopologicalSpace (rationalFunctionCompletion F (.finite v)) := by
  change TopologicalSpace (v.adicCompletion (RatFunc F))
  infer_instance

/-- The finite branch of the packaged completion retains its adic uniform structure. -/
noncomputable instance rationalFunctionFinitePlaceCompletionUniformSpace
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    UniformSpace (rationalFunctionCompletion F (.finite v)) := by
  change UniformSpace (v.adicCompletion (RatFunc F))
  infer_instance

noncomputable instance rationalFunctionFinitePlaceCompletionIsUniformAddGroup
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    IsUniformAddGroup (rationalFunctionCompletion F (.finite v)) := by
  change IsUniformAddGroup (v.adicCompletion (RatFunc F))
  infer_instance

noncomputable instance rationalFunctionFinitePlaceCompletionIsTopologicalAddGroup
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    IsTopologicalAddGroup (rationalFunctionCompletion F (.finite v)) := by
  change IsTopologicalAddGroup (v.adicCompletion (RatFunc F))
  infer_instance

/-- The packaged finite-place completion inherits its valuative relation. -/
noncomputable instance rationalFunctionFinitePlaceCompletionValuativeRel
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    ValuativeRel (rationalFunctionCompletion F (.finite v)) := by
  change ValuativeRel (v.adicCompletion (RatFunc F))
  infer_instance

/-- Every packaged finite completion of `F(t)` is a nonarchimedean local field. -/
noncomputable instance rationalFunctionFinitePlaceCompletionIsNonarchimedeanLocalField
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    IsNonarchimedeanLocalField (rationalFunctionCompletion F (.finite v)) := by
  change IsNonarchimedeanLocalField (v.adicCompletion (RatFunc F))
  infer_instance

noncomputable instance rationalFunctionFinitePlaceCompletionIsDiscreteValuationRing
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    IsDiscreteValuationRing 𝒪[rationalFunctionCompletion F (.finite v)] := by
  infer_instance

noncomputable instance rationalFunctionFinitePlaceCompletionFiniteResidueField
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    Finite 𝓀[rationalFunctionCompletion F (.finite v)] := by
  infer_instance

/-- The valued-integer ring of every packaged finite completion of `F(t)` is adically complete. -/
theorem rationalFunctionFinitePlaceCompletion_isAdicComplete
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    IsAdicComplete 𝓂[rationalFunctionCompletion F (.finite v)]
      𝒪[rationalFunctionCompletion F (.finite v)] := by
  letI := IsTopologicalAddGroup.rightUniformSpace (rationalFunctionCompletion F (.finite v))
  letI := isUniformAddGroup_of_addCommGroup
    (G := rationalFunctionCompletion F (.finite v))
  infer_instance

/-- The finite local rings of `F(t)` support Hensel lifting. -/
theorem rationalFunctionFinitePlaceCompletion_henselianRing
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    HenselianRing 𝒪[rationalFunctionCompletion F (.finite v)]
      𝓂[rationalFunctionCompletion F (.finite v)] := by
  letI : IsAdicComplete 𝓂[rationalFunctionCompletion F (.finite v)]
      𝒪[rationalFunctionCompletion F (.finite v)] :=
    rationalFunctionFinitePlaceCompletion_isAdicComplete F v
  infer_instance

/-- The finite local rings of `F(t)` are henselian local rings. -/
theorem rationalFunctionFinitePlaceCompletion_henselianLocalRing
    (F : Type u) [Field F] [Finite F] (v : HeightOneSpectrum F[X]) :
    HenselianLocalRing 𝒪[rationalFunctionCompletion F (.finite v)] := by
  letI : HenselianRing 𝒪[rationalFunctionCompletion F (.finite v)]
      𝓂[rationalFunctionCompletion F (.finite v)] :=
    rationalFunctionFinitePlaceCompletion_henselianRing F v
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ ha₀ hderivative
  exact HenselianRing.is_henselian f hf a₀ ha₀ (hderivative.map (Ideal.Quotient.mk _))

end GaloisForLFunctions.HTGeometry.ABHN
