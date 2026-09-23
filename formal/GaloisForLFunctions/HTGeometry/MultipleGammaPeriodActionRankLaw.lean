import GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionLaw
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# Multiple-Gamma marked period rank and excess law

This module formalizes the literal rationalized marked quotient
`Q tensor_Z (Z^(3 : ℕ) / ker p)`, the real span of the period image, marked excess, stabilizer rank,
finite/boundary depth ledger, and the general integral period-action conservation law.
-/

open Set Complex
open scoped TensorProduct

namespace GaloisForLFunctions
namespace HTGeometry

noncomputable section

/-! ## Literal marked quotient and real period span -/

/-- Rationalized effective marked source `Q tensor_Z (Z^(3 : ℕ) / ker p)`. -/
abbrev markedRationalizedSource (p : MultipleGammaPeriodSource →+ ℂ) : Type :=
  ℚ ⊗[ℤ] (MultipleGammaPeriodSource ⧸ p.ker)

/-- Real span of the realized marked period image. -/
abbrev markedPeriodRealSpan (p : MultipleGammaPeriodSource →+ ℂ) : Submodule ℝ ℂ :=
  Submodule.span ℝ (Set.range p)

/-- Literal marked period excess: rationalized effective-source dimension minus real-span
dimension. -/
noncomputable def markedPeriodExcess (p : MultipleGammaPeriodSource →+ ℂ) : ℕ :=
  Module.finrank ℚ (markedRationalizedSource p) - Module.finrank ℝ (markedPeriodRealSpan p)

/-- Finite effective marked source is rationally `Q^(3 : ℕ)`. -/
noncomputable def finiteMultipleGammaRationalizedSourceEquiv (m : ℕ+) :
    markedRationalizedSource (finiteMultipleGammaPeriodMap m) ≃ₗ[ℚ] (Fin 3 → ℚ) :=
  (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl ℚ ℚ)
    (((QuotientAddGroup.quotientAddEquivOfEq (finiteMultipleGammaPeriodMap_ker m)).trans
      QuotientAddGroup.quotientBot).toIntLinearEquiv)).trans
        (Algebra.TensorProduct.equivPiOfFiniteBasis ℚ (Pi.basisFun ℤ (Fin 3)))

/-- Finite rationalized effective marked-source dimension is three. -/
theorem finiteMultipleGammaRationalizedSource_finrank (m : ℕ+) :
    Module.finrank ℚ (markedRationalizedSource (finiteMultipleGammaPeriodMap m)) = 3 := by
  rw [(finiteMultipleGammaRationalizedSourceEquiv m).finrank_eq]
  simp

/-- Integral effective boundary coordinates `(a,b,c) mapsto (a,b+2c)`. -/
def boundaryMultipleGammaEffectiveCoordinates :
    MultipleGammaPeriodSource →+ (Fin 2 → ℤ) where
  toFun n := ![n 0, n 1 + 2 * n 2]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring

/-- Effective boundary coordinates are onto `Z^(2 : ℕ)`. -/
theorem boundaryMultipleGammaEffectiveCoordinates_surjective :
    Function.Surjective boundaryMultipleGammaEffectiveCoordinates := by
  intro y
  refine ⟨![y 0, y 1, 0], ?_⟩
  funext i
  fin_cases i <;> simp [boundaryMultipleGammaEffectiveCoordinates]

/-- Effective-coordinate kernel is exactly the boundary period-map kernel. -/
theorem boundaryMultipleGammaEffectiveCoordinates_ker :
    boundaryMultipleGammaEffectiveCoordinates.ker = boundaryMultipleGammaPeriodMap.ker := by
  rw [boundaryMultipleGammaPeriodMap_ker]
  ext n
  constructor
  · intro hn
    rw [AddMonoidHom.mem_ker] at hn
    have h0 := congrFun hn 0
    have h1 := congrFun hn 1
    simp [boundaryMultipleGammaEffectiveCoordinates] at h0 h1
    refine ⟨n 2, ?_⟩
    funext i
    fin_cases i
    · simp [boundaryMultipleGammaRelation, h0]
    · simp [boundaryMultipleGammaRelation]
      omega
    · simp [boundaryMultipleGammaRelation]
  · rintro ⟨k, rfl⟩
    rw [AddMonoidHom.mem_ker, map_zsmul]
    simp [boundaryMultipleGammaEffectiveCoordinates, boundaryMultipleGammaRelation]

/-- Boundary effective marked source is rationally `Q^(2 : ℕ)`. -/
noncomputable def boundaryMultipleGammaRationalizedSourceEquiv :
    markedRationalizedSource boundaryMultipleGammaPeriodMap ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl ℚ ℚ)
    (((QuotientAddGroup.quotientAddEquivOfEq
      boundaryMultipleGammaEffectiveCoordinates_ker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        boundaryMultipleGammaEffectiveCoordinates
        boundaryMultipleGammaEffectiveCoordinates_surjective)).toIntLinearEquiv)).trans
          (Algebra.TensorProduct.equivPiOfFiniteBasis ℚ (Pi.basisFun ℤ (Fin 2)))

/-- Boundary rationalized effective marked-source dimension is two. -/
theorem boundaryMultipleGammaRationalizedSource_finrank :
    Module.finrank ℚ (markedRationalizedSource boundaryMultipleGammaPeriodMap) = 2 := by
  rw [boundaryMultipleGammaRationalizedSourceEquiv.finrank_eq]
  simp

/-- Any marked period map containing the standard real basis `1,i` spans all of `C` over `R`. -/
theorem markedPeriodRealSpan_eq_top (p : MultipleGammaPeriodSource →+ ℂ)
    (h1 : p ![1, 0, 0] = 1) (hI : p ![0, 1, 0] = Complex.I) :
    markedPeriodRealSpan p = ⊤ := by
  let b : Module.Basis (Fin 2) ℝ ℂ := Complex.basisOneI
  apply top_unique
  rw [← b.span_eq]
  exact Submodule.span_mono (by
    rintro z ⟨i, rfl⟩
    fin_cases i
    · refine ⟨![1, 0, 0], ?_⟩
      simpa [b, Complex.basisOneI] using h1
    · refine ⟨![0, 1, 0], ?_⟩
      simpa [b, Complex.basisOneI] using hI)

/-- Finite marked periods span all of `C` over `R`. -/
theorem finiteMultipleGammaPeriodRealSpan_eq_top (m : ℕ+) :
    markedPeriodRealSpan (finiteMultipleGammaPeriodMap m) = ⊤ := by
  apply markedPeriodRealSpan_eq_top
  · simp [finiteMultipleGammaPeriodMap_apply]
  · simp [finiteMultipleGammaPeriodMap_apply]

/-- Boundary marked periods span all of `C` over `R`. -/
theorem boundaryMultipleGammaPeriodRealSpan_eq_top :
    markedPeriodRealSpan boundaryMultipleGammaPeriodMap = ⊤ := by
  apply markedPeriodRealSpan_eq_top
  · simp [boundaryMultipleGammaPeriodMap_apply]
  · simp [boundaryMultipleGammaPeriodMap_apply]

/-- Finite marked period real-span dimension is two. -/
theorem finiteMultipleGammaPeriodRealSpan_finrank (m : ℕ+) :
    Module.finrank ℝ (markedPeriodRealSpan (finiteMultipleGammaPeriodMap m)) = 2 := by
  rw [finiteMultipleGammaPeriodRealSpan_eq_top]
  simp [Complex.finrank_real_complex]

/-- Boundary marked period real-span dimension is two. -/
theorem boundaryMultipleGammaPeriodRealSpan_finrank :
    Module.finrank ℝ (markedPeriodRealSpan boundaryMultipleGammaPeriodMap) = 2 := by
  rw [boundaryMultipleGammaPeriodRealSpan_eq_top]
  simp [Complex.finrank_real_complex]

/-- Exact finite marked excess `3 - 2 = 1`. -/
theorem finiteMultipleGammaMarkedPeriodExcess_eq_one (m : ℕ+) :
    markedPeriodExcess (finiteMultipleGammaPeriodMap m) = 1 := by
  rw [markedPeriodExcess, finiteMultipleGammaRationalizedSource_finrank,
    finiteMultipleGammaPeriodRealSpan_finrank]

/-- Exact boundary marked excess `2 - 2 = 0`. -/
theorem boundaryMultipleGammaMarkedPeriodExcess_eq_zero :
    markedPeriodExcess boundaryMultipleGammaPeriodMap = 0 := by
  rw [markedPeriodExcess, boundaryMultipleGammaRationalizedSource_finrank,
    boundaryMultipleGammaPeriodRealSpan_finrank]

/-- Independent finite DA depth equals literal marked period excess. -/
theorem finiteMultipleGammaDADepth_eq_markedPeriodExcess (m : ℕ+) :
    multipleEllipticGammaTransverseDADepth
        (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) =
      markedPeriodExcess (finiteMultipleGammaPeriodMap m) := by
  rw [finiteMultipleGammaTransverseDADepth,
    finiteMultipleGammaMarkedPeriodExcess_eq_one]

/-- Independent boundary DA depth equals literal marked period excess. -/
theorem boundaryMultipleGammaDADepth_eq_markedPeriodExcess :
    multipleEllipticGammaTransverseDADepth
        boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos =
      markedPeriodExcess boundaryMultipleGammaPeriodMap := by
  rw [boundaryMultipleGammaTransverseDADepth,
    boundaryMultipleGammaMarkedPeriodExcess_eq_zero]

/-! ## Literal stabilizer ranks and the cofinal ledger -/

/-- Rationalized object stabilizer. -/
abbrev markedStabilizerRationalization
    (p : MultipleGammaPeriodSource →+ ℂ) (z : ℂ) : Type :=
  ℚ ⊗[ℤ] markedTranslationStabilizer p z

/-- Integral stabilizer rank, computed after rationalization. -/
noncomputable def markedStabilizerRank
    (p : MultipleGammaPeriodSource →+ ℂ) (z : ℂ) : ℕ :=
  Module.finrank ℚ (markedStabilizerRationalization p z)

/-- Finite marked action has stabilizer rank zero at every object. -/
theorem finiteMultipleGammaStabilizerRank_eq_zero (m : ℕ+) (z : ℂ) :
    markedStabilizerRank (finiteMultipleGammaPeriodMap m) z = 0 := by
  have hstab : markedTranslationStabilizer (finiteMultipleGammaPeriodMap m) z = ⊥ := by
    rw [markedTranslationStabilizer_eq_ker, finiteMultipleGammaPeriodMap_ker]
  rw [markedStabilizerRank]
  haveI : Subsingleton (markedTranslationStabilizer (finiteMultipleGammaPeriodMap m) z) := by
    rw [hstab]
    infer_instance
  haveI : Subsingleton
      (markedStabilizerRationalization (finiteMultipleGammaPeriodMap m) z) := inferInstance
  exact Module.finrank_zero_of_subsingleton

/-- The primitive boundary relation identifies its cyclic subgroup additively with `Z`. -/
noncomputable def boundaryMultipleGammaRelationZEquiv :
    (AddSubgroup.zmultiples boundaryMultipleGammaRelation : Type) ≃+ ℤ where
  toFun x := x.1 2
  invFun k := ⟨k • boundaryMultipleGammaRelation, ⟨k, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨x, k, rfl⟩
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [boundaryMultipleGammaRelation]
  right_inv k := by simp [boundaryMultipleGammaRelation]
  map_add' x y := by simp

/-- Additive equivalence induced by equality of two additive subgroups. -/
def addSubgroupAddEquivOfEq {G : Type*} [AddGroup G]
    {A B : AddSubgroup G} (h : A = B) : A ≃+ B := by
  subst h
  exact AddEquiv.refl _

/-- Every boundary object stabilizer is additively `Z`. -/
noncomputable def boundaryMultipleGammaStabilizerZEquiv (z : ℂ) :
    markedTranslationStabilizer boundaryMultipleGammaPeriodMap z ≃+ ℤ :=
  ((addSubgroupAddEquivOfEq (markedTranslationStabilizer_eq_ker
      boundaryMultipleGammaPeriodMap z)).trans
    (addSubgroupAddEquivOfEq boundaryMultipleGammaPeriodMap_ker)).trans
      boundaryMultipleGammaRelationZEquiv

/-- Rationalized boundary stabilizer is linearly `Q`. -/
noncomputable def boundaryMultipleGammaStabilizerRationalizationEquiv (z : ℂ) :
    markedStabilizerRationalization boundaryMultipleGammaPeriodMap z ≃ₗ[ℚ] ℚ :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ ℚ)
    (boundaryMultipleGammaStabilizerZEquiv z).toIntLinearEquiv).trans
      (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ)

/-- Boundary marked action has stabilizer rank one at every object. -/
theorem boundaryMultipleGammaStabilizerRank_eq_one (z : ℂ) :
    markedStabilizerRank boundaryMultipleGammaPeriodMap z = 1 := by
  rw [markedStabilizerRank,
    (boundaryMultipleGammaStabilizerRationalizationEquiv z).finrank_eq]
  simp

/-- Finite cofinal law-rank complementarity. -/
theorem finiteMultipleGammaDADepth_add_stabilizerRank (m : ℕ+) (z : ℂ) :
    multipleEllipticGammaTransverseDADepth
          (finiteMultipleGammaFunctionPeriods m) (finiteMultipleGammaFunctionPeriods_im_pos m) +
        markedStabilizerRank (finiteMultipleGammaPeriodMap m) z =
      1 := by
  rw [finiteMultipleGammaTransverseDADepth,
    finiteMultipleGammaStabilizerRank_eq_zero]

/-- Boundary cofinal law-rank complementarity. -/
theorem boundaryMultipleGammaDADepth_add_stabilizerRank (z : ℂ) :
    multipleEllipticGammaTransverseDADepth
          boundaryMultipleGammaFunctionPeriods boundaryMultipleGammaFunctionPeriods_im_pos +
        markedStabilizerRank boundaryMultipleGammaPeriodMap z =
      1 := by
  rw [boundaryMultipleGammaTransverseDADepth,
    boundaryMultipleGammaStabilizerRank_eq_one]

/-! ## General period-action conservation law -/

/-- Free marked source with `N` integral coordinates. -/
abbrev IntegralPeriodSource (N : ℕ) := Fin N → ℤ

/-- Integral image rank, represented canonically as rank of source modulo kernel. -/
noncomputable def integralPeriodImageRank {N : ℕ} {V : Type*} [AddCommGroup V]
    (p : IntegralPeriodSource N →+ V) : ℕ :=
  Module.finrank ℤ (IntegralPeriodSource N ⧸ p.ker.toIntSubmodule)

/-- Integral kernel rank. -/
noncomputable def integralPeriodKernelRank {N : ℕ} {V : Type*} [AddCommGroup V]
    (p : IntegralPeriodSource N →+ V) : ℕ :=
  Module.finrank ℤ p.ker.toIntSubmodule

/-- General integral period excess relative to real-span dimension `d`, valued in `Z` so the
conservation identity remains unconditional even before proving nonnegativity. -/
noncomputable def integralPeriodExcess {N : ℕ} {V : Type*} [AddCommGroup V]
    (p : IntegralPeriodSource N →+ V) (d : ℕ) : ℤ :=
  (integralPeriodImageRank p : ℤ) - d

/-- Exact integral rank-nullity for every marked period presentation. -/
theorem integralPeriodRankNullity {N : ℕ} {V : Type*} [AddCommGroup V]
    (p : IntegralPeriodSource N →+ V) :
    integralPeriodImageRank p + integralPeriodKernelRank p = N := by
  have h := p.ker.toIntSubmodule.finrank_quotient_add_finrank
  unfold integralPeriodImageRank integralPeriodKernelRank
  convert h using 1
  · rfl
  · simpa [IntegralPeriodSource] using
      (Module.finrank_fintype_fun_eq_card ℤ (η := Fin N)).symm

/-- **General period-action conservation law.** For every integral presentation and every target
span dimension `d`, excess plus integral isotropy rank is `N-d`. -/
theorem periodActionConservationLaw {N : ℕ} {V : Type*} [AddCommGroup V]
    (p : IntegralPeriodSource N →+ V) (d : ℕ) :
    integralPeriodExcess p d + integralPeriodKernelRank p = (N : ℤ) - d := by
  have h := integralPeriodRankNullity p
  rw [integralPeriodExcess]
  omega

/-- Conservation equation is invariant under every integral source-basis automorphism. -/
theorem periodActionConservation_sourceBasisInvariant
    {N : ℕ} {V : Type*} [AddCommGroup V]
    (p : IntegralPeriodSource N →+ V)
    (e : IntegralPeriodSource N ≃+ IntegralPeriodSource N) (d : ℕ) :
    integralPeriodExcess (p.comp e.toAddMonoidHom) d +
        integralPeriodKernelRank (p.comp e.toAddMonoidHom) =
      integralPeriodExcess p d + integralPeriodKernelRank p := by
  rw [periodActionConservationLaw, periodActionConservationLaw]

/-- Conservation equation is invariant under every invertible real-linear target coordinate
change. -/
theorem periodActionConservation_targetCoordinatesInvariant
    {N : ℕ} {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℝ V] [Module ℝ W]
    (p : IntegralPeriodSource N →+ V) (e : V ≃ₗ[ℝ] W) (d : ℕ) :
    integralPeriodExcess (e.toAddEquiv.toAddMonoidHom.comp p) d +
        integralPeriodKernelRank (e.toAddEquiv.toAddMonoidHom.comp p) =
      integralPeriodExcess p d + integralPeriodKernelRank p := by
  rw [periodActionConservationLaw, periodActionConservationLaw]

end

end HTGeometry
end GaloisForLFunctions
