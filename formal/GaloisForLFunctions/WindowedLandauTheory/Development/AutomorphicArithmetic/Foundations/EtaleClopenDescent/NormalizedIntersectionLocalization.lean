import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveIntersectionLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FormDenominatorLocalization

/-! The normalized chart intersections and their regular forms are
obtained by inverting the coordinate product. -/

noncomputable section

open GaloisForLFunctions.HTGeometry GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

section IntegralClosure

variable {A₁ C₁ E₁ : Type} [CommRing A₁] [CommRing C₁]
  [Field E₁] [Algebra A₁ C₁] [Algebra A₁ E₁] [Algebra C₁ E₁] [IsScalarTower A₁ C₁ E₁]

private abbrev integralClosureInclusionAlgebra :
    Algebra (integralClosure A₁ E₁) (integralClosure C₁ E₁) :=
  (integralClosureLocalizationMap (R := A₁) (Rf := C₁) (E := E₁)).toAlgebra

private theorem integralClosureInclusion_tower :
    letI := integralClosureInclusionAlgebra (A₁ := A₁) (C₁ := C₁) (E₁ := E₁)
    IsScalarTower (integralClosure A₁ E₁) (integralClosure C₁ E₁) E₁ := by
  letI := integralClosureInclusionAlgebra (A₁ := A₁) (C₁ := C₁) (E₁ := E₁)
  exact .of_algebraMap_eq fun _ => rfl

private theorem integralClosure_isLocalization_away (u : A₁) [IsLocalization.Away u C₁]
    (hu : algebraMap A₁ E₁ u ≠ 0) :
    letI := integralClosureInclusionAlgebra (A₁ := A₁) (C₁ := C₁) (E₁ := E₁)
    IsLocalization.Away (algebraMap A₁ (integralClosure A₁ E₁) u) (integralClosure C₁ E₁) := by
  let B₁ := integralClosure A₁ E₁
  let T₁ := integralClosure C₁ E₁
  letI : Algebra B₁ T₁ := integralClosureInclusionAlgebra (A₁ := A₁) (C₁ := C₁) (E₁ := E₁)
  letI : IsScalarTower B₁ T₁ E₁ := integralClosureInclusion_tower (A₁ := A₁) (C₁ := C₁)
  letI : Algebra A₁ T₁ := T₁.algebra'
  letI : IsScalarTower A₁ B₁ T₁ := .of_algebraMap_eq fun a =>
    Subtype.ext (IsScalarTower.algebraMap_apply A₁ B₁ E₁ a)
  letI : IsLocalization.Away (algebraMap A₁ E₁ u) E₁ := IsLocalization.of_le_isUnit <| by
    rintro _ ⟨n, rfl⟩
    exact (Ne.isUnit hu).pow n
  exact IsLocalization.Away.integralClosure (S := E₁) (Rf := C₁) (Sf := E₁) u

end IntegralClosure

variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F] [Algebra F E]
  {d : ℕ} {x : Fin (d + 1) → F} {I : Finset (Fin (d + 1))} {i : Fin (d + 1)}

local notation "A" => rA k x (Singleton.singleton i)
local notation "C" => rA k x I
local notation "B" => integralClosure A E
local notation "T" => integralClosure C E
local notation "s" => chartDenominator k x I i

/-- Inclusion between normalized charts induced by restriction. -/
abbrev normalizedIntersectionAlgebra (hi : i ∈ I) : Algebra B T := by
  letI := chartIntersectionAlgebra (k := k) (x := x) hi
  letI := chartIntersection_tower (k := k) (x := x) hi
  letI : IsScalarTower A C E := IsScalarTower.to₁₂₄ A C F E
  exact integralClosureInclusionAlgebra (A₁ := A) (C₁ := C) (E₁ := E)

theorem normalizedIntersection_tower (hi : i ∈ I) :
    letI := normalizedIntersectionAlgebra (k := k) (x := x) (E := E) hi
    IsScalarTower B T E := by
  letI := chartIntersectionAlgebra (k := k) (x := x) hi
  letI := chartIntersection_tower (k := k) (x := x) hi
  letI : IsScalarTower A C E := IsScalarTower.to₁₂₄ A C F E
  exact integralClosureInclusion_tower (A₁ := A) (C₁ := C) (E₁ := E)

/-- Normalization of the chart intersection localizes the original order. -/
theorem normalizedIntersection_isLocalization (h : IsPd k x) (hi : i ∈ I) :
    letI := normalizedIntersectionAlgebra (k := k) (x := x) (E := E) hi
    IsLocalization.Away (algebraMap A B s) T := by
  letI := chartIntersectionAlgebra (k := k) (x := x) hi
  letI := chartIntersection_tower (k := k) (x := x) hi
  letI : IsScalarTower A C E := IsScalarTower.to₁₂₄ A C F E
  letI := chartIntersection_isLocalization h hi
  have hn : algebraMap A E s ≠ 0 := by
    change algebraMap F E (s : F) ≠ 0
    exact (map_ne_zero _).mpr (chartDenominator_ne_zero h)
  exact integralClosure_isLocalization_away (C₁ := C) (E₁ := E) s hn

variable [Algebra k E] [IsScalarTower k F E]

/-- A rational form is regular on the intersection exactly when a
power of the coordinate product makes it regular on the single chart. -/
theorem mem_omB_chartIntersection_iff (h : IsPd k x) (hi : i ∈ I) {p : ℕ}
    (w : ExteriorDifferentials k E p) :
    (w : DR k E) ∈ omB k E (rB k E x I) p ↔
      ∃ n : ℕ, algebraMap F E (s : F) ^ n • (w : DR k E) ∈
        omB k E (rB k E x {i}) p := by
  let Bk := rB k E x {i}
  let Tk := rB k E x I
  letI : Algebra Bk Tk := normalizedIntersectionAlgebra (k := k) (x := x) (E := E) hi
  letI : IsScalarTower Bk Tk E := normalizedIntersection_tower (k := k) (x := x) (E := E) hi
  letI : IsScalarTower k Bk Tk := .of_algebraMap_eq fun _ => rfl
  let u : Bk := algebraMap A B s
  letI : IsLocalization.Away u Tk := normalizedIntersection_isLocalization (E := E) h hi
  have hloc : w ∈ LinearMap.range (algebraFormPullback k Tk E p) ↔
      ∃ a : Submonoid.powers u, (a : Bk) • w ∈ LinearMap.range (algebraFormPullback k Bk E p) :=
    mem_formRange_localization_iff (Submonoid.powers u) w
  refine (mem_omB_iff_pullback_range Tk w).trans (hloc.trans ⟨?_, ?_⟩)
  · rintro ⟨a, ha⟩
    obtain ⟨n, hn⟩ := a.property
    refine ⟨n, ?_⟩
    have hw := (mem_omB_iff_pullback_range Bk ((a : Bk) • w)).mpr ha
    change (((a : Bk) : E) • (w : DR k E)) ∈ omB k E Bk p at hw
    rwa [← hn, Subalgebra.coe_pow] at hw
  · rintro ⟨n, hn⟩
    refine ⟨⟨u ^ n, ⟨n, rfl⟩⟩, (mem_omB_iff_pullback_range Bk ((u ^ n) • w)).mp ?_⟩
    change ((u ^ n : Bk) : E) • (w : DR k E) ∈ omB k E Bk p
    rwa [Subalgebra.coe_pow]

end GlobalTheory.PD
