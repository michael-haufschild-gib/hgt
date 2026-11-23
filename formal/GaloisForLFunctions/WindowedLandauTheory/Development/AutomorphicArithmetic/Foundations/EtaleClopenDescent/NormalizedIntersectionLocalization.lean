import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveIntersectionLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FormDenominatorLocalization

/-! The normalized chart intersections and their regular forms are
obtained by inverting the coordinate product. -/

noncomputable section

open GaloisForLFunctions.HTGeometry GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F} {I : Finset (Fin (d + 1))} {i : Fin (d + 1)}

local notation "A" => rA k x {i}
local notation "C" => rA k x I
local notation "B" => integralClosure A E
local notation "T" => integralClosure C E
local notation "s" => chartDenominator k x I i

/-- Inclusion between normalized charts induced by restriction. -/
def normalizedIntersectionAlgebra (hi : i ∈ I) : Algebra B T := by
  letI := chartIntersectionAlgebra (k := k) (x := x) hi
  letI : IsScalarTower A C E := .of_algebraMap_eq fun _ => rfl
  exact (integralClosureLocalizationMap (R := A) (Rf := C) (E := E)).toAlgebra

theorem normalizedIntersection_tower (hi : i ∈ I) :
    letI := normalizedIntersectionAlgebra (k := k) (x := x) (E := E) hi
    IsScalarTower B T E :=
  .of_algebraMap_eq fun _ => rfl

/-- Normalization of the chart intersection localizes the original order. -/
theorem normalizedIntersection_isLocalization (h : IsPd k x) (hi : i ∈ I) :
    letI := normalizedIntersectionAlgebra (k := k) (x := x) (E := E) hi
    IsLocalization.Away (algebraMap A B s) T := by
  letI := chartIntersectionAlgebra (k := k) (x := x) hi
  letI : IsScalarTower A C E := .of_algebraMap_eq fun _ => rfl
  letI := normalizedIntersectionAlgebra (k := k) (x := x) (E := E) hi
  letI := normalizedIntersection_tower (k := k) (x := x) (E := E) hi
  letI : Algebra A T := (T).algebra'
  letI : IsScalarTower A B T := .of_algebraMap_eq fun _ => rfl
  letI := chartIntersection_isLocalization h hi
  letI : IsLocalization.Away (algebraMap A E s) E := IsLocalization.of_le_isUnit <| by
    rintro _ ⟨n, rfl⟩
    have hn : algebraMap A E s ≠ 0 :=
      (map_ne_zero _).mpr (chartDenominator_ne_zero h)
    exact (Ne.isUnit hn).pow _
  exact IsLocalization.Away.integralClosure (S := E) (Rf := C) (Sf := E) s

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
  rw [mem_omB_iff_pullback_range, mem_formRange_localization_iff (Submonoid.powers u)]
  constructor
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
