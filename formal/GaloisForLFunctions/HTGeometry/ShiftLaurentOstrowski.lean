import GaloisForLFunctions.HTGeometry.RatFuncLaurentDifferential
import GaloisForLFunctions.HTGeometry.AutomorphismFamilyOstrowski

/-!
# The one-shift telescoping alternative in the formal Laurent field

The differential Ostrowski criterion applied to the translation of `ℂ((s⁻¹))` says that an
additive primitive with rational increment is either differentially transcendental over `ℂ(s)` or
carries a constant telescoping relation, which forces a constant-coefficient inhomogeneous
differential equation with rational right-hand side.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

local instance : Differential (LaurentSeries ℂ) := laurentSDifferential
local instance ratFuncIntAlgebra' : Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _
local instance : Differential (RatFunc ℂ) := ratFuncSDifferential
local instance ratLaurentAlgebra : Algebra (RatFunc ℂ) (LaurentSeries ℂ) :=
  ratToLaurent.toAlgebra

theorem algebraMap_ratLaurent (r : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) (LaurentSeries ℂ) r = ratToLaurent r := rfl

local instance towerCRatLaurent : IsScalarTower ℂ (RatFunc ℂ) (LaurentSeries ℂ) where
  smul_assoc c r x := by
    show ratToLaurent (c • r) * x = c • (ratToLaurent r * x)
    rw [RatFunc.smul_eq_C_mul, map_mul, ratToLaurent_C, ← HahnSeries.C_mul_eq_smul,
      laurentCHom_eq_single, HahnSeries.C_apply, mul_assoc]

local instance towerCRatLaurentAlg :
    @IsScalarTower ℂ (RatFunc ℂ) (LaurentSeries ℂ) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun c : ℂ => by
    rw [algebraMap_ratLaurent, RatFunc.algebraMap_eq_C, ratToLaurent_C, laurentCHom_eq_single,
      LaurentSeries.algebraMap_apply, HahnSeries.C_apply]

local instance : DifferentialAlgebra (RatFunc ℂ) (LaurentSeries ℂ) :=
  ⟨fun r => by rw [algebraMap_ratLaurent, algebraMap_ratLaurent, deriv_ratToLaurent]⟩

/-! ### The Ostrowski alternative for the translation -/

theorem shiftLaurent_algebraMap_complex (h c : ℂ) :
    shiftLaurent h (algebraMap ℂ (LaurentSeries ℂ) c) = algebraMap ℂ (LaurentSeries ℂ) c := by
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, ← laurentCHom_eq_single,
    shiftLaurent_laurentCHom]

theorem exists_algebraMap_complex_of_shiftLaurent_eq {h : ℂ} (hh : h ≠ 0) {z : LaurentSeries ℂ}
    (hz : shiftLaurent h z = z) : ∃ c : ℂ, algebraMap ℂ (LaurentSeries ℂ) c = z := by
  obtain ⟨c, hc⟩ := exists_laurentC_of_shiftLaurent_eq hh hz
  refine ⟨c, ?_⟩
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, ← laurentCHom_eq_single]
  exact hc

/-- **The Ostrowski alternative.**  An additive primitive of a rational increment is
differentially transcendental over `ℂ(s)` unless its increment carries a constant telescoping
relation. -/
theorem hypertranscendental_of_no_telescoper {h : ℂ} (hh : h ≠ 0) {f : LaurentSeries ℂ}
    {r : RatFunc ℂ} (hfr : shiftLaurent h f = f + ratToLaurent r)
    (hnot : ∀ c : (Unit × ℕ) →₀ ℂ, c ≠ 0 → ∀ k : RatFunc ℂ,
      ratShiftEquivBy h k - k ≠ Finsupp.linearCombination (RatFunc ℂ)
        (fun p : Unit × ℕ => differentialJet p.2 r)
        (Finsupp.mapRange (algebraMap ℂ (RatFunc ℂ)) (map_zero _) c)) :
    HypertranscendentalOver (RatFunc ℂ) f := by
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton]
  refine GaloisForLFunctions.automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping
    (I := Unit) (kappa := Unit) (C := ℂ) (K := RatFunc ℂ) (L := LaurentSeries ℂ)
    (fun _ => ratShiftEquivBy h) (fun _ => shiftLaurent h)
    (fun _ k => by
      rw [algebraMap_ratLaurent, algebraMap_ratLaurent]
      exact shiftLaurent_ratToLaurent h k)
    (fun _ x => shiftLaurent_deriv h x)
    (fun _ c => shiftLaurent_algebraMap_complex h c)
    (fun z hz => exists_algebraMap_complex_of_shiftLaurent_eq hh (hz ()))
    (fun _ => f) (fun _ _ => r)
    (fun _ _ => by
      rw [algebraMap_ratLaurent]
      exact hfr)
    ?_
  intro c hc0 k
  exact ⟨(), hnot c hc0 k⟩

/-! ### From a telescoper to a constant-coefficient equation -/

theorem linearCombination_mapRange_eq_sum {R : Type*} [CommRing R] [Algebra ℂ R]
    (hinj : Function.Injective (algebraMap ℂ R))
    (c : (Unit × ℕ) →₀ ℂ) (v : (Unit × ℕ) → R) :
    Finsupp.linearCombination R v
        (Finsupp.mapRange (algebraMap ℂ R) (map_zero _) c)
      = ∑ p ∈ c.support, algebraMap ℂ R (c p) * v p := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [Finsupp.support_mapRange_of_injective (map_zero _) c hinj]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.mapRange_apply, smul_eq_mul]

/-- **The telescoping branch.**  A constant telescoping relation for the increment turns the
primitive into a solution of a constant-coefficient inhomogeneous equation with rational
right-hand side. -/
theorem exists_ode_of_telescoper {h : ℂ} (hh : h ≠ 0) {f : LaurentSeries ℂ} {r : RatFunc ℂ}
    (hfr : shiftLaurent h f = f + ratToLaurent r)
    {c : (Unit × ℕ) →₀ ℂ} {k : RatFunc ℂ}
    (htel : ratShiftBy h k - k
      = ∑ p ∈ c.support, algebraMap ℂ (RatFunc ℂ) (c p) * differentialJet p.2 r) :
    ∃ g : RatFunc ℂ,
      ∑ p ∈ c.support, algebraMap ℂ (LaurentSeries ℂ) (c p) * differentialJet p.2 f
        = ratToLaurent g := by
  classical
  set F : LaurentSeries ℂ :=
    ∑ p ∈ c.support, algebraMap ℂ (LaurentSeries ℂ) (c p) * differentialJet p.2 f with hF
  set R : RatFunc ℂ :=
    ∑ p ∈ c.support, algebraMap ℂ (RatFunc ℂ) (c p) * differentialJet p.2 r with hR
  have hjetf : ∀ n : ℕ, shiftLaurent h (differentialJet n f)
      = differentialJet n f + ratToLaurent (differentialJet n r) := by
    intro n
    rw [ringEquiv_differentialJet (fun _ : Unit => shiftLaurent h)
      (fun _ x => shiftLaurent_deriv h x) () n f, hfr]
    rw [← algebraMap_ratLaurent, differentialJet_add_algebraMap, algebraMap_ratLaurent]
  have hFshift : shiftLaurent h F = F + ratToLaurent R := by
    rw [hF, map_sum, hR, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul, shiftLaurent_algebraMap_complex, hjetf, mul_add]
    congr 1
    rw [map_mul, ← algebraMap_ratLaurent, ← algebraMap_ratLaurent,
      ← IsScalarTower.algebraMap_apply]
  have hkshift : shiftLaurent h (ratToLaurent k) = ratToLaurent k + ratToLaurent R := by
    rw [shiftLaurent_ratToLaurent, ← map_add]
    congr 1
    linear_combination htel
  have hfix : shiftLaurent h (F - ratToLaurent k) = F - ratToLaurent k := by
    rw [map_sub, hFshift, hkshift]
    ring
  obtain ⟨d, hd⟩ := exists_algebraMap_complex_of_shiftLaurent_eq hh hfix
  refine ⟨k + algebraMap ℂ (RatFunc ℂ) d, ?_⟩
  rw [map_add]
  have hdL : algebraMap ℂ (LaurentSeries ℂ) d
      = ratToLaurent (algebraMap ℂ (RatFunc ℂ) d) := by
    rw [← algebraMap_ratLaurent, ← IsScalarTower.algebraMap_apply]
  rw [← hdL, hd]
  ring

end

end GaloisForLFunctions.HTGeometry
