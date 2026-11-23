import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KaehlerCyclicJacobian
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalizedCyclicKaehler
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFormTrace
import GaloisForLFunctions.HTGeometry.DifferentIdealKaehlerAnnihilator
import GaloisForLFunctions.HTGeometry.TopExteriorPowerDeterminant

/-! At a localization of a finite normalization of a characteristic-zero
DVR, the different is the determinant of pullback on absolute
differentials in local bases. -/

noncomputable section

open GaloisForLFunctions.HTGeometry KaehlerDifferential TensorProduct IsLocalRing
open GlobalTheory.SchemeCohomology
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

/-- The top wedge of a linear map in source and target bases is its
matrix determinant times the target basis wedge. -/
theorem wedge_image_eq_det_smul {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {d : ℕ} (a : Module.Basis (Fin d) R M)
    (b : Module.Basis (Fin d) R N) (f : M →ₗ[R] N) :
    exteriorPower.ιMulti R d (fun i => f (a i)) =
      (LinearMap.toMatrix a b f).det • exteriorPower.ιMulti R d b := by
  let e := a.equiv b (Equiv.refl (Fin d))
  let g := f.comp e.symm.toLinearMap
  have he (i : Fin d) : e.symm (b i) = a i := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (Module.Basis.equiv_apply a i b (Equiv.refl (Fin d))).symm
  have hg : LinearMap.toMatrix b b g = LinearMap.toMatrix a b f := by
    ext i j
    simp only [LinearMap.toMatrix_apply, g, LinearMap.comp_apply, LinearEquiv.coe_coe, he]
  let P (n : ℕ) := exteriorPower.map n g =
    LinearMap.det g • (LinearMap.id : ⋀[R]^n N →ₗ[R] ⋀[R]^n N)
  have hmap : P d := Eq.mp (congrArg P (Fintype.card_fin d)) (exteriorPower_map_card_eq_det_smul b g)
  have h := LinearMap.congr_fun hmap (exteriorPower.ιMulti R d b)
  rw [exteriorPower.map_apply_ιMulti, ← LinearMap.det_toMatrix b, hg] at h
  have hfun : (⇑g ∘ ⇑b) = fun i => f (a i) := by
    funext i
    change f (e.symm (b i)) = f (a i)
    exact congrArg f (he i)
  exact (congrArg (exteriorPower.ιMulti R d) hfun).symm.trans h

/-- Extending a coordinate volume to the function field multiplies the
local basis volume by the Jacobian determinant. -/
theorem coordinateWedgeInField_eq_jacobian_smul
    {k A C E : Type*} [CommRing k] [CommRing A] [CommRing C] [Field E]
    [Algebra k A] [Algebra k C] [Algebra k E] [Algebra A C] [Algebra C E] [Algebra A E]
    [IsScalarTower k A C] [IsScalarTower k C E] [IsScalarTower A C E]
    {d : ℕ} (u : Fin d → A) (a : Module.Basis (Fin d) A Ω[A⁄k])
    (ha : ∀ i, a i = D k A (u i)) (b : Module.Basis (Fin d) C Ω[C⁄k]) :
    exteriorPower.ιMulti E d (fun i => D k E (algebraMap A E (u i))) =
      algebraMap C E (LinearMap.toMatrix (a.baseChange C) b (mapBaseChange k A C)).det •
        exteriorPower.ιMulti E d (fun i => KaehlerDifferential.map k k C E (b i)) := by
  have hc (i : Fin d) :
      KaehlerDifferential.map k k C E (mapBaseChange k A C ((a.baseChange C) i)) =
        D k E (algebraMap A E (u i)) := by
    rw [Module.Basis.baseChange_apply, ha, mapBaseChange_tmul, one_smul,
      KaehlerDifferential.map_D, KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply A C E]
  have h := congrArg (algebraFormPullback k C E d)
    (wedge_image_eq_det_smul (a.baseChange C) b (mapBaseChange k A C))
  rw [map_smul] at h
  simp only [algebraFormPullback, exteriorMapOver_ιMulti, hc] at h
  rw [← IsScalarTower.algebraMap_smul E] at h
  exact h

variable {k A T C F E : Type} [CommRing k]
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero (ResidueField A)]
  [CommRing T] [IsDedekindDomain T] [CommRing C] [Field F] [Field E]
  [Algebra A F] [Algebra A T] [Algebra A E] [Algebra T E] [Algebra F E]
  [IsScalarTower A F E] [IsScalarTower A T E]
  [IsFractionRing A F] [IsFractionRing T E] [IsIntegralClosure T A E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [Module.Finite A T] [Module.IsTorsionFree A T]
  [Algebra k A] [Algebra k C] [Algebra A C] [Algebra T C]
  [IsScalarTower k A C] [IsScalarTower A T C]

include F E in
/-- In equal-rank bases, the determinant of the differential pullback
generates the extension of the different. -/
theorem map_differentIdeal_eq_span_kaehler_det (S : Submonoid T) [IsLocalization S C]
    {d : ℕ} (a : Module.Basis (Fin d) C (C ⊗[A] Ω[A⁄k]))
    (b : Module.Basis (Fin d) C Ω[C⁄k]) :
    (differentIdeal A T).map (algebraMap T C) =
      Ideal.span {(LinearMap.toMatrix a b (mapBaseChange k A C)).det} := by
  have hinj : Function.Injective (algebraMap A T) :=
    algebraMap_injective_of_fractionTower A F (L := E) (B := T)
  have hmax : maxExt A T ≠ ⊥ := by
    intro hbot
    have h := le_comap_maxExt A T
    rw [hbot, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj] at h
    exact IsDiscreteValuationRing.not_a_field A (le_bot_iff.mp h)
  obtain ⟨x, hx⟩ := exists_adjoin_eq_top_of_dedekind_finite (S := A) (B := T) hmax
  let g := LinearMap.toSpanSingleton C Ω[C⁄A] (D A C (algebraMap T C x))
  have hg : Function.Surjective g := kaehler_toSpanSingleton_surjective_of_localization S x hx
  have hd := differentIdeal_eq_annihilator_kaehler A F (L := E) (B := T) hmax
  calc
    _ = (Module.annihilator T Ω[T⁄A]).map (algebraMap T C) :=
      congrArg (Ideal.map (algebraMap T C)) hd
    _ = Module.annihilator C Ω[C⁄A] :=
      map_kaehler_annihilator_of_localization (R := A) S
    _ = _ := kaehler_annihilator_eq_span_det a b g hg

end GlobalTheory.PD
