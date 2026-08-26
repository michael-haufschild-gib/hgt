import GaloisForLFunctions.HTGeometry.PrincipalOpenLocalizationFiniteType
import GaloisForLFunctions.HTGeometry.AffineExponentialAlgebraicLocusKaehler
import GaloisForLFunctions.HTGeometry.AffineExponentialInvariantKaehlerTranslation

/-!
# Principal-open sources of exact affine-exponential loci

From a mixed invariant Kähler relation at an extension-field point, this file constructs the exact
principal-open source of its locus over the base field.  The source is integral and finite type,
contains the identity after translation by a base-field point, retains the original generic point,
and kills the invariant form scheme-theoretically.
-/

open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry

open AffineExponentialGroup AffineExponentialPointEvaluation
open AffineExponentialPointRepresentation AffineExponentialPointClosure
open AffineExponentialInvariantKaehler

universe u

noncomputable section

structure AffineExponentialPrincipalOpenSource
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (n : ℕ) (p : Point L n) (tor add : Fin n → k) where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra k carrier]
  [isDomain : IsDomain carrier]
  [finiteType : Algebra.FiniteType k carrier]
  map : CoordinateAlgebra k n →ₐ[k] carrier
  identityPoint : carrier →ₐ[k] k
  genericPoint : carrier →ₐ[k] L
  algebraicPoint : Point k n
  map_identity : identityPoint.comp map =
    Bialgebra.counitAlgHom k (CoordinateAlgebra k n)
  map_generic : genericPoint.comp map =
    (eval (k := k) p).comp (rightTranslate algebraicPoint⁻¹)
  kaehler_zero : algHomKaehlerMap map (mixedInvariantKaehlerVector k tor add) = 0

/-- Generic vanishing of a mixed invariant form produces an integral finite-type principal-open
source of the translated exact locus, with both its identity point and original generic point. -/
theorem exists_affineExponentialPrincipalOpenSource
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [IsAlgClosed k] [CharZero k]
    {n : ℕ} (p : Point L n) (tor add : Fin n → k)
    (hw : pointKaehlerMap k p (mixedInvariantKaehlerVector k tor add) = 0) :
    Nonempty (AffineExponentialPrincipalOpenSource k L n p tor add) := by
  let A := CoordinateAlgebra k n
  let J : Ideal A := RingHom.ker (eval (k := k) p).toRingHom
  letI quotientCommRing : CommRing (A ⧸ J) := inferInstance
  letI : J.IsPrime := by
    exact RingHom.ker_isPrime (eval (k := k) p).toRingHom
  letI : IsDomain (A ⧸ J) := Ideal.Quotient.isDomain J
  letI : Algebra.FiniteType k (A ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k J)
      Ideal.Quotient.mk_surjective
  let π : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J
  let rhoP : (A ⧸ J) →ₐ[k] L :=
    Ideal.Quotient.liftₐ J (eval (k := k) p) (fun a ha => ha)
  have hrhoP : Function.Injective rhoP := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq]
    change eval (k := k) p (a - b) = 0
    rw [map_sub, sub_eq_zero]
    exact hxy
  have hcompP : rhoP.comp π = eval (k := k) p := by
    rfl
  have hgeneric :
      algHomKaehlerMap rhoP
        (algHomKaehlerMap π (mixedInvariantKaehlerVector k tor add)) = 0 := by
    rw [← algHomKaehlerMap_comp, hcompP]
    exact hw
  obtain ⟨s, hs, hsw⟩ :=
    exists_nonzero_smul_eq_zero_of_algHomKaehlerMap_eq_zero
      rhoP hrhoP hgeneric
  obtain ⟨rhoQ, hrhoQ⟩ :=
    exists_algHom_ne_zero_of_finiteType_domain k (A ⧸ J) s hs
  let O := Localization.Away s
  letI : IsDomain O := localizationAway_isDomain_of_ne_zero hs
  letI : Algebra.FiniteType k O := localizationAway_finiteType s
  let loc : (A ⧸ J) →ₐ[k] O := localizationAwayAlgHom (k := k) s
  let e : O →ₐ[k] k :=
    IsLocalization.Away.liftAlgHom s (isUnit_iff_ne_zero.mpr hrhoQ)
  have hrhoPs : rhoP s ≠ 0 := hrhoP.ne hs
  let r : O →ₐ[k] L :=
    IsLocalization.Away.liftAlgHom s (isUnit_iff_ne_zero.mpr hrhoPs)
  let chi : A →ₐ[k] k := rhoQ.comp π
  let q : Point k n := pointOfAlgHom chi
  let f : A →ₐ[k] O := loc.comp (π.comp (rightTranslate q⁻¹))
  have huQ : IsUnit (rhoQ.toRingHom s) := isUnit_iff_ne_zero.mpr hrhoQ
  have huP : IsUnit (rhoP.toRingHom s) := isUnit_iff_ne_zero.mpr hrhoPs
  have heLoc : e.comp loc = rhoQ := by
    apply DFunLike.ext _ _
    intro b
    change IsLocalization.Away.lift s huQ
      (algebraMap (A ⧸ J) O b) = rhoQ b
    exact IsLocalization.Away.lift_eq s huQ b
  have hrLoc : r.comp loc = rhoP := by
    apply DFunLike.ext _ _
    intro b
    change IsLocalization.Away.lift s huP
      (algebraMap (A ⧸ J) O b) = rhoP b
    exact IsLocalization.Away.lift_eq s huP b
  have hfIdentity : e.comp f = Bialgebra.counitAlgHom k A := by
    apply DFunLike.ext _ _
    intro a
    change e (loc (π (rightTranslate q⁻¹ a))) = Coalgebra.counit (R := k) a
    rw [show e (loc (π (rightTranslate q⁻¹ a))) =
      rhoQ (π (rightTranslate q⁻¹ a)) by
        exact DFunLike.congr_fun heLoc (π (rightTranslate q⁻¹ a))]
    change chi (rightTranslate q⁻¹ a) = Coalgebra.counit (R := k) a
    rw [← eval_pointOfAlgHom chi (rightTranslate q⁻¹ a)]
    rw [eval_rightTranslate]
    rw [mul_inv_cancel]
    exact eval_one_point a
  have hfGeneric : r.comp f = (eval (k := k) p).comp (rightTranslate q⁻¹) := by
    apply DFunLike.ext _ _
    intro a
    change r (loc (π (rightTranslate q⁻¹ a))) =
      eval (k := k) p (rightTranslate q⁻¹ a)
    rw [show r (loc (π (rightTranslate q⁻¹ a))) =
      rhoP (π (rightTranslate q⁻¹ a)) by
        exact DFunLike.congr_fun hrLoc (π (rightTranslate q⁻¹ a))]
    exact DFunLike.congr_fun hcompP (rightTranslate q⁻¹ a)
  have hloc : algHomKaehlerMap loc
      (algHomKaehlerMap π (mixedInvariantKaehlerVector k tor add)) = 0 := by
    exact algHomKaehlerMap_localizationAway_eq_zero_of_smul_eq_zero
      s (algHomKaehlerMap π (mixedInvariantKaehlerVector k tor add)) hsw
  have hbase : algHomKaehlerMap (loc.comp π)
      (mixedInvariantKaehlerVector k tor add) = 0 := by
    rw [algHomKaehlerMap_comp]
    exact hloc
  have hfKaehler : algHomKaehlerMap f
      (mixedInvariantKaehlerVector k tor add) = 0 := by
    rw [show f = (loc.comp π).comp (rightTranslate q⁻¹) by rfl]
    rw [algHomKaehlerMap_comp,
      algHomKaehlerMap_rightTranslate_mixedInvariantKaehlerVector]
    exact hbase
  exact ⟨{
    carrier := O
    map := f
    identityPoint := e
    genericPoint := r
    algebraicPoint := q
    map_identity := hfIdentity
    map_generic := hfGeneric
    kaehler_zero := hfKaehler
  }⟩

end

end GaloisForLFunctions.HTGeometry
