import GaloisForLFunctions.HTGeometry.AdjoinRootSplitBaseChangeSeparable
import GaloisForLFunctions.HTGeometry.FiniteEtaleAlgClosedSplit

/-!
# Separable principal-open presentations

A split local residue fibre produces a monic root presentation on one principal open.  The
distinguished root is the localized global numerator, and the defining polynomial remains
separable at the original residue point.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing
open scoped TensorProduct

/-- Canonical map from a principal localization into a prime localization containing that
principal open. -/
noncomputable def principalOpenToLocalizationRingHom
    (R : Type*) [CommRing R]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization p.primeCompl T]
    (g : R) (hg : g ∉ p) : Localization (Submonoid.powers g) →+* T :=
  IsLocalization.Away.lift g
    (IsLocalization.map_units (M := p.primeCompl) T ⟨g, hg⟩)

/-- Specialization from a principal open containing a prime to the residue field at that prime. -/
noncomputable def principalOpenToResidueRingHom
    (R : Type*) [CommRing R]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [IsLocalRing T] [Algebra R T]
    [IsLocalization p.primeCompl T]
    (g : R) (hg : g ∉ p) : Localization (Submonoid.powers g) →+* ResidueField T :=
  (residue T).comp (principalOpenToLocalizationRingHom R p T g hg)

/-- A split local residue fibre spreads to a principal-open monic root presentation whose
specialization at the original point is separable. -/
theorem exists_principalOpen_adjoinRoot_equiv_and_separable_of_split_residue_fibre
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T]
    [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [CommRing N] [IsDomain N] [Algebra R N] [Algebra T N]
    [IsScalarTower R T N] [NoZeroSMulDivisors T N] [Module.Finite T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule p.primeCompl fN.toLinearMap]
    [CharZero (ResidueField T)]
    {ι : Type*} [Fintype ι]
    (hsplit : Nonempty ((N ⧸ maxExt T N) ≃ₐ[ResidueField T] (ι → ResidueField T))) :
    ∃ theta : B, ∃ g : R, ∃ hg : g ∉ p,
      ∃ q : Polynomial (Localization (Submonoid.powers g)), q.Monic ∧
        ∃ e : AdjoinRoot q ≃ₐ[Localization (Submonoid.powers g)]
            TensorProduct R (Localization (Submonoid.powers g)) B,
          e (AdjoinRoot.root q) = Algebra.TensorProduct.includeRight
            (R := R) (A := Localization (Submonoid.powers g)) (B := B) theta ∧
          (q.map (principalOpenToResidueRingHom R p T g hg)).Separable := by
  obtain ⟨theta, g, hg, q, hq, e, he⟩ :=
    exists_principalOpen_adjoinRoot_equiv_of_split_residue_fibre R B p T N fN hsplit
  refine ⟨theta, g, hg, q, hq, e, he, ?_⟩
  let S := Localization (Submonoid.powers g)
  let k := ResidueField T
  letI : Algebra S T := (principalOpenToLocalizationRingHom R p T g hg).toAlgebra
  letI : Algebra R k := ((residue T).comp (algebraMap R T)).toAlgebra
  letI : Algebra S k := (principalOpenToResidueRingHom R p T g hg).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R T r =
      principalOpenToLocalizationRingHom R p T g hg (algebraMap R S r)
    rw [principalOpenToLocalizationRingHom, IsLocalization.Away.lift_eq]
  letI : IsScalarTower R T k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower S T k := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq fun r => by
    change residue T (algebraMap R T r) =
      residue T (principalOpenToLocalizationRingHom R p T g hg (algebraMap R S r))
    rw [principalOpenToLocalizationRingHom, IsLocalization.Away.lift_eq]
  exact separable_map_of_adjoinRoot_equiv_of_localized_split_baseChange
    R p.primeCompl S T k B N fN q hq e
    (nonempty_tensorProduct_algEquiv_pi_of_split_residue_fibre hsplit)

/-- A nondegenerate local residue trace spreads to a principal-open monic root presentation whose
specialization at the original point is separable. -/
theorem exists_principalOpen_adjoinRoot_equiv_and_separable_of_residue_traceForm_nondegenerate
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T]
    [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [CommRing N] [IsDomain N] [Algebra R N] [Algebra T N]
    [IsScalarTower R T N] [NoZeroSMulDivisors T N] [Module.Finite T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule p.primeCompl fN.toLinearMap]
    [CharZero (ResidueField T)] [IsAlgClosed (ResidueField T)]
    (h : (Algebra.traceForm (ResidueField T) (N ⧸ maxExt T N)).Nondegenerate) :
    ∃ theta : B, ∃ g : R, ∃ hg : g ∉ p,
      ∃ q : Polynomial (Localization (Submonoid.powers g)), q.Monic ∧
        ∃ e : AdjoinRoot q ≃ₐ[Localization (Submonoid.powers g)]
            TensorProduct R (Localization (Submonoid.powers g)) B,
          e (AdjoinRoot.root q) = Algebra.TensorProduct.includeRight
            (R := R) (A := Localization (Submonoid.powers g)) (B := B) theta ∧
          (q.map (principalOpenToResidueRingHom R p T g hg)).Separable := by
  letI : Module.Finite T (N ⧸ maxExt T N) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ T (maxExt T N)).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : Module.Finite (ResidueField T) (N ⧸ maxExt T N) :=
    Module.Finite.of_restrictScalars_finite T _ _
  letI : IsArtinianRing (N ⧸ maxExt T N) :=
    isArtinian_of_tower (ResidueField T) inferInstance
  letI : Fintype (MaximalSpectrum (N ⧸ maxExt T N)) := Fintype.ofFinite _
  exact exists_principalOpen_adjoinRoot_equiv_and_separable_of_split_residue_fibre
    R B p T N fN (nonempty_algEquiv_pi_of_traceForm_nondegenerate h)

/-- A finite étale local residue fibre spreads to a principal-open monic root presentation whose
specialization at the original point is separable. -/
theorem exists_principalOpen_adjoinRoot_equiv_and_separable_of_residue_finiteEtale
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (B : Type*) [CommRing B] [Algebra R B] [Module.Finite R B]
    (p : Ideal R) [p.IsPrime]
    (T : Type*) [CommRing T] [IsDomain T] [IsLocalRing T] [IsIntegrallyClosed T]
    [Algebra R T] [IsLocalization p.primeCompl T]
    (N : Type*) [CommRing N] [IsDomain N] [Algebra R N] [Algebra T N]
    [IsScalarTower R T N] [NoZeroSMulDivisors T N] [Module.Finite T N]
    (fN : B →ₐ[R] N) [IsLocalizedModule p.primeCompl fN.toLinearMap]
    [CharZero (ResidueField T)] [IsAlgClosed (ResidueField T)]
    [Algebra.Etale (ResidueField T) (N ⧸ maxExt T N)] :
    ∃ theta : B, ∃ g : R, ∃ hg : g ∉ p,
      ∃ q : Polynomial (Localization (Submonoid.powers g)), q.Monic ∧
        ∃ e : AdjoinRoot q ≃ₐ[Localization (Submonoid.powers g)]
            TensorProduct R (Localization (Submonoid.powers g)) B,
          e (AdjoinRoot.root q) = Algebra.TensorProduct.includeRight
            (R := R) (A := Localization (Submonoid.powers g)) (B := B) theta ∧
          (q.map (principalOpenToResidueRingHom R p T g hg)).Separable := by
  letI : Module.Finite T (N ⧸ maxExt T N) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ T (maxExt T N)).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : Module.Finite (ResidueField T) (N ⧸ maxExt T N) :=
    Module.Finite.of_restrictScalars_finite T _ _
  letI : IsArtinianRing (N ⧸ maxExt T N) :=
    isArtinian_of_tower (ResidueField T) inferInstance
  letI : Fintype (PrimeSpectrum (N ⧸ maxExt T N)) := Fintype.ofFinite _
  exact exists_principalOpen_adjoinRoot_equiv_and_separable_of_split_residue_fibre
    R B p T N fN Algebra.nonempty_algEquiv_pi_of_finiteEtale_isAlgClosed

end GaloisForLFunctions.HTGeometry
