import GaloisForLFunctions.HTGeometry.SplitResidueLocalMonogenic
import GaloisForLFunctions.HTGeometry.MonogenicKaehlerAnnihilator

/-!
# Adjoin-root presentations from split residue fibres

For finite domain extensions over an integrally closed local domain, the local generator supplied
by a split closed fibre presents the whole algebra as the root algebra of its minimal polynomial.
This is the algebraic presentation consumed by finite-cover charts.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing

/-- **Split residue fibre gives an adjoin-root presentation.** -/
theorem exists_adjoinRoot_equiv_of_split_residue_fibre
    {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Module.Finite A B] [CharZero (ResidueField A)]
    {ι : Type*} [Fintype ι]
    (hsplit : Nonempty ((B ⧸ maxExt A B) ≃ₐ[ResidueField A] (ι → ResidueField A))) :
    ∃ θ : B, IsIntegral A θ ∧
      Nonempty (AdjoinRoot (minpoly A θ) ≃ₐ[A] B) := by
  obtain ⟨θ, hgen⟩ := exists_adjoin_eq_top_of_split_residue_fibre hsplit
  have hθ : IsIntegral A θ := IsIntegral.of_finite A θ
  exact ⟨θ, hθ, ⟨monogenicEquiv hθ hgen⟩⟩

/-- **Nondegenerate residue trace gives an adjoin-root presentation.** -/
theorem exists_adjoinRoot_equiv_of_residue_traceForm_nondegenerate
    {A B : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [Algebra A B] [NoZeroSMulDivisors A B]
    [Module.Finite A B] [CharZero (ResidueField A)] [IsAlgClosed (ResidueField A)]
    (h : (Algebra.traceForm (ResidueField A) (B ⧸ maxExt A B)).Nondegenerate) :
    ∃ θ : B, IsIntegral A θ ∧
      Nonempty (AdjoinRoot (minpoly A θ) ≃ₐ[A] B) := by
  letI : Module.Finite A (B ⧸ maxExt A B) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (maxExt A B)).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : Module.Finite (ResidueField A) (B ⧸ maxExt A B) :=
    Module.Finite.of_restrictScalars_finite A _ _
  letI : IsArtinianRing (B ⧸ maxExt A B) :=
    isArtinian_of_tower (ResidueField A) inferInstance
  letI : Fintype (MaximalSpectrum (B ⧸ maxExt A B)) := Fintype.ofFinite _
  exact exists_adjoinRoot_equiv_of_split_residue_fibre
    (nonempty_algEquiv_pi_of_traceForm_nondegenerate h)

end GaloisForLFunctions.HTGeometry
