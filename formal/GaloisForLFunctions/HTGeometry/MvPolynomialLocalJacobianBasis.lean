import GaloisForLFunctions.HTGeometry.LocalizedMvPolynomialCotangent
import GaloisForLFunctions.HTGeometry.MvPolynomialLocalPoint
import GaloisForLFunctions.HTGeometry.SourceResidueCotangent

/-!
# Cotangent relation bases at formally smooth polynomial points

This module caches the expensive formal-smoothness step separately from denominator clearing.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

theorem localPresentationKernel_le_maximal
    {σ : Type} (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :
    localPresentationKernel I p ≤
      IsLocalRing.maximalIdeal (localPolynomialRing I p) := by
  intro a ha
  rw [IsLocalRing.mem_maximalIdeal]
  intro hua
  have hu : IsUnit (algebraMap (localPolynomialRing I p)
      (localQuotientRing I p) a) :=
    hua.map (algebraMap (localPolynomialRing I p) (localQuotientRing I p))
  rw [RingHom.mem_ker.mp ha] at hu
  exact not_isUnit_zero hu

noncomputable abbrev localPresentationSourceResidueCotangentMap
    {σ : Type} (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :
    IsLocalRing.ResidueField (localPolynomialRing I p) ⊗[localPolynomialRing I p]
        localPresentationKernel I p →ₗ[IsLocalRing.ResidueField (localPolynomialRing I p)]
      IsLocalRing.ResidueField (localPolynomialRing I p) ⊗[localPolynomialRing I p]
        Ω[localPolynomialRing I p⁄ℂ] :=
  sourceResidueCotangentMap ℂ (localPolynomialRing I p)
    (localQuotientRing I p) (localPresentationKernel_le_maximal I p)

set_option maxHeartbeats 8000000 in
theorem exists_sourceResidue_basis_at_formallySmooth_point
    {σ : Type} [Finite σ]
    (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I))
    (hlocal : Algebra.FormallySmooth ℂ
      (Localization.AtPrime p.asIdeal)) :
    ∃ (m : ℕ) (v : Fin m → localPresentationKernel I p),
      Submodule.span (localPolynomialRing I p) (Set.range v) = ⊤ ∧
      LinearIndependent (IsLocalRing.ResidueField (localPolynomialRing I p))
        (fun i ↦ localPresentationSourceResidueCotangentMap I p
          (1 ⊗ₜ[localPolynomialRing I p] v i)) := by
  let q : Ideal ((MvPolynomial σ ℂ) ⧸ I) := p.asIdeal
  let Q : Ideal (MvPolynomial σ ℂ) :=
    q.comap (Ideal.Quotient.mk I)
  let P := Localization.AtPrime Q
  let S := Localization.AtPrime q
  letI : Algebra.FormallyEtale (MvPolynomial σ ℂ) P :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  let bP : Module.Basis σ P Ω[P⁄ℂ] :=
    localizedMvPolynomialKaehlerBasis Q
  letI : Module.Free P Ω[P⁄ℂ] := Module.Free.of_basis bP
  letI : Module.Finite P Ω[P⁄ℂ] := Module.Finite.of_basis bP
  letI : q.LiesOver Q := ⟨rfl⟩
  letI : Algebra P S := Localization.AtPrime.algebraOfLiesOver Q q
  have hsurj : Function.Surjective (algebraMap P S) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    exact RingHom.surjective_localRingHom_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective q
  have hfg : (RingHom.ker (algebraMap P S)).FG :=
    IsNoetherian.noetherian _
  have hker : RingHom.ker (algebraMap P S) ≤
      IsLocalRing.maximalIdeal P := localPresentationKernel_le_maximal I p
  have hinj : Function.Injective
      (sourceResidueCotangentMap ℂ P S hker) :=
    sourceResidueCotangentMap_injective ℂ P S hsurj hfg hlocal
  obtain ⟨m, v, hvspan, hvli⟩ :=
    exists_finite_sourceResidue_basis_lifts ℂ P S hker hfg hinj
  refine ⟨m, v, hvspan, ?_⟩
  change LinearIndependent (IsLocalRing.ResidueField P)
    (fun i ↦ sourceResidueCotangentMap ℂ P S hker
      (1 ⊗ₜ[P] v i))
  exact hvli

end

end GaloisForLFunctions.HTGeometry
