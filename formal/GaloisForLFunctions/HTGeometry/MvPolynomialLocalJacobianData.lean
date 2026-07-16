import GaloisForLFunctions.HTGeometry.LocalizedMvPolynomialCotangent
import GaloisForLFunctions.HTGeometry.MvPolynomialLocalPoint
import GaloisForLFunctions.HTGeometry.SourceResidueCotangent
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.Localization.Algebra

/-!
# Local polynomial relation data at a formally smooth point

The two declarations in this file keep the expensive algebraic constructions separate.  The
first extracts a finite source-residue cotangent basis.  The second lifts that basis through the
localization to relations in the original polynomial ideal.
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

set_option maxHeartbeats 4000000 in
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
  simpa [localPresentationSourceResidueCotangentMap] using hvli

set_option maxHeartbeats 4000000 in
theorem exists_originalRelations_of_sourceResidue_basis
    {σ : Type} [Finite σ]
    (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :
    ∀ {m : ℕ} (v : Fin m → localPresentationKernel I p),
      Submodule.span (localPolynomialRing I p) (Set.range v) = ⊤ →
      LinearIndependent (IsLocalRing.ResidueField (localPolynomialRing I p))
        (fun i ↦ localPresentationSourceResidueCotangentMap I p
          (1 ⊗ₜ[localPolynomialRing I p] v i)) →
      ∃ (relation : Fin m → MvPolynomial σ ℂ)
        (u : Fin m → localPresentationKernel I p),
        (∀ i, relation i ∈ I) ∧
        (∀ i, (u i).1 = algebraMap (MvPolynomial σ ℂ)
          (localPolynomialRing I p) (relation i)) ∧
        Ideal.span (Set.range (fun i ↦
          algebraMap (MvPolynomial σ ℂ) (localPolynomialRing I p)
            (relation i))) = localPresentationKernel I p ∧
        LinearIndependent (IsLocalRing.ResidueField (localPolynomialRing I p))
          (fun i ↦ localPresentationSourceResidueCotangentMap I p
            (1 ⊗ₜ[localPolynomialRing I p] u i)) := by
  intro m v hvspan hvli
  let q : Ideal ((MvPolynomial σ ℂ) ⧸ I) := p.asIdeal
  let Q : Ideal (MvPolynomial σ ℂ) :=
    q.comap (Ideal.Quotient.mk I)
  let P := Localization.AtPrime Q
  let S := Localization.AtPrime q
  letI : q.LiesOver Q := ⟨rfl⟩
  letI : Algebra P S := Localization.AtPrime.algebraOfLiesOver Q q
  have hker : RingHom.ker (algebraMap P S) ≤
      IsLocalRing.maximalIdeal P := localPresentationKernel_le_maximal I p
  have hvli' : LinearIndependent (IsLocalRing.ResidueField P)
      (fun i ↦ sourceResidueCotangentMap ℂ P S hker
        (1 ⊗ₜ[P] v i)) := by
    simpa [localPresentationSourceResidueCotangentMap] using hvli
  have hT : Submonoid.map (Ideal.Quotient.mk I) Q.primeCompl =
      q.primeCompl := by
    exact q.map_primeCompl_comap_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hle : Q.primeCompl ≤
      Submonoid.comap (Ideal.Quotient.mk I) q.primeCompl := by
    exact hT.symm ▸ Submonoid.le_comap_map Q.primeCompl
  let fLoc : P →+* S :=
    Localization.localRingHom Q q (Ideal.Quotient.mk I) rfl
  have hmap : algebraMap P S = fLoc :=
    Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq
  let rawLocKer : RingHom.ker (Ideal.Quotient.mk I) →ₗ[MvPolynomial σ ℂ]
      RingHom.ker fLoc :=
    RingHom.toKerIsLocalization P S (Ideal.Quotient.mk I) hle
  let kerEquiv : RingHom.ker fLoc ≃ₗ[P]
      RingHom.ker (algebraMap P S) :=
    LinearEquiv.ofEq _ _ (congrArg RingHom.ker hmap.symm)
  let locKer : RingHom.ker (Ideal.Quotient.mk I) →ₗ[MvPolynomial σ ℂ]
      RingHom.ker (algebraMap P S) :=
    (kerEquiv.restrictScalars (MvPolynomial σ ℂ)).toLinearMap.comp rawLocKer
  letI : IsLocalizedModule Q.primeCompl rawLocKer :=
    RingHom.toKerIsLocalization_isLocalizedModule S
      (Ideal.Quotient.mk I) hT
  letI : IsLocalizedModule Q.primeCompl locKer :=
    IsLocalizedModule.of_linearEquiv Q.primeCompl rawLocKer
      (kerEquiv.restrictScalars (MvPolynomial σ ℂ))
  choose liftData hliftData using fun i ↦
    IsLocalizedModule.surj Q.primeCompl locKer (v i)
  let relationKer : Fin m → RingHom.ker (Ideal.Quotient.mk I) :=
    fun i ↦ (liftData i).1
  let denominator : Fin m → Q.primeCompl :=
    fun i ↦ (liftData i).2
  let denominatorUnit : Fin m → Pˣ := fun i ↦
    (IsLocalization.map_units P (denominator i)).unit
  let u : Fin m → RingHom.ker (algebraMap P S) :=
    fun i ↦ locKer (relationKer i)
  have hu : u = denominatorUnit • v := by
    funext i
    change locKer (relationKer i) =
      (denominatorUnit i : P) • v i
    rw [IsUnit.unit_spec]
    exact (hliftData i).symm
  have huspan : Submodule.span P (Set.range u) = ⊤ := by
    rw [hu]
    exact Module.Basis.units_smul_span_eq_top hvspan
  let relation : Fin m → MvPolynomial σ ℂ :=
    fun i ↦ (relationKer i).1
  have hrelation_mem : ∀ i, relation i ∈ I := by
    intro i
    exact (Ideal.Quotient.eq_zero_iff_mem).mp (relationKer i).2
  have huval : ∀ i, (u i).1 =
      algebraMap (MvPolynomial σ ℂ) P (relation i) := by
    intro i
    rfl
  have hideal : Ideal.span (Set.range (fun i ↦
      algebraMap (MvPolynomial σ ℂ) P (relation i))) =
      RingHom.ker (algebraMap P S) := by
    have hmapped := congrArg
      (Submodule.map (RingHom.ker (algebraMap P S)).subtype) huspan
    simpa [Submodule.map_span, huval] using hmapped
  let K := IsLocalRing.ResidueField P
  let denominatorUnitK : Fin m → Kˣ := fun i ↦
    Units.map (algebraMap P K) (denominatorUnit i)
  have husource :
      (fun i ↦ sourceResidueCotangentMap ℂ P S hker
        (1 ⊗ₜ[P] u i)) =
      denominatorUnitK •
        (fun i ↦ sourceResidueCotangentMap ℂ P S hker
          (1 ⊗ₜ[P] v i)) := by
    funext i
    rw [hu]
    simp [denominatorUnitK]
  have huli : LinearIndependent K
      (fun i ↦ sourceResidueCotangentMap ℂ P S hker
        (1 ⊗ₜ[P] u i)) := by
    rw [husource]
    exact hvli'.units_smul denominatorUnitK
  refine ⟨relation, u, hrelation_mem, huval, hideal, ?_⟩
  simpa [localPresentationSourceResidueCotangentMap] using huli

end

end GaloisForLFunctions.HTGeometry
