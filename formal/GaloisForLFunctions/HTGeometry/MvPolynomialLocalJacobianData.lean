import GaloisForLFunctions.HTGeometry.MvPolynomialLocalJacobianBasis
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.Localization.Algebra

/-!
# Local polynomial relation data at a formally smooth point

This module lifts a finite source-residue cotangent basis through the localization to relations
in the original polynomial ideal.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

set_option maxHeartbeats 8000000 in
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
    change LinearIndependent (IsLocalRing.ResidueField P)
      (fun i ↦ localPresentationSourceResidueCotangentMap I p
        (1 ⊗ₜ[P] v i)) at hvli
    exact hvli
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
    rw [← IsScalarTower.algebraMap_smul P]
    simpa only [relationKer, denominator] using (hliftData i).symm
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
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change algebraMap (MvPolynomial σ ℂ) P (relation i) ∈
        RingHom.ker (algebraMap P S)
      rw [← huval i]
      exact (u i).2
    · intro z hz
      let z' : RingHom.ker (algebraMap P S) := ⟨z, hz⟩
      have hzspan : z' ∈ Submodule.span P (Set.range u) := by
        rw [huspan]
        trivial
      refine Submodule.span_induction
        (p := fun w _ ↦ (w : P) ∈ Ideal.span (Set.range (fun i ↦
          algebraMap (MvPolynomial σ ℂ) P (relation i)))) ?_
        (Ideal.zero_mem _) ?_ ?_ hzspan
      · rintro _ ⟨i, rfl⟩
        change (u i : P) ∈ Ideal.span (Set.range (fun i ↦
          algebraMap (MvPolynomial σ ℂ) P (relation i)))
        rw [huval i]
        exact Ideal.subset_span ⟨i, rfl⟩
      · intro a b _ _ ha hb
        exact Ideal.add_mem _ ha hb
      · intro a w _ hw
        change a * (w : P) ∈ Ideal.span (Set.range (fun i ↦
          algebraMap (MvPolynomial σ ℂ) P (relation i)))
        exact Ideal.mul_mem_left _ a hw
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
  change LinearIndependent K
    (fun i ↦ sourceResidueCotangentMap ℂ P S hker
      (1 ⊗ₜ[P] u i))
  exact huli

end

end GaloisForLFunctions.HTGeometry
