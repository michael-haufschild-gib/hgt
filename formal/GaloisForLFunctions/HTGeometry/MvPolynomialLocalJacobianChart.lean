import GaloisForLFunctions.HTGeometry.LocalizedMvPolynomialCotangent
import GaloisForLFunctions.HTGeometry.SourceResidueCotangent
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.Localization.Algebra

/-!
# Polynomial Jacobian charts at smooth complex points

This file converts formal smoothness of a localized quotient of a complex polynomial ring into
an explicit finite polynomial chart.  The relations are lifted all the way back to the original
ideal, generate its localized presentation kernel, and have linearly independent complex
gradients at the chosen closed point.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

noncomputable section

/-- At the residue field of the localization at the complex point `x`, the image of a polynomial
is its ordinary evaluation at `x`. -/
theorem localizedMvPolynomialResidue_algebraMap_eq_eval
    {σ : Type} [Finite σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (x : σ → ℂ) (hQ : Q = MvPolynomial.vanishingIdeal ℂ {x})
    (r : MvPolynomial σ ℂ) :
    let P := Localization.AtPrime Q
    let K := IsLocalRing.ResidueField P
    algebraMap P K (algebraMap (MvPolynomial σ ℂ) P r) =
      algebraMap ℂ K (MvPolynomial.eval x r) := by
  dsimp only
  let P := Localization.AtPrime Q
  let K := IsLocalRing.ResidueField P
  letI : IsScalarTower ℂ P K :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower (MvPolynomial σ ℂ) P K :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hhom : IsScalarTower.toAlgHom ℂ (MvPolynomial σ ℂ) K =
      MvPolynomial.aeval (fun i ↦ algebraMap ℂ K (x i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    have hmem : MvPolynomial.X i - MvPolynomial.C (x i) ∈ Q := by
      rw [hQ, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    have hz : algebraMap (MvPolynomial σ ℂ) K
        (MvPolynomial.X i - MvPolynomial.C (x i)) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr hmem
    rw [map_sub, sub_eq_zero] at hz
    simpa using hz
  change (IsScalarTower.toAlgHom ℂ (MvPolynomial σ ℂ) K) r = _
  rw [hhom]
  change MvPolynomial.eval₂Hom (algebraMap ℂ K)
      (fun i ↦ algebraMap ℂ K (x i)) r =
    algebraMap ℂ K (MvPolynomial.eval₂Hom (RingHom.id ℂ) x r)
  simpa using (MvPolynomial.map_eval₂Hom (RingHom.id ℂ) x
    (algebraMap ℂ K) r).symm

/-- Cotangent independence in the source residue field becomes ordinary complex gradient
independence at the closed point. -/
theorem gradient_linearIndependent_of_sourceResidueCotangent
    {σ : Type} [Finite σ]
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (S : Type*) [CommRing S]
    [Algebra (Localization.AtPrime Q) S]
    (hker : RingHom.ker
        (algebraMap (Localization.AtPrime Q) S) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q))
    (x : σ → ℂ) (hQ : Q = MvPolynomial.vanishingIdeal ℂ {x})
    {m : ℕ} (relation : Fin m → MvPolynomial σ ℂ)
    (u : Fin m → RingHom.ker
      (algebraMap (Localization.AtPrime Q) S))
    (huval : ∀ i, (u i).1 =
      algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)
        (relation i))
    (huli : LinearIndependent
      (IsLocalRing.ResidueField (Localization.AtPrime Q))
      (fun i ↦ sourceResidueCotangentMap ℂ (Localization.AtPrime Q) S hker
        (1 ⊗ₜ[Localization.AtPrime Q] u i))) :
    LinearIndependent ℂ
      (fun i j ↦ MvPolynomial.eval x
        (MvPolynomial.pderiv j (relation i))) := by
  let P := Localization.AtPrime Q
  let K := IsLocalRing.ResidueField P
  letI : IsScalarTower ℂ P K :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower (MvPolynomial σ ℂ) P K :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let coord : (K ⊗[P] Ω[P⁄ℂ]) ≃ₗ[K] (σ → K) :=
    ((localizedMvPolynomialKaehlerBasis Q).baseChange K).repr.trans
      (Finsupp.linearEquivFunOnFinite K K σ)
  have hcoordli : LinearIndependent K
      (fun i ↦ coord (sourceResidueCotangentMap ℂ P S hker
        (1 ⊗ₜ[P] u i))) := by
    exact huli.map' coord.toLinearMap
      (LinearMap.ker_eq_bot.mpr coord.injective)
  have hcoord :
      (fun i ↦ coord (sourceResidueCotangentMap ℂ P S hker
        (1 ⊗ₜ[P] u i))) =
      (fun i j ↦ algebraMap P K
        (algebraMap (MvPolynomial σ ℂ) P
          (MvPolynomial.pderiv j (relation i)))) := by
    funext i j
    change ((localizedMvPolynomialKaehlerBasis Q).baseChange K).repr
      (1 ⊗ₜ[P] KaehlerDifferential.D ℂ P (u i).1) j = _
    rw [huval i]
    exact localizedMvPolynomialKaehlerBasis_baseChange_repr_D_algebraMap
      Q K (relation i) j
  rw [hcoord] at hcoordli
  have hgradK : LinearIndependent K
      (fun i j ↦ algebraMap ℂ K
        (MvPolynomial.eval x
          (MvPolynomial.pderiv j (relation i)))) := by
    convert hcoordli using 1
    funext i j
    exact (localizedMvPolynomialResidue_algebraMap_eq_eval Q x hQ
      (MvPolynomial.pderiv j (relation i))).symm
  exact (linearIndependent_algebraMap_comp_iff.mp (by
    simpa [Function.comp_def] using hgradK))

/- A formally smooth closed point of a complex polynomial quotient has an explicit finite
Jacobian chart.  The chosen relations belong to the original ideal, generate the kernel after
localization at the point, and have linearly independent gradients over `ℂ` at that point. -/
set_option maxHeartbeats 4000000 in
theorem exists_localJacobianChart_of_formallySmooth_point
    {σ : Type} [Finite σ]
    (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I))
    (x : σ → ℂ)
    (hQ : Ideal.comap (Ideal.Quotient.mk I) p.asIdeal =
      MvPolynomial.vanishingIdeal ℂ {x})
    (hlocal : Algebra.FormallySmooth ℂ
      (Localization.AtPrime p.asIdeal)) :
    ∃ (m : ℕ) (relation : Fin m → MvPolynomial σ ℂ),
      (∀ i, relation i ∈ I) ∧
      (let q : Ideal ((MvPolynomial σ ℂ) ⧸ I) := p.asIdeal
       let Q : Ideal (MvPolynomial σ ℂ) :=
         q.comap (Ideal.Quotient.mk I)
       let P := Localization.AtPrime Q
       let S := Localization.AtPrime q
       letI : q.LiesOver Q := ⟨rfl⟩
       letI : Algebra P S := Localization.AtPrime.algebraOfLiesOver Q q
       Ideal.span (Set.range (fun i ↦
           algebraMap (MvPolynomial σ ℂ) P (relation i))) =
         RingHom.ker (algebraMap P S)) ∧
      LinearIndependent ℂ
        (fun i j ↦ MvPolynomial.eval x
          (MvPolynomial.pderiv j (relation i))) := by
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
      IsLocalRing.maximalIdeal P := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal]
    intro hua
    have hu : IsUnit (algebraMap P S a) := hua.map (algebraMap P S)
    rw [RingHom.mem_ker.mp ha] at hu
    exact not_isUnit_zero hu
  have hinj : Function.Injective
      (sourceResidueCotangentMap ℂ P S hker) :=
    sourceResidueCotangentMap_injective ℂ P S hsurj hfg hlocal
  obtain ⟨m, v, hvspan, hvli⟩ :=
    exists_finite_sourceResidue_basis_lifts ℂ P S hker hfg hinj
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
  refine ⟨m, relation, hrelation_mem, ?_, ?_⟩
  · exact hideal
  · let K := IsLocalRing.ResidueField P
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
      exact hvli.units_smul denominatorUnitK
    have hQ' : Q = MvPolynomial.vanishingIdeal ℂ {x} := hQ
    exact gradient_linearIndependent_of_sourceResidueCotangent
      Q S hker x hQ' relation u huval huli

end

end GaloisForLFunctions.HTGeometry
