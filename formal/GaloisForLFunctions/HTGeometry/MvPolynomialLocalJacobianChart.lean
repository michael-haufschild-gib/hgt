import GaloisForLFunctions.HTGeometry.LocalizedMvPolynomialCotangent
import GaloisForLFunctions.HTGeometry.MvPolynomialLocalJacobianData
import GaloisForLFunctions.HTGeometry.SourceResidueCotangent
import GaloisForLFunctions.HTGeometry.SourceResidueCotangentApply
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
    simpa using! hz
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
    rw [sourceResidueCotangentMap_one_tmul]
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
  obtain ⟨m, v, hvspan, hvli⟩ :=
    exists_sourceResidue_basis_at_formallySmooth_point I p hlocal
  obtain ⟨relation, u, hrelation_mem, huval, hideal, huli⟩ :=
    exists_originalRelations_of_sourceResidue_basis I p v hvspan hvli
  refine ⟨m, relation, hrelation_mem, hideal, ?_⟩
  have hQ' : polynomialPointIdeal I p =
      MvPolynomial.vanishingIdeal ℂ {x} := hQ
  exact gradient_linearIndependent_of_sourceResidueCotangent
    (polynomialPointIdeal I p) (localQuotientRing I p)
    (localPresentationKernel_le_maximal I p) x hQ' relation u huval (by
      change LinearIndependent
        (IsLocalRing.ResidueField (localPolynomialRing I p))
        (fun i ↦ localPresentationSourceResidueCotangentMap I p
          (1 ⊗ₜ[localPolynomialRing I p] u i))
      exact huli)

end

end GaloisForLFunctions.HTGeometry
