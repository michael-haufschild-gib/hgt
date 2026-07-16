import GaloisForLFunctions.HTGeometry.MvPolynomialLocalJacobianChart
import GaloisForLFunctions.HTGeometry.MvPolynomialPointIdealHeight
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Codimension bounds for local polynomial Jacobian charts

The explicit Jacobian chart at a formally smooth point comes with finitely many localized
relations.  This module proves that a Krull-dimension drop forces the number of those independent
relations to be at least the drop.  It is the algebraic bridge from global dimension estimates to
the real codimension required by regular-level-set stratifications.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- At a complex closed point, a bound on the local quotient height forces a lower bound on the
number of relations generating the localized presentation kernel. -/
theorem localJacobian_relation_count_ge_of_height
    {n c m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (p : PrimeSpectrum ((MvPolynomial (Fin n) ℂ) ⧸ I))
    (x : Fin n → ℂ)
    (hQ : polynomialPointIdeal I p = MvPolynomial.vanishingIdeal ℂ {x})
    (relation : Fin m → MvPolynomial (Fin n) ℂ)
    (hspan : Ideal.span (Set.range (fun i ↦
        algebraMap (MvPolynomial (Fin n) ℂ) (localPolynomialRing I p) (relation i))) =
      localPresentationKernel I p)
    (hlocaldim : p.asIdeal.height.toNat + c ≤ n) :
    c ≤ m := by
  let P := localPolynomialRing I p
  let S := localQuotientRing I p
  let J : Ideal P := localPresentationKernel I p
  have hsurj : Function.Surjective (algebraMap P S) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    exact RingHom.surjective_localRingHom_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p.asIdeal
  have hJmax : J ≤ IsLocalRing.maximalIdeal P :=
    localPresentationKernel_le_maximal I p
  have hJfin : J.spanFinrank ≤ m := by
    change (localPresentationKernel I p).spanFinrank ≤ m
    rw [← hspan]
    calc
      (Ideal.span (Set.range (fun i ↦
          algebraMap (MvPolynomial (Fin n) ℂ) P (relation i)))).spanFinrank ≤
          (Set.range (fun i ↦
            algebraMap (MvPolynomial (Fin n) ℂ) P (relation i))).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ (Set.univ : Set (Fin m)).ncard := by
        rw [← Set.image_univ]
        exact Set.ncard_image_le
      _ = m := by simp
  have hheight := height_le_ringKrullDim_quotient_add_spanFinrank
    (p := IsLocalRing.maximalIdeal P) (I := J) hJmax
  have hquot : ringKrullDim (P ⧸ J) = ringKrullDim S :=
    (RingHom.quotientKerEquivOfSurjective hsurj).ringKrullDim
  have hdimP : ringKrullDim P =
      ((polynomialPointIdeal I p).height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height
      (polynomialPointIdeal I p) P
  have hdimS : ringKrullDim S =
      (p.asIdeal.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal S
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hquot, hdimS, hdimP] at hheight
  have hpointheight : (polynomialPointIdeal I p).height = n := by
    rw [hQ]
    exact height_vanishingIdeal_singleton_fin x
  rw [hpointheight] at hheight
  have hpfinite : p.asIdeal.height ≠ ⊤ :=
    Ideal.height_ne_top (I := p.asIdeal)
      (Ideal.IsPrime.ne_top (inferInstance : p.asIdeal.IsPrime))
  rw [← ENat.coe_toNat hpfinite] at hheight
  norm_cast at hheight
  omega

/-- A global Krull-dimension drop bounds the local height at every prime of the quotient. -/
theorem quotientPrime_height_toNat_add_le_of_krullDim_add_le
    {n c : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (p : PrimeSpectrum ((MvPolynomial (Fin n) ℂ) ⧸ I))
    (hglobal : ringKrullDim ((MvPolynomial (Fin n) ℂ) ⧸ I) + c ≤
      (n : WithBot ℕ∞)) :
    p.asIdeal.height.toNat + c ≤ n := by
  have hpheight : (p.asIdeal.height : WithBot ℕ∞) ≤
      ringKrullDim ((MvPolynomial (Fin n) ℂ) ⧸ I) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  have hglobal' : (c : WithBot ℕ∞) +
      ringKrullDim ((MvPolynomial (Fin n) ℂ) ⧸ I) ≤ (n : WithBot ℕ∞) := by
    simpa [add_comm] using hglobal
  have htotal : (p.asIdeal.height : WithBot ℕ∞) + c ≤ (n : WithBot ℕ∞) := by
    simpa [add_comm] using (add_le_add_right hpheight c).trans hglobal'
  have hpfinite : p.asIdeal.height ≠ ⊤ :=
    Ideal.height_ne_top (I := p.asIdeal)
      (Ideal.IsPrime.ne_top (inferInstance : p.asIdeal.IsPrime))
  rw [← ENat.coe_toNat hpfinite] at htotal
  norm_cast at htotal

set_option maxHeartbeats 4000000 in
/-- A formally smooth complex point under a global Krull-dimension drop has an explicit Jacobian
chart with at least that many independent complex equations. -/
theorem exists_localJacobianChart_of_formallySmooth_point_with_codim
    {n c : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (p : PrimeSpectrum ((MvPolynomial (Fin n) ℂ) ⧸ I))
    (x : Fin n → ℂ)
    (hQ : polynomialPointIdeal I p = MvPolynomial.vanishingIdeal ℂ {x})
    (hlocal : Algebra.FormallySmooth ℂ (localQuotientRing I p))
    (hglobal : ringKrullDim ((MvPolynomial (Fin n) ℂ) ⧸ I) + c ≤
      (n : WithBot ℕ∞)) :
    ∃ (m : ℕ) (relation : Fin m → MvPolynomial (Fin n) ℂ),
      c ≤ m ∧
      (∀ i, relation i ∈ I) ∧
      Ideal.span (Set.range (fun i ↦
          algebraMap (MvPolynomial (Fin n) ℂ) (localPolynomialRing I p) (relation i))) =
        localPresentationKernel I p ∧
      LinearIndependent ℂ
        (fun i j ↦ MvPolynomial.eval x (MvPolynomial.pderiv j (relation i))) := by
  obtain ⟨m, relation, hmem, hspan, hli⟩ :=
    exists_localJacobianChart_of_formallySmooth_point I p x hQ hlocal
  have hlocaldim : p.asIdeal.height.toNat + c ≤ n :=
    quotientPrime_height_toNat_add_le_of_krullDim_add_le I p hglobal
  have hcm : c ≤ m :=
    localJacobian_relation_count_ge_of_height I p x hQ relation hspan hlocaldim
  exact ⟨m, relation, hcm, hmem, hspan, hli⟩

end

end GaloisForLFunctions.HTGeometry
