import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Smooth.Local

/-!
# Smooth closed points of reduced complex affine algebras

Mathlib proves that the structure morphism of a reduced finite-presentation scheme over a
perfect field has dense smooth locus.  For the analytic regular-stratification bridge, a generic
scheme point is not enough: one needs an actual complex point.  This file combines density with
the Jacobson property and the weak Nullstellensatz to obtain such a closed smooth point.
-/

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry

noncomputable section

/-- A nonzero reduced finite-presentation complex affine algebra has a smooth maximal ideal. -/
theorem exists_maximal_formallySmooth_point_complex
    (A : Type) [CommRing A] [Algebra ℂ A]
    [Algebra.FinitePresentation ℂ A] [IsReduced A] [Nontrivial A] :
    ∃ p : PrimeSpectrum A,
      let f : Spec (.of A) ⟶ Spec (.of ℂ) :=
        Spec.map (CommRingCat.ofHom (algebraMap ℂ A))
      (f.stalkMap p).hom.FormallySmooth ∧ p.asIdeal.IsMaximal := by
  let f : Spec (.of A) ⟶ Spec (.of ℂ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ A))
  letI : LocallyOfFinitePresentation f :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.of_finitePresentation
  letI : IsJacobsonRing A :=
    isJacobsonRing_of_finiteType (A := ℂ) (B := A)
  have hdense : Dense (f.smoothLocus : Set (Spec (.of A))) :=
    f.dense_smoothLocus_of_perfectField
  obtain ⟨p, hp, hpclosed⟩ :=
    PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing
      (f.smoothLocus : Set (Spec (.of A))) f.smoothLocus.2 hdense.nonempty
  exact ⟨p, hp, (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mp hpclosed⟩

/-- Scheme-theoretic smoothness of a point of `Spec A` over `Spec ℂ` is the formal smoothness
of the ordinary local algebra `Aₚ` over `ℂ`.  This theorem performs the stalk/localization
comparison explicitly, so later Jacobian arguments can work directly in `Localization.AtPrime`. -/
theorem formallySmooth_atPrime_of_spec_formallySmooth_complex
    (A : Type) [CommRing A] [Algebra ℂ A]
    (p : PrimeSpectrum A)
    (h : let f : Spec (.of A) ⟶ Spec (.of ℂ) :=
      Spec.map (CommRingCat.ofHom (algebraMap ℂ A))
      (f.stalkMap p).hom.FormallySmooth) :
    Algebra.FormallySmooth ℂ (Localization.AtPrime p.asIdeal) := by
  let q : Ideal A := p.asIdeal
  let p0 : Ideal ℂ := (p.comap (algebraMap ℂ A)).asIdeal
  have hover : q.LiesOver p0 := by
    refine ⟨?_⟩
    exact PrimeSpectrum.comap_asIdeal (algebraMap ℂ A) p
  letI : Algebra (Localization.AtPrime p0) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p0 q
  have hlocal :
      (Localization.localRingHom p0 q (algebraMap ℂ A) hover.1).FormallySmooth := by
    exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap ℂ A)) p)).mp h
  have hlocal' :
      (algebraMap (Localization.AtPrime p0)
        (Localization.AtPrime q)).FormallySmooth := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    exact hlocal
  rw [RingHom.formallySmooth_algebraMap] at hlocal'
  exact Algebra.FormallySmooth.iff_restrictScalars.mpr hlocal'

/-- A proper radical ideal in a finite complex polynomial ring has an actual complex zero whose
point in the reduced quotient is smooth over `ℂ`.  The equality of ideals records that the
chosen scheme point is exactly the closed point represented by `x`. -/
theorem exists_complex_zero_formallySmooth_of_radicalIdeal
    {σ : Type} [Finite σ] (I : Ideal (MvPolynomial σ ℂ))
    (hI : I ≠ ⊤) (hrad : I.IsRadical) :
    ∃ (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) (x : σ → ℂ),
      x ∈ MvPolynomial.zeroLocus ℂ I ∧
      Ideal.comap (Ideal.Quotient.mk I) p.asIdeal =
        MvPolynomial.vanishingIdeal ℂ {x} ∧
      Algebra.FormallySmooth ℂ (Localization.AtPrime p.asIdeal) := by
  letI : Nontrivial ((MvPolynomial σ ℂ) ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr hI
  letI : IsReduced ((MvPolynomial σ ℂ) ⧸ I) :=
    (Ideal.isRadical_iff_quotient_reduced I).mp hrad
  letI : Algebra.FinitePresentation ℂ ((MvPolynomial σ ℂ) ⧸ I) :=
    Algebra.FinitePresentation.quotient (IsNoetherian.noetherian I)
  obtain ⟨p, hpsmooth, hpmax⟩ :=
    exists_maximal_formallySmooth_point_complex ((MvPolynomial σ ℂ) ⧸ I)
  have hcomapmax :
      (Ideal.comap (Ideal.Quotient.mk I) p.asIdeal).IsMaximal :=
    letI : p.asIdeal.IsMaximal := hpmax
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  obtain ⟨x, hx⟩ :=
    MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hcomapmax
  have hlocal :
      Algebra.FormallySmooth ℂ (Localization.AtPrime p.asIdeal) :=
    formallySmooth_atPrime_of_spec_formallySmooth_complex
      ((MvPolynomial σ ℂ) ⧸ I) p hpsmooth
  refine ⟨p, x, ?_, hx, hlocal⟩
  rw [← Set.singleton_subset_iff]
  rw [MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal, ← hx]
  intro r hr
  change Ideal.Quotient.mk I r ∈ p.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  exact p.asIdeal.zero_mem

end

end GaloisForLFunctions.HTGeometry
