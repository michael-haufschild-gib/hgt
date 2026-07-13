import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartGlobalIncidenceRing
import GaloisForLFunctions.HTGeometry.LocalizationQuotient
import Mathlib.RingTheory.MvPolynomial.Localization

namespace GaloisForLFunctions.HTGeometry

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable local instance chosenMvPolynomialCommRing
    {R σ : Type} [CommRing R] : CommRing (MvPolynomial σ R) := inferInstance

noncomputable local instance chosenMvPolynomialRing
    {R σ : Type} [CommRing R] : Ring (MvPolynomial σ R) :=
  @CommRing.toRing _ chosenMvPolynomialCommRing

noncomputable local instance chosenMvPolynomialSemiring
    {R σ : Type} [CommRing R] : Semiring (MvPolynomial σ R) :=
  @Ring.toSemiring _ chosenMvPolynomialRing

theorem projectiveChartRowPolynomial_map_localization
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] (b : row) :
    MvPolynomial.map
        (algebraMap (projectiveChartCoefficientRing j) (Localization.AtPrime p))
        (projectiveChartRowPolynomial q n z j exponent b) =
      localizedCoefficientRowPolynomial q n z (projectiveChartCoefficient j) exponent p b := by
  classical
  unfold projectiveChartRowPolynomial localizedCoefficientRowPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MvPolynomial.map_monomial]

def projectiveChartBaseChangedRowPolynomial
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] (b : row) :
    MvPolynomial (row × Fin n) (Localization.AtPrime p) :=
  MvPolynomial.rename (Prod.mk b)
    (localizedCoefficientRowPolynomial q n z (projectiveChartCoefficient j) exponent p b)

theorem projectiveChartGlobalRowPolynomial_map_localization
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] (b : row) :
    MvPolynomial.map
        (algebraMap (projectiveChartCoefficientRing j) (Localization.AtPrime p))
        (projectiveChartGlobalRowPolynomial q n z j exponent b) =
      projectiveChartBaseChangedRowPolynomial q n z j exponent p b := by
  rw [projectiveChartGlobalRowPolynomial, projectiveChartBaseChangedRowPolynomial,
    MvPolynomial.map_rename, projectiveChartRowPolynomial_map_localization]

def projectiveChartBaseChangedIncidenceIdeal
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :
    Ideal (MvPolynomial (row × Fin n) (Localization.AtPrime p)) :=
  Ideal.span (Set.range
    (projectiveChartBaseChangedRowPolynomial q n z j exponent p))

theorem projectiveChartGlobalIncidenceIdeal_map_localization
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :
    Ideal.map
        (MvPolynomial.map
          (algebraMap (projectiveChartCoefficientRing j) (Localization.AtPrime p)))
        (projectiveChartGlobalIncidenceIdeal q n z j exponent) =
      projectiveChartBaseChangedIncidenceIdeal q n z j exponent p := by
  classical
  unfold projectiveChartGlobalIncidenceIdeal projectiveChartBaseChangedIncidenceIdeal
  rw [Ideal.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨Q, ⟨b, rfl⟩, rfl⟩
    exact ⟨b, (projectiveChartGlobalRowPolynomial_map_localization
      q n z j exponent p b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨projectiveChartGlobalRowPolynomial q n z j exponent b, ⟨b, rfl⟩,
      projectiveChartGlobalRowPolynomial_map_localization q n z j exponent p b⟩

abbrev projectiveChartBaseChangedGlobalIncidenceRing
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :=
  MvPolynomial (row × Fin n) (Localization.AtPrime p) ⧸
    Ideal.map
      (algebraMap
        (MvPolynomial (row × Fin n) (projectiveChartCoefficientRing j))
        (MvPolynomial (row × Fin n) (Localization.AtPrime p)))
      (projectiveChartGlobalIncidenceIdeal q n z j exponent)

/-- The base-changed chart incidence quotient is the localization of the genuine global chart
incidence ring at the image of the coefficient-prime complement. -/
theorem isLocalization_projectiveChartBaseChangedGlobalIncidenceRing
    {row κ : Type} [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :
    let R := MvPolynomial (row × Fin n) (projectiveChartCoefficientRing j)
    let S := MvPolynomial (row × Fin n) (Localization.AtPrime p)
    let I := projectiveChartGlobalIncidenceIdeal q n z j exponent
    let M := p.primeCompl.map (MvPolynomial.C : projectiveChartCoefficientRing j →+* R)
    letI : CommRing R := chosenMvPolynomialCommRing
    letI : CommRing S := chosenMvPolynomialCommRing
    letI := (localizationQuotientMap (S := S) I).toAlgebra
    IsLocalization (M.map (Ideal.Quotient.mk I))
      (projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p) := by
  dsimp
  apply isLocalization_localizationQuotientMap

end
end GaloisForLFunctions.HTGeometry
