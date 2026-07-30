import GaloisForLFunctions.HTGeometry.FacetTranslationCoordinates

/-!
# Stanley--Reisner numerator differential matroid

For a finite family of classes in a Stanley--Reisner quotient over `C[D]`, complete facet
restriction followed by the coordinate change `x_v = t_v - 1` produces finite polynomial
differential-operator rows.  Acting on a differentially independent orbit packet realizes exactly
the original Stanley--Reisner linear matroid, with no additional nonlinear differential circuits.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial
open scoped Differential

noncomputable section

/-- Finitely supported coefficient rows of complete facet translation coordinates.

`MvPolynomial` is represented by `AddMonoidAlgebra`; extracting its coefficient Finsupp makes the
finite operator support explicit. -/
def stanleyReisnerNumeratorRows
    {C α ι : Type*} [Field C] [DecidableEq α]
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial C) ⧸
      stanleyReisnerIdeal (Polynomial C) facets) :
    ι → (F : facets) → (α →₀ ℕ) →₀ Polynomial C :=
  fun i F => AddMonoidAlgebra.coeff
    (stanleyReisnerFacetTranslationCoordinates facets (N i) F)

/-- **Exact Stanley--Reisner numerator matroid law.**  The structural outputs attached to a finite
family of Stanley--Reisner numerator classes are differentially independent exactly when those
classes are linearly independent over `C[D]`. -/
theorem differentialIndependent_stanleyReisnerNumeratorRows_iff
    {C K α ι : Type*}
    [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial C) ⧸
      stanleyReisnerIdeal (Polynomial C) facets)
    (x : FiniteFinsuppRowIndex (stanleyReisnerNumeratorRows facets N) → K)
    (hx : DifferentialIndependent C x) :
    DifferentialIndependent C
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerNumeratorRows facets N)) x) ↔
      LinearIndependent (Polynomial C) N := by
  classical
  rw [differentialIndependent_finiteFinsuppOperatorRows_iff hconst
    (stanleyReisnerNumeratorRows facets N) x hx]
  rw [← linearIndependent_stanleyReisnerFacetTranslationCoordinates_iff facets N]
  let e :
      ((F : facets) → MvPolynomial α (Polynomial C)) ≃ₗ[Polynomial C]
        ((F : facets) → (α →₀ ℕ) →₀ Polynomial C) :=
    LinearEquiv.piCongrRight fun _ =>
      AddMonoidAlgebra.coeffLinearEquiv (Polynomial C)
  have hrows :
      stanleyReisnerNumeratorRows facets N =
        e ∘ ((stanleyReisnerFacetTranslationCoordinates facets) ∘ N) := by
    rfl
  rw [hrows]
  constructor
  · intro h
    exact h.of_comp e.toLinearMap
  · intro h
    exact h.map' e.toLinearMap
      (LinearMap.ker_eq_bot.mpr e.injective)

end

end GaloisForLFunctions.HTGeometry
