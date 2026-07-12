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
    (x : FiniteFinsuppRowIndex
      (fun i => stanleyReisnerFacetTranslationCoordinates facets (N i)) → K)
    (hx : DifferentialIndependent C x) :
    DifferentialIndependent C
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows
            (fun i => stanleyReisnerFacetTranslationCoordinates facets (N i))) x) ↔
      LinearIndependent (Polynomial C) N := by
  classical
  rw [differentialIndependent_finiteFinsuppOperatorRows_iff hconst
    (fun i => stanleyReisnerFacetTranslationCoordinates facets (N i)) x hx]
  exact linearIndependent_stanleyReisnerFacetTranslationCoordinates_iff facets N

end

end GaloisForLFunctions.HTGeometry
