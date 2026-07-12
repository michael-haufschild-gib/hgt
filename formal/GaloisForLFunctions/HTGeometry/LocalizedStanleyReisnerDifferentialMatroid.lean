import GaloisForLFunctions.HTGeometry.StanleyReisnerLaurentRows

/-!
# Localized Stanley--Reisner differential matroid

After clearing one common translation denominator, the resulting finite Laurent facet rows act on
a differentially independent orbit packet.  Their complete nonlinear differential-independence
matroid is exactly the `C[D]`-linear matroid of the Stanley--Reisner numerator classes.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MvPolynomial
open scoped Differential

noncomputable section

/-- **Exact localized Stanley--Reisner differential matroid law.**  The finite Laurent structural
outputs are differentially independent precisely when their common-denominator numerator classes
are linearly independent in the Stanley--Reisner quotient over `C[D]`. -/
theorem differentialIndependent_stanleyReisnerLaurentRows_iff
    {C K α ι : Type*}
    [Field C] [Field K] [Algebra C K] [Differential K]
    [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]
    (hconst : ∀ c : C, (algebraMap C K c)′ = 0)
    (d : translationSubmonoid (Polynomial C) α)
    (facets : Finset (Finset α))
    (N : ι → MvPolynomial α (Polynomial C) ⧸
      stanleyReisnerIdeal (Polynomial C) facets)
    (x : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) → K)
    (hx : DifferentialIndependent C x) :
    DifferentialIndependent C
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) x) ↔
      LinearIndependent (Polynomial C) N := by
  classical
  rw [differentialIndependent_finiteFinsuppOperatorRows_iff hconst
    (stanleyReisnerLaurentRows d facets N) x hx]
  exact linearIndependent_stanleyReisnerLaurentRows_iff d facets N

end

end GaloisForLFunctions.HTGeometry
