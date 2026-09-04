import GaloisForLFunctions.HTGeometry.ValuationSubringExtension

/-!
# Transcendence detected by a valuation pole

A valuation that is trivial on a coefficient field cannot assign a pole to an element algebraic
over that field.  This is the exact one-step flag principle used when terminal cascade states are
peeled inward: the retained residue field is the coefficient field, while the new terminal state
has negative valuation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- If a valuation ring contains a whole coefficient field, every element outside the valuation
ring is transcendental over that field. -/
theorem transcendental_of_not_mem_valuationSubring
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (A : ValuationSubring K)
    (hF : ∀ c : F, algebraMap F K c ∈ A)
    {x : K} (hx : x ∉ A) :
    Transcendental F x := by
  change ¬ IsAlgebraic F x
  intro halg
  apply hx
  apply ValuationInertia.mem_of_isIntegral A hF
  exact isAlgebraic_iff_isIntegral.mp halg

/-- Contrapositive form: an element algebraic over a valuation-trivial field is integral at every
prolongation of that trivial valuation. -/
theorem mem_valuationSubring_of_isAlgebraic_over_trivial_subfield
    {F K : Type*} [Field F] [Field K] [Algebra F K]
    (A : ValuationSubring K)
    (hF : ∀ c : F, algebraMap F K c ∈ A)
    {x : K} (hx : IsAlgebraic F x) :
    x ∈ A := by
  apply ValuationInertia.mem_of_isIntegral A hF
  exact isAlgebraic_iff_isIntegral.mp hx

end

end GaloisForLFunctions.HTGeometry
