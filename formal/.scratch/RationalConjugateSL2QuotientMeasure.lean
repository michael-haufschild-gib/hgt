import GaloisForLFunctions.RHTower.RationalConjugateSL2FiniteCover

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups Pointwise

noncomputable section

/-- A Borel selector for right orbits of the rational-conjugate SL₂ source. -/
noncomputable def rationalConjugateSL2FundamentalSet (N : ℕ) (g : GL (Fin 2) ℚ) : Set SL2R :=
  (exists_measurable_strictDomain_of_discrete_subgroup (rationalConjugateSL2Group N g)).choose

theorem rationalConjugateSL2FundamentalSet_measurable (N : ℕ) (g : GL (Fin 2) ℚ) :
    MeasurableSet (rationalConjugateSL2FundamentalSet N g) :=
  (exists_measurable_strictDomain_of_discrete_subgroup (rationalConjugateSL2Group N g)).choose_spec.1

theorem rationalConjugateSL2FundamentalSet_unique (N : ℕ) (g : GL (Fin 2) ℚ) (x : SL2R) :
    ∃! h : (rationalConjugateSL2Group N g).op,
      h • x ∈ rationalConjugateSL2FundamentalSet N g :=
  (exists_measurable_strictDomain_of_discrete_subgroup (rationalConjugateSL2Group N g)).choose_spec.2 x

theorem rationalConjugateSL2FundamentalSet_isFundamentalDomain (N : ℕ) (g : GL (Fin 2) ℚ) :
    IsFundamentalDomain (rationalConjugateSL2Group N g).op
      (rationalConjugateSL2FundamentalSet N g) realSL2Haar :=
  IsFundamentalDomain.mk'
    (rationalConjugateSL2FundamentalSet_measurable N g).nullMeasurableSet
    (rationalConjugateSL2FundamentalSet_unique N g)

instance rationalConjugateSL2_hasFundamentalDomain (N : ℕ) (g : GL (Fin 2) ℚ) :
    HasFundamentalDomain (rationalConjugateSL2Group N g).op SL2R realSL2Haar :=
  (rationalConjugateSL2FundamentalSet_isFundamentalDomain N g).hasFundamentalDomain realSL2Haar

/-- Haar quotient measure for the determinant-one rational-conjugate source. -/
noncomputable def rationalConjugateSL2QuotientMeasure (N : ℕ) (g : GL (Fin 2) ℚ) :
    Measure (SL2R ⧸ rationalConjugateSL2Group N g) :=
  (realSL2Haar.restrict (rationalConjugateSL2FundamentalSet N g)).map QuotientGroup.mk

instance rationalConjugateSL2QuotientMeasure_projection (N : ℕ) (g : GL (Fin 2) ℚ) :
    QuotientMeasureEqMeasurePreimage realSL2Haar (rationalConjugateSL2QuotientMeasure N g) :=
  (rationalConjugateSL2FundamentalSet_isFundamentalDomain N g).quotientMeasureEqMeasurePreimage_quotientMeasure

instance rationalConjugateSL2QuotientMeasure_invariant (N : ℕ) (g : GL (Fin 2) ℚ) :
    SMulInvariantMeasure SL2R (SL2R ⧸ rationalConjugateSL2Group N g)
      (rationalConjugateSL2QuotientMeasure N g) :=
  QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient realSL2Haar

instance rationalConjugateSL2QuotientMeasure_sigmaFinite (N : ℕ) (g : GL (Fin 2) ℚ) :
    SigmaFinite (rationalConjugateSL2QuotientMeasure N g) :=
  QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient (ν := realSL2Haar)
    (rationalConjugateSL2QuotientMeasure N g)

end

end GaloisForLFunctions.RHTower
