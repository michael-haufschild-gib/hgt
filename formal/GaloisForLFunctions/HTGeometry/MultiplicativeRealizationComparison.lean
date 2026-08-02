import GaloisForLFunctions.HTGeometry.MultipleGammaPhysicalOrderLaw
import GaloisForLFunctions.HTGeometry.MultipleGammaMultiplicativeAnnihilator
import GaloisForLFunctions.HTGeometry.PhysicalArcComparisonCanonicity

/-!
# The multiplicative realization gives the same comparison

The source syntax of the multiple elliptic gamma hierarchy has two analytic realizations: the
additive one, where a difference operator acts on the logarithmic derivative, and the multiplicative
one, where an exponent system produces a finite product of integer powers of structural translates.

Both are classified by the same squarefree ideal.  Consequently the physical comparison built from
either realization is the same: an exponent system is differentially algebraic exactly when its
exponent operator lies in the differential-algebraic translation annihilator of the additive source,
and in that case the operator has the same arc-contact order, the same powered period-incidence
level, and the same polarizing half-density.

The comparison therefore does not depend on which of the two realizations produced it.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators ENNReal

namespace GaloisForLFunctions

open Bottcher HTGeometry VeroneseIdeal

noncomputable section

attribute [local instance] facePacketMeroDecidableEq

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra
  ellipticGammaRationalBaseCoordinateDifferential
  ellipticGammaRationalBaseCoordinateDifferentialAlgebra

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The two realizations share one annihilator -/

/-- Exponent systems whose multiplicative translate product is differentially algebraic. -/
def multiplicativeDaAnnihilator (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) :
    Set ((ι →₀ ℕ) →₀ ℤ) :=
  {c | DifferentialAlgebraicOver (RatFunc ℂ) (translateGammaProduct τ hτ c)}

/-- **The two realizations are classified by the same annihilator.**  A multiplicative translate
product is differentially algebraic exactly when its exponent operator annihilates the additive
source. -/
theorem mem_multiplicativeDaAnnihilator_iff (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (r : ℕ) (hcard : Fintype.card ι = r + 1)
    (c : (ι →₀ ℕ) →₀ ℤ) :
    c ∈ multiplicativeDaAnnihilator τ hτ ↔
      translateProductOperator c ∈ daTranslationAnnihilator τ hτ := by
  rw [multiplicativeDaAnnihilator, Set.mem_setOf_eq,
    differentialAlgebraicOver_translateGammaProduct_iff_mem_veroneseIdeal τ hτ hQ r hcard,
    daTranslationAnnihilator_eq_veroneseIdeal τ hτ hQ r hcard]
  rfl

/-! ## The comparison is realization independent -/

/-- **Realization independence of the physical comparison.**  For an exponent system whose
multiplicative translate product is differentially algebraic, the exponent operator has contact
order at least `r` along the physical exponential arc, its arc image lies at level `r` of the
powered period-incidence filtration, and the polarizing section of that level is the same
half-density `|w|^{r/2}` as for the additive realization. -/
theorem multiplicativeRealization_comparison
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (r : ℕ) (hr : 1 ≤ r) (hcard : Fintype.card ι = r + 1)
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    {c : (ι →₀ ℕ) →₀ ℤ} (hc : c ∈ multiplicativeDaAnnihilator τ hτ) :
    (Polynomial.X : Polynomial ℂ) ^ r ∣ physicalArcPullback τ (translateProductOperator c) ∧
      arcEvalVector L (physicalArcPullback τ (translateProductOperator c)) ∈
        Set.range (poweredPeriodIncidenceMultiplier L r) ∧
      poweredPeriodIncidenceHalfDensity L r ∈
        closure (Set.range (poweredPeriodIncidenceMultiplier L r)) ∧
      poweredPeriodIncidenceHalfDensity L r ∉
        Set.range (poweredPeriodIncidenceMultiplier L r) := by
  have hmem : translateProductOperator c ∈ veroneseIdeal ℂ ι r := by
    have := (mem_multiplicativeDaAnnihilator_iff τ hτ hQ r hcard c).mp hc
    rw [daTranslationAnnihilator_eq_veroneseIdeal τ hτ hQ r hcard] at this
    exact this
  exact ⟨pow_dvd_physicalArcPullback_of_mem_veroneseIdeal τ hmem,
    veroneseIdeal_arcEval_mem_poweredRange L τ hmem,
    (poweredPeriodIncidenceHalfDensity_closureOnly L hL r hr).1,
    (poweredPeriodIncidenceHalfDensity_closureOnly L hL r hr).2⟩

/-- **Both realizations produce the same normalized comparison.**  The additive and the
multiplicative source have literally the same annihilator, and the comparison is the unique algebra
map with the normalization `λ ↦ w`, so the pointed polarized comparison attached to either
realization is the same morphism. -/
theorem realizationIndependent_canonicalComparison
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (r : ℕ) (hcard : Fintype.card ι = r + 1) (L : Submodule ℤ ℂ) :
    (∀ c : (ι →₀ ℕ) →₀ ℤ, c ∈ multiplicativeDaAnnihilator τ hτ ↔
        translateProductOperator c ∈ daTranslationAnnihilator τ hτ) ∧
      (∀ φ : Polynomial ℂ →ₐ[ℂ] lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞,
        φ Polynomial.X = periodWeightVector L → φ = arcEvalHom L) :=
  ⟨mem_multiplicativeDaAnnihilator_iff τ hτ hQ r hcard, arcEvalHom_unique L⟩

end

end GaloisForLFunctions
