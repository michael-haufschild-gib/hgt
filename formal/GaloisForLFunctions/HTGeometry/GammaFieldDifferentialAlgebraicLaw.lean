import GaloisForLFunctions.HTGeometry.GammaFieldLawInstanceFree
import GaloisForLFunctions.HTGeometry.JetHypertranscendenceBridge
import GaloisForLFunctions.HTGeometry.UpperEndRatfuncDifferentialAlgebra
import GaloisForLFunctions.HTGeometry.VerticalPhaseRank

/-!
# The finite phase law from differential algebraicity alone

The law is stated on the card as an implication about a *function*: a holomorphic, vertically
uniformly almost periodic `Φ` that is differentially algebraic over `ℂ(s)⟨Γ⟩` satisfies an autonomous
algebraic differential equation and has finite rational Bohr frequency rank.  The corpus proves it
from a supplied relation.  Differential algebraicity is by definition the failure of algebraic
independence of the jets, and a failure of algebraic independence *is* such a relation — the support
of a witnessing polynomial gives distinct exponent vectors with nonzero coefficients.  So the law
runs with no relation chosen by hand, and its contrapositive is the hypertranscendence criterion of
the card's §6.
-/

open Filter Set Topology Function
open scoped Differential
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaDALawDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaDALawIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaDALawDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaDALawComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaDALawRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance gammaDALawRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaDALawRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- **The finite phase law from differential algebraicity over the Gamma field.**  A holomorphic
vertically uniformly almost periodic function whose germ is differentially algebraic over
`ℂ(s)⟨Γ⟩` satisfies an autonomous algebraic differential equation on the strip — eq. (8) — and its
vertical Bohr frequency group has finite rank — eq. (9). -/
theorem finite_phase_law_of_differentialAlgebraic {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (hDA : DifferentialAlgebraicOver
      ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
      (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ))
    {f : ℝ →ᵇ ℂ} (hf : ∀ y : ℝ, f y = Φ ((σ : ℂ) + (y : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun y => f y)) (hftb : HasTotallyBoundedOrbit (fun y => f y)) :
    ∃ (n N : ℕ) (e : Fin N → Fin (n + 1) → ℕ) (β : Fin N) (d : Fin N → ℂ),
      0 < N ∧ Function.Injective e ∧ d β = 1
      ∧ (∀ z ∈ verticalStrip σ R,
        jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0)
      ∧ (∑ α : Fin N, MvPolynomial.C (d α)
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℂ) ^ (e α i)) ≠ 0
      ∧ ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  obtain ⟨n, N, e, c, hN, he, hc, hrel⟩ := exists_jet_relation_of_differentialAlgebraic hDA
  obtain ⟨β, d, hdβ, hstrip, hpoly, hrank⟩ :=
    finite_phase_law_of_gammaField_relation' hσ hN hr hρ hrρ hR hΦ hap e he Ψ hΨ
      (fun α => algebraMap
        ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
        upperEndMeroField (c α))
      (fun α => (c α).2) (fun α h0 => hc α (Subtype.ext h0)) hrel hf hfu hftb
  exact ⟨n, N, e, β, d, hN, he, hdβ, hstrip, hpoly, hrank⟩

/-- **The hypertranscendence criterion of §6.**  A holomorphic vertically uniformly almost periodic
function whose vertical Bohr frequency group has infinite rank is hypertranscendental over
`ℂ(s)⟨Γ⟩`: no differential relation over the Gamma field can hold for it. -/
theorem hypertranscendentalOver_gammaField_of_infinite_rank {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    {f : ℝ →ᵇ ℂ} (hf : ∀ y : ℝ, f y = Φ ((σ : ℂ) + (y : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun y => f y)) (hftb : HasTotallyBoundedOrbit (fun y => f y))
    (hrank : ∀ K : ℕ, ¬ Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal)) :
    HypertranscendentalOver
      ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
      (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ) := by
  intro hDA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, K, hK⟩ :=
    finite_phase_law_of_differentialAlgebraic hσ hr hρ hrρ hR hΦ hap Ψ hΨ hDA hf hfu hftb
  exact hrank K hK

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaDAStripDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaDAStripIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaDAStripDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaDAStripComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaDAStripRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance gammaDAStripRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaDAStripRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- **The finite phase law with exactly the card's hypotheses.**  For a function holomorphic on the
vertical strip and uniformly almost periodic there — hypotheses (6) and (7) — differential
algebraicity over `ℂ(s)⟨Γ⟩` gives an autonomous algebraic differential equation on the strip, eq. (8),
and finite rank of the vertical Bohr frequency group of its central-line restriction, eq. (9).  The
line restriction, its uniform continuity and the total boundedness of its orbit are all produced from
the strip hypotheses. -/
theorem finite_phase_law_of_differentialAlgebraic_strip {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (hDA : DifferentialAlgebraicOver
      ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
      (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) :
    ∃ (n N : ℕ) (e : Fin N → Fin (n + 1) → ℕ) (β : Fin N) (d : Fin N → ℂ),
      0 < N ∧ Function.Injective e ∧ d β = 1
      ∧ (∀ z ∈ verticalStrip σ R,
        jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0)
      ∧ (∑ α : Fin N, MvPolynomial.C (d α)
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℂ) ^ (e α i)) ≠ 0
      ∧ ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies (verticalRestriction Φ hR hΦ hap))
          ≤ (K : Cardinal) := by
  have hcont : Continuous fun t : ℝ => (verticalRestriction Φ hR hΦ hap) t :=
    continuous_line_restriction hR hΦ
  have hapline : _root_.HTGeometry.IsBohrAlmostPeriodic fun t : ℝ => (verticalRestriction Φ hR hΦ hap) t :=
    isBohrAlmostPeriodic_line hR hap
  exact finite_phase_law_of_differentialAlgebraic hσ hr hρ hrρ hR hΦ hap Ψ hΨ hDA
    (f := verticalRestriction Φ hR hΦ hap) (verticalRestriction_apply Φ hR hΦ hap)
    (uniformContinuous_of_isBohrAlmostPeriodic hcont hapline)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapline)

/-- **§6 with exactly the card's hypotheses.**  A function holomorphic and uniformly almost periodic
on a vertical strip whose central-line frequency group has infinite rank is hypertranscendental over
`ℂ(s)⟨Γ⟩`. -/
theorem hypertranscendentalOver_gammaField_of_infinite_rank_strip {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (hrank : ∀ K : ℕ, ¬ Module.rank ℤ (bohrHullFrequencies (verticalRestriction Φ hR hΦ hap))
      ≤ (K : Cardinal)) :
    HypertranscendentalOver
      ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
      (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ) := by
  intro hDA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, K, hK⟩ :=
    finite_phase_law_of_differentialAlgebraic_strip hσ hr hρ hrρ hR hΦ hap Ψ hΨ hDA
  exact hrank K hK

end

end GaloisForLFunctions.HTGeometry
