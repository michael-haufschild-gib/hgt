import GaloisForLFunctions.HTGeometry.GammaFieldCoefficientLaw

/-!
# The finite phase law with no ambient measurable structure

The rank statements of the phase law are proved through Peter–Weyl on the hull, and the Haar-measure
argument there carries a Borel structure on the hull as an instance hypothesis.  That structure is
never an assumption about the problem: every topological space carries its Borel σ-algebra.  Choosing
it inside the proof removes the two instance hypotheses from the statements, leaving the law with
hypotheses about the function and the relation only.
-/

open Filter Set Topology Function
open scoped Differential
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance instFreeLawDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance instFreeLawIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance instFreeLawDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance instFreeLawComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance instFreeLawRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- **The finite phase law from a relation in the Gamma field**, with no instance hypotheses. -/
theorem finite_phase_law_of_gammaField_relation' {n N : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hN : 0 < N) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (x : Fin N → upperEndMeroField)
    (hxmem : ∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : ∀ α, x α ≠ 0)
    (hrel : ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
      (differentialJet (i : ℕ)
        (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) ^ (e α i) = 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ y : ℝ, f y = Φ ((σ : ℂ) + (y : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun y => f y)) (hftb : HasTotallyBoundedOrbit (fun y => f y)) :
    ∃ (β : Fin N) (d : Fin N → ℂ), d β = 1
      ∧ (∀ z ∈ verticalStrip σ R,
        jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0)
      ∧ (∑ α : Fin N, MvPolynomial.C (d α)
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℂ) ^ (e α i)) ≠ 0
      ∧ ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  exact finite_phase_law_of_gammaField_relation hσ hN hr hρ hrρ hR hΦ hap e he Ψ hΨ x hxmem hx0
    hrel hf hfu hftb

/-- **The finite phase law from a relation in the analytic carrier**, with no instance
hypotheses. -/
theorem finite_phase_law_of_gammaField_carrier_relation' {n N : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hN : 0 < N) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (F : Fin N → ℂ → ℂ) (W : Fin N → upperEndAnalyticSubring)
    (hWgerm : ∀ α, upperEndAnalyticSubring.subtype (W α)
      = Germ.coeRingHom upperEndFilter (F α))
    (hWmem : ∀ α, algebraMap upperEndAnalyticSubring upperEndMeroField (W α)
      ∈ differentialJetAlgebra (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hW0 : ∀ α, W α ≠ 0)
    (hrel : ∑ α : Fin N, W α
      * ∏ i : Fin (n + 1), (upperEndAnalyticDeriv^[(i : ℕ)] Ψ) ^ (e α i) = 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ y : ℝ, f y = Φ ((σ : ℂ) + (y : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun y => f y)) (hftb : HasTotallyBoundedOrbit (fun y => f y)) :
    ∃ (β : Fin N) (d : Fin N → ℂ), d β = 1
      ∧ (∀ z ∈ verticalStrip σ R,
        jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0)
      ∧ (∑ α : Fin N, MvPolynomial.C (d α)
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℂ) ^ (e α i)) ≠ 0
      ∧ ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  exact finite_phase_law_of_gammaField_carrier_relation hσ hN hr hρ hrρ hR hΦ hap e he Ψ hΨ F W
    hWgerm hWmem hW0 hrel hf hfu hftb

end

end GaloisForLFunctions.HTGeometry
