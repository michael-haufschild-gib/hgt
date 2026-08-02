import GaloisForLFunctions.HTGeometry.GammaFieldLawInstanceFree
import GaloisForLFunctions.HTGeometry.IndependentFrequencyRank
import GaloisForLFunctions.HTGeometry.DirichletStripAlmostPeriodic
import GaloisForLFunctions.HTGeometry.VerticalPhaseRank

/-!
# Dirichlet series with independent exponents, over the Gamma field

The finite phase law bounds the frequency rank of any solution of a relation with coefficients in
`ℂ(s)⟨Γ⟩`.  A function whose frequency rank exceeds every natural number therefore satisfies no such
relation, and a Dirichlet series whose exponents contain arbitrarily large `ℤ`-independent families
with nonvanishing coefficients has exactly that property.

This is the corpus's `dirichlet_no_gammaField_relation` with the coefficients freed: there they are
elements presented by explicit Gamma-jet data with a dominance hypothesis, here they are arbitrary
nonzero elements of the differential field.
-/

open Filter Set Topology Function

open scoped Differential

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance dirFieldDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance dirFieldIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance dirFieldDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance dirFieldComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance dirFieldRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- **Infinite frequency rank excludes a Gamma-field relation.**  If the frequency rank of the line
restriction exceeds every natural number, no relation with coefficients in `ℂ(s)⟨Γ⟩` holds. -/
theorem no_gammaField_field_relation_of_infinite_rank {σ R : ℝ} (hσ : 0 < σ) (hR : 0 < R)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ y : ℝ, f y = Φ ((σ : ℂ) + (y : ℂ) * Complex.I))
    (hfu : UniformContinuous fun y => f y) (hftb : HasTotallyBoundedOrbit fun y => f y)
    (hinf : ∀ K : ℕ, ¬ (Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal)))
    {n N : ℕ} (hN : 0 < N) (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (x : Fin N → upperEndMeroField)
    (hxmem : ∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : ∀ α, x α ≠ 0) :
    ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
        (differentialJet (i : ℕ)
          (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) ^ (e α i)
      ≠ 0 := by
  intro hrel
  obtain ⟨_, _, _, _, _, K, hK⟩ := finite_phase_law_of_gammaField_relation' hσ hN
    (show (0 : ℝ) < R / 4 by linarith) (show (0 : ℝ) < R / 4 by linarith)
    (show R / 4 + R / 4 < R by linarith) hR hΦ hap e he Ψ hΨ x hxmem hx0 hrel hf hfu hftb
  exact hinf K hK

/-- **A Dirichlet series with exponents of infinite rank has no Gamma-field relation**, with the
coefficients arbitrary nonzero elements of `ℂ(s)⟨Γ⟩`.  Uniform convergence on the strip supplies the
almost periodicity, and each `K+1`-element independent family of exponents with nonvanishing
coefficients pushes the frequency rank past `K`. -/
theorem dirichlet_no_gammaField_field_relation {σ R : ℝ} (hσ : 0 < σ) (hR : 0 < R)
    (a : ℕ → ℂ) (lam : ℕ → ℝ) (D : ℂ → ℂ) (hinj : Function.Injective lam)
    (hD : DifferentiableOn ℂ D (verticalStrip σ R))
    (hconv : ∀ r' : ℝ, r' < R → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ z ∈ closedStrip σ r',
      ‖D z - ∑ i ∈ Finset.range n₀, a i * Complex.exp (-(lam i : ℂ) * z)‖ ≤ ε)
    {f : ℝ →ᵇ ℂ} (hf : ∀ y : ℝ, f y = D ((σ : ℂ) + (y : ℂ) * Complex.I))
    (hrank : ∀ K : ℕ, ∃ idx : Fin (K + 1) → ℕ, (∀ i, a (idx i) ≠ 0) ∧
      (∀ i : Fin (K + 1), ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, idx i < n₀ ∧ ∀ t : ℝ,
        ‖D ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ∑ i' ∈ Finset.range n₀,
            a i' * Complex.exp (-(lam i' : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε) ∧
      LinearIndependent ℤ (fun i : Fin (K + 1) => -(lam (idx i))))
    {n N : ℕ} (hN : 0 < N) (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter D)
    (x : Fin N → upperEndMeroField)
    (hxmem : ∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : ∀ α, x α ≠ 0) :
    ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
        (differentialJet (i : ℕ)
          (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) ^ (e α i)
      ≠ 0 := by
  have hap : IsStripAlmostPeriodic D σ R := isStripAlmostPeriodic_dirichlet a lam D hconv
  have hDa : _root_.HTGeometry.IsBohrAlmostPeriodic
      fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I) := isBohrAlmostPeriodic_line hR hap
  have hfun : (fun y : ℝ => (f y : ℂ))
      = fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
  have hcont : Continuous fun y : ℝ => (f y : ℂ) := f.continuous
  have hfap : _root_.HTGeometry.IsBohrAlmostPeriodic fun y : ℝ => (f y : ℂ) := by
    rw [hfun]
    exact hDa
  have hfu : UniformContinuous fun y : ℝ => (f y : ℂ) :=
    uniformContinuous_of_isBohrAlmostPeriodic hcont hfap
  have hftb : HasTotallyBoundedOrbit fun y : ℝ => (f y : ℂ) :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hfap
  have hinf : ∀ K : ℕ, ¬ (Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal)) := by
    intro K
    obtain ⟨idx, ha, hm, hind⟩ := hrank K
    exact not_rank_le_of_dirichlet_independent a lam D hinj hf hDa K idx ha hm hind
  exact no_gammaField_field_relation_of_infinite_rank hσ hR hD hap hf hfu hftb hinf hN e he Ψ hΨ x
    hxmem hx0

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance specExclDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance specExclIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance specExclDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance specExclComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance specExclRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- A rationally independent family of reals is integrally independent. -/
theorem linearIndependent_int_of_rat {ι : Type*} {v : ι → ℝ} (h : LinearIndependent ℚ v) :
    LinearIndependent ℤ v := by
  refine h.restrict_scalars ?_
  intro u w huw
  have h' : ((u : ℚ)) = ((w : ℚ)) := by simpa [zsmul_eq_mul] using huw
  exact_mod_cast h'

/-- **Arbitrarily many independent Bohr–Fourier frequencies exclude a Gamma-field relation.**  The
hypothesis is stated on the spectrum itself: if for every `K` the Bohr–Fourier expansion of the line
restriction carries `K + 1` rationally independent frequencies, then no relation with coefficients in
`ℂ(s)⟨Γ⟩` holds. -/
theorem no_gammaField_field_relation_of_independent_spectrum {σ R : ℝ} (hσ : 0 < σ) (hR : 0 < R)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ y : ℝ, f y = Φ ((σ : ℂ) + (y : ℂ) * Complex.I))
    (hspec : ∀ K : ℕ, ∃ ν : Fin (K + 1) → ℝ, LinearIndependent ℚ ν ∧
      ∀ i, ν i ∈ bohrSpectrum fun y : ℝ => (f y : ℂ))
    {n N : ℕ} (hN : 0 < N) (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (x : Fin N → upperEndMeroField)
    (hxmem : ∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : ∀ α, x α ≠ 0) :
    ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
        (differentialJet (i : ℕ)
          (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) ^ (e α i)
      ≠ 0 := by
  have hfun : (fun y : ℝ => (f y : ℂ))
      = fun t : ℝ => Φ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
  have hcont : Continuous fun y : ℝ => (f y : ℂ) := f.continuous
  have hfap : _root_.HTGeometry.IsBohrAlmostPeriodic fun y : ℝ => (f y : ℂ) := by
    rw [hfun]
    exact isBohrAlmostPeriodic_line hR hap
  have hfu : UniformContinuous fun y : ℝ => (f y : ℂ) :=
    uniformContinuous_of_isBohrAlmostPeriodic hcont hfap
  have hftb : HasTotallyBoundedOrbit fun y : ℝ => (f y : ℂ) :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hfap
  have hinf : ∀ K : ℕ, ¬ (Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal)) := by
    intro K
    obtain ⟨ν, hνind, hνmem⟩ := hspec K
    refine not_rank_le_of_independent_frequencies K ν (fun i => ?_)
      (linearIndependent_int_of_rat hνind)
    exact bohrSpectrum_subset_bohrHullFrequencies hfap (hνmem i)
  exact no_gammaField_field_relation_of_infinite_rank hσ hR hΦ hap hf hfu hftb hinf hN e he Ψ hΨ x
    hxmem hx0

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance specLineDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance specLineIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance specLineDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance specLineComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance specLineRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- **The spectral exclusion criterion for the line restriction itself.**  No bundled restriction and
no auxiliary analytic hypotheses: strip almost periodicity supplies them. -/
theorem no_gammaField_field_relation_of_independent_spectrum_line {σ R : ℝ} (hσ : 0 < σ)
    (hR : 0 < R) {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R)
    (hspec : ∀ K : ℕ, ∃ ν : Fin (K + 1) → ℝ, LinearIndependent ℚ ν ∧
      ∀ i, ν i ∈ bohrSpectrum fun t : ℝ => Φ ((σ : ℂ) + (t : ℂ) * Complex.I))
    {n N : ℕ} (hN : 0 < N) (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    (x : Fin N → upperEndMeroField)
    (hxmem : ∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : ∀ α, x α ≠ 0) :
    ∑ α : Fin N, x α * ∏ i : Fin (n + 1),
        (differentialJet (i : ℕ)
          (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) ^ (e α i)
      ≠ 0 := by
  have hf : ∀ y : ℝ, (verticalRestriction Φ hR hΦ hap) y
      = Φ ((σ : ℂ) + (y : ℂ) * Complex.I) := verticalRestriction_apply Φ hR hΦ hap
  have hfun : (fun y : ℝ => ((verticalRestriction Φ hR hΦ hap) y : ℂ))
      = fun t : ℝ => Φ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
  refine no_gammaField_field_relation_of_independent_spectrum hσ hR hΦ hap hf ?_ hN e he Ψ hΨ x
    hxmem hx0
  intro K
  obtain ⟨ν, hνind, hνmem⟩ := hspec K
  refine ⟨ν, hνind, fun i => ?_⟩
  rw [hfun]
  exact hνmem i

end

end GaloisForLFunctions.HTGeometry
