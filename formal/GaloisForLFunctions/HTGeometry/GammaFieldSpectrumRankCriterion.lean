import GaloisForLFunctions.HTGeometry.DirichletGammaFieldFieldCoefficients
import GaloisForLFunctions.HTGeometry.InfiniteRankIndependentFamily
import GaloisForLFunctions.HTGeometry.JetHypertranscendenceBridge
import GaloisForLFunctions.HTGeometry.UpperEndRatfuncDifferentialAlgebra

/-!
# The hypertranscendence criterion of §6, from the rank of the spectrum

The frequency-rank exclusion consumes independent families of every size inside the Bohr spectrum.
A set whose rational span has infinite rank contains such families, so the criterion can be stated
with the hypothesis the card uses: *the frequency group has infinite rational rank*.

For a generalized Dirichlet series with distinct exponents, nonzero coefficients and uniform
convergence on the line, each exponent is a spectral frequency — the Bohr coefficient at `−λ_m` is
`a_m·e^{−λ_m σ}` — so the criterion applies to the exponent group directly: equations (30) and (31).
-/

open Filter Set Topology Function
open scoped Differential
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance gammaSpecDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaSpecIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaSpecDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaSpecComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaSpecRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance gammaSpecRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gammaSpecRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

/-- **§6 from the rank of a set of frequencies.**  If some subset of the Bohr spectrum has infinite
rational rank, the function is hypertranscendental over `ℂ(s)⟨Γ⟩`. -/
theorem hypertranscendentalOver_gammaField_of_infinite_spectrum_rank {σ R : ℝ} (hσ : 0 < σ)
    (hR : 0 < R) {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter Φ)
    {S : Set ℝ} (hS : S ⊆ bohrSpectrum fun t : ℝ => Φ ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hrank : ∀ m : ℕ, ¬ Module.rank ℚ ↥(Submodule.span ℚ S) ≤ (m : Cardinal)) :
    HypertranscendentalOver
      ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
      (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ) := by
  refine hypertranscendentalOver_of_no_jet_relation ?_
  intro n N hN e he c hc
  refine no_gammaField_field_relation_of_independent_spectrum_line hσ hR hΦ hap ?_ hN e he Ψ hΨ
    (fun α => algebraMap
      ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
      upperEndMeroField (c α))
    (fun α => (c α).2) (fun α h0 => hc α (Subtype.ext h0))
  intro L
  obtain ⟨ν, hind, hmem⟩ :=
    exists_independent_family_of_infinite_rank (K := ℚ) (S := S) hrank (L + 1)
  exact ⟨ν, hind, fun i => hS (hmem i)⟩

/-- Each exponent of a uniformly convergent generalized Dirichlet series is a spectral frequency. -/
theorem neg_lam_mem_bohrSpectrum {σ : ℝ} {D : ℂ → ℂ} (a : ℕ → ℂ) (lam : ℕ → ℝ)
    (hinj : Function.Injective lam)
    (hDc : Continuous fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hDa : _root_.HTGeometry.IsBohrAlmostPeriodic
      fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I))
    (m : ℕ) (ham : a m ≠ 0)
    (hm : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, m < n₀ ∧ ∀ t : ℝ,
      ‖D ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ∑ k ∈ Finset.range n₀,
          a k * Complex.exp (-(lam k : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε) :
    -(lam m) ∈ bohrSpectrum fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  have hcoeff := bohrCoefficient_dirichlet_line a lam D hinj hDc hDa m hm
  show bohrCoefficient _ _ ≠ 0
  rw [hcoeff]
  exact mul_ne_zero ham (by simp)

/-- **Equations (30) and (31).**  A generalized Dirichlet series with pairwise distinct exponents,
nonzero coefficients, uniform convergence on the line, and an exponent group of infinite rational
rank is hypertranscendental over `ℂ(s)⟨Γ⟩`. -/
theorem hypertranscendentalOver_gammaField_of_dirichlet {σ R : ℝ} (hσ : 0 < σ) (hR : 0 < R)
    {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic D σ R)
    (Ψ : upperEndAnalyticSubring)
    (hΨ : upperEndAnalyticSubring.subtype Ψ = Germ.coeRingHom upperEndFilter D)
    (a : ℕ → ℂ) (lam : ℕ → ℝ) (hinj : Function.Injective lam) (ha : ∀ m, a m ≠ 0)
    (hconv : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, m < n₀ ∧ ∀ t : ℝ,
      ‖D ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ∑ k ∈ Finset.range n₀,
          a k * Complex.exp (-(lam k : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε)
    (hrank : ∀ m : ℕ,
      ¬ Module.rank ℚ ↥(Submodule.span ℚ (Set.range fun k : ℕ => -(lam k))) ≤ (m : Cardinal)) :
    HypertranscendentalOver
      ↥(differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
      (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ) := by
  have hDc : Continuous fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    continuous_line_restriction hR hD
  have hDa : _root_.HTGeometry.IsBohrAlmostPeriodic
      fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I) := isBohrAlmostPeriodic_line hR hap
  refine hypertranscendentalOver_gammaField_of_infinite_spectrum_rank hσ hR hD hap Ψ hΨ
    (S := Set.range fun k : ℕ => -(lam k)) ?_ hrank
  rintro y ⟨k, rfl⟩
  exact neg_lam_mem_bohrSpectrum a lam hinj hDc hDa k (ha k) (hconv k)

end

end GaloisForLFunctions.HTGeometry
