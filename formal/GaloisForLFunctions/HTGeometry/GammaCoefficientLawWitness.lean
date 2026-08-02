import GaloisForLFunctions.HTGeometry.GammaFieldLawInstanceFree
import GaloisForLFunctions.HTGeometry.GammaRationalWitness
import GaloisForLFunctions.HTGeometry.GammaDatumValuation

/-!
# The law is inhabited with coefficients that are not Gamma-rational

The exponential witnesses the law with constant coefficients, which lie in the digamma field.  Scaling
the relation by `Γ` keeps it a relation and moves the coefficients out of that field: `Γ·Φ′ − μΓ·Φ = 0`
has coefficients of `Γ`-exponent `1`.

So the general form of the law — coefficients anywhere in `ℂ(s)⟨Γ⟩` — is not a restatement of the
constant-coefficient form: its hypothesis class contains instances at every abscissa whose
coefficients have nonzero exponential valuation.
-/

open Filter Topology Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry
open GaloisForLFunctions.HTGeometry

noncomputable section

local instance gammaWitDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance gammaWitIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance gammaWitDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance gammaWitComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance gammaWitRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- The exponential, as an upper-end analytic germ. -/
def expLineUpperAnalytic (μ : ℝ) : upperEndAnalyticSubring :=
  ⟨Germ.coeRingHom upperEndFilter (expLine μ),
    ⟨expLine μ, 0, DifferentiableOn.analyticOnNhd (differentiable_expLine μ).differentiableOn
      (isOpen_upperTail 0), rfl⟩⟩

theorem expLineUpperAnalytic_subtype (μ : ℝ) :
    upperEndAnalyticSubring.subtype (expLineUpperAnalytic μ)
      = Germ.coeRingHom upperEndFilter (expLine μ) := rfl

/-- The exponential solves its first-order equation in the analytic carrier. -/
theorem upperEndAnalyticDeriv_expLineUpperAnalytic (μ : ℝ) :
    upperEndAnalyticDeriv (expLineUpperAnalytic μ)
      = upperEndPolyToAnalytic (Polynomial.C (μ : ℂ)) * expLineUpperAnalytic μ := by
  refine Subtype.ext ?_
  show upperEndGermDeriv ((expLine μ : ℂ → ℂ) : Germ upperEndFilter ℂ)
    = ((fun z : ℂ => (Polynomial.C (μ : ℂ)).eval z : ℂ → ℂ) : Germ upperEndFilter ℂ)
      * ((expLine μ : ℂ → ℂ) : Germ upperEndFilter ℂ)
  rw [upperEndGermDeriv_coe]
  have hfun : deriv (expLine μ) = fun z : ℂ => (Polynomial.C (μ : ℂ)).eval z * expLine μ z := by
    funext z
    rw [deriv_expLine, Polynomial.eval_C]
  rw [hfun]
  rfl

/-- The exponential's first jet in the field is `μ` times itself. -/
theorem differentialJet_one_expLine (μ : ℝ) :
    differentialJet 1 (algebraMap upperEndAnalyticSubring upperEndMeroField
        (expLineUpperAnalytic μ))
      = upperEndComplexToMero (μ : ℂ) * algebraMap upperEndAnalyticSubring upperEndMeroField
        (expLineUpperAnalytic μ) := by
  rw [GaloisForLFunctions.HTGeometry.differentialJet_algebraMap 1 (expLineUpperAnalytic μ),
    Function.iterate_one, upperEndAnalyticDeriv_expLineUpperAnalytic, map_mul]
  rfl

/-- A nonzero constant has the trivial datum. -/
theorem hasGammaDatum_const {σ : ℝ} {c : ℂ} (hc : c ≠ 0) :
    HasGammaDatum σ (upperEndComplexToMero c) 0 0 0 c := by
  refine ⟨hc, fun _ => c, ?_, ?_⟩
  · have hrep := representsOnLine_algebraMap (σ := σ) (upperEndPolyToAnalytic (Polynomial.C c))
      (fun z : ℂ => (Polynomial.C c).eval z) (polyToAnalytic_subtype _)
    have hval : (fun t : ℝ => (Polynomial.C c).eval ((σ : ℂ) + (t : ℂ) * Complex.I))
        = fun _ : ℝ => c := by
      funext t
      rw [Polynomial.eval_C]
    rw [hval] at hrep
    exact hrep
  · refine tendsto_const_nhds.congr fun t => ?_
    rw [gammaShapeZ]
    simp

/-- The constant is a member of the Gamma field. -/
theorem upperEndComplexToMero_mem_gammaAdjoin (c : ℂ) :
    upperEndComplexToMero c ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField) := by
  have himg : upperEndComplexToMero c
      = algebraMap (RatFunc ℂ) upperEndMeroField
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c)) := by
    show upperEndComplexToMero c
      = upperEndRatfuncToMero (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c))
    rw [upperEndRatfuncToMero_algebraMap_polynomial]
    rfl
  rw [himg]
  exact IntermediateField.algebraMap_mem _ _

theorem upperEndComplexToMero_ne_zero {c : ℂ} (hc : c ≠ 0) : upperEndComplexToMero c ≠ 0 := by
  intro h0
  have hpoly : upperEndPolyToMero (Polynomial.C c) = 0 := h0
  have hC : (Polynomial.C c : Polynomial ℂ) = 0 :=
    upperEndPolyToMero_injective (by rw [hpoly, map_zero])
  exact hc (Polynomial.C_eq_zero.mp hC)

/-- An element with `Γ`-exponent `1` is not in the digamma field. -/
theorem not_mem_digammaAdjoin_of_gammaExponent_one {σ : ℝ} (hσ : 0 < σ) {x : upperEndMeroField}
    (hx0 : x ≠ 0) {a b : ℤ} {c : ℂ} (h : HasGammaDatum σ x 1 a b c) :
    x ∉ differentialAdjoin (RatFunc ℂ) ({digammaMero} : Set upperEndMeroField) := by
  intro hmem
  obtain ⟨a', b', c', hdat⟩ := exists_hasGammaDatum_digammaField hσ hmem hx0
  obtain ⟨h1, -, -, -⟩ := hasGammaDatum_unique hσ h hdat
  exact absurd h1 one_ne_zero

/-- **The finite phase law is inhabited with coefficients of nonzero `Γ`-exponent.**  The exponential
`e^{μ z}` satisfies the relation `Γ·Φ′ − μΓ·Φ = 0`, whose two coefficients lie in `ℂ(s)⟨Γ⟩`, have
`Γ`-exponent `1`, and therefore lie outside the digamma field; the law returns a rank between `1` and
a finite bound. -/
theorem gammaField_law_witness_gamma_coefficients {σ : ℝ} (hσ : 0 < σ) (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ x : Fin 2 → upperEndMeroField,
      (∀ α, x α ∈ differentialAdjoin (RatFunc ℂ)
        ({gammaUpperMero} : Set upperEndMeroField)) ∧
      (∀ α, x α ≠ 0) ∧
      (∀ α, ∃ c : ℂ, HasGammaDatum σ (x α) 1 0 0 c) ∧
      (∀ α, x α ∉ differentialAdjoin (RatFunc ℂ)
        ({digammaMero} : Set upperEndMeroField)) ∧
      ∃ K : ℕ, 1 ≤ Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ))
        ∧ Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) ≤ (K : Cardinal) := by
  classical
  set Ψ : upperEndAnalyticSubring := expLineUpperAnalytic μ with hΨdef
  have hμC : (-(μ : ℂ)) ≠ 0 := by
    simpa using hμ
  set x0 : upperEndMeroField := gammaUpperMero with hx0def
  set x1 : upperEndMeroField := upperEndComplexToMero (-(μ : ℂ)) * gammaUpperMero with hx1def
  set x : Fin 2 → upperEndMeroField := ![x0, x1] with hxdef
  have hcases : ∀ α : Fin 2, α = 0 ∨ α = 1 := by decide
  have hx0v : x 0 = x0 := by simp [hxdef]
  have hx1v : x 1 = x1 := by simp [hxdef]
  -- the data of the two coefficients
  have hdat : ∀ α, ∃ c : ℂ, HasGammaDatum σ (x α) 1 0 0 c := by
    intro α
    rcases hcases α with hα | hα <;> subst hα
    · refine ⟨1, ?_⟩
      rw [hx0v, hx0def]
      exact hasGammaDatum_gammaUpperMero hσ
    · refine ⟨(-(μ : ℂ)) * 1, ?_⟩
      rw [hx1v, hx1def]
      have h := (hasGammaDatum_const (σ := σ) hμC).mul hσ (hasGammaDatum_gammaUpperMero hσ)
      simpa only [zero_add, add_zero] using h
  have hmem : ∀ α : Fin 2, x α ∈ differentialAdjoin (RatFunc ℂ)
      ({gammaUpperMero} : Set upperEndMeroField) := by
    intro α
    rcases hcases α with hα | hα <;> subst hα
    · rw [hx0v, hx0def]
      exact subset_differentialAdjoin (RatFunc ℂ) _ (Set.mem_singleton _)
    · rw [hx1v, hx1def]
      exact mul_mem (upperEndComplexToMero_mem_gammaAdjoin _)
        (subset_differentialAdjoin (RatFunc ℂ) _ (Set.mem_singleton _))
  have hne : ∀ α : Fin 2, x α ≠ 0 := by
    intro α
    rcases hcases α with hα | hα <;> subst hα
    · rw [hx0v, hx0def]
      exact gammaUpperMero_ne_zero
    · rw [hx1v, hx1def]
      exact mul_ne_zero (upperEndComplexToMero_ne_zero hμC) gammaUpperMero_ne_zero
  refine ⟨x, hmem, hne, hdat, ?_, ?_⟩
  · intro α
    obtain ⟨c, hc⟩ := hdat α
    exact not_mem_digammaAdjoin_of_gammaExponent_one hσ (hne α) hc
  -- the law applies to the scaled relation
  set f : ℝ →ᵇ ℂ := expLineBC μ σ with hfdef
  have hR : (0 : ℝ) < 1 := one_pos
  have hΦ : DifferentiableOn ℂ (expLine μ) (verticalStrip σ 1) :=
    (differentiable_expLine μ).differentiableOn
  have hap : IsStripAlmostPeriodic (expLine μ) σ 1 := isStripAlmostPeriodic_expLine μ _ _
  set e : Fin 2 → Fin 2 → ℕ := ![![0, 1], ![1, 0]] with hedef
  have he : Function.Injective e := by
    intro α β hαβ
    fin_cases α <;> fin_cases β <;> simp_all
  have hrel : ∑ α : Fin 2, x α * ∏ i : Fin 2,
      (differentialJet (i : ℕ)
        (algebraMap upperEndAnalyticSubring upperEndMeroField Ψ)) ^ (e α i) = 0 := by
    rw [Fin.sum_univ_two]
    simp only [hedef, hxdef, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, mul_one]
    rw [hΨdef, differentialJet_one_expLine, differentialJet_zero, hx0def, hx1def, map_neg]
    ring
  have hf : ∀ y : ℝ, f y = expLine μ ((σ : ℂ) + (y : ℂ) * Complex.I) := by
    intro y
    rw [hfdef, expLineBC_apply]
  have hline : IsBohrAlmostPeriodic
      (fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    isBohrAlmostPeriodic_line hR hap
  have hcont : Continuous (fun y : ℝ => f y) := by
    have hfun : (fun y : ℝ => f y)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact continuous_line_restriction hR hΦ
  have hapf : IsBohrAlmostPeriodic (fun y : ℝ => f y) := by
    have hfun : (fun y : ℝ => f y)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact hline
  obtain ⟨-, -, -, -, -, K, hK⟩ := finite_phase_law_of_gammaField_relation' (rr := 1/4) (ρ := 1/4)
    hσ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hR hΦ hap e he Ψ rfl x
    hmem hne hrel hf (uniformContinuous_of_isBohrAlmostPeriodic hcont hapf)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapf)
  exact ⟨K, one_le_rank_expLineBC μ hμ σ, hK⟩

end

end GaloisForLFunctions
