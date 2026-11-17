import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.SubexponentialThickTailGivesTheAbscissaLaw
import GaloisForLFunctions.ExclusionOfTheCriticalState.Energy.TheChargeHyperplaneHasItsOwnCriticalRatio

/-!
# Stage 2 in thick-lag form

Stage 2 of ECS is B13: finitely many zeros off the line force none. In the finite stratum the zeros
approach the line, so RH is the asymptotic abscissa law there, and the thick-set receivers for that
law (`asymptoticAbscissaLaw_of_subexponential_thickLeft`,
`asymptoticAbscissaLaw_of_thick_heatedState_bound`) read it off the decay of the critical state.
B13 becomes a statement about the state alone:

* `b13_iff_criticalState_subexponential_thickLeft`: B13 holds iff, whenever only finitely many
  zeros lie off the line, every critical state has `F(u) e^{−8u}` subexponential almost
  everywhere on a set thick toward `−∞` (one set for each exponent).
* `b13_iff_criticalState_thick_heated_bound`: the same with the heated confined state along a thick
  set of levels of one tower.

Off RH a state exists, so under a finite layer B13 fails exactly when some critical state grows
exponentially relative to `e^{8u}` on every set thick toward `−∞`.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations InfiniteRankWeilTheory

/-- RH from the abscissa law in the finite stratum. -/
theorem riemannHypothesis_of_finiteOffLine_of_asymptoticAbscissaLaw (hfin : FiniteOffLine)
    (hAAL : _root_.RHTower.AsymptoticAbscissaLaw) : RiemannHypothesis :=
  _root_.RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
    ⟨zerosApproachLine_of_finiteOffLine hfin, hAAL⟩

/-- **Stage 2 in thick-lag form.** B13 holds iff, in the finite stratum, every critical state has
`F(u) e^{−8u}` subexponential almost everywhere on sets thick toward `−∞`. -/
theorem b13_iff_criticalState_subexponential_thickLeft :
    (FiniteOffLine → RiemannHypothesis) ↔
      (FiniteOffLine → ∀ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ →
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) →
        IsCriticalHalfLineGroundState W₀ F →
        ∀ a : ℝ, 0 < a → ∃ (E : Set ℝ) (C : ℝ), ThickLeft E ∧
          ∀ᵐ u ∂volume, u ∈ E → |F u * Real.exp (-(8 * u))| ≤ C * Real.exp (-(a * u))) := by
  constructor
  · intro h hfin W₀ F _ ht _
    exact absurd (h hfin) (not_riemannHypothesis_of_windowThreshold_eq ht)
  · intro h hfin
    rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
    · exact hRH
    · exact riemannHypothesis_of_finiteOffLine_of_asymptoticAbscissaLaw hfin
        (asymptoticAbscissaLaw_of_subexponential_thickLeft hW ht hF (h hfin W₀ F hW ht hF))

/-- **Stage 2 in heated thick-lag form.** B13 holds iff, in the finite stratum, every critical state
has a base `ℓ > 0` at which its heated confined state grows subexponentially along thick sets of
levels at every heat time. -/
theorem b13_iff_criticalState_thick_heated_bound :
    (FiniteOffLine → RiemannHypothesis) ↔
      (FiniteOffLine → ∀ (W₀ : ℝ) (F : ℝ → ℝ), 0 < W₀ →
        (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) →
        IsCriticalHalfLineGroundState W₀ F →
        ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ ε a : ℝ, 0 < ε → 0 < a → ∃ G : Set ℕ, Thick G ∧ ∃ C : ℝ,
          ∀ ν ∈ G, |heatedState ε F (-((ν : ℝ) * ℓ))| ≤ C * Real.exp (a * ν * ℓ)) := by
  constructor
  · intro h hfin W₀ F _ ht _
    exact absurd (h hfin) (not_riemannHypothesis_of_windowThreshold_eq ht)
  · intro h hfin
    rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hRH | ⟨W₀, F, hW, ht, hF⟩
    · exact hRH
    · obtain ⟨ℓ, hℓ, hb⟩ := h hfin W₀ F hW ht hF
      exact riemannHypothesis_of_finiteOffLine_of_asymptoticAbscissaLaw hfin
        (asymptoticAbscissaLaw_of_thick_heatedState_bound hW ht hF hℓ hb)

#print axioms b13_iff_criticalState_subexponential_thickLeft
#print axioms b13_iff_criticalState_thick_heated_bound

end GaloisForLFunctions.ExclusionOfTheCriticalState
