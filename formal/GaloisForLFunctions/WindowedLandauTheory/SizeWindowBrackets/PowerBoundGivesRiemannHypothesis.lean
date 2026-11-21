import GaloisForLFunctions.WindowedLandauTheory.StatementOC
import Mathlib.NumberTheory.LSeries.RiemannZeta



-- Powers in `ℤˣ` (also inside products) are monoid powers here, as the proofs assume.
attribute [-instance] Int.instUnitsPow

namespace WindowedLandauTheory.LFunctionChainParameters.ConditionalMainTheorem

open WindowedLandauTheory

def LandauZeroFreeHalfPlane : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ y₀ : ℝ, (∀ y : ℝ, y₀ ≤ y → Gz y ≤ y ^ θ) →
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

def PowerBoundGivesRiemannHypothesis : Prop :=
  ∀ C ε₁ : ℝ, 0 < ε₁ →
    (∀ ε : ℝ, 0 < ε → ε < ε₁ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → Gz x ≤ x ^ (1 / 2 + C * ε)) →
    RiemannHypothesis

end WindowedLandauTheory.LFunctionChainParameters.ConditionalMainTheorem

