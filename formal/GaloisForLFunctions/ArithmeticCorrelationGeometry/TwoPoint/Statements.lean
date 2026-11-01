/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GaloisForLFunctions.ArithmeticCorrelationGeometry.TwoPoint.Basic
import GaloisForLFunctions.ArithmeticCorrelationGeometry.TwoPoint.PretentiousDistance
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace OAI

open Filter

namespace TwoPointCorrelations

/-- Power-of-logarithm saving through all real cutoffs, with a single exponent
independent of the four affine coefficients. -/
def LiouvilleLogSaving : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ b₁ b₂ : ℕ,
    0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      ‖affineSum liouville liouville a₁ a₂ b₁ b₂ ⌊X⌋₊‖ ≤
        C * X / Real.rpow (Real.log X) c

/-- Binary cancellation for bounded multiplicative functions when either
factor is uniformly nonpretentious over the growing twist-height range. -/
def BinaryCorrectedElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
    OneBounded f₁ → OneBounded f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ h₁ h₂ : ℕ, h₁ ≠ h₂ →
      Tendsto (fun N : ℕ => correlationSum f₁ f₂ h₁ h₂ N / (N : ℂ)) atTop (nhds 0)

/-- Affine cancellation, including coefficients sharing prime factors. -/
def AffineCorrectedElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
    OneBounded f₁ → OneBounded f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ a₁ a₂ b₁ b₂ : ℕ, 0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
      Tendsto (fun N : ℕ => affineSum f₁ f₂ a₁ a₂ b₁ b₂ N / (N : ℂ)) atTop (nhds 0)

end TwoPointCorrelations

end OAI
