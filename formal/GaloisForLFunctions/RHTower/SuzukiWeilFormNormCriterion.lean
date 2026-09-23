import GaloisForLFunctions.RHTower.SuzukiPHatIsometry
import GaloisForLFunctions.RHTower.SuzukiScrewWeilIdentity
import GaloisForLFunctions.RHTower.SuzukiFriedrichsExtension

/-!
# Suzuki Theorem 1.2: the Weil form is the transform norm

```text
RH  ⟺  ‖𝒫̂_{Dψ}‖²_{L²(ℝ)} = π ⟨ψ, ψ⟩_W   for every ψ ∈ C_c^∞(ℝ).
```

Both directions reduce to Theorem 4.4 through Su22 Proposition 3.1, which identifies the screw
form of a derivative with the Weil distribution of a Hermitian convolution.

For the converse one needs every smooth zero-mean test to be a derivative, so that the
nonnegativity supplied by the hypothesis covers the whole test class of Su22 Theorem 1.3.  The
primitive `t ↦ ∫_{-r}^{t} φ` is compactly supported precisely because `φ` has zero mean, which is
the same hypothesis that defines the class; raising the aperture from `a` to `a + 1` puts the
support of `φ` inside an open interval, as the corpus's primitive construction requires.
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower
noncomputable section

theorem suzukiScrewSmoothForm_congr {a b : ℝ} (φ₁ φ₂ : SuzukiSmoothZeroMeanTest a)
    (ψ₁ ψ₂ : SuzukiSmoothZeroMeanTest b)
    (h1 : (φ₁ : ℝ → ℂ) = (ψ₁ : ℝ → ℂ)) (h2 : (φ₂ : ℝ → ℂ) = (ψ₂ : ℝ → ℂ)) :
    suzukiScrewSmoothForm φ₁ φ₂ = suzukiScrewSmoothForm ψ₁ ψ₂ := by
  rw [suzukiScrewSmoothForm, suzukiScrewSmoothForm]
  simp only [h1, h2]

/-- The compactly supported primitive of a smooth zero-mean test. -/
def suzukiZeroMeanPrimitive {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    SuzukiSmoothCompactTest (a + 1) where
  toFun := suzukiSmoothIntegralPrimitive (a + 1) (fun t => (φ : ℝ → ℂ) t)
  smooth := contDiff_suzukiSmoothIntegralPrimitive _ _ φ.smooth
  support_subset := by
    refine support_suzukiSmoothIntegralPrimitive_subset ?_ φ.integral_zero
    intro x hx
    have hmem : x ∈ Icc (-a) a := φ.support_subset hx
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem coe_suzukiZeroMeanPrimitive_toDerivativeZeroMean {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    ((suzukiZeroMeanPrimitive φ).toDerivativeZeroMean : ℝ → ℂ) = (φ : ℝ → ℂ) := by
  funext t
  rw [SuzukiSmoothCompactTest.coe_toDerivativeZeroMean]
  exact deriv_suzukiSmoothIntegralPrimitive _ _ φ.continuous t

/-- **Suzuki Theorem 1.2 (equivalently Theorem 4.5).**  RH holds if and only if the transform of
`Dψ` has squared `L²` norm `π ⟨ψ,ψ⟩_W` for every smooth compactly supported test. -/
theorem riemannHypothesis_iff_normSq_suzukiPHat_deriv :
    RiemannHypothesis ↔ ∀ (a : ℝ), 0 < a → ∀ ψ : SuzukiSmoothCompactTest a,
      (∫ x : ℝ, ‖suzukiPHat (fun t => (ψ.toDerivativeZeroMean : ℝ → ℂ) t) ((x : ℝ) : ℂ)‖ ^ (2 : ℕ))
        = Real.pi * (suzukiWeilDistribution (suzukiHermitianConvolution ψ ψ)).re := by
  constructor
  · intro hRH a ha ψ
    rw [(riemannHypothesis_iff_normSq_suzukiPHat.mp hRH) a ha ψ.toDerivativeZeroMean,
      suzuki_proposition_three_one ha ψ ψ]
  · intro h
    refine riemannHypothesis_of_suzukiSmoothTestFormNonnegative fun a ha φ => ?_
    set ψ := suzukiZeroMeanPrimitive φ with hψ
    have hcoe := coe_suzukiZeroMeanPrimitive_toDerivativeZeroMean φ
    have hform : suzukiScrewSmoothForm φ φ
        = suzukiWeilDistribution (suzukiHermitianConvolution ψ ψ) := by
      rw [← suzuki_proposition_three_one (show (0 : ℝ) < a + 1 by linarith) ψ ψ]
      exact suzukiScrewSmoothForm_congr φ φ _ _ hcoe.symm hcoe.symm
    have h1 := h (a + 1) (by linarith) ψ
    have h2 : (0 : ℝ) ≤ ∫ x : ℝ,
        ‖suzukiPHat (fun t => (ψ.toDerivativeZeroMean : ℝ → ℂ) t) ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) :=
      MeasureTheory.integral_nonneg fun x => sq_nonneg _
    rw [h1] at h2
    rw [hform]
    nlinarith [Real.pi_pos]

end
end RHTower
