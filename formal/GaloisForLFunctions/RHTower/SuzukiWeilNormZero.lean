import GaloisForLFunctions.RHTower.SuzukiWeilFormNormCriterion
import GaloisForLFunctions.RHTower.SuzukiWeilTestSpace

noncomputable section

/-!
# The norm `‖·‖₀` is the Weil norm

Under the Riemann hypothesis the source's unconditional norm
`‖ψ‖₀ = π^{-1/2} ‖𝒫̂_{Dψ}‖_{L²}` coincides with the Weil norm, so the unconditional completion `H_0`
is `H_W` — the first half of Theorem 5.6.

Read as an equivalence rather than an implication, the same identity is Corollary 1.5: the Riemann
hypothesis holds exactly when the `L²` mass and the Weil mass agree on `V°(0)`.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- Suzuki's differentiation operator on the aperture-free test space. -/
def suzukiTestDeriv (ψ : SuzukiTest) : ℝ → ℂ := deriv (ψ : ℝ → ℂ)

/-- **Theorem 5.6, first half.**  Under the Riemann hypothesis the source's norm `‖·‖₀` is the
Weil norm, so the completion `H_0` is `H_W`. -/
theorem normSq_suzukiPHat_deriv_eq_pi_mul_suzukiWeilInner (hRH : RiemannHypothesis)
    (ψ : SuzukiTest) :
    (∫ x : ℝ, ‖suzukiPHat (suzukiTestDeriv ψ) ((x : ℝ) : ℂ)‖ ^ 2)
      = Real.pi * (suzukiWeilInner ψ ψ).re := by
  obtain ⟨a, ha, hsupp⟩ := ψ.exists_aperture
  set Ψ : SuzukiSmoothCompactTest a := ψ.toCompactTest hsupp with hΨ
  have hbase := (riemannHypothesis_iff_normSq_suzukiPHat_deriv.mp hRH) a ha Ψ
  have hderiv : (fun t : ℝ => (Ψ.toDerivativeZeroMean : ℝ → ℂ) t) = suzukiTestDeriv ψ := by
    funext t
    rw [SuzukiSmoothCompactTest.coe_toDerivativeZeroMean]
    rfl
  rw [hderiv] at hbase
  exact hbase

/-- An aperture-indexed test viewed in the aperture-free test space. -/
def SuzukiSmoothCompactTest.toSuzukiTest {a : ℝ} (ψ : SuzukiSmoothCompactTest a) : SuzukiTest :=
  ⟨(ψ : ℝ → ℂ), ψ.smooth, ψ.hasCompactSupport⟩

@[simp] theorem SuzukiSmoothCompactTest.coe_toSuzukiTest {a : ℝ}
    (ψ : SuzukiSmoothCompactTest a) :
    ((ψ.toSuzukiTest : SuzukiTest) : ℝ → ℂ) = (ψ : ℝ → ℂ) := rfl

theorem suzukiWeilInner_toSuzukiTest {a : ℝ} (ψ : SuzukiSmoothCompactTest a) :
    suzukiWeilInner ψ.toSuzukiTest ψ.toSuzukiTest
      = suzukiWeilDistribution (suzukiHermitianConvolution ψ ψ) := rfl

/-- **Corollary 1.5.**  The Riemann hypothesis is equivalent to the equality of the `L²` mass and
the Weil mass on `V°(0) = {𝖥⁻¹ 𝒫̂_{Dψ} : ψ ∈ C_c^∞}`, parametrised by the test function.
(In the corpus's unitary Fourier normalisation the source's `2‖ψ‖² = ⟨ψ,ψ⟩_W` reads
`‖𝒫̂_{Dψ}‖² = π ⟨ψ,ψ⟩_W`.) -/
theorem riemannHypothesis_iff_normSq_suzukiPHat_suzukiTest :
    RiemannHypothesis ↔ ∀ ψ : SuzukiTest,
      (∫ x : ℝ, ‖suzukiPHat (suzukiTestDeriv ψ) ((x : ℝ) : ℂ)‖ ^ 2)
        = Real.pi * (suzukiWeilInner ψ ψ).re := by
  constructor
  · intro hRH ψ
    exact normSq_suzukiPHat_deriv_eq_pi_mul_suzukiWeilInner hRH ψ
  · intro h
    refine riemannHypothesis_iff_normSq_suzukiPHat_deriv.mpr ?_
    intro a ha ψ
    have hval := h ψ.toSuzukiTest
    have hderiv : suzukiTestDeriv ψ.toSuzukiTest
        = fun t : ℝ => (ψ.toDerivativeZeroMean : ℝ → ℂ) t := by
      funext t
      rw [SuzukiSmoothCompactTest.coe_toDerivativeZeroMean]
      rfl
    rw [hderiv] at hval
    rw [hval, suzukiWeilInner_toSuzukiTest]


end RHTower
