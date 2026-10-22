import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilRayVectorBridge

/-!
# Lemma 3.2, step 3b(ii): the multiplicity fibre sums vanish

Real-axis vanishing of the transform forces every fibre sum of the ray vector to vanish.  Nothing is
constructed here: `suzukiPHatRaySum_eq_zero_off_divisor` supplies vanishing on the whole divisor
complement, `xiCauchyTransform_suzukiRayVector` identifies the ray series with minus the corpus
Cauchy transform, and the corpus's
`xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball` — which needs only the *real part*
to vanish on *one* ball — closes it.

What is left of Lemma 3.2: read `xiWeilFiberSum (suzukiRayVectorFun phi) rho = 0` as
`m_rho * conj(F(-gamma_rho)) = 0` for `phi = D psi`, conclude `F(gamma) = 0` for every `gamma` in
the divisor (negation symmetry, `xiSpectralPoint_reflect`), and apply
`RHTower.suzuki_lemma_two_one`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-- **Lemma 3.2, step 3b(ii).**  Real-axis vanishing of the transform forces every multiplicity
fibre sum of the ray vector to vanish. -/
theorem xiWeilFiberSum_suzukiRayVectorFun_eq_zero {φ : ℝ → ℂ} (hφ : Integrable φ) {T : ℝ}
    (hsupp : ∀ t : ℝ, T < |t| → φ t = 0)
    (hvanish : ∀ x : ℝ, XiC ((x : ℝ) : ℂ) ≠ 0 →
      (∑' q : XiZeroCopy, suzukiPHatRayTerm φ ((x : ℝ) : ℂ) q) = 0)
    (ρ : XiDivisorSupport) :
    xiWeilFiberSum (suzukiRayVectorFun φ) ρ = 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_XiC_ne_zero 0 XiC_zero_ne
  have hre : ∀ z ∈ Metric.ball (0 : ℂ) r,
      (xiCauchyTransform ⟨suzukiRayVectorFun φ, memℓp_suzukiRayVectorFun hφ hsupp⟩ z).re = 0 := by
    intro z hz
    rw [xiCauchyTransform_suzukiRayVector hφ hsupp z,
      suzukiPHatRaySum_eq_zero_off_divisor hφ hsupp hvanish (hball hz)]
    simp
  exact xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball
    ⟨suzukiRayVectorFun φ, memℓp_suzukiRayVectorFun hφ hsupp⟩ hr hball hre ρ

end
end RHTower

