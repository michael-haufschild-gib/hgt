import GaloisForLFunctions.RHTower.Suzuki.SuzukiFGammaDiagonal
import GaloisForLFunctions.RHTower.XiLaguerrePolya

/-!
# The Gram matrix of the boundary Cauchy kernels

Under the Riemann hypothesis every Xi zero is real in the centered coordinate, so the divisor
support carries a real spectral point `γ_ρ` and a multiplicity `m_ρ`.  Weighting `L²(ℝ)` by the
boundary energy `|A/E|²` makes the Cauchy kernels `x ↦ 1/(x - γ_ρ)` pairwise orthogonal, with
diagonal `π/m_ρ`.  This is Proposition 4.1's orthonormality restated in the form the screw-line
computation consumes: `F_ρ` is `√(m_ρ/π) i (A/E)` times the kernel.
-/

open Complex Filter Topology MeasureTheory

namespace RHTower
noncomputable section

/-- The real spectral point attached to a support element of the Xi divisor. -/
def xiRealSpectralPointSupport (ρ : XiDivisorSupport) : ℝ := (xiSpectralPointSupport ρ).re

/-- The divisor multiplicity at a support element. -/
def xiSupportMult (ρ : XiDivisorSupport) : ℕ :=
  Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))

theorem xiSupportMult_pos (ρ : XiDivisorSupport) : 0 < xiSupportMult ρ := by
  have h := xi_divisor_pos_on_support ρ
  simp only [xiSupportMult]
  omega

theorem ofReal_xiRealSpectralPointSupport (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) = xiSpectralPointSupport ρ := by
  have hcopy : xiSpectralPoint (⟨ρ, ⟨0, xiSupportMult_pos ρ⟩⟩ : XiZeroCopy)
      = ((xiRealSpectralPoint (⟨ρ, ⟨0, xiSupportMult_pos ρ⟩⟩ : XiZeroCopy) : ℝ) : ℂ) :=
    xiSpectralPoint_eq_ofReal_of_rh hRH _
  rw [xiSpectralPoint_eq_support] at hcopy
  exact hcopy.symm

theorem xiRealSpectralPointSupport_injective (hRH : RiemannHypothesis) :
    Function.Injective xiRealSpectralPointSupport := by
  intro ρ σ h
  refine xiSpectralPointSupport_injective ?_
  rw [← ofReal_xiRealSpectralPointSupport hRH ρ, ← ofReal_xiRealSpectralPointSupport hRH σ, h]

theorem XiC_xiRealSpectralPointSupport (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    XiC ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) = 0 := by
  rw [ofReal_xiRealSpectralPointSupport hRH]
  have h := XiC_xiSpectralPoint_eq_zero (⟨ρ, ⟨0, xiSupportMult_pos ρ⟩⟩ : XiZeroCopy)
  rwa [xiSpectralPoint_eq_support] at h

theorem analyticOrderAt_xiRealSpectralPointSupport (hRH : RiemannHypothesis)
    (ρ : XiDivisorSupport) :
    analyticOrderAt XiC ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) = (xiSupportMult ρ : ℕ∞) := by
  rw [ofReal_xiRealSpectralPointSupport hRH, XiC_analyticOrderAt_support]
  rfl

/-- The boundary Cauchy kernel at a Xi zero. -/
def suzukiCauchyKernel (ρ : XiDivisorSupport) (x : ℝ) : ℂ :=
  ((x : ℂ) - ((xiRealSpectralPointSupport ρ : ℝ) : ℂ))⁻¹

theorem suzukiCauchyKernel_conj (ρ : XiDivisorSupport) (x : ℝ) :
    (starRingEnd ℂ) (suzukiCauchyKernel ρ x) = suzukiCauchyKernel ρ x := by
  rw [suzukiCauchyKernel, map_inv₀, map_sub, Complex.conj_ofReal, Complex.conj_ofReal]

theorem halfInnerEnergy_kernel_mul (ρ σ : XiDivisorSupport) (x : ℝ) :
    ((‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) : ℝ) : ℂ) *
        ((starRingEnd ℂ) (suzukiCauchyKernel ρ x)) * (suzukiCauchyKernel σ x)
      = (((‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ)
            / ((x - xiRealSpectralPointSupport ρ) * (x - xiRealSpectralPointSupport σ)) : ℝ)) : ℂ) := by
  rw [suzukiCauchyKernel_conj, suzukiCauchyKernel, suzukiCauchyKernel]
  push_cast
  rw [div_eq_mul_inv, mul_inv]
  ring

theorem integrable_halfInnerEnergy_kernel_pair (hRH : RiemannHypothesis)
    (ρ σ : XiDivisorSupport) :
    Integrable (fun x : ℝ => ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ)
      / ((x - xiRealSpectralPointSupport ρ) * (x - xiRealSpectralPointSupport σ))) := by
  rcases eq_or_ne ρ σ with rfl | hne
  · have h := integrable_normSq_suzukiHalfInner_div_sq hRH (xiSupportMult_pos ρ)
      (analyticOrderAt_xiRealSpectralPointSupport hRH ρ) (XiC_xiRealSpectralPointSupport hRH ρ)
    refine h.congr ?_
    filter_upwards with x
    ring
  · refine integrable_normSq_suzukiHalfInner_div_pair hRH
      (XiC_xiRealSpectralPointSupport hRH ρ) (XiC_xiRealSpectralPointSupport hRH σ) ?_
    exact fun h => hne ((xiRealSpectralPointSupport_injective hRH h).symm)

/-- **The Gram matrix of the boundary Cauchy kernels.**  The energy `|A/E|²` makes the kernels
`1/(x-γ_ρ)` orthogonal, with diagonal `π/m_ρ`. -/
theorem integral_halfInnerEnergy_kernel_pair (hRH : RiemannHypothesis) (ρ σ : XiDivisorSupport) :
    (∫ x : ℝ, ((‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) : ℝ) : ℂ) *
        ((starRingEnd ℂ) (suzukiCauchyKernel ρ x)) * (suzukiCauchyKernel σ x))
      = if ρ = σ then ((Real.pi / (xiSupportMult ρ : ℝ) : ℝ) : ℂ) else 0 := by
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (halfInnerEnergy_kernel_mul ρ σ)),
    integral_complex_ofReal]
  rcases eq_or_ne ρ σ with rfl | hne
  · rw [if_pos rfl]
    congr 1
    have h := integral_normSq_suzukiHalfInner_div_sq hRH (xiSupportMult_pos ρ)
      (analyticOrderAt_xiRealSpectralPointSupport hRH ρ) (XiC_xiRealSpectralPointSupport hRH ρ)
    rw [← h]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  · rw [if_neg hne]
    have hne' : xiRealSpectralPointSupport σ ≠ xiRealSpectralPointSupport ρ :=
      fun h => hne ((xiRealSpectralPointSupport_injective hRH h).symm)
    rw [integral_normSq_suzukiHalfInner_div_pair hRH (XiC_xiRealSpectralPointSupport hRH ρ)
      (XiC_xiRealSpectralPointSupport hRH σ) hne']
    simp

end
end RHTower
