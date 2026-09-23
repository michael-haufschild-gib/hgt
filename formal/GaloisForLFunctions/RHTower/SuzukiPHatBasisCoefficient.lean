import GaloisForLFunctions.RHTower.SuzukiPHatSpectralCoefficient

noncomputable section

/-!
# Equation (3.8)

The energy kernel at a spectral point is a fixed nonzero multiple of the orthonormal vector `F_γ`,
so the coefficient of `F_γ` in an energy-kernel series can be read off: pairing against `F_γ` makes
the partial sums eventually constant.  Combining with the integration-by-parts identification of the
ray coefficient gives the source's equation (3.8),

`⟪F_γ, 𝒫̂_{Dψ}⟩ = i √(π m_γ) ψ̂(γ)`.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- The normalising constant relating the energy kernel to the orthonormal vector. -/
def suzukiEnergyScale (ρ : XiDivisorSupport) : ℂ :=
  ((Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi) : ℝ) : ℂ) * I

theorem suzukiEnergyScale_ne_zero (ρ : XiDivisorSupport) : suzukiEnergyScale ρ ≠ 0 := by
  have hpi := Real.pi_pos
  have hm : (0 : ℝ) < (xiSupportMult ρ : ℝ) := by exact_mod_cast xiSupportMult_pos ρ
  refine mul_ne_zero ?_ Complex.I_ne_zero
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

theorem suzukiEnergyKernel_eq_smul (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    suzukiEnergyKernel hRH ρ = (suzukiEnergyScale ρ)⁻¹ • suzukiFGammaFamily hRH ρ := by
  rw [suzukiFGammaFamily_eq_smul_energyKernel hRH ρ, smul_smul]
  rw [show ((Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi) : ℝ) : ℂ) * I
      = suzukiEnergyScale ρ from rfl]
  rw [inv_mul_cancel₀ (suzukiEnergyScale_ne_zero ρ), one_smul]

theorem inner_suzukiFGammaFamily_suzukiEnergyKernel (hRH : RiemannHypothesis)
    (ρ σ : XiDivisorSupport) :
    (inner ℂ (suzukiFGammaFamily hRH ρ) (suzukiEnergyKernel hRH σ) : ℂ)
      = if σ = ρ then (suzukiEnergyScale ρ)⁻¹ else 0 := by
  rw [suzukiEnergyKernel_eq_smul hRH σ, inner_smul_right]
  by_cases h : σ = ρ
  · subst h
    rw [if_pos rfl]
    have hself : (inner ℂ (suzukiFGammaFamily hRH σ) (suzukiFGammaFamily hRH σ) : ℂ) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, norm_suzukiFGammaFamily hRH σ]
      norm_num
    rw [hself, mul_one]
  · rw [if_neg h, inner_suzukiFGammaFamily hRH (Ne.symm h), mul_zero]

theorem inner_suzukiFGammaFamily_suzukiCauchyPartial (hRH : RiemannHypothesis)
    (c : XiDivisorSupport → ℂ) (ρ : XiDivisorSupport) {N : ℕ}
    (hN : xiSupportEnum.symm ρ < N) :
    (inner ℂ (suzukiFGammaFamily hRH ρ) (suzukiCauchyPartial hRH c N) : ℂ)
      = c ρ * (suzukiEnergyScale ρ)⁻¹ := by
  rw [suzukiCauchyPartial, inner_sum]
  have hterm : ∀ n ∈ Finset.range N,
      (inner ℂ (suzukiFGammaFamily hRH ρ)
        (c (xiSupportEnum n) • suzukiEnergyKernel hRH (xiSupportEnum n)) : ℂ)
      = if n = xiSupportEnum.symm ρ then c ρ * (suzukiEnergyScale ρ)⁻¹ else 0 := by
    intro n _
    rw [inner_smul_right, inner_suzukiFGammaFamily_suzukiEnergyKernel]
    by_cases h : n = xiSupportEnum.symm ρ
    · subst h
      rw [if_pos rfl, if_pos (Equiv.apply_symm_apply xiSupportEnum ρ),
        Equiv.apply_symm_apply]
    · rw [if_neg h, if_neg ?_, mul_zero]
      intro hc
      exact h (by rw [← hc, Equiv.symm_apply_apply])
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range N)
    (xiSupportEnum.symm ρ) (fun _ => c ρ * (suzukiEnergyScale ρ)⁻¹),
    if_pos (Finset.mem_range.mpr hN)]

/-- **The coefficient of `F_ρ` in an energy-kernel series.** -/
theorem inner_suzukiFGammaFamily_of_tendsto (hRH : RiemannHypothesis)
    (c : XiDivisorSupport → ℂ) {S : Lp ℂ 2 (volume : Measure ℝ)}
    (hS : Tendsto (suzukiCauchyPartial hRH c) atTop (𝓝 S)) (ρ : XiDivisorSupport) :
    (inner ℂ (suzukiFGammaFamily hRH ρ) S : ℂ) = c ρ * (suzukiEnergyScale ρ)⁻¹ := by
  have hcont : Tendsto (fun N : ℕ =>
      (inner ℂ (suzukiFGammaFamily hRH ρ) (suzukiCauchyPartial hRH c N) : ℂ)) atTop
      (𝓝 (inner ℂ (suzukiFGammaFamily hRH ρ) S : ℂ)) := by
    have hmap := ((innerSL ℂ (suzukiFGammaFamily hRH ρ)).continuous.tendsto S).comp hS
    exact hmap
  have heven : Tendsto (fun N : ℕ =>
      (inner ℂ (suzukiFGammaFamily hRH ρ) (suzukiCauchyPartial hRH c N) : ℂ)) atTop
      (𝓝 (c ρ * (suzukiEnergyScale ρ)⁻¹)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop (xiSupportEnum.symm ρ)] with N hN
    exact (inner_suzukiFGammaFamily_suzukiCauchyPartial hRH c ρ hN).symm
  exact tendsto_nhds_unique hcont heven


theorem xiRealSpectralPointSupport_ne_zero (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    xiRealSpectralPointSupport ρ ≠ 0 := by
  intro h
  have hne := xiSpectralPoint_ne_zero (⟨ρ, ⟨0, xiSupportMult_pos ρ⟩⟩ : XiZeroCopy)
  rw [xiSpectralPoint_eq_support, ← ofReal_xiRealSpectralPointSupport hRH, h] at hne
  exact hne (by simp)

theorem suzukiPHatCoef_algebra (M s S F : ℂ) (hs : s ≠ 0) (hsS : s * S = M) :
    (-I) * (M * (-I * F)) * (s * I)⁻¹ = I * S * F := by
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp
  linear_combination (-F) * hsS

/-- **Equation (3.8).**  The coefficient of `F_γ` in the transform of `Dψ` is `i√(π m_γ) ψ̂(γ)`. -/
theorem inner_suzukiFGammaFamily_suzukiPHat (hRH : RiemannHypothesis) {a : ℝ} (ha : 0 ≤ a)
    (ψ : SuzukiTest) (hsupp : Function.support (ψ : ℝ → ℂ) ⊆ Icc (-a) a)
    {S : Lp ℂ 2 (volume : Measure ℝ)}
    (hS : Tendsto (suzukiCauchyPartial hRH
      (suzukiPHatEnergyCoef ((ψ.toCompactTest hsupp).toDerivativeZeroMean))) atTop (𝓝 S))
    (ρ : XiDivisorSupport) :
    (inner ℂ (suzukiFGammaFamily hRH ρ) S : ℂ)
      = I * ((Real.sqrt (Real.pi * (xiSupportMult ρ : ℝ)) : ℝ) : ℂ)
        * suzukiEntireFourier (ψ : ℝ → ℂ) ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  have hm : (0 : ℝ) < (xiSupportMult ρ : ℝ) := by exact_mod_cast xiSupportMult_pos ρ
  rw [inner_suzukiFGammaFamily_of_tendsto hRH _ hS ρ]
  rw [suzukiPHatEnergyCoef,
    suzukiPHatCoefFn_ofReal ha ψ hsupp (xiRealSpectralPointSupport_ne_zero hRH ρ)]
  rw [map_mul, Complex.conj_I, Complex.conj_conj]
  rw [suzukiEnergyScale]
  have hsq : Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi)
      * Real.sqrt (Real.pi * (xiSupportMult ρ : ℝ)) = (xiSupportMult ρ : ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (xiSupportMult ρ : ℝ) / Real.pi * (Real.pi * (xiSupportMult ρ : ℝ))
        = (xiSupportMult ρ : ℝ) ^ (2 : ℕ) by field_simp]
    exact Real.sqrt_sq (le_of_lt hm)
  have hs1 : (0 : ℝ) < Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi) :=
    Real.sqrt_pos.mpr (by positivity)
  have hs1c : ((Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hs1
  have hsqc : ((Real.sqrt ((xiSupportMult ρ : ℝ) / Real.pi) : ℝ) : ℂ)
      * ((Real.sqrt (Real.pi * (xiSupportMult ρ : ℝ)) : ℝ) : ℂ)
      = ((xiSupportMult ρ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hsq]
  exact suzukiPHatCoef_algebra _ _ _ _ hs1c hsqc


end RHTower
