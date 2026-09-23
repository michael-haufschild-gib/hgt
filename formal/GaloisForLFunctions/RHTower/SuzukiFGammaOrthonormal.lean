import GaloisForLFunctions.RHTower.SuzukiFGammaDiagonal

/-!
# Suzuki's family `F_γ` is an orthonormal system of `L²(ℝ)`

This module assembles Proposition 4.1 of Suzuki, *On the Hilbert space derived from the Weil
distribution*.  The family is equation (3.5),

```text
F_γ(z) = √(m_γ/π) · i (1 + Θ(z)) / (2 (z - γ)),
```

written with the divided slope of `A/E = (1+Θ)/2` so that the removable point `z = γ` carries
its true value.  With that reading equation (4.2) is immediate from the derivative law
`(A/E)'(γ) = -i/m_γ`: `F_γ(γ) = 1/√(m_γ π)` and `F_γ(γ') = 0` at every other zero.

Orthonormality rests on the boundary identity `|A/E|² = Re (A/E)` on the real axis, which turns
both inner products into the real integrals computed by Cauchy's theorem: zero off the diagonal
and `π/m_γ` on it, the latter after subtracting an explicit Cauchy-kernel comparison term.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

/-- Suzuki's family, equation (3.5): `F_γ(z) = √(m_γ/π) · i(1+Θ(z))/(2(z-γ))`, written with the
divided slope so that the removable point `z = γ` carries its true value. -/
def suzukiFGammaFun (γ : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  ((Real.sqrt ((m : ℝ) / Real.pi) : ℝ) : ℂ) * (I * dslope suzukiHalfInner ((γ : ℝ) : ℂ) z)

/-- **Suzuki equation (4.2), first half.**  `F_γ(γ) = 1/√(m_γ π)`. -/
theorem suzukiFGammaFun_self {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞)) :
    suzukiFGammaFun γ m ((γ : ℝ) : ℂ) = ((1 / Real.sqrt ((m : ℝ) * Real.pi) : ℝ) : ℂ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpi := Real.pi_pos
  have hd : deriv suzukiHalfInner ((γ : ℝ) : ℂ) = -I / (m : ℂ) :=
    (hasDerivAt_suzukiHalfInner hm hord).deriv
  have hprod : Real.sqrt ((m : ℝ) / Real.pi) * Real.sqrt ((m : ℝ) * Real.pi) = m := by
    rw [← Real.sqrt_mul (by positivity)]
    have hval : (m : ℝ) / Real.pi * ((m : ℝ) * Real.pi) = (m : ℝ) ^ (2 : ℕ) := by
      field_simp
    rw [hval, Real.sqrt_sq hmR.le]
  have hsqne : Real.sqrt ((m : ℝ) * Real.pi) ≠ 0 := by positivity
  have hid : Real.sqrt ((m : ℝ) / Real.pi) * (1 / (m : ℝ))
      = 1 / Real.sqrt ((m : ℝ) * Real.pi) := by
    field_simp
    linarith [hprod]
  have hmC : ((m : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [suzukiFGammaFun, dslope_same, hd]
  have hIval : I * (-I / (m : ℂ)) = 1 / (m : ℂ) := by
    field_simp
    rw [Complex.I_sq]
    ring
  rw [hIval, ← hid]
  push_cast
  ring

/-- **Suzuki equation (4.2), second half.**  `F_γ` vanishes at every other zero of `A`. -/
theorem suzukiFGammaFun_eq_zero_of_ne {γ : ℝ} (m : ℕ) (hγ : XiC ((γ : ℝ) : ℂ) = 0) {δ : ℂ}
    (hδ : XiC δ = 0) (hne : δ ≠ ((γ : ℝ) : ℂ)) : suzukiFGammaFun γ m δ = 0 := by
  rw [suzukiFGammaFun, dslope_suzukiHalfInner_apply hγ hne,
    suzukiHalfInner_eq_zero_of_XiC_zero hδ, zero_div, mul_zero, mul_zero]

theorem continuous_suzukiFGammaFun_ofReal (hRH : RiemannHypothesis) {γ : ℝ} (m : ℕ)
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    Continuous fun x : ℝ => suzukiFGammaFun γ m ((x : ℝ) : ℂ) := by
  refine Continuous.mul continuous_const (Continuous.mul continuous_const ?_)
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hd : DifferentiableAt ℂ (dslope suzukiHalfInner ((γ : ℝ) : ℂ)) ((x : ℝ) : ℂ) :=
    differentiableAt_dslope_suzukiHalfInner_of_rh hRH hγ (by simp)
  exact hd.continuousAt.comp Complex.continuous_ofReal.continuousAt

theorem norm_sq_suzukiFGammaFun_ofReal {γ : ℝ} {m : ℕ} (hγ : XiC ((γ : ℝ) : ℂ) = 0)
    {x : ℝ} (hx : x ≠ γ) :
    ‖suzukiFGammaFun γ m ((x : ℝ) : ℂ)‖ ^ (2 : ℕ)
      = ((m : ℝ) / Real.pi) * (‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) / (x - γ) ^ (2 : ℕ)) := by
  have hxne : ((x : ℝ) : ℂ) ≠ ((γ : ℝ) : ℂ) := by simpa using hx
  have hmR : (0 : ℝ) ≤ (m : ℝ) / Real.pi := by positivity
  have hcast : ((x : ℝ) : ℂ) - ((γ : ℝ) : ℂ) = (((x - γ : ℝ)) : ℂ) := by push_cast; ring
  rw [suzukiFGammaFun, dslope_suzukiHalfInner_apply hγ hxne, hcast, norm_mul, norm_mul,
    Complex.norm_I, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, Real.sq_sqrt hmR, div_pow, sq_abs]

theorem integrable_norm_sq_suzukiFGammaFun (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞))
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    Integrable fun x : ℝ => ‖suzukiFGammaFun γ m ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) := by
  have hbase := integrable_normSq_suzukiHalfInner_div_sq hRH hm hord hγ
  refine (hbase.const_mul ((m : ℝ) / Real.pi)).congr ?_
  have hnull : volume ({γ} : Set ℝ) = 0 := by simp
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx
  have hxne : x ≠ γ := fun h => hx (by simp [h])
  exact (norm_sq_suzukiFGammaFun_ofReal hγ hxne).symm

/-- **`F_γ` is a unit vector of `L²(ℝ)`.** -/
theorem integral_norm_sq_suzukiFGammaFun (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞))
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    (∫ x : ℝ, ‖suzukiFGammaFun γ m ((x : ℝ) : ℂ)‖ ^ (2 : ℕ)) = 1 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpi := Real.pi_pos
  have hnull : volume ({γ} : Set ℝ) = 0 := by simp
  have hae : (fun x : ℝ => ‖suzukiFGammaFun γ m ((x : ℝ) : ℂ)‖ ^ (2 : ℕ))
      =ᵐ[volume] fun x : ℝ =>
        ((m : ℝ) / Real.pi) * (‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) / (x - γ) ^ (2 : ℕ)) := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx
    exact norm_sq_suzukiFGammaFun_ofReal hγ (fun h => hx (by simp [h]))
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul,
    integral_normSq_suzukiHalfInner_div_sq hRH hm hord hγ]
  field_simp

theorem memLp_suzukiFGammaFun (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ}
    (hm : 0 < m) (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞))
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    MemLp (fun x : ℝ => suzukiFGammaFun γ m ((x : ℝ) : ℂ)) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm
    (continuous_suzukiFGammaFun_ofReal hRH m hγ).aestronglyMeasurable).mpr ?_
  exact integrable_norm_sq_suzukiFGammaFun hRH hm hord hγ

/-- The pointwise product behind the off-diagonal inner product. -/
theorem conj_pair_product (A B C D p q N : ℂ) (hN : C * D = N) :
    A * (-I * (C / p)) * (B * (I * (D / q))) = A * B * (N / (p * q)) := by
  rw [← hN]
  have hII : (-I : ℂ) * I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    ring
  linear_combination (A * B * C * D / (p * q)) * hII

/-- **Off-diagonal orthogonality of `F_γ`.**  For distinct zeros the `L²(ℝ)` inner product of
`F_γ` and `F_δ` vanishes. -/
theorem integral_conj_mul_suzukiFGammaFun (hRH : RiemannHypothesis) {γ δ : ℝ} (mγ mδ : ℕ)
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) (hδ : XiC ((δ : ℝ) : ℂ) = 0) (hne : δ ≠ γ) :
    (∫ x : ℝ, (starRingEnd ℂ) (suzukiFGammaFun γ mγ ((x : ℝ) : ℂ))
        * suzukiFGammaFun δ mδ ((x : ℝ) : ℂ)) = 0 := by
  set c : ℂ := ((Real.sqrt ((mγ : ℝ) / Real.pi) : ℝ) : ℂ)
    * ((Real.sqrt ((mδ : ℝ) / Real.pi) : ℝ) : ℂ) with hc
  have hnull : volume ({γ, δ} : Set ℝ) = 0 :=
    (Set.Finite.insert γ (Set.finite_singleton δ)).measure_zero volume
  have hae : (fun x : ℝ => (starRingEnd ℂ) (suzukiFGammaFun γ mγ ((x : ℝ) : ℂ))
        * suzukiFGammaFun δ mδ ((x : ℝ) : ℂ))
      =ᵐ[volume] fun x : ℝ =>
        c * (((‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) / ((x - γ) * (x - δ)) : ℝ)) : ℂ) := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx
    have hxγ : ((x : ℝ) : ℂ) ≠ ((γ : ℝ) : ℂ) := by
      simp only [ne_eq, Complex.ofReal_inj]
      exact fun h => hx (by simp [h])
    have hxδ : ((x : ℝ) : ℂ) ≠ ((δ : ℝ) : ℂ) := by
      simp only [ne_eq, Complex.ofReal_inj]
      exact fun h => hx (by simp [h])
    have hnormSq : (starRingEnd ℂ) (suzukiHalfInner ((x : ℝ) : ℂ))
        * suzukiHalfInner ((x : ℝ) : ℂ)
        = ((‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
    have hcast : (((‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) / ((x - γ) * (x - δ)) : ℝ)) : ℂ)
        = ((‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) : ℝ) : ℂ)
          / ((((x : ℝ) : ℂ) - ((γ : ℝ) : ℂ)) * (((x : ℝ) : ℂ) - ((δ : ℝ) : ℂ))) := by
      push_cast
      ring
    rw [hcast, hc]
    simp only [suzukiFGammaFun]
    rw [dslope_suzukiHalfInner_apply hγ hxγ, dslope_suzukiHalfInner_apply hδ hxδ]
    simp only [map_mul, map_div₀, map_sub, Complex.conj_ofReal, Complex.conj_I]
    exact conj_pair_product _ _ _ _ _ _ _ hnormSq
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul,
    integral_complex_ofReal, integral_normSq_suzukiHalfInner_div_pair hRH hγ hδ hne]
  simp

/-! ## `F_γ` as an orthonormal system of `L²(ℝ)` -/

/-- The `L²(ℝ)` vector represented by `F_γ`. -/
def suzukiFGammaLp (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞)) (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_suzukiFGammaFun hRH hm hord hγ).toLp _

/-- **Proposition 4.1, orthogonality.** -/
theorem inner_suzukiFGammaLp (hRH : RiemannHypothesis) {γ δ : ℝ} {mγ mδ : ℕ}
    (hmγ : 0 < mγ) (hordγ : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (mγ : ℕ∞))
    (hγ : XiC ((γ : ℝ) : ℂ) = 0)
    (hmδ : 0 < mδ) (hordδ : analyticOrderAt XiC ((δ : ℝ) : ℂ) = (mδ : ℕ∞))
    (hδ : XiC ((δ : ℝ) : ℂ) = 0) (hne : δ ≠ γ) :
    inner ℂ (suzukiFGammaLp hRH hmγ hordγ hγ) (suzukiFGammaLp hRH hmδ hordδ hδ) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hae : (fun x : ℝ => inner ℂ ((suzukiFGammaLp hRH hmγ hordγ hγ : Lp ℂ 2 _) x)
        ((suzukiFGammaLp hRH hmδ hordδ hδ : Lp ℂ 2 _) x))
      =ᵐ[volume] fun x : ℝ => (starRingEnd ℂ) (suzukiFGammaFun γ mγ ((x : ℝ) : ℂ))
        * suzukiFGammaFun δ mδ ((x : ℝ) : ℂ) := by
    simp only [suzukiFGammaLp]
    filter_upwards [(memLp_suzukiFGammaFun hRH hmγ hordγ hγ).coeFn_toLp,
      (memLp_suzukiFGammaFun hRH hmδ hordδ hδ).coeFn_toLp] with x h1 h2
    rw [h1, h2, RCLike.inner_apply]
    ring
  rw [MeasureTheory.integral_congr_ae hae]
  exact integral_conj_mul_suzukiFGammaFun hRH mγ mδ hγ hδ hne

/-- **Proposition 4.1, normalization.** -/
theorem norm_suzukiFGammaLp (hRH : RiemannHypothesis) {γ : ℝ} {m : ℕ} (hm : 0 < m)
    (hord : analyticOrderAt XiC ((γ : ℝ) : ℂ) = (m : ℕ∞)) (hγ : XiC ((γ : ℝ) : ℂ) = 0) :
    ‖suzukiFGammaLp hRH hm hord hγ‖ = 1 := by
  have hae : (fun x : ℝ => inner ℂ ((suzukiFGammaLp hRH hm hord hγ : Lp ℂ 2 _) x)
        ((suzukiFGammaLp hRH hm hord hγ : Lp ℂ 2 _) x))
      =ᵐ[volume] fun x : ℝ => ((‖suzukiFGammaFun γ m ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp only [suzukiFGammaLp]
    filter_upwards [(memLp_suzukiFGammaFun hRH hm hord hγ).coeFn_toLp] with x h1
    rw [h1, RCLike.inner_apply, Complex.mul_conj, Complex.sq_norm]
  have hinner : inner ℂ (suzukiFGammaLp hRH hm hord hγ) (suzukiFGammaLp hRH hm hord hγ)
      = (1 : ℂ) := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.integral_congr_ae hae,
      integral_complex_ofReal, integral_norm_sq_suzukiFGammaFun hRH hm hord hγ]
    norm_num
  have hreal : ‖suzukiFGammaLp hRH hm hord hγ‖ ^ (2 : ℕ) = 1 := by
    have h := @inner_self_eq_norm_sq ℂ _ _ _ _ (suzukiFGammaLp hRH hm hord hγ)
    rw [hinner] at h
    simpa using h.symm
  nlinarith [norm_nonneg (suzukiFGammaLp hRH hm hord hγ), hreal]

end
end RHTower

