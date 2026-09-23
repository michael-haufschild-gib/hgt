import GaloisForLFunctions.HTGeometry.SpectralHeatKernel.Semigroup

/-!
# The heat kernel represents the heat semigroup

The spectral kernel `K(t,x,y) = Σₙ e^{−tλₙ} φₙ(x) \overline{φₙ(y)}` acts on functions by integration,
and that action is the spectral heat semigroup:

```text
∫ K(t,x,y) v(y) dμ(y) = Σₙ e^{−tλₙ} ⟪φₙ, v⟫ φₙ(x) .
```

This is the identity that turns pointwise kernel estimates into statements about the operator
`e^{−tΔ}`, and conversely.  It is proved by the same absolutely convergent interchange as the
semigroup property.
-/

open MeasureTheory Set Filter Real

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The `L²` pairing bound with a general second factor. -/
theorem integral_norm_mul_le_half_add {f g : X → ℂ}
    (hf : Integrable (fun z => ‖f z‖ ^ (2 : ℕ)) μ) (hg : Integrable (fun z => ‖g z‖ ^ (2 : ℕ)) μ)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ) :
    ∫ z, ‖f z‖ * ‖g z‖ ∂μ ≤ ((∫ z, ‖f z‖ ^ (2 : ℕ) ∂μ) + ∫ z, ‖g z‖ ^ (2 : ℕ) ∂μ) / 2 := by
  have hmaj : Integrable (fun z => (‖f z‖ ^ (2 : ℕ) + ‖g z‖ ^ (2 : ℕ)) / 2) μ := (hf.add hg).div_const 2
  have hint := integrable_norm_mul_norm hf hg hfm hgm
  refine le_trans (MeasureTheory.integral_mono hint hmaj
    (fun z => norm_mul_norm_le_half_add_sq _ _)) (le_of_eq ?_)
  rw [MeasureTheory.integral_div, MeasureTheory.integral_add hf hg]

/-- **The kernel represents the semigroup.**

`∫ K(t,x,y) v(y) dμ(y) = Σₙ e^{−tλₙ} ⟪φₙ, v⟫ φₙ(x)`. -/
theorem integral_spectralHeatKernel_mul (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) {t : ℝ} {x : X}
    (v : X → ℂ)
    (hmeas : ∀ n, AEStronglyMeasurable (φ n) μ) (hvm : AEStronglyMeasurable v μ)
    (hsq : ∀ n, Integrable (fun z => ‖φ n z‖ ^ (2 : ℕ)) μ)
    (hvsq : Integrable (fun z => ‖v z‖ ^ (2 : ℕ)) μ)
    (hnorm : ∀ n, ∫ z, ‖φ n z‖ ^ (2 : ℕ) ∂μ = 1)
    (hsx : Summable fun n => Real.exp (-(t * lam n)) * ‖φ n x‖) :
    (∫ y, spectralHeatKernel lam φ t x y * v y ∂μ)
      = ∑' n, (Real.exp (-(t * lam n)) : ℂ)
          * ((∫ y, (starRingEnd ℂ) (φ n y) * v y ∂μ) * φ n x) := by
  classical
  set c : ℕ → ℂ := fun n => (Real.exp (-(t * lam n)) : ℂ) * φ n x with hc
  have hnormc : ∀ n, ‖c n‖ = Real.exp (-(t * lam n)) * ‖φ n x‖ := by
    intro n
    rw [hc]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]
  -- the pointwise expansion of the integrand
  have hpoint : ∀ y, spectralHeatKernel lam φ t x y * v y
      = ∑' n, c n * ((starRingEnd ℂ) (φ n y) * v y) := by
    intro y
    rw [spectralHeatKernel, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    rw [hc]
    ring
  -- integrability of each term
  have hIint : ∀ n, Integrable (fun y => c n * ((starRingEnd ℂ) (φ n y) * v y)) μ := fun n =>
    (integrable_conj_mul (hsq n) hvsq (hmeas n) hvm).const_mul _
  have hbound : ∀ n, (∫ y, ‖c n * ((starRingEnd ℂ) (φ n y) * v y)‖ ∂μ)
      ≤ ‖c n‖ * ((1 + ∫ z, ‖v z‖ ^ (2 : ℕ) ∂μ) / 2) := by
    intro n
    have hcongr : ∀ y, ‖c n * ((starRingEnd ℂ) (φ n y) * v y)‖
        = ‖c n‖ * (‖φ n y‖ * ‖v y‖) := by
      intro y
      simp only [norm_mul, Complex.norm_conj]
    simp only [hcongr]
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have := integral_norm_mul_le_half_add (hsq n) hvsq (hmeas n) hvm
    rwa [hnorm n] at this
  have hnormsum : Summable fun n =>
      ∫ y, ‖c n * ((starRingEnd ℂ) (φ n y) * v y)‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun n => MeasureTheory.integral_nonneg fun y => norm_nonneg _)
      hbound ?_
    refine Summable.mul_right _ ?_
    exact hsx.congr fun n => (hnormc n).symm
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun n => fun y => c n * ((starRingEnd ℂ) (φ n y) * v y)) hIint hnormsum
  calc (∫ y, spectralHeatKernel lam φ t x y * v y ∂μ)
      = ∫ y, ∑' n, c n * ((starRingEnd ℂ) (φ n y) * v y) ∂μ :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑' n, ∫ y, c n * ((starRingEnd ℂ) (φ n y) * v y) ∂μ := hswap.symm
    _ = ∑' n, (Real.exp (-(t * lam n)) : ℂ)
          * ((∫ y, (starRingEnd ℂ) (φ n y) * v y ∂μ) * φ n x) := by
        refine tsum_congr fun n => ?_
        rw [MeasureTheory.integral_const_mul, hc]
        ring

end GaloisForLFunctions.HTGeometry
