import GaloisForLFunctions.HTGeometry.SpectralHeatKernel.Basic

/-!
# The semigroup property of a spectral heat kernel

The defining property of a heat kernel is the Chapman–Kolmogorov identity

```text
∫ K(s,x,z) K(t,z,y) dμ(z) = K(s+t,x,y) ,
```

which for a spectral kernel is orthonormality of the eigenfunctions read through a double sum.  It
is proved here, together with the elementary `L²` bound `∫ ‖f‖‖g‖ ≤ 1` for two normalized functions
that makes the double sum absolutely convergent.
-/

open MeasureTheory Set Filter Real

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Pointwise arithmetic–geometric bound. -/
theorem norm_mul_norm_le_half_add_sq (u v : ℝ) : u * v ≤ (u ^ (2 : ℕ) + v ^ (2 : ℕ)) / 2 := by
  nlinarith [sq_nonneg (u - v)]

/-- The product of two square-integrable functions is integrable. -/
theorem integrable_norm_mul_norm {f g : X → ℂ}
    (hf : Integrable (fun z => ‖f z‖ ^ (2 : ℕ)) μ) (hg : Integrable (fun z => ‖g z‖ ^ (2 : ℕ)) μ)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ) :
    Integrable (fun z => ‖f z‖ * ‖g z‖) μ := by
  refine ((hf.add hg).div_const 2).mono' (hfm.norm.mul hgm.norm) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact norm_mul_norm_le_half_add_sq _ _

/-- **The arithmetic–geometric bound for two normalized `L²` functions.** -/
theorem integral_norm_mul_le_one {f g : X → ℂ}
    (hf : Integrable (fun z => ‖f z‖ ^ (2 : ℕ)) μ) (hg : Integrable (fun z => ‖g z‖ ^ (2 : ℕ)) μ)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hfn : ∫ z, ‖f z‖ ^ (2 : ℕ) ∂μ = 1) (hgn : ∫ z, ‖g z‖ ^ (2 : ℕ) ∂μ = 1) :
    ∫ z, ‖f z‖ * ‖g z‖ ∂μ ≤ 1 := by
  have hmaj : Integrable (fun z => (‖f z‖ ^ (2 : ℕ) + ‖g z‖ ^ (2 : ℕ)) / 2) μ := (hf.add hg).div_const 2
  have hint := integrable_norm_mul_norm hf hg hfm hgm
  refine le_trans (MeasureTheory.integral_mono hint hmaj
    (fun z => norm_mul_norm_le_half_add_sq _ _)) (le_of_eq ?_)
  rw [MeasureTheory.integral_div, MeasureTheory.integral_add hf hg, hfn, hgn]
  norm_num

/-- The product of two eigenfunctions is integrable. -/
theorem integrable_conj_mul {f g : X → ℂ}
    (hf : Integrable (fun z => ‖f z‖ ^ (2 : ℕ)) μ) (hg : Integrable (fun z => ‖g z‖ ^ (2 : ℕ)) μ)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ) :
    Integrable (fun z => (starRingEnd ℂ) (f z) * g z) μ := by
  refine (integrable_norm_mul_norm hf hg hfm hgm).mono'
    ((Complex.continuous_conj.comp_aestronglyMeasurable hfm).mul hgm) ?_
  filter_upwards with z
  rw [norm_mul, Complex.norm_conj]

/-- **The semigroup property of a spectral heat kernel.** -/
theorem spectralHeatKernel_semigroup (lam : ℕ → ℝ) (φ : ℕ → X → ℂ) {s t : ℝ} {x y : X}
    (hmeas : ∀ n, AEStronglyMeasurable (φ n) μ)
    (hsq : ∀ n, Integrable (fun z => ‖φ n z‖ ^ (2 : ℕ)) μ)
    (hnorm : ∀ n, ∫ z, ‖φ n z‖ ^ (2 : ℕ) ∂μ = 1)
    (horth : ∀ m n, ∫ z, (starRingEnd ℂ) (φ m z) * φ n z ∂μ = if m = n then 1 else 0)
    (hsx : Summable fun m => Real.exp (-(s * lam m)) * ‖φ m x‖)
    (hty : Summable fun n => Real.exp (-(t * lam n)) * ‖φ n y‖)
    (habsx : ∀ z, Summable fun m => Real.exp (-(s * lam m)) * (‖φ m x‖ * ‖φ m z‖))
    (habsy : ∀ z, Summable fun n => Real.exp (-(t * lam n)) * (‖φ n z‖ * ‖φ n y‖)) :
    (∫ z, spectralHeatKernel lam φ s x z * spectralHeatKernel lam φ t z y ∂μ)
      = spectralHeatKernel lam φ (s + t) x y := by
  classical
  set a : ℕ → X → ℂ := fun m z =>
    (Real.exp (-(s * lam m)) : ℂ) * (φ m x * (starRingEnd ℂ) (φ m z)) with ha
  set b : ℕ → X → ℂ := fun n z =>
    (Real.exp (-(t * lam n)) : ℂ) * (φ n z * (starRingEnd ℂ) (φ n y)) with hb
  set c : ℕ × ℕ → ℂ := fun p =>
    (Real.exp (-(s * lam p.1)) : ℂ) * (Real.exp (-(t * lam p.2)) : ℂ)
      * (φ p.1 x * (starRingEnd ℂ) (φ p.2 y)) with hc
  have hnorma : ∀ z n, ‖a n z‖ = Real.exp (-(s * lam n)) * (‖φ n x‖ * ‖φ n z‖) := by
    intro z n
    rw [ha]
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]
  have hnormb : ∀ z n, ‖b n z‖ = Real.exp (-(t * lam n)) * (‖φ n z‖ * ‖φ n y‖) := by
    intro z n
    rw [hb]
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]
  have hsa : ∀ z, Summable fun n => ‖a n z‖ := fun z =>
    (habsx z).congr fun n => (hnorma z n).symm
  have hsb : ∀ z, Summable fun n => ‖b n z‖ := fun z =>
    (habsy z).congr fun n => (hnormb z n).symm
  have hnormc : ∀ p : ℕ × ℕ, ‖c p‖
      = (Real.exp (-(s * lam p.1)) * ‖φ p.1 x‖) * (Real.exp (-(t * lam p.2)) * ‖φ p.2 y‖) := by
    intro p
    rw [hc]
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]
    ring
  have hsc : Summable fun p : ℕ × ℕ => ‖c p‖ := by
    refine Summable.congr ?_ fun p => (hnormc p).symm
    exact hsx.mul_of_nonneg hty (fun n => by positivity) (fun n => by positivity)
  -- the pointwise product of the two kernels
  have hpoint : ∀ z, spectralHeatKernel lam φ s x z * spectralHeatKernel lam φ t z y
      = ∑' p : ℕ × ℕ, c p * ((starRingEnd ℂ) (φ p.1 z) * φ p.2 z) := by
    intro z
    have hprod := tsum_mul_tsum_of_summable_norm (hsa z) (hsb z)
    rw [spectralHeatKernel, spectralHeatKernel]
    rw [show (∑' n, (Real.exp (-(s * lam n)) : ℂ) * (φ n x * (starRingEnd ℂ) (φ n z)))
        = ∑' n, a n z from rfl,
      show (∑' n, (Real.exp (-(t * lam n)) : ℂ) * (φ n z * (starRingEnd ℂ) (φ n y)))
        = ∑' n, b n z from rfl, hprod]
    refine tsum_congr fun p => ?_
    rw [ha, hb, hc]
    ring
  -- integrate term by term
  have hIint : ∀ p : ℕ × ℕ,
      Integrable (fun z => c p * ((starRingEnd ℂ) (φ p.1 z) * φ p.2 z)) μ := fun p =>
    (integrable_conj_mul (hsq p.1) (hsq p.2) (hmeas p.1) (hmeas p.2)).const_mul _
  have hnormint : ∀ p : ℕ × ℕ,
      (∫ z, ‖c p * ((starRingEnd ℂ) (φ p.1 z) * φ p.2 z)‖ ∂μ) ≤ ‖c p‖ := by
    intro p
    have hcongr : ∀ z, ‖c p * ((starRingEnd ℂ) (φ p.1 z) * φ p.2 z)‖
        = ‖c p‖ * (‖φ p.1 z‖ * ‖φ p.2 z‖) := by
      intro z
      simp only [norm_mul, Complex.norm_conj]
    simp only [hcongr]
    rw [MeasureTheory.integral_const_mul]
    calc ‖c p‖ * ∫ z, ‖φ p.1 z‖ * ‖φ p.2 z‖ ∂μ
        ≤ ‖c p‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (integral_norm_mul_le_one (hsq p.1) (hsq p.2) (hmeas p.1) (hmeas p.2)
              (hnorm p.1) (hnorm p.2)) (norm_nonneg _)
      _ = ‖c p‖ := mul_one _
  have hnormsum : Summable fun p : ℕ × ℕ =>
      ∫ z, ‖c p * ((starRingEnd ℂ) (φ p.1 z) * φ p.2 z)‖ ∂μ := by
    refine Summable.of_nonneg_of_le (fun p => ?_) hnormint hsc
    exact MeasureTheory.integral_nonneg fun z => norm_nonneg _
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (F := fun p : ℕ × ℕ => fun z => c p * ((starRingEnd ℂ) (φ p.1 z) * φ p.2 z)) hIint hnormsum
  -- evaluate each term by orthonormality
  have hterm : ∀ p : ℕ × ℕ,
      (∫ z, c p * ((starRingEnd ℂ) (φ p.1 z) * φ p.2 z) ∂μ)
        = c p * (if p.1 = p.2 then 1 else 0) := by
    intro p
    rw [MeasureTheory.integral_const_mul, horth p.1 p.2]
  have hsummableTerm : Summable fun p : ℕ × ℕ => c p * (if p.1 = p.2 then 1 else 0) := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hsc
    rw [norm_mul]
    by_cases hp : p.1 = p.2
    · simp [hp]
    · simp [hp]
  -- collapse the double sum to the diagonal
  have hdiag : (∑' p : ℕ × ℕ, c p * (if p.1 = p.2 then 1 else 0)) = ∑' m, c (m, m) := by
    rw [hsummableTerm.tsum_prod]
    refine tsum_congr fun m => ?_
    rw [tsum_eq_single m ?_]
    · simp
    · intro n hn
      simp [Ne.symm hn]
  calc (∫ z, spectralHeatKernel lam φ s x z * spectralHeatKernel lam φ t z y ∂μ)
      = ∫ z, ∑' p : ℕ × ℕ, c p * ((starRingEnd ℂ) (φ p.1 z) * φ p.2 z) ∂μ := by
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑' p : ℕ × ℕ, ∫ z, c p * ((starRingEnd ℂ) (φ p.1 z) * φ p.2 z) ∂μ := hswap.symm
    _ = ∑' p : ℕ × ℕ, c p * (if p.1 = p.2 then 1 else 0) := tsum_congr hterm
    _ = ∑' m, c (m, m) := hdiag
    _ = spectralHeatKernel lam φ (s + t) x y := by
        rw [spectralHeatKernel]
        refine tsum_congr fun m => ?_
        show (Real.exp (-(s * lam m)) : ℂ) * (Real.exp (-(t * lam m)) : ℂ)
            * (φ m x * (starRingEnd ℂ) (φ m y))
          = (Real.exp (-((s + t) * lam m)) : ℂ) * (φ m x * (starRingEnd ℂ) (φ m y))
        have hexp : (Real.exp (-(s * lam m)) : ℂ) * (Real.exp (-(t * lam m)) : ℂ)
            = ((Real.exp (-((s + t) * lam m)) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Real.exp_add]
          congr 2
          ring
        rw [hexp]

end GaloisForLFunctions.HTGeometry
