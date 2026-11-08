import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainTruncatedOverlap

/-!
# The actual regularized Narain Eisenstein overlap

Subtracting the two Eisenstein constant-term integrals from the literal
height-truncated fundamental-domain overlap gives the scalar Mellin
transform for `Re s > 1`, hence the exact two-target Eisenstein product.
-/

open Complex RHTower UpperHalfPlane ModularGroup Set Filter Topology MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Increasing scalar cutoffs recover the Mellin transform of the actual nonvacuum source. -/
theorem tendsto_narainScalarHeat_truncated_mellin
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun T : ℝ => ∫ y in Ioc (0 : ℝ) T,
      (y : ℂ) ^ (s - 1) * narainScalarHeat ρ σ y) atTop
        (𝓝 (mellin (narainScalarHeat ρ σ) s)) := by
  have hu : (⋃ T : ℝ, Ioc (0 : ℝ) T) = Ioi 0 := by
    ext y
    simp only [mem_iUnion, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨T, hy, _⟩
      exact hy
    · intro hy
      exact ⟨y, hy, le_rfl⟩
  have hm : Monotone (fun T : ℝ => Ioc (0 : ℝ) T) := by
    intro a b hab y hy
    exact ⟨hy.1, hy.2.trans hab⟩
  have h := tendsto_setIntegral_of_monotone (μ := volume)
    (f := fun y : ℝ => (y : ℂ) ^ (s - 1) * narainScalarHeat ρ σ y)
    (fun _ => measurableSet_Ioc) hm
    (by rw [hu]; exact mellinConvergent_narainScalarHeat ρ σ hs)
  simpa only [hu, mellin, smul_eq_mul] using h

private theorem scattering_correction_tendsto_zero {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun T : ℝ => narainOverlapScattering s * (T : ℂ) ^ (1 - s) / (1 - s))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun T : ℝ => (T : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (tendsto_rpow_neg_atTop (sub_pos.mpr hs))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hT]
    simp only [Complex.sub_re, Complex.one_re]
    rw [show -(s.re - 1) = 1 - s.re by ring]
  simpa only [mul_zero, zero_div] using (hp.const_mul (narainOverlapScattering s)).div_const (1 - s)

/-- The regularized actual Narain–Eisenstein overlap equals the scalar Mellin transform. -/
theorem narain_regularized_overlap (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun T : ℝ => narainTruncatedOverlap ρ σ s T - (T : ℂ) ^ s / s -
      narainOverlapScattering s * (T : ℂ) ^ (1 - s) / (1 - s)) atTop
        (𝓝 (mellin (narainScalarHeat ρ σ) s)) := by
  have h := ((tendsto_narainScalarHeat_truncated_mellin ρ σ hs).sub
    (narainEisensteinCuspTail_tendsto_zero ρ σ hs)).sub (scattering_correction_tendsto_zero hs)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [narainTruncatedOverlap_sub_vacuum ρ σ hs hT]

/-- The literal regularized overlap has the exact two-target Eisenstein product. -/
theorem narain_regularized_overlap_eq_eisenstein_product
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun T : ℝ => narainTruncatedOverlap ρ σ s T - (T : ℂ) ^ s / s -
      narainOverlapScattering s * (T : ℂ) ^ (1 - s) / (1 - s)) atTop
      (𝓝 (2 * ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s)) *
        d4BMRawEisensteinPoincareSeries ρ ⟨s, hs⟩ *
          d4BMRawEisensteinPoincareSeries σ ⟨s, hs⟩)) := by
  simpa only [mellin_narainScalarHeat_eq_eisenstein_product ρ σ hs] using
    narain_regularized_overlap ρ σ hs

/-- The regularized fundamental-domain integral uses the original Poincaré series and exact scattering factor. -/
theorem narain_regularized_overlap_poincare
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun T : ℝ =>
      (∫ τ in fd ∩ {τ : UpperHalfPlane | τ.im ≤ T},
        narainPartitionOnUpperHalfPlane ρ σ τ *
          d4BMRawEisensteinPoincareSeries ⟨τ.re, τ.im, τ.im_pos⟩ ⟨s, hs⟩) -
      (T : ℂ) ^ s / s -
      (reflectedCompletedLambda (2 * s - 1) / reflectedCompletedLambda (2 * s)) *
        (T : ℂ) ^ (1 - s) / (1 - s)) atTop
      (𝓝 (2 * ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s * riemannZeta (2 * s)) *
        d4BMRawEisensteinPoincareSeries ρ ⟨s, hs⟩ *
          d4BMRawEisensteinPoincareSeries σ ⟨s, hs⟩)) := by
  simpa only [narainTruncatedOverlap_eq_setIntegral,
    narainOverlapEisenstein_eq_poincare hs, narainOverlapScattering_eq_completedLambda] using
    narain_regularized_overlap_eq_eisenstein_product ρ σ hs

#print axioms narain_regularized_overlap
#print axioms narain_regularized_overlap_poincare
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
