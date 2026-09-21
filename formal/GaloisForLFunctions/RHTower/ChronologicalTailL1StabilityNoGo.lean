import GaloisForLFunctions.RHTower.ChronologicalTailSeparation

/-!
# `L¹`-stable chronological tail repair is impossible

The existing fixed-tail separation shows that one bounded tail profile cannot
have the Bose response of a critical profile.  The missing stability question
is whether a moving tail could converge in `L¹` while its response converges to
that critical response.  It cannot: at every Bose-domain point, the transform
is Lipschitz in the tail's `L¹` distance, with the compact kernel bound as its
constant.  Thus any repair array with a convergent reindexing must escape
`L¹`-compactness (or leave this fixed bounded-tail arena).

This is a no-go for a specified CTF subfamily, not a claim that all moving
arrays are excluded.  The remaining CTF gate is still a literal noncompact or
all-grade source-orientation mechanism.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

namespace RHTower

/-- The Bose transform is Lipschitz in the tail's `L¹` distance at any fixed point of its
analytic domain. -/
theorem boseTransform_le_kernelBound_mul_tailL1 {g h : ℝ → ℂ}
    (hgm : Measurable g) (hhm : Measurable h)
    (hg : IntegrableOn g (Ioo (0 : ℝ) 1))
    (hh : IntegrableOn h (Ioo (0 : ℝ) 1))
    {u : ℂ} {M : ℝ} (hu : u ∈ boseDomain)
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, ‖boseKernelE ((x : ℂ) * u)‖ ≤ M) :
    ‖boseTransform g u - boseTransform h u‖ ≤
      M * ∫ x in Ioo (0 : ℝ) 1, ‖g x - h x‖ := by
  rw [← boseTransform_sub hgm hhm hg hh hu]
  have hdiff : IntegrableOn (g - h) (Ioo (0 : ℝ) 1) := hg.sub hh
  have hintegrand : IntegrableOn
      (fun x : ℝ => (g x - h x) * boseKernelE ((x : ℂ) * u)) (Ioo (0 : ℝ) 1) :=
    integrableOn_profile_kernel (hgm.sub hhm) hdiff hu
  have hright : IntegrableOn (fun x : ℝ => M * ‖g x - h x‖) (Ioo (0 : ℝ) 1) :=
    hdiff.norm.const_mul M
  calc
    ‖∫ x in Ioo (0 : ℝ) 1, (g x - h x) * boseKernelE ((x : ℂ) * u)‖
        ≤ ∫ x in Ioo (0 : ℝ) 1, ‖(g x - h x) * boseKernelE ((x : ℂ) * u)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioo (0 : ℝ) 1, M * ‖g x - h x‖ := by
      apply integral_mono_ae hintegrand.norm hright
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [norm_mul]
      calc
        ‖g x - h x‖ * ‖boseKernelE ((x : ℂ) * u)‖ ≤ ‖g x - h x‖ * M :=
          mul_le_mul_of_nonneg_left (hM x ⟨hx.1.le, hx.2.le⟩) (norm_nonneg _)
        _ = M * ‖g x - h x‖ := by ring
    _ = M * ∫ x in Ioo (0 : ℝ) 1, ‖g x - h x‖ := by
      rw [integral_const_mul]

/-- A bounded tail profile is integrable on the transform interval. -/
theorem integrableOn_tailProfile_of_bounded {θ C : ℝ} (hθ0 : 0 < θ) {f : ℝ → ℂ}
    (hfm : Measurable f) (hC : 0 ≤ C) (hfb : ∀ x, ‖f x‖ ≤ C) :
    IntegrableOn (tailProfile θ f) (Ioo (0 : ℝ) 1) := by
  exact integrableOn_of_weight (measurable_tailProfile θ hfm) (s := (0 : ℝ)) (by norm_num)
    (integrableOn_tailProfile_weight hθ0 hC hfm hfb (s := (0 : ℝ)) (by norm_num))

/-- `L¹` convergence of bounded tail profiles forces convergence of their Bose transforms at each
point in the Bose domain. -/
theorem tendsto_boseTransform_of_tailL1 {θ C : ℝ} (hθ0 : 0 < θ)
    {f : ℕ → ℝ → ℂ} {g : ℝ → ℂ}
    (hfm : ∀ n, Measurable (f n)) (hfb : ∀ n x, ‖f n x‖ ≤ C)
    (hgm : Measurable g) (hgb : ∀ x, ‖g x‖ ≤ C) (hC : 0 ≤ C)
    (hL1 : Tendsto (fun n => ∫ x in Ioo (0 : ℝ) 1,
      ‖tailProfile θ (f n) x - tailProfile θ g x‖) atTop (𝓝 0))
    {u : ℂ} (hu : u ∈ boseDomain) :
    Tendsto (fun n => boseTransform (tailProfile θ (f n)) u) atTop
      (𝓝 (boseTransform (tailProfile θ g) u)) := by
  obtain ⟨M, hM0, hM⟩ := exists_kernel_bound_at hu
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hscaled : Tendsto (fun n => M * ∫ x in Ioo (0 : ℝ) 1,
      ‖tailProfile θ (f n) x - tailProfile θ g x‖) atTop (𝓝 0) :=
    by simpa using hL1.const_mul M
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hscaled ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hfn : IntegrableOn (tailProfile θ (f n)) (Ioo (0 : ℝ) 1) :=
    integrableOn_tailProfile_of_bounded hθ0 (hfm n) hC (hfb n)
  have hg : IntegrableOn (tailProfile θ g) (Ioo (0 : ℝ) 1) :=
    integrableOn_tailProfile_of_bounded hθ0 hgm hC hgb
  have hbound := boseTransform_le_kernelBound_mul_tailL1
    (measurable_tailProfile θ (hfm n)) (measurable_tailProfile θ hgm) hfn hg hu hM
  have hnear := hN n hn
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (mul_nonneg hM0 (integral_nonneg fun _ => norm_nonneg _))] at hnear
  rw [Complex.dist_eq]
  exact lt_of_le_of_lt hbound hnear

/-- No bounded moving chronological-tail repair can converge in `L¹` while its Bose response
converges on the sampling interval to the critical profile's response. -/
theorem no_l1_stable_tail_repair :
    ¬ ∃ (θ C : ℝ) (ρ : ℂ) (f : ℕ → ℝ → ℂ) (g : ℝ → ℂ),
      0 < θ ∧ θ < 1 ∧ ρ.re = 1 / 2 ∧ 0 ≤ C ∧
      (∀ n, Measurable (f n)) ∧ (∀ n x, ‖f n x‖ ≤ C) ∧
      Measurable g ∧ (∀ x, ‖g x‖ ≤ C) ∧
      Tendsto (fun n => ∫ x in Ioo (0 : ℝ) 1,
        ‖tailProfile θ (f n) x - tailProfile θ g x‖) atTop (𝓝 0) ∧
      (∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 →
        Tendsto (fun n => boseTransform (tailProfile θ (f n)) (t : ℂ)) atTop
          (𝓝 (boseTransform (criticalProfile θ ρ) (t : ℂ)))) := by
  rintro ⟨θ, C, ρ, f, g, hθ0, hθ1, hρ, hC, hfm, hfb, hgm, hgb, hL1, htarget⟩
  apply heatTransform_separation hθ0 hθ1 hρ hC hgm hgb
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
  have htail := tendsto_boseTransform_of_tailL1 hθ0 hfm hfb hgm hgb hC hL1
    (ofReal_mem_boseDomain ht0)
  exact tendsto_nhds_unique (htarget t ht) htail

end RHTower
