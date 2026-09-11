import GaloisForLFunctions.RHTower.ChronologicalTailKernelAnalytic
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The Bose transform of a profile, and its analyticity

For an integrable profile `g` on `(0,1)` put

  `boseTransform g u = ∫_(0)^(1) g(x) h(x u) dx`,

where `h` is the analytic Bose defect kernel of `ChronologicalTailKernelAnalytic`. Both the
heat-transform `F_f` of a tail profile and the critical profile `K_ρ` of the fixed-tail
obstruction are of this form.

The transform is analytic on

  `boseDomain = {u | 0 < Re u ∧ |Im u| < 2π}`,

because `x u` stays in the strip `|Im z| < 2π` for `0 ≤ x ≤ 1`, where the kernel is analytic.
Differentiation under the integral sign works because the extended kernel's derivative is
continuous on the compact set swept out by `x u`, so the dominating function is a constant
multiple of `‖g‖`.

Since `boseDomain` is convex and contains `[1,2]`, a transform vanishing on `[1,2]` vanishes on
the whole positive axis: this is the propagation step of the separation argument, and it needs no
analytic continuation of `h` across `0`.
-/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

namespace RHTower

/-! ### The domain -/

/-- The domain of analyticity of the Bose transform. -/
def boseDomain : Set ℂ := {u : ℂ | 0 < u.re ∧ |u.im| < 2 * Real.pi}

theorem mem_boseDomain {u : ℂ} : u ∈ boseDomain ↔ 0 < u.re ∧ |u.im| < 2 * Real.pi := Iff.rfl

theorem isOpen_boseDomain : IsOpen boseDomain := by
  have h : boseDomain = {z : ℂ | 0 < z.re} ∩ (fun z : ℂ => |z.im|) ⁻¹' (Iio (2 * Real.pi)) := rfl
  rw [h]
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (IsOpen.preimage (continuous_abs.comp Complex.continuous_im) isOpen_Iio)

theorem convex_boseDomain : Convex ℝ boseDomain := by
  have h : boseDomain = {z : ℂ | 0 < Complex.reLm z} ∩
      {z : ℂ | Complex.imLm z < 2 * Real.pi} ∩ {z : ℂ | -(2 * Real.pi) < Complex.imLm z} := by
    ext z
    simp only [mem_boseDomain, Set.mem_inter_iff, Set.mem_setOf_eq, abs_lt]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨h1, h2, h3⟩
  rw [h]
  exact ((convex_halfSpace_gt (LinearMap.isLinear Complex.reLm) 0).inter
    (convex_halfSpace_lt (LinearMap.isLinear Complex.imLm) _)).inter
    (convex_halfSpace_gt (LinearMap.isLinear Complex.imLm) _)

theorem isPreconnected_boseDomain : IsPreconnected boseDomain :=
  convex_boseDomain.isPreconnected

theorem ofReal_mem_boseDomain {t : ℝ} (ht : 0 < t) : (t : ℂ) ∈ boseDomain := by
  refine ⟨?_, ?_⟩
  · simpa using ht
  · simp [Real.pi_pos]

theorem mul_ofReal_mem_boseStrip {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {u : ℂ}
    (hu : u ∈ boseDomain) : (x : ℂ) * u ∈ boseStrip := by
  have him : ((x : ℂ) * u).im = x * u.im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [mem_boseStrip, him, abs_mul, abs_of_nonneg hx0]
  have h2 := hu.2
  have habs : 0 ≤ |u.im| := abs_nonneg _
  nlinarith

/-! ### The transform -/

/-- The Bose transform of a profile supported on `(0,1)`. -/
def boseTransform (g : ℝ → ℂ) (u : ℂ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, g x * boseKernelE ((x : ℂ) * u)

/-- Its derivative in the transform variable. -/
def boseTransformDeriv (g : ℝ → ℂ) (u : ℂ) : ℂ :=
  ∫ x in Ioo (0 : ℝ) 1, g x * (deriv boseKernelE ((x : ℂ) * u) * (x : ℂ))

theorem continuousOn_kernel_comp {u : ℂ} (hu : u ∈ boseDomain) :
    ContinuousOn (fun x : ℝ => boseKernelE ((x : ℂ) * u)) (Ioo (0 : ℝ) 1) := by
  refine boseKernelE_continuousOn.comp ?_ ?_
  · exact (Complex.continuous_ofReal.mul continuous_const).continuousOn
  · intro x hx
    exact mul_ofReal_mem_boseStrip (le_of_lt hx.1) (le_of_lt hx.2) hu

theorem continuousOn_derivKernel_comp {u : ℂ} (hu : u ∈ boseDomain) :
    ContinuousOn (fun x : ℝ => deriv boseKernelE ((x : ℂ) * u) * (x : ℂ)) (Ioo (0 : ℝ) 1) := by
  refine ContinuousOn.mul ?_ Complex.continuous_ofReal.continuousOn
  refine (boseKernelE_analyticOnNhd.deriv.continuousOn).comp ?_ ?_
  · exact (Complex.continuous_ofReal.mul continuous_const).continuousOn
  · intro x hx
    exact mul_ofReal_mem_boseStrip (le_of_lt hx.1) (le_of_lt hx.2) hu

theorem aestronglyMeasurable_boseIntegrand {g : ℝ → ℂ}
    (hg : IntegrableOn g (Ioo (0 : ℝ) 1)) {u : ℂ} (hu : u ∈ boseDomain) :
    AEStronglyMeasurable (fun x : ℝ => g x * boseKernelE ((x : ℂ) * u))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
  hg.aestronglyMeasurable.mul
    ((continuousOn_kernel_comp hu).aestronglyMeasurable measurableSet_Ioo)

theorem aestronglyMeasurable_boseDerivIntegrand {g : ℝ → ℂ}
    (hg : IntegrableOn g (Ioo (0 : ℝ) 1)) {u : ℂ} (hu : u ∈ boseDomain) :
    AEStronglyMeasurable (fun x : ℝ => g x * (deriv boseKernelE ((x : ℂ) * u) * (x : ℂ)))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
  hg.aestronglyMeasurable.mul
    ((continuousOn_derivKernel_comp hu).aestronglyMeasurable measurableSet_Ioo)

/-- A uniform bound for the kernel data over a closed ball inside the domain. -/
theorem exists_kernel_bound {u₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall u₀ r ⊆ boseDomain) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ u ∈ Metric.closedBall u₀ r,
      ‖boseKernelE ((x : ℂ) * u)‖ ≤ M ∧ ‖deriv boseKernelE ((x : ℂ) * u)‖ ≤ M := by
  set K : Set ℂ := (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) '' (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall u₀ r)
    with hK
  have hKcompact : IsCompact K := by
    refine (isCompact_Icc.prod (ProperSpace.isCompact_closedBall u₀ r)).image ?_
    exact (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
  have hKsub : K ⊆ boseStrip := by
    rintro z ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
    exact mul_ofReal_mem_boseStrip hx.1 hx.2 (hball hu)
  obtain ⟨M₁, hM₁⟩ := hKcompact.exists_bound_of_continuousOn
    (boseKernelE_continuousOn.mono hKsub)
  obtain ⟨M₂, hM₂⟩ := hKcompact.exists_bound_of_continuousOn
    ((boseKernelE_analyticOnNhd.deriv.continuousOn).mono hKsub)
  refine ⟨max (max M₁ M₂) 0, le_max_right _ _, ?_⟩
  intro x hx u hu
  have hmem : (x : ℂ) * u ∈ K := ⟨(x, u), ⟨hx, hu⟩, rfl⟩
  exact ⟨le_trans (hM₁ _ hmem) (le_trans (le_max_left _ _) (le_max_left _ _)),
    le_trans (hM₂ _ hmem) (le_trans (le_max_right _ _) (le_max_left _ _))⟩

/-- **Differentiation under the integral sign for the Bose transform.** -/
theorem hasDerivAt_boseTransform {g : ℝ → ℂ} (hg : IntegrableOn g (Ioo (0 : ℝ) 1))
    {u₀ : ℂ} (hu₀ : u₀ ∈ boseDomain) :
    HasDerivAt (boseTransform g) (boseTransformDeriv g u₀) u₀ := by
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp isOpen_boseDomain u₀ hu₀
  set r : ℝ := ε / 2 with hrdef
  have hr : 0 < r := by positivity
  have hclosed : Metric.closedBall u₀ r ⊆ boseDomain := by
    refine subset_trans (Metric.closedBall_subset_ball ?_) hεsub
    rw [hrdef]; linarith
  have hballsub : Metric.ball u₀ r ⊆ Metric.closedBall u₀ r := Metric.ball_subset_closedBall
  obtain ⟨M, hM0, hMbound⟩ := exists_kernel_bound hr hclosed
  have hsnhds : Metric.ball u₀ r ∈ 𝓝 u₀ := Metric.ball_mem_nhds _ hr
  have hmeas : ∀ᶠ u in 𝓝 u₀, AEStronglyMeasurable
      (fun x : ℝ => g x * boseKernelE ((x : ℂ) * u)) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    filter_upwards [hsnhds] with u hu
    exact aestronglyMeasurable_boseIntegrand hg (hclosed (hballsub hu))
  have hint : Integrable (fun x : ℝ => g x * boseKernelE ((x : ℂ) * u₀))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    refine Integrable.mono' (g := fun x : ℝ => M * ‖g x‖) (hg.norm.const_mul M)
      (aestronglyMeasurable_boseIntegrand hg hu₀) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hb := (hMbound x ⟨hx.1.le, hx.2.le⟩ u₀ (Metric.mem_closedBall_self hr.le)).1
    rw [norm_mul]
    calc ‖g x‖ * ‖boseKernelE ((x : ℂ) * u₀)‖ ≤ ‖g x‖ * M :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = M * ‖g x‖ := by ring
  have hbound : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ u ∈ Metric.ball u₀ r,
      ‖g x * (deriv boseKernelE ((x : ℂ) * u) * (x : ℂ))‖ ≤ M * ‖g x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx u hu
    have hb := (hMbound x ⟨hx.1.le, hx.2.le⟩ u (hballsub hu)).2
    have hx1 : ‖(x : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
      exact hx.2.le
    rw [norm_mul, norm_mul]
    calc ‖g x‖ * (‖deriv boseKernelE ((x : ℂ) * u)‖ * ‖(x : ℂ)‖)
        ≤ ‖g x‖ * (M * 1) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul hb hx1 (norm_nonneg _) hM0) (norm_nonneg _)
      _ = M * ‖g x‖ := by ring
  have hdiff : ∀ᵐ x ∂(volume.restrict (Ioo (0 : ℝ) 1)), ∀ u ∈ Metric.ball u₀ r,
      HasDerivAt (fun u : ℂ => g x * boseKernelE ((x : ℂ) * u))
        (g x * (deriv boseKernelE ((x : ℂ) * u) * (x : ℂ))) u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx u hu
    have hmemstrip : (x : ℂ) * u ∈ boseStrip :=
      mul_ofReal_mem_boseStrip hx.1.le hx.2.le (hclosed (hballsub hu))
    have hkd : HasDerivAt boseKernelE (deriv boseKernelE ((x : ℂ) * u)) ((x : ℂ) * u) := by
      have hda : DifferentiableAt ℂ boseKernelE ((x : ℂ) * u) :=
        boseKernelE_differentiableOn.differentiableAt (isOpen_boseStrip.mem_nhds hmemstrip)
      exact hda.hasDerivAt
    have hin : HasDerivAt (fun u : ℂ => (x : ℂ) * u) (x : ℂ) u := by
      simpa using (hasDerivAt_id u).const_mul ((x : ℂ))
    exact (HasDerivAt.comp u hkd hin).const_mul (g x)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun x : ℝ => M * ‖g x‖) hsnhds hmeas hint
    (aestronglyMeasurable_boseDerivIntegrand hg hu₀) hbound (hg.norm.const_mul M) hdiff
  exact hres.2

theorem differentiableOn_boseTransform {g : ℝ → ℂ} (hg : IntegrableOn g (Ioo (0 : ℝ) 1)) :
    DifferentiableOn ℂ (boseTransform g) boseDomain := fun u hu =>
  ((hasDerivAt_boseTransform hg hu).differentiableAt).differentiableWithinAt

theorem analyticOnNhd_boseTransform {g : ℝ → ℂ} (hg : IntegrableOn g (Ioo (0 : ℝ) 1)) :
    AnalyticOnNhd ℂ (boseTransform g) boseDomain :=
  (differentiableOn_boseTransform hg).analyticOnNhd isOpen_boseDomain

/-! ### Propagation from `[1,2]` to the whole positive axis -/

/-- **The identity theorem for the Bose transform.** A transform vanishing on the sampling
interval `[1,2]` vanishes on the whole positive axis. -/
theorem boseTransform_eq_zero_of_eqOn_Icc {g : ℝ → ℂ} (hg : IntegrableOn g (Ioo (0 : ℝ) 1))
    (h : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 → boseTransform g (t : ℂ) = 0) :
    Set.EqOn (boseTransform g) 0 boseDomain := by
  set z₀ : ℂ := ((3 / 2 : ℝ) : ℂ) with hz₀
  have hz₀mem : z₀ ∈ boseDomain := ofReal_mem_boseDomain (by norm_num)
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, boseTransform g z = 0 := by
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) := h1.inv_tendsto_atTop
      simpa [one_div] using h2
    have htend : Tendsto (fun n : ℕ => ((3 / 2 + 1 / (n + 2 : ℝ) : ℝ) : ℂ)) atTop (𝓝[≠] z₀) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · rw [hz₀]
        refine (Complex.continuous_ofReal.tendsto _).comp ?_
        simpa using tendsto_const_nhds.add hinv
      · filter_upwards with n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hz₀]
        intro hcontra
        have := Complex.ofReal_injective hcontra
        have hpos : (0 : ℝ) < 1 / (n + 2 : ℝ) := by positivity
        linarith
    refine htend.frequently (Frequently.of_forall fun n => ?_)
    refine h _ ⟨?_, ?_⟩
    · have : (0 : ℝ) < 1 / (n + 2 : ℝ) := by positivity
      linarith
    · have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num) hn
      linarith
  exact (analyticOnNhd_boseTransform hg).eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_boseDomain hz₀mem hfreq

theorem boseTransform_ofReal_eq_zero {g : ℝ → ℂ} (hg : IntegrableOn g (Ioo (0 : ℝ) 1))
    (h : ∀ t : ℝ, t ∈ Icc (1 : ℝ) 2 → boseTransform g (t : ℂ) = 0) {t : ℝ} (ht : 0 < t) :
    boseTransform g (t : ℂ) = 0 :=
  boseTransform_eq_zero_of_eqOn_Icc hg h (ofReal_mem_boseDomain ht)

end RHTower
