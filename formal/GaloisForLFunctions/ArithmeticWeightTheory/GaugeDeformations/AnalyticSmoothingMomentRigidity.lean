import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticSmoothingScaling
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.AnalyticSmoothingMoment

/-!
# Endpoint moment obstruction to entire scaling

A positive real Taylor coefficient produces a nonremovable shifted
singularity. Continuation through the upper half-plane isolates its
logarithmic factor and a nonzero boundary unit. Entire scaling therefore
forces real endpoint derivative at most minus two, excluding all real
affine mixtures of normalized unimodular analytic profiles.
-/

open Complex Filter Topology Metric Set
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Continue a finite logarithmic head through the upper half-plane, leaving a holomorphic tail. -/
def continuedSmoothingProfile (Φ : ℂ → ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  analyticSmoothingScalingProfile Φ (k + 1) w *
    Complex.exp (-(∑ j ∈ Finset.range (k + 1),
      smoothingTaylorCoefficient Φ j * Complex.log (w + (j : ℂ))))

/-- The remaining unit along the upper approach to the kth shifted singularity. -/
def singularSmoothingUnit (Φ : ℂ → ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  analyticSmoothingScalingProfile Φ (k + 1) (-(k : ℂ) + (t : ℂ) * I) *
    Complex.exp (-(∑ j ∈ Finset.range k,
      smoothingTaylorCoefficient Φ j * Complex.log (-(k : ℂ) + (t : ℂ) * I + (j : ℂ))))

theorem singularSmoothingUnit_zero_ne (Φ : ℂ → ℂ) (k : ℕ) :
    singularSmoothingUnit Φ k 0 ≠ 0 :=
  mul_ne_zero (analyticSmoothingScalingProfile_ne_zero _ _ _) (Complex.exp_ne_zero _)

theorem continuedSmoothingProfile_eq {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (k : ℕ) {w : ℂ} (hw : 0 < w.re) :
    continuedSmoothingProfile Φ k w = analyticSmoothingScalingProfile Φ 0 w := by
  have hh (n : ℕ) : analyticSmoothingScalingProfile Φ 0 w =
      analyticSmoothingScalingProfile Φ n w * Complex.exp
        (-(∑ j ∈ Finset.range n, smoothingTaylorCoefficient Φ j * Complex.log (w + (j : ℂ)))) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih, analyticSmoothingScalingProfile_factorization hR hΦ n
        (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith only [hw, hn]),
        Finset.sum_range_succ, neg_add, Complex.exp_add]
      simp only [neg_mul]
      ring
  exact (hh (k + 1)).symm

theorem analyticOnNhd_continuedSmoothingProfile {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (k : ℕ) :
    AnalyticOnNhd ℂ (continuedSmoothingProfile Φ k)
      ({w : ℂ | -((k + 1 : ℕ) : ℝ) < w.re} ∩ {w : ℂ | 0 < w.im}) := by
  intro w hw
  have heq : (∑ j ∈ Finset.range (k + 1), fun z : ℂ =>
      smoothingTaylorCoefficient Φ j * Complex.log (z + (j : ℂ))) =
      (fun z => ∑ j ∈ Finset.range (k + 1),
        smoothingTaylorCoefficient Φ j * Complex.log (z + (j : ℂ))) := by
    funext z
    simp only [Finset.sum_apply]
  have hh : AnalyticAt ℂ (fun z => ∑ j ∈ Finset.range (k + 1),
      smoothingTaylorCoefficient Φ j * Complex.log (z + (j : ℂ))) w := by
    rw [← heq]
    apply (Finset.range (k + 1)).analyticAt_sum
    intro j _
    have hl : AnalyticAt ℂ (fun z : ℂ => z + (j : ℂ)) w :=
      analyticAt_id.add analyticAt_const
    have hslit : w + (j : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inr (by
        simp only [Complex.add_im, Complex.natCast_im, add_zero]
        exact hw.2.ne'))
    exact (show AnalyticAt ℂ (fun _ : ℂ => smoothingTaylorCoefficient Φ j) w from
      analyticAt_const).mul (hl.clog hslit)
  exact (analyticOnNhd_analyticSmoothingScalingProfile hR hΦ (k + 1) w hw.1).mul hh.neg.cexp

/-- All logarithms except the selected one have finite upper boundary values. -/
theorem tendsto_singularSmoothingUnit {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) (k : ℕ) :
    Tendsto (singularSmoothingUnit Φ k) (𝓝[>] 0) (𝓝 (singularSmoothingUnit Φ k 0)) := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hw : Tendsto (fun t : ℝ => -(k : ℂ) + (t : ℂ) * I) (𝓝[>] 0) (𝓝 (-(k : ℂ))) := by
    simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (ht.mul_const I)
  have htail := (analyticOnNhd_analyticSmoothingScalingProfile hR hΦ (k + 1) (-(k : ℂ))
    (by simp only [mem_setOf_eq, Complex.neg_re, Complex.natCast_re, Nat.cast_add, Nat.cast_one]; linarith)).continuousAt.tendsto.comp hw
  have hhead : Tendsto (fun t : ℝ => ∑ j ∈ Finset.range k,
      smoothingTaylorCoefficient Φ j * Complex.log (-(k : ℂ) + (t : ℂ) * I + (j : ℂ)))
      (𝓝[>] 0) (𝓝 (∑ j ∈ Finset.range k,
      smoothingTaylorCoefficient Φ j * Complex.log (-(k : ℂ) + (j : ℂ)))) := by
    apply tendsto_finsetSum
    intro j hj
    apply Tendsto.const_mul
    have hjk : (j : ℝ) < k := by exact_mod_cast Finset.mem_range.mp hj
    have hlog := Complex.continuousWithinAt_log_of_re_neg_of_im_zero
      (z := -(k : ℂ) + (j : ℂ)) (by
        simp only [Complex.add_re, Complex.neg_re, Complex.natCast_re]
        linarith only [hjk]) (by simp)
    apply hlog.tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hw.add_const (j : ℂ), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    simpa only [mem_setOf_eq, Complex.add_im, Complex.neg_im, Complex.natCast_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, neg_zero, zero_add] using ht.le
  unfold singularSmoothingUnit
  simpa only [Complex.ofReal_zero, zero_mul, add_zero, Function.comp_apply] using htail.mul hhead.neg.cexp

theorem continuedSmoothingProfile_remove_factor (Φ : ℂ → ℂ) (k : ℕ) (t : ℝ) :
    continuedSmoothingProfile Φ k (-(k : ℂ) + (t : ℂ) * I) *
      Complex.exp (smoothingTaylorCoefficient Φ k * Complex.log ((t : ℂ) * I)) =
        singularSmoothingUnit Φ k t := by
  rw [continuedSmoothingProfile, Finset.sum_range_succ]
  rw [show -(k : ℂ) + (t : ℂ) * I + (k : ℂ) = (t : ℂ) * I by ring]
  rw [mul_assoc, ← Complex.exp_add, show
    -(∑ j ∈ Finset.range k, smoothingTaylorCoefficient Φ j *
      Complex.log (-(k : ℂ) + (t : ℂ) * I + (j : ℂ)) +
      smoothingTaylorCoefficient Φ k * Complex.log ((t : ℂ) * I)) +
      smoothingTaylorCoefficient Φ k * Complex.log ((t : ℂ) * I) =
    -(∑ j ∈ Finset.range k, smoothingTaylorCoefficient Φ j *
      Complex.log (-(k : ℂ) + (t : ℂ) * I + (j : ℂ))) by ring]
  rfl

/-- A positive real branch exponent vanishes after inversion along an upper ray. -/
theorem tendsto_exp_positive_log_vertical {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => Complex.exp (a * Complex.log ((t : ℂ) * I)))
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hl := Real.tendsto_exp_atBot.comp
    (Filter.Tendsto.const_mul_atBot ha Real.tendsto_log_nhdsGT_zero)
  have hh := hl.mul_const (Real.exp (-a.im * (Real.pi / 2)))
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [Complex.norm_exp, Complex.log_ofReal_mul ht Complex.I_ne_zero, Complex.log_I]
  simp only [Function.comp_apply]
  rw [← Real.exp_add]
  congr 1
  norm_num [Complex.mul_re, Complex.mul_im]
  ring

/-- A positive real coefficient prevents a continuous filling of its shifted branch. -/
theorem continuedSmoothingProfile_no_continuous_extension {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    {k : ℕ} (hk : 0 < (smoothingTaylorCoefficient Φ k).re) :
    ¬ ∃ F : ℂ → ℂ, ContinuousAt F (-(k : ℂ)) ∧
      ∀ᶠ t : ℝ in 𝓝[>] 0,
        F (-(k : ℂ) + (t : ℂ) * I) =
          continuedSmoothingProfile Φ k (-(k : ℂ) + (t : ℂ) * I) := by
  rintro ⟨F, hF, he⟩
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hw : Tendsto (fun t : ℝ => -(k : ℂ) + (t : ℂ) * I) (𝓝[>] 0) (𝓝 (-(k : ℂ))) := by
    simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (ht.mul_const I)
  have hz := (hF.tendsto.comp hw).mul (tendsto_exp_positive_log_vertical hk)
  simp only [mul_zero] at hz
  have hzero : Tendsto (singularSmoothingUnit Φ k) (𝓝[>] 0) (𝓝 0) := by
    apply hz.congr'
    filter_upwards [he] with t ht
    simp only [Function.comp_apply]
    rw [ht, continuedSmoothingProfile_remove_factor]
  exact singularSmoothingUnit_zero_ne Φ k
    (tendsto_nhds_unique (tendsto_singularSmoothingUnit hR hΦ k) hzero)

/-- A positive real Taylor coefficient rules out every entire continuation of the profile. -/
theorem analyticSmoothingScalingProfile_no_entire_extension_of_positive_coefficient
    {Φ : ℂ → ℂ} {R : NNReal} (hR : 1 < (R : ℝ))
    (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R)) {k : ℕ}
    (hk : 0 < (smoothingTaylorCoefficient Φ k).re) :
    ¬ ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ w : ℂ, 0 < w.re → analyticSmoothingScalingProfile Φ 0 w = F w := by
  rintro ⟨F, hF, he⟩
  let D : Set ℂ := {w : ℂ | -((k + 1 : ℕ) : ℝ) < w.re} ∩ {w : ℂ | 0 < w.im}
  have hD : IsPreconnected D :=
    ((convex_halfSpace_re_gt (-((k + 1 : ℕ) : ℝ))).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hFanalytic : AnalyticOnNhd ℂ F D := fun w _ => hF.analyticAt w
  have hz : (1 + I : ℂ) ∈ D := by
    constructor
    · simp only [mem_setOf_eq, Complex.add_re, Complex.one_re, Complex.I_re, add_zero]
      have hn : (0 : ℝ) ≤ (k + 1 : ℕ) := Nat.cast_nonneg _
      linarith only [hn]
    · norm_num
  have hev : continuedSmoothingProfile Φ k =ᶠ[𝓝 (1 + I)] F := by
    have hnh : ∀ᶠ w : ℂ in 𝓝 (1 + I), 0 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnh] with w hw
    exact (continuedSmoothingProfile_eq hR hΦ k hw).trans (he w hw)
  have hid := (analyticOnNhd_continuedSmoothingProfile hR hΦ k).eqOn_of_preconnected_of_eventuallyEq
    hFanalytic hD hz hev
  apply continuedSmoothingProfile_no_continuous_extension hR hΦ hk
  refine ⟨F, hF.continuous.continuousAt, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  symm
  apply hid
  constructor
  · simp only [mem_setOf_eq, Complex.add_re, Complex.neg_re, Complex.natCast_re,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Nat.cast_add, Nat.cast_one]
    linarith
  · simpa only [mem_setOf_eq, Complex.add_im, Complex.neg_im, Complex.natCast_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, neg_zero, zero_add] using ht

#print axioms continuedSmoothingProfile_no_continuous_extension
#print axioms analyticSmoothingScalingProfile_no_entire_extension_of_positive_coefficient


/-- Endpoint tangency forces a surviving singular shift and excludes entire scaling profiles. -/
theorem analyticSmoothing_endpoint_moment_rigidity {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (h0 : Φ 0 = 1) (h1 : Φ 1 = -1) (ht : (deriv Φ 1).re = 0) :
    (∃ k : ℕ, 0 < k ∧ 0 < (smoothingTaylorCoefficient Φ k).re ∧
      singularSmoothingUnit Φ k 0 ≠ 0 ∧
      Tendsto (fun t : ℝ => continuedSmoothingProfile Φ k (-(k : ℂ) + (t : ℂ) * I) *
        Complex.exp (smoothingTaylorCoefficient Φ k * Complex.log ((t : ℂ) * I)))
        (𝓝[>] 0) (𝓝 (singularSmoothingUnit Φ k 0)) ∧
      ¬ ∃ F : ℂ → ℂ, ContinuousAt F (-(k : ℂ)) ∧
        ∀ᶠ t : ℝ in 𝓝[>] 0, F (-(k : ℂ) + (t : ℂ) * I) =
          continuedSmoothingProfile Φ k (-(k : ℂ) + (t : ℂ) * I)) ∧
    (¬ ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ w : ℂ, 0 < w.re → analyticSmoothingScalingProfile Φ 0 w = F w) ∧
    ¬ ∃ P : Polynomial ℂ, ∀ w : ℂ, 0 < w.re →
      analyticSmoothingScalingProfile Φ 0 w = P.eval w := by
  obtain ⟨k, hk0, hk⟩ := analyticSmoothing_exists_positive_real_coefficient hR hΦ h0 h1 ht
  have hn := analyticSmoothingScalingProfile_no_entire_extension_of_positive_coefficient hR hΦ hk
  refine ⟨⟨k, hk0, hk, singularSmoothingUnit_zero_ne Φ k, ?_,
    continuedSmoothingProfile_no_continuous_extension hR hΦ hk⟩, hn, ?_⟩
  · simpa only [continuedSmoothingProfile_remove_factor] using tendsto_singularSmoothingUnit hR hΦ k
  · rintro ⟨P, hP⟩
    exact hn ⟨P.eval, P.differentiable, hP⟩

/-- Cancellation in any finite real affine mixture cannot produce an entire scaling profile. -/
theorem analyticPhase_affine_average_no_entire_scaling {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (Φ : ι → ℂ → ℂ) {R : NNReal}
    (hR : 1 < (R : ℝ)) (hc : ∑ j ∈ s, c j = 1)
    (hΦ : ∀ j ∈ s, AnalyticOnNhd ℂ (Φ j) (closedBall 0 R))
    (h0 : ∀ j ∈ s, Φ j 0 = 1) (h1 : ∀ j ∈ s, Φ j 1 = -1)
    (hu : ∀ j ∈ s, ∀ x : ℝ, x ∈ Icc 0 1 → ‖Φ j (x : ℂ)‖ = 1) :
    let Ψ : ℂ → ℂ := fun z => ∑ j ∈ s, (c j : ℂ) * Φ j z
    (∃ k : ℕ, 0 < k ∧ 0 < (smoothingTaylorCoefficient Ψ k).re) ∧
    (¬ ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ w : ℂ, 0 < w.re → analyticSmoothingScalingProfile Ψ 0 w = F w) ∧
    ¬ ∃ P : Polynomial ℂ, ∀ w : ℂ, 0 < w.re →
      analyticSmoothingScalingProfile Ψ 0 w = P.eval w := by
  obtain ⟨ha, hz, ho, ht⟩ := analyticPhase_affine_average s c Φ hR hc hΦ h0 h1 hu
  have hh := analyticSmoothing_endpoint_moment_rigidity hR ha hz ho ht
  exact ⟨analyticSmoothing_exists_positive_real_coefficient hR ha hz ho ht, hh.2⟩

#print axioms analyticSmoothing_endpoint_moment_rigidity
#print axioms analyticPhase_affine_average_no_entire_scaling


/-- Nonpositive real coefficients force an endpoint slope no greater than the coefficient mass. -/
theorem analyticSmoothing_nonpositive_endpoint_bound {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (h0 : Φ 0 = 1) (h1 : Φ 1 = -1)
    (hn : ∀ k : ℕ, (smoothingTaylorCoefficient Φ k).re ≤ 0) :
    (deriv Φ 1).re ≤ -2 := by
  have hm := Complex.hasSum_re (smoothingTaylor_hasSum_firstMoment hR hΦ)
  have hc := Complex.hasSum_re
    (Summable.of_norm (summable_norm_smoothingTaylorCoefficient hR hΦ)).hasSum
  rw [tsum_smoothingTaylorCoefficient hR hΦ h1] at hc
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at hm
  have hz := smoothingTaylorCoefficient_zero hR hΦ h0
  have hle := hm.summable.tsum_le_tsum (g := fun n : ℕ => (smoothingTaylorCoefficient Φ n).re)
    (fun n => by
      by_cases hn0 : n = 0
      · simp only [hn0, hz, Complex.zero_re, mul_zero, le_refl]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
        nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hn1) (hn n)])
    hc.summable
  rw [hm.tsum_eq, hc.tsum_eq] at hle
  norm_num at hle
  exact hle

/-- Entire scaling profiles necessarily have real endpoint slope at most minus two. -/
theorem analyticSmoothing_entire_endpoint_bound {Φ : ℂ → ℂ} {R : NNReal}
    (hR : 1 < (R : ℝ)) (hΦ : AnalyticOnNhd ℂ Φ (closedBall 0 R))
    (h0 : Φ 0 = 1) (h1 : Φ 1 = -1)
    (hE : ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ w : ℂ, 0 < w.re → analyticSmoothingScalingProfile Φ 0 w = F w) :
    (deriv Φ 1).re ≤ -2 := by
  apply analyticSmoothing_nonpositive_endpoint_bound hR hΦ h0 h1
  intro k
  exact le_of_not_gt (fun hk =>
    analyticSmoothingScalingProfile_no_entire_extension_of_positive_coefficient hR hΦ hk hE)

#print axioms analyticSmoothing_entire_endpoint_bound

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
