import GaloisForLFunctions.RHTower.ThetaTailFirstMomentKernel

/-!
# Common-translation Loewner propagation fails infinitesimally

The shifted-tail formula makes the negative common-translation derivative of the actual theta-tail
kernel equal to the explicit generator below.  Every distinct two-node compression of that
generator has strictly negative determinant.  Therefore positive-cone kernel positivity cannot be
propagated to the full real line by a common-translation Loewner-decreasing flow.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Candidate positive generator forced by common-translation Loewner decrease of the actual
theta-tail first-moment kernel. -/
def thetaTailCommonTranslationGenerator (a x t : ℝ) : ℝ :=
  (x + t + 2 * a) * thetaCuspFullSource (x + a) * thetaCuspFullSource (t + a)

/-- Fixed integrand whose moving lower cut is common translation of the theta-tail kernel. -/
def thetaTailCommonTranslationIntegrand (x t r : ℝ) : ℝ :=
  (x + t + 2 * r) * thetaCuspFullSource (x + r) * thetaCuspFullSource (t + r)

theorem integrable_thetaTailCommonTranslationIntegrand (x t : ℝ) :
    Integrable (thetaTailCommonTranslationIntegrand x t) := by
  have hshift : Integrable (fun u : ℝ =>
      thetaTailFirstMomentIntegrand x t (u + (x + t))) :=
    (integrable_thetaTailFirstMomentIntegrand x t).comp_add_right (x + t)
  have hscale : Integrable (fun r : ℝ =>
      thetaTailFirstMomentIntegrand x t (2 * r + (x + t))) :=
    (integrable_comp_mul_left_iff
      (fun u : ℝ => thetaTailFirstMomentIntegrand x t (u + (x + t)))
      (by norm_num : (2 : ℝ) ≠ 0)).2 hshift
  refine hscale.congr ?_
  filter_upwards with r
  unfold thetaTailCommonTranslationIntegrand thetaTailFirstMomentIntegrand
  rw [show (2 * r + (x + t) + x - t) / 2 = x + r by ring,
    show (2 * r + (x + t) - x + t) / 2 = t + r by ring]
  ring

/-- Exact moving-cut form of a common translation of the actual theta-tail kernel. -/
theorem thetaTailFirstMomentKernel_commonShift_eq_tail (a x t : ℝ) :
    thetaTailFirstMomentKernel (x + a) (t + a) =
      ∫ r in Ioi a, thetaTailCommonTranslationIntegrand x t r := by
  rw [thetaTailFirstMomentKernel_eq_shiftTail,
    ← setIntegral_Ioi_zero_comp_add_right
      (thetaTailCommonTranslationIntegrand x t) a]
  apply integral_congr_ae
  filter_upwards with r
  unfold thetaTailCommonTranslationIntegrand
  ring_nf

private theorem integral_Ioi_eq_sub_real
    {f : ℝ → ℝ} {c u : ℝ} (hcu : c ≤ u)
    (hint : IntegrableOn f (Ioi c) volume) :
    (∫ t in Ioi u, f t) = (∫ t in Ioi c, f t) - ∫ t in c..u, f t := by
  have hsplit : Ioi c = Ioc c u ∪ Ioi u := by
    ext t
    constructor
    · intro ht
      rcases le_or_gt t u with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h)
      · exact h1
      · exact lt_of_le_of_lt hcu h
  have hdisj : Disjoint (Ioc c u) (Ioi u) := by
    rw [Set.disjoint_left]
    rintro t ⟨_, ht2⟩ ht3
    exact absurd ht3 (not_lt.mpr ht2)
  have hunion : (∫ t in Ioi c, f t) =
      (∫ t in Ioc c u, f t) + ∫ t in Ioi u, f t := by
    rw [hsplit]
    exact setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set (by rw [hsplit]; exact Set.subset_union_left))
      (hint.mono_set (by rw [hsplit]; exact Set.subset_union_right))
  rw [intervalIntegral.integral_of_le hcu, hunion]
  ring

private theorem hasDerivAt_integral_Ioi_real
    {f : ℝ → ℝ} {c y : ℝ} (hcy : c < y)
    (hint : IntegrableOn f (Ioi c) volume)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 y) volume)
    (hcont : ContinuousAt f y) :
    HasDerivAt (fun u : ℝ => ∫ t in Ioi u, f t) (-f y) y := by
  have hII : IntervalIntegrable f volume c y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hcy.le).mpr
      (hint.mono_set Ioc_subset_Ioi_self)
  have hd : HasDerivAt
      (fun u : ℝ => (∫ t in Ioi c, f t) - ∫ t in c..u, f t) (-f y) y := by
    have hbase := intervalIntegral.integral_hasDerivAt_right hII hmeas hcont
    simpa using hbase.const_sub (∫ t in Ioi c, f t)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hcy] with u hu
  exact integral_Ioi_eq_sub_real (le_of_lt hu) hint

/-- The generator is exactly the negative common-translation derivative of the actual kernel. -/
theorem hasDerivAt_thetaTailFirstMomentKernel_commonShift (a x t : ℝ) :
    HasDerivAt (fun u : ℝ => thetaTailFirstMomentKernel (x + u) (t + u))
      (-thetaTailCommonTranslationGenerator a x t) a := by
  have hcont : Continuous (thetaTailCommonTranslationIntegrand x t) := by
    unfold thetaTailCommonTranslationIntegrand
    exact ((continuous_const.add continuous_const).add (continuous_const.mul continuous_id)).mul
      (contDiff_thetaCuspFullSource.continuous.comp
        (continuous_const.add continuous_id)) |>.mul
      (contDiff_thetaCuspFullSource.continuous.comp
        (continuous_const.add continuous_id))
  have hd := hasDerivAt_integral_Ioi_real
    (f := thetaTailCommonTranslationIntegrand x t) (c := a - 1) (y := a)
    (by linarith)
    (integrable_thetaTailCommonTranslationIntegrand x t).integrableOn
    (hcont.stronglyMeasurableAtFilter volume (𝓝 a)) hcont.continuousAt
  simpa only [thetaTailFirstMomentKernel_commonShift_eq_tail,
    thetaTailCommonTranslationGenerator, thetaTailCommonTranslationIntegrand] using hd

theorem thetaTailCommonTranslationGenerator_comm (a x t : ℝ) :
    thetaTailCommonTranslationGenerator a x t =
      thetaTailCommonTranslationGenerator a t x := by
  unfold thetaTailCommonTranslationGenerator
  ring

/-- Exact two-node determinant.  Its sign is independent of all fine theta-source structure. -/
theorem thetaTailCommonTranslationGenerator_twoNode_det
    (a x t : ℝ) :
    thetaTailCommonTranslationGenerator a x x *
          thetaTailCommonTranslationGenerator a t t -
        thetaTailCommonTranslationGenerator a x t ^ 2 =
      -(x - t) ^ 2 *
        (thetaCuspFullSource (x + a) * thetaCuspFullSource (t + a)) ^ 2 := by
  unfold thetaTailCommonTranslationGenerator
  ring

/-- Every distinct two-node compression of the common-translation generator is indefinite. -/
theorem thetaTailCommonTranslationGenerator_twoNode_det_neg
    (a x t : ℝ) (hxt : x ≠ t) :
    thetaTailCommonTranslationGenerator a x x *
          thetaTailCommonTranslationGenerator a t t -
        thetaTailCommonTranslationGenerator a x t ^ 2 < 0 := by
  rw [thetaTailCommonTranslationGenerator_twoNode_det]
  have hdiff : 0 < (x - t) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxt)
  have hx : 0 < thetaCuspFullSource (x + a) :=
    HedenmalmThetaSource.thetaCuspFullSource_pos _
  have ht : 0 < thetaCuspFullSource (t + a) :=
    HedenmalmThetaSource.thetaCuspFullSource_pos _
  have hsource : 0 <
      (thetaCuspFullSource (x + a) * thetaCuspFullSource (t + a)) ^ 2 :=
    sq_pos_of_pos (mul_pos hx ht)
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hdiff) hsource

/-- Closed negative quadratic direction at nodes `0,1` and cut `a=1`.  This directly refutes
positive semidefiniteness of the infinitesimal generator without any spectral hypothesis. -/
theorem thetaTailCommonTranslationGenerator_explicit_quadraticForm_neg :
    let c0 : ℝ := 3 * thetaCuspFullSource 2
    let c1 : ℝ := -2 * thetaCuspFullSource 1
    c0 ^ 2 * thetaTailCommonTranslationGenerator 1 0 0 +
          2 * c0 * c1 * thetaTailCommonTranslationGenerator 1 0 1 +
        c1 ^ 2 * thetaTailCommonTranslationGenerator 1 1 1 < 0 := by
  dsimp [thetaTailCommonTranslationGenerator]
  have h1 : 0 < thetaCuspFullSource 1 :=
    HedenmalmThetaSource.thetaCuspFullSource_pos _
  have h2 : 0 < thetaCuspFullSource 2 :=
    HedenmalmThetaSource.thetaCuspFullSource_pos _
  norm_num
  ring_nf
  nlinarith [sq_pos_of_pos (mul_pos h1 h2)]

/-- Fixed scalar compression used to witness failure of finite common-shift Loewner order. -/
def thetaTailCommonTranslationWitnessQuadratic (u : ℝ) : ℝ :=
  let c0 : ℝ := 3 * thetaCuspFullSource 2
  let c1 : ℝ := -2 * thetaCuspFullSource 1
  c0 ^ 2 * thetaTailFirstMomentKernel u u +
      2 * c0 * c1 * thetaTailFirstMomentKernel u (1 + u) +
    c1 ^ 2 * thetaTailFirstMomentKernel (1 + u) (1 + u)

theorem hasDerivAt_thetaTailCommonTranslationWitnessQuadratic (u : ℝ) :
    HasDerivAt thetaTailCommonTranslationWitnessQuadratic
      (-(let c0 : ℝ := 3 * thetaCuspFullSource 2
          let c1 : ℝ := -2 * thetaCuspFullSource 1
          c0 ^ 2 * thetaTailCommonTranslationGenerator u 0 0 +
              2 * c0 * c1 * thetaTailCommonTranslationGenerator u 0 1 +
            c1 ^ 2 * thetaTailCommonTranslationGenerator u 1 1)) u := by
  let c0 : ℝ := 3 * thetaCuspFullSource 2
  let c1 : ℝ := -2 * thetaCuspFullSource 1
  have h00 := hasDerivAt_thetaTailFirstMomentKernel_commonShift u 0 0
  have h01 := hasDerivAt_thetaTailFirstMomentKernel_commonShift u 0 1
  have h11 := hasDerivAt_thetaTailFirstMomentKernel_commonShift u 1 1
  have hsum := ((h00.const_mul (c0 ^ 2)).add
    (h01.const_mul (2 * c0 * c1))).add
    (h11.const_mul (c1 ^ 2))
  simpa only [thetaTailCommonTranslationWitnessQuadratic, c0, c1,
    zero_add] using hsum.congr_deriv (by ring)

private theorem exists_right_gt_of_hasDerivAt_pos_at
    {f : ℝ → ℝ} {f' a : ℝ} (h : HasDerivAt f f' a) (hf' : 0 < f') :
    ∃ b : ℝ, a < b ∧ f a < f b := by
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t⁻¹ * (f (a + t) - f a) := by
    simpa [smul_eq_mul] using
      h.tendsto_slope_zero_right.eventually (eventually_gt_nhds hf')
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, htSlope, ht⟩ := (hslope.and hpos).exists
  refine ⟨a + t, by linarith, ?_⟩
  rcases (mul_pos_iff.mp htSlope) with hgood | hbad
  · exact sub_pos.mp hgood.2
  · exact False.elim ((not_lt_of_ge (inv_nonneg.mpr ht.le)) hbad.1)

/-- Decisive finite-shift no-go: the actual theta-tail kernel has a positive common shift whose
difference from the cut `1` has a strictly negative two-node quadratic form. -/
theorem exists_thetaTailFirstMomentKernel_commonShift_difference_quadraticForm_neg :
    ∃ b : ℝ, 1 < b ∧
      let c0 : ℝ := 3 * thetaCuspFullSource 2
      let c1 : ℝ := -2 * thetaCuspFullSource 1
      c0 ^ 2 *
            (thetaTailFirstMomentKernel 1 1 - thetaTailFirstMomentKernel b b) +
          2 * c0 * c1 *
            (thetaTailFirstMomentKernel 1 2 - thetaTailFirstMomentKernel b (1 + b)) +
        c1 ^ 2 *
            (thetaTailFirstMomentKernel 2 2 -
              thetaTailFirstMomentKernel (1 + b) (1 + b)) < 0 := by
  have hgen := thetaTailCommonTranslationGenerator_explicit_quadraticForm_neg
  have hderiv := hasDerivAt_thetaTailCommonTranslationWitnessQuadratic 1
  have hderivPos : 0 < deriv thetaTailCommonTranslationWitnessQuadratic 1 := by
    rw [hderiv.deriv]
    simpa only using neg_pos.mpr hgen
  obtain ⟨b, hb, hrise⟩ := exists_right_gt_of_hasDerivAt_pos_at hderiv hderivPos
  refine ⟨b, hb, ?_⟩
  change thetaTailCommonTranslationWitnessQuadratic 1 -
      thetaTailCommonTranslationWitnessQuadratic b < 0
  linarith

end

end RHTower
