import GaloisForLFunctions.RHTower.CHMDMasslessCramerContinuation

/-!
# CHMD: the light-cone transmutation in complex time

For a function `A` of complex time define the (even) light-cone transmutation

`L[A](z) = A(z) − z² ∫_0^1 B(2z²(1−t²)) A(zt) dt`     (`lightConeTransmuteC`),

with the entire Bessel kernel `B(w) = Σ (−w/4)^k/(k!(k+1)!)`.  The light-cone identity at mass² `= 2`
(`cos_mul_eq_lightCone_half`) says `cos(z√(r²+2)) = L[cos(· r)](z)` for every complex `z, r`.

* **Zero side** (`kgZeroWave_eq_lightConeTransmuteC`): on the time strip `|Im z| < 1` the
  Klein–Gordon zero-side wave is the transmutation of the massless one,
  `Φ(z) = Φ₀(z) − z² ∫_0^1 B(2z²(1−t²)) Φ₀(zt) dt`.
* **Holomorphy** (`differentiableAt_lightConeTail`): the transmutation tail is holomorphic at `z₁`
  as soon as `A` is analytic along the segment `[0, z₁]`.  So the transmutation propagates every
  analytic continuation of `Φ₀` to `Φ`: it only ever samples `Φ₀` on the segment from `0` to `z`.
-/

open Complex MeasureTheory Set Filter Topology Metric Zeta23
open scoped Real
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

open RHTower.CHMDGrowthCollapse

/-- The light-cone transmutation `L[A](z) = A(z) − z² ∫_0^1 B(2z²(1−t²)) A(zt) dt`. -/
def lightConeTransmuteC (A : ℂ → ℂ) (z : ℂ) : ℂ :=
  A z - z ^ 2 * ∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * A (z * t)

theorem norm_lightConeBessel_light_cone_le (z : ℂ) {t : ℝ} (ht : |t| ≤ 1) :
    ‖lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2))‖ ≤ Real.exp (‖z‖ ^ 2 / 2) := by
  refine (norm_lightConeBessel_le _).trans (Real.exp_le_exp.mpr ?_)
  have ht2 : |1 - t ^ 2| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [abs_nonneg t, sq_abs t, abs_le.mp ht]
  rw [norm_mul, norm_mul, norm_pow, show (1 - (t : ℂ) ^ 2) = ((1 - t ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have := mul_le_mul_of_nonneg_left ht2 (by positivity : (0 : ℝ) ≤ 2 * ‖z‖ ^ 2)
  linarith

/-- **The light-cone identity in even form**: for `w² = r² + 2`,
`cos(z w) = cos(z r) − z² ∫_0^1 B(2z²(1−t²)) cos(z t r) dt`. -/
theorem cos_mul_eq_lightCone_half (z r w : ℂ) (hw : w ^ 2 = r ^ 2 + 2) :
    Complex.cos (z * w) = Complex.cos (z * r) -
      z ^ 2 * ∫ t in (0 : ℝ)..1,
        lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * Complex.cos (z * t * r) := by
  have h := cos_mul_eq_lightCone z r 2 w hw
  set g : ℝ → ℂ := fun t => lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
    Complex.cos (z * r * t) with hg
  have hgc : Continuous g := by
    simp only [hg]
    exact (differentiable_lightConeBessel.continuous.comp (by fun_prop)).mul (by fun_prop)
  have heven : ∀ t, g (-t) = g t := by
    intro t; simp only [hg]; push_cast
    rw [neg_sq, show z * r * -(t : ℂ) = -(z * r * t) by ring, Complex.cos_neg]
  have hsym : ∫ t in (-1 : ℝ)..0, g t = ∫ t in (0 : ℝ)..1, g t := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) g
    simp only [neg_zero] at this
    rw [← this]
    exact intervalIntegral.integral_congr fun t _ => heven t
  have hsplit : ∫ t in (-1 : ℝ)..1, g t = 2 * ∫ t in (0 : ℝ)..1, g t := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _), hsym]
    ring
  have hcomm : (∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
      Complex.cos (z * t * r)) = ∫ t in (0 : ℝ)..1, g t := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hg]
    rw [mul_right_comm z (t : ℂ) r]
  rw [hcomm]
  have h' : Complex.cos (z * w) = Complex.cos (z * r) - 2 * z ^ 2 / 4 * ∫ t in (-1 : ℝ)..1, g t := h
  rw [h', hsplit]
  ring

/-! ## The zero side -/

/-- **The Klein–Gordon zero-side wave is the transmutation of the massless one** on `|Im z| < 1`. -/
theorem kgZeroWave_eq_lightConeTransmuteC {z : ℂ} (hz : |z.im| < 1) :
    kgZeroWave z = lightConeTransmuteC masslessZeroWave z := by
  haveI : Countable zetaZeroConfig.carrier := WeilConditional.countable_carrier.to_subtype
  set F : zetaZeroConfig.carrier → ℝ → ℂ := fun ρ t =>
    lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
      ((zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * t * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ))
    with hF
  have hint : HasSum (fun ρ => ∫ t in (0 : ℝ)..1, F ρ t)
      (∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
        masslessZeroWave (z * t)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun ρ _ => Real.exp (‖z‖ ^ 2 / 2) * (sechConst * Real.exp (|z.re| / 2) *
        ((zetaZeroConfig.mult ρ : ℝ) * Real.exp (-((1 - |z.im|) *
          |(Zeta23.gammaOf (ρ : ℂ)).re|)))))
      (fun ρ => (Continuous.aestronglyMeasurable (by
        simp only [hF]
        exact (differentiable_lightConeBessel.continuous.comp (by fun_prop)).mul (by fun_prop))))
      (fun ρ => Eventually.of_forall fun t ht => ?_)
      (Eventually.of_forall fun _ _ =>
        (((summable_mult_mul_exp_neg_abs_re (by linarith : (0 : ℝ) < 1 - |z.im|)).mul_left
          (sechConst * Real.exp (|z.re| / 2))).mul_left (Real.exp (‖z‖ ^ 2 / 2))))
      intervalIntegrable_const
      (Eventually.of_forall fun t ht => ?_)
    · rw [Set.uIoc_of_le zero_le_one] at ht
      have hta : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      simp only [hF]
      rw [norm_mul]
      refine mul_le_mul (norm_lightConeBessel_light_cone_le z hta)
        (norm_masslessTerm_le (z := z * t) ?_ ?_ ρ) (norm_nonneg _) (Real.exp_pos _).le
      · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hta
      · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) hta
    · have hzt : z * t ∈ causalTimeStrip := by
        rw [Set.uIoc_of_le zero_le_one] at ht
        show |(z * t).im| < 1
        rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, abs_mul]
        have : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        nlinarith [abs_nonneg z.im, abs_nonneg t]
      exact ((summable_masslessTerm _ hzt).hasSum).mul_left _
  have hterm : ∀ ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * kgFreq ρ) * kgWeight ρ) =
        (zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * Zeta23.gammaOf (ρ : ℂ)) * kgWeight ρ) -
          z ^ 2 * ∫ t in (0 : ℝ)..1, F ρ t := by
    intro ρ
    rw [cos_mul_eq_lightCone_half z _ _ (kgFreq_sq ρ)]
    simp only [hF]
    rw [show (fun t : ℝ => lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
        ((zetaZeroConfig.mult ρ : ℂ) * (Complex.cos (z * t * Zeta23.gammaOf (ρ : ℂ)) *
          kgWeight ρ))) = fun t : ℝ => ((zetaZeroConfig.mult ρ : ℂ) * kgWeight ρ) *
        (lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
          Complex.cos (z * t * Zeta23.gammaOf (ρ : ℂ))) by funext t; ring,
      intervalIntegral.integral_const_mul]
    ring
  have hs := summable_masslessTerm z hz
  unfold kgZeroWave lightConeTransmuteC masslessZeroWave
  simp_rw [hterm]
  rw [hs.tsum_sub (hint.summable.mul_left _), tsum_mul_left, hint.tsum_eq]
  rfl

/-! ## Holomorphy of the transmutation tail -/

/-- **The transmutation tail is holomorphic** at `z₁` whenever `A` is analytic along `[0, z₁]`. -/
theorem differentiableAt_lightConeTail {A : ℂ → ℂ} {z₁ : ℂ}
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ A (z₁ * t)) :
    DifferentiableAt ℂ (fun z => ∫ t in (0 : ℝ)..1,
      lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * A (z * t)) z₁ := by
  set Ω := {w : ℂ | AnalyticAt ℂ A w}
  have hΩ : IsOpen Ω := isOpen_analyticAt ℂ A
  set S := (fun t : ℝ => z₁ * t) '' Icc (0 : ℝ) 1
  have hSc : IsCompact S := isCompact_Icc.image (continuous_const.mul continuous_ofReal)
  have hSΩ : S ⊆ Ω := by rintro _ ⟨t, ht, rfl⟩; exact hA t ht
  obtain ⟨δ, hδ, hthick⟩ := hSc.exists_thickening_subset_open hΩ hSΩ
  set r := δ / 2 with hr
  have hr0 : 0 < r := by positivity
  set K := (fun p : ℂ × ℝ => p.1 * p.2) '' (closedBall z₁ r ×ˢ Icc (0 : ℝ) 1)
  have hKc : IsCompact K := ((isCompact_closedBall z₁ r).prod isCompact_Icc).image
    (continuous_fst.mul (continuous_ofReal.comp continuous_snd))
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    refine hthick (Metric.mem_thickening_iff.mpr ⟨z₁ * t, ⟨t, ht, rfl⟩, ?_⟩)
    rw [dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1, ← dist_eq_norm]
    have h1 : dist z z₁ ≤ r := mem_closedBall.mp hz
    calc dist z z₁ * t ≤ r * 1 := mul_le_mul h1 ht.2 ht.1 hr0.le
      _ < δ := by rw [hr]; linarith
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    fun w hw => (hKΩ hw).continuousAt.continuousWithinAt
  set c : ℝ → ℝ := fun x => max 0 (min x 1) with hc
  have hc0 : ∀ x, 0 ≤ c x := fun x => le_max_left _ _
  have hc1 : ∀ x, c x ≤ 1 := fun x => max_le zero_le_one (min_le_right _ _)
  have hcc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hmemK : ∀ z ∈ ball z₁ r, ∀ x, z * c x ∈ K := fun z hz x =>
    ⟨⟨z, c x⟩, ⟨ball_subset_closedBall hz, hc0 x, hc1 x⟩, rfl⟩
  set F : ℂ → ℝ → ℂ := fun z x =>
    lightConeBessel (2 * z ^ 2 * (1 - (c x : ℂ) ^ 2)) * A (z * c x) with hF
  have hbound : ∀ x, ∀ z ∈ ball z₁ r, ‖F z x‖ ≤ Real.exp ((‖z₁‖ + r) ^ 2 / 2) * M := by
    intro x z hz
    simp only [hF]
    rw [norm_mul]
    have hcx : |c x| ≤ 1 := by rw [abs_of_nonneg (hc0 x)]; exact hc1 x
    have hzn : ‖z‖ ≤ ‖z₁‖ + r := by
      have := norm_sub_norm_le z z₁
      have h2 : ‖z - z₁‖ < r := by rw [← dist_eq_norm]; exact hz
      linarith
    refine mul_le_mul ((norm_lightConeBessel_light_cone_le z hcx).trans
      (Real.exp_le_exp.mpr (by gcongr))) (hM _ (hmemK z hz x)) (norm_nonneg _) (Real.exp_pos _).le
  have hdiff : ∀ x, DifferentiableOn ℂ (fun z => F z x) (ball z₁ r) := by
    intro x z hz
    simp only [hF]
    exact ((differentiable_lightConeBessel _).comp z (by fun_prop)).mul
      ((hKΩ (hmemK z hz x)).differentiableAt.comp z (differentiableAt_id.mul_const _))
      |>.differentiableWithinAt
  have hmeas : ∀ z ∈ ball z₁ r, AEStronglyMeasurable (F z) (volume.restrict (Ioc 0 1)) := by
    intro z hz
    have hcont : Continuous fun x => A (z * c x) :=
      continuous_iff_continuousAt.mpr fun x =>
        ContinuousAt.comp (f := fun x => z * (c x : ℂ)) (g := A)
          (hKΩ (hmemK z hz x)).continuousAt
          ((continuous_const.mul (continuous_ofReal.comp hcc)).continuousAt)
    exact ((differentiable_lightConeBessel.continuous.comp
      (continuous_const.mul (continuous_const.sub ((continuous_ofReal.comp hcc).pow 2)))).mul
      hcont).aestronglyMeasurable
  have hD := differentiableAt_integral_of_cauchy_dominated (μ := volume.restrict (Ioc 0 1))
    hr0 hmeas hdiff hbound (integrableOn_const (by simp))
  refine hD.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  simp only
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  have : c x = x := by simp only [hc]; rw [min_eq_left hx.2, max_eq_right hx.1.le]
  simp only [hF, this]

theorem differentiableAt_lightConeTransmuteC {A : ℂ → ℂ} {z₁ : ℂ}
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, AnalyticAt ℂ A (z₁ * t)) :
    DifferentiableAt ℂ (lightConeTransmuteC A) z₁ := by
  have h1 : AnalyticAt ℂ A z₁ := by simpa using hA 1 ⟨zero_le_one, le_rfl⟩
  exact h1.differentiableAt.sub ((differentiableAt_id.pow 2).mul (differentiableAt_lightConeTail hA))

end RHTower.CHMDLightCone
