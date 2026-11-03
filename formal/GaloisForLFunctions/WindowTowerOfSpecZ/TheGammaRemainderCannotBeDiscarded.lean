import GaloisForLFunctions.WindowTowerOfSpecZ.TheRetainedGammaLowerFormHasANegativeDirection
import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderPaysAUniformReserve
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampFullWeilSmoothingLimit

/-!
# Support-preserving smoothing of the negative retained form

Mollification followed by a compensating dilation preserves the unit support.
Uniform Lipschitz bounds dominate the logarithmic lag integrand at zero.
The exterior Gamma reserve repairs the same negative retained direction,
giving a smooth test with negative retained form and positive complete form.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.CHMDDoobGraph
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis

private def quinticPolynomial (x : ℝ) := 2*x-12*x^3+16*x^5

private theorem quinticPolynomial_deriv (x : ℝ) : HasDerivAt quinticPolynomial (2-36*x^2+80*x^4) x := by
  have h1 := (hasDerivAt_id x).const_mul 2
  have h2 := (hasDerivAt_pow 3 x).const_mul 12
  have h3 := (hasDerivAt_pow 5 x).const_mul 16
  exact ((h1.sub h2).add h3).congr_deriv (by ring)

private theorem quinticPolynomial_lipschitz : LipschitzOnWith 16 quinticPolynomial (Icc (-(1/2 : ℝ)) (1/2)) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun x _ => (quinticPolynomial_deriv x).differentiableAt) _ (convex_Icc _ _)
  intro x hx
  change ‖deriv quinticPolynomial x‖ ≤ (16 : ℝ)
  rw [(quinticPolynomial_deriv x).deriv, Real.norm_eq_abs]
  have h2 : x^2 ≤ 1/4 := by
    nlinarith only [mul_nonneg (by linarith only [hx.1] : 0 ≤ x+1/2)
      (by linarith only [hx.2] : 0 ≤ 1/2-x)]
  have h4 := pow_le_pow_left₀ (sq_nonneg x) h2 2
  rw [← pow_mul] at h4
  norm_num at h4
  apply abs_le.mpr
  constructor
  · nlinarith only [h2, sq_nonneg (x ^ 2)]
  · linarith only [h4, sq_nonneg x]

private theorem quinticWindow_lipschitz (x y : ℝ) : |quinticWindow x - quinticWindow y| ≤ 16 * |x-y| := by
  have hab : -(1/2 : ℝ) ≤ 1/2 := by norm_num
  let c := Set.projIcc (-(1/2 : ℝ)) (1/2) hab
  have he (z : ℝ) : quinticWindow z = quinticPolynomial (c z) := by
    by_cases hl : z < -(1/2 : ℝ)
    · have hz := quinticWindow_outside (x:=z) (fun h => not_lt_of_ge h.1 hl)
      rw [hz]
      change 0 = quinticPolynomial ((Set.projIcc _ _ hab z : Icc _ _) : ℝ)
      rw [Set.projIcc_of_le_left hab hl.le]
      norm_num [quinticPolynomial]
    · by_cases hr : (1/2 : ℝ) < z
      · have hz := quinticWindow_outside (x:=z) (fun h => not_lt_of_ge h.2 hr)
        rw [hz]
        change 0 = quinticPolynomial ((Set.projIcc _ _ hab z : Icc _ _) : ℝ)
        rw [Set.projIcc_of_right_le hab hr.le]
        norm_num [quinticPolynomial]
      · have hi : z ∈ Icc (-(1/2 : ℝ)) (1/2) := ⟨not_lt.mp hl, not_lt.mp hr⟩
        change quinticWindow z = quinticPolynomial ((Set.projIcc _ _ hab z : Icc _ _) : ℝ)
        rw [Set.projIcc_of_mem hab hi, quinticWindow_inside hi.1 hi.2]
        rfl
  have hc : |(c x : ℝ)-(c y : ℝ)| ≤ |x-y| := by
    have h := (LipschitzWith.projIcc hab).dist_le_mul x y
    change dist (c x : ℝ) (c y : ℝ) ≤ 1 * dist x y at h
    simpa only [Real.dist_eq, one_mul] using h
  rw [he x, he y]
  have h := quinticPolynomial_lipschitz.dist_le_mul (c x) (c x).property (c y) (c y).property
  have hp : |quinticPolynomial (c x)-quinticPolynomial (c y)| ≤ 16 * |(c x : ℝ)-(c y : ℝ)| := by
    norm_num only [Real.dist_eq] at h
    exact h
  exact hp.trans (mul_le_mul_of_nonneg_left hc (by norm_num))

private theorem quinticWindow_abs_le_one (x : ℝ) : |quinticWindow x| ≤ 1 := by
  by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
  · have hsq : x ^ 2 ≤ 1 / 4 := by
      nlinarith only [mul_nonneg (by linarith only [hx.1] : 0 ≤ x + 1 / 2)
        (by linarith only [hx.2] : 0 ≤ 1 / 2 - x)]
    have ha : 0 ≤ 1 - 4 * x ^ 2 := by linarith only [hsq]
    have hb : 0 ≤ 1 - 2 * x ^ 2 := by linarith only [hsq]
    have ha1 : 1 - 4 * x ^ 2 ≤ 1 := by linarith only [sq_nonneg x]
    have hb1 : 1 - 2 * x ^ 2 ≤ 1 := by linarith only [sq_nonneg x]
    have hp : (1 - 4 * x ^ 2) * (1 - 2 * x ^ 2) ≤ 1 := by
      simpa only [one_mul] using mul_le_mul ha1 hb1 hb (by norm_num : (0 : ℝ) ≤ 1)
    have h2 : 2 * |x| ≤ 1 := by linarith only [abs_le.mpr hx]
    have he : |quinticWindow x| =
        (2 * |x|) * ((1 - 4 * x ^ 2) * (1 - 2 * x ^ 2)) := by
      rw [quinticWindow, cubicWindow_inside hx.1 hx.2,
        abs_mul, abs_mul, abs_mul, abs_two, abs_of_nonneg ha, abs_of_nonneg hb]
      ring
    rw [he]
    simpa only [one_mul] using mul_le_mul h2 hp (mul_nonneg ha hb) (by norm_num : (0 : ℝ) ≤ 1)
  · rw [quinticWindow_outside hx, abs_zero]
    norm_num

private def quinticSmoothScale (n : ℕ) : ℝ := 1 + 1 / (2 * ((n : ℝ) + 1))

/-- Smoothing followed by contraction of the enlarged support to the unit window. -/
def unitSmoothQuintic (n : ℕ) (x : ℝ) : ℝ :=
  smooth quinticWindow n (quinticSmoothScale n * x)

private theorem quinticSmoothScale_bounds (n : ℕ) :
    1 ≤ quinticSmoothScale n ∧ quinticSmoothScale n ≤ 3 / 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold quinticSmoothScale
  constructor
  · have h : 0 ≤ 1 / (2 * ((n : ℝ) + 1)) := by positivity
    linarith only [h]
  · have h : 1 / (2 * ((n : ℝ) + 1)) ≤ (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) (by linarith only [hn])
    linarith only [h]

theorem unitSmoothQuintic_contDiff (n : ℕ) : ContDiff ℝ 2 (unitSmoothQuintic n) := by
  have hf2 : MemLp quinticWindow 2 volume :=
    continuous_quinticWindow.memLp_of_hasCompactSupport compact_quinticWindow
  have hs : ContDiff ℝ 2 (smooth quinticWindow n) :=
    (smooth_contDiff hf2 n).of_le (by simp)
  exact hs.comp (contDiff_const.mul contDiff_id)

private theorem quintic_mollifier_even (n : ℕ) (t : ℝ) : CHMDDoobGraph.mollifier n (-t) = CHMDDoobGraph.mollifier n t := by
  unfold CHMDDoobGraph.mollifier
  rw [ContDiffBump.normed_def, ContDiffBump.normed_def, ContDiffBump.neg]

theorem unitSmoothQuintic_odd (n : ℕ) (x : ℝ) :
    unitSmoothQuintic n (-x) = -unitSmoothQuintic n x := by
  change (∫ t, CHMDDoobGraph.mollifier n t * quinticWindow (quinticSmoothScale n * (-x) - t)) =
    -(∫ t, CHMDDoobGraph.mollifier n t * quinticWindow (quinticSmoothScale n * x - t))
  rw [← integral_neg_eq_self (fun t => CHMDDoobGraph.mollifier n t *
    quinticWindow (quinticSmoothScale n * (-x) - t)) volume]
  calc _ = ∫ t, -(CHMDDoobGraph.mollifier n t * quinticWindow (quinticSmoothScale n * x - t)) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun t => by
            change CHMDDoobGraph.mollifier n (-t) *
              quinticWindow (quinticSmoothScale n * (-x) - -t) =
                -(CHMDDoobGraph.mollifier n t * quinticWindow (quinticSmoothScale n * x - t))
            rw [quintic_mollifier_even,
              show quinticSmoothScale n * (-x) - -t = -(quinticSmoothScale n * x - t) by ring,
              quinticWindow_odd, mul_neg]
    _ = _ := integral_neg _

theorem unitSmoothQuintic_outside (n : ℕ) {x : ℝ}
    (hx : x ∉ Icc (-(1 / 2 : ℝ)) (1 / 2)) : unitSmoothQuintic n x = 0 := by
  have hxa : 1 / 2 < |x| := not_le.mp fun h => hx (abs_le.mp h)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : 0 ≤ 1 / (4 * ((n : ℝ) + 1)) := by positivity
  have hscale : quinticSmoothScale n = 1 + 2 * (1 / (4 * ((n : ℝ) + 1))) := by
    unfold quinticSmoothScale
    have hnp : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hnp] <;> ring
  have hfar : 1 / 2 + 1 / (4 * ((n : ℝ) + 1)) < |quinticSmoothScale n * x| := by
    rw [abs_mul, abs_of_nonneg (by linarith only [(quinticSmoothScale_bounds n).1])]
    rw [hscale]
    nlinarith only [hxa, hr, mul_pos (by linarith only [hr] : (0 : ℝ) < 1 +
      2 * (1 / (4 * ((n : ℝ) + 1)))) (sub_pos.mpr hxa)]
  change (∫ t, CHMDDoobGraph.mollifier n t * quinticWindow (quinticSmoothScale n * x - t)) = 0
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun t => by
    change CHMDDoobGraph.mollifier n t * quinticWindow (quinticSmoothScale n * x - t) = 0
    by_cases ht : 1 / (4 * ((n : ℝ) + 1)) ≤ |t|
    · have hm : CHMDDoobGraph.mollifier n t = 0 := by
        apply Function.notMem_support.mp
        change t ∉ Function.support ((WeilOneSided.narrowBump n).normed volume)
        rw [(WeilOneSided.narrowBump n).support_normed_eq, Metric.mem_ball,
          dist_zero_right, Real.norm_eq_abs]
        exact not_lt.mpr ht
      rw [hm, zero_mul]
    · have hz : quinticWindow (quinticSmoothScale n * x - t) = 0 := by
        apply quinticWindow_outside
        intro hi
        have ha := abs_le.mpr hi
        have h := abs_sub_abs_le_abs_sub (quinticSmoothScale n * x) t
        linarith only [ha, h, hfar, not_le.mp ht]
      rw [hz, mul_zero]

theorem unitSmoothQuintic_support (n : ℕ) :
    tsupport (unitSmoothQuintic n) ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hi
  exact hx (unitSmoothQuintic_outside n hi)

theorem unitSmoothQuintic_compact (n : ℕ) : HasCompactSupport (unitSmoothQuintic n) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => unitSmoothQuintic_outside n hx)

theorem unitSmoothQuintic_abs_le_one (n : ℕ) (x : ℝ) : |unitSmoothQuintic n x| ≤ 1 :=
  smooth_bound (by norm_num : (0 : ℝ) ≤ 1) quinticWindow_abs_le_one n _

private theorem smooth_quintic_lipschitz (n : ℕ) (x y : ℝ) :
    |smooth quinticWindow n x - smooth quinticWindow n y| ≤ 16 * |x-y| := by
  have he := difference_smooth (v := quinticWindow) continuous_quinticWindow.measurable
    (by norm_num : (0 : ℝ) ≤ 1) quinticWindow_abs_le_one n (y-x) x
  rw [show x + (y-x) = y by ring] at he
  rw [he]
  exact smooth_bound (by positivity : 0 ≤ 16 * |x-y|)
    (fun z => by simpa only [show z - (z + (y-x)) = x-y by ring]
      using quinticWindow_lipschitz z (z + (y-x))) n x

theorem unitSmoothQuintic_lipschitz (n : ℕ) (x y : ℝ) :
    |unitSmoothQuintic n x - unitSmoothQuintic n y| ≤ 24 * |x-y| := by
  have h := smooth_quintic_lipschitz n (quinticSmoothScale n * x) (quinticSmoothScale n * y)
  have ha := quinticSmoothScale_bounds n
  rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith only [ha.1] : 0 ≤ quinticSmoothScale n)] at h
  have hm := mul_le_mul_of_nonneg_right ha.2 (abs_nonneg (x-y))
  change |smooth quinticWindow n (quinticSmoothScale n * x) -
    smooth quinticWindow n (quinticSmoothScale n * y)| ≤ _
  linarith only [h, hm]

private theorem quinticSmoothScale_tendsto : Tendsto quinticSmoothScale atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hdiv : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hn.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  change Tendsto (fun n : ℕ => 1 + 1 / (2 * ((n : ℝ) + 1))) atTop (𝓝 1)
  simpa only [add_zero] using tendsto_const_nhds.add hdiv

/-- The compensating dilation tends to one, preserving the mollification limit. -/
theorem unitSmoothQuintic_tendsto (x : ℝ) :
    Tendsto (fun n => unitSmoothQuintic n x) atTop (𝓝 (quinticWindow x)) := by
  have hb (n : ℕ) : ‖unitSmoothQuintic n x - smooth quinticWindow n x‖ ≤
      16 * |(quinticSmoothScale n - 1) * x| := by
    have h := smooth_quintic_lipschitz n (quinticSmoothScale n * x) x
    rw [show quinticSmoothScale n * x - x = (quinticSmoothScale n - 1) * x by ring] at h
    exact h
  have hz : Tendsto (fun n => 16 * |(quinticSmoothScale n - 1) * x|) atTop (𝓝 0) := by
    have h := (((quinticSmoothScale_tendsto.sub_const 1).mul_const x).abs).const_mul 16
    simpa only [sub_self, zero_mul, abs_zero, mul_zero] using h
  have hd := squeeze_zero_norm hb hz
  have h := hd.add (smooth_tendsto_of_continuous continuous_quinticWindow x)
  simpa only [sub_add_cancel, zero_add] using h

private theorem unitSmoothQuintic_autocorr_tendsto (t : ℝ) :
    Tendsto (fun n => autocorr (unitSmoothQuintic n) t) atTop
      (𝓝 (autocorr quinticWindow t)) := by
  have hb : Integrable (fun x : ℝ =>
      (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1 : ℝ)) x) :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  change Tendsto (fun n => ∫ x, unitSmoothQuintic n x * unitSmoothQuintic n (x+t)) atTop
    (𝓝 (∫ x, quinticWindow x * quinticWindow (x+t)))
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hb (fun n => ?_) ?_
  · exact ((unitSmoothQuintic_contDiff n).continuous.mul
      ((unitSmoothQuintic_contDiff n).continuous.comp (continuous_add_const t))).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
      · rw [indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        simpa only [one_mul] using mul_le_mul (unitSmoothQuintic_abs_le_one n x)
          (unitSmoothQuintic_abs_le_one n (x+t)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      · rw [indicator_of_notMem hx, unitSmoothQuintic_outside n hx, zero_mul, norm_zero]
  · exact Eventually.of_forall fun x =>
      (unitSmoothQuintic_tendsto x).mul (unitSmoothQuintic_tendsto (x+t))

private theorem unitSmoothQuintic_mass_tendsto :
    Tendsto (fun n => ∫ x, unitSmoothQuintic n x ^ 2) atTop
      (𝓝 (∫ x, quinticWindow x ^ 2)) := by
  simpa only [autocorr, add_zero, pow_two] using unitSmoothQuintic_autocorr_tendsto 0

/-- Uniform quadratic control of the lag deficit pays its logarithmic singularity. -/
private theorem unitSmoothQuintic_deficit_bound (n : ℕ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ (∫ x, unitSmoothQuintic n x ^ 2) - autocorr (unitSmoothQuintic n) t ∧
      (∫ x, unitSmoothQuintic n x ^ 2) - autocorr (unitSmoothQuintic n) t ≤ 576 * t ^ 2 := by
  let B : ℝ → ℝ := (Icc (-(3/2 : ℝ)) (1/2)).indicator (fun _ => 576 * t ^ 2)
  have hBi : Integrable B :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hB (x : ℝ) : ‖(unitSmoothQuintic n x - unitSmoothQuintic n (x+t)) ^ 2‖ ≤ B x := by
    dsimp only [B]
    by_cases hx : x ∈ Icc (-(3/2 : ℝ)) (1/2)
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := unitSmoothQuintic_lipschitz n x (x+t)
      rw [show x-(x+t) = -t by ring, abs_neg, abs_of_pos ht.1] at h
      have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs, mul_pow] at hs
      norm_num at hs
      exact hs
    · have hz : unitSmoothQuintic n x = 0 ∧ unitSmoothQuintic n (x+t) = 0 := by
        by_cases hl : x < -(3/2 : ℝ)
        · constructor
          · apply unitSmoothQuintic_outside n
            intro hi
            linarith only [hl, hi.1]
          · apply unitSmoothQuintic_outside n
            intro hi
            linarith only [hl, hi.1, ht.2]
        · have hr : (1/2 : ℝ) < x := not_le.mp (fun h => hx ⟨not_lt.mp hl, h⟩)
          constructor
          · apply unitSmoothQuintic_outside n
            intro hi
            linarith only [hr, hi.2]
          · apply unitSmoothQuintic_outside n
            intro hi
            linarith only [hr, hi.2, ht.1]
      rw [indicator_of_notMem hx, hz.1, hz.2, sub_self]
      norm_num
  have hBv : (∫ x, B x) = 1152 * t ^ 2 := by
    dsimp only [B]
    rw [integral_indicator measurableSet_Icc, setIntegral_const]
    norm_num <;> ring
  have hnn : 0 ≤ ∫ x, (unitSmoothQuintic n x - unitSmoothQuintic n (x+t)) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hb := norm_integral_le_of_norm_le hBi (Eventually.of_forall hB)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, hBv] at hb
  have he := integral_sub_shift_sq (unitSmoothQuintic_compact n)
    (unitSmoothQuintic_contDiff n).continuous t
  have hzero : autocorr (unitSmoothQuintic n) 0 = ∫ x, unitSmoothQuintic n x ^ 2 := by
    simp only [autocorr, add_zero, pow_two]
  rw [hzero] at he
  constructor <;> linarith only [he, hnn, hb]

private theorem unitSmoothQuintic_logarithmic_tendsto :
    Tendsto (fun n => ∫ t in Ioc (0 : ℝ) 1,
      ((∫ x, unitSmoothQuintic n x ^ 2) - autocorr (unitSmoothQuintic n) t) / t) atTop
      (𝓝 (∫ t in Ioc (0 : ℝ) 1,
        ((∫ x, quinticWindow x ^ 2) - autocorr quinticWindow t) / t)) := by
  have hb : IntegrableOn (fun t : ℝ => 576 * t) (Ioc (0 : ℝ) 1) :=
    (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hb (fun n => ?_) ?_
  · have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr
      (unitSmoothQuintic_contDiff n) (unitSmoothQuintic_compact n)
    exact ((continuous_const.sub hc).measurable.div measurable_id).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    obtain ⟨h0, h1⟩ := unitSmoothQuintic_deficit_bound n ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 ht.1.le)]
    apply (div_le_iff₀ ht.1).mpr
    nlinarith only [h1]
  · exact Eventually.of_forall fun t =>
      (unitSmoothQuintic_mass_tendsto.sub (unitSmoothQuintic_autocorr_tendsto t)).div_const t

private theorem unitSmoothQuintic_first_moment_tendsto :
    Tendsto (fun n => ∫ t in Ioc (0 : ℝ) 1,
      t * ((∫ x, unitSmoothQuintic n x ^ 2) - autocorr (unitSmoothQuintic n) t)) atTop
      (𝓝 (∫ t in Ioc (0 : ℝ) 1,
        t * ((∫ x, quinticWindow x ^ 2) - autocorr quinticWindow t))) := by
  have hb : IntegrableOn (fun _ : ℝ => (576 : ℝ)) (Ioc (0 : ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hb (fun n => ?_) ?_
  · have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr
      (unitSmoothQuintic_contDiff n) (unitSmoothQuintic_compact n)
    exact (continuous_id.mul (continuous_const.sub hc)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    obtain ⟨h0, h1⟩ := unitSmoothQuintic_deficit_bound n ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.1.le h0)]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.1, ht.2]
    have hd : (∫ x, unitSmoothQuintic n x ^ 2) - autocorr (unitSmoothQuintic n) t ≤ 576 := by
      nlinarith only [h1, ht2]
    simpa only [one_mul] using mul_le_mul ht.2 hd h0 (by norm_num : (0 : ℝ) ≤ 1)
  · exact Eventually.of_forall fun t =>
      (unitSmoothQuintic_mass_tendsto.sub (unitSmoothQuintic_autocorr_tendsto t)).const_mul t

private theorem unitSmoothQuintic_weight_tendsto (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun n => ∫ x, unitSmoothQuintic n x * g x) atTop
      (𝓝 (∫ x, quinticWindow x * g x)) := by
  have hb : Integrable (fun x : ℝ =>
      (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun x => |g x|) x) :=
    hg.abs.integrableOn_Icc.integrable_indicator measurableSet_Icc
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hb (fun n => ?_) ?_
  · exact ((unitSmoothQuintic_contDiff n).continuous.mul hg).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
      · rw [indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (unitSmoothQuintic_abs_le_one n x) (abs_nonneg (g x))
      · rw [indicator_of_notMem hx, unitSmoothQuintic_outside n hx, zero_mul, norm_zero]
  · exact Eventually.of_forall fun x => (unitSmoothQuintic_tendsto x).mul_const (g x)

/-- Every term of the retained lower form survives support-preserving smoothing. -/
theorem retainedOddGammaLowerForm_unitSmoothQuintic_tendsto :
    Tendsto (fun n => retainedOddGammaLowerForm (unitSmoothQuintic n)) atTop
      (𝓝 (retainedOddGammaLowerForm quinticWindow)) := by
  have hm : Tendsto (fun n => ∫ x, x * unitSmoothQuintic n x) atTop
      (𝓝 (∫ x, x * quinticWindow x)) := by
    simpa only [mul_comm] using unitSmoothQuintic_weight_tendsto (fun x => x) continuous_id
  have hp : Tendsto (fun n => sinhPairing (unitSmoothQuintic n)) atTop
      (𝓝 (sinhPairing quinticWindow)) :=
    unitSmoothQuintic_weight_tendsto (fun x => 2 * Real.sinh (x/2)) (by fun_prop)
  have harch := unitSmoothQuintic_logarithmic_tendsto.sub
    (unitSmoothQuintic_mass_tendsto.const_mul
      (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2))
  have hfirst := harch.sub (unitSmoothQuintic_first_moment_tendsto.div_const 24)
  have hposition := hfirst.sub ((hm.pow 2).div_const 16)
  have hpole := hposition.sub ((hp.pow 2).div_const 2)
  exact hpole.sub
    ((unitSmoothQuintic_autocorr_tendsto (Real.log 2)).const_mul (2 * (Real.log 2 / Real.sqrt 2)))

/-- Discarding the nonnegative Gamma remainder fails even on smooth odd unit-window tests. -/
theorem exists_odd_unit_retainedGamma_neg :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Icc (-(1/2 : ℝ)) (1/2) ∧
      (∀ x, F (-x) = -F x) ∧ retainedOddGammaLowerForm F < 0 := by
  obtain ⟨n, hn⟩ := (retainedOddGammaLowerForm_unitSmoothQuintic_tendsto.eventually
    (Iio_mem_nhds retainedOddGammaLowerForm_quintic_neg)).exists
  exact ⟨unitSmoothQuintic n, unitSmoothQuintic_contDiff n, unitSmoothQuintic_support n,
    unitSmoothQuintic_odd n, hn⟩

/-- The discarded Gamma remainder repairs a negative retained direction on the same C² test. -/
theorem exists_odd_unit_retainedGamma_neg_weil_pos :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Icc (-(1/2 : ℝ)) (1/2) ∧
      (∀ x, F (-x) = -F x) ∧ retainedOddGammaLowerForm F < 0 ∧ 0 < weilQuad F := by
  have hneg := retainedOddGammaLowerForm_unitSmoothQuintic_tendsto.eventually
    (Iio_mem_nhds retainedOddGammaLowerForm_quintic_neg)
  have hpos :=
    (retainedOddGammaLowerForm_unitSmoothQuintic_tendsto.add
      (unitSmoothQuintic_mass_tendsto.div_const 64)).eventually
      (Ioi_mem_nhds retainedOddGammaLowerForm_quintic_add_reserve_pos)
  obtain ⟨n, hn, hp⟩ := (hneg.and hpos).exists
  exact ⟨unitSmoothQuintic n, unitSmoothQuintic_contDiff n, unitSmoothQuintic_support n,
    unitSmoothQuintic_odd n, hn, hp.trans_le
      (weilQuad_ge_retainedOddGamma_add_reserve (unitSmoothQuintic_contDiff n)
        (unitSmoothQuintic_support n) (unitSmoothQuintic_odd n))⟩

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unitSmoothQuintic_support
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.unitSmoothQuintic_tendsto

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.exists_odd_unit_retainedGamma_neg
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.exists_odd_unit_retainedGamma_neg_weil_pos
