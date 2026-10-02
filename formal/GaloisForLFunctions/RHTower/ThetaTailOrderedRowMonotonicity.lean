import GaloisForLFunctions.RHTower.ThetaTailNormalizedRowCurvature
import GaloisForLFunctions.RHTower.ThetaTailTwoPointPositivity
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Strict decrease of the actual source-normalized tail row beyond its diagonal. -/

noncomputable section

open MeasureTheory Filter Topology Set

namespace RHTower.ThetaTailRow

private def weighted (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => t) f

private theorem weighted_apply (f : SchwartzMap ℝ ℝ) (t : ℝ) :
    weighted f t = t * f t := by
  have hg : (fun t : ℝ => t).HasTemperateGrowth := by fun_prop
  simp only [weighted, SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]

private theorem shifted_integrable (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    Integrable (fun t => f (x + t)) := by
  simpa only [add_comm] using f.integrable.comp_add_right x

private theorem weighted_shift_integrable (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    Integrable (fun t => t * f (x + t)) := by
  have h := (shifted_integrable (weighted f) x).sub
    ((shifted_integrable f x).const_mul x)
  simp only [weighted_apply] at h
  convert h using 1
  ext t
  simp only [Pi.sub_apply]
  ring

private theorem linear_product_integrable (f g : SchwartzMap ℝ ℝ) (x y a b : ℝ) :
    Integrable (fun t => (a + b * t) * f (x + t) * g (y + t)) := by
  have h := ((shifted_integrable f x).const_mul a).add
    ((weighted_shift_integrable f x).const_mul b)
  have hp := h.mul_bdd (g.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => g.norm_le_seminorm ℝ (y + t))
  convert hp using 1
  ext t
  simp only [Pi.add_apply, Function.comp_apply, id_eq]
  ring

private theorem shifted_zero (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    Tendsto (fun t => f (x + t)) atTop (𝓝 0) :=
  (f.tendsto_cocompact.mono_left atTop_le_cocompact).comp
    (tendsto_atTop_add_const_left atTop x tendsto_id)

private theorem weighted_shift_zero (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    Tendsto (fun t => t * f (x + t)) atTop (𝓝 0) := by
  have h := (shifted_zero (weighted f) x).sub ((shifted_zero f x).const_mul x)
  simp only [weighted_apply, mul_zero, sub_zero] at h
  convert h using 1
  ext t
  ring

private theorem source_deriv_eq (z : ℝ) :
    deriv thetaCuspFullSource z = -thetaCuspLogDecaySlope z * thetaCuspFullSource z := by
  have h : iteratedDeriv 1 thetaCuspLogSource z =
      deriv thetaCuspFullSource z / thetaCuspFullSource z := by
    simpa only [iteratedDeriv_one] using (hasDerivAt_thetaCuspLogSource z).deriv
  dsimp only [thetaCuspLogDecaySlope]
  rw [h]
  field_simp [(thetaCuspFullSource_pos_all z).ne']

private def rawDerivative (x y t : ℝ) : ℝ :=
  thetaCuspFullSource (x+t) * thetaCuspFullSource (y+t) +
    (x+y+2*t) * thetaCuspFullSource (x+t) * deriv thetaCuspFullSource (y+t)

private theorem rawDerivative_integrable (x y : ℝ) : Integrable (rawDerivative x y) := by
  have h := (linear_product_integrable thetaCuspSchwartzReal thetaCuspSchwartzReal x y 1 0).add
    (linear_product_integrable thetaCuspSchwartzReal
      (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal) x y (x+y) 2)
  convert! h using 1
  ext t
  simp only [rawDerivative, Pi.add_apply, zero_mul, add_zero, one_mul,
    SchwartzMap.derivCLM_apply]
  rfl

private theorem raw_hasDerivAt (x y t : ℝ) :
    HasDerivAt (fun y => thetaTailCommonTranslationIntegrand x y t)
      (rawDerivative x y t) y := by
  have hk := (thetaCuspSchwartzReal.hasDerivAt (y+t)).comp y ((hasDerivAt_id y).add_const t)
  have hs := ((hasDerivAt_const y x).add (hasDerivAt_id y)).add_const (2*t)
  convert! (hs.mul_const (thetaCuspFullSource (x+t))).mul hk using 1
  simp only [rawDerivative, zero_add, one_mul, mul_one]
  rfl

private theorem kernel_hasDerivAt (x y : ℝ) :
    HasDerivAt (thetaTailFirstMomentKernel x)
      (∫ t in Ioi 0, rawDerivative x y t) y := by
  let f := thetaCuspSchwartzReal
  let g := SchwartzMap.derivCLM ℝ ℝ f
  let c₀ := SchwartzMap.seminorm ℝ 0 0 f
  let c₁ := SchwartzMap.seminorm ℝ 0 0 g
  let A := |x| + |y| + 1
  let B : ℝ → ℝ := fun t => (c₀ + (A + 2*|t|)*c₁)*|f (x+t)|
  have hc₀ : 0 ≤ c₀ := (norm_nonneg (f 0)).trans (f.norm_le_seminorm ℝ 0)
  have hc₁ : 0 ≤ c₁ := (norm_nonneg (g 0)).trans (g.norm_le_seminorm ℝ 0)
  have hi : Integrable B := by
    have h := ((shifted_integrable f x).norm.const_mul c₀).add
      ((((shifted_integrable f x).norm.const_mul A).add
        ((weighted_shift_integrable f x).norm.const_mul 2)).mul_const c₁)
    convert! h using 1
    ext t
    dsimp
    rw [abs_mul]
    ring
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := thetaTailCommonTranslationIntegrand x)
    (F' := rawDerivative x) (bound := B)
    (s := Ioo (y-1) (y+1)) (x₀ := y)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun z =>
      (integrable_thetaTailCommonTranslationIntegrand x z).integrableOn.aestronglyMeasurable)
    (integrable_thetaTailCommonTranslationIntegrand x y).integrableOn
    (rawDerivative_integrable x y).integrableOn.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t z hz => by
      have hz' : |z| ≤ |y|+1 := by
        rw [abs_le]
        constructor <;> linarith [le_abs_self y, neg_abs_le y, hz.1, hz.2]
      have hs : |x+z+2*t| ≤ A+2*|t| := by
        calc
          |x+z+2*t| ≤ |x|+|z|+|2*t| := by
            linarith only [abs_add_le (x+z) (2*t), abs_add_le x z]
          _ ≤ A+2*|t| := by norm_num [abs_mul]; dsimp [A]; linarith
      have hf := f.norm_le_seminorm ℝ (z+t)
      have hg := g.norm_le_seminorm ℝ (z+t)
      change |f (x+t) * f (z+t)+(x+z+2*t) * f (x+t) * g (z+t)| ≤ B t
      calc
        _ ≤ |f (x+t)| * |f (z+t)| + |x+z+2*t| * |f (x+t)| * |g (z+t)| := by
          simpa only [abs_mul] using abs_add_le (f (x+t)*f (z+t))
            ((x+z+2*t)*f (x+t)*g (z+t))
        _ ≤ |f (x+t)| * c₀ + (A+2*|t|) * |f (x+t)| * c₁ := by
          exact add_le_add (mul_le_mul_of_nonneg_left hf (abs_nonneg _))
            (mul_le_mul (mul_le_mul_of_nonneg_right hs (abs_nonneg _)) hg
              (abs_nonneg _) (mul_nonneg (by dsimp [A]; positivity) (abs_nonneg _)))
        _ = B t := by dsimp [B]; ring)
    hi.integrableOn
    (Filter.Eventually.of_forall fun t z _ => raw_hasDerivAt x z t)
  have heq : (fun y => ∫ t in Ioi 0, thetaTailCommonTranslationIntegrand x y t) =
      thetaTailFirstMomentKernel x := by
    funext z
    simpa only [add_zero] using (thetaTailFirstMomentKernel_commonShift_eq_tail 0 x z).symm
  rw [heq] at hd
  exact hd.2

private def boundaryDerivative (x y t : ℝ) : ℝ :=
  thetaCuspFullSource (x+t) * thetaCuspFullSource (y+t) +
    t * deriv thetaCuspFullSource (x+t) * thetaCuspFullSource (y+t) +
    t * thetaCuspFullSource (x+t) * deriv thetaCuspFullSource (y+t)

private theorem boundaryDerivative_integrable (x y : ℝ) :
    Integrable (boundaryDerivative x y) := by
  have h := ((linear_product_integrable thetaCuspSchwartzReal thetaCuspSchwartzReal x y 1 0).add
    (linear_product_integrable (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal)
      thetaCuspSchwartzReal x y 0 1)).add
    (linear_product_integrable thetaCuspSchwartzReal
      (SchwartzMap.derivCLM ℝ ℝ thetaCuspSchwartzReal) x y 0 1)
  convert! h using 1
  ext t
  simp only [boundaryDerivative, Pi.add_apply, zero_mul, add_zero, one_mul, zero_add,
    SchwartzMap.derivCLM_apply]
  rfl

private theorem boundary_integral_zero (x y : ℝ) :
    (∫ t in Ioi 0, boundaryDerivative x y t) = 0 := by
  have hd (t : ℝ) : HasDerivAt
      (fun t => t * thetaCuspFullSource (x+t) * thetaCuspFullSource (y+t))
      (boundaryDerivative x y t) t := by
    have hk (z : ℝ) : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource z) z :=
      thetaCuspSchwartzReal.hasDerivAt z
    have hx := (hk (x+t)).comp t
      ((hasDerivAt_const t x).add (hasDerivAt_id t))
    have hy := (hk (y+t)).comp t
      ((hasDerivAt_const t y).add (hasDerivAt_id t))
    convert! ((hasDerivAt_id t).mul hx).mul hy using 1
    dsimp [boundaryDerivative]
    ring
  have hl := (weighted_shift_zero thetaCuspSchwartzReal x).mul
    (shifted_zero thetaCuspSchwartzReal y)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := 0) (fun t _ => hd t) (boundaryDerivative_integrable x y).integrableOn hl
  simpa using h

private def signedRemainder (x y t : ℝ) : ℝ :=
  rawDerivative x y t + thetaCuspLogDecaySlope y * thetaTailCommonTranslationIntegrand x y t -
    boundaryDerivative x y t

private theorem signedRemainder_integrable (x y : ℝ) : Integrable (signedRemainder x y) :=
  ((rawDerivative_integrable x y).add
    ((integrable_thetaTailCommonTranslationIntegrand x y).const_mul
      (thetaCuspLogDecaySlope y))).sub (boundaryDerivative_integrable x y)

private theorem signedRemainder_eq (x y t : ℝ) :
    signedRemainder x y t = thetaCuspFullSource (x+t) * thetaCuspFullSource (y+t) *
      (t * (thetaCuspLogDecaySlope (x+t) + thetaCuspLogDecaySlope (y+t)) -
        (x+y+2*t) * (thetaCuspLogDecaySlope (y+t) - thetaCuspLogDecaySlope y)) := by
  simp only [signedRemainder, rawDerivative, boundaryDerivative,
    thetaTailCommonTranslationIntegrand, source_deriv_eq]
  ring

private theorem signedRemainder_neg {x y t : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : 0 < y) (ht : 0 < t) : signedRemainder x y t < 0 := by
  have hxt : 0 < x+t := by linarith
  have hyt : 0 < y+t := by linarith
  have hq := ThetaTailTwoPoint.strictMonoOn_decaySlope_div.monotoneOn hxt hyt
    (show x+t ≤ y+t by linarith)
  have hr := ThetaTailTwoPoint.strictMonoOn_decaySlope_div hy hyt
    (show y < y+t by linarith)
  have hq' := (div_le_div_iff₀ hxt hyt).mp hq
  have hr' := (div_lt_div_iff₀ hy hyt).mp hr
  have ha : t * (thetaCuspLogDecaySlope (x+t) * (y+t) -
      thetaCuspLogDecaySlope (y+t) * (x+t)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht.le (sub_nonpos.mpr hq')
  have hb : (x+y+2*t) * (thetaCuspLogDecaySlope y * (y+t) -
      thetaCuspLogDecaySlope (y+t) * y) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (sub_neg.mpr hr')
  have hn : t * (thetaCuspLogDecaySlope (x+t) + thetaCuspLogDecaySlope (y+t)) -
      (x+y+2*t) * (thetaCuspLogDecaySlope (y+t) - thetaCuspLogDecaySlope y) < 0 := by
    have hm : (t * (thetaCuspLogDecaySlope (x+t) + thetaCuspLogDecaySlope (y+t)) -
        (x+y+2*t) * (thetaCuspLogDecaySlope (y+t) - thetaCuspLogDecaySlope y)) * (y+t) < 0 := by
      nlinarith only [ha, hb]
    exact (mul_neg_iff.mp hm).resolve_left (fun h => (not_lt_of_ge hyt.le) h.2) |>.1
  rw [signedRemainder_eq]
  exact mul_neg_of_pos_of_neg
    (mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)) hn

private theorem signed_integral_eq (x y : ℝ) :
    (∫ t in Ioi 0, signedRemainder x y t) =
      (∫ t in Ioi 0, rawDerivative x y t) +
        thetaCuspLogDecaySlope y * thetaTailFirstMomentKernel x y := by
  have heq := thetaTailFirstMomentKernel_commonShift_eq_tail 0 x y
  simp only [add_zero] at heq
  simp only [signedRemainder]
  have ha : IntegrableOn (fun t => rawDerivative x y t +
      thetaCuspLogDecaySlope y * thetaTailCommonTranslationIntegrand x y t) (Ioi 0) :=
    ((rawDerivative_integrable x y).add
      ((integrable_thetaTailCommonTranslationIntegrand x y).const_mul _)).integrableOn
  rw [integral_sub ha
    (boundaryDerivative_integrable x y).integrableOn,
    integral_add (rawDerivative_integrable x y).integrableOn
      ((integrable_thetaTailCommonTranslationIntegrand x y).const_mul _).integrableOn,
    integral_const_mul, boundary_integral_zero, sub_zero, ← heq]

private theorem normalized_hasDerivAt (x y : ℝ) :
    HasDerivAt (normalized x)
      ((∫ t in Ioi 0, signedRemainder x y t) /
        (thetaCuspFullSource x * thetaCuspFullSource y)) y := by
  have hk : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource y) y :=
    thetaCuspSchwartzReal.hasDerivAt y
  have hn := (kernel_hasDerivAt x y).div (hk.const_mul (thetaCuspFullSource x))
    (mul_ne_zero (thetaCuspFullSource_pos_all x).ne' (thetaCuspFullSource_pos_all y).ne')
  convert! hn using 1
  rw [signed_integral_eq, source_deriv_eq]
  field_simp [(thetaCuspFullSource_pos_all x).ne', (thetaCuspFullSource_pos_all y).ne']
  ring

/-- Every actual normalized row has a strictly negative derivative to the right of
its nonnegative diagonal (and at a positive diagonal). -/
theorem deriv_normalized_neg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : 0 < y) :
    deriv (normalized x) y < 0 := by
  have hi : IntegrableOn (fun t => -signedRemainder x y t) (Ioi 0) :=
    (signedRemainder_integrable x y).neg.integrableOn
  have hp (t : ℝ) (ht : t ∈ Ioi 0) : 0 < -signedRemainder x y t :=
    neg_pos.mpr (signedRemainder_neg hx hxy hy ht)
  have hnn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ -signedRemainder x y t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hp t ht).le
  have hs : 0 < (volume.restrict (Ioi 0)) (Function.support (fun t => -signedRemainder x y t)) := by
    have hm : 0 < (volume.restrict (Ioi (0:ℝ))) (Ioi 0) := by
      simp only [Measure.restrict_apply measurableSet_Ioi, inter_self, Real.volume_Ioi,
        ENNReal.zero_lt_top]
    exact lt_of_lt_of_le hm (measure_mono fun t ht => (hp t ht).ne')
  have hn := (integral_pos_iff_support_of_nonneg_ae hnn hi).mpr hs
  rw [integral_neg] at hn
  rw [(normalized_hasDerivAt x y).deriv]
  exact div_neg_of_neg_of_pos (neg_pos.mp hn)
    (mul_pos (thetaCuspFullSource_pos_all x) (thetaCuspFullSource_pos_all y))

/-- The actual theta tail kernel, divided by its endpoint source values,
strictly decreases along each row after its nonnegative diagonal. -/
theorem strictAntiOn_normalized_row {x : ℝ} (hx : 0 ≤ x) :
    StrictAntiOn (normalized x) (Ici x) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici x)
    (fun y _ => (normalized_hasDerivAt x y).continuousAt.continuousWithinAt)
  intro y hy
  rw [interior_Ici] at hy
  exact deriv_normalized_neg hx hy.le (lt_of_le_of_lt hx hy)

end RHTower.ThetaTailRow
