import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional

/-!
# Polar enforcement by a distant translated copy

Subtracting an exponentially attenuated translate cancels an exponential moment exactly.
When the original autocorrelation is compactly supported, the normalized correlation is
unchanged on any prescribed bounded interval once the translate is sufficiently distant.
The normalized archimedean energy changes by at most an explicit constant times `exp (-T)`.
Consequently polar and nonpolar finite logarithmic-grid classes have exactly the same lower
bounds, at every differentiability order at least two, including smooth sources.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- A source with one attenuated translated copy subtracted. -/
def subtractCopy (f : ℝ → ℝ) (a T u : ℝ) : ℝ := f u - a * f (u - T)

/-- The attenuation that cancels the positive half-exponential source moment. -/
def polarCopy (f : ℝ → ℝ) (T : ℝ) : ℝ → ℝ := subtractCopy f (Real.exp (-T / 2)) T

theorem continuous_subtractCopy {f : ℝ → ℝ} (hf : Continuous f) (a T : ℝ) :
    Continuous (subtractCopy f a T) :=
  hf.sub (continuous_const.mul (hf.comp (continuous_id.sub continuous_const)))

theorem contDiff_subtractCopy {f : ℝ → ℝ} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (a T : ℝ) :
    ContDiff ℝ n (subtractCopy f a T) :=
  hf.sub (contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const)))

theorem hasCompactSupport_subtractCopy {f : ℝ → ℝ} (hf : HasCompactSupport f) (a T : ℝ) :
    HasCompactSupport (subtractCopy f a T) :=
  hf.sub ((hf.comp_homeomorph (Homeomorph.subRight T)).mul_left)

/-- Literal four-term autocorrelation expansion of the translated-copy operation. -/
theorem autocorr_subtractCopy {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (a T x : ℝ) :
    autocorr (subtractCopy f a T) x =
      (1 + a ^ 2) * autocorr f x - a * (autocorr f (x - T) + autocorr f (x + T)) := by
  have hi := integrable_shift_mul_shift hf hfc
  have hi12 : Integrable (fun u => f (u + 0) * f (u + x) -
      a * (f (u + 0) * f (u + (x - T)))) :=
    (hi 0 x).sub ((hi 0 (x - T)).const_mul a)
  have hi123 : Integrable (fun u => (f (u + 0) * f (u + x) -
      a * (f (u + 0) * f (u + (x - T)))) - a * (f (u + -T) * f (u + x))) :=
    hi12.sub ((hi (-T) x).const_mul a)
  calc
    autocorr (subtractCopy f a T) x =
        ∫ u, ((f (u + 0) * f (u + x) - a * (f (u + 0) * f (u + (x - T)))) -
          a * (f (u + -T) * f (u + x))) + a ^ 2 * (f (u + -T) * f (u + (x - T))) := by
      unfold autocorr subtractCopy
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [add_zero, sub_eq_add_neg, add_assoc]
      ring
    _ = (1 + a ^ 2) * autocorr f x - a * (autocorr f (x - T) + autocorr f (x + T)) := by
      rw [integral_add hi123 ((hi (-T) (x - T)).const_mul (a ^ 2)),
        integral_sub hi12 ((hi (-T) x).const_mul a),
        integral_sub (hi 0 x) ((hi 0 (x - T)).const_mul a)]
      simp only [integral_const_mul, integral_shift_mul_shift, sub_zero, sub_neg_eq_add]
      rw [show x - T + T = x by ring]
      ring

/-- Exponential moments transform by the translation character. -/
theorem integral_shift_mul_exp (f : ℝ → ℝ) (s T : ℝ) :
    (∫ u, f (u - T) * Real.exp (s * u)) = Real.exp (s * T) * ∫ u, f u * Real.exp (s * u) := by
  rw [← integral_add_right_eq_self (fun u => f (u - T) * Real.exp (s * u)) T]
  simp_rw [add_sub_cancel_right, mul_add, Real.exp_add]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  ring

/-- Exact source moment multiplier; no moment vanishing is assumed. -/
theorem integral_subtractCopy_mul_exp {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (a T s : ℝ) :
    (∫ u, subtractCopy f a T u * Real.exp (s * u)) =
      (1 - a * Real.exp (s * T)) * ∫ u, f u * Real.exp (s * u) := by
  have hi : Integrable (fun u => f u * Real.exp (s * u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hit : Integrable (fun u => f (u - T) * Real.exp (s * u)) :=
    ((hf.comp (continuous_id.sub continuous_const)).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hfc.comp_homeomorph (Homeomorph.subRight T)).mul_right
  simp only [subtractCopy, sub_mul, mul_assoc]
  rw [integral_sub hi (hit.const_mul a), integral_const_mul, integral_shift_mul_exp]
  ring

/-- The constructed source has vanishing positive exponential moment for every translation. -/
theorem integral_polarCopy_exp_half {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (T : ℝ) :
    (∫ u, polarCopy f T u * Real.exp (u / 2)) = 0 := by
  have h := integral_subtractCopy_mul_exp hf hfc (Real.exp (-T / 2)) T (1 / 2)
  have hexp : Real.exp (-T / 2) * Real.exp (1 / 2 * T) = 1 := by
    rw [← Real.exp_add, show -T / 2 + 1 / 2 * T = 0 by ring, Real.exp_zero]
  rw [hexp, sub_self, zero_mul] at h
  simpa only [polarCopy, one_div, div_eq_mul_inv, one_mul, mul_comm] using h

/-- Polar neutrality is produced by the source operation, rather than postulated. -/
theorem integral_polarCopy_autocorr_cosh {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (T : ℝ) :
    (∫ x in Ioi 0, autocorr (polarCopy f T) x * Real.cosh (x / 2)) = 0 := by
  have hwhole := integral_autocorr_mul_cosh
    (contDiff_subtractCopy hf (Real.exp (-T / 2)) T)
    (hasCompactSupport_subtractCopy hfc (Real.exp (-T / 2)) T)
  change (∫ x, autocorr (polarCopy f T) x * Real.cosh (x / 2)) =
    (∫ u, polarCopy f T u * Real.exp (u / 2)) *
      ∫ u, polarCopy f T u * Real.exp (-u / 2) at hwhole
  rw [integral_polarCopy_exp_half hf.continuous hfc T, zero_mul] at hwhole
  have heven := integral_comp_abs (f := fun x => autocorr (polarCopy f T) x * Real.cosh (x / 2))
  have hid : (fun x : ℝ => autocorr (polarCopy f T) |x| * Real.cosh (|x| / 2)) =
      fun x => autocorr (polarCopy f T) x * Real.cosh (x / 2) := by
    funext x
    rcases abs_choice x with hx | hx
    · rw [hx]
    · rw [hx, autocorr_neg, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
  rw [hid, hwhole] at heven
  linarith

/-- Compact correlation support makes the copy operation exactly scalar on a bounded window. -/
theorem autocorr_subtractCopy_local {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {D A T : ℝ}
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + A < T)
    {x : ℝ} (hx : |x| ≤ A) (a : ℝ) :
    autocorr (subtractCopy f a T) x = (1 + a ^ 2) * autocorr f x := by
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  have hleft : D < |x - T| := lt_of_lt_of_le (by linarith : D < -(x - T)) (neg_le_abs _)
  have hright : D < |x + T| := lt_of_lt_of_le (by linarith : D < x + T) (le_abs_self _)
  rw [autocorr_subtractCopy hf hfc, hsupp _ hleft, hsupp _ hright]
  ring

/-- Exact preservation of normalized local data; hence any finite set of zero samples survives. -/
theorem normalized_autocorr_subtractCopy_local {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {D A T : ℝ} (hA : 0 ≤ A)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + A < T)
    {x : ℝ} (hx : |x| ≤ A) (a : ℝ) :
    autocorr (subtractCopy f a T) x / autocorr (subtractCopy f a T) 0 =
      autocorr f x / autocorr f 0 := by
  rw [autocorr_subtractCopy_local hf hfc hsupp hT hx,
    autocorr_subtractCopy_local hf hfc hsupp hT (by simpa using hA : |(0 : ℝ)| ≤ A)]
  have ha : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
  exact mul_div_mul_left _ _ ha

/-- Compact source support supplies an actual positive autocorrelation support radius. -/
theorem exists_pos_autocorr_support_radius {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    ∃ D : ℝ, 0 < D ∧ ∀ x, D < |x| → autocorr f x = 0 := by
  have hc : IsCompact (tsupport (autocorr f)) := hasCompactSupport_autocorr hfc
  obtain ⟨r, hr⟩ := hc.isBounded.subset_closedBall 0
  refine ⟨max r 0 + 1, by positivity, ?_⟩
  intro x hx
  by_contra hne
  have hmem : x ∈ tsupport (autocorr f) := subset_closure (Function.mem_support.mpr hne)
  have hbound := hr hmem
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hbound
  have := le_max_left r 0
  linarith

/-- Every nonzero smooth compact source has a polar source with identical normalized data on
any given bounded interval. The support radius is derived from compactness. -/
theorem exists_polar_source_same_local_data {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) (A : ℝ) (hA : 0 ≤ A) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ 0 < autocorr g 0 ∧
      (∫ x in Ioi 0, autocorr g x * Real.cosh (x / 2)) = 0 ∧
      ∀ x, |x| ≤ A → autocorr g x / autocorr g 0 = autocorr f x / autocorr f 0 := by
  obtain ⟨D, _, hsupp⟩ := exists_pos_autocorr_support_radius hfc
  let T := D + A + 1
  have hT : D + A < T := by dsimp [T]; linarith
  refine ⟨polarCopy f T, contDiff_subtractCopy hf _ _, hasCompactSupport_subtractCopy hfc _ _,
    ?_, integral_polarCopy_autocorr_cosh hf hfc T, ?_⟩
  · change 0 < autocorr (subtractCopy f (Real.exp (-T / 2)) T) 0
    rw [autocorr_subtractCopy_local hf.continuous hfc hsupp hT (by simpa using hA : |(0 : ℝ)| ≤ A)]
    positivity
  · intro x hx
    exact normalized_autocorr_subtractCopy_local hf.continuous hfc hA hsupp hT hx _

/-! ## Quantitative archimedean energy control -/

/-- A uniform exponential envelope for the archimedean weight past distance one. -/
theorem archLevySinhWeight_le_exp_tail {x : ℝ} (hx : 1 ≤ x) :
    archLevySinhWeight x ≤ 2 * Real.exp (-x / 2) / (1 - Real.exp (-2)) := by
  have hd : 0 < 1 - Real.exp (-2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have he : Real.exp (-2 * x) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
  have hb := div_le_div_of_nonneg_left (Real.exp_pos (-x / 2)).le hd
    (show 1 - Real.exp (-2) ≤ 1 - Real.exp (-2 * x) by linarith)
  unfold archLevySinhWeight
  rw [exp_half_div_sinh_eq (by linarith : 0 < x)]
  unfold RHTower.archLevyDensity
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ 2)

/-- The weight envelope on a correlation packet translated beyond its support radius. -/
def copyTailFactor (D T : ℝ) : ℝ :=
  2 * Real.exp (-(T - D) / 2) / (1 - Real.exp (-2))

theorem copyTailFactor_nonneg (D T : ℝ) : 0 ≤ copyTailFactor D T := by
  have hd : 0 < 1 - Real.exp (-2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  unfold copyTailFactor
  positivity

theorem abs_shifted_autocorr_mul_arch_le {f : ℝ → ℝ} {D T : ℝ}
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T)
    {x : ℝ} (hx : 0 < x) :
    |autocorr f (x - T) * archLevySinhWeight x| ≤
      copyTailFactor D T * |autocorr f (x - T)| := by
  by_cases hz : autocorr f (x - T) = 0
  · simp [hz]
  have hs : |x - T| ≤ D := le_of_not_gt (fun h => hz (hsupp _ h))
  have hdist := (abs_le.mp hs).1
  have hx1 : 1 ≤ x := by linarith
  have hw := archLevySinhWeight_le_exp_tail hx1
  have he : Real.exp (-x / 2) ≤ Real.exp (-(T - D) / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hd : 0 ≤ 1 - Real.exp (-2) :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).le
  have hew := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2)) hd
  have hweight : archLevySinhWeight x ≤ copyTailFactor D T := hw.trans hew
  rw [abs_mul, abs_of_nonneg (archLevySinhWeight_pos hx).le]
  exact (mul_le_mul_of_nonneg_left hweight (abs_nonneg _)).trans_eq (mul_comm _ _)

theorem integrable_abs_shifted_autocorr {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (T : ℝ) :
    Integrable (fun x => |autocorr f (x - T)|) := by
  have hi : Integrable (fun x => autocorr f (x - T)) :=
    ((continuous_autocorr hf hfc).comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      ((hasCompactSupport_autocorr hfc).comp_homeomorph (Homeomorph.subRight T))
  simpa only [Real.norm_eq_abs] using hi.norm

theorem integrableOn_shifted_autocorr_arch {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {D T : ℝ}
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) :
    IntegrableOn (fun x => autocorr f (x - T) * archLevySinhWeight x) (Ioi 0) := by
  have hi : IntegrableOn (fun x => copyTailFactor D T * |autocorr f (x - T)|) (Ioi 0) :=
    ((integrable_abs_shifted_autocorr hf hfc T).const_mul (copyTailFactor D T)).integrableOn
  have hm : Measurable (fun x => autocorr f (x - T) * archLevySinhWeight x) := by
    have hc := continuous_autocorr hf hfc
    unfold archLevySinhWeight
    exact (hc.measurable.comp (measurable_id.sub measurable_const)).mul
      ((Real.continuous_exp.comp (continuous_id.div_const 2)).measurable.div Real.continuous_sinh.measurable)
  refine hi.mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [Real.norm_eq_abs] using abs_shifted_autocorr_mul_arch_le hsupp hT hx

/-- The translated correlation packet has exponentially small archimedean pairing. -/
theorem abs_integral_shifted_autocorr_arch_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {D T : ℝ}
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) :
    |∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x| ≤
      copyTailFactor D T * ∫ x, |autocorr f x| := by
  have hi := integrableOn_shifted_autocorr_arch hf hfc hsupp hT
  have hj := integrable_abs_shifted_autocorr hf hfc T
  have hshift : (∫ x, |autocorr f (x - T)|) = ∫ x, |autocorr f x| := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self (fun x => |autocorr f x|) (-T)
  calc
    _ ≤ ∫ x in Ioi 0, |autocorr f (x - T) * archLevySinhWeight x| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Ioi 0)) (fun x => autocorr f (x - T) * archLevySinhWeight x)
    _ ≤ ∫ x in Ioi 0, copyTailFactor D T * |autocorr f (x - T)| := by
      apply integral_mono_ae (by simpa only [Real.norm_eq_abs] using hi.norm)
        ((hj.const_mul _).integrableOn)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact abs_shifted_autocorr_mul_arch_le hsupp hT hx
    _ = copyTailFactor D T * ∫ x in Ioi 0, |autocorr f (x - T)| := integral_const_mul _ _
    _ ≤ copyTailFactor D T * ∫ x, |autocorr f (x - T)| :=
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hj (Eventually.of_forall fun x => abs_nonneg _))
        (copyTailFactor_nonneg D T)
    _ = _ := by rw [hshift]

/-- Exact energy change of any sufficiently separated translated-copy subtraction. -/
theorem biScaleLevyEnergy_subtractCopy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {D T : ℝ}
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) (a : ℝ) :
    biScaleLevyEnergy (subtractCopy f a T) = (1 + a ^ 2) * biScaleLevyEnergy f +
      a * ∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x := by
  have hm : autocorr (subtractCopy f a T) 0 = (1 + a ^ 2) * autocorr f 0 :=
    autocorr_subtractCopy_local hf.continuous hfc (A := 0) hsupp (by linarith) (by simp) a
  have hfi := integrableOn_biScaleLevyIntegrand hf hfc
  have hti := integrableOn_shifted_autocorr_arch hf hfc hsupp hT
  unfold biScaleLevyEnergy
  calc
    _ = ∫ x in Ioi 0, (1 + a ^ 2) * ((autocorr f 0 - autocorr f x) * archLevySinhWeight x) +
        a * (autocorr f (x - T) * archLevySinhWeight x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      have hp : autocorr f (x + T) = 0 := hsupp _
        (lt_of_lt_of_le (by linarith : D < x + T) (le_abs_self _))
      rw [hm, autocorr_subtractCopy hf.continuous hfc, hp]
      ring
    _ = _ := by rw [integral_add (hfi.const_mul _) (hti.const_mul _), integral_const_mul, integral_const_mul]

/-- The normalized archimedean energy of a real source. -/
def normalizedArchEnergy (f : ℝ → ℝ) : ℝ := biScaleLevyEnergy f / autocorr f 0

theorem normalizedArchEnergy_subtractCopy_sub {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {D T : ℝ}
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) (a : ℝ) :
    normalizedArchEnergy (subtractCopy f a T) - normalizedArchEnergy f =
      a / ((1 + a ^ 2) * autocorr f 0) *
        ∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x := by
  have hm : autocorr (subtractCopy f a T) 0 = (1 + a ^ 2) * autocorr f 0 :=
    autocorr_subtractCopy_local hf.continuous hfc (A := 0) hsupp (by linarith) (by simp) a
  have ha : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
  rw [normalizedArchEnergy, normalizedArchEnergy, biScaleLevyEnergy_subtractCopy hf hfc hsupp hT, hm]
  field_simp
  ring

/-- Explicit error constant for polar enforcement at correlation support radius `D`. -/
def polarEnergyErrorConstant (f : ℝ → ℝ) (D : ℝ) : ℝ :=
  2 * Real.exp (D / 2) * (∫ x, |autocorr f x|) /
    (autocorr f 0 * (1 - Real.exp (-2)))

/-- Polar enforcement has exponentially vanishing normalized archimedean energy cost. -/
theorem normalizedArchEnergy_polarCopy_error {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {D T : ℝ}
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) :
    |normalizedArchEnergy (polarCopy f T) - normalizedArchEnergy f| ≤
      polarEnergyErrorConstant f D * Real.exp (-T) := by
  let a := Real.exp (-T / 2)
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have hM : 0 ≤ ∫ x, |autocorr f x| := integral_nonneg (fun _ => abs_nonneg _)
  have hcoeff : 0 ≤ a / ((1 + a ^ 2) * autocorr f 0) := by positivity
  have hratio : a / ((1 + a ^ 2) * autocorr f 0) ≤ a / autocorr f 0 :=
    div_le_div_of_nonneg_left ha hR (by nlinarith [sq_nonneg a])
  change |normalizedArchEnergy (subtractCopy f a T) - normalizedArchEnergy f| ≤ _
  rw [normalizedArchEnergy_subtractCopy_sub hf hfc hR hsupp hT, abs_mul, abs_of_nonneg hcoeff]
  calc
    _ ≤ a / ((1 + a ^ 2) * autocorr f 0) *
        (copyTailFactor D T * ∫ x, |autocorr f x|) :=
      mul_le_mul_of_nonneg_left (abs_integral_shifted_autocorr_arch_le hf hfc hsupp hT) hcoeff
    _ ≤ a / autocorr f 0 * (copyTailFactor D T * ∫ x, |autocorr f x|) :=
      mul_le_mul_of_nonneg_right hratio (mul_nonneg (copyTailFactor_nonneg D T) hM)
    _ = polarEnergyErrorConstant f D * Real.exp (-T) := by
      have he : a * Real.exp (-(T - D) / 2) = Real.exp (D / 2) * Real.exp (-T) := by
        dsimp [a]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      unfold copyTailFactor polarEnergyErrorConstant
      calc
        _ = 2 * (a * Real.exp (-(T - D) / 2)) * (∫ x, |autocorr f x|) /
            (autocorr f 0 * (1 - Real.exp (-2))) := by
              have hd : 0 < 1 - Real.exp (-2) :=
                sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
              field_simp [hR.ne', hd.ne']
        _ = _ := by rw [he]; ring

/-- Arbitrarily accurate polar enforcement preserves every normalized correlation value in
the requested bounded window. All analytic obligations follow from the source regularity. -/
theorem exists_polar_source_local_energy_close {f : ℝ → ℝ} {r : WithTop ℕ∞}
    (hr : 2 ≤ r) (hf : ContDiff ℝ r f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) (A : ℝ) (hA : 0 ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ r g ∧ HasCompactSupport g ∧ 0 < autocorr g 0 ∧
      (∫ x in Ioi 0, autocorr g x * Real.cosh (x / 2)) = 0 ∧
      (∀ x, |x| ≤ A → autocorr g x / autocorr g 0 = autocorr f x / autocorr f 0) ∧
      |normalizedArchEnergy g - normalizedArchEnergy f| < ε := by
  obtain ⟨D, _, hsupp⟩ := exists_pos_autocorr_support_radius hfc
  have hf2 : ContDiff ℝ 2 f := hf.of_le hr
  have htend : Tendsto (fun T : ℝ => polarEnergyErrorConstant f D * Real.exp (-T)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (polarEnergyErrorConstant f D)
  have hevent := (tendsto_order.mp htend).2 ε hε
  obtain ⟨T, hlarge, hsmall⟩ := ((eventually_gt_atTop (D + max A 1)).and hevent).exists
  have hTA : D + A < T := lt_of_le_of_lt (by linarith [le_max_left A 1]) hlarge
  have hT1 : D + 1 ≤ T := le_of_lt (lt_of_le_of_lt (by linarith [le_max_right A 1]) hlarge)
  refine ⟨polarCopy f T, contDiff_subtractCopy hf _ _, hasCompactSupport_subtractCopy hfc _ _,
    ?_, integral_polarCopy_autocorr_cosh hf2 hfc T, ?_, ?_⟩
  · change 0 < autocorr (subtractCopy f (Real.exp (-T / 2)) T) 0
    rw [autocorr_subtractCopy_local hf.continuous hfc hsupp hTA (by simpa using hA : |(0 : ℝ)| ≤ A)]
    positivity
  · intro x hx
    exact normalized_autocorr_subtractCopy_local hf.continuous hfc hA hsupp hTA hx _
  · exact (normalizedArchEnergy_polarCopy_error hf2 hfc hR hsupp hT1).trans_lt hsmall

/-- A normalized lower bound on the polar logarithmic-grid class holds exactly when it holds
on the entire logarithmic-grid class. In particular the two classes have the same best constant. -/
theorem polar_log_grid_lower_bound_iff (r : WithTop ℕ∞) (hr : 2 ≤ r) (N : ℕ) (C : ℝ) :
    (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → 0 < autocorr f 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) →
      (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) = 0 → C ≤ normalizedArchEnergy f) ↔
    (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → 0 < autocorr f 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) → C ≤ normalizedArchEnergy f) := by
  constructor
  · intro hpolar f hf hfc hR hgrid
    by_contra hbad
    have hgap : 0 < (C - normalizedArchEnergy f) / 2 := by linarith
    let A := max (Real.log (N : ℝ)) 0
    obtain ⟨g, hg, hgc, hRg, hpg, hlocal, herr⟩ :=
      exists_polar_source_local_energy_close hr hf hfc hR A (le_max_right _ _) hgap
    have hgridg : ∀ n ∈ Finset.Icc 2 N, autocorr g (Real.log (n : ℝ)) = 0 := by
      intro n hn
      have hnrange := Finset.mem_Icc.mp hn
      have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      have hbound : |Real.log (n : ℝ)| ≤ A := by
        rw [abs_of_nonneg hln]
        exact (Real.log_le_log hnp (by exact_mod_cast hnrange.2)).trans (le_max_left _ _)
      have hval := hlocal (Real.log (n : ℝ)) hbound
      rw [hgrid n hn, zero_div] at hval
      exact (div_eq_zero_iff.mp hval).resolve_right hRg.ne'
    have hgC := hpolar g hg hgc hRg hgridg hpg
    have := (le_abs_self (normalizedArchEnergy g - normalizedArchEnergy f)).trans_lt herr
    linarith
  · intro hall f hf hfc hR hgrid _
    exact hall f hf hfc hR hgrid

end

end GaloisForLFunctions.BiScaleUncertainty
