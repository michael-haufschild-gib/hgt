import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPoissonEuler
import GaloisForLFunctions.HTGeometry.PoissonFatou
import GaloisForLFunctions.RHTower.LogSineStieltjesRepresentation

/-!
# Positive conductance moments for the logarithmic sine profile

The negative cosine coefficients of the literal profile are shifted Hausdorff
moments. The explicit map `R(s) = (sqrt(s+1)-sqrt(s))^2` lies in `(0,1)`, and the
mixing weight is positive and integrable on `(0,infinity)`. Consequently every
finite shifted conductance Hankel form is a nonnegative weighted square.

The proof connects the actual profile to its positive Stieltjes representation,
then evaluates each sine resolvent's cosine coefficients using the existing
Poisson Fourier moments. All interchanges and moment integrability are proved.
This proves the proposed all-order source positivity for the test family; it
makes no assertion about real spectrum, nonreal zeros, or the theta source.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open RHTower.WeilSingularArithmetic
namespace RHTower
noncomputable section


private theorem additivePoissonKernel_coe {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    additivePoissonKernel (realPoissonParameter r hr0 hr1) (t : UnitAddCircle) =
      (1 - r ^ 2) / (1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2) := by
  change poissonKernel 0 (r : ℂ)
    ((AddCircle.homeomorphCircle one_ne_zero (t : UnitAddCircle)) : ℂ) = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  simp only [div_one, Circle.coe_exp]
  exact (poissonKer_eq_poissonKernel hr0 (2 * Real.pi * t)).symm

private theorem fourier_re_unit_coe (n : ℕ) (t : ℝ) :
    (fourier (n : ℤ) (t : UnitAddCircle)).re = Real.cos (2 * Real.pi * n * t) := by
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_one]
  have he : 2 * (Real.pi : ℂ) * Complex.I * (n : ℤ) * (t : ℂ) / (1 : ℂ) =
      ((2 * Real.pi * n * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re]

/-- Exact cosine moments of the angular Poisson kernel on the unit interval. -/
theorem integral_unit_poissonKer_cos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∫ t in Ioo (0 : ℝ) 1, poissonKer r (2 * Real.pi * t) *
      Real.cos (2 * Real.pi * n * t)) = r ^ n := by
  let P := additivePoissonKernel (realPoissonParameter r hr0 hr1)
  have hc : Continuous (fun x : UnitAddCircle => (P x : ℂ) * fourier (n : ℤ) x) :=
    (Complex.continuous_ofReal.comp P.continuous).mul (fourier (n : ℤ)).continuous
  have hi : Integrable (fun x : UnitAddCircle => (P x : ℂ) * fourier (n : ℤ) x) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he := integral_realPoissonKernel_fourier hr0 hr1 (n : ℤ)
  have hre := congrArg Complex.re he
  change (∫ x : UnitAddCircle, (P x : ℂ) * fourier (n : ℤ) x).re = _ at hre
  have hri : (∫ x : UnitAddCircle, ((P x : ℂ) * fourier (n : ℤ) x).re) =
      (∫ x : UnitAddCircle, (P x : ℂ) * fourier (n : ℤ) x).re := by
    exact integral_re hi
  rw [← hri] at hre
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Int.natAbs_natCast, ← Complex.ofReal_pow, Complex.ofReal_re] at hre
  rw [← UnitAddCircle.integral_preimage 0] at hre
  simp only [zero_add] at hre
  rw [integral_Ioc_eq_integral_Ioo] at hre
  calc
    _ = ∫ t in Ioo (0 : ℝ) 1, P (t : UnitAddCircle) *
        (fourier (n : ℤ) (t : UnitAddCircle)).re := by
      apply integral_congr_ae
      filter_upwards with t
      rw [fourier_re_unit_coe]
      change poissonKer r (2 * Real.pi * t) * _ =
        additivePoissonKernel (realPoissonParameter r hr0 hr1) (t : UnitAddCircle) * _
      rw [additivePoissonKernel_coe]
      rfl
    _ = r ^ n := hre

def logSinePoissonRadius (s : ℝ) : ℝ := (Real.sqrt (s + 1) - Real.sqrt s) ^ 2

theorem logSinePoissonRadius_pos {s : ℝ} (hs : 0 < s) :
    0 < logSinePoissonRadius s := by
  have ha := Real.sq_sqrt (show 0 ≤ s + 1 by linarith)
  have hb := Real.sq_sqrt hs.le
  have hna := Real.sqrt_nonneg (s + 1)
  have hnb := Real.sqrt_nonneg s
  have hd : 0 < Real.sqrt (s + 1) - Real.sqrt s := by nlinarith
  exact sq_pos_of_pos hd

theorem logSinePoissonRadius_lt_one {s : ℝ} (hs : 0 < s) :
    logSinePoissonRadius s < 1 := by
  have ha := Real.sq_sqrt (show 0 ≤ s + 1 by linarith)
  have hb := Real.sq_sqrt hs.le
  have hna := Real.sqrt_nonneg (s + 1)
  have hnb := Real.sqrt_pos.mpr hs
  have hd0 : 0 < Real.sqrt (s + 1) - Real.sqrt s := by nlinarith
  have hd1 : Real.sqrt (s + 1) - Real.sqrt s < 1 := by nlinarith
  unfold logSinePoissonRadius
  nlinarith

theorem logSinePoissonRadius_relation {s : ℝ} (hs : 0 < s) :
    4 * s * logSinePoissonRadius s = (1 - logSinePoissonRadius s) ^ 2 := by
  have ha := Real.sq_sqrt (show 0 ≤ s + 1 by linarith)
  have hb := Real.sq_sqrt hs.le
  have hd : 1 - (Real.sqrt (s + 1) - Real.sqrt s) ^ 2 =
      2 * Real.sqrt s * (Real.sqrt (s + 1) - Real.sqrt s) := by nlinarith
  unfold logSinePoissonRadius
  rw [hd, mul_pow, mul_pow, hb]
  ring

private theorem sine_resolvent_poisson {s : ℝ} (hs : 0 < s) (t : ℝ) :
    (Real.sin (Real.pi * t)) ^ 2 / ((Real.sin (Real.pi * t)) ^ 2 + s) =
      1 - ((1 - logSinePoissonRadius s) / (1 + logSinePoissonRadius s)) *
        poissonKer (logSinePoissonRadius s) (2 * Real.pi * t) := by
  set r := logSinePoissonRadius s
  have hr : 0 < r := logSinePoissonRadius_pos hs
  have hr1 : r < 1 := logSinePoissonRadius_lt_one hs
  have hrel : 4 * s * r = (1 - r) ^ 2 := logSinePoissonRadius_relation hs
  have hc : Real.cos (2 * Real.pi * t) = 1 - 2 * (Real.sin (Real.pi * t)) ^ 2 := by
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * t)]
  have hden : 1 - 2 * r * Real.cos (2 * Real.pi * t) + r ^ 2 =
      4 * r * ((Real.sin (Real.pi * t)) ^ 2 + s) := by
    rw [hc]
    nlinarith [hrel]
  have hd : (Real.sin (Real.pi * t)) ^ 2 + s ≠ 0 := by positivity
  unfold poissonKer
  rw [hden]
  field_simp [hr.ne', hd, show 1 + r ≠ 0 by positivity]
  nlinarith [hrel]

private theorem integral_unit_cos_eq_zero {n : ℕ} (hn : 0 < n) :
    (∫ t in Ioo (0 : ℝ) 1, Real.cos (2 * Real.pi * n * t)) = 0 := by
  simpa [poissonKer, zero_pow hn.ne'] using
    integral_unit_poissonKer_cos (r := 0) le_rfl zero_lt_one n

/-- Each elementary sine resolvent has a positive geometric negative cosine sequence. -/
theorem integral_sine_resolvent_cos {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 0 < n) :
    -(∫ t in Ioo (0 : ℝ) 1,
      (Real.sin (Real.pi * t)) ^ 2 / ((Real.sin (Real.pi * t)) ^ 2 + s) *
        Real.cos (2 * Real.pi * n * t)) =
      (1 - logSinePoissonRadius s) / (1 + logSinePoissonRadius s) *
        logSinePoissonRadius s ^ n := by
  set r := logSinePoissonRadius s
  have hr0 : 0 ≤ r := (logSinePoissonRadius_pos hs).le
  have hr1 : r < 1 := logSinePoissonRadius_lt_one hs
  have hc : Continuous (fun t : ℝ => Real.cos (2 * Real.pi * n * t)) := by fun_prop
  have hp : Continuous (fun t : ℝ => poissonKer r (2 * Real.pi * t)) :=
    (poissonKer_continuous (by rwa [abs_of_nonneg hr0])).comp (by fun_prop)
  have hci : IntegrableOn (fun t : ℝ => Real.cos (2 * Real.pi * n * t)) (Ioo 0 1) :=
    hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hpi : IntegrableOn (fun t : ℝ =>
      ((1 - r) / (1 + r)) * (poissonKer r (2 * Real.pi * t) *
        Real.cos (2 * Real.pi * n * t))) (Ioo 0 1) :=
    ((hp.mul hc).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self).const_mul _
  have he : (fun t : ℝ =>
      (Real.sin (Real.pi * t)) ^ 2 / ((Real.sin (Real.pi * t)) ^ 2 + s) *
        Real.cos (2 * Real.pi * n * t)) =
      fun t => Real.cos (2 * Real.pi * n * t) -
        ((1 - r) / (1 + r)) * (poissonKer r (2 * Real.pi * t) *
          Real.cos (2 * Real.pi * n * t)) := by
    funext t
    rw [sine_resolvent_poisson hs]
    dsimp [r]
    ring
  rw [he, integral_sub hci hpi, integral_const_mul, integral_unit_cos_eq_zero hn,
    integral_unit_poissonKer_cos hr0 hr1]
  simp

/-- Negative cosine coefficient of the literal logarithmic sine profile. -/
def logSineConductance (δ : ℝ) (n : ℕ) : ℝ :=
  -(∫ t in Ioo (0 : ℝ) 1, logSineProfile δ t * Real.cos (2 * Real.pi * n * t))

/-- Integrable positive weight whose pushforward by `logSinePoissonRadius` gives the
Hausdorff moments of the shifted conductance sequence. -/
def logSineMomentWeight (δ s : ℝ) : ℝ :=
  logSineStieltjesDensity δ s *
    ((1 - logSinePoissonRadius s) / (1 + logSinePoissonRadius s)) *
      logSinePoissonRadius s

theorem logSineConductance_succ_eq_moment {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    logSineConductance δ (n + 1) = ∫ s in Ioi (0 : ℝ),
      logSineMomentWeight δ s * logSinePoissonRadius s ^ n := by
  unfold logSineConductance
  rw [logSineProfile_cosine_stieltjes hδ, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [neg_mul_eq_mul_neg, integral_sine_resolvent_cos hs (Nat.succ_pos n)]
  unfold logSineMomentWeight
  rw [pow_succ]
  ring

/-- Strict positivity of the explicit mixing weight. -/
theorem logSineMomentWeight_pos {δ s : ℝ} (hδ : 0 ≤ δ) (hs : 0 < s) :
    0 < logSineMomentWeight δ s := by
  have hr := logSinePoissonRadius_pos hs
  have hr1 := logSinePoissonRadius_lt_one hs
  have hd := logSineStieltjesDensity_pos hδ hs
  unfold logSineMomentWeight
  positivity

private theorem logSineMomentWeight_bound {δ s : ℝ} (hδ : 0 ≤ δ) (hs : 0 < s) :
    logSineMomentWeight δ s ≤ logSineStieltjesDensity δ s / (1 + s) := by
  set r := logSinePoissonRadius s
  have hr : 0 < r := logSinePoissonRadius_pos hs
  have hr1 : r < 1 := logSinePoissonRadius_lt_one hs
  have hrel : 4 * s * r = (1 - r) ^ 2 := logSinePoissonRadius_relation hs
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hrd : r ≤ 1 / (1 + s) := by
    apply (le_div_iff₀ (show 0 < 1 + s by positivity)).mpr
    nlinarith
  have hc : (1 - r) / (1 + r) ≤ 1 := by
    apply (div_le_one (show 0 < 1 + r by positivity)).mpr
    linarith
  have hd : 0 ≤ logSineStieltjesDensity δ s := (logSineStieltjesDensity_pos hδ hs).le
  change logSineStieltjesDensity δ s * ((1 - r) / (1 + r)) * r ≤ _
  calc
    _ ≤ logSineStieltjesDensity δ s * r :=
      mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hd hc) hr.le
    _ ≤ logSineStieltjesDensity δ s * (1 / (1 + s)) :=
      mul_le_mul_of_nonneg_left hrd hd
    _ = _ := by ring

/-- The Hausdorff mixing measure is finite. -/
theorem integrableOn_logSineMomentWeight {δ : ℝ} (hδ : 0 ≤ δ) :
    IntegrableOn (logSineMomentWeight δ) (Ioi 0) := by
  have hb : IntegrableOn (fun s : ℝ => logSineStieltjesDensity δ s / (1 + s))
      (Ioi 0) := by
    have he : (fun s : ℝ => logSineStieltjesDensity δ s / (1 + s)) =
        fun s => (1 : ℝ) ^ 2 / (1 ^ 2 + s) * logSineStieltjesDensity δ s := by
      funext s
      simp only [one_pow]
      ring
    rw [he]
    exact integrableOn_logSineStieltjes zero_lt_one
  apply hb.mono'
  · have hm : Measurable (logSineMomentWeight δ) := by
      unfold logSineMomentWeight logSinePoissonRadius logSineStieltjesDensity
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (logSineMomentWeight_pos hδ hs).le]
    exact logSineMomentWeight_bound hδ hs

/-- Every power moment used by the conductance and Hankel identities is integrable. -/
theorem integrableOn_logSineMoment {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    IntegrableOn (fun s : ℝ => logSineMomentWeight δ s * logSinePoissonRadius s ^ n)
      (Ioi 0) := by
  apply (integrableOn_logSineMomentWeight hδ).mono'
  · have hm : Measurable (fun s : ℝ =>
        logSineMomentWeight δ s * logSinePoissonRadius s ^ n) := by
      unfold logSineMomentWeight logSinePoissonRadius logSineStieltjesDensity
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hw := (logSineMomentWeight_pos hδ hs).le
    have hr := (logSinePoissonRadius_pos hs).le
    rw [Real.norm_of_nonneg (mul_nonneg hw (pow_nonneg hr n))]
    exact mul_le_of_le_one_right hw
      (pow_le_one₀ hr (logSinePoissonRadius_lt_one hs).le)

/-- Exact positive integral behind every finite shifted conductance Hankel form. -/
theorem logSineConductance_hankel_eq_integral {δ : ℝ} (hδ : 0 ≤ δ)
    (shift : ℕ) (F : Finset ℕ) (c : ℕ → ℝ) :
    (∑ m ∈ F, ∑ n ∈ F, c m * c n * logSineConductance δ (m + n + shift + 1)) =
      ∫ s in Ioi (0 : ℝ), logSineMomentWeight δ s * logSinePoissonRadius s ^ shift *
        (∑ m ∈ F, c m * logSinePoissonRadius s ^ m) ^ 2 := by
  have hi (m n : ℕ) : IntegrableOn (fun s : ℝ => c m * c n *
      (logSineMomentWeight δ s * logSinePoissonRadius s ^ (m + n + shift))) (Ioi 0) :=
    (integrableOn_logSineMoment hδ (m + n + shift)).const_mul _
  calc
    _ = ∑ m ∈ F, ∑ n ∈ F, ∫ s in Ioi (0 : ℝ), c m * c n *
        (logSineMomentWeight δ s * logSinePoissonRadius s ^ (m + n + shift)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul, logSineConductance_succ_eq_moment hδ]
    _ = ∫ s in Ioi (0 : ℝ), ∑ m ∈ F, ∑ n ∈ F, c m * c n *
        (logSineMomentWeight δ s * logSinePoissonRadius s ^ (m + n + shift)) := by
      rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun n _ => hi m n]
      apply Finset.sum_congr rfl
      intro m hm
      rw [integral_finsetSum _ fun n _ => hi m n]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with s
      rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [pow_add, pow_add]
      ring

/-- All finite shifted Hankel forms of the literal positive-frequency conductances are
nonnegative; this is a source theorem, with no spectral-placement premise. -/
theorem logSineConductance_hankel_nonneg {δ : ℝ} (hδ : 0 ≤ δ)
    (shift : ℕ) (F : Finset ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ m ∈ F, ∑ n ∈ F, c m * c n * logSineConductance δ (m + n + shift + 1) := by
  rw [logSineConductance_hankel_eq_integral hδ]
  apply setIntegral_nonneg measurableSet_Ioi
  intro s hs
  exact mul_nonneg (mul_nonneg (logSineMomentWeight_pos hδ hs).le
    (pow_nonneg (logSinePoissonRadius_pos hs).le shift)) (sq_nonneg _)

/-- Every positive-frequency conductance is strictly positive. -/
theorem logSineConductance_succ_pos {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    0 < logSineConductance δ (n + 1) := by
  rw [logSineConductance_succ_eq_moment hδ]
  have hp (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      0 < logSineMomentWeight δ s * logSinePoissonRadius s ^ n :=
    mul_pos (logSineMomentWeight_pos hδ hs) (pow_pos (logSinePoissonRadius_pos hs) n)
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs; exact (hp s hs).le)
    (integrableOn_logSineMoment hδ n)).mpr
  have he : Function.support (fun s : ℝ =>
      logSineMomentWeight δ s * logSinePoissonRadius s ^ n) ∩ Ioi 0 = Ioi 0 := by
    apply inter_eq_right.mpr
    intro s hs
    exact (hp s hs).ne'
  rw [he]
  simp

end
end RHTower
