import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftAveragedKernel

/-!
# Averaging one shift over the shift parameter

For a fixed shift `t`, the reflected and same-side variations of the shifted ground states,
integrated over `a > 0`, are variations against the averaged kernel `K(x,y) = G(x−y) − G(x+y)`:

    ∫_0^∞ ∫_0^t m_a(x) m_a(t−x) (u(x) − u(t−x))² dx da = ∫_0^t K(x, t−x) (u(x) − u(t−x))² dx,
    ∫_0^∞ ∫_{x>0} m_a(x) m_a(x+t) (u(x) − u(x+t))² dx da = ∫_{x>0} K(x, x+t) (u(x) − u(x+t))² dx.

The exchange of the two integrations needs no majorant: the integrands are nonnegative, and their
exact `a`-integrals `K(x,·) (…)²` are continuous in `x`. The averaged shifts are bounded by `t`
near `t = 0` and decay like `Φ((t − 2R)/2)` (reflected) and `Φ(t/2)` (same side) when `u` is
supported in `[−R, R]`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The averaged kernel -/

/-- The averaged kernel `K(x,y) = G(x − y) − G(x + y)`. -/
def averagedKernel (x y : ℝ) : ℝ := riemannAutocorr (x - y) - riemannAutocorr (x + y)

theorem averagedKernel_eq_integral (x y : ℝ) :
    averagedKernel x y = ∫ a in Ioi (0 : ℝ), shiftDifference a x * shiftDifference a y :=
  (integral_Ioi_shiftDifference_mul_shiftDifference x y).symm

theorem averagedKernel_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ averagedKernel x y := by
  rw [averagedKernel_eq_integral]
  exact setIntegral_nonneg measurableSet_Ioi fun a ha =>
    mul_nonneg (shiftDifference_nonneg_of_nonneg (le_of_lt ha) hx)
      (shiftDifference_nonneg_of_nonneg (le_of_lt ha) hy)

theorem averagedKernel_le_autocorr (x y : ℝ) : averagedKernel x y ≤ riemannAutocorr (x - y) := by
  unfold averagedKernel
  linarith [riemannAutocorr_nonneg (x + y)]

theorem averagedKernel_le_zero_point (x y : ℝ) : averagedKernel x y ≤ riemannKernelReal 0 :=
  (averagedKernel_le_autocorr x y).trans (riemannAutocorr_le_zero_point _)

theorem continuous_averagedKernel : Continuous fun p : ℝ × ℝ => averagedKernel p.1 p.2 :=
  (riemannAutocorr_continuous.comp (continuous_fst.sub continuous_snd)).sub
    (riemannAutocorr_continuous.comp (continuous_fst.add continuous_snd))

theorem continuous_shiftDifference_uncurry :
    Continuous fun p : ℝ × ℝ => shiftDifference p.1 p.2 := by
  unfold shiftDifference
  exact (continuous_riemannKernelReal.comp (continuous_snd.sub continuous_fst)).sub
    (continuous_riemannKernelReal.comp (continuous_snd.add continuous_fst))

theorem sq_sub_le_four_mul_sq {u : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |u x| ≤ M) (x y : ℝ) :
    (u x - u y) ^ 2 ≤ 4 * M ^ 2 := by
  have h : |u x - u y| ≤ 2 * M := by linarith [abs_sub (u x) (u y), hM x, hM y]
  calc (u x - u y) ^ 2 = |u x - u y| ^ 2 := (sq_abs _).symm
    _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = 4 * M ^ 2 := by ring

/-! ### The averaged reflected shift -/

/-- The averaged reflected variation of one shift,
`∫_0^t K(x, t−x) (u(x) − u(t−x))² dx`. -/
def averagedReflectedShift (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) t, averagedKernel x (t - x) * (u x - u (t - x)) ^ 2

theorem integrable_reflected_shift_prod {u : ℝ → ℝ} (hu : Continuous u) (t : ℝ) :
    Integrable (Function.uncurry fun a x =>
        shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (0 : ℝ) t))) := by
  have hcont : Continuous (Function.uncurry fun a x : ℝ =>
      shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2) := by
    have h2 : Continuous fun p : ℝ × ℝ => shiftDifference p.1 (t - p.2) :=
      continuous_shiftDifference_uncurry.comp
        (continuous_fst.prodMk (continuous_const.sub continuous_snd))
    exact (continuous_shiftDifference_uncurry.mul h2).mul
      (((hu.comp continuous_snd).sub (hu.comp (continuous_const.sub continuous_snd))).pow 2)
  rw [integrable_prod_iff' hcont.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · show Integrable (fun a => shiftDifference a x * shiftDifference a (t - x) *
      (u x - u (t - x)) ^ 2) (volume.restrict (Ioi 0))
    exact ((integrable_shiftDifference_mul_shiftDifference x (t - x)).mul_const _).integrableOn
  have hK : Integrable (fun x => averagedKernel x (t - x) * (u x - u (t - x)) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) t)) := by
    have hc : Continuous fun x => averagedKernel x (t - x) * (u x - u (t - x)) ^ 2 :=
      (continuous_averagedKernel.comp (continuous_id.prodMk (continuous_const.sub continuous_id))).mul
        ((hu.sub (hu.comp (continuous_const.sub continuous_id))).pow 2)
    exact (hc.integrableOn_Icc (a := 0) (b := t)).mono_set Ioo_subset_Icc_self
  refine hK.congr (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_)
  show averagedKernel x (t - x) * (u x - u (t - x)) ^ 2 =
    ∫ a in Ioi (0 : ℝ), ‖shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2‖
  rw [averagedKernel_eq_integral, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg
    (shiftDifference_nonneg_of_nonneg (le_of_lt ha) hx.1.le)
    (shiftDifference_nonneg_of_nonneg (le_of_lt ha) (by linarith [hx.2]))) (sq_nonneg _))]

/-- The shift average of the reflected difference integral. -/
theorem integral_Ioi_reflectedDifferenceIntegral_shiftedGroundState {u : ℝ → ℝ}
    (hu : Continuous u) (t : ℝ) :
    (∫ a in Ioi (0 : ℝ), ∫ x in Ioo (0 : ℝ) t,
        reflectedDifferenceJump (shiftedGroundState a) u t x) = averagedReflectedShift u t := by
  have e : ∀ a, (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) =
      ∫ x in Ioo (0 : ℝ) t,
        shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2 := fun a =>
    setIntegral_congr_fun measurableSet_Ioo fun x _ =>
      reflectedDifferenceJump_shiftedGroundState a u t x
  rw [integral_congr_ae (Eventually.of_forall e),
    integral_integral_swap (integrable_reflected_shift_prod hu t)]
  unfold averagedReflectedShift
  refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  rw [averagedKernel_eq_integral, ← integral_mul_const]

theorem integrableOn_reflectedDifferenceIntegral_shiftedGroundState {u : ℝ → ℝ}
    (hu : Continuous u) (t : ℝ) :
    IntegrableOn (fun a => ∫ x in Ioo (0 : ℝ) t,
      reflectedDifferenceJump (shiftedGroundState a) u t x) (Ioi 0) := by
  have h := (integrable_reflected_shift_prod hu t).integral_prod_left
  refine h.congr (Eventually.of_forall fun a => ?_)
  show (∫ x in Ioo (0 : ℝ) t,
      shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2) =
    ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x
  exact setIntegral_congr_fun measurableSet_Ioo fun x _ =>
    (reflectedDifferenceJump_shiftedGroundState a u t x).symm

theorem averagedReflectedShift_nonneg (u : ℝ → ℝ) (t : ℝ) : 0 ≤ averagedReflectedShift u t :=
  setIntegral_nonneg measurableSet_Ioo fun x hx =>
    mul_nonneg (averagedKernel_nonneg hx.1.le (by linarith [hx.2])) (sq_nonneg _)

theorem averagedReflectedShift_le_of_bound {u : ℝ → ℝ} {t C : ℝ} (ht : 0 < t)
    (hb : ∀ x ∈ Ioo (0 : ℝ) t, averagedKernel x (t - x) * (u x - u (t - x)) ^ 2 ≤ C) :
    averagedReflectedShift u t ≤ C * t := by
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) t)
    (f := fun x => averagedKernel x (t - x) * (u x - u (t - x)) ^ 2) (C := C)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (averagedKernel_nonneg hx.1.le (by linarith [hx.2])) (sq_nonneg _))]
      exact hb x hx)
  rw [Real.volume_real_Ioo, max_eq_left (by linarith), sub_zero, Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-- `averagedReflectedShift u t ≤ 4 M² Φ(0) t`. -/
theorem averagedReflectedShift_le_linear {u : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |u x| ≤ M) {t : ℝ}
    (ht : 0 < t) :
    averagedReflectedShift u t ≤ 4 * M ^ 2 * riemannKernelReal 0 * t := by
  refine averagedReflectedShift_le_of_bound ht fun x hx => ?_
  have h2 := averagedKernel_le_zero_point x (t - x)
  have h3 := sq_sub_le_four_mul_sq hM x (t - x)
  calc averagedKernel x (t - x) * (u x - u (t - x)) ^ 2
      ≤ riemannKernelReal 0 * (4 * M ^ 2) :=
        mul_le_mul h2 h3 (sq_nonneg _) (riemannKernelReal_pos 0).le
    _ = _ := by ring

/-- `averagedReflectedShift u t ≤ 4 M² Φ((t − 2R)/2) t` for `t ≥ 2R` when `u` is supported in
`[−R, R]`. -/
theorem averagedReflectedShift_le_decay {u : ℝ → ℝ} {M R : ℝ} (hM : ∀ x, |u x| ≤ M)
    (hsupp : ∀ x, R < |x| → u x = 0) {t : ℝ} (ht : 2 * R ≤ t) (ht0 : 0 < t) :
    averagedReflectedShift u t ≤ 4 * M ^ 2 * riemannKernelReal ((t - 2 * R) / 2) * t := by
  refine averagedReflectedShift_le_of_bound ht0 fun x hx => ?_
  obtain ⟨hx0, hxt⟩ := hx
  have hK := (riemannKernelReal_pos ((t - 2 * R) / 2)).le
  by_cases hmid : R < x ∧ x < t - R
  · rw [hsupp x (by rw [abs_of_pos hx0]; exact hmid.1),
      hsupp (t - x) (by rw [abs_of_pos (by linarith)]; linarith)]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    simp only [sub_self, sq, mul_zero]
    positivity
  · have hdist : (t - 2 * R) / 2 ≤ |x - (t - x)| / 2 := by
      rw [not_and_or] at hmid
      rcases hmid with h | h
      · rw [not_lt] at h
        have : t - 2 * R ≤ -(x - (t - x)) := by linarith
        have := le_abs.mpr (Or.inr this)
        linarith
      · rw [not_lt] at h
        have : t - 2 * R ≤ x - (t - x) := by linarith
        have := le_abs.mpr (Or.inl this)
        linarith
    have h1 : averagedKernel x (t - x) ≤ riemannKernelReal ((t - 2 * R) / 2) :=
      (averagedKernel_le_autocorr x (t - x)).trans
        ((riemannAutocorr_le_kernel_half _).trans
          (riemannKernelReal_antitone_of_nonneg (by linarith) hdist))
    have h3 := sq_sub_le_four_mul_sq hM x (t - x)
    calc averagedKernel x (t - x) * (u x - u (t - x)) ^ 2
        ≤ riemannKernelReal ((t - 2 * R) / 2) * (4 * M ^ 2) :=
          mul_le_mul h1 h3 (sq_nonneg _) hK
      _ = _ := by ring

theorem measurable_averagedReflectedShift {u : ℝ → ℝ} (hu : Continuous u) :
    Measurable (averagedReflectedShift u) := by
  have hF : Measurable fun p : ℝ × ℝ =>
      if 0 < p.2 ∧ p.2 < p.1 then averagedKernel p.2 (p.1 - p.2) * (u p.2 - u (p.1 - p.2)) ^ 2
      else 0 := by
    have hc : Continuous fun p : ℝ × ℝ =>
        averagedKernel p.2 (p.1 - p.2) * (u p.2 - u (p.1 - p.2)) ^ 2 :=
      (continuous_averagedKernel.comp (continuous_snd.prodMk (continuous_fst.sub continuous_snd))).mul
        (((hu.comp continuous_snd).sub (hu.comp (continuous_fst.sub continuous_snd))).pow 2)
    refine Measurable.ite ?_ hc.measurable measurable_const
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have h := (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have heq : averagedReflectedShift u = fun t => ∫ x,
      (if 0 < x ∧ x < t then averagedKernel x (t - x) * (u x - u (t - x)) ^ 2 else 0) := by
    funext t
    unfold averagedReflectedShift
    rw [← integral_indicator measurableSet_Ioo]
    congr 1
    funext x
    simp only [Set.indicator_apply, mem_Ioo]
  rw [heq]
  exact h

/-! ### The averaged same-side shift -/

/-- The averaged same-side variation of one shift,
`∫_{x>0} K(x, x+t) (u(x) − u(x+t))² dx`. -/
def averagedSameSideShift (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), averagedKernel x (x + t) * (u x - u (x + t)) ^ 2

theorem hasCompactSupport_sub_translate {u : ℝ → ℝ} (huc : HasCompactSupport u) (t : ℝ) :
    HasCompactSupport fun x => u x - u (x + t) :=
  huc.sub (huc.comp_homeomorph (Homeomorph.addRight t))

theorem integrable_sameSide_shift_prod {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (Function.uncurry fun a x =>
        shiftDifference a x * shiftDifference a (x + t) * (u x - u (x + t)) ^ 2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hcont : Continuous (Function.uncurry fun a x : ℝ =>
      shiftDifference a x * shiftDifference a (x + t) * (u x - u (x + t)) ^ 2) := by
    have h2 : Continuous fun p : ℝ × ℝ => shiftDifference p.1 (p.2 + t) :=
      continuous_shiftDifference_uncurry.comp
        (continuous_fst.prodMk (continuous_snd.add continuous_const))
    exact (continuous_shiftDifference_uncurry.mul h2).mul
      (((hu.comp continuous_snd).sub (hu.comp (continuous_snd.add continuous_const))).pow 2)
  rw [integrable_prod_iff' hcont.aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · show Integrable (fun a => shiftDifference a x * shiftDifference a (x + t) *
      (u x - u (x + t)) ^ 2) (volume.restrict (Ioi 0))
    exact ((integrable_shiftDifference_mul_shiftDifference x (x + t)).mul_const _).integrableOn
  have hK : Integrable (fun x => averagedKernel x (x + t) * (u x - u (x + t)) ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_continuous_mul_sq
      (continuous_averagedKernel.comp (continuous_id.prodMk (continuous_id.add continuous_const)))
      (hu.sub (hu.comp (continuous_id.add continuous_const)))
      (hasCompactSupport_sub_translate huc t) _
  refine hK.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
  show averagedKernel x (x + t) * (u x - u (x + t)) ^ 2 =
    ∫ a in Ioi (0 : ℝ), ‖shiftDifference a x * shiftDifference a (x + t) * (u x - u (x + t)) ^ 2‖
  rw [averagedKernel_eq_integral, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun a ha => ?_
  have hx0 : 0 < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg
    (shiftDifference_nonneg_of_nonneg (le_of_lt ha) hx0.le)
    (shiftDifference_nonneg_of_nonneg (le_of_lt ha) (by linarith))) (sq_nonneg _))]

/-- The shift average of the same-side integral. -/
theorem integral_Ioi_sameSideIntegral_shiftedGroundState {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) {t : ℝ} (ht : 0 ≤ t) :
    (∫ a in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ),
        sameSideGroundJump (shiftedGroundState a) u t x) = averagedSameSideShift u t := by
  have e : ∀ a, (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) =
      ∫ x in Ioi (0 : ℝ),
        shiftDifference a x * shiftDifference a (x + t) * (u x - u (x + t)) ^ 2 := fun a =>
    setIntegral_congr_fun measurableSet_Ioi fun x _ =>
      sameSideGroundJump_shiftedGroundState a u t x
  rw [integral_congr_ae (Eventually.of_forall e),
    integral_integral_swap (integrable_sameSide_shift_prod hu huc ht)]
  unfold averagedSameSideShift
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [averagedKernel_eq_integral, ← integral_mul_const]

theorem integrableOn_sameSideIntegral_shiftedGroundState {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun a => ∫ x in Ioi (0 : ℝ),
      sameSideGroundJump (shiftedGroundState a) u t x) (Ioi 0) := by
  have h := (integrable_sameSide_shift_prod hu huc ht).integral_prod_left
  refine h.congr (Eventually.of_forall fun a => ?_)
  show (∫ x in Ioi (0 : ℝ),
      shiftDifference a x * shiftDifference a (x + t) * (u x - u (x + t)) ^ 2) =
    ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x
  exact setIntegral_congr_fun measurableSet_Ioi fun x _ =>
    (sameSideGroundJump_shiftedGroundState a u t x).symm

theorem averagedSameSideShift_nonneg (u : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ averagedSameSideShift u t :=
  setIntegral_nonneg measurableSet_Ioi fun x hx =>
    mul_nonneg (averagedKernel_nonneg (le_of_lt hx) (by linarith [mem_Ioi.mp hx])) (sq_nonneg _)

theorem averagedSameSideShift_le_of_indicator_bound {u : ℝ → ℝ} {t C R : ℝ} (hR : 0 ≤ R)
    (hb : ∀ x, 0 < x → |averagedKernel x (x + t) * (u x - u (x + t)) ^ 2| ≤
      C * (if x ≤ R then 1 else 0)) :
    averagedSameSideShift u t ≤ C * R := by
  unfold averagedSameSideShift
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans (integral_Ioi_norm_le_of_le_indicator hR hb)

/-- `averagedSameSideShift u t ≤ Φ(0) (L² + 4M²) t R` for `t > 0`, where `L` is a Lipschitz
constant of `u` on `[−R−1, R+1]`. -/
theorem averagedSameSideShift_le_linear {u : ℝ → ℝ} {M R L : ℝ} (hR : 0 ≤ R)
    (hM : ∀ x, |u x| ≤ M) (hsupp : ∀ x, R < |x| → u x = 0)
    (hL : ∀ x ∈ Icc (-R - 1) (R + 1), ∀ y ∈ Icc (-R - 1) (R + 1), |u y - u x| ≤ L * |y - x|)
    {t : ℝ} (ht : 0 < t) :
    averagedSameSideShift u t ≤ riemannKernelReal 0 * (L ^ 2 + 4 * M ^ 2) * t * R := by
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  refine averagedSameSideShift_le_of_indicator_bound hR fun x hx => ?_
  split_ifs with hxR
  · rw [mul_one, abs_of_nonneg (mul_nonneg (averagedKernel_nonneg hx.le (by linarith))
      (sq_nonneg _))]
    have hK := averagedKernel_le_zero_point x (x + t)
    have hw : (u x - u (x + t)) ^ 2 ≤ (L ^ 2 + 4 * M ^ 2) * t := by
      rcases le_or_gt t 1 with ht1 | ht1
      · have hmem1 : x ∈ Icc (-R - 1) (R + 1) := ⟨by linarith, by linarith⟩
        have hmem2 : x + t ∈ Icc (-R - 1) (R + 1) := ⟨by linarith, by linarith⟩
        have h := hL x hmem1 (x + t) hmem2
        rw [show x + t - x = t by ring, abs_of_pos ht] at h
        have hL0 : 0 ≤ L * t := (abs_nonneg _).trans h
        have h2 : (u (x + t) - u x) ^ 2 ≤ (L * t) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
        have h3 : (L * t) ^ 2 ≤ L ^ 2 * t := by
          have : L ^ 2 * t ^ 2 ≤ L ^ 2 * t := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg L)
            nlinarith
          nlinarith
        nlinarith [sq_nonneg M]
      · have h3 := sq_sub_le_four_mul_sq hM x (x + t)
        nlinarith [sq_nonneg L]
    calc averagedKernel x (x + t) * (u x - u (x + t)) ^ 2
        ≤ riemannKernelReal 0 * ((L ^ 2 + 4 * M ^ 2) * t) :=
          mul_le_mul hK hw (sq_nonneg _) hΘ0
      _ = _ := by ring
  · rw [not_le] at hxR
    rw [hsupp x (by rw [abs_of_pos hx]; exact hxR),
      hsupp (x + t) (by rw [abs_of_pos (by linarith)]; linarith)]
    simp

/-- `averagedSameSideShift u t ≤ 4 M² Φ(t/2) R` for `t ≥ 0` when `u` is supported in `[−R, R]`. -/
theorem averagedSameSideShift_le_decay {u : ℝ → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (hM : ∀ x, |u x| ≤ M) (hsupp : ∀ x, R < |x| → u x = 0) {t : ℝ} (ht : 0 ≤ t) :
    averagedSameSideShift u t ≤ 4 * M ^ 2 * riemannKernelReal (t / 2) * R := by
  refine averagedSameSideShift_le_of_indicator_bound hR fun x hx => ?_
  split_ifs with hxR
  · rw [mul_one, abs_of_nonneg (mul_nonneg (averagedKernel_nonneg hx.le (by linarith))
      (sq_nonneg _))]
    have hK : averagedKernel x (x + t) ≤ riemannKernelReal (t / 2) := by
      refine (averagedKernel_le_autocorr x (x + t)).trans ?_
      rw [show x - (x + t) = -t by ring, riemannAutocorr_neg]
      have := riemannAutocorr_le_kernel_half t
      rwa [abs_of_nonneg ht] at this
    have h3 := sq_sub_le_four_mul_sq hM x (x + t)
    calc averagedKernel x (x + t) * (u x - u (x + t)) ^ 2
        ≤ riemannKernelReal (t / 2) * (4 * M ^ 2) :=
          mul_le_mul hK h3 (sq_nonneg _) (riemannKernelReal_pos _).le
      _ = _ := by ring
  · rw [not_le] at hxR
    rw [hsupp x (by rw [abs_of_pos hx]; exact hxR),
      hsupp (x + t) (by rw [abs_of_pos (by linarith)]; linarith)]
    simp

theorem measurable_averagedSameSideShift {u : ℝ → ℝ} (hu : Continuous u) :
    Measurable (averagedSameSideShift u) := by
  have hc : Continuous fun p : ℝ × ℝ =>
      averagedKernel p.2 (p.2 + p.1) * (u p.2 - u (p.2 + p.1)) ^ 2 :=
    (continuous_averagedKernel.comp (continuous_snd.prodMk (continuous_snd.add continuous_fst))).mul
      (((hu.comp continuous_snd).sub (hu.comp (continuous_snd.add continuous_fst))).pow 2)
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
