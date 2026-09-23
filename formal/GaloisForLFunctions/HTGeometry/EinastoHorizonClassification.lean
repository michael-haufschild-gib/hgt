import GaloisForLFunctions.HTGeometry.EinastoHorizonBalance
import GaloisForLFunctions.HTGeometry.EinastoHorizonExistence

/-!
# Complete Einasto horizon classification and critical quadratic contact

Proves the zero/one/two positive-root classification described in section 4.1
of arXiv:2608.23600v1 for every positive Einasto central density, length, and
shape. Actual integrated compactness has a unique maximum. The reciprocal of
that maximum defines the critical central density. Below it every lapse value
is positive; at it there is one zero; above it there are exactly two zeros.

The critical zero is nondegenerate: the actual radial first derivative is
zero and the actual second derivative is strictly positive. This closes the
paper's double-root claim through derivatives, beyond merely counting roots.
All positive radii are covered by the logarithmic coordinate; there are no
root-existence, monotonicity, or asymptotic hypotheses and no computations.
-/

noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

/-- Logarithmic-radius compactness of the unit-central-density Einasto source. -/
def einastoLogCompactness (l a t : ℝ) : ℝ := 2 * einastoMass 0 l a (exp t) / exp t

theorem einastoLogCompactness_core (l a t : ℝ) :
    einastoLogCompactness l a t = 2 * exp t ^ (2 : ℕ) * einastoCore 0 l a (exp t) := by
  rw [einastoLogCompactness, einastoMass_core]
  field_simp

theorem einastoLogCompactness_pos (l a t : ℝ) : 0 < einastoLogCompactness l a t := by
  rw [einastoLogCompactness_core]
  exact mul_pos (by positivity) (einastoCore_pos 0 l a t)

theorem einastoLogCompactness_continuous (l a : ℝ) : Continuous (einastoLogCompactness l a) := by
  simp only [funext (einastoLogCompactness_core l a)]
  exact (continuous_const.mul (continuous_exp.pow 2)).mul ((einastoCore_continuous 0 l a).comp continuous_exp)

theorem einastoLogCompactness_core_limit (l a : ℝ) :
    Tendsto (einastoLogCompactness l a) atBot (𝓝 0) := by
  have h := ((tendsto_exp_atBot.pow 2).const_mul 2).mul
    ((einastoCore_continuous 0 l a).continuousAt.tendsto.comp tendsto_exp_atBot)
  simp only [funext (einastoLogCompactness_core l a)]
  simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, Function.comp_def] using h

theorem einastoLogCompactness_infinity_limit (l a : ℝ) :
    Tendsto (einastoLogCompactness l a) atTop (𝓝 0) := by
  have h := (((einastoMass_total 0 l a).comp tendsto_exp_atTop).const_mul 2).div_atTop tendsto_exp_atTop
  unfold einastoLogCompactness
  simpa only [Function.comp_def] using h

theorem einastoLogCompactness_derivative (l a t : ℝ) :
    HasDerivAt (einastoLogCompactness l a)
      (2 * einastoHorizonBalance 0 l a (exp t) / exp t) t := by
  have h := (((einastoMass_derivative 0 l a (exp t)).comp t (hasDerivAt_exp t)).const_mul 2).div
    (hasDerivAt_exp t) (exp_ne_zero t)
  apply h.congr_deriv
  dsimp [einastoHorizonBalance]
  field_simp

/-- Compactness increases strictly up to its unique peak. -/
theorem einastoLogCompactness_strictMono_left (l a : ℝ) :
    StrictMonoOn (einastoLogCompactness l a) (Iic (einastoBalanceZeroLogRadius 0 l a)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic _) (einastoLogCompactness_continuous l a).continuousOn
  intro x hx
  have hx' : x < einastoBalanceZeroLogRadius 0 l a := by simpa only [interior_Iic, mem_Iio] using hx
  rw [(einastoLogCompactness_derivative l a x).deriv]
  exact div_pos (mul_pos (by norm_num) ((einastoHorizonBalance_pos_iff 0 l a x).mpr hx')) (exp_pos x)

/-- Compactness decreases strictly after its unique peak. -/
theorem einastoLogCompactness_strictAnti_right (l a : ℝ) :
    StrictAntiOn (einastoLogCompactness l a) (Ici (einastoBalanceZeroLogRadius 0 l a)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (einastoLogCompactness_continuous l a).continuousOn
  intro x hx
  have hx' : einastoBalanceZeroLogRadius 0 l a < x := by simpa only [interior_Ici, mem_Ioi] using hx
  rw [(einastoLogCompactness_derivative l a x).deriv]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (by norm_num) ((einastoHorizonBalance_neg_iff 0 l a x).mpr hx')) (exp_pos x)

theorem einastoLogCompactness_le_peak (l a t : ℝ) :
    einastoLogCompactness l a t ≤ einastoLogCompactness l a (einastoBalanceZeroLogRadius 0 l a) := by
  rcases le_total t (einastoBalanceZeroLogRadius 0 l a) with h | h
  · exact (einastoLogCompactness_strictMono_left l a).monotoneOn
      (mem_Iic.mpr h) (mem_Iic.mpr le_rfl) h
  · exact (einastoLogCompactness_strictAnti_right l a).antitoneOn
      (mem_Ici.mpr le_rfl) (mem_Ici.mpr h) h

theorem einastoLogCompactness_eq_peak_iff (l a t : ℝ) :
    einastoLogCompactness l a t = einastoLogCompactness l a (einastoBalanceZeroLogRadius 0 l a) ↔
      t = einastoBalanceZeroLogRadius 0 l a := by
  constructor
  · intro he
    rcases lt_trichotomy t (einastoBalanceZeroLogRadius 0 l a) with ht | ht | ht
    · have hh := einastoLogCompactness_strictMono_left l a (mem_Iic.mpr ht.le) (mem_Iic.mpr le_rfl) ht
      rw [he] at hh
      exact (lt_irrefl _ hh).elim
    · exact ht
    · have hh := einastoLogCompactness_strictAnti_right l a (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.le) ht
      rw [he] at hh
      exact (lt_irrefl _ hh).elim
  · rintro rfl
    rfl

/-- Logarithm of the central density at which the lapse first touches zero. -/
def einastoCriticalLogDensity (l a : ℝ) : ℝ :=
  -log (einastoLogCompactness l a (einastoBalanceZeroLogRadius 0 l a))

theorem einastoMetric_compactness (d l a t : ℝ) :
    einastoMetric d l a (exp t) = 1 - exp d * einastoLogCompactness l a t := by
  rw [einastoMetric_core, einastoCore_amplitude, einastoLogCompactness_core]
  ring

theorem einastoCriticalLogDensity_calibration (l a : ℝ) :
    exp (einastoCriticalLogDensity l a) * einastoLogCompactness l a (einastoBalanceZeroLogRadius 0 l a) = 1 := by
  rw [einastoCriticalLogDensity, exp_neg, exp_log (einastoLogCompactness_pos _ _ _)]
  have hp := (einastoLogCompactness_pos l a (einastoBalanceZeroLogRadius 0 l a)).ne'
  field_simp

theorem einastoMetric_critical_peak (l a : ℝ) :
    einastoMetric (einastoCriticalLogDensity l a) l a (exp (einastoBalanceZeroLogRadius 0 l a)) = 0 := by
  rw [einastoMetric_compactness, einastoCriticalLogDensity_calibration, sub_self]

/-- At critical density the only positive lapse zero is the compactness maximum. -/
theorem einastoMetric_critical_zero_iff (l a t : ℝ) :
    einastoMetric (einastoCriticalLogDensity l a) l a (exp t) = 0 ↔
      t = einastoBalanceZeroLogRadius 0 l a := by
  rw [einastoMetric_compactness]
  have hc := einastoCriticalLogDensity_calibration l a
  constructor
  · intro h
    apply (einastoLogCompactness_eq_peak_iff l a t).mp
    have he : exp (einastoCriticalLogDensity l a) * einastoLogCompactness l a t =
        exp (einastoCriticalLogDensity l a) * einastoLogCompactness l a (einastoBalanceZeroLogRadius 0 l a) := by linarith
    exact mul_left_cancel₀ (exp_ne_zero _) he
  · rintro rfl
    rw [hc, sub_self]

/-- The lapse has a unique minimum at the compactness peak. -/
theorem einastoMetric_strictAnti_left (d l a : ℝ) :
    StrictAntiOn (fun t => einastoMetric d l a (exp t)) (Iic (einastoBalanceZeroLogRadius 0 l a)) := by
  intro x hx y hy hxy
  have h := einastoLogCompactness_strictMono_left l a hx hy hxy
  simp only [einastoMetric_compactness]
  nlinarith [exp_pos d]

theorem einastoMetric_strictMono_right (d l a : ℝ) :
    StrictMonoOn (fun t => einastoMetric d l a (exp t)) (Ici (einastoBalanceZeroLogRadius 0 l a)) := by
  intro x hx y hy hxy
  have h := einastoLogCompactness_strictAnti_right l a hx hy hxy
  simp only [einastoMetric_compactness]
  nlinarith [exp_pos d]

/-- All radii have positive lapse exactly below the critical density. -/
theorem einastoMetric_positive_everywhere_iff (d l a : ℝ) :
    (∀ t, 0 < einastoMetric d l a (exp t)) ↔ d < einastoCriticalLogDensity l a := by
  have hc := einastoCriticalLogDensity_calibration l a
  have hp := einastoLogCompactness_pos l a (einastoBalanceZeroLogRadius 0 l a)
  constructor
  · intro h
    have hh := h (einastoBalanceZeroLogRadius 0 l a)
    rw [einastoMetric_compactness] at hh
    apply exp_lt_exp.mp
    exact (mul_lt_mul_iff_left₀ hp).mp (by linarith)
  · intro hd t
    rw [einastoMetric_compactness]
    have hs := mul_lt_mul_of_pos_right (exp_lt_exp.mpr hd) hp
    have hb := mul_le_mul_of_nonneg_left (einastoLogCompactness_le_peak l a t) (exp_pos d).le
    linarith

theorem einastoMetric_peak_profile (l a u : ℝ) :
    einastoMetric (einastoCriticalLogDensity l a + u) l a (exp (einastoBalanceZeroLogRadius 0 l a)) =
      1 - exp u := by
  rw [einastoMetric_compactness, exp_add]
  have hc := einastoCriticalLogDensity_calibration l a
  calc
    1 - exp (einastoCriticalLogDensity l a) * exp u *
        einastoLogCompactness l a (einastoBalanceZeroLogRadius 0 l a) =
      1 - exp u * (exp (einastoCriticalLogDensity l a) *
        einastoLogCompactness l a (einastoBalanceZeroLogRadius 0 l a)) := by ring
    _ = 1 - exp u := by rw [hc, mul_one]

/-- Above critical density there are exactly two positive-radius lapse zeros. -/
theorem einastoMetric_supercritical_exactly_two (l a v : ℝ) :
    ∃ inner outer : ℝ, inner < einastoBalanceZeroLogRadius 0 l a ∧
      einastoBalanceZeroLogRadius 0 l a < outer ∧
      ∀ t, einastoMetric (einastoCriticalLogDensity l a + exp v) l a (exp t) = 0 ↔
        t = inner ∨ t = outer := by
  let d := einastoCriticalLogDensity l a + exp v
  let z := einastoBalanceZeroLogRadius 0 l a
  let f := fun t => einastoMetric d l a (exp t)
  have hc : Continuous f := (einastoMetric_continuous d l a).comp continuous_exp
  have hz : f z < 0 := by
    change einastoMetric (einastoCriticalLogDensity l a + exp v) l a
      (exp (einastoBalanceZeroLogRadius 0 l a)) < 0
    rw [einastoMetric_peak_profile]
    have he : 1 < exp (exp v) := by simpa only [exp_zero] using exp_lt_exp.mpr (exp_pos v)
    linarith
  have hbot : Tendsto f atBot (𝓝 1) := by
    simpa only [Function.comp_def] using (einastoMetric_flat_core_limit d l a).comp tendsto_exp_atBot
  have htop : Tendsto f atTop (𝓝 1) := by
    simpa only [Function.comp_def] using (einastoMetric_asymptotically_flat d l a).comp tendsto_exp_atTop
  obtain ⟨L, hLp, hLz⟩ := ((hbot.eventually (eventually_gt_nhds zero_lt_one)).and
    (eventually_lt_atBot z)).exists
  obtain ⟨R, hRp, hzR⟩ := ((htop.eventually (eventually_gt_nhds zero_lt_one)).and
    (eventually_gt_atTop z)).exists
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' hLz.le hc.continuousOn
    (show (0 : ℝ) ∈ Icc (f z) (f L) from ⟨hz.le, hLp.le⟩)
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc hzR.le hc.continuousOn
    (show (0 : ℝ) ∈ Icc (f z) (f R) from ⟨hz.le, hRp.le⟩)
  have hsz : s < z := by
    by_contra h
    have he : s = z := le_antisymm hs.2 (not_lt.mp h)
    rw [he] at hfs
    rw [hfs] at hz
    exact lt_irrefl 0 hz
  have hzu : z < u := by
    by_contra h
    have he : u = z := le_antisymm (not_lt.mp h) hu.1
    rw [he] at hfu
    rw [hfu] at hz
    exact lt_irrefl 0 hz
  refine ⟨s, u, hsz, hzu, ?_⟩
  intro t
  change f t = 0 ↔ t = s ∨ t = u
  constructor
  · intro ht
    by_cases htz : t ≤ z
    · exact Or.inl ((einastoMetric_strictAnti_left d l a).injOn
        (mem_Iic.mpr htz) (mem_Iic.mpr hsz.le) (ht.trans hfs.symm))
    · exact Or.inr ((einastoMetric_strictMono_right d l a).injOn
        (mem_Ici.mpr (not_le.mp htz).le) (mem_Ici.mpr hzu.le) (ht.trans hfu.symm))
  · rintro (rfl | rfl)
    · exact hfs
    · exact hfu

/-- Complete zero/one/two horizon classification for every positive Einasto family. -/
theorem einastoMetric_horizon_classification (d l a : ℝ) :
    (d < einastoCriticalLogDensity l a ∧ ∀ t, 0 < einastoMetric d l a (exp t)) ∨
    (d = einastoCriticalLogDensity l a ∧ ∀ t, einastoMetric d l a (exp t) = 0 ↔
      t = einastoBalanceZeroLogRadius 0 l a) ∨
    (einastoCriticalLogDensity l a < d ∧ ∃ inner outer : ℝ,
      inner < einastoBalanceZeroLogRadius 0 l a ∧ einastoBalanceZeroLogRadius 0 l a < outer ∧
      ∀ t, einastoMetric d l a (exp t) = 0 ↔ t = inner ∨ t = outer) := by
  rcases lt_trichotomy d (einastoCriticalLogDensity l a) with hd | hd | hd
  · exact Or.inl ⟨hd, (einastoMetric_positive_everywhere_iff d l a).mpr hd⟩
  · right; left
    refine ⟨hd, ?_⟩
    rw [hd]
    exact einastoMetric_critical_zero_iff l a
  · right; right
    refine ⟨hd, ?_⟩
    have he : einastoCriticalLogDensity l a + exp (log (d - einastoCriticalLogDensity l a)) = d := by
      rw [exp_log (sub_pos.mpr hd)]
      ring
    simpa only [he] using einastoMetric_supercritical_exactly_two l a (log (d - einastoCriticalLogDensity l a))

/-- The actual logarithmic lapse derivative, expressed through horizon balance. -/
theorem einastoMetric_log_derivative (d l a t : ℝ) :
    HasDerivAt (fun s => einastoMetric d l a (exp s))
      (-exp d * (2 * einastoHorizonBalance 0 l a (exp t) / exp t)) t := by
  have he : (fun s => einastoMetric d l a (exp s)) =
      (fun s => 1 - exp d * einastoLogCompactness l a s) := funext (einastoMetric_compactness d l a)
  rw [he]
  exact (((einastoLogCompactness_derivative l a t).const_mul (exp d)).const_sub 1).congr_deriv (by ring)

/-- The critical horizon has zero actual radial first derivative. -/
theorem einastoMetric_critical_stationary (l a : ℝ) :
    HasDerivAt (einastoMetric (einastoCriticalLogDensity l a) l a) 0
      (exp (einastoBalanceZeroLogRadius 0 l a)) := by
  let d := einastoCriticalLogDensity l a
  let z := einastoBalanceZeroLogRadius 0 l a
  have hlog := einastoMetric_log_derivative d l a z
  have hq : einastoHorizonBalance 0 l a (exp z) = 0 := einastoBalanceZeroLogRadius_eq 0 l a
  rw [hq] at hlog
  simp only [mul_zero, zero_div] at hlog
  have hrad := einastoMetric_derivative d l a z
  have he := hlog.unique (hrad.comp z (hasDerivAt_exp z))
  apply hrad.congr_deriv
  have hp := exp_pos z
  nlinarith

/-- At the compactness peak, boundary density is exactly one third of mean enclosed density. -/
theorem einastoCore_at_compactness_peak (l a : ℝ) :
    einastoCore 0 l a (exp (einastoBalanceZeroLogRadius 0 l a)) =
      4 * Real.pi * einastoDensity 0 l a (exp (einastoBalanceZeroLogRadius 0 l a)) := by
  let z := einastoBalanceZeroLogRadius 0 l a
  have hq := einastoBalanceZeroLogRadius_eq 0 l a
  rw [einastoHorizonBalance, einastoMass_core] at hq
  have he : exp z ^ (3 : ℕ) * (4 * Real.pi * einastoDensity 0 l a (exp z) - einastoCore 0 l a (exp z)) = 0 := by
    dsimp [z]
    nlinarith [hq]
  have hr := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 3 (exp_ne_zero z))
  linarith

/-- The actual second radial derivative at the critical horizon is strictly positive. -/
theorem einastoMetric_critical_second_derivative_pos (l a : ℝ) :
    0 < deriv (deriv (einastoMetric (einastoCriticalLogDensity l a) l a))
      (exp (einastoBalanceZeroLogRadius 0 l a)) := by
  let d := einastoCriticalLogDensity l a
  let z := einastoBalanceZeroLogRadius 0 l a
  have hneg : deriv (einastoHorizonBalance 0 l a) (exp z) < 0 := by
    have h := (einastoHorizonBalance_derivative_neg_iff 0 l a
      (z - einastoBalanceCriticalLogRadius l a)).mpr
      (sub_pos.mpr (einastoBalanceZeroLogRadius_after_maximum 0 l a))
    rw [show einastoBalanceCriticalLogRadius l a + (z - einastoBalanceCriticalLogRadius l a) = z by ring] at h
    exact h
  have he : deriv (deriv (einastoMetric d l a)) (exp z) =
      -2 * exp d * deriv (einastoHorizonBalance 0 l a) (exp z) / exp z ^ (2 : ℕ) := by
    rw [(einastoMetric_second_derivative d l a z).deriv,
      einastoCore_amplitude, einastoCore_at_compactness_peak,
      einastoSlope, einastoDensity_amplitude d l a (exp z),
      (einastoHorizonBalance_derivative 0 l a z).deriv]
    dsimp only [z]
    field_simp
    ring
  rw [he]
  have hn : -2 * exp d < 0 := mul_neg_of_neg_of_pos (by norm_num) (exp_pos d)
  exact div_pos (mul_pos_of_neg_of_neg hn hneg) (sq_pos_of_pos (exp_pos z))

/-- Critical density gives a genuine nondegenerate quadratic horizon contact. -/
theorem einastoMetric_critical_quadratic_contact (l a : ℝ) :
    einastoMetric (einastoCriticalLogDensity l a) l a (exp (einastoBalanceZeroLogRadius 0 l a)) = 0 ∧
      deriv (einastoMetric (einastoCriticalLogDensity l a) l a)
        (exp (einastoBalanceZeroLogRadius 0 l a)) = 0 ∧
      0 < deriv (deriv (einastoMetric (einastoCriticalLogDensity l a) l a))
        (exp (einastoBalanceZeroLogRadius 0 l a)) := by
  exact ⟨einastoMetric_critical_peak l a, (einastoMetric_critical_stationary l a).deriv,
    einastoMetric_critical_second_derivative_pos l a⟩

end GaloisForLFunctions.HTGeometry
