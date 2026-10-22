import GaloisForLFunctions.RHTower.PrimeCountingLiLandau
import GaloisForLFunctions.RHTower.LittlewoodOmega
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompressionRHCriterion

/-!
# Littlewood's theorem: `π(x) > li(x)` infinitely often

Partial summation gives, for `x ≥ 2`,

```text
π(x) - li(x) = 2/log 2 + (θ(x) - x)/log x + ∫_2^x (θ(t) - t)/(t log²t) dt,
```

with `li(x) = ∫_2^x dt/log t`.  In the variable `t = e^s` the integral is `∫ (θ(e^s) - e^s)/s² ds`.
Under the Riemann hypothesis the primitive `D(s) = ∫_0^s (e^r - ψ(e^r)) dr` is `O(e^{s/2})`, so
integration by parts against `1/s²` together with `0 ≤ ψ - θ ≤ C√x` bounds the integral below by
`-O(√x/log²x) - O(1)`; at Littlewood's points `ψ(x) - x > c√x logloglog x` this leaves
`π(x) - li(x) > (c/2)√x logloglog x/log x`.  If the Riemann hypothesis fails, Landau's theorem
(`riemannHypothesis_of_primeCounting_le_logIntegral_add_sqrt`) gives `π(x) > li(x) + √x`
infinitely often.  Either way `π(x) - li(x)` exceeds `(c/2)√x logloglog x/log x` infinitely often.
-/

open Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Partial summation -/

theorem continuousOn_inv_log_sq_uIcc {x : ℝ} (hx : 2 ≤ x) :
    ContinuousOn (fun t : ℝ => 1 / Real.log t ^ 2) (uIcc 2 x) := by
  rw [uIcc_of_le hx]
  refine continuousOn_const.div ((Real.continuousOn_log.mono ?_).pow 2) ?_
  · intro t ht; simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]
  · intro t ht
    exact pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'

/-- `li(x) = x/log x - 2/log 2 + ∫_2^x dt/log²t`. -/
theorem integral_inv_log_eq (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, 1 / Real.log t
      = x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hpos : ∀ t ∈ uIcc (2 : ℝ) x, 0 < Real.log t := fun t ht => by
    rw [uIcc_of_le hx] at ht; exact Real.log_pos (by linarith [ht.1])
  have hu : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt (fun t => 1 / Real.log t)
      (-(1 / (t * Real.log t ^ 2))) t := by
    intro t ht
    have ht0 : t ≠ 0 := by
      rw [uIcc_of_le hx] at ht; linarith [ht.1]
    have h := (Real.hasDerivAt_log ht0).inv (hpos t ht).ne'
    simp only [one_div]
    refine h.congr_deriv ?_
    rw [mul_inv, div_eq_mul_inv]
    ring
  have hv : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt (fun t : ℝ => t) 1 t := fun t _ => hasDerivAt_id t
  have hcont : ContinuousOn (fun t : ℝ => -(1 / (t * Real.log t ^ 2))) (uIcc 2 x) := by
    refine (continuousOn_const.div (continuousOn_id.mul
      ((Real.continuousOn_log.mono ?_).pow 2)) ?_).neg
    · intro t ht; rw [uIcc_of_le hx] at ht
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [ht.1]
    · intro t ht
      have h1 := hpos t ht
      have ht0 : 0 < t := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
      exact mul_ne_zero ht0.ne' (pow_ne_zero 2 h1.ne')
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    hcont.intervalIntegrable (continuousOn_const.intervalIntegrable)
  simp only [mul_one] at hparts
  rw [hparts]
  have hcongr : ∫ t in (2 : ℝ)..x, -(1 / (t * Real.log t ^ 2)) * t
      = -∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht0 : t ≠ 0 := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
    field_simp
  rw [hcongr]
  ring

/-- **Partial summation for `π - li`.** -/
theorem primeCounting_sub_logIntegral_eq {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t
      = 2 / Real.log 2 + (Chebyshev.theta x - x) / Real.log x
        + ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
  have hθ : IntervalIntegrable (fun t => Chebyshev.theta t / (t * Real.log t ^ 2)) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  have hl : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
    (continuousOn_inv_log_sq_uIcc hx).intervalIntegrable
  have hsplit : ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)
      = (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2))
        - ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    rw [← intervalIntegral.integral_sub hθ hl]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht0 : t ≠ 0 := by rw [uIcc_of_le hx] at ht; linarith [ht.1]
    have hl0 : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 (Real.log_pos (by
      rw [uIcc_of_le hx] at ht; linarith [ht.1])).ne'
    field_simp
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx, integral_inv_log_eq x hx, hsplit]
  ring

/-- The error integral in the logarithmic variable. -/
theorem integral_theta_sub_eq_log_variable {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)
      = ∫ s in (Real.log 2)..(Real.log x),
          (Chebyshev.theta (Real.exp s) - Real.exp s) / s ^ 2 := by
  have hl : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  rw [intervalIntegral.integral_of_le hx, intervalIntegral.integral_of_le hl,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
  have himg : Icc (2 : ℝ) x = Real.exp '' Icc (Real.log 2) (Real.log x) := by
    rw [Real.image_exp_Icc, Real.exp_log (by norm_num), Real.exp_log (by linarith)]
  rw [himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun s _ => (Real.hasDerivAt_exp s).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [abs_of_pos (Real.exp_pos s), smul_eq_mul, Real.log_exp]
  have he := (Real.exp_pos s).ne'
  field_simp

/-! ## Integration by parts against the deficit primitive -/

theorem intervalIntegrable_chebyshevDeficit (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.exp t - Chebyshev.psi (Real.exp t)) volume a b :=
  (Real.continuous_exp.intervalIntegrable a b).sub
    ((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable)

theorem continuousOn_inv_pow_uIcc {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) (k : ℕ) :
    ContinuousOn (fun s : ℝ => (s ^ k)⁻¹) (uIcc a T) := by
  rw [uIcc_of_le haT]
  exact (continuousOn_id.pow k).inv₀ fun s hs => pow_ne_zero k (lt_of_lt_of_le ha hs.1).ne'

/-- `∫_a^T f/s² = P(T)/T² + 2∫_a^T P/s³` with `P(s) = ∫_a^s f`, `f(r) = e^r - ψ(e^r)`. -/
theorem integral_chebyshevDeficit_div_sq_eq {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) :
    ∫ s in a..T, (s ^ 2)⁻¹ * (Real.exp s - Chebyshev.psi (Real.exp s))
      = (T ^ 2)⁻¹ * (∫ r in a..T, Real.exp r - Chebyshev.psi (Real.exp r))
        + ∫ s in a..T, 2 * (s ^ 3)⁻¹
          * ∫ r in a..s, Real.exp r - Chebyshev.psi (Real.exp r) := by
  set f : ℝ → ℝ := fun r => Real.exp r - Chebyshev.psi (Real.exp r) with hf
  set P : ℝ → ℝ := fun s => ∫ r in a..s, f r with hP
  set E : ℝ → ℝ := fun s => (s ^ 2)⁻¹ with hE
  have hi : IntervalIntegrable f volume a T := intervalIntegrable_chebyshevDeficit a T
  have hPac : AbsolutelyContinuousOnInterval P a T :=
    hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hEcd : ContDiffOn ℝ 1 E (uIcc a T) := by
    rw [uIcc_of_le haT]
    exact (contDiffOn_id.pow 2).inv fun s hs => pow_ne_zero 2 (by simp; linarith [hs.1])
  have hEac : AbsolutelyContinuousOnInterval E a T := hEcd.absolutelyContinuousOnInterval
  have hparts := hEac.integral_mul_deriv_eq_deriv_mul hPac
  have hleft : (∫ s in a..T, E s * deriv P s) = ∫ s in a..T, E s * f s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hi.ae_hasDerivAt_integral] with s hs hmem
    have hd : HasDerivAt P (f s) s := hs (uIoc_subset_uIcc hmem) a left_mem_uIcc
    rw [hd.deriv]
  have hright : (∫ s in a..T, deriv E s * P s) = ∫ s in a..T, -(2 * (s ^ 3)⁻¹ * P s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le haT] at hs
    have hs0 : s ≠ 0 := by linarith [hs.1]
    have hd : HasDerivAt E (-(2 * (s ^ 3)⁻¹)) s := by
      have h := (hasDerivAt_pow 2 s).inv (pow_ne_zero 2 hs0)
      refine h.congr_deriv ?_
      norm_num
      field_simp
    rw [hd.deriv]
    ring
  have hPa : P a = 0 := by simp [hP]
  rw [hleft, hright, hPa, mul_zero, sub_zero, intervalIntegral.integral_neg] at hparts
  rw [hparts]
  ring

/-- A primitive bound `|D(t)| ≤ B e^{t/2}` bounds every `∫_a^s f` by `2B e^{s/2}`. -/
theorem abs_integral_chebyshevDeficit_le {B a s : ℝ} (ha : 0 ≤ a) (has : a ≤ s)
    (hB : ∀ t : ℝ, 0 ≤ t → |ccmLogChebyshevDeficitPrimitive t| ≤ B * Real.exp (t / 2)) :
    |∫ r in a..s, Real.exp r - Chebyshev.psi (Real.exp r)| ≤ 2 * B * Real.exp (s / 2) := by
  have hsplit : ∫ r in a..s, Real.exp r - Chebyshev.psi (Real.exp r)
      = ccmLogChebyshevDeficitPrimitive s - ccmLogChebyshevDeficitPrimitive a := by
    unfold ccmLogChebyshevDeficitPrimitive
    rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_chebyshevDeficit 0 s)
      (intervalIntegrable_chebyshevDeficit 0 a)]
  have h1 := hB s (le_trans ha has)
  have h2 := hB a ha
  have h3 : Real.exp (a / 2) ≤ Real.exp (s / 2) := Real.exp_le_exp.mpr (by linarith)
  have hB0 : 0 ≤ B := by
    have := (abs_nonneg _).trans h2
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  rw [hsplit]
  calc |ccmLogChebyshevDeficitPrimitive s - ccmLogChebyshevDeficitPrimitive a|
      ≤ |ccmLogChebyshevDeficitPrimitive s| + |ccmLogChebyshevDeficitPrimitive a| := abs_sub _ _
    _ ≤ B * Real.exp (s / 2) + B * Real.exp (a / 2) := add_le_add h1 h2
    _ ≤ 2 * B * Real.exp (s / 2) := by nlinarith

/-! ## The weight integral -/

/-- `∫_8^T e^{s/2}/s² ds ≤ 4 e^{T/2}/T²`. -/
theorem integral_exp_half_div_sq_le {T : ℝ} (hT : 8 ≤ T) :
    ∫ s in (8 : ℝ)..T, Real.exp (s / 2) / s ^ 2 ≤ 4 * (Real.exp (T / 2) / T ^ 2) := by
  set h' : ℝ → ℝ := fun s => Real.exp (s / 2) / (2 * s ^ 2) - 2 * Real.exp (s / 2) / s ^ 3
    with hh'
  have hpos : ∀ s ∈ uIcc (8 : ℝ) T, 0 < s := fun s hs => by
    rw [uIcc_of_le hT] at hs; linarith [hs.1]
  have hd : ∀ s ∈ uIcc (8 : ℝ) T, HasDerivAt (fun s => Real.exp (s / 2) / s ^ 2) (h' s) s := by
    intro s hs
    have hs0 := (hpos s hs).ne'
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (s / 2) * (1 / 2)) s := by
      have := ((hasDerivAt_id s).div_const 2).exp
      simpa using this
    have h := h1.div (hasDerivAt_pow 2 s) (pow_ne_zero 2 hs0)
    refine h.congr_deriv ?_
    rw [hh']
    norm_num
    field_simp
  have hcont : ContinuousOn h' (uIcc 8 T) := by
    rw [hh']
    refine ContinuousOn.sub ?_ ?_
    · exact (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.div
        (continuousOn_const.mul (continuousOn_id.pow 2))
        fun s hs => by have := hpos s hs; positivity
    · exact (continuous_const.mul (Real.continuous_exp.comp
        (continuous_id.div_const 2))).continuousOn.div (continuousOn_id.pow 3)
        fun s hs => by have := hpos s hs; positivity
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  have hcont2 : ContinuousOn (fun s : ℝ => Real.exp (s / 2) / s ^ 2) (uIcc 8 T) :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.div
      (continuousOn_id.pow 2) fun s hs => by have := hpos s hs; positivity
  have hmono : ∫ s in (8 : ℝ)..T, Real.exp (s / 2) / s ^ 2 ≤ ∫ s in (8 : ℝ)..T, 4 * h' s := by
    refine intervalIntegral.integral_mono_on hT hcont2.intervalIntegrable
      (hcont.intervalIntegrable.const_mul 4) fun s hs => ?_
    have hs8 : 8 ≤ s := hs.1
    have hs0 : 0 < s := by linarith
    have hE := Real.exp_pos (s / 2)
    rw [hh']
    rw [show 4 * (Real.exp (s / 2) / (2 * s ^ 2) - 2 * Real.exp (s / 2) / s ^ 3)
      = Real.exp (s / 2) / s ^ 2 + (Real.exp (s / 2) / s ^ 3) * (s - 8) by
        field_simp; ring]
    have : 0 ≤ (Real.exp (s / 2) / s ^ 3) * (s - 8) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  rw [intervalIntegral.integral_const_mul, hFTC] at hmono
  have h8 : 0 ≤ Real.exp (8 / 2) / (8 : ℝ) ^ 2 := by positivity
  linarith


/-! ## The lower bound for the error integral under a primitive bound -/

theorem continuousOn_exp_half_div_sq {a T : ℝ} (ha : 0 < a) (haT : a ≤ T) :
    ContinuousOn (fun s : ℝ => Real.exp (s / 2) / s ^ 2) (uIcc a T) := by
  rw [uIcc_of_le haT]
  exact (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.div
    (continuousOn_id.pow 2) fun s hs => pow_ne_zero 2 (lt_of_lt_of_le ha hs.1).ne'

/-- With `|D(t)| ≤ B e^{t/2}` and `ψ - θ ≤ C√x`, the error integral is at least
`-2B e^{T/2}/T² - (4B/a + C) ∫_a^T e^{s/2}/s² ds`. -/
theorem integral_theta_sub_div_sq_ge {B C a T : ℝ} (ha : 0 < a) (haT : a ≤ T)
    (hB : ∀ t : ℝ, 0 ≤ t → |ccmLogChebyshevDeficitPrimitive t| ≤ B * Real.exp (t / 2))
    (hC : ∀ x : ℝ, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x) :
    -(2 * B * (Real.exp (T / 2) / T ^ 2))
        - (4 * B / a + C) * ∫ s in a..T, Real.exp (s / 2) / s ^ 2
      ≤ ∫ s in a..T, (Chebyshev.theta (Real.exp s) - Real.exp s) / s ^ 2 := by
  have hT0 : 0 < T := lt_of_lt_of_le ha haT
  have hB0 : 0 ≤ B := by
    have := (abs_nonneg _).trans (hB 0 le_rfl)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  set f : ℝ → ℝ := fun r => Real.exp r - Chebyshev.psi (Real.exp r) with hf
  set P : ℝ → ℝ := fun s => ∫ r in a..s, f r with hP
  set p : ℝ → ℝ := fun s => Chebyshev.psi (Real.exp s) - Chebyshev.theta (Real.exp s) with hp
  have hPc : Continuous P :=
    intervalIntegral.continuous_primitive (fun u v => intervalIntegrable_chebyshevDeficit u v) a
  have hPb : ∀ s ∈ Icc a T, P s ≤ 2 * B * Real.exp (s / 2) := fun s hs =>
    (le_abs_self _).trans (abs_integral_chebyshevDeficit_le ha.le hs.1 hB)
  have hinv2 := continuousOn_inv_pow_uIcc ha haT 2
  have hinv3 := continuousOn_inv_pow_uIcc ha haT 3
  have hW := continuousOn_exp_half_div_sq ha haT
  have hfi : IntervalIntegrable (fun s => (s ^ 2)⁻¹ * f s) volume a T :=
    (intervalIntegrable_chebyshevDeficit a T).continuousOn_mul hinv2
  have hpi : IntervalIntegrable (fun s => p s * (s ^ 2)⁻¹) volume a T :=
    (((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable).sub
      ((Chebyshev.theta_mono.comp Real.exp_monotone).intervalIntegrable)).mul_continuousOn hinv2
  have hPi : IntervalIntegrable (fun s => 2 * (s ^ 3)⁻¹ * P s) volume a T :=
    ((continuousOn_const.mul hinv3).mul hPc.continuousOn).intervalIntegrable
  -- the integrand splits
  have hsplit : ∫ s in a..T, (Chebyshev.theta (Real.exp s) - Real.exp s) / s ^ 2
      = -(∫ s in a..T, (s ^ 2)⁻¹ * f s) - ∫ s in a..T, p s * (s ^ 2)⁻¹ := by
    have hfin : IntervalIntegrable (fun s => -((s ^ 2)⁻¹ * f s)) volume a T := hfi.neg
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_sub hfin hpi]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hf, hp]
    rw [div_eq_mul_inv]
    ring
  have hparts := integral_chebyshevDeficit_div_sq_eq ha haT
  -- the boundary term
  have hbd : (T ^ 2)⁻¹ * P T ≤ 2 * B * (Real.exp (T / 2) / T ^ 2) := by
    have := mul_le_mul_of_nonneg_left (hPb T ⟨haT, le_rfl⟩) (inv_nonneg.mpr (sq_nonneg T))
    rw [div_eq_mul_inv]
    linarith
  -- the interior term
  have hint : ∫ s in a..T, 2 * (s ^ 3)⁻¹ * P s
      ≤ ∫ s in a..T, 4 * B / a * (Real.exp (s / 2) / s ^ 2) := by
    refine intervalIntegral.integral_mono_on haT hPi
      ((hW.intervalIntegrable).const_mul _) fun s hs => ?_
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have h1 : 2 * (s ^ 3)⁻¹ * P s ≤ 2 * (s ^ 3)⁻¹ * (2 * B * Real.exp (s / 2)) :=
      mul_le_mul_of_nonneg_left (hPb s hs) (by positivity)
    have h2 : 2 * (s ^ 3)⁻¹ * (2 * B * Real.exp (s / 2))
        = 4 * B * Real.exp (s / 2) / s ^ 2 * (1 / s) := by
      field_simp
      ring
    have h3 : 1 / s ≤ 1 / a := one_div_le_one_div_of_le ha hs.1
    have h4 : 0 ≤ 4 * B * Real.exp (s / 2) / s ^ 2 := by positivity
    have h5 : 4 * B * Real.exp (s / 2) / s ^ 2 * (1 / s)
        ≤ 4 * B * Real.exp (s / 2) / s ^ 2 * (1 / a) :=
      mul_le_mul_of_nonneg_left h3 h4
    have h6 : 4 * B * Real.exp (s / 2) / s ^ 2 * (1 / a)
        = 4 * B / a * (Real.exp (s / 2) / s ^ 2) := by
      field_simp
    linarith
  -- the prime-power term
  have hpp : ∫ s in a..T, p s * (s ^ 2)⁻¹ ≤ ∫ s in a..T, C * (Real.exp (s / 2) / s ^ 2) := by
    refine intervalIntegral.integral_mono_on haT hpi ((hW.intervalIntegrable).const_mul _)
      fun s hs => ?_
    have hs0 : 0 < s := lt_of_lt_of_le ha hs.1
    have h1 := hC (Real.exp s)
    rw [sqrt_exp_eq_exp_half_mul] at h1
    have h2 : Real.exp (1 / 2 * s) = Real.exp (s / 2) := by ring_nf
    rw [h2] at h1
    rw [mul_div_assoc', div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  rw [intervalIntegral.integral_const_mul] at hint hpp
  rw [hsplit, hparts]
  have hexp : (4 * B / a + C) * ∫ s in a..T, Real.exp (s / 2) / s ^ 2
      = 4 * B / a * (∫ s in a..T, Real.exp (s / 2) / s ^ 2)
        + C * ∫ s in a..T, Real.exp (s / 2) / s ^ 2 := by ring
  linarith

/-! ## The Riemann-hypothesis branch -/

/-- **Under the Riemann hypothesis, `π - li` is bounded below by the Chebyshev error.**  There are
constants `C, K₁, K₂` with
`π(x) - li(x) ≥ (ψ(x) - x)/log x - C√x/log x - K₁√x/log²x - K₂` for `x ≥ e⁸`. -/
theorem exists_primeCounting_sub_logIntegral_ge_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ C K₁ K₂ : ℝ, 0 ≤ C ∧ 0 ≤ K₁ ∧ ∀ x : ℝ, Real.exp 8 ≤ x →
      (Chebyshev.psi x - x) / Real.log x - C * Real.sqrt x / Real.log x
          - K₁ * Real.sqrt x / Real.log x ^ 2 - K₂
        ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t := by
  obtain ⟨B, hB0, hB⟩ := riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound.mp hRH
  obtain ⟨C₀, hC₀⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  set C : ℝ := |C₀| with hCdef
  have hC0 : 0 ≤ C := abs_nonneg _
  have hC : ∀ x : ℝ, Chebyshev.psi x - Chebyshev.theta x ≤ C * Real.sqrt x := fun x =>
    (hC₀ x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
  set a : ℝ := Real.log 2 with ha
  have ha0 : 0 < a := Real.log_pos (by norm_num)
  have ha8 : a ≤ 8 := by have := Real.log_two_lt_d9; linarith
  set W₈ : ℝ := ∫ s in a..8, Real.exp (s / 2) / s ^ 2 with hW₈
  refine ⟨C, 2 * B + 4 * (4 * B / a + C), (4 * B / a + C) * W₈, hC0, by positivity,
    fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx
  have hx2 : 2 ≤ x := by
    have := Real.add_one_le_exp 8; linarith
  set T : ℝ := Real.log x with hT
  have hT8 : 8 ≤ T := by rw [hT, Real.le_log_iff_exp_le hx0]; exact hx
  have hT0 : 0 < T := by linarith
  have haT : a ≤ T := le_trans ha8 hT8
  have hsq : Real.exp (T / 2) = Real.sqrt x := by
    rw [← Real.exp_log hx0, sqrt_exp_eq_exp_half_mul, ← hT]; ring_nf
  -- partial summation and the change of variables
  rw [primeCounting_sub_logIntegral_eq hx2, integral_theta_sub_eq_log_variable hx2]
  have hJ := integral_theta_sub_div_sq_ge ha0 haT hB hC
  have hsplitW : ∫ s in a..T, Real.exp (s / 2) / s ^ 2
      = W₈ + ∫ s in (8 : ℝ)..T, Real.exp (s / 2) / s ^ 2 := by
    rw [hW₈, intervalIntegral.integral_add_adjacent_intervals
      ((continuousOn_exp_half_div_sq ha0 ha8).intervalIntegrable)
      ((continuousOn_exp_half_div_sq (by norm_num) hT8).intervalIntegrable)]
  have hW8T := integral_exp_half_div_sq_le hT8
  have hcoef : 0 ≤ 4 * B / a + C := by positivity
  have hJ' : -(2 * B * (Real.exp (T / 2) / T ^ 2)) - (4 * B / a + C) * (W₈
      + 4 * (Real.exp (T / 2) / T ^ 2))
      ≤ ∫ s in a..T, (Chebyshev.theta (Real.exp s) - Real.exp s) / s ^ 2 := by
    rw [hsplitW] at hJ
    have := mul_le_mul_of_nonneg_left (add_le_add_left hW8T W₈) hcoef
    linarith
  -- the boundary term
  have hθ : (Chebyshev.psi x - x) / T - C * Real.sqrt x / T ≤ (Chebyshev.theta x - x) / T := by
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith [hC x]) hT0.le
  have h2 : 0 ≤ 2 / Real.log 2 := div_nonneg (by norm_num) ha0.le
  rw [hsq] at hJ'
  have hK : (2 * B + 4 * (4 * B / a + C)) * Real.sqrt x / T ^ 2
      = 2 * B * (Real.sqrt x / T ^ 2) + (4 * B / a + C) * (4 * (Real.sqrt x / T ^ 2)) := by
    ring
  rw [hK]
  nlinarith


theorem tendsto_logLogLog_atTop :
    Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)

/-- `log x ≤ ε √x` for all large `x`. -/
theorem eventually_log_le_mul_sqrt {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ ε * Real.sqrt x := by
  filter_upwards [(isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound hε,
    eventually_ge_atTop (1 : ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hx
  exact hx

/-- **Littlewood's theorem for `π - li`, Riemann-hypothesis branch.** -/
theorem frequently_logIntegral_add_lt_primeCounting_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ᶠ x : ℝ in atTop, (∫ t in (2 : ℝ)..x, 1 / Real.log t)
        + littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x
      < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  obtain ⟨C, K₁, K₂, hC0, hK₁, hbound⟩ :=
    exists_primeCounting_sub_logIntegral_ge_of_riemannHypothesis hRH
  set c : ℝ := littlewoodConst / 14 with hc
  have hc0 : 0 < c := by rw [hc]; have := littlewoodConst_pos; positivity
  have hev := ((eventually_ge_atTop (Real.exp 8)).and
    (eventually_log_le_mul_sqrt (by positivity : (0 : ℝ) < 1 / (|K₂| + 1)))).and
    (tendsto_logLogLog_atTop.eventually_ge_atTop ((C + K₁ + 1) / (c / 2)))
  refine ((frequently_littlewood_lt_chebyshevError_of_riemannHypothesis hRH).and_eventually
    hev).mono ?_
  rintro x ⟨hlw, ⟨hx8, hlog⟩, hL3⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 8) hx8
  have hlx : 8 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact hx8
  have hlx0 : 0 < Real.log x := by linarith
  have hb := hbound x hx8
  set L := Real.log x with hL
  set u : ℝ := Real.sqrt x / L with hu
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hu0 : 0 < u := div_pos hsx hlx0
  set L3 := Real.log (Real.log (Real.log x)) with hL3def
  -- the Littlewood point
  have hψ : c * L3 * u < (Chebyshev.psi x - x) / L := by
    have : c * Real.sqrt x * L3 < Chebyshev.psi x - x := by
      simpa [chebyshevError, hc] using hlw
    rw [hu, lt_div_iff₀ hlx0]
    have : c * L3 * (Real.sqrt x / L) * L = c * Real.sqrt x * L3 := by field_simp
    linarith
  -- the error terms
  have hK₁u : K₁ * Real.sqrt x / L ^ 2 ≤ K₁ * u := by
    rw [hu, div_le_iff₀ (by positivity)]
    have : K₁ * (Real.sqrt x / L) * L ^ 2 = K₁ * Real.sqrt x * L := by field_simp
    rw [this]
    have : 0 ≤ K₁ * Real.sqrt x := mul_nonneg hK₁ hsx.le
    nlinarith
  have hK₂u : K₂ ≤ u := by
    have h1 : (|K₂| + 1) * L ≤ Real.sqrt x := by
      have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ |K₂| + 1)
      rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
      exact this
    rw [hu, le_div_iff₀ hlx0]
    nlinarith [le_abs_self K₂]
  have hCu : C * Real.sqrt x / L = C * u := by rw [hu]; ring
  have hL3' : C + K₁ + 1 ≤ c / 2 * L3 := by
    rw [div_le_iff₀ (by positivity)] at hL3
    linarith
  have hmain : c / 2 * L3 * u ≤ c * L3 * u - C * u - K₁ * u - u := by
    have : (C + K₁ + 1) * u ≤ c / 2 * L3 * u := mul_le_mul_of_nonneg_right hL3' hu0.le
    linarith
  have hgoal : littlewoodConst / 28 * Real.sqrt x * L3 / L = c / 2 * L3 * u := by
    rw [hu, hc]; field_simp; ring
  rw [hgoal]
  linarith

theorem littlewoodConst_le_one : littlewoodConst ≤ 1 := by
  unfold littlewoodConst
  rw [div_le_one (by positivity)]
  have : 1 ≤ Real.pi ^ 3 := one_le_pow₀ (by linarith [Real.pi_gt_three])
  linarith

/-- **Littlewood's theorem: `π(x) - li(x) > (c/2)√x logloglog x / log x` infinitely often**, with
`c = 1/(70π³)` and `li(x) = ∫_2^x dt/log t`. -/
theorem frequently_logIntegral_add_littlewood_lt_primeCounting :
    ∃ᶠ x : ℝ in atTop, (∫ t in (2 : ℝ)..x, 1 / Real.log t)
        + littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x
      < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  by_cases hRH : RiemannHypothesis
  · exact frequently_logIntegral_add_lt_primeCounting_of_riemannHypothesis hRH
  · have hfr : ∃ᶠ x : ℝ in atTop,
        (∫ t in (2 : ℝ)..x, 1 / Real.log t) + 1 * Real.sqrt x < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
      by_contra hno
      rw [Filter.not_frequently] at hno
      exact hRH (riemannHypothesis_of_primeCounting_le_logIntegral_add_sqrt
        (hno.mono fun x hx => not_lt.mp hx))
    have hev : ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ Real.log x :=
      Real.tendsto_log_atTop.eventually_ge_atTop _
    refine (hfr.and_eventually (hev.and (eventually_gt_atTop (1 : ℝ)))).mono ?_
    rintro x ⟨hx, hlx, hx1⟩
    have hlx0 : 0 < Real.log x := Real.log_pos hx1
    have hL3 := logLogLog_le_log hlx
    have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hc := littlewoodConst_le_one
    have hc0 := littlewoodConst_pos
    have hle : littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x)) / Real.log x
        ≤ 1 * Real.sqrt x := by
      rw [div_le_iff₀ hlx0]
      have h1 : littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x))
          ≤ littlewoodConst / 28 * Real.sqrt x * Real.log x :=
        mul_le_mul_of_nonneg_left hL3 (by positivity)
      have h2 : littlewoodConst / 28 * Real.sqrt x * Real.log x ≤ 1 * Real.sqrt x * Real.log x := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hsx) hlx0.le
        linarith
      linarith
    linarith

/-- **`π(x) > li(x) + B` infinitely often, for every constant `B`.**  With `B = li(2)` this is
Littlewood's sign change for the principal-value logarithmic integral. -/
theorem frequently_logIntegral_add_const_lt_primeCounting (B : ℝ) :
    ∃ᶠ x : ℝ in atTop, (∫ t in (2 : ℝ)..x, 1 / Real.log t) + B < (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hc0 : 0 < littlewoodConst / 28 := by have := littlewoodConst_pos; positivity
  set ε : ℝ := littlewoodConst / 28 / (|B| + 1) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  refine (frequently_logIntegral_add_littlewood_lt_primeCounting.and_eventually
    (((eventually_log_le_mul_sqrt hε0).and (eventually_gt_atTop (1 : ℝ))).and
      (tendsto_logLogLog_atTop.eventually_ge_atTop 1))).mono ?_
  rintro x ⟨hx, ⟨hlog, hx1⟩, hL3⟩
  have hlx0 : 0 < Real.log x := Real.log_pos hx1
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hge : B ≤ littlewoodConst / 28 * Real.sqrt x * Real.log (Real.log (Real.log x))
      / Real.log x := by
    rw [le_div_iff₀ hlx0]
    have h1 : littlewoodConst / 28 * Real.sqrt x ≤ littlewoodConst / 28 * Real.sqrt x
        * Real.log (Real.log (Real.log x)) := le_mul_of_one_le_right (by positivity) hL3
    have h2 : (|B| + 1) * Real.log x ≤ littlewoodConst / 28 * Real.sqrt x := by
      have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ |B| + 1)
      rw [hε, ← mul_assoc, mul_div_cancel₀ _ (by positivity : (|B| + 1) ≠ 0)] at this
      exact this
    nlinarith [le_abs_self B]
  linarith

end

end RHTower
