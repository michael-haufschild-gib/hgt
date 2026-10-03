import GaloisForLFunctions.RHTower.PrimeCountingLogIntegralExponentLaw
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.RHTower.GaussianLogFinitePart

/-!
# Landau's theorem for Mertens' prime-power sum

Let `A(x) = Σ_{n ≤ x} Λ(n)/(n log n)` (so `A(x) = Σ_{p^k ≤ x} 1/(k p^k)`), let
`Ein(t) = ∫_0^t (1 - e^{-u})/u du` and let `R(x) = A(x) - log log x - γ` be the Mertens error.
For real `s > 0`,

```text
∫_0^∞ A(e^t) e^{-st} dt = log ζ(1+s)/s,       ∫_0^∞ Ein(t) e^{-st} dt = log((1+s)/s)/s ,
```

so `∫_0^∞ (A(e^t) - Ein(t)) e^{-st} dt = log(s ζ(1+s)/(1+s))/s`, whose right side extends
analytically across `s = 0` (the logarithm vanishes there) and along `(-1, ∞)`.  Since
`Ein(t) = log t + γ + E₁(t)` with `0 ≤ E₁(t) ≤ e^{-t}` for `t ≥ 1`, Landau's theorem applied to
`K e^{(b-1)t} ± (Ein(t) - A(e^t)) + M e^{-t}` gives:

* a one-sided bound `±R(x) ≤ K x^{b-1}` (`0 < b ≤ 1`) excludes zeros of `ζ` from `Re s > b`;
* `R(x) = O(x^{-1/2})` from either side implies the Riemann hypothesis;
* `R(x) > x^{b-1}` and `R(x) < -x^{b-1}` infinitely often for every `b < Θ`, the supremum of the
  real parts of the zeros; in particular `R(x) = Ω±(x^{b-1})` for every `b < 1/2`.
-/

open MeasureTheory Set Filter Topology

open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## A general Laplace transform of a counting function -/

/-- `Σ_{1 ≤ n ≤ e^t} c_n` as a series of indicators. -/
theorem sum_Icc_floor_exp_eq_tsum (c : ℕ → ℝ) (hc0 : c 0 = 0) (t : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, c n
      = ∑' n : ℕ, c n * (Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) t := by
  classical
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp t⌋₊)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hle : (n : ℝ) ≤ Real.exp t := le_trans (by exact_mod_cast hn.2)
      (Nat.floor_le (Real.exp_pos t).le)
    have hlog : Real.log n ≤ t := by
      rw [Real.log_le_iff_le_exp (by linarith)]; exact hle
    rw [Set.indicator_of_mem (show t ∈ Ici (Real.log n) from hlog), mul_one]
  · intro n hn
    rw [Finset.mem_Icc, not_and_or] at hn
    rcases hn with h | h
    · have : n = 0 := by omega
      subst this
      simp [hc0]
    · have hn1 : 1 ≤ n := by
        by_contra h1
        have : n = 0 := by omega
        subst this; simp at h
      have hgt : Real.exp t < n := by
        by_contra hle
        exact h (Nat.le_floor (le_of_not_gt hle))
      have hlog : t < Real.log n := by
        rw [Real.lt_log_iff_exp_lt (by exact_mod_cast hn1)]; exact hgt
      rw [Set.indicator_of_notMem (show t ∉ Ici (Real.log n) from fun h' => by
        simp only [Set.mem_Ici] at h'; linarith), mul_zero]

/-- **Laplace transform of a nonnegative counting function.**  If `c_n ≥ 0`, `c_0 = 0` and
`Σ c_n n^{-σ}` converges (`σ > 0`), then `∫_0^∞ (Σ_{n ≤ e^t} c_n) e^{-σt} dt = (Σ c_n n^{-σ})/σ`. -/
theorem integral_sum_Icc_floor_exp_mul {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (hc0 : c 0 = 0) {σ : ℝ}
    (hσ : 0 < σ) (hs : Summable fun n : ℕ => c n * (n : ℝ) ^ (-σ)) :
    ∫ t in Ioi (0 : ℝ), (∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, c n) * Real.exp (-σ * t)
      = (∑' n : ℕ, c n * (n : ℝ) ^ (-σ)) / σ := by
  set F : ℕ → ℝ → ℝ := fun n t =>
    c n * ((Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) t * Real.exp (-σ * t)) with hF
  have hpt : ∀ t, (∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, c n) * Real.exp (-σ * t) = ∑' n, F n t := by
    intro t
    rw [sum_Icc_floor_exp_eq_tsum c hc0, ← tsum_mul_right]
    congr 1; funext n; rw [hF]; ring
  have hFint : ∀ n, ∫ t in Ioi (0 : ℝ), F n t = c n * ((n : ℝ) ^ (-σ) / σ) := by
    intro n
    rw [hF, integral_const_mul]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hc0]
    · rw [integral_Ioi_indicator_log_mul_exp hσ hn]
  have hFnn : ∀ n t, 0 ≤ F n t := by
    intro n t; rw [hF]
    exact mul_nonneg (hc n) (mul_nonneg
      (Set.indicator_nonneg (fun _ _ => zero_le_one) t) (Real.exp_pos _).le)
  have hFintegrable : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    have hexp : IntegrableOn (fun t => Real.exp (-σ * t)) (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    refine (hexp.const_mul (c n)).mono' ?_ ?_
    · rw [hF]
      exact (measurable_const.mul ((measurable_const.indicator measurableSet_Ici).mul
        (Real.measurable_exp.comp (measurable_const.mul measurable_id)))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n t), hF]
      have h1 : (Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) t ≤ 1 := by
        by_cases ht : t ∈ Ici (Real.log n)
        · rw [Set.indicator_of_mem ht]
        · rw [Set.indicator_of_notMem ht]; norm_num
      have h3 := Real.exp_pos (-σ * t)
      have h5 : (Ici (Real.log n)).indicator (fun _ => (1 : ℝ)) t * Real.exp (-σ * t)
          ≤ Real.exp (-σ * t) := by
        have := mul_le_mul_of_nonneg_right h1 h3.le
        linarith
      exact mul_le_mul_of_nonneg_left h5 (hc n)
  have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    have heq : ∀ n, ∫ t in Ioi (0 : ℝ), ‖F n t‖ = c n * ((n : ℝ) ^ (-σ) / σ) := by
      intro n
      rw [← hFint n]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hFnn n t)]
    simp_rw [heq]
    refine (hs.div_const σ).congr fun n => ?_
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpt t),
    ← integral_tsum_of_summable_integral_norm hFintegrable hsum]
  simp_rw [hFint]
  rw [← tsum_div_const]
  congr 1; funext n; ring

/-! ## Mertens' prime-power sum -/

/-- `A(x) = Σ_{1 ≤ n ≤ x} Λ(n)/(n log n)`. -/
def mertensPowerSum (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, eulerLogCoeffReal n / n

theorem mertensPowerSum_nonneg (x : ℝ) : 0 ≤ mertensPowerSum x :=
  Finset.sum_nonneg fun n _ => div_nonneg (eulerLogCoeffReal_nonneg n) (Nat.cast_nonneg n)

theorem mertensPowerSum_mono : Monotone mertensPowerSum := by
  intro x y hxy
  unfold mertensPowerSum
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.floor_le_floor hxy))
    (fun n _ _ => div_nonneg (eulerLogCoeffReal_nonneg n) (Nat.cast_nonneg n))

theorem summable_eulerLogCoeffReal_div_rpow {σ : ℝ} (hσ : 0 < σ) :
    Summable fun n : ℕ => eulerLogCoeffReal n / n * (n : ℝ) ^ (-σ) := by
  have hrp : Summable fun n : ℕ => (n : ℝ) ^ (-(1 + σ)) := by
    have := Real.summable_nat_rpow_inv.mpr (show 1 < 1 + σ by linarith)
    refine this.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (div_nonneg (eulerLogCoeffReal_nonneg n)
    (Nat.cast_nonneg n)) (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (fun n => ?_) hrp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [eulerLogCoeffReal] using Real.rpow_nonneg (le_refl (0 : ℝ)) _
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 := eulerLogCoeffReal_le_one n
    have h2 := eulerLogCoeffReal_nonneg n
    have e : (n : ℝ) ^ (-(1 + σ)) = (n : ℝ)⁻¹ * (n : ℝ) ^ (-σ) := by
      rw [show -(1 + σ) = -1 + -σ by ring, Real.rpow_add hn0, Real.rpow_neg_one]
    rw [e, div_eq_mul_inv]
    have hp : 0 ≤ (n : ℝ)⁻¹ * (n : ℝ) ^ (-σ) := by positivity
    calc eulerLogCoeffReal n * (n : ℝ)⁻¹ * (n : ℝ) ^ (-σ)
        = eulerLogCoeffReal n * ((n : ℝ)⁻¹ * (n : ℝ) ^ (-σ)) := by ring
      _ ≤ 1 * ((n : ℝ)⁻¹ * (n : ℝ) ^ (-σ)) := mul_le_mul_of_nonneg_right h1 hp
      _ = (n : ℝ)⁻¹ * (n : ℝ) ^ (-σ) := one_mul _

theorem tsum_eulerLogCoeffReal_div_rpow_eq (σ : ℝ) :
    ∑' n : ℕ, eulerLogCoeffReal n / n * (n : ℝ) ^ (-σ)
      = ∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-(1 + σ)) := by
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerLogCoeffReal]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show -(1 + σ) = -1 + -σ by ring, Real.rpow_add hn0, Real.rpow_neg_one]
    ring

/-- **The Laplace transform of `A(e^t)`.**  `∫_0^∞ A(e^t) e^{-σt} dt = (Σ a_n n^{-1-σ})/σ`. -/
theorem integral_mertensPowerSum_exp_mul {σ : ℝ} (hσ : 0 < σ) :
    ∫ t in Ioi (0 : ℝ), mertensPowerSum (Real.exp t) * Real.exp (-σ * t)
      = (∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-(1 + σ))) / σ := by
  have h := integral_sum_Icc_floor_exp_mul (c := fun n => eulerLogCoeffReal n / n)
    (fun n => div_nonneg (eulerLogCoeffReal_nonneg n) (Nat.cast_nonneg n)) (by simp) hσ
    (summable_eulerLogCoeffReal_div_rpow hσ)
  rw [tsum_eulerLogCoeffReal_div_rpow_eq σ] at h
  exact h


/-! ## The comparison function `Ein` -/

/-- The kernel `(1 - e^{-u})/u = e^{-u} (e^u - 1)/u`, continuous with value `1` at `0`. -/
def einKernel (u : ℝ) : ℝ := Real.exp (-u) * logIntegralKernel u

theorem continuous_einKernel : Continuous einKernel :=
  (Real.continuous_exp.comp continuous_neg).mul continuous_logIntegralKernel

theorem einKernel_pos (u : ℝ) : 0 < einKernel u :=
  mul_pos (Real.exp_pos _) (logIntegralKernel_pos u)

theorem einKernel_of_pos {u : ℝ} (hu : 0 < u) : einKernel u = (1 - Real.exp (-u)) / u := by
  rw [einKernel, logIntegralKernel_of_ne hu.ne']
  have e : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  field_simp
  linarith

theorem einKernel_le_one {u : ℝ} (hu : 0 ≤ u) : einKernel u ≤ 1 := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · rw [einKernel, logIntegralKernel_zero]; simp
  · rw [einKernel_of_pos hu, div_le_one hu]
    linarith [Real.add_one_le_exp (-u)]

/-- `Ein(t) = ∫_0^t (1 - e^{-u})/u du`. -/
def einCompare (t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t, einKernel u

theorem hasDerivAt_einCompare (t : ℝ) : HasDerivAt einCompare (einKernel t) t :=
  intervalIntegral.integral_hasDerivAt_right (continuous_einKernel.intervalIntegrable _ _)
    (continuous_einKernel.stronglyMeasurableAtFilter _ _) continuous_einKernel.continuousAt

theorem continuous_einCompare : Continuous einCompare :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_einCompare t).continuousAt

theorem einCompare_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ einCompare t :=
  intervalIntegral.integral_nonneg ht fun u _ => (einKernel_pos u).le

theorem einCompare_le_self {t : ℝ} (ht : 0 ≤ t) : einCompare t ≤ t := by
  have h := intervalIntegral.integral_mono_on ht (continuous_einKernel.intervalIntegrable 0 t)
    (intervalIntegrable_const (μ := volume) (c := (1 : ℝ))) fun u hu => einKernel_le_one hu.1
  simpa [einCompare] using h

theorem einCompare_eq_ein {t : ℝ} (ht : 0 ≤ t) : einCompare t = ein t := by
  unfold einCompare ein
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u hu => ?_)
  rw [Set.uIoc_of_le ht] at hu
  rw [einKernel_of_pos hu.1, einProfile, if_neg hu.1.ne']

/-- `Ein(t) = γ + log t + E₁(t)` with `0 ≤ E₁(t) ≤ e^{-t}` for `t ≥ 1`. -/
theorem einCompare_sub_log_mem {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ einCompare t - Real.log t - Real.eulerMascheroniConstant ∧
      einCompare t - Real.log t - Real.eulerMascheroniConstant ≤ Real.exp (-t) := by
  have ht0 : 0 < t := by linarith
  rw [einCompare_eq_ein ht0.le, ein_eq_eulerMascheroni_add_log_add_tail ht]
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-u) / u) (Ioi t) :=
    integrableOn_exp_neg_div_Ioi_one.mono_set (Ioi_subset_Ioi ht)
  have hnn : 0 ≤ ∫ u in Ioi t, Real.exp (-u) / u :=
    setIntegral_nonneg measurableSet_Ioi fun u hu =>
      div_nonneg (Real.exp_pos _).le (lt_trans ht0 hu).le
  have hle : ∫ u in Ioi t, Real.exp (-u) / u ≤ ∫ u in Ioi t, Real.exp (-1 * u) := by
    refine setIntegral_mono_on hint (exp_neg_integrableOn_Ioi t one_pos) measurableSet_Ioi
      fun u hu => ?_
    have hu1 : 1 ≤ u := le_trans ht (le_of_lt hu)
    rw [div_le_iff₀ (by linarith), neg_one_mul]
    nlinarith [Real.exp_pos (-u)]
  have hval : ∫ u in Ioi t, Real.exp (-1 * u) = Real.exp (-t) := by
    rw [integral_exp_mul_Ioi (by norm_num) t]
    simp
  refine ⟨by linarith, by linarith⟩

/-- `t e^{-st} ≤ (2/s) e^{-(s/2)t}`. -/
theorem mul_exp_neg_mul_le_two_div {s t : ℝ} (hs : 0 < s) :
    t * Real.exp (-s * t) ≤ 2 / s * Real.exp (-(s / 2) * t) := by
  have h1 := Real.add_one_le_exp (s / 2 * t)
  have h2 : Real.exp (s / 2 * t) * Real.exp (-s * t) = Real.exp (-(s / 2) * t) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : t ≤ 2 / s * Real.exp (s / 2 * t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hs]; nlinarith
  calc t * Real.exp (-s * t) ≤ 2 / s * Real.exp (s / 2 * t) * Real.exp (-s * t) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = 2 / s * Real.exp (-(s / 2) * t) := by rw [mul_assoc, h2]

/-- **Frullani for `Ein`.**  `∫_0^∞ (1 - e^{-u})/u · e^{-su} du = log((s + 1)/s)`, `s > 0`. -/
theorem integral_einKernel_mul_exp {s : ℝ} (hs : 0 < s) :
    ∫ u in Ioi (0 : ℝ), einKernel u * Real.exp (-s * u) = Real.log ((s + 1) / s) := by
  have h := integral_logIntegralKernel_mul_exp (σ := s + 1) (by linarith)
  rw [show s + 1 - 1 = s by ring] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [einKernel, show Real.exp (-(s + 1) * u) = Real.exp (-u) * Real.exp (-s * u) by
    rw [← Real.exp_add]; ring_nf]
  ring

/-- **The Laplace transform of `Ein`.**  `∫_0^∞ Ein(t) e^{-st} dt = log((s + 1)/s)/s`, `s > 0`. -/
theorem integral_einCompare_mul_exp {s : ℝ} (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), einCompare t * Real.exp (-s * t) = Real.log ((s + 1) / s) / s := by
  have hdom : IntegrableOn (fun t => 2 / s * Real.exp (-(s / 2) * t)) (Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith : 0 < s / 2)).const_mul _
  have hL : IntegrableOn (fun t => einCompare t * Real.exp (-s * t)) (Ioi (0 : ℝ)) := by
    refine hdom.mono' ((continuous_einCompare.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (einCompare_nonneg (le_of_lt ht))
      (Real.exp_pos _).le)]
    exact le_trans (mul_le_mul_of_nonneg_right (einCompare_le_self (le_of_lt ht))
      (Real.exp_pos _).le) (mul_exp_neg_mul_le_two_div hs)
  have hK : IntegrableOn (fun t => einKernel t * Real.exp (-s * t)) (Ioi (0 : ℝ)) := by
    refine (exp_neg_integrableOn_Ioi 0 hs).mono' ((continuous_einKernel.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (einKernel_pos t).le (Real.exp_pos _).le)]
    have := mul_le_mul_of_nonneg_right (einKernel_le_one (le_of_lt ht))
      (Real.exp_pos (-s * t)).le
    linarith
  set G : ℝ → ℝ := fun t => -(einCompare t * Real.exp (-s * t) / s) with hG
  have hGd : ∀ t, HasDerivAt G (einCompare t * Real.exp (-s * t)
      - einKernel t * Real.exp (-s * t) / s) t := by
    intro t
    have he : HasDerivAt (fun y => Real.exp (-s * y)) (Real.exp (-s * t) * (-s)) t := by
      have := ((hasDerivAt_id t).const_mul (-s)).exp
      simpa using this
    have h2 := (((hasDerivAt_einCompare t).mul he).div_const s).neg
    refine h2.congr_deriv ?_
    field_simp
    ring
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => 2 / s * Real.exp (-(s / 2) * t) / s) atTop (𝓝 0) := by
      have := ((Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (by linarith : -(s / 2) < 0))).const_mul (2 / s)).div_const s
      simpa using this
    refine squeeze_zero_norm' ?_ h1
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hG, norm_neg, Real.norm_eq_abs, abs_div, abs_of_pos hs,
      abs_of_nonneg (mul_nonneg (einCompare_nonneg ht) (Real.exp_pos _).le)]
    exact div_le_div_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_right (einCompare_le_self ht)
      (Real.exp_pos _).le) (mul_exp_neg_mul_le_two_div hs)) hs.le
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto (f := G) (a := 0)
    (hGd 0).continuousAt.continuousWithinAt (fun t _ => hGd t) (hL.sub (hK.div_const s)) hlim
  have hG0 : G 0 = 0 := by
    rw [hG]; simp [einCompare]
  rw [hG0, sub_zero, integral_sub hL (hK.div_const s), integral_div,
    integral_einKernel_mul_exp hs] at hibp
  linarith


/-! ## The Landau measure -/

theorem mertensPowerSum_le_self {x : ℝ} (hx : 0 ≤ x) : mertensPowerSum x ≤ x := by
  unfold mertensPowerSum
  calc ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, eulerLogCoeffReal n / n ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        rw [div_le_one (by linarith)]
        linarith [eulerLogCoeffReal_le_one n]
    _ = ⌊x⌋₊ := by simp
    _ ≤ x := Nat.floor_le hx

/-- The clipped density `K e^{(b-1)t} + ε(Ein(t) - A(e^t)) + M e^{-t}`. -/
def mertensLandauDensity (b K M ε : ℝ) (t : ℝ) : NNReal :=
  Real.toNNReal (K * Real.exp ((b - 1) * t) + ε * (einCompare t - mertensPowerSum (Real.exp t))
    + M * Real.exp (-t))

theorem measurable_mertensLandauDensity (b K M ε : ℝ) :
    Measurable (mertensLandauDensity b K M ε) := by
  unfold mertensLandauDensity
  refine Measurable.real_toNNReal ?_
  refine Measurable.add ?_ (measurable_const.mul (Real.measurable_exp.comp measurable_neg))
  refine Measurable.add (measurable_const.mul (Real.measurable_exp.comp
    (measurable_const.mul measurable_id))) (measurable_const.mul ?_)
  exact continuous_einCompare.measurable.sub
    (mertensPowerSum_mono.measurable.comp Real.measurable_exp)

/-- `g dt + e^{(b-1)t} dt` on `(0, ∞)`. -/
def mertensLandauMeasure (b K M ε : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (mertensLandauDensity b K M ε u : ENNReal))
    + (volume.restrict (Ioi (0:ℝ))).withDensity (fun u => (growthShiftDensity (b - 1) u : ENNReal))

theorem mertensLandauDensity_le {b K M ε : ℝ} (hb : b ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hε : ε = 1 ∨ ε = -1) {t : ℝ} (ht : 0 < t) :
    ((mertensLandauDensity b K M ε t : ℝ)) ≤ (K + M + 2) * Real.exp t := by
  unfold mertensLandauDensity
  rw [Real.coe_toNNReal']
  have h1 : Real.exp ((b - 1) * t) ≤ Real.exp t := Real.exp_le_exp.mpr (by nlinarith)
  have h1' : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.mpr (by linarith)
  have h2 := einCompare_nonneg ht.le
  have h2' := einCompare_le_self ht.le
  have h3 := mertensPowerSum_nonneg (Real.exp t)
  have h3' := mertensPowerSum_le_self (Real.exp_pos t).le
  have h4 : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have hE := Real.exp_pos t
  have hK' : K * Real.exp ((b - 1) * t) ≤ K * Real.exp t := mul_le_mul_of_nonneg_left h1 hK
  have hM' : M * Real.exp (-t) ≤ M * Real.exp t := mul_le_mul_of_nonneg_left h1' hM
  refine max_le ?_ (by positivity)
  rcases hε with rfl | rfl <;> nlinarith

theorem laplaceMass_mertensLandau_density_ne_top {b K M ε σ : ℝ} (hb : b ≤ 1) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hε : ε = 1 ∨ ε = -1) (hσ : 1 < σ) :
    laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
      (fun u => (mertensLandauDensity b K M ε u : ENNReal))) σ ≠ ⊤ := by
  unfold laplaceMass
  have hg : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (-σ * u))) := by measurability
  rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_self, lintegral_withDensity_eq_lintegral_mul _
      (measurable_mertensLandauDensity b K M ε).coe_nnreal_ennreal hg]
  refine ne_top_of_le_ne_top
    (integrableOn_exp_majorant (C := K + M + 2) hσ).lintegral_lt_top.ne ?_
  refine lintegral_mono_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (mertensLandauDensity_le hb hK hM hε hu) (Real.exp_pos _).le

theorem laplaceMass_mertensLandau_eq (b K M ε σ : ℝ) :
    laplaceMass (mertensLandauMeasure b K M ε) σ =
      laplaceMass ((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (mertensLandauDensity b K M ε u : ENNReal))) σ
        + laplaceMass volume (σ - (b - 1)) := by
  unfold laplaceMass mertensLandauMeasure
  rw [Measure.restrict_add, lintegral_add_measure]
  congr 1
  have := laplaceMass_growthShift (b - 1) σ
  unfold laplaceMass at this
  exact this

theorem laplaceMass_mertensLandau_two_ne_top {b K M ε : ℝ} (hb : b ≤ 1) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hε : ε = 1 ∨ ε = -1) :
    laplaceMass (mertensLandauMeasure b K M ε) 2 ≠ ⊤ := by
  rw [laplaceMass_mertensLandau_eq]
  exact ENNReal.add_ne_top.mpr ⟨laplaceMass_mertensLandau_density_ne_top hb hK hM hε
    (by norm_num), laplaceMass_volume_ne_top (by linarith)⟩

theorem laplaceMass_mertensLandau_eq_top {b K M ε σ : ℝ} (hσ : σ ≤ b - 1) :
    laplaceMass (mertensLandauMeasure b K M ε) σ = ⊤ := by
  rw [laplaceMass_mertensLandau_eq]
  rcases lt_or_eq_of_le hσ with h | h
  · rw [laplaceMass_volume_eq_top (by linarith), add_top]
  · rw [h, sub_self, laplaceMass_volume_zero_eq_top, add_top]

/-- The abscissa of `ν` lies in `[b - 1, 2]`. -/
theorem isAbscissa_mertensLandau {b K M ε : ℝ} (hb : b ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hε : ε = 1 ∨ ε = -1) :
    IsAbscissa (mertensLandauMeasure b K M ε)
        (sInf {σ : ℝ | laplaceMass (mertensLandauMeasure b K M ε) σ ≠ ⊤}) ∧
      b - 1 ≤ sInf {σ : ℝ | laplaceMass (mertensLandauMeasure b K M ε) σ ≠ ⊤} ∧
      sInf {σ : ℝ | laplaceMass (mertensLandauMeasure b K M ε) σ ≠ ⊤} ≤ 2 := by
  set S := {σ : ℝ | laplaceMass (mertensLandauMeasure b K M ε) σ ≠ ⊤} with hS
  have hpos : ∀ σ ∈ S, b - 1 < σ := by
    intro σ hσ
    by_contra hle
    exact hσ (laplaceMass_mertensLandau_eq_top (not_lt.mp hle))
  have hbdd : BddBelow S := ⟨b - 1, fun σ hσ => (hpos σ hσ).le⟩
  have h2S : (2:ℝ) ∈ S := laplaceMass_mertensLandau_two_ne_top hb hK hM hε
  have hne : S.Nonempty := ⟨2, h2S⟩
  refine ⟨⟨fun σ hσ => ?_, fun σ hσ => ?_⟩, le_csInf hne fun σ hσ => (hpos σ hσ).le,
    csInf_le hbdd h2S⟩
  · obtain ⟨σ', hσ'S, hlt⟩ := exists_lt_of_csInf_lt hne hσ
    exact ne_top_of_le_ne_top hσ'S (laplaceMass_antitone _ hlt.le)
  · by_contra h
    exact absurd (csInf_le hbdd (show σ ∈ S from h)) (not_le.mpr hσ)

/-! ## The real transform for `σ > 1` -/

theorem integrableOn_mertensPowerSum_exp_mul {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ => mertensPowerSum (Real.exp t) * Real.exp (-σ * t)) (Ioi 0) := by
  refine (integrableOn_exp_majorant (C := 1) hσ).mono' ?_ ?_
  · exact ((mertensPowerSum_mono.measurable.comp Real.measurable_exp).mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mertensPowerSum_nonneg _)
      (Real.exp_pos _).le), one_mul]
    exact mul_le_mul_of_nonneg_right (mertensPowerSum_le_self (Real.exp_pos t).le)
      (Real.exp_pos _).le

theorem integrableOn_einCompare_mul_exp {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ => einCompare t * Real.exp (-σ * t)) (Ioi 0) := by
  refine (integrableOn_exp_majorant (C := 1) hσ).mono' ?_ ?_
  · exact (continuous_einCompare.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (einCompare_nonneg (le_of_lt ht))
      (Real.exp_pos _).le), one_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    linarith [einCompare_le_self (le_of_lt ht), Real.add_one_le_exp t]

/-- Under positivity of the density, the real transform of `ν` for `σ > 1`. -/
theorem laplaceReal_mertensLandau_eq {b K M ε : ℝ} (hb : b ≤ 1) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hε : ε = 1 ∨ ε = -1)
    (hg : ∀ t, 0 < t → 0 ≤ K * Real.exp ((b - 1) * t)
      + ε * (einCompare t - mertensPowerSum (Real.exp t)) + M * Real.exp (-t))
    {σ : ℝ} (hσ : 1 < σ) :
    laplaceReal (mertensLandauMeasure b K M ε) σ = (K + 1) / (σ - (b - 1)) + M / (σ + 1)
      + ε * (Real.log ((σ + 1) / σ)
        - ∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-(1 + σ))) / σ := by
  have hσ0 : 0 < σ := by linarith
  have hσa : 0 < σ - (b - 1) := by linarith
  have hσ1 : 0 < σ + 1 := by linarith
  have hexpInt : ∀ c : ℝ, 0 < c → IntegrableOn (fun u : ℝ => Real.exp (-c * u)) (Ioi 0) :=
    fun c hc => exp_neg_integrableOn_Ioi 0 hc
  have hI1 : Integrable (fun u : ℝ => Real.exp (-σ * u))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (mertensLandauDensity b K M ε u : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul
        (measurable_mertensLandauDensity b K M ε)]
    refine (integrableOn_exp_majorant (C := K + M + 2) hσ).mono' ?_ ?_
    · exact ((measurable_mertensLandauDensity b K M ε).coe_nnreal_real.aestronglyMeasurable.smul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
      rw [NNReal.smul_def, smul_eq_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (NNReal.coe_nonneg _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (mertensLandauDensity_le hb hK hM hε hu)
        (Real.exp_pos _).le
  have hI2 : Integrable (fun u : ℝ => Real.exp (-σ * u))
      (((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (growthShiftDensity (b - 1) u : ENNReal))).restrict (Ioi 0)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integrable_withDensity_iff_integrable_smul (measurable_growthShiftDensity _)]
    refine (hexpInt (σ - (b - 1)) hσa).congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [NNReal.smul_def, smul_eq_mul, growthShiftDensity_coe, ← Real.exp_add]
    ring_nf
  unfold laplaceReal mertensLandauMeasure
  rw [Measure.restrict_add, integral_add_measure hI1 hI2]
  have hshift : ∫ u in Ioi (0:ℝ), Real.exp (-σ * u)
      ∂((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (growthShiftDensity (b - 1) u : ENNReal))) = 1 / (σ - (b - 1)) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul (measurable_growthShiftDensity _)]
    rw [← integral_Ioi_exp_neg_mul_eq_one_div hσa]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [NNReal.smul_def, smul_eq_mul, growthShiftDensity_coe, ← Real.exp_add]
    ring_nf
  have hdens : ∫ u in Ioi (0:ℝ), Real.exp (-σ * u)
      ∂((volume.restrict (Ioi (0:ℝ))).withDensity
        (fun u => (mertensLandauDensity b K M ε u : ENNReal)))
      = K / (σ - (b - 1)) + ε * (Real.log ((σ + 1) / σ) / σ
        - (∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-(1 + σ))) / σ) + M / (σ + 1) := by
    rw [restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_self, integral_withDensity_eq_integral_smul (measurable_mertensLandauDensity b K M ε)]
    have hpt : ∀ u ∈ Ioi (0:ℝ), mertensLandauDensity b K M ε u • Real.exp (-σ * u)
        = (K * Real.exp (-(σ - (b - 1)) * u) + ε * (einCompare u * Real.exp (-σ * u)
          - mertensPowerSum (Real.exp u) * Real.exp (-σ * u)))
          + M * Real.exp (-(σ + 1) * u) := by
      intro u hu
      rw [NNReal.smul_def, smul_eq_mul]
      unfold mertensLandauDensity
      rw [Real.coe_toNNReal _ (hg u hu)]
      rw [show Real.exp (-(σ - (b - 1)) * u) = Real.exp ((b - 1) * u) * Real.exp (-σ * u) by
        rw [← Real.exp_add]; ring_nf]
      rw [show Real.exp (-(σ + 1) * u) = Real.exp (-u) * Real.exp (-σ * u) by
        rw [← Real.exp_add]; ring_nf]
      ring
    have i1 : IntegrableOn (fun u => K * Real.exp (-(σ - (b - 1)) * u)) (Ioi 0) :=
      (hexpInt _ hσa).const_mul K
    have i2 := integrableOn_einCompare_mul_exp hσ
    have i3 := integrableOn_mertensPowerSum_exp_mul hσ
    have i4 : IntegrableOn (fun u => M * Real.exp (-(σ + 1) * u)) (Ioi 0) :=
      (hexpInt _ hσ1).const_mul M
    have i23 : IntegrableOn (fun u => ε * (einCompare u * Real.exp (-σ * u)
        - mertensPowerSum (Real.exp u) * Real.exp (-σ * u))) (Ioi 0) := (i2.sub i3).const_mul ε
    have i123 : IntegrableOn (fun u => K * Real.exp (-(σ - (b - 1)) * u)
        + ε * (einCompare u * Real.exp (-σ * u)
          - mertensPowerSum (Real.exp u) * Real.exp (-σ * u))) (Ioi 0) := i1.add i23
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add i123 i4, integral_add i1 i23,
      integral_const_mul, integral_const_mul, integral_sub i2 i3, integral_const_mul,
      integral_Ioi_exp_neg_mul_eq_one_div hσa, integral_Ioi_exp_neg_mul_eq_one_div hσ1,
      integral_einCompare_mul_exp hσ0, integral_mertensPowerSum_exp_mul hσ0]
    ring
  rw [hdens, hshift]
  ring


/-! ## The continuation and Landau's theorem -/

/-- A difference quotient of a function analytic at both points is analytic. -/
theorem analyticAt_dslope_of_analyticAt_of_analyticAt {f : ℂ → ℂ} {z₀ z : ℂ}
    (h₀ : AnalyticAt ℂ f z₀) (h : AnalyticAt ℂ f z) : AnalyticAt ℂ (dslope f z₀) z := by
  by_cases hz : z = z₀
  · subst hz
    obtain ⟨p, hp⟩ := h₀
    exact hp.has_fpower_series_dslope_fslope.analyticAt
  · have heq : (fun w => (w - z₀)⁻¹ * (f w - f z₀)) =ᶠ[𝓝 z] dslope f z₀ := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      rw [dslope_of_ne _ hw, slope_def_field, div_eq_inv_mul]
    exact (((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hz)).mul
      (h.sub analyticAt_const)).congr heq

/-- `g(z) = log((z ζ(1 + z))/(1 + z))`, the logarithm of `ZRU(1 + z)/(1 + z)`. -/
def mertensLandauLog (z : ℂ) : ℂ := Complex.log (zetaResidueUnit (1 + z) / (1 + z))

theorem mertensLandauLog_zero : mertensLandauLog 0 = 0 := by
  simp [mertensLandauLog]

theorem analyticAt_mertensLandauLog {z : ℂ} (hz : 1 + z ≠ 0)
    (hslit : zetaResidueUnit (1 + z) / (1 + z) ∈ Complex.slitPlane) :
    AnalyticAt ℂ mertensLandauLog z := by
  unfold mertensLandauLog
  have h1 : AnalyticAt ℂ (fun w : ℂ => 1 + w) z := analyticAt_const.add analyticAt_id
  exact (((analyticAt_zetaResidueUnit (1 + z)).comp h1).div h1 hz).clog hslit

theorem mertensLandau_slit_ofReal {t : ℝ} (ht : -1 < t) :
    zetaResidueUnit (1 + (t : ℂ)) / (1 + (t : ℂ)) ∈ Complex.slitPlane := by
  have h := zetaResidueUnit_div_mem_slitPlane (t := 1 + t) (by linarith)
  push_cast at h
  exact h

theorem analyticAt_mertensLandauLog_ofReal {t : ℝ} (ht : -1 < t) :
    AnalyticAt ℂ mertensLandauLog (t : ℂ) :=
  analyticAt_mertensLandauLog (by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith) (mertensLandau_slit_ofReal ht)

theorem mertensLandauLog_ofReal {σ : ℝ} (hσ : 0 < σ) :
    mertensLandauLog (σ : ℂ) = (((∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-(1 + σ)))
      - Real.log ((σ + 1) / σ) : ℝ) : ℂ) := by
  have h := log_zetaResidueUnit_div_ofReal (σ := σ + 1) (by linarith)
  rw [show σ + 1 - 1 = σ by ring, show -(σ + 1) = -(1 + σ) by ring] at h
  unfold mertensLandauLog
  rw [show (1 : ℂ) + σ = ((σ + 1 : ℝ) : ℂ) by push_cast; ring, h]

/-- `Φ(z) = (K+1)/(z-(b-1)) + M/(z+1) - ε g(z)/z`, with the removable singularity at `0` filled. -/
def mertensLandauContinuation (b K M ε : ℝ) (z : ℂ) : ℂ :=
  (K + 1) / (z - (b - 1)) + M / (z + 1) - ε * dslope mertensLandauLog 0 z

theorem analyticAt_mertensLandauContinuation (b K M ε : ℝ) {z : ℂ} (hzb : z - (b - 1) ≠ 0)
    (hz1 : z + 1 ≠ 0) (hg : AnalyticAt ℂ mertensLandauLog z) :
    AnalyticAt ℂ (mertensLandauContinuation b K M ε) z := by
  unfold mertensLandauContinuation
  have h0 : AnalyticAt ℂ mertensLandauLog 0 := by
    simpa using analyticAt_mertensLandauLog_ofReal (t := 0) (by norm_num)
  refine ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) hzb).add
    (analyticAt_const.div (analyticAt_id.add analyticAt_const) hz1)).sub ?_
  exact analyticAt_const.mul (analyticAt_dslope_of_analyticAt_of_analyticAt h0 hg)

theorem mertensLandauContinuation_ofReal {b K M ε σ : ℝ} (hσ : 0 < σ) :
    mertensLandauContinuation b K M ε (σ : ℂ) = (((K + 1) / (σ - (b - 1)) + M / (σ + 1)
      + ε * (Real.log ((σ + 1) / σ)
        - ∑' n : ℕ, eulerLogCoeffReal n * (n : ℝ) ^ (-(1 + σ))) / σ : ℝ) : ℂ) := by
  unfold mertensLandauContinuation
  have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
  rw [dslope_of_ne _ hσ0, slope_def_field, mertensLandauLog_zero, mertensLandauLog_ofReal hσ]
  push_cast
  ring

theorem abscissa_mertensLandau_eq {b K M ε : ℝ} (hb0 : 0 < b) (hb : b ≤ 1) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hε : ε = 1 ∨ ε = -1)
    (hg : ∀ t, 0 < t → 0 ≤ K * Real.exp ((b - 1) * t)
      + ε * (einCompare t - mertensPowerSum (Real.exp t)) + M * Real.exp (-t)) :
    IsAbscissa (mertensLandauMeasure b K M ε) (b - 1) := by
  obtain ⟨hc, hac, hc2⟩ := isAbscissa_mertensLandau (K := K) (M := M) hb hK hM hε
  set c : ℝ := sInf {σ : ℝ | laplaceMass (mertensLandauMeasure b K M ε) σ ≠ ⊤} with hcdef
  rcases hac.lt_or_eq with hpos | hzero
  · exfalso
    have hc1 : -1 < c := by linarith
    have hcb : (c : ℂ) - (b - 1) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hcm : (c : ℂ) + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hc1' : (1 : ℂ) + c ≠ 0 := by rw [add_comm]; exact hcm
    have hcont : ContinuousAt (fun z => zetaResidueUnit (1 + z) / (1 + z)) (c : ℂ) :=
      ((analyticAt_zetaResidueUnit _).continuousAt.comp
        (continuous_const.add continuous_id).continuousAt).div
        (continuous_const.add continuous_id).continuousAt hc1'
    have hev : ∀ᶠ z in 𝓝 (c : ℂ), zetaResidueUnit (1 + z) / (1 + z) ∈ Complex.slitPlane ∧
        1 + z ≠ 0 ∧ z - (b - 1) ≠ 0 ∧ z + 1 ≠ 0 :=
      (hcont.eventually (Complex.isOpen_slitPlane.mem_nhds (mertensLandau_slit_ofReal hc1))).and
        (((continuous_const.add continuous_id).continuousAt.eventually_ne hc1').and
          (((continuous_id.sub continuous_const).continuousAt.eventually_ne hcb).and
            ((continuous_id.add continuous_const).continuousAt.eventually_ne hcm)))
    obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine false_of_analyticAt_abscissa hc hd (Φ := mertensLandauContinuation b K M ε) ?_ ?_
    · intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hball hz
      exact analyticAt_mertensLandauContinuation b K M ε h3 h4
        (analyticAt_mertensLandauLog h2 h1)
    · intro σ hσc _
      have hV : IsOpen {z : ℂ | c < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hTdiff : DifferentiableOn ℂ (complexLaplace (mertensLandauMeasure b K M ε))
          {z : ℂ | c < z.re} :=
        fun z hz => (hasDerivAt_complexLaplace hc hz).differentiableAt.differentiableWithinAt
      have hT : AnalyticOnNhd ℝ
          (fun t : ℝ => complexLaplace (mertensLandauMeasure b K M ε) (t : ℂ)) (Ioi c) := by
        intro t ht
        have h1 : AnalyticAt ℂ (complexLaplace (mertensLandauMeasure b K M ε)) (t : ℂ) :=
          hTdiff.analyticAt (hV.mem_nhds (by simpa using ht))
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have hH : AnalyticOnNhd ℝ (fun t : ℝ => mertensLandauContinuation b K M ε (t : ℂ))
          (Ioi c) := by
        intro t ht
        have htb : b - 1 < t := lt_trans hpos ht
        have ht1 : -1 < t := by linarith
        have h1 : AnalyticAt ℂ (mertensLandauContinuation b K M ε) (t : ℂ) := by
          refine analyticAt_mertensLandauContinuation b K M ε ?_ ?_
            (analyticAt_mertensLandauLog_ofReal ht1)
          · intro h; have := congrArg Complex.re h; simp at this; linarith
          · intro h; have := congrArg Complex.re h; simp at this; linarith
        exact h1.restrictScalars.comp (Complex.ofRealCLM.analyticAt t)
      have h3mem : (3 : ℝ) ∈ Ioi c := by show c < 3; linarith
      have hfg : (fun t : ℝ => complexLaplace (mertensLandauMeasure b K M ε) (t : ℂ)) =ᶠ[𝓝 (3:ℝ)]
          (fun t : ℝ => mertensLandauContinuation b K M ε (t : ℂ)) := by
        refine Filter.eventuallyEq_of_mem
          (Ioo_mem_nhds (by norm_num : (2 : ℝ) < 3) (by norm_num : (3:ℝ) < 4)) fun t ht => ?_
        have ht1 : 1 < t := by linarith [ht.1]
        show complexLaplace (mertensLandauMeasure b K M ε) (t : ℂ)
          = mertensLandauContinuation b K M ε (t : ℂ)
        rw [complexLaplace_ofReal, laplaceReal_mertensLandau_eq hb hK hM hε hg ht1,
          mertensLandauContinuation_ofReal (by linarith)]
      have heq := hT.eqOn_of_preconnected_of_eventuallyEq hH isPreconnected_Ioi h3mem hfg
      have hσ : complexLaplace (mertensLandauMeasure b K M ε) (σ : ℂ)
          = mertensLandauContinuation b K M ε (σ : ℂ) := heq (show σ ∈ Ioi c from hσc)
      rw [← hσ, complexLaplace_ofReal]
  · rw [← hzero] at hc
    exact hc

/-- **A positive Mertens density excludes zeros of `ζ` from `Re s > b`.** -/
theorem zetaResidueUnit_ne_zero_of_mertensLandau {b K M ε : ℝ} (hb0 : 0 < b) (hb : b ≤ 1)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hε : ε = 1 ∨ ε = -1)
    (hg : ∀ t, 0 < t → 0 ≤ K * Real.exp ((b - 1) * t)
      + ε * (einCompare t - mertensPowerSum (Real.exp t)) + M * Real.exp (-t))
    {z : ℂ} (hz : b < z.re) : zetaResidueUnit z ≠ 0 := by
  have hc := abscissa_mertensLandau_eq hb0 hb hK hM hε hg
  set U : Set ℂ := {w : ℂ | b - 1 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hne1 : ∀ w ∈ U, w + 1 ≠ 0 := fun w hw h => by
    have := congrArg Complex.re h; simp [hU] at this hw; linarith
  have hneb : ∀ w ∈ U, w - (b - 1) ≠ 0 := fun w hw h => by
    have := congrArg Complex.re h; simp [hU] at this hw; linarith
  set B : ℂ → ℂ := fun w => ε * w * ((K + 1) / (w - (b - 1)) + M / (w + 1)
    - complexLaplace (mertensLandauMeasure b K M ε) w) with hB
  have hBd : DifferentiableOn ℂ B U := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w : ℂ => ((K : ℂ) + 1) / (w - (b - 1))) w :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
        (hneb w hw)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => (M : ℂ) / (w + 1)) w :=
      (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _))
        (hne1 w hw)
    have h3 := (hasDerivAt_complexLaplace hc hw).differentiableAt
    have h4 : DifferentiableAt ℂ B w :=
      ((differentiableAt_const (ε : ℂ)).mul differentiableAt_id).mul ((h1.add h2).sub h3)
    exact h4.differentiableWithinAt
  have hF : AnalyticOnNhd ℂ (fun w => Complex.exp (B w) * (1 + w)) U :=
    ((hBd.cexp).mul (differentiableOn_const _ |>.add differentiableOn_id)).analyticOnNhd hUo
  have hG : AnalyticOnNhd ℂ (fun w => zetaResidueUnit (1 + w)) U := fun w _ =>
    (analyticAt_zetaResidueUnit _).comp (analyticAt_const.add analyticAt_id)
  have h2U : (2 : ℂ) ∈ U := by simp [hU]; linarith
  have hreal : ∀ t : ℝ, 1 < t → Complex.exp (B t) * (1 + t) = zetaResidueUnit (1 + t) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < t).ne'
    have hBt : B t = mertensLandauLog t := by
      simp only [hB]
      rw [complexLaplace_ofReal, laplaceReal_mertensLandau_eq hb hK hM hε hg ht,
        mertensLandauLog_ofReal (by linarith)]
      push_cast
      field_simp
      rcases hε with rfl | rfl <;> push_cast <;> ring
    have hslit := mertensLandau_slit_ofReal (t := t) (by linarith)
    rw [hBt, mertensLandauLog, Complex.exp_log (Complex.slitPlane_ne_zero hslit)]
    have h1t : (1 : ℂ) + t ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    field_simp
  have hfreq : ∃ᶠ w : ℂ in 𝓝[≠] ((2 : ℂ)),
      Complex.exp (B w) * (1 + w) = zetaResidueUnit (1 + w) := by
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (2 : ℝ),
        Complex.exp (B t) * (1 + t) = zetaResidueUnit (1 + t) := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds
        (show (2 : ℝ) ∈ Ioi (1 : ℝ) by norm_num))] with t ht
      exact hreal t ht
    have hcast : ((2 : ℂ)) = (((2 : ℝ)) : ℂ) := by norm_num
    rw [hcast]
    exact (tendsto_ofReal_nhdsNE 2).frequently hev.frequently
  have hEq := hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt (b - 1)).isPreconnected h2U hfreq
  have hzU : z - 1 ∈ U := by simp [hU]; linarith
  have := hEq hzU
  simp only [add_sub_cancel] at this
  rw [← this]
  exact mul_ne_zero (Complex.exp_ne_zero _) (by
    intro h; have := congrArg Complex.re h; simp at this; linarith)


/-! ## Receivers and oscillation of the Mertens error -/

/-- The Mertens error `R(x) = Σ_{n ≤ x} Λ(n)/(n log n) - log log x - γ`. -/
def mertensError (x : ℝ) : ℝ :=
  mertensPowerSum x - Real.log (Real.log x) - Real.eulerMascheroniConstant

theorem rpow_eq_exp_of_exp {t y : ℝ} : Real.exp t ^ y = Real.exp (y * t) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp, mul_comm]

/-- The threshold `T ≥ 1` with `e^T ≥ X`. -/
theorem exists_threshold_exp (X : ℝ) : ∃ T : ℝ, 1 ≤ T ∧ ∀ t, T ≤ t → X ≤ Real.exp t := by
  refine ⟨max (Real.log (max X 1)) 1, le_max_right _ _, fun t ht => ?_⟩
  have h1 : Real.log (max X 1) ≤ t := le_trans (le_max_left _ _) ht
  have h2 : max X 1 ≤ Real.exp t := by
    rw [← Real.exp_log (lt_of_lt_of_le one_pos (le_max_right X 1))]
    exact Real.exp_le_exp.mpr h1
  exact le_trans (le_max_left _ _) h2

/-- **Upper receiver.**  `R(x) ≤ K x^{b-1}` eventually (`0 < b ≤ 1`) clears `Re s > b`. -/
theorem zetaResidueUnit_ne_zero_of_mertensError_le {b K : ℝ} (hb0 : 0 < b) (hb : b ≤ 1)
    (h : ∀ᶠ x : ℝ in atTop, mertensError x ≤ K * x ^ (b - 1)) {z : ℂ} (hz : b < z.re) :
    zetaResidueUnit z ≠ 0 := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp h
  obtain ⟨T, hT1, hTX⟩ := exists_threshold_exp X
  set K' : ℝ := max K 0 with hK'
  set M : ℝ := mertensPowerSum (Real.exp T) * Real.exp T with hM
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hM0 : 0 ≤ M := mul_nonneg (mertensPowerSum_nonneg _) (Real.exp_pos _).le
  refine zetaResidueUnit_ne_zero_of_mertensLandau hb0 hb hK'0 hM0 (Or.inl rfl) ?_ hz
  intro t ht
  have hE := Real.exp_pos ((b - 1) * t)
  have hEt := Real.exp_pos (-t)
  have hKE : 0 ≤ K' * Real.exp ((b - 1) * t) := mul_nonneg hK'0 hE.le
  have hMt : 0 ≤ M * Real.exp (-t) := mul_nonneg hM0 hEt.le
  by_cases htT : T ≤ t
  · have hx := hX (Real.exp t) (hTX t htT)
    rw [mertensError, Real.log_exp, rpow_eq_exp_of_exp] at hx
    have hein := (einCompare_sub_log_mem (le_trans hT1 htT)).1
    have hKK : K * Real.exp ((b - 1) * t) ≤ K' * Real.exp ((b - 1) * t) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hE.le
    linarith
  · have htT' : t ≤ T := (not_le.mp htT).le
    have hA : mertensPowerSum (Real.exp t) ≤ mertensPowerSum (Real.exp T) :=
      mertensPowerSum_mono (Real.exp_le_exp.mpr htT')
    have hein := einCompare_nonneg ht.le
    have hexp : Real.exp T * Real.exp (-t) ≥ 1 := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have hMt' : mertensPowerSum (Real.exp T) ≤ M * Real.exp (-t) := by
      rw [hM, mul_assoc]
      have := mertensPowerSum_nonneg (Real.exp T)
      nlinarith
    linarith

/-- **Lower receiver.**  `R(x) ≥ -K x^{b-1}` eventually (`0 < b ≤ 1`) clears `Re s > b`. -/
theorem zetaResidueUnit_ne_zero_of_le_mertensError {b K : ℝ} (hb0 : 0 < b) (hb : b ≤ 1)
    (h : ∀ᶠ x : ℝ in atTop, -(K * x ^ (b - 1)) ≤ mertensError x) {z : ℂ} (hz : b < z.re) :
    zetaResidueUnit z ≠ 0 := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp h
  obtain ⟨T, hT1, hTX⟩ := exists_threshold_exp X
  set K' : ℝ := max K 0 + 1 with hK'
  set M : ℝ := T * Real.exp T with hM
  have hK'0 : 0 ≤ K' := by rw [hK']; positivity
  have hM0 : 0 ≤ M := mul_nonneg (by linarith) (Real.exp_pos _).le
  refine zetaResidueUnit_ne_zero_of_mertensLandau hb0 hb hK'0 hM0 (Or.inr rfl) ?_ hz
  intro t ht
  have hE := Real.exp_pos ((b - 1) * t)
  have hEt := Real.exp_pos (-t)
  have hKE : 0 ≤ K' * Real.exp ((b - 1) * t) := mul_nonneg hK'0 hE.le
  have hMt : 0 ≤ M * Real.exp (-t) := mul_nonneg hM0 hEt.le
  have hA := mertensPowerSum_nonneg (Real.exp t)
  by_cases htT : T ≤ t
  · have hx := hX (Real.exp t) (hTX t htT)
    rw [mertensError, Real.log_exp, rpow_eq_exp_of_exp] at hx
    have hein := (einCompare_sub_log_mem (le_trans hT1 htT)).2
    have hKK : K * Real.exp (t * (b - 1)) ≤ max K 0 * Real.exp (t * (b - 1)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    have hee : Real.exp (-t) ≤ Real.exp ((b - 1) * t) := Real.exp_le_exp.mpr (by nlinarith)
    rw [mul_comm t (b - 1)] at hKK
    have hsplit : K' * Real.exp ((b - 1) * t)
        = max K 0 * Real.exp ((b - 1) * t) + Real.exp ((b - 1) * t) := by rw [hK']; ring
    linarith
  · have htT' : t ≤ T := (not_le.mp htT).le
    have hein := einCompare_le_self ht.le
    have hexp : Real.exp T * Real.exp (-t) ≥ 1 := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have hMt' : T ≤ M * Real.exp (-t) := by
      rw [hM, mul_assoc]; nlinarith
    linarith

/-- **Mertens' theorem with a square-root error forces the Riemann hypothesis**, either side. -/
theorem riemannHypothesis_of_mertensError_le_sqrt {K : ℝ}
    (h : (∀ᶠ x : ℝ in atTop, mertensError x ≤ K * x ^ (-(1 / 2) : ℝ))
      ∨ ∀ᶠ x : ℝ in atTop, -(K * x ^ (-(1 / 2) : ℝ)) ≤ mertensError x) :
    RiemannHypothesis := by
  rw [Sieve.riemannHypothesis_iff_zetaResidueUnit_ne_zero]
  intro s hs
  have e : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
  rcases h with h | h
  · exact zetaResidueUnit_ne_zero_of_mertensError_le (b := 1 / 2) (by norm_num) (by norm_num)
      (by rw [e]; exact h) hs
  · exact zetaResidueUnit_ne_zero_of_le_mertensError (b := 1 / 2) (by norm_num) (by norm_num)
      (by rw [e]; exact h) hs

theorem rpow_sub_one_le_of_le {x b b' : ℝ} (hx : 1 ≤ x) (hbb : b ≤ b') :
    x ^ (b - 1) ≤ x ^ (b' - 1) :=
  Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- **Oscillation of the Mertens error, upper side.**  For every `b < Θ`, `R(x) > x^{b-1}`
infinitely often. -/
theorem frequently_rpow_lt_mertensError {b : ℝ} (hb : b < zeroReSup) :
    ∃ᶠ x : ℝ in atTop, x ^ (b - 1) < mertensError x := by
  have hhalf := half_le_zeroReSup
  have hΘ1 := zeroReSup_le_one
  set b' : ℝ := max b (1 / 4) with hb'
  have hb'Θ : b' < zeroReSup := max_lt hb (by linarith)
  by_contra hno
  rw [Filter.not_frequently] at hno
  have hev : ∀ᶠ x : ℝ in atTop, mertensError x ≤ 1 * x ^ (b' - 1) := by
    filter_upwards [hno, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [one_mul]
    exact le_trans (not_lt.mp hx) (rpow_sub_one_le_of_le hx1 (le_max_left _ _))
  have hz := fun s hs => zetaResidueUnit_ne_zero_of_mertensError_le
    (lt_of_lt_of_le (by norm_num) (le_max_right b (1 / 4))) (by linarith) hev (z := s) hs
  have := zeroReSup_le_of_zetaResidueUnit_ne_zero hz
  linarith

/-- **Oscillation of the Mertens error, lower side.**  For every `b < Θ`, `R(x) < -x^{b-1}`
infinitely often. -/
theorem frequently_mertensError_lt_neg_rpow {b : ℝ} (hb : b < zeroReSup) :
    ∃ᶠ x : ℝ in atTop, mertensError x < -x ^ (b - 1) := by
  have hhalf := half_le_zeroReSup
  have hΘ1 := zeroReSup_le_one
  set b' : ℝ := max b (1 / 4) with hb'
  have hb'Θ : b' < zeroReSup := max_lt hb (by linarith)
  by_contra hno
  rw [Filter.not_frequently] at hno
  have hev : ∀ᶠ x : ℝ in atTop, -(1 * x ^ (b' - 1)) ≤ mertensError x := by
    filter_upwards [hno, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [one_mul]
    have := rpow_sub_one_le_of_le hx1 (le_max_left b (1 / 4))
    linarith [not_lt.mp hx]
  have hz := fun s hs => zetaResidueUnit_ne_zero_of_le_mertensError
    (lt_of_lt_of_le (by norm_num) (le_max_right b (1 / 4))) (by linarith) hev (z := s) hs
  have := zeroReSup_le_of_zetaResidueUnit_ne_zero hz
  linarith

/-- **Unconditional oscillation.**  For every `b < 1/2`, `R(x) = Ω±(x^{b-1})`. -/
theorem mertensError_omega_pm_rpow {b : ℝ} (hb : b < 1 / 2) :
    (∃ᶠ x : ℝ in atTop, x ^ (b - 1) < mertensError x) ∧
      ∃ᶠ x : ℝ in atTop, mertensError x < -x ^ (b - 1) := by
  have h : b < zeroReSup := lt_of_lt_of_le hb half_le_zeroReSup
  exact ⟨frequently_rpow_lt_mertensError h, frequently_mertensError_lt_neg_rpow h⟩

end

end RHTower
