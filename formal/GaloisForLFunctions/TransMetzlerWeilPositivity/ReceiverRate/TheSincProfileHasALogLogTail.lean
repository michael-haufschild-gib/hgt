import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheSincProfileIsAProductOfSincs
import GaloisForLFunctions.HTGeometry.ArcsineLogIntegral
import GaloisForLFunctions.RHTower.Sieve.MertensFirst
import Mathlib.Analysis.Convex.Integral

/-!
# The Fourier tail of the sinc-product profile is `exp(−Θ(c/log² c))`

For large `c`, `∫_c^{2c} |𝓕 sincProfile|² ≥ c · exp(−K c/log² c)` with `K = 8π/3 + 3000`
(`exp_mul_le_integral_norm_fourier_sincProfile_sq`). Mechanism:

* cut the product at `J = ⌈4πc/log² c⌉ + 2`: beyond `J` every factor has argument `≤ 1` on
  `[c, 2c]` and the tail costs `exp(−(4π/3) c/log² c)` (`eventually_cut`, `sum_sincRadius_sq_le`);
* for the first `J` factors, Jensen's inequality for `exp` gives
  `∫_c^{2c} Π_{j<J} sinc² ≥ c exp(−(2/c) Σ_j ∫ −log sinc)` (`integral_prod_sinc_sq_ge`), and each
  `∫_c^{2c} −log sinc(2πρξ) ≤ (c + 1/(2ρ)) log 2 + c log⁺(4πρc)` (`integral_neg_log_sinc_le`):
  `−log|sin|` costs `π log 2` per period, and `Σ_{j<J} log(ρ_j/ρ_J) = O(J)` by Stirling
  (`sum_log_radius_ratio_le`).
-/

noncomputable section

open MeasureTheory Filter Topology Real
open scoped ContDiff FourierTransform

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

theorem sincRadius_succ (j : ℕ) :
    sincRadius (j + 1) = 1 / (4 * ((j : ℝ) + 3) * Real.log ((j : ℝ) + 3) ^ 2) := rfl

/-! ### `−log |sin|` and one sinc factor -/

theorem neg_log_sin_nonneg (y : ℝ) : 0 ≤ -Real.log (Real.sin y) := by
  rw [neg_nonneg, ← Real.log_abs]
  exact Real.log_nonpos (abs_nonneg _) (Real.abs_sin_le_one y)

/-- `∫_A^B −log|sin| ≤ (B − A + π) log 2`: cover `[A, B]` by `⌈(B − A)/π⌉` periods, each worth
`π log 2`. -/
theorem integral_neg_log_sin_le {A B : ℝ} (hAB : A ≤ B) :
    ∫ y in A..B, -Real.log (Real.sin y) ≤ (B - A + π) * Real.log 2 := by
  have hπ := Real.pi_pos
  set n : ℕ := ⌈(B - A) / π⌉₊ with hn
  have hn1 : (B - A) / π ≤ n := Nat.le_ceil _
  have hn2 : (n : ℝ) < (B - A) / π + 1 := Nat.ceil_lt_add_one (div_nonneg (by linarith) hπ.le)
  have hB : B ≤ A + n * π := by
    have := (div_le_iff₀ hπ).mp hn1
    linarith
  have hint : ∀ t₁ t₂, IntervalIntegrable (fun y => -Real.log (Real.sin y)) volume t₁ t₂ :=
    fun t₁ t₂ => (intervalIntegrable_log_sin (a := t₁) (b := t₂)).neg
  have hper : Function.Periodic (fun y : ℝ => -Real.log (Real.sin y)) π := fun u => by
    simp only [HTGeometry.periodic_log_sin u]
  have h1 : ∫ y in A..B, -Real.log (Real.sin y) ≤ ∫ y in A..A + n * π, -Real.log (Real.sin y) :=
    intervalIntegral.integral_mono_interval le_rfl hAB hB
      (Filter.Eventually.of_forall fun y => neg_log_sin_nonneg y) (hint _ _)
  have h2 : ∫ y in A..A + n * π, -Real.log (Real.sin y) = n * (π * Real.log 2) := by
    have := hper.intervalIntegral_add_zsmul_eq (n : ℤ) A hint
    simp only [zsmul_eq_mul, Int.cast_natCast] at this
    rw [this, hper.intervalIntegral_add_eq A 0, zero_add, intervalIntegral.integral_neg,
      integral_log_sin_zero_pi]
    ring
  have h3 : (n : ℝ) * (π * Real.log 2) ≤ (B - A + π) * Real.log 2 := by
    have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have : (n : ℝ) * π ≤ B - A + π := by
      have := mul_lt_mul_of_pos_right hn2 hπ
      rw [add_mul, div_mul_cancel₀ _ hπ.ne', one_mul] at this
      linarith
    nlinarith
  linarith


/-- `−log sinc x ≤ −log sin x + log⁺ x` for `x > 0` (equality off the zeros of `sin`). -/
theorem neg_log_sinc_le {x : ℝ} (hx : 0 < x) :
    -Real.log (Real.sinc x) ≤ -Real.log (Real.sin x) + max (Real.log x) 0 := by
  rw [Real.sinc_of_ne_zero hx.ne']
  by_cases hs : Real.sin x = 0
  · simp [hs]
  · rw [Real.log_div hs hx.ne']
    have := le_max_left (Real.log x) 0
    linarith


/-- `Σ_{i<m} log((m+3)/(i+3)) ≤ m + 3`. -/
theorem sum_log_ratio_le (m : ℕ) :
    ∑ i ∈ Finset.range m, Real.log (((m : ℝ) + 3) / ((i : ℝ) + 3)) ≤ m + 3 := by
  have hprod : ∏ i ∈ Finset.range m, ((i : ℝ) + 3) = ((m + 2).factorial : ℝ) / 2 := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      have hf : (m + 1 + 2).factorial = (m + 3) * (m + 2).factorial := by
        rw [show m + 1 + 2 = (m + 2) + 1 by ring, Nat.factorial_succ]
      rw [hf]; push_cast; ring
  have hsplit : ∑ i ∈ Finset.range m, Real.log (((m : ℝ) + 3) / ((i : ℝ) + 3)) =
      m * Real.log ((m : ℝ) + 3) - Real.log (((m + 2).factorial : ℝ) / 2) := by
    rw [← hprod, Real.log_prod (fun i _ => by positivity)]
    rw [Finset.sum_congr rfl fun i _ => Real.log_div (by positivity) (by positivity),
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsplit]
  have hf : (0 : ℝ) < ((m + 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [Real.log_div hf.ne' two_ne_zero]
  have hst := RHTower.Sieve.le_log_factorial (m + 2)
  push_cast at hst
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hdiff : Real.log ((m : ℝ) + 3) - Real.log ((m : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) := by
    rw [← Real.log_div (by positivity) hm2.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < ((m : ℝ) + 3) / ((m : ℝ) + 2) by positivity)
    have e : ((m : ℝ) + 3) / ((m : ℝ) + 2) - 1 = 1 / ((m : ℝ) + 2) := by field_simp; ring
    linarith
  have hl2 : Real.log 2 ≤ Real.log ((m : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmm : (m : ℝ) * (1 / ((m : ℝ) + 2)) ≤ 1 := by
    rw [mul_one_div, div_le_one hm2]; linarith
  have h1 : (m : ℝ) * (Real.log ((m : ℝ) + 3) - Real.log ((m : ℝ) + 2)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg m)).trans hmm
  nlinarith


/-- `log(log y / log x) ≤ log(y/x)` for `3 ≤ x ≤ y`, since `log t / t` decreases beyond `e`. -/
theorem log_log_ratio_le {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    Real.log (Real.log y / Real.log x) ≤ Real.log (y / x) := by
  have he : Real.exp 1 ≤ x := by have := Real.exp_one_lt_d9; linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hanti := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr he) (Set.mem_Ici.mpr (he.trans hxy)) hxy
  simp only at hanti
  apply Real.log_le_log (div_pos hly hlx)
  rw [div_le_div_iff₀ hlx hx0]
  rw [div_le_div_iff₀ (by linarith) hx0] at hanti
  linarith

/-- `Σ_{i<m} log(a_i/a_m) ≤ 3(m + 3)` for the Steklov radii. -/
theorem sum_log_radius_ratio_le (m : ℕ) :
    ∑ i ∈ Finset.range m, Real.log (steklovRadius i / steklovRadius m) ≤ 3 * ((m : ℝ) + 3) := by
  have hterm : ∀ i ∈ Finset.range m, Real.log (steklovRadius i / steklovRadius m) ≤
      3 * Real.log (((m : ℝ) + 3) / ((i : ℝ) + 3)) := by
    intro i hi
    have him : (i : ℝ) + 3 ≤ (m : ℝ) + 3 := by
      have := Finset.mem_range.mp hi; exact_mod_cast (by omega : i + 3 ≤ m + 3)
    have hi3 : (3 : ℝ) ≤ (i : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) i]
    have hli : 0 < Real.log ((i : ℝ) + 3) := Real.log_pos (by linarith)
    have hlm : 0 < Real.log ((m : ℝ) + 3) := Real.log_pos (by linarith)
    have hratio : steklovRadius i / steklovRadius m =
        (((m : ℝ) + 3) / ((i : ℝ) + 3)) * (Real.log ((m : ℝ) + 3) / Real.log ((i : ℝ) + 3)) ^ 2 := by
      unfold steklovRadius
      field_simp
    rw [hratio, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have := log_log_ratio_le hi3 him
    push_cast
    linarith
  calc ∑ i ∈ Finset.range m, Real.log (steklovRadius i / steklovRadius m)
      ≤ ∑ i ∈ Finset.range m, 3 * Real.log (((m : ℝ) + 3) / ((i : ℝ) + 3)) :=
        Finset.sum_le_sum hterm
    _ = 3 * ∑ i ∈ Finset.range m, Real.log (((m : ℝ) + 3) / ((i : ℝ) + 3)) := by
        rw [Finset.mul_sum]
    _ ≤ 3 * ((m : ℝ) + 3) := by linarith [sum_log_ratio_le m]

/-- **One factor.** For `ρ, c > 0`: `∫_c^{2c} −log sinc(2πρξ) dξ ≤ (c + 1/(2ρ)) log 2 + c log⁺(4πρc)`. -/
theorem integral_neg_log_sinc_le {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) :
    ∫ ξ in c..2 * c, -Real.log (Real.sinc (2 * π * ρ * ξ)) ≤
      (c + 1 / (2 * ρ)) * Real.log 2 + c * max (Real.log (4 * π * ρ * c)) 0 := by
  have hπ := Real.pi_pos
  set b := 2 * π * ρ with hb
  have hb0 : 0 < b := by positivity
  -- integrability
  have hsin : IntervalIntegrable (fun ξ => -Real.log (Real.sin (b * ξ))) volume c (2 * c) := by
    have h := (intervalIntegrable_log_sin (a := b * c) (b := b * (2 * c))).comp_mul_left (c := b)
    rw [mul_div_cancel_left₀ _ hb0.ne', mul_div_cancel_left₀ _ hb0.ne'] at h
    exact h.neg
  have hlog : IntervalIntegrable (fun ξ => max (Real.log (b * ξ)) 0) volume c (2 * c) := by
    refine ContinuousOn.intervalIntegrable fun ξ hξ => ?_
    rw [Set.uIcc_of_le (by linarith)] at hξ
    have : b * ξ ≠ 0 := (mul_pos hb0 (by linarith [hξ.1])).ne'
    exact ((Real.continuousAt_log this).comp (continuousAt_const.mul continuousAt_id)).continuousWithinAt.max
      continuousWithinAt_const
  have hpt : ∀ ξ, c ≤ ξ → -Real.log (Real.sinc (b * ξ)) ≤
      -Real.log (Real.sin (b * ξ)) + max (Real.log (b * ξ)) 0 := fun ξ hξ =>
    neg_log_sinc_le (mul_pos hb0 (by linarith))
  have hsinc_nonneg : ∀ x, 0 ≤ -Real.log (Real.sinc x) := fun x => by
    rw [neg_nonneg, ← Real.log_abs]
    exact Real.log_nonpos (abs_nonneg _) (Real.abs_sinc_le_one x)
  have hsin_nonneg : ∀ x, 0 ≤ -Real.log (Real.sin x) := fun x => by
    rw [neg_nonneg, ← Real.log_abs]
    exact Real.log_nonpos (abs_nonneg _) (Real.abs_sin_le_one x)
  have hsinc : IntervalIntegrable (fun ξ => -Real.log (Real.sinc (b * ξ))) volume c (2 * c) := by
    refine (hsin.add hlog).mono_fun' ?_ ?_
    · exact (Real.measurable_log.comp (Real.continuous_sinc.comp
        (continuous_const.mul continuous_id)).measurable).neg.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun ξ hξ => ?_)
      rw [Set.uIoc_of_le (by linarith)] at hξ
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (hsinc_nonneg _)]
      exact hpt ξ hξ.1.le
  have h1 : ∫ ξ in c..2 * c, -Real.log (Real.sinc (b * ξ)) ≤
      ∫ ξ in c..2 * c, (-Real.log (Real.sin (b * ξ)) + max (Real.log (b * ξ)) 0) :=
    intervalIntegral.integral_mono_on (by linarith) hsinc (hsin.add hlog) fun ξ hξ => hpt ξ hξ.1
  have h2 : ∫ ξ in c..2 * c, -Real.log (Real.sin (b * ξ)) ≤ (c + 1 / (2 * ρ)) * Real.log 2 := by
    rw [intervalIntegral.integral_comp_mul_left (fun y => -Real.log (Real.sin y)) hb0.ne',
      smul_eq_mul]
    have := integral_neg_log_sin_le (show b * c ≤ b * (2 * c) by nlinarith)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc b⁻¹ * ∫ y in b * c..b * (2 * c), -Real.log (Real.sin y)
        ≤ b⁻¹ * ((b * (2 * c) - b * c + π) * Real.log 2) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hb0.le)
      _ = (c + 1 / (2 * ρ)) * Real.log 2 := by rw [hb]; field_simp; ring
  have h3 : ∫ ξ in c..2 * c, max (Real.log (b * ξ)) 0 ≤ c * max (Real.log (4 * π * ρ * c)) 0 := by
    have hle : ∀ ξ ∈ Set.Icc c (2 * c), max (Real.log (b * ξ)) 0 ≤ max (Real.log (4 * π * ρ * c)) 0 :=
      fun ξ hξ => max_le_max (Real.log_le_log (mul_pos hb0 (by linarith [hξ.1]))
        (by rw [hb]; nlinarith [hξ.2])) le_rfl
    have := intervalIntegral.integral_mono_on (by linarith) hlog intervalIntegrable_const hle
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  rw [intervalIntegral.integral_add hsin hlog] at h1
  linarith

/-- `log sinc(bξ)` is interval integrable on `[c, 2c]`, dominated by `|log sin| + log⁺`. -/
theorem intervalIntegrable_log_sinc {b c : ℝ} (hb0 : 0 < b) (hc : 0 < c) :
    IntervalIntegrable (fun ξ => Real.log (Real.sinc (b * ξ))) volume c (2 * c) := by
  have hsin : IntervalIntegrable (fun ξ => -Real.log (Real.sin (b * ξ))) volume c (2 * c) := by
    have h := (intervalIntegrable_log_sin (a := b * c) (b := b * (2 * c))).comp_mul_left (c := b)
    rw [mul_div_cancel_left₀ _ hb0.ne', mul_div_cancel_left₀ _ hb0.ne'] at h
    exact h.neg
  have hlog : IntervalIntegrable (fun ξ => max (Real.log (b * ξ)) 0) volume c (2 * c) := by
    refine ContinuousOn.intervalIntegrable fun ξ hξ => ?_
    rw [Set.uIcc_of_le (by linarith)] at hξ
    have : b * ξ ≠ 0 := (mul_pos hb0 (by linarith [hξ.1])).ne'
    exact ((Real.continuousAt_log this).comp
      (continuousAt_const.mul continuousAt_id)).continuousWithinAt.max continuousWithinAt_const
  refine (hsin.add hlog).mono_fun' ?_ ?_
  · exact (Real.measurable_log.comp (Real.continuous_sinc.comp
      (continuous_const.mul continuous_id)).measurable).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun ξ hξ => ?_)
    rw [Set.uIoc_of_le (by linarith)] at hξ
    have hx : 0 < b * ξ := mul_pos hb0 (by linarith [hξ.1])
    have hle0 : Real.log (Real.sinc (b * ξ)) ≤ 0 := by
      rw [← Real.log_abs]
      exact Real.log_nonpos (abs_nonneg _) (Real.abs_sinc_le_one _)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonpos hle0]
    exact neg_log_sinc_le hx

/-- **Jensen for a finite sinc product.** On `[c, 2c]`,
`∫ Π_j sinc(2πρ_jξ)² ≥ c · exp(−(2/c) Σ_j ∫ −log sinc(2πρ_jξ))`. -/
theorem integral_prod_sinc_sq_ge {s : Finset ℕ} {ρ : ℕ → ℝ} (hρ : ∀ j ∈ s, 0 < ρ j) {c : ℝ}
    (hc : 0 < c) :
    c * Real.exp (-(2 / c) * ∑ j ∈ s, ∫ ξ in c..2 * c, -Real.log (Real.sinc (2 * π * ρ j * ξ)))
      ≤ ∫ ξ in c..2 * c, ∏ j ∈ s, Real.sinc (2 * π * ρ j * ξ) ^ 2 := by
  have hπ := Real.pi_pos
  set t := Set.Ioc c (2 * c) with ht
  have hvol : volume t = ENNReal.ofReal c := by
    rw [ht, Real.volume_Ioc]; congr 1; ring
  have hvolr : volume.real t = c := by
    rw [Measure.real, hvol, ENNReal.toReal_ofReal hc.le]
  set f : ℝ → ℝ := fun ξ => ∑ j ∈ s, 2 * Real.log (Real.sinc (2 * π * ρ j * ξ)) with hf
  have hint_j : ∀ j ∈ s, IntervalIntegrable (fun ξ => Real.log (Real.sinc (2 * π * ρ j * ξ)))
      volume c (2 * c) := fun j hj => intervalIntegrable_log_sinc (by have := hρ j hj; positivity) hc
  have hfi : IntegrableOn f t := by
    rw [ht, ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    have h := IntervalIntegrable.sum s fun j hj => (hint_j j hj).const_mul 2
    rw [Finset.sum_fn] at h
    exact h
  have hf_le : ∀ ξ, f ξ ≤ 0 := fun ξ => by
    simp only [hf]
    refine Finset.sum_nonpos fun j _ => ?_
    have : Real.log (Real.sinc (2 * π * ρ j * ξ)) ≤ 0 := by
      rw [← Real.log_abs]
      exact Real.log_nonpos (abs_nonneg _) (Real.abs_sinc_le_one _)
    linarith
  have hfm : Measurable f := by
    simp only [hf]
    exact Finset.measurable_sum s fun j _ => (Real.measurable_log.comp
      (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).measurable).const_mul 2
  have hgi : IntegrableOn (Real.exp ∘ f) t := by
    haveI : IsFiniteMeasure (volume.restrict t) :=
      isFiniteMeasure_restrict.mpr (by rw [hvol]; exact ENNReal.ofReal_ne_top)
    refine Integrable.mono' (integrable_const (1 : ℝ)) (Real.measurable_exp.comp hfm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (hf_le ξ)
  have hJ := ConvexOn.map_set_average_le convexOn_exp continuousOn_exp isClosed_univ
    (by rw [hvol]; exact (ENNReal.ofReal_pos.mpr hc).ne') (by rw [hvol]; exact ENNReal.ofReal_ne_top)
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hfi hgi
  rw [setAverage_eq, setAverage_eq, hvolr, smul_eq_mul, smul_eq_mul] at hJ
  -- the average of `f`
  have hfavg : ∫ ξ in t, f ξ = -2 * ∑ j ∈ s, ∫ ξ in c..2 * c, -Real.log (Real.sinc (2 * π * ρ j * ξ)) := by
    rw [ht, ← intervalIntegral.integral_of_le (by linarith)]
    simp only [hf]
    rw [intervalIntegral.integral_finsetSum fun j hj => (hint_j j hj).const_mul 2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg]
    ring
  -- `exp ∘ f` is the squared product off a countable set
  have hzero : ∀ᵐ ξ ∂(volume.restrict t), Real.exp (f ξ) = ∏ j ∈ s, Real.sinc (2 * π * ρ j * ξ) ^ 2 := by
    have hcount : ({ξ : ℝ | ∃ j ∈ s, Real.sinc (2 * π * ρ j * ξ) = 0}).Countable := by
      have hsub : {ξ : ℝ | ∃ j ∈ s, Real.sinc (2 * π * ρ j * ξ) = 0} ⊆
          ⋃ j ∈ s, Set.range (fun n : ℤ => (n : ℝ) / (2 * ρ j)) := by
        rintro ξ ⟨j, hj, hz⟩
        have hρj := hρ j hj
        have hne : 2 * π * ρ j * ξ ≠ 0 := by
          intro h0; rw [h0, Real.sinc_zero] at hz; exact one_ne_zero hz
        rw [Real.sinc_of_ne_zero hne, div_eq_zero_iff] at hz
        rcases hz with hz | hz
        · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hz
          refine Set.mem_biUnion hj ⟨n, ?_⟩
          show (n : ℝ) / (2 * ρ j) = ξ
          rw [div_eq_iff (by positivity)]
          have h2 : ((n : ℝ) - ξ * (2 * ρ j)) * π = 0 := by rw [sub_mul]; linarith [hn]
          rcases mul_eq_zero.mp h2 with h | h
          · linarith
          · exact absurd h hπ.ne'
        · exact absurd hz hne
      exact (Set.Countable.biUnion s.countable_toSet fun j _ => Set.countable_range _).mono hsub
    have hnull := hcount.measure_zero volume
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    refine measure_mono_null (fun ξ hξ => ?_) hnull
    simp only [Set.mem_setOf_eq] at hξ ⊢
    by_contra hall
    push Not at hall
    apply hξ
    show Real.exp (∑ j ∈ s, 2 * Real.log (Real.sinc (2 * π * ρ j * ξ))) = _
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [show 2 * Real.log (Real.sinc (2 * π * ρ j * ξ)) =
        (2 : ℕ) * Real.log (Real.sinc (2 * π * ρ j * ξ)) by norm_num, Real.exp_nat_mul,
      Real.exp_log_eq_abs (hall j hj), sq_abs]
  have hint_eq : ∫ ξ in t, Real.exp (f ξ) = ∫ ξ in c..2 * c, ∏ j ∈ s, Real.sinc (2 * π * ρ j * ξ) ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← ht]
    exact integral_congr_ae hzero
  rw [hfavg, hint_eq] at hJ
  have hexp : Real.exp (c⁻¹ * (-2 * ∑ j ∈ s, ∫ ξ in c..2 * c, -Real.log (Real.sinc (2 * π * ρ j * ξ)))) =
      Real.exp (-(2 / c) * ∑ j ∈ s, ∫ ξ in c..2 * c, -Real.log (Real.sinc (2 * π * ρ j * ξ))) := by
    congr 1; field_simp
  rw [hexp] at hJ
  have := mul_le_mul_of_nonneg_left hJ hc.le
  rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this


theorem one_le_log_three_add {x : ℝ} (hx : 0 ≤ x) : 1 ≤ Real.log (x + 3) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith


theorem sincRadius_succ_le (j : ℕ) : sincRadius (j + 1) ≤ sincRadius j := by
  cases j with
  | zero =>
    show steklovRadius 0 ≤ 1 / 4
    unfold steklovRadius
    have hl := one_le_log_three_add (le_refl (0 : ℝ))
    apply one_div_le_one_div_of_le (by norm_num)
    have : (1 : ℝ) ≤ Real.log ((0 : ℕ) + 3 : ℝ) ^ 2 := by
      simpa using one_le_pow₀ (n := 2) hl
    push_cast at this ⊢
    nlinarith
  | succ j => exact steklovRadius_succ_le j

theorem sincRadius_le_of_le {i j : ℕ} (hij : i ≤ j) : sincRadius j ≤ sincRadius i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (sincRadius_succ_le j).trans ih


/-- `ρ_j = 1/(4(j+2) log²(j+2))` for `j ≥ 1`. -/
theorem sincRadius_eq {j : ℕ} (hj : 1 ≤ j) :
    sincRadius j = 1 / (4 * ((j : ℝ) + 2) * Real.log ((j : ℝ) + 2) ^ 2) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [sincRadius_succ]; push_cast; ring_nf

/-- **(K1) Small arguments beyond the cut.** -/
theorem four_pi_sincRadius_mul_le {c : ℝ} {J : ℕ} (hJ : 1 ≤ J)
    (hcJ : π * c ≤ ((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) {j : ℕ} (hj : J ≤ j) :
    4 * π * sincRadius j * c ≤ 1 := by
  rw [sincRadius_eq (hJ.trans hj)]
  have hJj : (J : ℝ) + 2 ≤ (j : ℝ) + 2 := by exact_mod_cast (by omega : J + 2 ≤ j + 2)
  have hlJ : 1 ≤ Real.log ((J : ℝ) + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  have hlj : Real.log ((J : ℝ) + 2) ≤ Real.log ((j : ℝ) + 2) := Real.log_le_log (by positivity) hJj
  have hmono : ((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2 ≤
      ((j : ℝ) + 2) * Real.log ((j : ℝ) + 2) ^ 2 :=
    mul_le_mul hJj (pow_le_pow_left₀ (by linarith) hlj 2) (by positivity) (by positivity)
  have hpos : 0 < 4 * ((j : ℝ) + 2) * Real.log ((j : ℝ) + 2) ^ 2 := by
    have : 0 < Real.log ((j : ℝ) + 2) := by linarith
    positivity
  rw [show 4 * π * (1 / (4 * ((j : ℝ) + 2) * Real.log ((j : ℝ) + 2) ^ 2)) * c =
      (π * c) / (((j : ℝ) + 2) * Real.log ((j : ℝ) + 2) ^ 2) by field_simp]
  have hpos' : 0 < ((j : ℝ) + 2) * Real.log ((j : ℝ) + 2) ^ 2 := by
    have : 0 < Real.log ((j : ℝ) + 2) := by linarith
    positivity
  rw [div_le_one hpos']
  linarith

/-- **(K2) The tail of the squared radii.** -/
theorem sum_sincRadius_sq_le {J : ℕ} (hJ : 1 ≤ J) (M : ℕ) :
    ∑ j ∈ Finset.Ico J M, sincRadius j ^ 2 ≤
      1 / (16 * Real.log ((J : ℝ) + 2) ^ 4 * ((J : ℝ) + 1)) := by
  have hlJ : 1 ≤ Real.log ((J : ℝ) + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    linarith
  have hterm : ∀ j ∈ Finset.Ico J M, sincRadius j ^ 2 ≤
      1 / (16 * Real.log ((J : ℝ) + 2) ^ 4) * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) := by
    intro j hj
    have hJj := (Finset.mem_Ico.mp hj).1
    rw [sincRadius_eq (hJ.trans hJj)]
    have hJj' : (J : ℝ) + 2 ≤ (j : ℝ) + 2 := by exact_mod_cast (by omega : J + 2 ≤ j + 2)
    have hlj : Real.log ((J : ℝ) + 2) ≤ Real.log ((j : ℝ) + 2) := Real.log_le_log (by positivity) hJj'
    have htel : 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2) = 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
      field_simp; ring
    rw [htel, div_pow, one_pow, mul_pow, mul_pow, ← pow_mul]
    rw [div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    have h4 : Real.log ((J : ℝ) + 2) ^ 4 ≤ Real.log ((j : ℝ) + 2) ^ (2 * 2) :=
      pow_le_pow_left₀ (by linarith) hlj 4
    have hj1 : ((j : ℝ) + 1) * ((j : ℝ) + 2) ≤ ((j : ℝ) + 2) ^ 2 := by nlinarith
    calc 16 * Real.log ((J : ℝ) + 2) ^ 4 * (((j : ℝ) + 1) * ((j : ℝ) + 2))
        ≤ 16 * Real.log ((j : ℝ) + 2) ^ (2 * 2) * ((j : ℝ) + 2) ^ 2 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h4 (by norm_num)) hj1 (by positivity)
            (mul_nonneg (by norm_num) (pow_nonneg (by linarith) _))
      _ = 4 ^ 2 * ((j : ℝ) + 2) ^ 2 * Real.log ((j : ℝ) + 2) ^ (2 * 2) := by ring
  calc ∑ j ∈ Finset.Ico J M, sincRadius j ^ 2
      ≤ ∑ j ∈ Finset.Ico J M,
          1 / (16 * Real.log ((J : ℝ) + 2) ^ 4) * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) :=
        Finset.sum_le_sum hterm
    _ = 1 / (16 * Real.log ((J : ℝ) + 2) ^ 4) *
          ∑ j ∈ Finset.Ico J M, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) := by
        rw [Finset.mul_sum]
    _ ≤ 1 / (16 * Real.log ((J : ℝ) + 2) ^ 4) * (1 / ((J : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rcases le_total J M with hJM | hJM
        · have := Finset.sum_Ico_sub (fun j => -(1 / ((j : ℝ) + 1))) hJM
          have e : ∑ j ∈ Finset.Ico J M, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + 2)) =
              ∑ j ∈ Finset.Ico J M, (-(1 / (((j + 1 : ℕ) : ℝ) + 1)) - -(1 / ((j : ℝ) + 1))) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            push_cast; ring_nf
          rw [e, this]
          have : 0 ≤ 1 / ((M : ℝ) + 1) := by positivity
          linarith
        · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
          positivity
    _ = 1 / (16 * Real.log ((J : ℝ) + 2) ^ 4 * ((J : ℝ) + 1)) := by
        rw [one_div_mul_one_div]

theorem sincRadius_eq_steklovRadius {J : ℕ} (hJ : 1 ≤ J) : sincRadius J = steklovRadius (J - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, J = i + 1 := ⟨J - 1, by omega⟩
  simp [sincRadius]

/-- **(K3) The finite factors cost `O(cJ + J² log² J)`.** -/
theorem sum_factor_bound_le {c : ℝ} (hc : 0 < c) {J : ℕ} (hJ : 1 ≤ J)
    (hcJ : π * c ≤ ((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) :
    ∑ j ∈ Finset.range J,
        ((c + 1 / (2 * sincRadius j)) * Real.log 2 + c * max (Real.log (4 * π * sincRadius j * c)) 0) ≤
      c * J * Real.log 2 + 2 * Real.log 2 * J * (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) +
        c * (3 * Real.log ((J : ℝ) + 2) + 3 * ((J : ℝ) + 2)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hρJ := sincRadius_pos J
  have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hlJ : 1 ≤ Real.log ((J : ℝ) + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hinvJ : 1 / sincRadius J = 4 * (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) := by
    rw [sincRadius_eq hJ]; field_simp
  have hsmallJ : 4 * π * sincRadius J * c ≤ 1 := four_pi_sincRadius_mul_le hJ hcJ le_rfl
  -- each factor
  have hterm : ∀ j ∈ Finset.range J,
      (c + 1 / (2 * sincRadius j)) * Real.log 2 + c * max (Real.log (4 * π * sincRadius j * c)) 0 ≤
        c * Real.log 2 + 2 * Real.log 2 * (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) +
          c * Real.log (sincRadius j / sincRadius J) := by
    intro j hj
    have hjJ : j ≤ J := (Finset.mem_range.mp hj).le
    have hρj := sincRadius_pos j
    have hmono : sincRadius J ≤ sincRadius j := sincRadius_le_of_le hjJ
    have h1 : 1 / (2 * sincRadius j) ≤ 2 * (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) := by
      have : 1 / sincRadius j ≤ 1 / sincRadius J := one_div_le_one_div_of_le hρJ hmono
      rw [hinvJ, one_div] at this
      rw [one_div, mul_inv]
      linarith
    have h2 : max (Real.log (4 * π * sincRadius j * c)) 0 ≤ Real.log (sincRadius j / sincRadius J) := by
      have hge : 0 ≤ Real.log (sincRadius j / sincRadius J) :=
        Real.log_nonneg (by rw [le_div_iff₀ hρJ]; linarith)
      refine max_le ?_ hge
      have hpos : 0 < 4 * π * sincRadius j * c := by have := Real.pi_pos; positivity
      apply Real.log_le_log hpos
      rw [le_div_iff₀ hρJ]
      have := mul_le_mul_of_nonneg_left hsmallJ hρj.le
      nlinarith [Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left h2 hc.le, mul_le_mul_of_nonneg_right h1 hl2.le]
  -- the logarithmic sum
  have hlogsum : ∑ j ∈ Finset.range J, Real.log (sincRadius j / sincRadius J) ≤
      3 * Real.log ((J : ℝ) + 2) + 3 * ((J : ℝ) + 2) := by
    obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 := ⟨J - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have hsum := sum_log_radius_ratio_le n
    have hshift : ∑ i ∈ Finset.range n, Real.log (sincRadius (i + 1) / sincRadius (n + 1)) =
        ∑ i ∈ Finset.range n, Real.log (steklovRadius i / steklovRadius n) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rfl
    rw [hshift]
    have h0 : Real.log (sincRadius 0 / sincRadius (n + 1)) ≤ 3 * Real.log (((n + 1 : ℕ) : ℝ) + 2) := by
      have hr : sincRadius 0 / sincRadius (n + 1) =
          (((n + 1 : ℕ) : ℝ) + 2) * Real.log (((n + 1 : ℕ) : ℝ) + 2) ^ 2 := by
        rw [div_eq_mul_one_div, show sincRadius 0 = 1 / 4 from rfl, hinvJ]; ring
      have hl1 : 1 ≤ Real.log (((n + 1 : ℕ) : ℝ) + 2) := hlJ
      rw [hr, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have := Real.log_le_sub_one_of_pos (show 0 < Real.log (((n + 1 : ℕ) : ℝ) + 2) by linarith)
      push_cast at this ⊢
      linarith
    push_cast at hsum h0 ⊢
    linarith
  calc ∑ j ∈ Finset.range J,
        ((c + 1 / (2 * sincRadius j)) * Real.log 2 + c * max (Real.log (4 * π * sincRadius j * c)) 0)
      ≤ ∑ j ∈ Finset.range J,
          (c * Real.log 2 + 2 * Real.log 2 * (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) +
            c * Real.log (sincRadius j / sincRadius J)) := Finset.sum_le_sum hterm
    _ = J * (c * Real.log 2 + 2 * Real.log 2 * (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2)) +
          c * ∑ j ∈ Finset.range J, Real.log (sincRadius j / sincRadius J) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Finset.mul_sum]
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hlogsum hc.le
        nlinarith

open Filter in
/-- **(K4) The cut `J = ⌈4πc/log²c⌉ + 2`.** For large `c` it makes every later factor small,
its tail costs `(4π/3) c/log²c`, and the earlier factors cost at most `3000 c/log²c`. -/
theorem eventually_cut : ∀ᶠ c : ℝ in atTop, ∃ J : ℕ, 1 ≤ J ∧
    π * c ≤ ((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2 ∧
    16 * π ^ 2 * c ^ 2 / 3 * (1 / (16 * Real.log ((J : ℝ) + 2) ^ 4 * ((J : ℝ) + 1))) ≤
      4 * π / 3 * (c / Real.log c ^ 2) ∧
    2 / c * (c * J * Real.log 2 + 2 * Real.log 2 * J * (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) +
        c * (3 * Real.log ((J : ℝ) + 2) + 3 * ((J : ℝ) + 2))) ≤ 3000 * (c / Real.log c ^ 2) := by
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hπ4 := Real.pi_lt_d2
  have ho2 := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  have ho3 := (isLittleO_log_rpow_rpow_atTop 3 (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1)
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (8 * π)
  filter_upwards [ho2, ho3, hlog, eventually_ge_atTop (25 : ℝ)] with c h2 h3 hl8 hc25
  have hc0 : 0 < c := by linarith
  have hlc0 : 0 < Real.log c := by linarith
  -- clean forms of the asymptotic inputs
  have hsq : Real.log c ^ 2 ≤ Real.sqrt c := by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul,
      Real.rpow_two, ← Real.sqrt_eq_rpow] at h2
    exact h2
  have hcube : Real.log c ^ 3 ≤ c := by
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul,
      Real.rpow_one, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h3
    exact h3
  have hl2 : 8 * π ≤ Real.log c ^ 2 := by nlinarith
  have hsqc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc0.le
  have hs5 : 5 ≤ Real.sqrt c := by
    rw [show (5 : ℝ) = Real.sqrt 25 by rw [show (25 : ℝ) = 5 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hc25
  set X := 4 * π * c / Real.log c ^ 2 with hX
  have hL2 : 0 < Real.log c ^ 2 := by positivity
  have hXsqrt : Real.sqrt c ≤ X := by
    rw [hX, le_div_iff₀ hL2]
    nlinarith [Real.sqrt_nonneg c]
  have hX5 : 5 ≤ X := hs5.trans hXsqrt
  have hXc : 2 * X ≤ c := by
    rw [hX, show 2 * (4 * π * c / Real.log c ^ 2) = 8 * π * c / Real.log c ^ 2 by ring,
      div_le_iff₀ hL2]
    nlinarith
  set J : ℕ := ⌈X⌉₊ + 2 with hJ
  have hJX : X + 2 ≤ (J : ℝ) := by rw [hJ]; push_cast; linarith [Nat.le_ceil X]
  have hJX' : (J : ℝ) ≤ X + 3 := by
    rw [hJ]; push_cast; linarith [Nat.ceil_lt_add_one (by linarith : 0 ≤ X)]
  have hJ2 : (J : ℝ) + 2 ≤ 2 * X := by linarith
  have hXpos : 0 < X := by linarith
  have hlogJ_lo : Real.log c / 2 ≤ Real.log ((J : ℝ) + 2) := by
    have h1 : Real.log (Real.sqrt c) = Real.log c / 2 := by rw [Real.log_sqrt hc0.le]
    rw [← h1]
    exact Real.log_le_log (by linarith) (by linarith)
  have hlogJ_hi : Real.log ((J : ℝ) + 2) ≤ Real.log c :=
    Real.log_le_log (by positivity) (by linarith)
  have hlJ0 : 0 < Real.log ((J : ℝ) + 2) := by linarith
  refine ⟨J, by rw [hJ]; omega, ?_, ?_, ?_⟩
  · -- (b)
    have h1 : X * (Real.log c / 2) ^ 2 ≤ ((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2 :=
      mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity) hlogJ_lo 2) (by positivity)
        (by positivity)
    have h2 : X * (Real.log c / 2) ^ 2 = π * c := by rw [hX]; field_simp; ring
    linarith
  · -- (c)
    have hden : 4 * π * c * Real.log c ^ 2 ≤
        16 * Real.log ((J : ℝ) + 2) ^ 4 * ((J : ℝ) + 1) := by
      have h4 : (Real.log c / 2) ^ 4 ≤ Real.log ((J : ℝ) + 2) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hlogJ_lo 4
      have hJ1 : X ≤ (J : ℝ) + 1 := by linarith
      have : 16 * (Real.log c / 2) ^ 4 * X = 4 * π * c * Real.log c ^ 2 := by
        rw [hX]; field_simp; ring
      rw [← this]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h4 (by norm_num)) hJ1 hXpos.le (by positivity)
    have hpos : 0 < 4 * π * c * Real.log c ^ 2 := by positivity
    calc 16 * π ^ 2 * c ^ 2 / 3 * (1 / (16 * Real.log ((J : ℝ) + 2) ^ 4 * ((J : ℝ) + 1)))
        ≤ 16 * π ^ 2 * c ^ 2 / 3 * (1 / (4 * π * c * Real.log c ^ 2)) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpos hden) (by positivity)
      _ = 4 * π / 3 * (c / Real.log c ^ 2) := by field_simp; ring
  · -- (d)
    have hl2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hJle : (J : ℝ) ≤ 2 * X := by linarith
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hlog_c : Real.log c ≤ c / Real.log c ^ 2 := by
      rw [le_div_iff₀ hL2]; nlinarith
    have hlog2J : Real.log ((J : ℝ) + 2) ^ 2 ≤ Real.log c ^ 2 :=
      pow_le_pow_left₀ hlJ0.le hlogJ_hi 2
    have hXsq : X * X * Real.log c ^ 2 / c = 16 * π ^ 2 * (c / Real.log c ^ 2) := by
      rw [hX]; field_simp; ring
    have hA : 2 / c * (c * J * Real.log 2) ≤ 4 * X := by
      rw [show 2 / c * (c * J * Real.log 2) = 2 * J * Real.log 2 by field_simp]
      nlinarith
    have hB : 2 / c * (2 * Real.log 2 * J * (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2)) ≤
        16 * (X * X * Real.log c ^ 2 / c) := by
      have h1 : 2 * Real.log 2 * J * (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) ≤
          2 * 1 * (2 * X) * ((2 * X) * Real.log c ^ 2) := by
        apply mul_le_mul (mul_le_mul (by linarith) hJle hJ0 (by norm_num))
          (mul_le_mul hJ2 hlog2J (by positivity) (by positivity)) (by positivity) (by positivity)
      have h2 : 2 / c * (2 * 1 * (2 * X) * ((2 * X) * Real.log c ^ 2)) =
          16 * (X * X * Real.log c ^ 2 / c) := by field_simp; ring
      rw [← h2]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hC : 2 / c * (c * (3 * Real.log ((J : ℝ) + 2) + 3 * ((J : ℝ) + 2))) ≤
        6 * Real.log c + 12 * X := by
      rw [show 2 / c * (c * (3 * Real.log ((J : ℝ) + 2) + 3 * ((J : ℝ) + 2))) =
        6 * Real.log ((J : ℝ) + 2) + 6 * ((J : ℝ) + 2) by field_simp; ring]
      linarith
    have hsum : 2 / c * (c * J * Real.log 2 + 2 * Real.log 2 * J *
        (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) +
        c * (3 * Real.log ((J : ℝ) + 2) + 3 * ((J : ℝ) + 2))) ≤
        16 * X + 16 * (X * X * Real.log c ^ 2 / c) + 6 * Real.log c := by
      rw [mul_add, mul_add]; linarith
    rw [hXsq] at hsum
    have hXeq : X = 4 * π * (c / Real.log c ^ 2) := by rw [hX]; ring
    have hcl : 0 ≤ c / Real.log c ^ 2 := by positivity
    rw [hXeq] at hsum
    have hπu : π * (c / Real.log c ^ 2) ≤ 3.15 * (c / Real.log c ^ 2) :=
      mul_le_mul_of_nonneg_right hπ4.le hcl
    have hπ2u : π ^ 2 * (c / Real.log c ^ 2) ≤ 10 * (c / Real.log c ^ 2) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hcl
    linarith


/-! ### The tail -/

theorem continuous_sincPartial (m : ℕ) : Continuous (sincPartial m) := by
  unfold sincPartial
  exact continuous_finsetProd _ fun j _ =>
    Real.continuous_sinc.comp (continuous_const.mul continuous_id)

/-- **The Fourier tail of the sinc profile.** For all large `c`,
`∫_c^{2c} |𝓕 sincProfile|² ≥ c · exp(−(8π/3 + 3000) c/log² c)`. -/
theorem exp_mul_le_integral_norm_fourier_sincProfile_sq :
    ∀ᶠ c : ℝ in atTop, c * Real.exp (-((8 * π / 3 + 3000) * (c / Real.log c ^ 2))) ≤
      ∫ ξ in c..2 * c, ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ^ 2 := by
  filter_upwards [eventually_cut, eventually_gt_atTop 0] with c ⟨J, hJ, hb, hcS, hd⟩ hc
  have hπ := Real.pi_pos
  set S := 1 / (16 * Real.log ((J : ℝ) + 2) ^ 4 * ((J : ℝ) + 1)) with hS
  set E := Real.exp (-(16 * π ^ 2 * c ^ 2 / 3 * S)) with hE
  set u := c / Real.log c ^ 2 with hu
  have hS0 : 0 ≤ S := by
    have : 0 < Real.log ((J : ℝ) + 2) := Real.log_pos (by
      have : (1 : ℝ) ≤ J := by exact_mod_cast hJ
      linarith)
    positivity
  -- pointwise lower bound on `[c, 2c]`
  have hpt : ∀ ξ ∈ Set.Icc c (2 * c),
      sincPartial J ξ ^ 2 * E ^ 2 ≤ ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ^ 2 := by
    intro ξ hξ
    have hξ0 : 0 < ξ := by linarith [hξ.1]
    have hsmall : ∀ j, J ≤ j → 2 * π * sincRadius j * |ξ| ≤ 1 := by
      intro j hj
      have h4 := four_pi_sincRadius_mul_le hJ hb hj
      rw [abs_of_pos hξ0]
      have hr := (sincRadius_pos j).le
      nlinarith [hξ.2]
    have h := abs_sincPartial_mul_exp_le_norm_fourier hsmall (sum_sincRadius_sq_le hJ)
    have hEle : E ≤ Real.exp (-(4 * π ^ 2 * ξ ^ 2 / 3 * S)) := by
      apply Real.exp_le_exp.mpr
      have : ξ ^ 2 ≤ 4 * c ^ 2 := by nlinarith [hξ.2]
      have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 4 * π ^ 2 / 3 * S)
      nlinarith
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have h2 : |sincPartial J ξ| * E ≤ ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ :=
      (mul_le_mul_of_nonneg_left hEle (abs_nonneg _)).trans h
    have h3 := pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) hE0) h2 2
    rwa [mul_pow, sq_abs] at h3
  -- integrate
  have hcont_F : Continuous fun ξ => ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ^ 2 :=
    (HTGeometry.continuous_fourier ((contDiff_sincProfile.continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanishes sincProfile_vanishesOff)).ofReal)).norm.pow 2
  have hcont_P : Continuous fun ξ => sincPartial J ξ ^ 2 * E ^ 2 :=
    ((continuous_sincPartial J).pow 2).mul continuous_const
  have hmono : ∫ ξ in c..2 * c, sincPartial J ξ ^ 2 * E ^ 2 ≤
      ∫ ξ in c..2 * c, ‖𝓕 (fun x => (sincProfile x : ℂ)) ξ‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith) (hcont_P.intervalIntegrable _ _)
      (hcont_F.intervalIntegrable _ _) hpt
  have hprod : ∀ ξ, sincPartial J ξ ^ 2 =
      ∏ j ∈ Finset.range J, Real.sinc (2 * π * sincRadius j * ξ) ^ 2 := fun ξ => by
    rw [sincPartial, Finset.prod_pow]
  have hjensen := integral_prod_sinc_sq_ge (s := Finset.range J) (ρ := sincRadius)
    (fun j _ => sincRadius_pos j) hc
  have hfactor : ∑ j ∈ Finset.range J, ∫ ξ in c..2 * c,
      -Real.log (Real.sinc (2 * π * sincRadius j * ξ)) ≤
      c * J * Real.log 2 + 2 * Real.log 2 * J * (((J : ℝ) + 2) * Real.log ((J : ℝ) + 2) ^ 2) +
        c * (3 * Real.log ((J : ℝ) + 2) + 3 * ((J : ℝ) + 2)) :=
    (Finset.sum_le_sum fun j _ => integral_neg_log_sinc_le (sincRadius_pos j) hc).trans
      (sum_factor_bound_le hc hJ hb)
  have hD : -(2 / c) * ∑ j ∈ Finset.range J, ∫ ξ in c..2 * c,
      -Real.log (Real.sinc (2 * π * sincRadius j * ξ)) ≥ -(3000 * u) := by
    have := mul_le_mul_of_nonneg_left hfactor (by positivity : (0 : ℝ) ≤ 2 / c)
    linarith
  have hE2 : Real.exp (-(8 * π / 3 * u)) ≤ E ^ 2 := by
    rw [hE, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  calc c * Real.exp (-((8 * π / 3 + 3000) * u))
      = Real.exp (-(8 * π / 3 * u)) * (c * Real.exp (-(3000 * u))) := by
        rw [show -((8 * π / 3 + 3000) * u) = -(8 * π / 3 * u) + -(3000 * u) by ring,
          Real.exp_add]; ring
    _ ≤ E ^ 2 * (c * Real.exp (-(2 / c) * ∑ j ∈ Finset.range J, ∫ ξ in c..2 * c,
          -Real.log (Real.sinc (2 * π * sincRadius j * ξ)))) := by
        apply mul_le_mul hE2 _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hD) hc.le
    _ ≤ E ^ 2 * ∫ ξ in c..2 * c, ∏ j ∈ Finset.range J, Real.sinc (2 * π * sincRadius j * ξ) ^ 2 :=
        mul_le_mul_of_nonneg_left hjensen (by positivity)
    _ = ∫ ξ in c..2 * c, sincPartial J ξ ^ 2 * E ^ 2 := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1; funext ξ; rw [hprod]; ring
    _ ≤ _ := hmono

end GaloisForLFunctions.TransMetzlerWeilPositivity
