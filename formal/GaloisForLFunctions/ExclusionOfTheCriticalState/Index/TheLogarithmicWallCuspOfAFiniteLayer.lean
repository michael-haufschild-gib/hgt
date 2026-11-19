import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheMeanSquareWallTraceOfAFiniteLayer
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheHighFrequencyMassOfAFiniteLayer
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalLineCuspOfTheGroundState
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheModulusOfContinuityOfEveryConfinedGroundStateIsCarriedByTheWall

/-!
# The logarithmic wall cusp and critical-line ordinate moments of a finite layer

For a half-line profile `F` whose terminal square mass obeys the logarithmic cusp law
`(log(1/h)/h) ∫_{-h}^0 F(u)² du → Q`, Tonelli's theorem and dominated convergence yield the
exact Abelian law `(x log x) ∫_0^∞ e^{-2xv} F(-v)² dv → Q / 2`, and vertical Plancherel gives
`(x log x) ∫_ℝ ‖L F(x + iy)‖² dy → π Q`. Applied to confined ground states (`Q = 8 a M`), a single
logarithm separates the ground-state vertical trace from the `o(1/x)` finite-layer bound of
`IsConfinedNullVector.abel_square_wall_limit`.

For the threshold ground state `F` of `ζ`, the weighted increment law
`∫ (F(u) - F(u+h))² e^{-8u} du = o(h)` implies that the continuous boundary Fourier tail on
`Re w = -4` is `o(1/T)` above height `T`, and its first absolute frequency moment on `[-T, T]` is
`o(log T)`. Combining this with `IsConfinedNullVector.localized_high_frequency_mass` isolates the
exact high-frequency tail and logarithmic first moment of the critical-line zero samples under
`FiniteOffLine`:

* `T · ∑_{|γ_q| > T} ‖L F(iγ_q)‖² → 8 a M / π`;
* `(log T)⁻¹ · ∑_{|γ_q| ≤ T} |γ_q| ‖L F(iγ_q)‖² → 8 a M / π`.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23
open scoped ComplexConjugate ENNReal NNReal
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Exact logarithmic Abel and vertical-line square-mass laws -/

private theorem integral_Ioi_exp_neg {a : ℝ} :
    (∫ t in Ioi a, Real.exp (-t)) = Real.exp (-a) := by
  let g : ℝ → ℝ := fun x => -Real.exp (-x)
  have hd : ∀ t ∈ Ioi a, HasDerivAt g (Real.exp (-t)) t := fun t _ => by
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t :=
      (hasDerivAt_neg t).exp.congr_deriv (by ring)
    exact h1.neg.congr_deriv (neg_neg _)
  have hi : IntegrableOn (fun t => Real.exp (-t)) (Ioi a) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := -1) neg_one_lt_zero a
  have hc : ContinuousWithinAt g (Ici a) a := by unfold g; fun_prop
  have hlim : Tendsto g atTop (𝓝 0) := by
    simpa [g] using Real.tendsto_exp_neg_atTop_nhds_zero.neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd hi hlim]
  dsimp only [g]
  ring

private theorem mul_exp_neg_le_two_exp_neg_half {t : ℝ} (ht : 0 ≤ t) :
    t * Real.exp (-t) ≤ 2 * Real.exp (-(t / 2)) := by
  have hle : t / 2 ≤ Real.exp (t / 2) := by linarith only [Real.add_one_le_exp (t / 2)]
  have hm := mul_le_mul_of_nonneg_right hle (Real.exp_pos (-(t / 2))).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  have hexp : t * Real.exp (-t) = 2 * ((t / 2) * Real.exp (-(t / 2))) * Real.exp (-(t / 2)) := by
    rw [mul_assoc, mul_assoc, ← Real.exp_add, show -(t / 2) + -(t / 2) = -t by ring]
    ring
  rw [hexp]
  have _ := ht
  nlinarith only [hm, mul_le_mul_of_nonneg_right hm (Real.exp_pos (-(t / 2))).le,
    Real.exp_pos (-(t / 2))]

private theorem pow_four_mul_exp_neg_le {t : ℝ} (ht : 0 ≤ t) :
    t ^ 4 * Real.exp (-t) ≤ 4096 * Real.exp (-(t / 2)) := by
  have h1 : t / 8 ≤ Real.exp (t / 8) := by linarith only [Real.add_one_le_exp (t / 8)]
  have h4 : (t / 8) ^ 4 ≤ Real.exp (t / 8) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
  rw [← Real.exp_nat_mul, show ((4 : ℕ) : ℝ) * (t / 8) = t / 2 by push_cast; ring] at h4
  have ht4 : t ^ 4 ≤ 4096 * Real.exp (t / 2) := by
    have e : (t / 8) ^ 4 = t ^ 4 / 4096 := by ring
    rw [e, div_le_iff₀ (by norm_num)] at h4
    linarith only [h4]
  calc t ^ 4 * Real.exp (-t)
      ≤ 4096 * Real.exp (t / 2) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right ht4 (Real.exp_pos _).le
    _ = 4096 * Real.exp (-(t / 2)) := by
        rw [mul_assoc, ← Real.exp_add, show t / 2 + -t = -(t / 2) by ring]

private theorem integral_Ioi_mul_exp_neg :
    (∫ t in Ioi (0 : ℝ), t * Real.exp (-t)) = 1 := by
  let f : ℝ → ℝ := fun t => -(t + 1) * Real.exp (-t)
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (t * Real.exp (-t)) t := fun t _ => by
    have h1 : HasDerivAt (fun x : ℝ => -(x + 1)) (-1) t :=
      (((hasDerivAt_id t).add_const (1 : ℝ)).neg : HasDerivAt (fun x : ℝ => -(x + 1)) (-1) t)
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t :=
      (hasDerivAt_neg t).exp.congr_deriv (by ring)
    exact (h1.mul h2).congr_deriv (by ring)
  have hi : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi 0) := by
    refine (integrableOn_exp_neg_half.const_mul 2).mono'
      (by fun_prop : Measurable fun t : ℝ => t * Real.exp (-t)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [Real.norm_of_nonneg (mul_nonneg ht.le (Real.exp_pos _).le)]
    exact mul_exp_neg_le_two_exp_neg_half ht.le
  have h0 : Tendsto (fun t : ℝ => 4 * Real.exp (-(t / 2))) atTop (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => Real.exp (-(t / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const two_pos)
    simpa only [mul_zero] using he.const_mul 4
  have hlim : Tendsto f atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    dsimp only [f]
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by linarith), abs_of_pos (Real.exp_pos _)]
    have hle := mul_exp_neg_le_two_exp_neg_half ht
    have he : Real.exp (-t) ≤ Real.exp (-(t / 2)) := Real.exp_le_exp.mpr (by linarith)
    have hsplit : (t + 1) * Real.exp (-t) = t * Real.exp (-t) + Real.exp (-t) := add_one_mul t _
    linarith only [hle, he, hsplit, Real.exp_pos (-(t / 2))]
  have hc : ContinuousWithinAt f (Ici 0) 0 := by unfold f; fun_prop
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd hi hlim]
  simp [f]

private theorem dampedMass_eq_scaled_terminal {F : ℝ → ℝ} (hFm : Measurable F)
    (hF2 : Integrable fun u => F u ^ 2) {x : ℝ} (hx : 0 < x) :
    (∫ v in Ioi (0 : ℝ), Real.exp (-(2 * x * v)) * F (-v) ^ 2) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ∫ u in Ioo (-(t / (2 * x))) 0, F u ^ 2 := by
  let f : ℝ → ℝ := fun v => F (-v) ^ 2
  have hfm : Measurable f := (hFm.comp measurable_neg).pow_const 2
  have hf : Integrable f :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable hF2
  let g1 : ℝ → ℝ := (Ioi (0 : ℝ)).indicator f
  let g2 : ℝ → ℝ := (Ioi (0 : ℝ)).indicator fun t => Real.exp (-t)
  have hg1 : Integrable g1 := hf.integrableOn.integrable_indicator measurableSet_Ioi
  have hg2 : Integrable g2 := by
    have hi : IntegrableOn (fun t => Real.exp (-t)) (Ioi (0 : ℝ)) := by
      simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := -1) neg_one_lt_zero 0
    exact hi.integrable_indicator measurableSet_Ioi
  let K : ℝ → ℝ → ℝ := fun v t =>
    if 0 < v ∧ 2 * x * v < t then Real.exp (-t) * f v else 0
  have hKm : Measurable (Function.uncurry K) := by
    refine Measurable.ite ?_
      ((Real.continuous_exp.comp continuous_snd.neg).measurable.mul (hfm.comp measurable_fst))
      measurable_const
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt (measurable_const.mul measurable_fst) measurable_snd)
  have hprod : Integrable (Function.uncurry K) (volume.prod volume) := by
    refine (hg1.mul_prod hg2).mono' hKm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    dsimp only [Function.uncurry, K, g1, g2]
    split_ifs with h
    · have ht0 : 0 < p.2 := lt_trans (mul_pos (mul_pos two_pos hx) h.1) h.2
      rw [indicator_of_mem (mem_Ioi.mpr h.1), indicator_of_mem (mem_Ioi.mpr ht0),
        Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)), mul_comm]
    · rw [norm_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ => sq_nonneg _) _)
        (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
  have hswap := integral_integral_swap hprod
  have hL : (∫ v, ∫ t, K v t) = ∫ v in Ioi (0 : ℝ), Real.exp (-(2 * x * v)) * f v := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    dsimp only
    by_cases hv : 0 < v
    · rw [indicator_of_mem (mem_Ioi.mpr hv)]
      have heq : (fun t => K v t) = (Ioi (2 * x * v)).indicator (fun t => Real.exp (-t) * f v) := by
        funext t; simp only [K, hv, true_and, indicator, mem_Ioi]
      rw [show (∫ t, K v t) = ∫ t, (Ioi (2 * x * v)).indicator (fun t => Real.exp (-t) * f v) t from
        congrArg (fun h : ℝ → ℝ => ∫ t, h t) heq, integral_indicator measurableSet_Ioi,
        integral_mul_const, integral_Ioi_exp_neg]
    · rw [indicator_of_notMem (by simpa using hv)]
      have heq : (fun t => K v t) = fun _ => 0 := by funext t; simp [K, hv]
      rw [show (∫ t, K v t) = ∫ _ : ℝ, (0 : ℝ) from congrArg (fun h : ℝ → ℝ => ∫ t, h t) heq,
        integral_zero]
  have hR : (∫ t, ∫ v, K v t) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ∫ u in Ioo (-(t / (2 * x))) 0, F u ^ 2 := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    by_cases ht : 0 < t
    · rw [indicator_of_mem (mem_Ioi.mpr ht)]
      have heq : (fun v => K v t) = (Ioo 0 (t / (2 * x))).indicator (fun v => Real.exp (-t) * f v) := by
        funext v
        unfold K indicator
        have hiff : (2 * x * v < t) ↔ (v < t / (2 * x)) :=
          (lt_div_iff₀' (mul_pos two_pos hx)).symm
        simp only [mem_Ioo, hiff]
      rw [show (∫ v, K v t) = ∫ v, (Ioo 0 (t / (2 * x))).indicator (fun v => Real.exp (-t) * f v) v
        from congrArg (fun h : ℝ → ℝ => ∫ v, h v) heq, integral_indicator measurableSet_Ioo,
        integral_const_mul, ← integral_reflect_initial_interval (fun u => F u ^ 2) (t / (2 * x))]
    · rw [indicator_of_notMem (by simpa using ht)]
      have heq : (fun v => K v t) = fun _ => 0 := by
        funext v; unfold K
        split_ifs with h
        · exfalso; linarith [mul_pos (mul_pos two_pos hx) h.1, h.2]
        · rfl
      rw [show (∫ v, K v t) = ∫ _ : ℝ, (0 : ℝ) from congrArg (fun h : ℝ → ℝ => ∫ v, h v) heq,
        integral_zero]
  rw [← hL, hswap, hR]

/-- **Logarithmic Abelian theorem at the wall.** If `(log(1/h)/h) ∫_{-h}^0 F(u)² du → Q` as
`h → 0⁺` for a square-integrable profile `F`, then
`(x log x) ∫_0^∞ e^{-2xv} F(-v)² dv → Q / 2` as `x → +∞`. -/
theorem tendsto_mul_log_dampedMass_of_terminal_sq {F : ℝ → ℝ}
    (hFm : Measurable F) (hF2 : Integrable fun u => F u ^ 2) {Q : ℝ}
    (hlim : Tendsto (fun h : ℝ => Real.log (1 / h) / h * ∫ u in Ioo (-h) 0, F u ^ 2)
      (𝓝[>] 0) (𝓝 Q)) :
    Tendsto (fun x : ℝ => (x * Real.log x) * ∫ v in Ioi (0 : ℝ), Real.exp (-(2 * x * v)) * F (-v) ^ 2)
      atTop (𝓝 (Q / 2)) := by
  let S : ℝ → ℝ := fun h => ∫ u in Ioo (-(max h 0)) 0, F u ^ 2
  have hS_mono : Monotone S := fun h₁ h₂ h12 => by
    refine setIntegral_mono_set hF2.integrableOn (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun u (hu : -(max h₁ 0) < u ∧ u < 0) => ?_)
    exact ⟨lt_of_le_of_lt (neg_le_neg (max_le_max_right 0 h12)) hu.1, hu.2⟩
  have hSm : Measurable S := hS_mono.measurable
  have hS_eq : ∀ {h : ℝ}, 0 ≤ h → S h = ∫ u in Ioo (-h) 0, F u ^ 2 := fun hh => by
    simp only [S, max_eq_left hh]
  let M₀ : ℝ := ∫ u, F u ^ 2
  have hM₀ : 0 ≤ M₀ := integral_nonneg fun _ => sq_nonneg _
  have hS0 : ∀ h, 0 ≤ S h := fun _ => integral_nonneg fun _ => sq_nonneg _
  have hSM : ∀ h, S h ≤ M₀ := fun h =>
    setIntegral_le_integral hF2 (Eventually.of_forall fun _ => sq_nonneg _)
  have hQ0 : 0 ≤ Q := ge_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with h hh0 hh1
    have hh0' : (0 : ℝ) < h := hh0
    have hh1' : h < 1 := hh1
    exact mul_nonneg (div_nonneg (Real.log_nonneg (by rw [le_div_iff₀ hh0']; linarith)) hh0'.le)
      (integral_nonneg fun _ => sq_nonneg _))
  obtain ⟨δ₁, hδ₁, hnear⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim 1 zero_lt_one
  set δ := min (δ₁ / 2) (1 / 4)
  have hδ0 : 0 < δ := lt_min (half_pos hδ₁) (by norm_num)
  have hδ_lt : δ < δ₁ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ₁)
  have hS_bound : ∀ {h : ℝ}, 0 < h → h ≤ δ → Real.log (1 / h) / h * S h ≤ Q + 1 := by
    intro h hh0 hhδ
    have hd : dist h 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hh0]
      exact lt_of_le_of_lt hhδ hδ_lt
    have h1 := hnear hh0 hd
    rw [Real.dist_eq, ← hS_eq hh0.le] at h1
    linarith [(abs_lt.mp h1).2]
  let g : ℝ → ℝ → ℝ := fun x t => (2 * x * Real.log x) * Real.exp (-t) * S (t / (2 * x))
  let B : ℝ → ℝ := fun t => (4 * (Q + 1) + 8192 * M₀) * Real.exp (-(t / 2))
  have hBi : IntegrableOn B (Ioi 0) := integrableOn_exp_neg_half.const_mul _
  have hdom : Tendsto (fun x => ∫ t in Ioi (0 : ℝ), g x t) atTop
      (𝓝 (∫ t in Ioi (0 : ℝ), Q * (t * Real.exp (-t)))) := by
    refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hBi ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _
      exact (((continuous_const.mul (Real.continuous_exp.comp continuous_neg)).measurable.mul
        (hSm.comp (measurable_id.div_const (2 * x)))).aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop (max 16 (1 / δ ^ 2))] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      have hx16 : 16 ≤ x := (le_max_left _ _).trans hx
      have hxδ : 1 / δ ^ 2 ≤ x := (le_max_right _ _).trans hx
      have hx0 : 0 < x := by linarith
      have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      have hgnn : 0 ≤ g x t := mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (hS0 _)
      rw [Real.norm_of_nonneg hgnn]
      rcases le_or_gt t (Real.sqrt x) with hts | hts
      · set h := t / (2 * x)
        have hh0 : 0 < h := div_pos ht (by positivity)
        have hδ_inv : 1 / Real.sqrt x ≤ δ := by
          have h1 : 1 ≤ x * δ ^ 2 := (div_le_iff₀ (pow_pos hδ0 2)).mp hxδ
          have h2 : 1 ≤ Real.sqrt (x * δ ^ 2) := Real.one_le_sqrt.mpr h1
          rw [Real.sqrt_mul hx0.le, Real.sqrt_sq hδ0.le] at h2
          exact (div_le_iff₀' (Real.sqrt_pos.mpr hx0)).mpr h2
        have hhδ : h ≤ δ := by
          calc h ≤ Real.sqrt x / (2 * x) := div_le_div_of_nonneg_right hts (by positivity)
            _ = 1 / (2 * Real.sqrt x) := by
                rw [div_eq_div_iff (by positivity) (by positivity)]
                have := Real.mul_self_sqrt hx0.le; nlinarith
            _ ≤ 1 / Real.sqrt x :=
                one_div_le_one_div_of_le (Real.sqrt_pos.mpr hx0) (by linarith [Real.sqrt_pos.mpr hx0])
            _ ≤ δ := hδ_inv
        have h1h : Real.sqrt x ≤ 1 / h := by
          rw [one_div_div]
          calc Real.sqrt x ≤ 2 * Real.sqrt x := by linarith [Real.sqrt_pos.mpr hx0]
            _ = 2 * x / Real.sqrt x := by
                rw [eq_div_iff (Real.sqrt_pos.mpr hx0).ne']
                have := Real.mul_self_sqrt hx0.le; nlinarith
            _ ≤ 2 * x / t := div_le_div_of_nonneg_left (by positivity) ht hts
        have hlog1h : Real.log x / 2 ≤ Real.log (1 / h) := by
          have hl := Real.log_le_log (Real.sqrt_pos.mpr hx0) h1h
          rwa [Real.log_sqrt hx0.le] at hl
        have hlog_pos : 0 < Real.log (1 / h) := by
          have hl4 : 0 < Real.log 16 := Real.log_pos (by norm_num)
          have hlx : Real.log 16 ≤ Real.log x := Real.log_le_log (by norm_num) hx16
          linarith
        have hrat : Real.log x / Real.log (1 / h) ≤ 2 :=
          (div_le_iff₀ hlog_pos).mpr (by linarith)
        have hSb := hS_bound hh0 hhδ
        set Lh := Real.log (1 / h)
        have hLh_ne : Lh ≠ 0 := hlog_pos.ne'
        have hid : g x t = (t * Real.exp (-t)) * (Real.log x / Lh) * (Lh / h * S h) := by
          change (2 * x * Real.log x) * Real.exp (-t) * S h =
            (t * Real.exp (-t)) * (Real.log x / Lh) * (Lh / (t / (2 * x)) * S h)
          field_simp [hLh_ne, hx0.ne', ht.ne']
        rw [hid]
        have hp1 : (Real.log x / Lh) * (Lh / h * S h) ≤
            2 * (Q + 1) := mul_le_mul hrat hSb (mul_nonneg (div_nonneg hlog_pos.le hh0.le) (hS0 h))
              two_pos.le
        have hp2 := mul_exp_neg_le_two_exp_neg_half ht.le
        calc (t * Real.exp (-t)) * (Real.log x / Lh) * (Lh / h * S h)
            = (t * Real.exp (-t)) * ((Real.log x / Lh) * (Lh / h * S h)) := by ring
          _ ≤ (2 * Real.exp (-(t / 2))) * (2 * (Q + 1)) :=
              mul_le_mul hp2 hp1 (mul_nonneg (div_nonneg hlogx hlog_pos.le)
                (mul_nonneg (div_nonneg hlog_pos.le hh0.le) (hS0 h))) (by positivity)
          _ ≤ B t := by
              dsimp only [B]
              nlinarith [mul_nonneg hM₀ (Real.exp_pos (-(t / 2))).le]
      · have hxt2 : x ≤ t ^ 2 := by
          have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg x) hts.le 2
          rwa [Real.sq_sqrt hx0.le] at h2
        have hlog_le : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
        have hxlog : 2 * x * Real.log x ≤ 2 * t ^ 4 := by
          have hx2 : x * Real.log x ≤ x ^ 2 := by nlinarith [hx0]
          have ht4 : x ^ 2 ≤ t ^ 4 := by
            have := pow_le_pow_left₀ hx0.le hxt2 2
            linarith [show (t ^ 2) ^ 2 = t ^ 4 by ring]
          linarith
        have hp4 := pow_four_mul_exp_neg_le ht.le
        calc g x t
            ≤ (2 * t ^ 4) * Real.exp (-t) * M₀ := by
              dsimp only [g]
              exact mul_le_mul (mul_le_mul_of_nonneg_right hxlog (Real.exp_pos _).le)
                (hSM _) (hS0 _) (by positivity)
          _ = 2 * M₀ * (t ^ 4 * Real.exp (-t)) := by ring
          _ ≤ 2 * M₀ * (4096 * Real.exp (-(t / 2))) :=
              mul_le_mul_of_nonneg_left hp4 (by positivity)
          _ ≤ B t := by
              dsimp only [B]
              nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Q + 1) (Real.exp_pos (-(t / 2))).le]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      have hh_tend : Tendsto (fun x : ℝ => t / (2 * x)) atTop (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have h0 : Tendsto (fun x : ℝ => t * (2⁻¹ * x⁻¹)) atTop (𝓝 0) := by
            simpa only [mul_zero] using
              ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2⁻¹ : ℝ)).const_mul t
          exact h0.congr fun x => by ring
        · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx using div_pos ht (by positivity)
      have hS_tend : Tendsto (fun x : ℝ =>
          Real.log (1 / (t / (2 * x))) / (t / (2 * x)) * S (t / (2 * x))) atTop (𝓝 Q) := by
        refine (hlim.comp hh_tend).congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        dsimp only [Function.comp_apply]
        rw [hS_eq (div_pos ht (by positivity)).le]
      have hrat_tend : Tendsto (fun x : ℝ => Real.log x / Real.log (1 / (t / (2 * x))))
          atTop (𝓝 1) := by
        have h1 : Tendsto (fun x : ℝ => (1 + Real.log (2 / t) * (Real.log x)⁻¹)⁻¹)
            atTop (𝓝 1) := by
          have hz : Tendsto (fun x : ℝ => Real.log (2 / t) * (Real.log x)⁻¹) atTop (𝓝 0) := by
            simpa using ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp Real.tendsto_log_atTop).const_mul
              (Real.log (2 / t))
          simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add hz).inv₀ (by norm_num)
        refine h1.congr' ?_
        filter_upwards [eventually_gt_atTop (max 2 (t + 1))] with x hx
        have hx2 : 2 < x := lt_of_le_of_lt (le_max_left _ _) hx
        have hxt : t < x := by linarith [lt_of_le_of_lt (le_max_right 2 (t + 1)) hx]
        have hx0 : 0 < x := by linarith
        have hlx : Real.log x ≠ 0 := (Real.log_pos (by linarith)).ne'
        have hlog_eq : Real.log (1 / (t / (2 * x))) = Real.log x + Real.log (2 / t) := by
          rw [one_div_div, show 2 * x / t = x * (2 / t) by ring,
            Real.log_mul hx0.ne' (div_pos two_pos ht).ne']
        have hden : Real.log x + Real.log (2 / t) ≠ 0 := by
          have : 1 < 2 * x / t := (lt_div_iff₀ ht).mpr (by linarith)
          have hpos := Real.log_pos this
          rw [← one_div_div, hlog_eq] at hpos
          exact hpos.ne'
        rw [hlog_eq]
        field_simp [hlx, hden]
      have hprod_tend := ((tendsto_const_nhds (x := t * Real.exp (-t))).mul hrat_tend).mul hS_tend
      have heq_lim : t * Real.exp (-t) * 1 * Q = Q * (t * Real.exp (-t)) := by ring
      rw [heq_lim] at hprod_tend
      refine hprod_tend.congr' ?_
      filter_upwards [eventually_gt_atTop (max 2 (t + 1))] with x hx
      have hx2 : 2 < x := lt_of_le_of_lt (le_max_left _ _) hx
      have hxt : t < x := by linarith [lt_of_le_of_lt (le_max_right 2 (t + 1)) hx]
      have hx0 : 0 < x := by linarith
      set Lh := Real.log (1 / (t / (2 * x)))
      have hden : Lh ≠ 0 := by
        dsimp only [Lh]
        rw [one_div_div]
        exact (Real.log_pos ((lt_div_iff₀ ht).mpr (by linarith))).ne'
      change t * Real.exp (-t) * (Real.log x / Lh) * (Lh / (t / (2 * x)) * S (t / (2 * x))) =
        (2 * x * Real.log x) * Real.exp (-t) * S (t / (2 * x))
      field_simp [hden, hx0.ne', ht.ne']
  rw [integral_const_mul, integral_Ioi_mul_exp_neg, mul_one] at hdom
  have hhalf := hdom.div_const 2
  refine hhalf.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [dampedMass_eq_scaled_terminal hFm hF2 hx]
  have heq : (∫ t in Ioi (0 : ℝ), g x t) =
      (2 * x * Real.log x) * ∫ t in Ioi (0 : ℝ), Real.exp (-t) *
        ∫ u in Ioo (-(t / (2 * x))) 0, F u ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    dsimp only [g]
    rw [hS_eq (div_pos ht (by positivity)).le]
    ring
  rw [heq]
  ring

/-- Vertical Plancherel transfers the logarithmic wall cusp to `(x log x) ∫_ℝ ‖L F(x + iy)‖² dy → π Q`. -/
theorem tendsto_mul_log_vertical_laplace_sq_of_terminal_sq {F : ℝ → ℝ}
    (hd : CriticalHalfLineEnergyDomain F) {Q : ℝ}
    (hlim : Tendsto (fun h : ℝ => Real.log (1 / h) / h * ∫ u in Ioo (-h) 0, F u ^ 2)
      (𝓝[>] 0) (𝓝 Q)) :
    Tendsto (fun x : ℝ => (x * Real.log x) *
      ∫ y : ℝ, ‖negativeHalfLineLaplace (cx F) (hardyVerticalLine x y)‖ ^ 2)
      atTop (𝓝 (Real.pi * Q)) := by
  have h1 := (tendsto_mul_log_dampedMass_of_terminal_sq hd.meas hd.sq hlim).const_mul (2 * Real.pi)
  rw [show 2 * Real.pi * (Q / 2) = Real.pi * Q by ring] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hi : Integrable (cx F) := hd.integrable.ofReal
  have h2 : MemLp (cx F) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mpr
      (by simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hd.sq)
  have hs : ∀ u : ℝ, 0 ≤ u → cx F u = 0 := fun u hu => by simp [cx, hd.support u hu]
  have hline : (∫ y : ℝ, ‖negativeHalfLineLaplace (cx F) (hardyVerticalLine x y)‖ ^ 2) =
      2 * Real.pi * ∫ v in Ioi (0 : ℝ), Real.exp (-(2 * x * v)) * F (-v) ^ 2 := by
    simp_rw [negativeHalfLineLaplace_eq_laplaceRay_reflect _ hs]
    simpa only [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      integral_norm_sq_laplaceRay_vertical (memLp_reflected_negativeProfile h2) hx
  rw [hline]
  ring

/-- Every confined half-line energy minimizer at ratio `R > 0` has exact logarithmic Abel square mass
`4 a(R) ∫ F² e^{-8u}`, unconditional on any zero-divisor hypothesis. -/
theorem halfLineEnergyMinimizer_tendsto_mul_log_dampedMass {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    Tendsto (fun x : ℝ => (x * Real.log x) * ∫ v in Ioi (0 : ℝ), Real.exp (-(2 * x * v)) * F (-v) ^ 2)
      atTop (𝓝 (4 * criticalAliasCoefficient R * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) := by
  have h := tendsto_mul_log_dampedMass_of_terminal_sq hF.1.meas hF.1.sq
    (halfLineEnergyMinimizer_tendsto_log_div_mul_terminal_sq hR hF)
  rwa [show 8 * criticalAliasCoefficient R * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / 2 =
    4 * criticalAliasCoefficient R * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) by ring] at h

/-- Every confined half-line energy minimizer at ratio `R > 0` has exact logarithmic vertical-line
Laplace trace `8 π a(R) ∫ F² e^{-8u}`. -/
theorem halfLineEnergyMinimizer_tendsto_mul_log_vertical_laplace_sq {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    Tendsto (fun x : ℝ => (x * Real.log x) *
      ∫ y : ℝ, ‖negativeHalfLineLaplace (cx F) (hardyVerticalLine x y)‖ ^ 2)
      atTop (𝓝 (8 * Real.pi * criticalAliasCoefficient R *
        ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) := by
  have h := tendsto_mul_log_vertical_laplace_sq_of_terminal_sq hF.1
    (halfLineEnergyMinimizer_tendsto_log_div_mul_terminal_sq hR hF)
  rwa [show Real.pi * (8 * criticalAliasCoefficient R * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) =
    8 * Real.pi * criticalAliasCoefficient R * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) by ring] at h

/-- Every confined half-line energy minimizer at ratio `R > 0` has vanishing unscaled mean-square wall
trace `h⁻¹ ∫_{-h}^0 F(u)² du → 0`. -/
theorem halfLineEnergyMinimizer_mean_square_wall_trace_zero {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsHalfLineEnergyMinimizer R F) :
    Tendsto (fun h : ℝ => (∫ u in Ioo (-h) 0, F u ^ 2) / h) (𝓝[>] 0) (𝓝 0) := by
  have hcusp := halfLineEnergyMinimizer_tendsto_log_div_mul_terminal_sq hR hF
  have hinv_log : Tendsto (fun h : ℝ => (Real.log (1 / h))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have hcomp := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
      (Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)))
    exact hcomp.congr fun h => by simp [one_div]
  have hprod := hcusp.mul hinv_log
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with h hh0 hh2
  have hh0' : (0 : ℝ) < h := hh0
  have hh2' : h < 1 / 2 := hh2
  have hlog : Real.log (1 / h) ≠ 0 :=
    (Real.log_pos (by rw [lt_div_iff₀ hh0']; linarith)).ne'
  field_simp [hlog, hh0'.ne']

/-- For a threshold critical state `F`, `(x log x) ∫_0^∞ e^{-2xv} F(-v)² dv → 4 a M` as `x → +∞`. -/
theorem criticalState_tendsto_mul_log_dampedMass {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun x : ℝ => (x * Real.log x) * ∫ v in Ioi (0 : ℝ), Real.exp (-(2 * x * v)) * F (-v) ^ 2)
      atTop (𝓝 (4 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h := tendsto_mul_log_dampedMass_of_terminal_sq hd.meas hd.sq
    (criticalState_tendsto_log_div_mul_terminal_sq hW ht hF)
  rwa [show 8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / 2 =
    4 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) by ring] at h

/-- For a threshold critical state `F`, `(x log x) ∫_ℝ ‖L F(x + iy)‖² dy → 8 π a M` as `x → +∞`. -/
theorem criticalState_tendsto_mul_log_vertical_laplace_sq {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun x : ℝ => (x * Real.log x) *
      ∫ y : ℝ, ‖negativeHalfLineLaplace (cx F) (hardyVerticalLine x y)‖ ^ 2)
      atTop (𝓝 (8 * Real.pi * criticalAliasCoefficient W₀ *
        ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h := tendsto_mul_log_vertical_laplace_sq_of_terminal_sq hd
    (criticalState_tendsto_log_div_mul_terminal_sq hW ht hF)
  rwa [show Real.pi * (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) =
    8 * Real.pi * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) by ring] at h

/-! ### Vanishing of the continuous boundary Fourier tail on `Re w = -4` -/

private def boundaryTilt (F : ℝ → ℝ) (u : ℝ) : ℝ := Real.exp (-(4 * u)) * F u

private theorem integrable_boundaryTilt {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) : Integrable (boundaryTilt F) := by
  have ht := hF.tilt_domain hr zero_le_one le_rfl
  have hi := integrable_cexp_neg_mul_cx ht (show ((3 : ℂ)).re < 4 by norm_num)
  refine hi.re.congr (Eventually.of_forall fun u => ?_)
  dsimp only [cx, boundaryTilt]
  rw [show (-3 : ℂ) * (u : ℂ) = (((-(3 * u)) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  change ((((Real.exp (-(3 * u)) * (Real.exp (-(1 * u)) * F u)) : ℝ) : ℂ)).re =
    Real.exp (-(4 * u)) * F u
  rw [Complex.ofReal_re, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem integrable_sq_boundaryTilt {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F) :
    Integrable fun u => boundaryTilt F u ^ 2 := by
  refine hd.exponential.congr (Eventually.of_forall fun u => ?_)
  dsimp only [boundaryTilt]
  rw [mul_pow, ← Real.exp_nat_mul]
  push_cast
  ring

private theorem laplace_neg_four_eq_paperFT {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    (y : ℝ) :
    negativeHalfLineLaplace (cx F) ⟨-4, y⟩ = paperFT (cx (boundaryTilt F)) y := by
  have hw : (⟨-4, y⟩ : ℂ) = ((-4 : ℝ) : ℂ) + (y : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hw, negativeHalfLineLaplace_add_mul_I_eq_paperFT hd.support]
  congr 2
  funext u
  rcases le_total u 0 with hu | hu
  · simp only [min_eq_left hu, boundaryTilt, neg_mul]
  · simp only [hd.support u hu, boundaryTilt, mul_zero]

private theorem integral_one_sub_cos_boundary {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (h : ℝ) :
    (∫ y : ℝ, (1 - Real.cos (h * y)) * ‖negativeHalfLineLaplace (cx F) ⟨-4, y⟩‖ ^ 2) =
      Real.pi * ∫ u : ℝ, (boundaryTilt F u - boundaryTilt F (u + h)) ^ 2 := by
  let G := boundaryTilt F
  have hGi := integrable_boundaryTilt hr hF
  have hG2 := integrable_sq_boundaryTilt hF.1
  have hGm : Measurable G := (by fun_prop : Measurable fun u => Real.exp (-(4 * u))).mul hF.1.meas
  let D : ℝ → ℝ := fun u => G u + (-1) * G (u + h)
  have hDi : Integrable D := hGi.add ((hGi.comp_add_right h).const_mul (-1))
  have hD2 : Integrable fun u => D u ^ 2 := by
    have hsum : Integrable fun u => 2 * G u ^ 2 + 2 * G (u + h) ^ 2 :=
      (hG2.const_mul 2).add ((hG2.comp_add_right h).const_mul 2)
    refine hsum.mono' (((hGm.add ((hGm.comp (measurable_id.add_const h)).const_mul (-1)))).pow_const
      2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    dsimp only [D]
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith only [sq_nonneg (G u + G (u + h))]
  have hpl := KernelStrip.integral_norm_sq_paperFT_of_memLp (h := cx D)
    (hDi.ofReal (𝕜 := ℂ)) (memLp_cx_of_sq hDi hD2)
  have hL : (∫ y : ℝ, ‖paperFT (cx D) y‖ ^ 2) =
      2 * ∫ y : ℝ, (1 - Real.cos (h * y)) * ‖negativeHalfLineLaplace (cx F) ⟨-4, y⟩‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [laplace_neg_four_eq_paperFT hF.1 y]
    exact norm_sq_paperFT_increment hGi h y
  have hR : (∫ u : ℝ, ‖cx D u‖ ^ 2) = ∫ u : ℝ, (G u - G (u + h)) ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only [cx, D]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  rw [hL, hR] at hpl
  linarith only [hpl]

private theorem tendsto_boundaryTilt_sq_increment_div {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun h : ℝ => (∫ u : ℝ, (boundaryTilt F u - boundaryTilt F (u + h)) ^ 2) / h)
      (𝓝[>] 0) (𝓝 0) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hG2 := integrable_sq_boundaryTilt hd
  have hGm : Measurable (boundaryTilt F) :=
    (by fun_prop : Measurable fun u => Real.exp (-(4 * u))).mul hd.meas
  let M : ℝ := ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))
  have hlim1 := (criticalState_tendsto_weighted_sq_increment_div hW ht hF).const_mul 2
  have hlim2 : Tendsto (fun h : ℝ => 32 * Real.exp 8 * M * h) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun h : ℝ => 32 * Real.exp 8 * M * id h) (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left nhdsWithin_le_nhds).const_mul (32 * Real.exp 8 * M)
    exact h0.congr fun _ => rfl
  have hsum := hlim1.add hlim2
  rw [mul_zero, add_zero] at hsum
  refine squeeze_zero' ?_ ?_ hsum
  · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    exact div_nonneg (integral_nonneg fun _ => sq_nonneg _) hh.le
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with h hh0 hh1
    have hh0' : (0 : ℝ) < h := hh0
    have hh1' : h < 1 := hh1
    let r := Real.exp (-(4 * h))
    have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h1mr : (1 - r) ^ 2 ≤ 16 * h ^ 2 := by
      have hle : 1 - r ≤ 4 * h := by linarith [Real.add_one_le_exp (-(4 * h))]
      have hsq := pow_le_pow_left₀ (sub_nonneg.mpr hr1) hle 2
      linarith [show (4 * h) ^ 2 = 16 * h ^ 2 by ring]
    have hiL : Integrable fun u => (boundaryTilt F u - boundaryTilt F (u + h)) ^ 2 := by
      have hsum' : Integrable fun u => 2 * boundaryTilt F u ^ 2 + 2 * boundaryTilt F (u + h) ^ 2 :=
        (hG2.const_mul 2).add ((hG2.comp_add_right h).const_mul 2)
      refine hsum'.mono' ((hGm.sub (hGm.comp (measurable_id.add_const h))).pow_const
        2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith only [sq_nonneg (boundaryTilt F u + boundaryTilt F (u + h))]
    have hi1 : Integrable fun u => 2 * ((F u - F (u + h)) ^ 2 * Real.exp (-(8 * u))) :=
      ((criticalHalfLineEnergyDomain_increment hd hh0'.le).exponential.congr
        (Eventually.of_forall fun u => by ring)).const_mul 2
    have hi2 : Integrable fun u =>
        32 * Real.exp 8 * h ^ 2 * (F (u + h) ^ 2 * Real.exp (-(8 * (u + h)))) :=
      (hd.exponential.comp_add_right h).const_mul _
    have hpt : ∀ u : ℝ, (boundaryTilt F u - boundaryTilt F (u + h)) ^ 2 ≤
        2 * ((F u - F (u + h)) ^ 2 * Real.exp (-(8 * u))) +
          32 * Real.exp 8 * h ^ 2 * (F (u + h) ^ 2 * Real.exp (-(8 * (u + h)))) := fun u => by
      have he : boundaryTilt F u - boundaryTilt F (u + h) =
          Real.exp (-(4 * u)) * ((F u - F (u + h)) + (1 - r) * F (u + h)) := by
        dsimp only [boundaryTilt, r]
        rw [show -(4 * (u + h)) = -(4 * u) + -(4 * h) by ring, Real.exp_add]
        ring
      have hexp8 : Real.exp (-(4 * u)) ^ 2 = Real.exp (-(8 * u)) := by
        rw [← Real.exp_nat_mul]; push_cast; ring
      have hshift_exp : Real.exp (-(8 * u)) ≤ Real.exp 8 * Real.exp (-(8 * (u + h))) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      rw [he, mul_pow, hexp8]
      have hquad : ((F u - F (u + h)) + (1 - r) * F (u + h)) ^ 2 ≤
          2 * (F u - F (u + h)) ^ 2 + 32 * h ^ 2 * F (u + h) ^ 2 := by
        nlinarith only [sq_nonneg ((F u - F (u + h)) - (1 - r) * F (u + h)),
          mul_le_mul_of_nonneg_right h1mr (sq_nonneg (F (u + h)))]
      have hm1 := mul_le_mul_of_nonneg_left hquad (Real.exp_pos (-(8 * u))).le
      have hm2 := mul_le_mul_of_nonneg_right hshift_exp
        (mul_nonneg (by positivity : (0 : ℝ) ≤ 32 * h ^ 2) (sq_nonneg (F (u + h))))
      linarith
    have hint : (∫ u : ℝ, (boundaryTilt F u - boundaryTilt F (u + h)) ^ 2) ≤
        ∫ u : ℝ, (2 * ((F u - F (u + h)) ^ 2 * Real.exp (-(8 * u))) +
          32 * Real.exp 8 * h ^ 2 * (F (u + h) ^ 2 * Real.exp (-(8 * (u + h))))) :=
      integral_mono hiL (hi1.add hi2) hpt
    rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
      integral_add_right_eq_self (fun v => F v ^ 2 * Real.exp (-(8 * v))) h] at hint
    set I1 : ℝ := ∫ u : ℝ, (F u - F (u + h)) ^ 2 * Real.exp (-(8 * u))
    have hdiv : (∫ u : ℝ, (boundaryTilt F u - boundaryTilt F (u + h)) ^ 2) / h ≤
        (2 * I1 + 32 * Real.exp 8 * h ^ 2 * M) / h :=
      div_le_div_of_nonneg_right hint hh0'.le
    calc (∫ u : ℝ, (boundaryTilt F u - boundaryTilt F (u + h)) ^ 2) / h
        ≤ (2 * I1 + 32 * Real.exp 8 * h ^ 2 * M) / h := hdiv
      _ = 2 * (I1 / h) + 32 * Real.exp 8 * M * h := by field_simp [hh0'.ne']

private theorem integrable_boundary_power {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) :
    Integrable fun y : ℝ => ‖negativeHalfLineLaplace (cx F) ⟨-4, y⟩‖ ^ 2 := by
  have hP := integrable_norm_sq_paperFT_cx (integrable_boundaryTilt hr hF)
    (integrable_sq_boundaryTilt hF.1)
  refine hP.congr (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [laplace_neg_four_eq_paperFT hF.1 y]

private theorem tendsto_mul_setIntegral_boundary_octave {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun U : ℝ => U * ∫ y in {y : ℝ | U ≤ |y| ∧ |y| ≤ 2 * U},
      ‖negativeHalfLineLaplace (cx F) ⟨-4, y⟩‖ ^ 2) atTop (𝓝 0) := by
  have hnull := isConfinedNullVector_of_groundState hW ht hF
  have hP := integrable_boundary_power hW hnull
  have hh_tend : Tendsto (fun U : ℝ => (2 * U)⁻¹) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Tendsto (fun U : ℝ => (2⁻¹ : ℝ) * U⁻¹) atTop (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2⁻¹ : ℝ)
      exact h0.congr fun U => by ring
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with U (hU : 0 < U)
      exact inv_pos.mpr (mul_pos two_pos hU)
  have hinc := ((tendsto_boundaryTilt_sq_increment_div hW ht hF).comp hh_tend).const_mul
    (8 * Real.pi)
  rw [mul_zero] at hinc
  refine squeeze_zero' ?_ ?_ hinc
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with U hU
    exact mul_nonneg hU (integral_nonneg fun _ => sq_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
    set h := (2 * U)⁻¹
    have hh0 : 0 < h := inv_pos.mpr (by positivity)
    let S := {y : ℝ | U ≤ |y| ∧ |y| ≤ 2 * U}
    have hSm : MeasurableSet S :=
      (measurableSet_le measurable_const continuous_abs.measurable).inter
        (measurableSet_le continuous_abs.measurable measurable_const)
    let P := fun y : ℝ => ‖negativeHalfLineLaplace (cx F) ⟨-4, y⟩‖ ^ 2
    let Q := fun y : ℝ => (1 - Real.cos (h * y)) * P y
    have hQi : Integrable Q := integrable_one_sub_cos_mul hP h
    have hle1 : ∫ y in S, P y ≤ 16 * ∫ y in S, Q y := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on hP.integrableOn (hQi.const_mul 16).integrableOn hSm fun y hy => ?_
      have hhi : |h * y| ≤ 1 := by
        rw [abs_mul, abs_of_pos hh0]
        dsimp only [h]
        exact (inv_mul_le_iff₀ (by positivity)).mpr (by linarith [hy.2])
      have hlo : 1 / 2 ≤ |h * y| := by
        rw [abs_mul, abs_of_pos hh0]
        dsimp only [h]
        rw [le_inv_mul_iff₀ (by positivity)]
        linarith [hy.1]
      have hcos := sq_div_four_le_one_sub_cos hhi
      have hsq : (1 / 2 : ℝ) ^ 2 ≤ |h * y| ^ 2 := pow_le_pow_left₀ (by norm_num) hlo 2
      rw [sq_abs] at hsq
      have h16 : 1 ≤ 16 * (1 - Real.cos (h * y)) := by linarith only [hcos, hsq]
      exact (le_mul_of_one_le_left (sq_nonneg _) h16).trans_eq (mul_assoc _ _ _)
    have hle2 : ∫ y in S, Q y ≤ ∫ y : ℝ, Q y :=
      setIntegral_le_integral hQi (Eventually.of_forall fun y =>
        mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _))
    rw [integral_one_sub_cos_boundary hW hnull h] at hle2
    set I_inc := ∫ u : ℝ, (boundaryTilt F u - boundaryTilt F (u + h)) ^ 2
    have hcomb : U * ∫ y in S, P y ≤ U * (16 * (Real.pi * I_inc)) :=
      mul_le_mul_of_nonneg_left (hle1.trans (mul_le_mul_of_nonneg_left hle2 (by norm_num))) hU.le
    change U * ∫ y in S, P y ≤ 8 * Real.pi * (I_inc / h)
    refine hcomb.trans_eq ?_
    dsimp only [h]
    rw [div_inv_eq_mul]
    ring

/-- **Vanishing of the continuous boundary Fourier tail.** For a threshold ground state `F`,
`T ∫_{|y| > T} ‖L F(-4 + iy)‖² dy → 0` as `T → +∞`. -/
theorem criticalState_boundary_fourier_tail_zero {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun T : ℝ => T * ∫ y in {y : ℝ | T < |y|},
      ‖negativeHalfLineLaplace (cx F) ⟨-4, y⟩‖ ^ 2) atTop (𝓝 0) := by
  have hnull := isConfinedNullVector_of_groundState hW ht hF
  have hP := integrable_boundary_power hW hnull
  let P := fun y : ℝ => ‖negativeHalfLineLaplace (cx F) ⟨-4, y⟩‖ ^ 2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨U₀, hU₀⟩ := Metric.tendsto_atTop.mp
    (tendsto_mul_setIntegral_boundary_octave hW ht hF) (ε / 4) (by positivity)
  refine ⟨max U₀ 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTU : U₀ ≤ T := (le_max_left _ _).trans hT
  let S : ℕ → Set ℝ := fun k => {y : ℝ | (2 : ℝ) ^ k * T < |y| ∧ |y| ≤ (2 : ℝ) ^ (k + 1) * T}
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    (measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  have hcover : {y : ℝ | T < |y|} = ⋃ k : ℕ, S k := by
    ext y
    simp only [mem_setOf_eq, mem_iUnion, S]
    constructor
    · intro hy
      obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near ((one_le_div hT0).mpr hy.le) one_lt_two
      rcases eq_or_lt_of_le ((le_div_iff₀ hT0).mp hk1) with heq | hlt
      · have hk_pos : 0 < k := by
          by_contra hle0
          have hk0 : k = 0 := Nat.eq_zero_of_not_pos hle0
          subst hk0
          simp at heq
          linarith
        refine ⟨k - 1, ?_, ?_⟩
        · have hlt_pow : (2 : ℝ) ^ (k - 1) < (2 : ℝ) ^ k :=
            pow_lt_pow_right₀ one_lt_two (Nat.sub_lt hk_pos zero_lt_one)
          have hm := mul_lt_mul_of_pos_right hlt_pow hT0
          linarith
        · rw [Nat.sub_add_cancel hk_pos]
          linarith
      · exact ⟨k, hlt, ((div_lt_iff₀ hT0).mp hk2).le⟩
    · rintro ⟨k, hk1, _⟩
      exact lt_of_le_of_lt (le_mul_of_one_le_left hT0.le (one_le_pow₀ (by norm_num))) hk1
  have hdisj : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro y hyi hyj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hpow : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hlt
      linarith [mul_le_mul_of_nonneg_right hpow hT0.le, hyi.2, hyj.1]
    · have hpow : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ i := pow_le_pow_right₀ (by norm_num) hgt
      linarith [mul_le_mul_of_nonneg_right hpow hT0.le, hyj.2, hyi.1]
  have hsum_int : (∫ y in {y : ℝ | T < |y|}, P y) = ∑' k : ℕ, ∫ y in S k, P y := by
    rw [hcover, integral_iUnion hSm hdisj hP.integrableOn]
  have hbound : ∀ k : ℕ, ∫ y in S k, P y ≤ (ε / 4 / T) * (1 / 2 : ℝ) ^ k := fun k => by
    set U := (2 : ℝ) ^ k * T
    have hU_ge : U₀ ≤ U := hTU.trans (le_mul_of_one_le_left hT0.le (one_le_pow₀ (by norm_num)))
    have hU_pos : 0 < U := mul_pos (pow_pos two_pos k) hT0
    have hoct := hU₀ U hU_ge
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hU_pos.le
      (integral_nonneg fun _ => sq_nonneg _))] at hoct
    have hsub_oct : S k ⊆ {y : ℝ | U ≤ |y| ∧ |y| ≤ 2 * U} := fun y hy =>
      ⟨hy.1.le, by simpa only [U, pow_succ', mul_assoc] using hy.2⟩
    have hmono := setIntegral_mono_set hP.integrableOn
      (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hsub_oct)
    have hdiv := (le_div_iff₀' hU_pos).mpr ((mul_le_mul_of_nonneg_left hmono hU_pos.le).trans hoct.le)
    refine hdiv.trans_eq ?_
    dsimp only [U]
    rw [one_div_pow]
    field_simp [hT0.ne']
  have hgeom : Summable fun k : ℕ => (ε / 4 / T) * (1 / 2 : ℝ) ^ k :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hint_nn : ∀ k, 0 ≤ ∫ y in S k, P y := fun _ => integral_nonneg fun _ => sq_nonneg _
  have htsum_le : (∑' k : ℕ, ∫ y in S k, P y) ≤ ∑' k : ℕ, (ε / 4 / T) * (1 / 2 : ℝ) ^ k :=
    Summable.tsum_le_tsum hbound (hgeom.of_nonneg_of_le hint_nn hbound) hgeom
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at htsum_le
  have htot : T * ∫ y in {y : ℝ | T < |y|}, P y ≤ ε / 2 := by
    rw [hsum_int]
    have hm := mul_le_mul_of_nonneg_left htsum_le hT0.le
    calc T * ∑' k : ℕ, ∫ y in S k, P y
        ≤ T * (ε / 4 / T * (1 - 1 / 2)⁻¹) := hm
      _ = ε / 2 := by
          rw [show (1 - 1 / 2 : ℝ)⁻¹ = 2 by norm_num,
            show ε / 4 / T * 2 = ε / 2 * T⁻¹ by ring,
            ← mul_assoc, mul_comm T (ε / 2), mul_assoc, mul_inv_cancel₀ hT0.ne', mul_one]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hT0.le
    (integral_nonneg fun _ => sq_nonneg _))]
  linarith

/-- **Sub-logarithmic first moment of the continuous boundary Fourier power.** For a threshold
ground state `F`, `(log T)⁻¹ ∫_{-T}^T |y| ‖L F(-4 + iy)‖² dy → 0` as `T → +∞`. -/
theorem criticalState_boundary_fourier_firstMoment_sublogarithmic {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun T : ℝ => (Real.log T)⁻¹ * ∫ y in Icc (-T) T,
      |y| * ‖negativeHalfLineLaplace (cx F) ⟨-4, y⟩‖ ^ 2) atTop (𝓝 0) := by
  have hnull := isConfinedNullVector_of_groundState hW ht hF
  have hP := integrable_boundary_power hW hnull
  let P := fun y : ℝ => ‖negativeHalfLineLaplace (cx F) ⟨-4, y⟩‖ ^ 2
  let YP := fun y : ℝ => |y| * P y
  have hYP_int_set : ∀ {S : Set ℝ} {B : ℝ}, 0 ≤ B → (∀ y ∈ S, |y| ≤ B) → MeasurableSet S →
      IntegrableOn YP S := fun {S B} _ hSB hSm => by
    refine (hP.integrableOn.const_mul B).mono'
      (continuous_abs.measurable.aestronglyMeasurable.mul hP.aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem hSm] with y hy
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hSB y hy) (sq_nonneg _)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨U₀, hU₀⟩ := Metric.tendsto_atTop.mp
    (tendsto_mul_setIntegral_boundary_octave hW ht hF) (ε * Real.log 2 / 8) (by positivity)
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (max U₀ 1)
  set R₀ : ℝ := (2 : ℝ) ^ k₀
  have hR₀_pos : 0 < R₀ := pow_pos two_pos k₀
  have hR₀_ge : U₀ ≤ R₀ := by
    have hk1 : (k₀ : ℝ) ≤ (2 : ℝ) ^ k₀ := by
      exact_mod_cast (Nat.lt_pow_self (n := k₀) one_lt_two).le
    exact ((le_max_left U₀ 1).trans hk₀.le).trans hk1
  set C₀ : ℝ := ∫ y in Icc (-R₀) R₀, YP y
  have hC₀_nn : 0 ≤ C₀ := setIntegral_nonneg measurableSet_Icc fun _ _ =>
    mul_nonneg (abs_nonneg _) (sq_nonneg _)
  refine ⟨max (Real.exp 2) (Real.exp ((4 * C₀ + ε * Real.log 2 + 1) / ε)), fun T hT => ?_⟩
  have hTe2 : Real.exp 2 ≤ T := (le_max_left _ _).trans hT
  have hTbig : Real.exp ((4 * C₀ + ε * Real.log 2 + 1) / ε) ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos 2) hTe2
  have hlogT : 2 ≤ Real.log T := (Real.le_log_iff_exp_le hT0).mpr hTe2
  have hlogT_big : (4 * C₀ + ε * Real.log 2 + 1) / ε ≤ Real.log T :=
    (Real.le_log_iff_exp_le hT0).mpr hTbig
  have hlogT_pos : 0 < Real.log T := by linarith
  set N : ℕ := ⌊Real.log T / Real.log 2⌋₊ + 1
  have hTN : T < (2 : ℝ) ^ N := by
    have hlt : Real.log T / Real.log 2 < (N : ℝ) := by
      dsimp only [N]
      exact_mod_cast Nat.lt_floor_add_one (Real.log T / Real.log 2)
    have h1 : Real.log T < (N : ℝ) * Real.log 2 := (div_lt_iff₀ hlog2).mp hlt
    rw [← Real.log_pow] at h1
    exact (Real.log_lt_log_iff hT0 (pow_pos two_pos N)).mp h1
  let Oct : ℕ → Set ℝ := fun k => {y : ℝ | (2 : ℝ) ^ k ≤ |y| ∧ |y| < (2 : ℝ) ^ (k + 1)}
  have hOctm : ∀ k, MeasurableSet (Oct k) := fun k =>
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hYP_T : IntegrableOn YP (Icc (-T) T) :=
    hYP_int_set hT0.le (fun _ hy => abs_le.mpr hy) measurableSet_Icc
  have hYP_R₀ : Integrable fun y => (Icc (-R₀) R₀).indicator YP y :=
    (hYP_int_set hR₀_pos.le (fun _ hy => abs_le.mpr hy) measurableSet_Icc).integrable_indicator
      measurableSet_Icc
  have hYP_Oct : ∀ k, IntegrableOn YP (Oct k) := fun k =>
    hYP_int_set (pow_pos two_pos (k + 1)).le (fun _ hy => hy.2.le) (hOctm k)
  have hYP_Oct_ind : ∀ k, Integrable fun y => (Oct k).indicator YP y := fun k =>
    (hYP_Oct k).integrable_indicator (hOctm k)
  have hpt_cover : ∀ y : ℝ, (Icc (-T) T).indicator YP y ≤
      (Icc (-R₀) R₀).indicator YP y + ∑ k ∈ Finset.Ico k₀ N, (Oct k).indicator YP y := fun y => by
    have hnn_sum : 0 ≤ ∑ k ∈ Finset.Ico k₀ N, (Oct k).indicator YP y :=
      Finset.sum_nonneg fun k _ => indicator_nonneg
        (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) y
    have hnn_R₀ : 0 ≤ (Icc (-R₀) R₀).indicator YP y :=
      indicator_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) y
    by_cases hy : y ∈ Icc (-T) T
    · rw [indicator_of_mem hy]
      have habs : |y| ≤ T := abs_le.mpr hy
      rcases le_or_gt |y| R₀ with hle | hgt
      · rw [indicator_of_mem (mem_Icc.mpr (abs_le.mp hle))]
        linarith
      · have hy_gt1 : 1 ≤ |y| := (one_le_pow₀ (by norm_num)).trans hgt.le
        obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hy_gt1 one_lt_two
        have hk_ge : k₀ ≤ k := by
          by_contra hlt'
          have hp : (2 : ℝ) ^ (k + 1) ≤ R₀ :=
            pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt (not_le.mp hlt'))
          linarith
        have hk_lt : k < N := by
          by_contra hge
          have hp : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (not_lt.mp hge)
          linarith
        have hk_mem : k ∈ Finset.Ico k₀ N := Finset.mem_Ico.mpr ⟨hk_ge, hk_lt⟩
        have hsingle : (Oct k).indicator YP y ≤ ∑ j ∈ Finset.Ico k₀ N, (Oct j).indicator YP y :=
          Finset.single_le_sum
            (fun j _ => indicator_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) y)
            hk_mem
        rw [indicator_of_mem (show y ∈ Oct k from ⟨hk1, hk2⟩)] at hsingle
        linarith
    · rw [indicator_of_notMem hy]
      linarith
  have hoct_bound : ∀ k ∈ Finset.Ico k₀ N, ∫ y in Oct k, YP y ≤ ε * Real.log 2 / 4 := by
    intro k hk
    have hk_ge : k₀ ≤ k := (Finset.mem_Ico.mp hk).1
    set U := (2 : ℝ) ^ k
    have hU_ge : U₀ ≤ U := hR₀_ge.trans (pow_le_pow_right₀ (by norm_num) hk_ge)
    have hU_pos : 0 < U := pow_pos two_pos k
    have hoct := hU₀ U hU_ge
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hU_pos.le
      (integral_nonneg fun _ => sq_nonneg _))] at hoct
    have hle1 : ∫ y in Oct k, YP y ≤ (2 * U) * ∫ y in Oct k, P y := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hYP_Oct k) (hP.integrableOn.const_mul (2 * U)) (hOctm k)
        fun y hy => ?_
      have hy2 : |y| ≤ 2 * U := by simpa only [U, pow_succ'] using hy.2.le
      exact mul_le_mul_of_nonneg_right hy2 (sq_nonneg _)
    have hsub_oct : Oct k ⊆ {y : ℝ | U ≤ |y| ∧ |y| ≤ 2 * U} := fun y hy =>
      ⟨hy.1, by simpa only [U, pow_succ'] using hy.2.le⟩
    have hle2 : ∫ y in Oct k, P y ≤ ∫ y in {y : ℝ | U ≤ |y| ∧ |y| ≤ 2 * U}, P y :=
      setIntegral_mono_set hP.integrableOn
        (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hsub_oct)
    have hcomb : ∫ y in Oct k, YP y ≤ 2 * (U * ∫ y in {y : ℝ | U ≤ |y| ∧ |y| ≤ 2 * U}, P y) := by
      have hm := mul_le_mul_of_nonneg_left hle2 (show (0 : ℝ) ≤ 2 * U by positivity)
      linarith [hle1, hm]
    linarith [hoct.le]
  have htot_int : ∫ y in Icc (-T) T, YP y ≤ C₀ + (N : ℝ) * (ε * Real.log 2 / 4) := by
    have hi_sum : Integrable fun y => ∑ k ∈ Finset.Ico k₀ N, (Oct k).indicator YP y :=
      integrable_finsetSum _ fun k _ => hYP_Oct_ind k
    have hmono : (∫ y, (Icc (-T) T).indicator YP y) ≤
        ∫ y, ((Icc (-R₀) R₀).indicator YP y + ∑ k ∈ Finset.Ico k₀ N, (Oct k).indicator YP y) :=
      integral_mono (hYP_T.integrable_indicator measurableSet_Icc) (hYP_R₀.add hi_sum) hpt_cover
    rw [integral_indicator measurableSet_Icc, integral_add hYP_R₀ hi_sum,
      integral_indicator measurableSet_Icc,
      integral_finsetSum _ fun k _ => hYP_Oct_ind k] at hmono
    have hsum_le : (∑ k ∈ Finset.Ico k₀ N, ∫ y, (Oct k).indicator YP y) ≤
        (N : ℝ) * (ε * Real.log 2 / 4) := by
      have heq_sum : (∑ k ∈ Finset.Ico k₀ N, ∫ y, (Oct k).indicator YP y) =
          ∑ k ∈ Finset.Ico k₀ N, ∫ y in Oct k, YP y :=
        Finset.sum_congr rfl fun k _ => integral_indicator (hOctm k)
      rw [heq_sum]
      calc ∑ k ∈ Finset.Ico k₀ N, ∫ y in Oct k, YP y
          ≤ ∑ _ ∈ Finset.Ico k₀ N, (ε * Real.log 2 / 4) := Finset.sum_le_sum hoct_bound
        _ = ((Finset.Ico k₀ N).card : ℝ) * (ε * Real.log 2 / 4) := by simp
        _ ≤ (N : ℝ) * (ε * Real.log 2 / 4) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [Nat.card_Ico]
            exact_mod_cast Nat.sub_le N k₀
    linarith [hmono, hsum_le]
  have hN_le : (N : ℝ) * Real.log 2 ≤ Real.log T + Real.log 2 := by
    have hfl : (⌊Real.log T / Real.log 2⌋₊ : ℝ) ≤ Real.log T / Real.log 2 :=
      Nat.floor_le (div_nonneg hlogT_pos.le hlog2.le)
    have hm := mul_le_mul_of_nonneg_right hfl hlog2.le
    rw [div_mul_cancel₀ _ hlog2.ne'] at hm
    dsimp only [N]
    push_cast
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hlogT_pos.le)
    (setIntegral_nonneg measurableSet_Icc fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)))]
  rw [inv_mul_lt_iff₀ hlogT_pos]
  have hbig' : 4 * C₀ + ε * Real.log 2 + 1 ≤ Real.log T * ε :=
    (div_le_iff₀ hε).mp hlogT_big
  have hNε : (N : ℝ) * (ε * Real.log 2 / 4) ≤ (Real.log T + Real.log 2) * (ε / 4) := by
    have hm := mul_le_mul_of_nonneg_right hN_le (show (0 : ℝ) ≤ ε / 4 by positivity)
    linarith
  have hpos_prod : 0 < Real.log T * ε := mul_pos hlogT_pos hε
  change ∫ y in Icc (-T) T, YP y < Real.log T * ε
  linarith [htot_int, hNε, hbig', hC₀_nn, hpos_prod]

/-! ### Exact ordinate-tail and first-moment asymptotics under `FiniteOffLine` -/

private def reflectOnLine : onLineCopies ≃ onLineCopies :=
  xiZeroCopyReflectEquiv.subtypeEquiv fun q => by
    change (centredZero q).re = 0 ↔ (centredZero (xiZeroCopyReflectEquiv q)).re = 0
    have h : centredZero (xiZeroCopyReflectEquiv q) = -centredZero q := by
      simp only [centredZero, xiZeroCopy_reflect_val]; ring
    rw [h, neg_re, neg_eq_zero]

private theorem im_centredZero_reflectOnLine (q : onLineCopies) :
    (centredZero (reflectOnLine q)).im = -(centredZero q).im := by
  have h : centredZero (reflectOnLine q : XiZeroCopy) = -centredZero (q : XiZeroCopy) := by
    simp only [reflectOnLine, Equiv.subtypeEquiv_apply, centredZero, xiZeroCopy_reflect_val]
    ring
  rw [h, neg_im]

private theorem zeroValueMass_reflectOnLine (F : ℝ → ℝ) (q : onLineCopies) :
    zeroValueMass F (reflectOnLine q) = zeroValueMass F q := by
  dsimp only [zeroValueMass]
  have h : centredZero (reflectOnLine q : XiZeroCopy) = conj (centredZero (q : XiZeroCopy)) := by
    have hc : centredZero (reflectOnLine q : XiZeroCopy) = -centredZero (q : XiZeroCopy) := by
      simp only [reflectOnLine, Equiv.subtypeEquiv_apply, centredZero, xiZeroCopy_reflect_val]
      ring
    have hre : (centredZero (q : XiZeroCopy)).re = 0 := q.property
    rw [hc]
    apply Complex.ext
    · simp [hre]
    · simp
  rw [h, show cx F = fun u => (F u : ℂ) from rfl, negativeHalfLineLaplace_real_conj, norm_conj]

private theorem integrableOn_Ioi_inv_sq {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun u : ℝ => (u ^ 2)⁻¹) (Ioi R) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR).congr_fun
    (fun u (hu : R < u) => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_neg (lt_trans hR hu).le, Real.rpow_two]

private theorem integral_Ioi_inv_sq {R : ℝ} (hR : 0 < R) :
    (∫ u in Ioi R, (u ^ 2)⁻¹) = R⁻¹ := by
  let g : ℝ → ℝ := fun x => -x⁻¹
  have hd : ∀ u ∈ Ioi R, HasDerivAt g ((u ^ 2)⁻¹) u := fun u (hu : R < u) => by
    have hne : u ≠ 0 := (lt_trans hR hu).ne'
    exact ((hasDerivAt_inv hne).neg : HasDerivAt g (- -(u ^ 2)⁻¹) u).congr_deriv (neg_neg _)
  have hi : IntegrableOn (fun u : ℝ => (u ^ 2)⁻¹) (Ioi R) := integrableOn_Ioi_inv_sq hR
  have hc : ContinuousWithinAt g (Ici R) R :=
    (continuousAt_inv₀ hR.ne').neg.continuousWithinAt
  have hlim : Tendsto g atTop (𝓝 0) := by
    simpa [g] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd hi hlim]
  dsimp only [g]
  ring

private theorem integral_poissonKernel_univ (γ : ℝ) :
    (∫ y : ℝ, 4 / (16 + (y - γ) ^ 2)) = Real.pi := by
  have h4 := integral_inv_sq_add_sq_univ (by norm_num : (0 : ℝ) < 4)
  have hshift : (∫ y : ℝ, 4 / (16 + (y - γ) ^ 2)) = 4 * ∫ u : ℝ, ((4 : ℝ) ^ 2 + u ^ 2)⁻¹ := by
    calc (∫ y : ℝ, 4 / (16 + (y - γ) ^ 2))
        = ∫ u : ℝ, 4 / (16 + u ^ 2) :=
          integral_sub_right_eq_self (fun u : ℝ => 4 / (16 + u ^ 2)) γ
      _ = ∫ u : ℝ, 4 * ((4 : ℝ) ^ 2 + u ^ 2)⁻¹ :=
          integral_congr_ae (Eventually.of_forall fun u => by norm_num [div_eq_mul_inv])
      _ = 4 * ∫ u : ℝ, ((4 : ℝ) ^ 2 + u ^ 2)⁻¹ := integral_const_mul _ _
  rw [hshift, h4]
  ring

private theorem integrable_poissonKernel (γ : ℝ) :
    Integrable fun y : ℝ => 4 / (16 + (y - γ) ^ 2) :=
  Integrable.of_integral_ne_zero (by rw [integral_poissonKernel_univ γ]; exact Real.pi_ne_zero)

private theorem setIntegral_poissonKernel_le_pi (γ : ℝ) (S : Set ℝ) :
    (∫ y in S, 4 / (16 + (y - γ) ^ 2)) ≤ Real.pi :=
  (setIntegral_le_integral (integrable_poissonKernel γ)
    (Eventually.of_forall fun _ => by positivity)).trans_eq (integral_poissonKernel_univ γ)

private theorem pi_sub_div_le_setIntegral_poissonKernel (γ : ℝ) {R : ℝ} (hR : 0 < R) :
    Real.pi - 8 / R ≤ ∫ y in Ioo (γ - R) (γ + R), 4 / (16 + (y - γ) ^ 2) := by
  let K : ℝ → ℝ := fun u => 4 / (16 + u ^ 2)
  have hKi : Integrable K := by simpa only [K, sub_zero] using integrable_poissonKernel 0
  have hshift : (∫ y in Ioo (γ - R) (γ + R), 4 / (16 + (y - γ) ^ 2)) = ∫ u in Ioo (-R) R, K u := by
    have heq : (Ioo (γ - R) (γ + R)).indicator (fun y => 4 / (16 + (y - γ) ^ 2)) =
        fun y => (Ioo (-R) R).indicator K (y - γ) := by
      funext y
      unfold indicator
      have hiff : (γ - R < y ∧ y < γ + R) ↔ (-R < y - γ ∧ y - γ < R) := by
        constructor <;> intro h <;> constructor <;> linarith
      simp only [mem_Ioo, hiff, K]
    rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo, heq,
      integral_sub_right_eq_self (fun u => (Ioo (-R) R).indicator K u) γ]
  rw [hshift]
  have htot : (∫ u in Ioo (-R) R, K u) + ∫ u in (Ioo (-R) R)ᶜ, K u = Real.pi := by
    rw [integral_add_compl measurableSet_Ioo hKi]
    simpa only [K, sub_zero] using integral_poissonKernel_univ 0
  have hray_R : ∫ u in Ici R, K u ≤ 4 / R := by
    rw [integral_Ici_eq_integral_Ioi]
    have hi_inv : IntegrableOn (fun u : ℝ => 4 * (u ^ 2)⁻¹) (Ioi R) :=
      (integrableOn_Ioi_inv_sq hR).const_mul 4
    have hle : ∫ u in Ioi R, K u ≤ ∫ u in Ioi R, 4 * (u ^ 2)⁻¹ :=
      setIntegral_mono_on hKi.integrableOn hi_inv measurableSet_Ioi fun u (hu : R < u) => by
        dsimp only [K]
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          (inv_anti₀ (sq_pos_of_pos (lt_trans hR hu)) (by linarith)) (by norm_num)
    rw [integral_const_mul, integral_Ioi_inv_sq hR] at hle
    exact hle.trans_eq (div_eq_mul_inv 4 R).symm
  have hray_L : ∫ u in Iic (-R), K u ≤ 4 / R := by
    have heq : (∫ u in Iic (-R), K u) = ∫ u in Ici R, K u := by
      rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Ici,
        ← integral_neg_eq_self (fun u => (Ici R).indicator K u)]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      unfold indicator
      have hiff : (u ≤ -R) ↔ (R ≤ -u) := ⟨fun h => by linarith, fun h => by linarith⟩
      simp only [mem_Iic, mem_Ici, hiff, K, neg_sq]
    exact heq.le.trans hray_R
  have hcompl_le : ∫ u in (Ioo (-R) R)ᶜ, K u ≤ 8 / R := by
    have hK_nn : ∀ x : ℝ, 0 ≤ K x := fun x => div_nonneg (by norm_num) (by positivity)
    have hi1 : Integrable fun u => (Iic (-R)).indicator K u :=
      (hKi.integrableOn (s := Iic (-R))).integrable_indicator measurableSet_Iic
    have hi2 : Integrable fun u => (Ici R).indicator K u :=
      (hKi.integrableOn (s := Ici R)).integrable_indicator measurableSet_Ici
    have hpt : ∀ u : ℝ, ((Ioo (-R) R)ᶜ).indicator K u ≤
        (Iic (-R)).indicator K u + (Ici R).indicator K u := fun u => by
      by_cases hu : u ∈ Ioo (-R) R
      · rw [indicator_of_notMem (not_notMem.mpr hu)]
        exact add_nonneg (indicator_nonneg (fun x _ => hK_nn x) u)
          (indicator_nonneg (fun x _ => hK_nn x) u)
      · rw [indicator_of_mem hu]
        rcases le_or_gt u (-R) with hle | hgt
        · rw [indicator_of_mem (mem_Iic.mpr hle)]
          linarith [indicator_nonneg (s := Ici R) (fun x _ => hK_nn x) u]
        · have hge : R ≤ u := not_lt.mp fun hlt => hu ⟨hgt, hlt⟩
          rw [indicator_of_mem (mem_Ici.mpr hge)]
          linarith [indicator_nonneg (s := Iic (-R)) (fun x _ => hK_nn x) u]
    have hm : (∫ u, ((Ioo (-R) R)ᶜ).indicator K u) ≤
        ∫ u, ((Iic (-R)).indicator K u + (Ici R).indicator K u) :=
      integral_mono (hKi.integrableOn.integrable_indicator measurableSet_Ioo.compl)
        (hi1.add hi2) hpt
    rw [integral_indicator measurableSet_Ioo.compl, integral_add hi1 hi2,
      integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ici] at hm
    have h48 : 4 / R + 4 / R = 8 / R := by ring
    linarith [hm, hray_L, hray_R, h48]
  linarith

private theorem tendsto_mul_setIntegral_Ioi_of_sq_tendsto {g : ℝ → ℝ}
    (hg_nn : ∀ y, 0 ≤ g y) (hg_meas : Measurable g) {C : ℝ}
    (hlim : Tendsto (fun y : ℝ => y ^ 2 * g y) atTop (𝓝 C)) :
    Tendsto (fun T : ℝ => T * ∫ y in Ioi T, g y) atTop (𝓝 C) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Y₀, hY₀⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  refine ⟨max Y₀ 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTY : Y₀ ≤ T := (le_max_left _ _).trans hT
  have hi_inv : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹) (Ioi T) := integrableOn_Ioi_inv_sq hT0
  have hpt_hi : ∀ y ∈ Ioi T, g y ≤ (C + ε / 2) * (y ^ 2)⁻¹ := fun y (hy : T < y) => by
    have hy0 : 0 < y := lt_trans hT0 hy
    have hd := hY₀ y (hTY.trans hy.le)
    rw [Real.dist_eq] at hd
    have hub : y ^ 2 * g y ≤ C + ε / 2 := by linarith [(abs_lt.mp hd).2]
    exact ((le_div_iff₀' (sq_pos_of_pos hy0)).mpr hub).trans_eq (div_eq_mul_inv _ _)
  have hpt_lo : ∀ y ∈ Ioi T, (C - ε / 2) * (y ^ 2)⁻¹ ≤ g y := fun y (hy : T < y) => by
    have hy0 : 0 < y := lt_trans hT0 hy
    have hd := hY₀ y (hTY.trans hy.le)
    rw [Real.dist_eq] at hd
    have hlb : C - ε / 2 ≤ y ^ 2 * g y := by linarith [(abs_lt.mp hd).1]
    exact (div_eq_mul_inv (C - ε / 2) (y ^ 2)).symm.le.trans ((div_le_iff₀' (sq_pos_of_pos hy0)).mpr hlb)
  have hgi : IntegrableOn g (Ioi T) := by
    refine (hi_inv.const_mul (C + ε / 2)).mono' hg_meas.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [Real.norm_of_nonneg (hg_nn y)]
    exact hpt_hi y hy
  have hint_hi := setIntegral_mono_on hgi (hi_inv.const_mul (C + ε / 2)) measurableSet_Ioi hpt_hi
  have hint_lo := setIntegral_mono_on (hi_inv.const_mul (C - ε / 2)) hgi measurableSet_Ioi hpt_lo
  rw [integral_const_mul, integral_Ioi_inv_sq hT0] at hint_hi hint_lo
  have hm_hi := mul_le_mul_of_nonneg_left hint_hi hT0.le
  have hm_lo := mul_le_mul_of_nonneg_left hint_lo hT0.le
  have he_hi : T * ((C + ε / 2) * T⁻¹) = C + ε / 2 := by field_simp [hT0.ne']
  have he_lo : T * ((C - ε / 2) * T⁻¹) = C - ε / 2 := by field_simp [hT0.ne']
  rw [he_hi] at hm_hi
  rw [he_lo] at hm_lo
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private theorem ite_zero_nonneg {p : Prop} [Decidable p] {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ (if p then a else 0) := by
  by_cases hp : p <;> simp [hp, ha]

private theorem ite_zero_le {p : Prop} [Decidable p] {a : ℝ} (ha : 0 ≤ a) :
    (if p then a else 0) ≤ a := by
  by_cases hp : p <;> simp [hp, ha]

private theorem setIntegral_tsum_of_summable_integral_norm {ι : Type*} [Countable ι]
    {μ : Measure ℝ} {f : ι → ℝ → ℝ} (hf_int : ∀ i, Integrable (f i) μ)
    (hf_sum : Summable fun i => ∫ x, ‖f i x‖ ∂μ) :
    (∫ x, ∑' i, f i x ∂μ) = ∑' i, ∫ x, f i x ∂μ := by
  apply MeasureTheory.integral_tsum
  · exact fun i => (hf_int i).aestronglyMeasurable
  · have hi : ∀ i, (∫⁻ x, ‖f i x‖ₑ ∂μ) = ‖∫ x, ‖f i x‖ ∂μ‖ₑ := fun i => by
      dsimp only [enorm]
      rw [lintegral_coe_eq_integral _ (hf_int i).norm, ENNReal.coe_nnreal_eq,
        coe_nnnorm, Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (f i x))]
      simp only [coe_nnnorm]
    rw [funext hi]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hf_sum.abs)

private theorem setIntegral_poissonWindow_eq_tsum {m γ : onLineCopies → ℝ}
    (hm_sum : Summable m) (hm_nn : ∀ q, 0 ≤ m q) (η : ℝ) (S : Set ℝ) :
    (∫ y in S, ∑' q : onLineCopies,
      if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0) =
      ∑' q : onLineCopies, ∫ y in S,
        if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0 := by
  let f : onLineCopies → ℝ → ℝ := fun q y =>
    if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0
  have hf_meas : ∀ q, Measurable (f q) := fun q =>
    Measurable.ite (measurableSet_lt (continuous_id.sub continuous_const).abs.measurable
      (continuous_const.mul continuous_id).measurable)
      (measurable_const.mul (measurable_const.div
        (measurable_const.add ((measurable_id.sub measurable_const).pow_const 2))))
      measurable_const
  have hf_nn : ∀ q y, 0 ≤ f q y := fun q y => by
    dsimp only [f]; split_ifs
    · exact mul_nonneg (hm_nn q) (by positivity)
    · exact le_rfl
  have hf_le : ∀ q y, f q y ≤ m q * (4 / (16 + (y - γ q) ^ 2)) := fun q y => by
    dsimp only [f]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (hm_nn q) (by positivity)
  have hf_int : ∀ q, Integrable (f q) := fun q =>
    ((integrable_poissonKernel (γ q)).const_mul (m q)).mono' (hf_meas q).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Real.norm_of_nonneg (hf_nn q y)]; exact hf_le q y)
  have hnorm_le : ∀ q, (∫ y in S, ‖f q y‖) ≤ m q * Real.pi := fun q => by
    calc (∫ y in S, ‖f q y‖)
        ≤ ∫ y : ℝ, ‖f q y‖ :=
          setIntegral_le_integral (hf_int q).norm (Eventually.of_forall fun _ => norm_nonneg _)
      _ = ∫ y : ℝ, f q y :=
          integral_congr_ae (Eventually.of_forall fun y => Real.norm_of_nonneg (hf_nn q y))
      _ ≤ ∫ y : ℝ, m q * (4 / (16 + (y - γ q) ^ 2)) :=
          integral_mono (hf_int q) ((integrable_poissonKernel (γ q)).const_mul (m q)) (hf_le q)
      _ = m q * Real.pi := by rw [integral_const_mul, integral_poissonKernel_univ]
  exact setIntegral_tsum_of_summable_integral_norm (fun q => (hf_int q).integrableOn)
    ((hm_sum.mul_right Real.pi).of_nonneg_of_le
      (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm_le)

private theorem criticalState_criticalLine_posTail_asymptotic {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun T : ℝ => T * ∑' q : onLineCopies,
      if T < (centredZero q).im then zeroValueMass F q else 0)
      atTop (𝓝 (4 * criticalAliasCoefficient W₀ *
        (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / Real.pi)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hnull := isConfinedNullVector_of_groundState hW ht hF
  let a := criticalAliasCoefficient W₀
  let M := ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))
  let L := 4 * a * M / Real.pi
  have ha : 0 < a := criticalAliasCoefficient_positive hW
  have hM_eq : M = criticalHalfLineExponentialPair F F := by
    dsimp only [M, criticalHalfLineExponentialPair]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  have hM : 0 < M := hM_eq ▸ exponentialPair_self_pos hd hnull.2.1
  have hL : 0 < L := by dsimp only [L]; positivity
  let m := fun q : onLineCopies => zeroValueMass F q
  let γ := fun q : onLineCopies => (centredZero q).im
  have hm_sum : Summable m := (domain_zeroParseval_of_finiteOffLine hd hf).1
  have hm_nn : ∀ q, 0 ≤ m q := fun q => zeroValueMass_nonneg F q
  let posTail : ℝ → ℝ := fun T => ∑' q : onLineCopies, if T < γ q then m q else 0
  have hposTail_nn : ∀ T, 0 ≤ posTail T := fun T =>
    tsum_nonneg fun q => ite_zero_nonneg (hm_nn q)
  let bp := fun y : ℝ => ‖negativeHalfLineLaplace (cx F) ⟨-4, y⟩‖ ^ 2
  have hbp_int : Integrable bp := integrable_boundary_power hW hnull
  have hbp_meas : Measurable bp := by
    have hc : Continuous fun y : ℝ => negativeHalfLineLaplace (cx F) ⟨-4, y⟩ := by
      simp_rw [laplace_neg_four_eq_paperFT hd]
      exact continuous_paperFT_cx (integrable_boundaryTilt hW hnull)
    exact (hc.norm.pow 2).measurable
  have hbp_tail : Tendsto (fun T : ℝ => T * ∫ y in Ioi T, (a / 2) * bp y) atTop (𝓝 0) := by
    have h0 := (criticalState_boundary_fourier_tail_zero hW ht hF).const_mul (a / 2)
    rw [mul_zero] at h0
    refine squeeze_zero' ?_ ?_ h0
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact mul_nonneg hT (integral_nonneg fun _ => mul_nonneg (by positivity) (sq_nonneg _))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      rw [integral_const_mul]
      have hsub : Ioi T ⊆ {y : ℝ | T < |y|} := fun y (hy : T < y) =>
        lt_of_lt_of_le hy (le_abs_self y)
      have hle : ∫ y in Ioi T, bp y ≤ ∫ y in {y : ℝ | T < |y|}, bp y :=
        setIntegral_mono_set hbp_int.integrableOn
          (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hsub)
      have hm := mul_le_mul_of_nonneg_left hle (mul_nonneg hT (by positivity : (0 : ℝ) ≤ a / 2))
      change T * ((a / 2) * ∫ y in Ioi T, bp y) ≤ (a / 2) * (T * ∫ y in {y : ℝ | T < |y|}, bp y)
      linarith
  have hP_asymp : ∀ {η : ℝ}, 0 < η → η < 1 →
      Tendsto (fun T : ℝ => T * ∫ y in Ioi T,
        ∑' q : onLineCopies, if |y - γ q| < η * y then
          m q * (4 / (16 + (y - γ q) ^ 2)) else 0)
        atTop (𝓝 (Real.pi * L)) := by
    intro η hη0 hη1
    let f_q : onLineCopies → ℝ → ℝ := fun q y =>
      if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0
    have hfq_meas : ∀ q, Measurable (f_q q) := fun q =>
      Measurable.ite (measurableSet_lt (continuous_id.sub continuous_const).abs.measurable
        (continuous_const.mul continuous_id).measurable)
        (measurable_const.mul (measurable_const.div
          (measurable_const.add ((measurable_id.sub measurable_const).pow_const 2))))
        measurable_const
    have hfq_nn : ∀ q y, 0 ≤ f_q q y := fun q y => by
      dsimp only [f_q]; split_ifs
      · exact mul_nonneg (hm_nn q) (by positivity)
      · exact le_rfl
    let P : ℝ → ℝ := fun y => ∑' q : onLineCopies, f_q q y
    have hPm : Measurable P := by
      have heq : P = fun y => (∑' q : onLineCopies, ENNReal.ofReal (f_q q y)).toReal := by
        funext y
        have hs : Summable fun q => f_q q y :=
          hm_sum.of_nonneg_of_le (fun q => hfq_nn q y) fun q => by
            dsimp only [f_q]
            split_ifs
            · exact mul_le_of_le_one_right (hm_nn q)
                ((div_le_one (by positivity)).mpr (by linarith [sq_nonneg (y - γ q)]))
            · exact hm_nn q
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => hfq_nn q y) hs,
          ENNReal.toReal_ofReal (tsum_nonneg fun q => hfq_nn q y)]
      rw [heq]
      exact (Measurable.tsum fun q => (hfq_meas q).ennreal_ofReal).ennreal_toReal
    let J : ℝ → ℝ := fun y => (a / 2) * bp y + P y
    have hJ_nn : ∀ y, 0 ≤ J y := fun y =>
      add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (tsum_nonneg fun q => hfq_nn q y)
    have hJm : Measurable J := (measurable_const.mul hbp_meas).add hPm
    have hloc := (hnull.localized_high_frequency_mass hW hf hη0 hη1).2
    have hpiL : 4 * (a * criticalHalfLineExponentialPair F F) = Real.pi * L := by
      rw [← hM_eq]
      dsimp only [L]
      field_simp [Real.pi_ne_zero]
    rw [hpiL] at hloc
    obtain ⟨Y₀, hY₀⟩ := Metric.tendsto_atTop.mp hloc 1 zero_lt_one
    have hJ_int := tendsto_mul_setIntegral_Ioi_of_sq_tendsto hJ_nn hJm hloc
    have hdiff := hJ_int.sub hbp_tail
    rw [sub_zero] at hdiff
    refine hdiff.congr' ?_
    filter_upwards [eventually_ge_atTop (max Y₀ 1)] with T hT
    have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
    have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have hTY : Y₀ ≤ T := (le_max_left _ _).trans hT
    have hP_int_T : IntegrableOn P (Ioi T) := by
      refine ((integrableOn_Ioi_inv_sq hT0).const_mul (Real.pi * L + 1)).mono'
        hPm.aestronglyMeasurable.restrict ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : T < y)
      have hy0 : 0 < y := lt_trans hT0 hy
      have hP_nn : 0 ≤ P y := tsum_nonneg fun q => hfq_nn q y
      rw [Real.norm_of_nonneg hP_nn]
      have hd_y := hY₀ y (hTY.trans hy.le)
      rw [Real.dist_eq] at hd_y
      have hP_le_J : P y ≤ J y := le_add_of_nonneg_left (mul_nonneg (by positivity) (sq_nonneg _))
      have hub : y ^ 2 * P y ≤ Real.pi * L + 1 := by
        have h1 : y ^ 2 * P y ≤ y ^ 2 * J y := mul_le_mul_of_nonneg_left hP_le_J (sq_nonneg y)
        have h2 : |y ^ 2 * J y - Real.pi * L| < 1 := hd_y
        linarith [(abs_lt.mp h2).2]
      exact ((le_div_iff₀' (sq_pos_of_pos hy0)).mpr hub).trans_eq (div_eq_mul_inv _ _)
    change T * (∫ y in Ioi T, ((a / 2) * bp y + P y)) - T * (∫ y in Ioi T, (a / 2) * bp y) =
      T * ∫ y in Ioi T, P y
    rw [integral_add (hbp_int.const_mul (a / 2)).integrableOn hP_int_T]
    ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := min (1 / 4) (ε / (8 * (L + 1)))
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη4 : η ≤ 1 / 4 := min_le_left _ _
  have hη1 : η < 1 := lt_of_le_of_lt hη4 (by norm_num)
  have hηL : η * L ≤ ε / 8 := by
    have hle : η ≤ ε / (8 * (L + 1)) := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_right hle hL.le
    calc η * L ≤ ε / (8 * (L + 1)) * (L + 1) := by nlinarith [hε]
      _ = ε / 8 := by field_simp [show (L + 1) ≠ 0 by linarith]
  have hδ_int : 0 < Real.pi * min (ε / 4) (L / 4) := by positivity
  obtain ⟨T₁, hT₁⟩ := Metric.tendsto_atTop.mp (hP_asymp hη0 hη1)
    (Real.pi * min (ε / 4) (L / 4)) hδ_int
  set T₂ : ℝ := (1 + η) * max (max T₁ 1) (64 / (η * Real.pi * η))
  refine ⟨max T₂ (T₁ + 1), fun T hT => ?_⟩
  have hTT₂ : T₂ ≤ T := (le_max_left _ _).trans hT
  have hTT₁ : T₁ + 1 ≤ T := (le_max_right _ _).trans hT
  have hT_pos : 0 < T := lt_of_lt_of_le (by dsimp only [T₂]; positivity) hTT₂
  have hlo_bound : L - ε < T * posTail T := by
    set T' := T / (1 - η)
    have h1mη : 0 < 1 - η := by linarith
    have hT'_pos : 0 < T' := div_pos hT_pos h1mη
    have hT'_ge : T₁ ≤ T' := by
      have hle : T ≤ T' := le_div_self hT_pos.le h1mη (by linarith)
      linarith
    have hd1 := hT₁ T' hT'_ge
    rw [Real.dist_eq] at hd1
    have hP_lb : Real.pi * (L - ε / 4) ≤ T' * ∫ y in Ioi T',
        ∑' q : onLineCopies, if |y - γ q| < η * y then
          m q * (4 / (16 + (y - γ q) ^ 2)) else 0 := by
      have hmin : Real.pi * min (ε / 4) (L / 4) ≤ Real.pi * (ε / 4) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) Real.pi_pos.le
      linarith [(abs_lt.mp hd1).1]
    rw [setIntegral_poissonWindow_eq_tsum hm_sum hm_nn η (Ioi T')] at hP_lb
    have hterm_le : ∀ q : onLineCopies,
        (∫ y in Ioi T', if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0) ≤
          if T < γ q then Real.pi * m q else 0 := fun q => by
      split_ifs with hγT
      · have hf_le : ∀ y : ℝ,
            (if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0) ≤
              m q * (4 / (16 + (y - γ q) ^ 2)) := fun y => by
          split_ifs
          · exact le_rfl
          · exact mul_nonneg (hm_nn q) (by positivity)
        have hfm : Measurable fun y : ℝ =>
            if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0 :=
          Measurable.ite (measurableSet_lt (continuous_id.sub continuous_const).abs.measurable
            (continuous_const.mul continuous_id).measurable)
            (measurable_const.mul (measurable_const.div
              (measurable_const.add ((measurable_id.sub measurable_const).pow_const 2))))
            measurable_const
        have hfi : IntegrableOn (fun y : ℝ =>
            if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0) (Ioi T') := by
          refine ((integrable_poissonKernel (γ q)).const_mul (m q)).integrableOn.mono'
            hfm.aestronglyMeasurable.restrict ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _
          rw [Real.norm_of_nonneg (ite_zero_nonneg (mul_nonneg (hm_nn q) (by positivity)))]
          exact hf_le y
        have hm1 := setIntegral_mono_on hfi
          ((integrable_poissonKernel (γ q)).const_mul (m q)).integrableOn measurableSet_Ioi
          fun y _ => hf_le y
        rw [integral_const_mul] at hm1
        exact hm1.trans ((mul_le_mul_of_nonneg_left (setIntegral_poissonKernel_le_pi (γ q) (Ioi T'))
          (hm_nn q)).trans_eq (mul_comm _ _))
      · have hzero : ∀ y ∈ Ioi T',
            (if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0) = 0 := by
          intro y (hy : T' < y)
          rw [if_neg]
          intro habs
          have h1 : (1 - η) * y < γ q := by linarith [(abs_lt.mp habs).2]
          have h2 : T < (1 - η) * y := by
            have hm_lt := mul_lt_mul_of_pos_left hy h1mη
            have heT : (1 - η) * T' = T := mul_div_cancel₀ T h1mη.ne'
            rwa [heT] at hm_lt
          exact hγT (lt_trans h2 h1)
        rw [setIntegral_eq_zero_of_forall_eq_zero hzero]
    have hsum_rhs : Summable fun q : onLineCopies => if T < γ q then Real.pi * m q else 0 :=
      (hm_sum.mul_left Real.pi).of_nonneg_of_le
        (fun q => ite_zero_nonneg (mul_nonneg Real.pi_pos.le (hm_nn q)))
        (fun q => ite_zero_le (mul_nonneg Real.pi_pos.le (hm_nn q)))
    have hsum_int : Summable fun q : onLineCopies =>
        ∫ y in Ioi T', if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0 :=
      hsum_rhs.of_nonneg_of_le
        (fun q => integral_nonneg fun y => ite_zero_nonneg (mul_nonneg (hm_nn q) (by positivity)))
        hterm_le
    have htsum_le := Summable.tsum_le_tsum hterm_le hsum_int hsum_rhs
    have hrhs_eq : (∑' q : onLineCopies, if T < γ q then Real.pi * m q else 0) =
        Real.pi * posTail T := by
      rw [← tsum_mul_left]
      congr 1; funext q; split_ifs <;> ring
    rw [hrhs_eq] at htsum_le
    have hm_T' := mul_le_mul_of_nonneg_left htsum_le hT'_pos.le
    have hcomb := hP_lb.trans hm_T'
    have hrel : T' * (Real.pi * posTail T) = Real.pi / (1 - η) * (T * posTail T) := by
      dsimp only [T']; ring
    rw [hrel] at hcomb
    have hmul := mul_le_mul_of_nonneg_left hcomb (div_nonneg h1mη.le Real.pi_pos.le)
    have hsimpL : (1 - η) / Real.pi * (Real.pi * (L - ε / 4)) = (1 - η) * (L - ε / 4) := by
      field_simp [Real.pi_ne_zero]
    have hsimpR : (1 - η) / Real.pi * (Real.pi / (1 - η) * (T * posTail T)) = T * posTail T := by
      field_simp [Real.pi_ne_zero, h1mη.ne']
    rw [hsimpL, hsimpR] at hmul
    nlinarith [hηL, hη0, hε]
  have hhi_bound : T * posTail T < L + ε := by
    set T'' := T / (1 + η)
    have h1pη : 0 < 1 + η := by linarith
    have hT''_pos : 0 < T'' := div_pos hT_pos h1pη
    have hT''_max : max (max T₁ 1) (64 / (η * Real.pi * η)) ≤ T'' := by
      have h := (le_div_iff₀' h1pη).mpr hTT₂
      simpa only [T₂, T''] using h
    have hT''_T₁ : T₁ ≤ T'' := ((le_max_left _ _).trans (le_max_left _ _)).trans hT''_max
    have hT''_big : 64 / (η * Real.pi * η) ≤ T'' := (le_max_right _ _).trans hT''_max
    have hd2 := hT₁ T'' hT''_T₁
    rw [Real.dist_eq] at hd2
    have hP_ub : T'' * (∫ y in Ioi T'',
        ∑' q : onLineCopies, if |y - γ q| < η * y then
          m q * (4 / (16 + (y - γ q) ^ 2)) else 0) ≤ Real.pi * (L + min (ε / 4) (L / 4)) := by
      linarith [(abs_lt.mp hd2).2]
    rw [setIntegral_poissonWindow_eq_tsum hm_sum hm_nn η (Ioi T'')] at hP_ub
    set R := η / 2 * T''
    have hR_pos : 0 < R := by dsimp only [R]; positivity
    have h8R : 8 / R ≤ Real.pi * η / 4 := by
      have h1 : 64 ≤ T'' * (η * Real.pi * η) := (div_le_iff₀ (by positivity)).mp hT''_big
      rw [div_le_iff₀ hR_pos]
      dsimp only [R]
      nlinarith
    have hker_pos : 0 < Real.pi - 8 / R := by nlinarith [Real.pi_pos, h8R, hη4]
    have hterm_ge : ∀ q : onLineCopies,
        (if T < γ q then (Real.pi - 8 / R) * m q else 0) ≤
          ∫ y in Ioi T'', if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0 := by
      intro q
      split_ifs with hγT
      · have hTT'' : T = (1 + η) * T'' := (mul_div_cancel₀ T h1pη.ne').symm
        let I_q := Ioo (γ q - R) (γ q + R)
        have hsub_Ioi : I_q ⊆ Ioi T'' := fun y hy => by
          rw [mem_Ioo] at hy
          rw [mem_Ioi]
          have hηT'' : 0 < η * T'' := mul_pos hη0 hT''_pos
          have hy1 : γ q - η / 2 * T'' < y := hy.1
          linarith [hy1, hγT, hTT'', hηT'']
        have hnear_I : ∀ y ∈ I_q, |y - γ q| < η * y := fun y hy => by
          have hy_gt : T'' < y := hsub_Ioi hy
          rw [mem_Ioo] at hy
          have habs : |y - γ q| < R := abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
          dsimp only [R] at habs
          have hηy : η * T'' < η * y := mul_lt_mul_of_pos_left hy_gt hη0
          have hηT'' : 0 < η * T'' := mul_pos hη0 hT''_pos
          linarith
        have hfm : Measurable fun y : ℝ =>
            if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0 :=
          Measurable.ite (measurableSet_lt (continuous_id.sub continuous_const).abs.measurable
            (continuous_const.mul continuous_id).measurable)
            (measurable_const.mul (measurable_const.div
              (measurable_const.add ((measurable_id.sub measurable_const).pow_const 2))))
            measurable_const
        have hfi : IntegrableOn (fun y : ℝ =>
            if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0) (Ioi T'') := by
          refine ((integrable_poissonKernel (γ q)).const_mul (m q)).integrableOn.mono'
            hfm.aestronglyMeasurable.restrict ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _
          rw [Real.norm_of_nonneg (ite_zero_nonneg (mul_nonneg (hm_nn q) (by positivity)))]
          exact ite_zero_le (mul_nonneg (hm_nn q) (by positivity))
        have hmono : (∫ y in I_q,
            if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0) ≤
              ∫ y in Ioi T'',
                if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0 :=
          setIntegral_mono_set hfi
            (Eventually.of_forall fun y => ite_zero_nonneg (mul_nonneg (hm_nn q) (by positivity)))
            (Eventually.of_forall hsub_Ioi)
        have heq_Iq : (∫ y in I_q,
            if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0) =
              m q * ∫ y in I_q, 4 / (16 + (y - γ q) ^ 2) := by
          rw [← integral_const_mul]
          exact setIntegral_congr_fun measurableSet_Ioo fun y hy => if_pos (hnear_I y hy)
        rw [heq_Iq] at hmono
        have hker := mul_le_mul_of_nonneg_right
          (pi_sub_div_le_setIntegral_poissonKernel (γ q) hR_pos) (hm_nn q)
        linarith [hmono, hker]
      · exact integral_nonneg fun y => ite_zero_nonneg (mul_nonneg (hm_nn q) (by positivity))
    have hsum_lhs : Summable fun q : onLineCopies =>
        if T < γ q then (Real.pi - 8 / R) * m q else 0 :=
      (hm_sum.mul_left (Real.pi - 8 / R)).of_nonneg_of_le
        (fun q => ite_zero_nonneg (mul_nonneg hker_pos.le (hm_nn q)))
        (fun q => ite_zero_le (mul_nonneg hker_pos.le (hm_nn q)))
    have hsum_rhs : Summable fun q : onLineCopies =>
        ∫ y in Ioi T'', if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0 := by
      refine (hm_sum.mul_left Real.pi).of_nonneg_of_le
        (fun q => integral_nonneg fun y => ite_zero_nonneg (mul_nonneg (hm_nn q) (by positivity)))
        fun q => ?_
      have hfm : Measurable fun y : ℝ =>
          if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0 :=
        Measurable.ite (measurableSet_lt (continuous_id.sub continuous_const).abs.measurable
          (continuous_const.mul continuous_id).measurable)
          (measurable_const.mul (measurable_const.div
            (measurable_const.add ((measurable_id.sub measurable_const).pow_const 2))))
          measurable_const
      have hfi : IntegrableOn (fun y : ℝ =>
          if |y - γ q| < η * y then m q * (4 / (16 + (y - γ q) ^ 2)) else 0) (Ioi T'') := by
        refine ((integrable_poissonKernel (γ q)).const_mul (m q)).integrableOn.mono'
          hfm.aestronglyMeasurable.restrict ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y _
        rw [Real.norm_of_nonneg (ite_zero_nonneg (mul_nonneg (hm_nn q) (by positivity)))]
        exact ite_zero_le (mul_nonneg (hm_nn q) (by positivity))
      have hm1 := setIntegral_mono_on hfi
        ((integrable_poissonKernel (γ q)).const_mul (m q)).integrableOn measurableSet_Ioi fun y _ =>
          ite_zero_le (mul_nonneg (hm_nn q) (by positivity))
      rw [integral_const_mul] at hm1
      exact hm1.trans ((mul_le_mul_of_nonneg_left (setIntegral_poissonKernel_le_pi (γ q) (Ioi T''))
        (hm_nn q)).trans_eq (mul_comm _ _))
    have htsum_ge := Summable.tsum_le_tsum hterm_ge hsum_lhs hsum_rhs
    have hlhs_eq : (∑' q : onLineCopies, if T < γ q then (Real.pi - 8 / R) * m q else 0) =
        (Real.pi - 8 / R) * posTail T := by
      rw [← tsum_mul_left]
      congr 1; funext q; split_ifs <;> ring
    rw [hlhs_eq] at htsum_ge
    have hm_T'' := mul_le_mul_of_nonneg_left htsum_ge hT''_pos.le
    have hcomb := hm_T''.trans hP_ub
    have hker_lb : Real.pi * (1 - η / 4) ≤ Real.pi - 8 / R := by linarith [h8R]
    have hpos1 : 0 < 1 - η / 4 := by linarith [hη4]
    have hstep1 : Real.pi * (1 - η / 4) * (T'' * posTail T) ≤
        Real.pi * (L + min (ε / 4) (L / 4)) := by
      calc Real.pi * (1 - η / 4) * (T'' * posTail T)
          = T'' * ((Real.pi * (1 - η / 4)) * posTail T) := by ring
        _ ≤ T'' * ((Real.pi - 8 / R) * posTail T) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hker_lb (hposTail_nn T)) hT''_pos.le
        _ ≤ Real.pi * (L + min (ε / 4) (L / 4)) := hcomb
    have hstep2 : (1 - η / 4) * (T * posTail T) ≤ (1 + η) * (L + min (ε / 4) (L / 4)) := by
      have hc1 : (1 - η / 4) * (T'' * posTail T) ≤ L + min (ε / 4) (L / 4) :=
        le_of_mul_le_mul_left (by linarith [hstep1] :
          Real.pi * ((1 - η / 4) * (T'' * posTail T)) ≤
            Real.pi * (L + min (ε / 4) (L / 4))) Real.pi_pos
      have hm2 := mul_le_mul_of_nonneg_left hc1 h1pη.le
      have heT : (1 + η) * ((1 - η / 4) * (T'' * posTail T)) =
          (1 - η / 4) * (T * posTail T) := by
        dsimp only [T'']
        field_simp [h1pη.ne']
      linarith
    have hmin_ε : min (ε / 4) (L / 4) ≤ ε / 4 := min_le_left _ _
    have hmin_L : min (ε / 4) (L / 4) ≤ L / 4 := min_le_right _ _
    have hη_min : η * min (ε / 4) (L / 4) ≤ ε / 32 := by
      have hm := mul_le_mul_of_nonneg_left hmin_L hη0.le
      linarith [hηL]
    have hη_ε : η * ε ≤ ε / 4 := (mul_le_mul_of_nonneg_right hη4 hε.le).trans_eq (by ring)
    have hstrict : (1 - η / 4) * (T * posTail T) < (1 - η / 4) * (L + ε) := by
      nlinarith only [hstep2, hmin_ε, hηL, hη_min, hη_ε, hε]
    exact lt_of_mul_lt_mul_left hstrict hpos1.le
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- **Exact high-frequency tail of critical-line zero samples under `FiniteOffLine`.** For a
threshold ground state `F`, `T · ∑_{|γ_q| > T} ‖L F(iγ_q)‖² → 8 a M / π` as `T → +∞`. -/
theorem criticalState_criticalLine_tail_asymptotic {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun T : ℝ => T * ∑' q : onLineCopies,
      if T < |(centredZero q).im| then zeroValueMass F q else 0)
      atTop (𝓝 (8 * criticalAliasCoefficient W₀ *
        (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / Real.pi)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hm_sum : Summable (fun q : onLineCopies => zeroValueMass F q) :=
    (domain_zeroParseval_of_finiteOffLine hd hf).1
  have hm_nn : ∀ q : onLineCopies, 0 ≤ zeroValueMass F q := fun q => zeroValueMass_nonneg F q
  have hpos := (criticalState_criticalLine_posTail_asymptotic hW ht hF hf).const_mul 2
  rw [show 2 * (4 * criticalAliasCoefficient W₀ *
      (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / Real.pi) =
    8 * criticalAliasCoefficient W₀ *
      (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / Real.pi by ring] at hpos
  refine hpos.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  let fpos : onLineCopies → ℝ := fun q => if T < (centredZero q).im then zeroValueMass F q else 0
  let fneg : onLineCopies → ℝ := fun q => if (centredZero q).im < -T then zeroValueMass F q else 0
  have hs_pos : Summable fpos := hm_sum.of_nonneg_of_le
    (fun q => ite_zero_nonneg (hm_nn q))
    (fun q => ite_zero_le (hm_nn q))
  have hs_neg : Summable fneg := hm_sum.of_nonneg_of_le
    (fun q => ite_zero_nonneg (hm_nn q))
    (fun q => ite_zero_le (hm_nn q))
  have hneg_eq : (∑' q : onLineCopies, fneg q) = ∑' q : onLineCopies, fpos q := by
    rw [← reflectOnLine.tsum_eq fneg]
    congr 1; funext q
    dsimp only [fneg, fpos]
    rw [im_centredZero_reflectOnLine, zeroValueMass_reflectOnLine]
    have hiff : (-(centredZero q).im < -T) ↔ (T < (centredZero q).im) :=
      ⟨fun h => by linarith, fun h => by linarith⟩
    simp only [hiff]
  have htot_eq : (∑' q : onLineCopies, if T < |(centredZero q).im| then zeroValueMass F q else 0) =
      (∑' q : onLineCopies, fpos q) + ∑' q : onLineCopies, fneg q := by
    rw [← Summable.tsum_add hs_pos hs_neg]
    congr 1; funext q
    dsimp only [fpos, fneg]
    rcases le_total 0 (centredZero q).im with h0 | h0
    · rw [abs_of_nonneg h0]
      have hneg_false : ¬ (centredZero q).im < -T := by linarith
      rw [if_neg hneg_false, add_zero]
    · rw [abs_of_nonpos h0]
      have hpos_false : ¬ T < (centredZero q).im := by linarith
      rw [if_neg hpos_false, zero_add]
      have hiff : (T < -(centredZero q).im) ↔ ((centredZero q).im < -T) :=
        ⟨fun h => by linarith, fun h => by linarith⟩
      simp only [hiff]
  rw [htot_eq, hneg_eq]
  ring

private theorem posFirstMoment_add_mul_posTail_eq_integral {m γ : onLineCopies → ℝ}
    (hm_sum : Summable m) (hm_nn : ∀ q, 0 ≤ m q) {T : ℝ} (hT : 0 ≤ T) :
    (∑' q : onLineCopies, if 0 < γ q ∧ γ q ≤ T then γ q * m q else 0) +
      T * (∑' q : onLineCopies, if T < γ q then m q else 0) =
      ∫ u in Icc 0 T, ∑' q : onLineCopies, if u < γ q then m q else 0 := by
  let g : onLineCopies → ℝ → ℝ := fun q u => if u < γ q then m q else 0
  have hg_meas : ∀ q, Measurable (g q) := fun q =>
    Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  have hg_int : ∀ q, IntegrableOn (g q) (Icc 0 T) := fun q => by
    refine (continuousOn_const (c := m q)).integrableOn_Icc.mono'
      (hg_meas q).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u _
    dsimp only [g]
    split_ifs
    · rw [Real.norm_of_nonneg (hm_nn q)]
    · rw [norm_zero]; exact hm_nn q
  have hnorm_le : ∀ q, (∫ u in Icc 0 T, ‖g q u‖) ≤ T * m q := fun q => by
    have hm1 := setIntegral_mono_on (hg_int q).norm
      (continuousOn_const (c := m q)).integrableOn_Icc measurableSet_Icc fun u _ => by
        dsimp only [g]
        split_ifs
        · rw [Real.norm_of_nonneg (hm_nn q)]
        · rw [norm_zero]; exact hm_nn q
    rwa [setIntegral_const, Real.volume_real_Icc_of_le hT, sub_zero, smul_eq_mul] at hm1
  have htsum_int : (∫ u in Icc 0 T, ∑' q : onLineCopies, g q u) =
      ∑' q : onLineCopies, ∫ u in Icc 0 T, g q u :=
    setIntegral_tsum_of_summable_integral_norm hg_int
      ((hm_sum.mul_left T).of_nonneg_of_le
        (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm_le)
  rw [htsum_int]
  have hterm : ∀ q : onLineCopies,
      (∫ u in Icc 0 T, g q u) =
        (if 0 < γ q ∧ γ q ≤ T then γ q * m q else 0) + (if T < γ q then T * m q else 0) := fun q => by
    rcases le_or_gt (γ q) 0 with hle0 | hgt0
    · have hzero : ∀ u ∈ Icc 0 T, g q u = 0 := fun u hu => by
        dsimp only [g]; rw [if_neg]; linarith [hu.1]
      rw [setIntegral_eq_zero_of_forall_eq_zero hzero,
        if_neg (fun h => not_lt.mpr hle0 h.1), if_neg (not_lt.mpr (hle0.trans hT)), add_zero]
    · rcases le_or_gt (γ q) T with hleT | hgtT
      · have heq : (Icc 0 T).indicator (g q) = (Ico 0 (γ q)).indicator (fun _ => m q) := by
          funext u
          by_cases hu : u ∈ Ico 0 (γ q)
          · have huI : u ∈ Icc 0 T := ⟨hu.1, hu.2.le.trans hleT⟩
            rw [indicator_of_mem huI, indicator_of_mem hu]
            dsimp only [g]
            exact if_pos hu.2
          · rw [indicator_of_notMem hu]
            by_cases hI : u ∈ Icc 0 T
            · rw [indicator_of_mem hI]
              dsimp only [g]
              exact if_neg fun hlt => hu ⟨hI.1, hlt⟩
            · rw [indicator_of_notMem hI]
        rw [← integral_indicator measurableSet_Icc, heq, integral_indicator measurableSet_Ico,
          setIntegral_const, Real.volume_real_Ico_of_le hgt0.le, sub_zero, smul_eq_mul,
          if_pos ⟨hgt0, hleT⟩, if_neg (not_lt.mpr hleT), add_zero]
      · have heq : ∀ u ∈ Ioo 0 T, g q u = m q := fun u hu => by
          dsimp only [g]; exact if_pos (lt_trans hu.2 hgtT)
        rw [integral_Icc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo heq,
          setIntegral_const, Real.volume_real_Ioo_of_le hT, sub_zero, smul_eq_mul,
          if_neg (fun h => not_lt.mpr h.2 hgtT), if_pos hgtT, zero_add]
  have hs1 : Summable fun q : onLineCopies => if 0 < γ q ∧ γ q ≤ T then γ q * m q else 0 :=
    (hm_sum.mul_left T).of_nonneg_of_le
      (fun q => by
        split_ifs with h
        · exact mul_nonneg h.1.le (hm_nn q)
        · exact le_rfl)
      (fun q => by
        split_ifs with h
        · exact mul_le_mul_of_nonneg_right h.2 (hm_nn q)
        · exact mul_nonneg hT (hm_nn q))
  have hs2 : Summable fun q : onLineCopies => if T < γ q then T * m q else 0 :=
    (hm_sum.mul_left T).of_nonneg_of_le
      (fun q => ite_zero_nonneg (mul_nonneg hT (hm_nn q)))
      (fun q => ite_zero_le (mul_nonneg hT (hm_nn q)))
  simp_rw [hterm]
  rw [Summable.tsum_add hs1 hs2, ← tsum_mul_left]
  congr 2; funext q; split_ifs <;> ring

/-- **Exact logarithmic asymptotic of the critical-line first ordinate moment under `FiniteOffLine`.**
For a threshold ground state `F`,
`(log T)⁻¹ · ∑_{|γ_q| ≤ T} |γ_q| ‖L F(iγ_q)‖² → 8 a M / π` as `T → +∞`, sharpening
`criticalState_criticalLine_firstMoment_not_summable` to its exact universal slope. -/
theorem criticalState_criticalLine_firstMoment_asymptotic {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hf : BacklundConverse.FiniteOffLine) :
    Tendsto (fun T : ℝ => (Real.log T)⁻¹ * ∑' q : onLineCopies,
      if |(centredZero q).im| ≤ T then |(centredZero q).im| * zeroValueMass F q else 0)
      atTop (𝓝 (8 * criticalAliasCoefficient W₀ *
        (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / Real.pi)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  let m := fun q : onLineCopies => zeroValueMass F q
  let γ := fun q : onLineCopies => (centredZero q).im
  have hm_sum : Summable m := (domain_zeroParseval_of_finiteOffLine hd hf).1
  have hm_nn : ∀ q, 0 ≤ m q := fun q => zeroValueMass_nonneg F q
  let L := 4 * criticalAliasCoefficient W₀ *
    (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / Real.pi
  let posTail : ℝ → ℝ := fun u => ∑' q : onLineCopies, if u < γ q then m q else 0
  have hposTail_sum : ∀ u, Summable (fun q : onLineCopies => if u < γ q then m q else 0) :=
    fun u => hm_sum.of_nonneg_of_le
      (fun q => ite_zero_nonneg (hm_nn q))
      (fun q => ite_zero_le (hm_nn q))
  have hposTail_anti : Antitone posTail := fun u₁ u₂ h12 => by
    refine Summable.tsum_le_tsum (fun q => ?_) (hposTail_sum u₂) (hposTail_sum u₁)
    split_ifs with h2 h1
    · exact le_rfl
    · exfalso; linarith
    · exact hm_nn q
    · exact le_rfl
  have hposTail_meas : Measurable posTail := hposTail_anti.measurable
  have hposTail_nn : ∀ u, 0 ≤ posTail u := fun u =>
    tsum_nonneg fun q => ite_zero_nonneg (hm_nn q)
  have hposTail_le : ∀ u, posTail u ≤ ∑' q, m q := fun u =>
    Summable.tsum_le_tsum (fun q => ite_zero_le (hm_nn q)) (hposTail_sum u) hm_sum
  have hposTail_int : ∀ A B : ℝ, IntegrableOn posTail (Icc A B) := fun A B => by
    refine (continuousOn_const (c := ∑' q, m q)).integrableOn_Icc.mono'
      hposTail_meas.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u _
    rw [Real.norm_of_nonneg (hposTail_nn u)]
    exact hposTail_le u
  have htail_lim := criticalState_criticalLine_posTail_asymptotic hW ht hF hf
  have hint_lim : Tendsto (fun T : ℝ => (Real.log T)⁻¹ * ∫ u in Icc 0 T, posTail u)
      atTop (𝓝 L) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨U₁, hU₁⟩ := Metric.tendsto_atTop.mp htail_lim (ε / 4) (by positivity)
    set U₀ := max U₁ 2
    have hU₀_pos : 0 < U₀ := by dsimp only [U₀]; positivity
    have hU₀_ge1 : 1 ≤ U₀ := by dsimp only [U₀]; linarith [le_max_right U₁ 2]
    set C₀ : ℝ := U₀ * (∑' q, m q) + (|L| + ε) * |Real.log U₀| + 1
    have hC₀_pos : 0 < C₀ := by
      have h1 : 0 ≤ U₀ * (∑' q, m q) := mul_nonneg hU₀_pos.le (tsum_nonneg hm_nn)
      have h2 : 0 ≤ (|L| + ε) * |Real.log U₀| := by positivity
      linarith
    refine ⟨max (U₀ + 1) (Real.exp (4 * C₀ / ε)), fun T hT => ?_⟩
    have hTU : U₀ + 1 ≤ T := (le_max_left _ _).trans hT
    have hTexp : Real.exp (4 * C₀ / ε) ≤ T := (le_max_right _ _).trans hT
    have hT_pos : 0 < T := by linarith
    have hlogT_big : 4 * C₀ / ε ≤ Real.log T := (Real.le_log_iff_exp_le hT_pos).mpr hTexp
    have hlogT_pos : 0 < Real.log T := lt_of_lt_of_le (by positivity) hlogT_big
    have hsplit : (∫ u in Icc 0 T, posTail u) =
        (∫ u in Icc 0 U₀, posTail u) + ∫ u in Ioc U₀ T, posTail u := by
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        ← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
          ((hposTail_int 0 U₀).mono_set Ioc_subset_Icc_self)
          ((hposTail_int U₀ T).mono_set Ioc_subset_Icc_self),
        Ioc_union_Ioc_eq_Ioc hU₀_pos.le (by linarith)]
    have hhead_le : ∫ u in Icc 0 U₀, posTail u ≤ U₀ * (∑' q, m q) := by
      have hm1 := setIntegral_mono_on (hposTail_int 0 U₀)
        (continuousOn_const (c := ∑' q, m q)).integrableOn_Icc measurableSet_Icc
        fun u _ => hposTail_le u
      rwa [setIntegral_const, Real.volume_real_Icc_of_le hU₀_pos.le, sub_zero, smul_eq_mul] at hm1
    have hinv_int : IntegrableOn (fun u : ℝ => u⁻¹) (Ioc U₀ T) :=
      (continuousOn_id.inv₀ fun u (hu : u ∈ Icc U₀ T) =>
        (lt_of_lt_of_le hU₀_pos hu.1).ne').integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hlog_int : (∫ u in Ioc U₀ T, u⁻¹) = Real.log T - Real.log U₀ := by
      rw [← intervalIntegral.integral_of_le (by linarith : U₀ ≤ T),
        integral_inv_of_pos hU₀_pos hT_pos, Real.log_div hT_pos.ne' hU₀_pos.ne']
    have hpt_hi : ∀ u ∈ Ioc U₀ T, posTail u ≤ (L + ε / 4) * u⁻¹ := fun u hu => by
      have hu0 : 0 < u := lt_trans hU₀_pos hu.1
      have hd1 := hU₁ u ((le_max_left U₁ 2).trans hu.1.le)
      rw [Real.dist_eq] at hd1
      have hub : u * posTail u ≤ L + ε / 4 := by linarith [(abs_lt.mp hd1).2]
      exact ((le_div_iff₀' hu0).mpr hub).trans_eq (div_eq_mul_inv _ _)
    have hpt_lo : ∀ u ∈ Ioc U₀ T, (L - ε / 4) * u⁻¹ ≤ posTail u := fun u hu => by
      have hu0 : 0 < u := lt_trans hU₀_pos hu.1
      have hd1 := hU₁ u ((le_max_left U₁ 2).trans hu.1.le)
      rw [Real.dist_eq] at hd1
      have hlb : L - ε / 4 ≤ u * posTail u := by linarith [(abs_lt.mp hd1).1]
      exact (div_eq_mul_inv (L - ε / 4) u).symm.le.trans ((div_le_iff₀' hu0).mpr hlb)
    have hint_hi := setIntegral_mono_on ((hposTail_int U₀ T).mono_set Ioc_subset_Icc_self)
      (hinv_int.const_mul (L + ε / 4)) measurableSet_Ioc hpt_hi
    have hint_lo := setIntegral_mono_on (hinv_int.const_mul (L - ε / 4))
      ((hposTail_int U₀ T).mono_set Ioc_subset_Icc_self) measurableSet_Ioc hpt_lo
    rw [integral_const_mul, hlog_int] at hint_hi hint_lo
    have hhead_nn : 0 ≤ ∫ u in Icc 0 U₀, posTail u :=
      setIntegral_nonneg measurableSet_Icc fun u _ => hposTail_nn u
    have hlogU_nn : 0 ≤ Real.log U₀ := Real.log_nonneg hU₀_ge1
    have habs_logU : |Real.log U₀| = Real.log U₀ := abs_of_nonneg hlogU_nn
    have hC₀_bound1 : U₀ * (∑' q, m q) + |(L + ε / 4) * Real.log U₀| < C₀ := by
      dsimp only [C₀]
      rw [abs_mul, habs_logU]
      have h1 : |L + ε / 4| ≤ |L| + ε := by
        have hn := norm_add_le L (ε / 4)
        simp only [Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < ε / 4 by positivity)] at hn
        linarith
      nlinarith [mul_le_mul_of_nonneg_right h1 hlogU_nn]
    have hC₀_bound2 : |(L - ε / 4) * Real.log U₀| < C₀ := by
      dsimp only [C₀]
      rw [abs_mul, habs_logU]
      have h1 : |L - ε / 4| ≤ |L| + ε := by
        have hn := norm_sub_le L (ε / 4)
        simp only [Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < ε / 4 by positivity)] at hn
        linarith
      have h2 : 0 ≤ U₀ * (∑' q, m q) := mul_nonneg hU₀_pos.le (tsum_nonneg hm_nn)
      nlinarith [mul_le_mul_of_nonneg_right h1 hlogU_nn]
    have h4C₀ : 4 * C₀ ≤ Real.log T * ε := (div_le_iff₀ hε).mp hlogT_big
    have hX_lo : (L - ε) * Real.log T < ∫ u in Icc 0 T, posTail u := by
      have h1 := le_abs_self ((L - ε / 4) * Real.log U₀)
      rw [hsplit]
      nlinarith only [hhead_nn, hint_lo, h1, hC₀_bound2, h4C₀, hε, hlogT_pos]
    have hX_hi : ∫ u in Icc 0 T, posTail u < (L + ε) * Real.log T := by
      have h1 := neg_le_abs ((L + ε / 4) * Real.log U₀)
      rw [hsplit]
      nlinarith only [hhead_le, hint_hi, h1, hC₀_bound1, h4C₀, hε, hlogT_pos]
    have hdiv_lo : L - ε < (Real.log T)⁻¹ * ∫ u in Icc 0 T, posTail u := by
      have hm := mul_lt_mul_of_pos_left hX_lo (inv_pos.mpr hlogT_pos)
      rwa [show (Real.log T)⁻¹ * ((L - ε) * Real.log T) = L - ε by
        field_simp [hlogT_pos.ne']] at hm
    have hdiv_hi : (Real.log T)⁻¹ * ∫ u in Icc 0 T, posTail u < L + ε := by
      have hm := mul_lt_mul_of_pos_left hX_hi (inv_pos.mpr hlogT_pos)
      rwa [show (Real.log T)⁻¹ * ((L + ε) * Real.log T) = L + ε by
        field_simp [hlogT_pos.ne']] at hm
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  have hrem_lim : Tendsto (fun T : ℝ => (Real.log T)⁻¹ * (T * posTail T)) atTop (𝓝 0) := by
    have hinv_log : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp Real.tendsto_log_atTop
    simpa only [zero_mul] using hinv_log.mul htail_lim
  have hpos_mom : Tendsto (fun T : ℝ => (Real.log T)⁻¹ * ∑' q : onLineCopies,
      if 0 < γ q ∧ γ q ≤ T then γ q * m q else 0) atTop (𝓝 L) := by
    have hdiff := hint_lim.sub hrem_lim
    rw [sub_zero] at hdiff
    refine hdiff.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hid := posFirstMoment_add_mul_posTail_eq_integral (γ := γ) hm_sum hm_nn hT
    change (Real.log T)⁻¹ * (∫ u in Icc 0 T, posTail u) - (Real.log T)⁻¹ * (T * posTail T) = _
    rw [← mul_sub, ← hid]
    ring
  have htwo := hpos_mom.const_mul 2
  rw [show 2 * L = 8 * criticalAliasCoefficient W₀ *
      (∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) / Real.pi by dsimp only [L]; ring] at htwo
  refine htwo.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  let fpos : onLineCopies → ℝ := fun q => if 0 < γ q ∧ γ q ≤ T then γ q * m q else 0
  let fneg : onLineCopies → ℝ := fun q => if -T ≤ γ q ∧ γ q < 0 then (-γ q) * m q else 0
  have hs_pos : Summable fpos := (hm_sum.mul_left T).of_nonneg_of_le
    (fun q => by
      dsimp only [fpos]; split_ifs with h
      · exact mul_nonneg h.1.le (hm_nn q)
      · exact le_rfl)
    (fun q => by
      dsimp only [fpos]; split_ifs with h
      · exact mul_le_mul_of_nonneg_right h.2 (hm_nn q)
      · exact mul_nonneg hT (hm_nn q))
  have hs_neg : Summable fneg := (hm_sum.mul_left T).of_nonneg_of_le
    (fun q => by
      dsimp only [fneg]; split_ifs with h
      · exact mul_nonneg (by linarith [h.2]) (hm_nn q)
      · exact le_rfl)
    (fun q => by
      dsimp only [fneg]; split_ifs with h
      · exact mul_le_mul_of_nonneg_right (by linarith [h.1]) (hm_nn q)
      · exact mul_nonneg hT (hm_nn q))
  have hneg_eq : (∑' q : onLineCopies, fneg q) = ∑' q : onLineCopies, fpos q := by
    rw [← reflectOnLine.tsum_eq fneg]
    congr 1; funext q
    dsimp only [fneg, fpos, γ, m]
    simp only [im_centredZero_reflectOnLine, zeroValueMass_reflectOnLine, neg_neg]
    have hiff : (-T ≤ -(centredZero q).im ∧ -(centredZero q).im < 0) ↔
        (0 < (centredZero q).im ∧ (centredZero q).im ≤ T) :=
      ⟨fun h => ⟨by linarith [h.2], by linarith [h.1]⟩,
        fun h => ⟨by linarith [h.2], by linarith [h.1]⟩⟩
    simp only [hiff]
  have htot_eq : (∑' q : onLineCopies, if |γ q| ≤ T then |γ q| * m q else 0) =
      (∑' q : onLineCopies, fpos q) + ∑' q : onLineCopies, fneg q := by
    rw [← Summable.tsum_add hs_pos hs_neg]
    congr 1; funext q
    dsimp only [fpos, fneg]
    rcases lt_trichotomy (γ q) 0 with hlt | heq | hgt
    · rw [abs_of_neg hlt]
      have h1 : ¬ (0 < γ q ∧ γ q ≤ T) := fun h => absurd hlt (not_lt.mpr h.1.le)
      rw [if_neg h1, zero_add]
      have hiff : (-γ q ≤ T) ↔ (-T ≤ γ q ∧ γ q < 0) :=
        ⟨fun h => ⟨by linarith, hlt⟩, fun h => by linarith [h.1]⟩
      simp only [hiff]
    · rw [heq, abs_zero, zero_mul, if_pos hT,
        if_neg (show ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) ≤ T) from fun h => lt_irrefl 0 h.1),
        if_neg (show ¬ (-T ≤ (0 : ℝ) ∧ (0 : ℝ) < 0) from fun h => lt_irrefl 0 h.2), add_zero]
    · rw [abs_of_pos hgt]
      have h1 : ¬ (-T ≤ γ q ∧ γ q < 0) := fun h => absurd hgt (not_lt.mpr h.2.le)
      rw [if_neg h1, add_zero]
      by_cases hle : γ q ≤ T
      · rw [if_pos hle, if_pos ⟨hgt, hle⟩]
      · rw [if_neg hle, if_neg fun h => hle h.2]
  rw [htot_eq, hneg_eq]
  ring

#print axioms tendsto_mul_log_dampedMass_of_terminal_sq
#print axioms halfLineEnergyMinimizer_tendsto_mul_log_dampedMass
#print axioms halfLineEnergyMinimizer_tendsto_mul_log_vertical_laplace_sq
#print axioms halfLineEnergyMinimizer_mean_square_wall_trace_zero
#print axioms criticalState_tendsto_mul_log_dampedMass
#print axioms criticalState_tendsto_mul_log_vertical_laplace_sq
#print axioms criticalState_boundary_fourier_tail_zero
#print axioms criticalState_boundary_fourier_firstMoment_sublogarithmic
#print axioms criticalState_criticalLine_tail_asymptotic
#print axioms criticalState_criticalLine_firstMoment_asymptotic

end GaloisForLFunctions.ExclusionOfTheCriticalState
