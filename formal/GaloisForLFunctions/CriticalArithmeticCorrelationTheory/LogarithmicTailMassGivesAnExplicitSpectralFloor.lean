import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.IntegrableLogarithmsForceSubexponentialTails

/-!
# A quantitative spectral floor from logarithmic tail mass

The absolute logarithmic mass beyond a radius controls the logarithm of the ordinary
mass beyond that radius. Integrating on a doubled interval gives the explicit constant
five for the weight `1/(1 + u²)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- The remaining weighted logarithmic mass is an explicit subexponential decay rate.
Positivity almost everywhere excludes the totalized-logarithm value at zero. -/
theorem exp_logarithmic_tail_le_tail {H : ℝ → ℝ}
    (hH0 : ∀ u : ℝ, 0 ≤ H u) (hHpos : ∀ᵐ u : ℝ, 0 < H u)
    (hH : IntegrableOn H (Ioi 0))
    (hlog : Integrable (fun u : ℝ => Real.log (H u) / (1 + u ^ 2)))
    {c : ℝ} (hc1 : 1 ≤ c) :
    Real.exp (-5 * c * (∫ u in Ioi c, |Real.log (H u) / (1 + u ^ 2)|)) ≤
      ∫ u in Ioi c, H u := by
  let g := fun u : ℝ => Real.log (H u) / (1 + u ^ 2)
  let η := ∫ u in Ioi c, H u
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hHc : IntegrableOn H (Ioi c) := hH.mono_set (Ioi_subset_Ioi hc.le)
  have hlog' : Integrable (fun u : ℝ =>
      Real.log (H u) / (((1 : ℝ) * u - 0) ^ 2 + (1 : ℝ) ^ 2)) := by
    simpa only [one_mul, sub_zero, one_pow, add_comm] using hlog
  have hη : 0 < η := by
    obtain ⟨C, hC⟩ := eventually_atTop.mp
      (eventually_exp_le_tail_of_integrable_log_weight hH0 hHpos hH zero_lt_one hlog' zero_lt_one)
    have hmono : (∫ u in Ioi (max C c), H u) ≤ ∫ u in Ioi c, H u :=
      setIntegral_mono_set hHc (ae_of_all _ hH0)
        (ae_of_all _ (Ioi_subset_Ioi (le_max_right C c)))
    exact (Real.exp_pos _).trans_le ((hC _ (le_max_left C c)).trans hmono)
  have hHI : IntegrableOn H (Ioc c (2 * c)) :=
    hHc.mono_set (fun _ hu => hu.1)
  have hg : Integrable g := hlog
  have hgI : IntegrableOn (fun u => |g u|) (Ioc c (2 * c)) := hg.abs.integrableOn
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioc c (2 * c)),
      -Real.log η + 1 ≤ H u / η + 5 * c ^ 2 * |g u| := by
    filter_upwards [ae_restrict_of_ae hHpos, ae_restrict_mem measurableSet_Ioc] with u hu huI
    have hu0 : 0 ≤ u := hc.le.trans huI.1.le
    have hsq := pow_le_pow_left₀ hu0 huI.2 2
    have hcSq : 1 ≤ c ^ 2 := one_le_pow₀ hc1
    have hden : 1 + u ^ 2 ≤ 5 * c ^ 2 := by nlinarith only [hsq, hcSq]
    have hw : 0 < 1 + u ^ 2 := by positivity
    have hlogRatio := Real.log_le_sub_one_of_pos (div_pos hu hη)
    rw [Real.log_div hu.ne' hη.ne'] at hlogRatio
    have hpay : |Real.log (H u)| ≤ 5 * c ^ 2 * |g u| := by
      have hh := mul_le_mul_of_nonneg_right hden (abs_nonneg (g u))
      have heq : (1 + u ^ 2) * |g u| = |Real.log (H u)| := by
        dsimp only [g]
        rw [abs_div, abs_of_pos hw]
        field_simp
      rwa [heq] at hh
    linarith only [hlogRatio, neg_abs_le (Real.log (H u)), hpay]
  have hconstInt : IntegrableOn (fun _u : ℝ => -Real.log η + 1) (Ioc c (2 * c)) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hrightInt : IntegrableOn
      (fun u => H u / η + 5 * c ^ 2 * |g u|) (Ioc c (2 * c)) :=
    (hHI.div_const η).add (hgI.const_mul (5 * c ^ 2))
  have hint := integral_mono_ae hconstInt hrightInt hpoint
  have hconst : (∫ _u in Ioc c (2 * c), -Real.log η + 1) =
      c * (-Real.log η + 1) := by
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc,
      max_eq_left (by linarith only [hc] : 0 ≤ 2 * c - c)]
    ring
  rw [hconst, integral_add (hHI.div_const η) (hgI.const_mul (5 * c ^ 2)),
    integral_div, integral_const_mul] at hint
  have hHmono : (∫ u in Ioc c (2 * c), H u) ≤ η :=
    setIntegral_mono_set hHc (ae_of_all _ hH0) (ae_of_all _ fun _ hu => hu.1)
  have hHcost : (∫ u in Ioc c (2 * c), H u) / η ≤ 1 := (div_le_one hη).mpr hHmono
  have hgmono : (∫ u in Ioc c (2 * c), |g u|) ≤ ∫ u in Ioi c, |g u| :=
    setIntegral_mono_set hg.abs.integrableOn (ae_of_all _ fun u => abs_nonneg (g u))
      (ae_of_all _ fun _ hu => hu.1)
  have hgcost := mul_le_mul_of_nonneg_left hgmono (by positivity : 0 ≤ 5 * c ^ 2)
  have hlogMass : c * (-Real.log η) ≤ c * (5 * c * ∫ u in Ioi c, |g u|) := by
    nlinarith only [hint, hHcost, hgcost, hc1]
  have hlogBound : -5 * c * (∫ u in Ioi c, |g u|) ≤ Real.log η := by
    have hh := (mul_le_mul_iff_right₀ hc).mp hlogMass
    linarith only [hh]
  exact (Real.exp_le_exp.mpr hlogBound).trans_eq (Real.exp_log hη)

/-- Absolute weighted logarithmic mass remaining beyond a radius. -/
def logarithmicTailMass (H : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in Ioi t, |Real.log (H u) / (1 + u ^ 2)|

/-- A tail-adapted radius, capped quadratically to retain geometric error bounds. -/
def logarithmicTailClock (H : ℝ → ℝ) (t : ℝ) : ℝ :=
  min (t ^ 2) (t / Real.sqrt (logarithmicTailMass H t + 1 / t))

theorem logarithmicTailMass_nonneg (H : ℝ → ℝ) (t : ℝ) :
    0 ≤ logarithmicTailMass H t :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => abs_nonneg _

theorem logarithmicTailMass_antitone {H : ℝ → ℝ}
    (hlog : Integrable (fun u : ℝ => Real.log (H u) / (1 + u ^ 2))) :
    Antitone (logarithmicTailMass H) := by
  intro s t hst
  exact setIntegral_mono_set hlog.abs.integrableOn (ae_of_all _ fun _ => abs_nonneg _)
    (ae_of_all _ (Ioi_subset_Ioi hst))

theorem tendsto_logarithmicTailMass_zero (H : ℝ → ℝ) :
    Tendsto (logarithmicTailMass H) atTop (𝓝 0) :=
  tendsto_integral_Ioi_zero tendsto_id

private theorem tendsto_sqrt_logarithmicTailMass (H : ℝ → ℝ) :
    Tendsto (fun t : ℝ => Real.sqrt (logarithmicTailMass H t + 1 / t))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun t : ℝ => logarithmicTailMass H t + 1 / t) atTop (𝓝 0) := by
    simpa only [one_div, add_zero] using
      (tendsto_logarithmicTailMass_zero H).add tendsto_inv_atTop_zero
  simpa only [Real.sqrt_zero] using hg.sqrt

/-- The explicit radius eventually exceeds every fixed multiple of its input scale. -/
theorem eventually_mul_le_logarithmicTailClock (H : ℝ → ℝ) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ t : ℝ in atTop, K * t ≤ logarithmicTailClock H t := by
  have hs := (tendsto_sqrt_logarithmicTailMass H).eventually
    (ge_mem_nhds (one_div_pos.mpr hK))
  filter_upwards [hs, eventually_ge_atTop K, eventually_gt_atTop (0 : ℝ)]
    with t hsmall hKt ht
  have hg : 0 < logarithmicTailMass H t + 1 / t :=
    add_pos_of_nonneg_of_pos (logarithmicTailMass_nonneg H t) (one_div_pos.mpr ht)
  have hsqrt := Real.sqrt_pos.mpr hg
  refine le_min ?_ ?_
  · nlinarith only [mul_le_mul_of_nonneg_right hKt ht.le]
  · apply (le_div_iff₀ hsqrt).mpr
    have hKs : K * Real.sqrt (logarithmicTailMass H t + 1 / t) ≤ 1 := by
      simpa only [mul_comm] using (le_div_iff₀ hK).mp hsmall
    nlinarith only [mul_le_mul_of_nonneg_right hKs ht.le]

/-- The tail-adapted radius grows faster than the input scale. -/
theorem tendsto_logarithmicTailClock_div_atTop (H : ℝ → ℝ) :
    Tendsto (fun t : ℝ => logarithmicTailClock H t / t) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_mul_le_logarithmicTailClock H
    (show 0 < max K 1 from zero_lt_one.trans_le (le_max_right _ _)),
    eventually_gt_atTop (0 : ℝ)] with t hclock ht
  exact (le_div_iff₀ ht).mpr
    ((mul_le_mul_of_nonneg_right (le_max_left K 1) ht.le).trans hclock)

/-- The clock makes logarithmic tail loss negligible compared with its input scale. -/
theorem eventually_logarithmicTailClock_cost_le {H : ℝ → ℝ}
    (hlog : Integrable (fun u : ℝ => Real.log (H u) / (1 + u ^ 2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop,
      5 * logarithmicTailClock H t * logarithmicTailMass H (logarithmicTailClock H t) ≤
        ε * t := by
  have hs := (tendsto_sqrt_logarithmicTailMass H).eventually
    (ge_mem_nhds (div_pos hε (by norm_num : (0 : ℝ) < 5)))
  filter_upwards [hs, eventually_mul_le_logarithmicTailClock H zero_lt_one,
    eventually_gt_atTop (0 : ℝ)] with t hsmall hclock ht
  rw [one_mul] at hclock
  let g := logarithmicTailMass H t + 1 / t
  have hg : 0 < g := add_pos_of_nonneg_of_pos
    (logarithmicTailMass_nonneg H t) (one_div_pos.mpr ht)
  have hmass : logarithmicTailMass H (logarithmicTailClock H t) ≤ g :=
    (logarithmicTailMass_antitone hlog hclock).trans
      (le_add_of_nonneg_right (one_div_pos.mpr ht).le)
  have hcost : logarithmicTailClock H t *
      logarithmicTailMass H (logarithmicTailClock H t) ≤ t * Real.sqrt g := by
    calc
      _ ≤ (t / Real.sqrt g) * g := mul_le_mul
        (min_le_right _ _) hmass (logarithmicTailMass_nonneg H _) (by positivity)
      _ = t * Real.sqrt g := by
        calc
          _ = t * (g / Real.sqrt g) := by ring
          _ = _ := by rw [Real.div_sqrt]
  have hh := mul_le_mul_of_nonneg_left hsmall ht.le
  change t * Real.sqrt g ≤ t * (ε / 5) at hh
  nlinarith only [hcost, hh]

/-- Every exponential in the input scale bounds the tail throughout the explicit
clock range. No rate of decay of the weighted logarithm is assumed. -/
theorem eventually_exp_le_tail_up_to_logarithmicTailClock {H : ℝ → ℝ}
    (hH0 : ∀ u : ℝ, 0 ≤ H u) (hHpos : ∀ᵐ u : ℝ, 0 < H u)
    (hH : IntegrableOn H (Ioi 0))
    (hlog : Integrable (fun u : ℝ => Real.log (H u) / (1 + u ^ 2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ c : ℝ, 0 ≤ c → c ≤ logarithmicTailClock H t →
      Real.exp (-ε * t) ≤ ∫ u in Ioi c, H u := by
  filter_upwards [eventually_logarithmicTailClock_cost_le hlog hε,
    eventually_mul_le_logarithmicTailClock H zero_lt_one, eventually_ge_atTop (1 : ℝ)]
    with t hcost hclock ht
  rw [one_mul] at hclock
  intro c hc hct
  have hfloor := exp_logarithmic_tail_le_tail hH0 hHpos hH hlog (ht.trans hclock)
  have hmono : (∫ u in Ioi (logarithmicTailClock H t), H u) ≤ ∫ u in Ioi c, H u :=
    setIntegral_mono_set (hH.mono_set (Ioi_subset_Ioi hc)) (ae_of_all _ hH0)
      (ae_of_all _ (Ioi_subset_Ioi hct))
  refine (Real.exp_le_exp.mpr ?_).trans (hfloor.trans hmono)
  change -ε * t ≤ -5 * logarithmicTailClock H t *
    logarithmicTailMass H (logarithmicTailClock H t)
  linarith only [hcost]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
