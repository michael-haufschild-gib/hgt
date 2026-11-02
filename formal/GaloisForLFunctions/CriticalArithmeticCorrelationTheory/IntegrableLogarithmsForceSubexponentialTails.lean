import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A logarithmic integral prevents exponentially small tails

An exponentially small positive-density tail forces an order-one contribution to the
quadratically weighted absolute logarithm on a moving interval. Integrability of that
logarithm excludes this contribution at every sufficiently large radius.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

private theorem quadratic_log_weight_le {s x y c u : ℝ}
    (hc : 1 ≤ c) (hu : u ∈ Ioc c (2 * c)) :
    (s * u - x) ^ 2 + y ^ 2 ≤ ((2 * |s| + |x|) ^ 2 + y ^ 2 + 1) * c ^ 2 := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hu0 : 0 ≤ u := hc0.le.trans hu.1.le
  have hsu : |s * u - x| ≤ (2 * |s| + |x|) * c := by
    calc
      _ ≤ |s * u| + |x| := abs_sub _ _
      _ = |s| * u + |x| := by rw [abs_mul, abs_of_nonneg hu0]
      _ ≤ |s| * (2 * c) + |x| * c := add_le_add
        (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg s))
        (le_mul_of_one_le_right (abs_nonneg x) hc)
      _ = _ := by ring
  have hsuSq := pow_le_pow_left₀ (abs_nonneg _) hsu 2
  rw [sq_abs] at hsuSq
  have hcSq : 1 ≤ c ^ 2 := one_le_pow₀ hc
  have hySq := mul_le_mul_of_nonneg_left hcSq (sq_nonneg y)
  nlinarith only [hsuSq, hySq, sq_nonneg c]

private theorem log_weight_pointwise_payment {H s x y c ε : ℝ}
    (hH : 0 < H) (hy : 0 < y) (hden : (s - x) ^ 2 + y ^ 2 ≤ c) :
    ε + 1 ≤ H / Real.exp (-ε) + c * |Real.log H / ((s - x) ^ 2 + y ^ 2)| := by
  have hw : 0 < (s - x) ^ 2 + y ^ 2 := by positivity
  have hη := Real.exp_pos (-ε)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hH hη)
  rw [Real.log_div hH.ne' hη.ne', Real.log_exp] at hlog
  have hpay : |Real.log H| ≤ c * |Real.log H / ((s - x) ^ 2 + y ^ 2)| := by
    have hh := mul_le_mul_of_nonneg_right hden
      (abs_nonneg (Real.log H / ((s - x) ^ 2 + y ^ 2)))
    have heq : ((s - x) ^ 2 + y ^ 2) *
        |Real.log H / ((s - x) ^ 2 + y ^ 2)| = |Real.log H| := by
      rw [abs_div, abs_of_pos hw]
      field_simp
    rwa [heq] at hh
  linarith only [hlog, neg_abs_le (Real.log H), hpay]

/-- An integrable quadratic logarithmic weight excludes exponentially small tails of a
positive density. Positivity almost everywhere is essential because the logarithm is zero
at zero in Lean's totalized convention. -/
theorem eventually_exp_le_tail_of_integrable_log_weight {H : ℝ → ℝ}
    (hH0 : ∀ u : ℝ, 0 ≤ H u) (hHpos : ∀ᵐ u : ℝ, 0 < H u)
    (hH : IntegrableOn H (Ioi 0)) {s x y : ℝ} (hy : 0 < y)
    (hlog : Integrable (fun u : ℝ => Real.log (H u) / ((s * u - x) ^ 2 + y ^ 2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c : ℝ in atTop, Real.exp (-ε * c) ≤ ∫ u in Ioi c, H u := by
  let g := fun u : ℝ => Real.log (H u) / ((s * u - x) ^ 2 + y ^ 2)
  let D := (2 * |s| + |x|) ^ 2 + y ^ 2 + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  have hg : Integrable g := hlog
  have htail : Tendsto (fun c : ℝ => ∫ u in Ioi c, |g u|) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  filter_upwards [htail.eventually (ge_mem_nhds
    (div_pos hε (mul_pos zero_lt_two hD))), eventually_ge_atTop 1] with c htailc hc1
  have hc : 0 < c := zero_lt_one.trans_le hc1
  by_contra hbad
  have hbad' : (∫ u in Ioi c, H u) < Real.exp (-ε * c) := lt_of_not_ge hbad
  let η := Real.exp (-ε * c)
  have hη : 0 < η := Real.exp_pos _
  have hsub0 : Ioc c (2 * c) ⊆ Ioi (0 : ℝ) := fun u hu => hc.trans hu.1
  have hsubc : Ioc c (2 * c) ⊆ Ioi c := fun _ hu => hu.1
  have hHc : IntegrableOn H (Ioi c) := hH.mono_set (Ioi_subset_Ioi hc.le)
  have hHI : IntegrableOn H (Ioc c (2 * c)) := hH.mono_set hsub0
  have hgI : IntegrableOn (fun u => |g u|) (Ioc c (2 * c)) := hg.abs.integrableOn
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioc c (2 * c)),
      ε * c + 1 ≤ H u / η + D * c ^ 2 * |g u| := by
    filter_upwards [ae_restrict_of_ae hHpos, ae_restrict_mem measurableSet_Ioc] with u hu huI
    have hden : (s * u - x) ^ 2 + y ^ 2 ≤ D * c ^ 2 :=
      quadratic_log_weight_le hc1 huI
    have hh := log_weight_pointwise_payment hu hy hden (ε := ε * c)
    simpa only [η, g, neg_mul] using hh
  have hconstInt : IntegrableOn (fun _u : ℝ => ε * c + 1) (Ioc c (2 * c)) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hrightInt : IntegrableOn
      (fun u => H u / η + D * c ^ 2 * |g u|) (Ioc c (2 * c)) :=
    (hHI.div_const η).add (hgI.const_mul (D * c ^ 2))
  have hint := integral_mono_ae hconstInt hrightInt hpoint
  have hconst : (∫ _u in Ioc c (2 * c), ε * c + 1) = c * (ε * c + 1) := by
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc,
      max_eq_left (by linarith : 0 ≤ 2 * c - c)]
    ring
  rw [hconst, integral_add (hHI.div_const η) (hgI.const_mul (D * c ^ 2)),
    integral_div, integral_const_mul] at hint
  have hHmono : (∫ u in Ioc c (2 * c), H u) ≤ ∫ u in Ioi c, H u :=
    setIntegral_mono_set hHc (ae_of_all _ hH0) (ae_of_all _ hsubc)
  have hgmono : (∫ u in Ioc c (2 * c), |g u|) ≤ ∫ u in Ioi c, |g u| :=
    setIntegral_mono_set hg.abs.integrableOn (ae_of_all _ fun u => abs_nonneg (g u))
      (ae_of_all _ hsubc)
  have hHcost : (∫ u in Ioc c (2 * c), H u) / η < 1 :=
    (div_lt_one hη).mpr (hHmono.trans_lt hbad')
  have hgcost : D * c ^ 2 * (∫ u in Ioc c (2 * c), |g u|) ≤ ε / 2 * c ^ 2 := by
    calc
      _ ≤ D * c ^ 2 * (ε / (2 * D)) :=
        mul_le_mul_of_nonneg_left (hgmono.trans htailc) (by positivity)
      _ = _ := by field_simp
  have hεc : 0 < ε * c ^ 2 := mul_pos hε (sq_pos_of_pos hc)
  nlinarith only [hint, hHcost, hgcost, hc1, hεc]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
