import GaloisForLFunctions.HTGeometry.BarnesShiftTaylorDescent
import GaloisForLFunctions.HTGeometry.BarnesDoubleGamma

/-!
# The shift equation of the continued Barnes double zeta

The kernel identity `F_2(x,t) = F_2(x+omega_1,t) + F_1(omega_2;x,t)` and its descent to the Taylor
data make the shift equation an identity between the individual ingredients of the deep split: the
three pole coefficients match, the subtracted head integrals match, and the tail integrals match.
Assembling them gives

```text
zeta_2(s, x) = zeta_2(s, x + omega_1) + zeta_1(omega_2; s, x)
```

for the continued functions on `Re s > -1`, with no appeal to analytic continuation.  Both tails are
absolutely convergent for every exponent, since exponential decay beats every power.
-/

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The cone tail converges for every exponent.**  Beyond `t = 1` the kernel decays
exponentially, which beats every power. -/
theorem integrableOn_cpow_mul_barnesConeKernel_Ioi_one_all {o1 o2 x : ℝ} (h1 : 0 < o1)
    (h2 : 0 < o2) (hx : 0 < x) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t) (Ioi 1) := by
  have hp1 : 0 < 1 - Real.exp (-o1) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos h1 one_pos
  have hp2 : 0 < 1 - Real.exp (-o2) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos h2 one_pos
  set c : ℝ := (1 - Real.exp (-o1)) * (1 - Real.exp (-o2)) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  set σ : ℝ := max (s.re - 1) 0 with hσ
  have hσ1 : (-1 : ℝ) < σ := by
    have : (0 : ℝ) ≤ σ := le_max_right _ _
    linarith
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hdom : IntegrableOn (fun t : ℝ => c⁻¹ * (t ^ σ * Real.exp (-(x * t)))) (Ioi 1) :=
    ((integrableOn_rpow_mul_exp_neg_mul_Ioi (σ := σ) (a := x) hσ1 hx).mono_set hsub).const_mul _
  refine Integrable.mono' hdom
    (aestronglyMeasurable_cpow_mul_of_continuousOn measurableSet_Ioi hsub
      ((continuousOn_barnesConeKernel h1 h2).mono hsub) s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hpow : t ^ (s.re - 1) ≤ t ^ σ :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left _ _)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  calc t ^ (s.re - 1) * ‖barnesConeKernel o1 o2 x t‖
      ≤ t ^ σ * (Real.exp (-x * t) / c) := by
        refine mul_le_mul hpow (norm_barnesConeKernel_le h1 h2 ht1) (norm_nonneg _)
          (Real.rpow_nonneg ht0.le _)
    _ = c⁻¹ * (t ^ σ * Real.exp (-(x * t))) := by
        rw [neg_mul, div_eq_mul_inv]
        ring

/-- **The ray tail converges for every exponent.** -/
theorem integrableOn_cpow_mul_barnesRayKernel_Ioi_one_all {o x : ℝ} (ho : 0 < o) (hx : 0 < x)
    (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * barnesRayKernel o x t) (Ioi 1) := by
  have hp : 0 < 1 - Real.exp (-o) := by
    simpa using one_sub_exp_neg_mul_ofReal_pos ho one_pos
  set σ : ℝ := max (s.re - 1) 0 with hσ
  have hσ1 : (-1 : ℝ) < σ := by
    have : (0 : ℝ) ≤ σ := le_max_right _ _
    linarith
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hdom : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-o))⁻¹ * (t ^ σ * Real.exp (-(x * t)))) (Ioi 1) :=
    ((integrableOn_rpow_mul_exp_neg_mul_Ioi (σ := σ) (a := x) hσ1 hx).mono_set hsub).const_mul _
  refine Integrable.mono' hdom
    (aestronglyMeasurable_cpow_mul_of_continuousOn measurableSet_Ioi hsub
      ((continuousOn_barnesRayKernel ho).mono hsub) s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hpow : t ^ (s.re - 1) ≤ t ^ σ :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left _ _)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  calc t ^ (s.re - 1) * ‖barnesRayKernel o x t‖
      ≤ t ^ σ * (Real.exp (-x * t) / (1 - Real.exp (-o))) := by
        refine mul_le_mul hpow (norm_barnesRayKernel_le ho ht1) (norm_nonneg _)
          (Real.rpow_nonneg ht0.le _)
    _ = (1 - Real.exp (-o))⁻¹ * (t ^ σ * Real.exp (-(x * t))) := by
        rw [neg_mul, div_eq_mul_inv]
        ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The analytic part of the deep split for the ray. -/
def barnesRayDeepPart (o x : ℝ) (s : ℂ) : ℂ :=
  (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) * barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ))
    + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesRayKernel o x t

/-- The continued one-dimensional Barnes zeta, before dividing by `Gamma`. -/
def barnesSingleZetaBracket (o x : ℝ) (s : ℂ) : ℂ :=
  (o : ℂ)⁻¹ / (s - 1) + barnesRayLinearCoeff (o : ℂ) (x : ℂ) / s + barnesRayDeepPart o x s

/-- The continued Barnes double zeta, before dividing by `Gamma`. -/
def barnesDoubleZetaBracket (o1 o2 x : ℝ) (s : ℂ) : ℂ :=
  ((o1 : ℂ)⁻¹ * (o2 : ℂ)⁻¹) / (s - 2)
    + barnesConeLinearCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / (s - 1)
    + barnesConeQuadCoeff (o1 : ℂ) (o2 : ℂ) (x : ℂ) / s
    + barnesConeDeepPart o1 o2 x s

set_option maxHeartbeats 800000 in
/-- **The shift equation of the continued Barnes double zeta.**  Shifting the argument by a period
peels off the one-dimensional zeta of the other period.  Every ingredient of the split -- the three
pole coefficients, the subtracted head and the tail -- satisfies the identity separately, so no
analytic continuation argument is involved. -/
theorem barnesDoubleZetaBracket_shift {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (hx : 0 < x)
    {s : ℂ} (hs : -1 < s.re) :
    barnesDoubleZetaBracket o1 o2 x s
      = barnesDoubleZetaBracket o1 o2 (x + o1) s + barnesSingleZetaBracket o2 x s := by
  have hx1 : 0 < x + o1 := by linarith
  have hcast : ((x + o1 : ℝ) : ℂ) = (x : ℂ) + (o1 : ℂ) := by push_cast; ring
  have ho1 : (o1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h1)
  have ho2 : (o2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h2)
  have hlin := barnesConeLinearCoeff_shift ho1 ho2 (x : ℂ)
  have hquad := barnesConeQuadCoeff_shift ho1 ho2 (x : ℂ)
  rw [← hcast] at hlin hquad
  have hhead : (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
        barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ))
      = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
          barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) ((x + o1 : ℝ) : ℂ) (t : ℂ))
        + ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
            barnesRayRemainder (o2 : ℂ) (x : ℂ) (t : ℂ) := by
    have hcongr : ∀ t ∈ Ioc (0 : ℝ) 1,
        (t : ℂ) ^ (s + 1 - 1) * barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)
          = (t : ℂ) ^ (s + 1 - 1) *
              barnesConeCubicRemainder (o1 : ℂ) (o2 : ℂ) ((x + o1 : ℝ) : ℂ) (t : ℂ)
            + (t : ℂ) ^ (s + 1 - 1) * barnesRayRemainder (o2 : ℂ) (x : ℂ) (t : ℂ) := by
      intro t ht
      rw [barnesConeCubicRemainder_shift h1 h2 x ht.1]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr]
    exact integral_add (integrableOn_cpow_mul_barnesConeCubicRemainder_Ioc (x := x + o1) h1 h2 hs)
      (integrableOn_cpow_mul_barnesRayRemainder_Ioc (x := x) h2 hs)
  have htail : (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t)
      = (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 (x + o1) t)
        + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesRayKernel o2 x t := by
    have hcongr : ∀ t ∈ Ioi (1 : ℝ),
        (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 x t
          = (t : ℂ) ^ (s - 1) * barnesConeKernel o1 o2 (x + o1) t
            + (t : ℂ) ^ (s - 1) * barnesRayKernel o2 x t := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
      rw [barnesConeKernel_shift h1 h2 x ht0]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    exact integral_add (integrableOn_cpow_mul_barnesConeKernel_Ioi_one_all h1 h2 hx1 s)
      (integrableOn_cpow_mul_barnesRayKernel_Ioi_one_all h2 hx s)
  rw [barnesDoubleZetaBracket, barnesDoubleZetaBracket, barnesSingleZetaBracket,
    barnesConeDeepPart, barnesConeDeepPart, barnesRayDeepPart, hlin, hquad, hhead, htail]
  ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem barnesDoubleZetaDeep_eq_bracket (o1 o2 x : ℝ) (s : ℂ) :
    barnesDoubleZetaDeep o1 o2 x s = barnesDoubleZetaBracket o1 o2 x s * (Complex.Gamma s)⁻¹ :=
  rfl

theorem barnesDoubleZetaBracket_eq_Gamma_mul {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (hx : 0 < x) {s : ℂ} (hs : 2 < s.re) :
    barnesDoubleZetaBracket o1 o2 x s = Complex.Gamma s * barnesDoubleZeta o1 o2 s (x : ℂ) := by
  rw [barnesDoubleZetaBracket, barnesConeDeepPart,
    Gamma_mul_barnesDoubleZeta_eq_continuation_three h1 h2 hx hs]
  ring

theorem barnesSingleZetaBracket_eq_Gamma_mul {o x : ℝ} (ho : 0 < o) (hx : 0 < x)
    {s : ℂ} (hs : 1 < s.re) :
    barnesSingleZetaBracket o x s = Complex.Gamma s * barnesSingleZeta o s (x : ℂ) := by
  rw [barnesSingleZetaBracket, barnesRayDeepPart,
    Gamma_mul_barnesSingleZeta_eq_continuation ho hx hs]
  ring

/-- The continued one-dimensional Barnes zeta. -/
def barnesSingleZetaDeep (o x : ℝ) (s : ℂ) : ℂ :=
  barnesSingleZetaBracket o x s * (Complex.Gamma s)⁻¹

/-- **The shift equation of the continued Barnes double zeta.** -/
theorem barnesDoubleZetaDeep_shift {o1 o2 x : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (hx : 0 < x)
    {s : ℂ} (hs : -1 < s.re) :
    barnesDoubleZetaDeep o1 o2 x s
      = barnesDoubleZetaDeep o1 o2 (x + o1) s + barnesSingleZetaDeep o2 x s := by
  rw [barnesDoubleZetaDeep_eq_bracket, barnesDoubleZetaDeep_eq_bracket, barnesSingleZetaDeep,
    barnesDoubleZetaBracket_shift h1 h2 hx hs]
  ring

end

end GaloisForLFunctions.HTGeometry
