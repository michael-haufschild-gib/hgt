import GaloisForLFunctions.HTGeometry.BarnesRayKernelShift

/-!
# The shift equation of the one-dimensional Barnes zeta

Peeling a period off the ray kernel leaves a bare exponential, so the shift equation of the
continued one-dimensional zeta reads

```text
zeta_1(omega; s, x) = zeta_1(omega; s, x + omega) + [Euler bracket],
```

where the Euler bracket is the split form of `Gamma(s) x^(-s)`: the pole `1/s`, a head integral of
`t^(s-1)(e^(-xt) - 1)` convergent for `Re s > -1` because `1 - e^(-xt) <= xt`, and an entire tail.
Where the Mellin integral converges the bracket is exactly `Gamma(s) x^(-s)`.
-/

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_exp_neg_sub_one_le {x t : ℝ} (hx : 0 < x) (ht : 0 < t) :
    ‖Complex.exp (-((x : ℂ) * (t : ℂ))) - 1‖ ≤ x * t := by
  have hcast : Complex.exp (-((x : ℂ) * (t : ℂ))) = ((Real.exp (-x * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hle : 1 - Real.exp (-x * t) ≤ x * t := by
    have h := Real.add_one_le_exp (-x * t)
    linarith
  have hpos : Real.exp (-x * t) < 1 := exp_neg_mul_lt_one hx ht
  rw [hcast, show ((Real.exp (-x * t) : ℝ) : ℂ) - 1 = (((Real.exp (-x * t) - 1 : ℝ)) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith

theorem integrableOn_cpow_mul_expSub_Ioc {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : -1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1)) (Ioc 0 1) := by
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun t ht => ht.1
  have hrpow : IntegrableOn (fun t : ℝ => t ^ s.re) (Ioc 0 1) := by
    have : IntervalIntegrable (fun t : ℝ => t ^ s.re) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' hs
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at this
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1)) (volume.restrict (Ioc (0:ℝ) 1)) := by
    refine aestronglyMeasurable_cpow_mul_of_continuousOn measurableSet_Ioc hsub ?_ s
    exact ((Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).neg)).sub continuous_const).continuousOn
  refine Integrable.mono' (hrpow.const_mul x) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re]
  have hpow : t ^ (s.re - 1) * (x * t) = x * t ^ s.re := by
    have hone : t ^ (s.re - 1) * t ^ (1 : ℝ) = t ^ (s.re - 1 + 1) := (Real.rpow_add ht0 _ _).symm
    rw [Real.rpow_one] at hone
    calc t ^ (s.re - 1) * (x * t) = (t ^ (s.re - 1) * t) * x := by ring
      _ = t ^ (s.re - 1 + 1) * x := by rw [hone]
      _ = x * t ^ s.re := by rw [show s.re - 1 + 1 = s.re by ring]; ring
  calc t ^ (s.re - 1) * ‖Complex.exp (-((x : ℂ) * (t : ℂ))) - 1‖
      ≤ t ^ (s.re - 1) * (x * t) :=
        mul_le_mul_of_nonneg_left (norm_exp_neg_sub_one_le hx ht0) (Real.rpow_nonneg ht0.le _)
    _ = x * t ^ s.re := hpow

/-- The split form of `Gamma(s) x^(-s)`: the pole at `s = 0`, a head convergent for `Re s > -1`,
and an entire tail. -/
def expShiftBracket (x : ℝ) (s : ℂ) : ℂ :=
  1 / s + (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) *
      (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1))
    + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-((x : ℂ) * (t : ℂ)))

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem integrableOn_cpow_mul_exp_Ioi_one {x : ℝ} (hx : 0 < x) (s : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      Complex.exp (-((x : ℂ) * (t : ℂ)))) (Ioi 1) := by
  set σ : ℝ := max (s.re - 1) 0 with hσ
  have hσ1 : (-1 : ℝ) < σ := by
    have : (0 : ℝ) ≤ σ := le_max_right _ _
    linarith
  have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (by norm_num)
  have hdom : IntegrableOn (fun t : ℝ => t ^ σ * Real.exp (-(x * t))) (Ioi 1) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi (σ := σ) (a := x) hσ1 hx).mono_set hsub
  refine Integrable.mono' hdom
    (aestronglyMeasurable_cpow_mul_of_continuousOn measurableSet_Ioi hsub
      ((Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).neg)).continuousOn) s) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
  have hpow : t ^ (s.re - 1) ≤ t ^ σ :=
    Real.rpow_le_rpow_of_exponent_le ht1 (le_max_left _ _)
  have hnorm : ‖Complex.exp (-((x : ℂ) * (t : ℂ)))‖ = Real.exp (-(x * t)) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re, hnorm]
  exact mul_le_mul hpow le_rfl (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _)

set_option maxHeartbeats 800000 in
/-- **The shift equation of the continued one-dimensional Barnes zeta.** -/
theorem barnesSingleZetaBracket_shift {o x : ℝ} (ho : 0 < o) (hx : 0 < x) {s : ℂ}
    (hs : -1 < s.re) :
    barnesSingleZetaBracket o x s
      = barnesSingleZetaBracket o (x + o) s + expShiftBracket x s := by
  have hx1 : 0 < x + o := by linarith
  have hcast : ((x + o : ℝ) : ℂ) = (x : ℂ) + (o : ℂ) := by push_cast; ring
  have hoC : (o : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ho)
  have hlin := barnesRayLinearCoeff_shift hoC (x : ℂ)
  rw [← hcast] at hlin
  have hexpcast : ∀ t : ℝ, Complex.exp (-((x : ℂ) * (t : ℂ)))
      = ((Real.exp (-x * t) : ℝ) : ℂ) := by
    intro t
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hhead : (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
        barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ))
      = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s + 1 - 1) *
          barnesRayRemainder (o : ℂ) ((x + o : ℝ) : ℂ) (t : ℂ))
        + ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) *
            (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1) := by
    have hcongr : ∀ t ∈ Ioc (0 : ℝ) 1,
        (t : ℂ) ^ (s + 1 - 1) * barnesRayRemainder (o : ℂ) (x : ℂ) (t : ℂ)
          = (t : ℂ) ^ (s + 1 - 1) * barnesRayRemainder (o : ℂ) ((x + o : ℝ) : ℂ) (t : ℂ)
            + (t : ℂ) ^ (s - 1) * (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1) := by
      intro t ht
      have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht.1)
      have hpow : (t : ℂ) ^ (s - 1) * (t : ℂ) = (t : ℂ) ^ (s + 1 - 1) := by
        rw [show s + 1 - 1 = (s - 1) + 1 by ring, Complex.cpow_add _ _ htC, Complex.cpow_one]
      rw [barnesRayRemainder_shift ho x ht.1, ← hpow]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr]
    exact integral_add (integrableOn_cpow_mul_barnesRayRemainder_Ioc (x := x + o) ho hs)
      (integrableOn_cpow_mul_expSub_Ioc hx hs)
  have htail : (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesRayKernel o x t)
      = (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * barnesRayKernel o (x + o) t)
        + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-((x : ℂ) * (t : ℂ))) := by
    have hcongr : ∀ t ∈ Ioi (1 : ℝ),
        (t : ℂ) ^ (s - 1) * barnesRayKernel o x t
          = (t : ℂ) ^ (s - 1) * barnesRayKernel o (x + o) t
            + (t : ℂ) ^ (s - 1) * Complex.exp (-((x : ℂ) * (t : ℂ))) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
      rw [barnesRayKernel_shift ho x ht0, hexpcast t]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    exact integral_add (integrableOn_cpow_mul_barnesRayKernel_Ioi_one_all ho hx1 s)
      (integrableOn_cpow_mul_exp_Ioi_one hx s)
  rw [barnesSingleZetaBracket, barnesSingleZetaBracket, expShiftBracket,
    barnesRayDeepPart, barnesRayDeepPart, hlin, hhead, htail]
  ring

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem integrableOn_cpow_Ioc {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioc 0 1) := by
  refine MeasureTheory.IntegrableOn.congr_fun
    (integrableOn_cpow_mul_cpow_Ioc (0 : ℂ) (by simpa using hs)) (fun t ht => ?_)
    measurableSet_Ioc
  rw [Complex.cpow_zero, mul_one]

theorem integral_cpow_Ioc {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1)) = 1 / s := by
  have h0 := integral_cpow_mul_cpow_Ioc (0 : ℂ) (by simpa using hs)
  rw [show s + (0 : ℂ) = s by ring] at h0
  rw [← h0]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  rw [Complex.cpow_zero, mul_one]

/-- **The exponential bracket is the Euler integral.**  Where the Mellin integral converges, the
split form is `Gamma(s) x^(-s)`. -/
theorem expShiftBracket_eq_Gamma_mul {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    expShiftBracket x s = Complex.Gamma s * (x : ℂ) ^ (-s) := by
  have hw : (0 : ℝ) < ((x : ℂ)).re := by simpa using hx
  have hfull := integral_cpow_mul_exp_neg_mul_Ioi hs hw
  have hsub : Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun t ht => ht.1
  have hIocE : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      Complex.exp (-((x : ℂ) * (t : ℂ)))) (Ioc 0 1) :=
    (integrableOn_cpow_mul_exp_neg_mul_Ioi hs hw).mono_set hsub
  have hIoiE := integrableOn_cpow_mul_exp_Ioi_one hx s
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr fun t ht ht' => absurd ht.2 (not_le.mpr ht')
  have hsplit : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) *
        Complex.exp (-((x : ℂ) * (t : ℂ))))
      = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) * Complex.exp (-((x : ℂ) * (t : ℂ))))
        + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * Complex.exp (-((x : ℂ) * (t : ℂ))) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1),
      setIntegral_union hdisj measurableSet_Ioi hIocE hIoiE]
  have hhead : (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) *
        Complex.exp (-((x : ℂ) * (t : ℂ))))
      = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) *
          (Complex.exp (-((x : ℂ) * (t : ℂ))) - 1))
        + ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) := by
    rw [← integral_add (integrableOn_cpow_mul_expSub_Ioc hx (by linarith))
      (integrableOn_cpow_Ioc hs)]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    ring
  rw [expShiftBracket, ← hfull, hsplit, hhead, integral_cpow_Ioc hs]
  ring

end

end GaloisForLFunctions.HTGeometry
