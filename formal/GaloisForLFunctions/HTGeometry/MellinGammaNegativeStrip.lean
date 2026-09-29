import Mathlib

/-!
# The Mellin transform of `e^{-x} - 1` on the strip `-1 < Re w < 0`

For `-1 < Re w < 0` the function `e^{-x} - 1` has Mellin transform `Γ(w)`
(`mellin_exp_neg_sub_one`).  This is the continuation of Euler's integral one strip to the left of
its half-plane of convergence.  Near `0` the subtracted constant makes the integrand `O(x^{Re w})`,
and near `∞` the constant is what is left, which is `O(x^{Re w - 1})`.

The proof integrates the derivative of `x^w (e^{-x} - 1)` over `(0, ∞)`.  Both boundary values
vanish, so `w · M(w) = Γ(w + 1)`.

After rescaling, `e^{-πx} - 1` has Mellin transform `Γ_ℝ(s)` at `s/2` for `-2 < Re s < 0`
(`mellin_exp_neg_pi_sub_one_half`).  This is the form used to invert completed Dirichlet series to
the left of their poles.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `e^{-x} - 1`, as a complex-valued function of a real variable. -/
def expNegSubOne (x : ℝ) : ℂ := ((Real.exp (-x) - 1 : ℝ) : ℂ)

theorem abs_exp_neg_sub_one_le_self {x : ℝ} (hx : 0 ≤ x) : |Real.exp (-x) - 1| ≤ x := by
  have h1 := Real.add_one_le_exp (-x)
  have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem abs_exp_neg_sub_one_le_one {x : ℝ} (hx : 0 ≤ x) : |Real.exp (-x) - 1| ≤ 1 := by
  have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 := Real.exp_pos (-x)
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem norm_expNegSubOne_le_self {x : ℝ} (hx : 0 ≤ x) : ‖expNegSubOne x‖ ≤ x := by
  rw [expNegSubOne, Complex.norm_real, Real.norm_eq_abs]
  exact abs_exp_neg_sub_one_le_self hx

theorem norm_expNegSubOne_le_one {x : ℝ} (hx : 0 ≤ x) : ‖expNegSubOne x‖ ≤ 1 := by
  rw [expNegSubOne, Complex.norm_real, Real.norm_eq_abs]
  exact abs_exp_neg_sub_one_le_one hx

theorem continuous_expNegSubOne : Continuous expNegSubOne := by
  unfold expNegSubOne
  fun_prop

/-- `e^{-x} - 1` is Mellin-convergent on the strip `-1 < Re w < 0`. -/
theorem mellinConvergent_expNegSubOne {w : ℂ} (h1 : -1 < w.re) (h2 : w.re < 0) :
    MellinConvergent expNegSubOne w := by
  unfold MellinConvergent
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hmeas : ∀ s : Set ℝ, MeasurableSet s → s ⊆ Ioi 0 →
      AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (w - 1) • expNegSubOne t)
        (volume.restrict s) := by
    intro s hs hsub
    refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) hs
    have htpos : 0 < t := hsub ht
    refine ContinuousAt.continuousWithinAt ?_
    show ContinuousAt (fun t : ℝ => (t : ℂ) ^ (w - 1) * expNegSubOne t) t
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr htpos.ne')).mul
      continuous_expNegSubOne.continuousAt
  refine IntegrableOn.union ?_ ?_
  · have hint : IntegrableOn (fun t : ℝ => t ^ w.re) (Ioc 0 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_rpow' h1
    refine hint.mono' (hmeas _ measurableSet_Ioc Ioc_subset_Ioi_self) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have htpos : 0 < t := ht.1
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, sub_re, one_re]
    calc t ^ (w.re - 1) * ‖expNegSubOne t‖ ≤ t ^ (w.re - 1) * t :=
          mul_le_mul_of_nonneg_left (norm_expNegSubOne_le_self htpos.le) (by positivity)
      _ = t ^ w.re := by
          rw [← Real.rpow_add_one htpos.ne']
          ring_nf
  · have hint : IntegrableOn (fun t : ℝ => t ^ (w.re - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hint.mono' (hmeas _ measurableSet_Ioi (Ioi_subset_Ioi zero_le_one)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have htpos : 0 < t := zero_lt_one.trans ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, sub_re, one_re]
    calc t ^ (w.re - 1) * ‖expNegSubOne t‖ ≤ t ^ (w.re - 1) * 1 :=
          mul_le_mul_of_nonneg_left (norm_expNegSubOne_le_one htpos.le) (by positivity)
      _ = t ^ (w.re - 1) := mul_one _

/-- **Euler's integral one strip to the left.**  For `-1 < Re w < 0`,
`∫₀^∞ x^{w-1} (e^{-x} - 1) dx = Γ(w)`. -/
theorem mellin_expNegSubOne {w : ℂ} (h1 : -1 < w.re) (h2 : w.re < 0) :
    mellin expNegSubOne w = Complex.Gamma w := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, zero_re] at h2
    exact lt_irrefl _ h2
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ w * expNegSubOne x with hg
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt g (w * ((x : ℂ) ^ (w - 1) * expNegSubOne x) -
      ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (w + 1 - 1)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ w) (w * (x : ℂ) ^ (w - 1)) x :=
      (hasStrictDerivAt_cpow_const (by simp [hx0])).hasDerivAt.comp_ofReal
    have h2 : HasDerivAt expNegSubOne (((Real.exp (-x) * (-1) : ℝ)) : ℂ) x :=
      (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).sub_const 1).ofReal_comp
    refine (h1.mul h2).congr_deriv ?_
    rw [add_sub_cancel_right]
    push_cast
    ring
  have hcont : ContinuousWithinAt g (Ici 0) 0 := by
    have hg0 : g 0 = 0 := by simp [hg, expNegSubOne]
    rw [ContinuousWithinAt, hg0]
    have hlim : Tendsto (fun x : ℝ => x ^ (w.re + 1)) (𝓝[Ici 0] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (w.re + 1) (Or.inr (by linarith))).tendsto
      rw [Real.zero_rpow (by linarith)] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    rcases (show (0 : ℝ) ≤ x from hx).eq_or_lt with h | h
    · subst h
      rw [hg0, norm_zero, Real.zero_rpow (by linarith)]
    · rw [hg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h, Real.rpow_add_one h.ne']
      exact mul_le_mul_of_nonneg_left (norm_expNegSubOne_le_self h.le) (by positivity)
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hl : Tendsto (fun x : ℝ => x ^ w.re) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := -w.re) (by linarith)
      simpa using this
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [hg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    calc x ^ w.re * ‖expNegSubOne x‖ ≤ x ^ w.re * 1 :=
          mul_le_mul_of_nonneg_left (norm_expNegSubOne_le_one hx.le) (by positivity)
      _ = x ^ w.re := mul_one _
  have hconv : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * expNegSubOne x) (Ioi 0) :=
    mellinConvergent_expNegSubOne h1 h2
  have hGamma : IntegrableOn (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (w + 1 - 1))
      (Ioi 0) := Complex.GammaIntegral_convergent (by simp; linarith)
  have hint : IntegrableOn (fun x : ℝ => w * ((x : ℂ) ^ (w - 1) * expNegSubOne x) -
      ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (w + 1 - 1)) (Ioi 0) :=
    Integrable.sub (Integrable.const_mul hconv w) hGamma
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hg0 : g 0 = 0 := by simp [hg, expNegSubOne]
  rw [hg0, sub_zero] at hmain
  rw [integral_sub (Integrable.const_mul hconv w) hGamma, integral_const_mul] at hmain
  have hΓ : (∫ x in Ioi (0 : ℝ), ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (w + 1 - 1)) =
      Complex.Gamma (w + 1) := by
    rw [Complex.Gamma_eq_integral (by simp; linarith)]
    rfl
  rw [hΓ, Complex.Gamma_add_one w hw0, sub_eq_zero] at hmain
  have hmel : mellin expNegSubOne w =
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (w - 1) * expNegSubOne x := by
    simp [mellin, smul_eq_mul]
  rw [hmel]
  exact mul_left_cancel₀ hw0 hmain

/-- `e^{-πx} - 1` is Mellin-convergent at `s/2` for `-2 < Re s < 0`. -/
theorem mellinConvergent_exp_neg_pi_sub_one_half {s : ℂ} (h1 : -2 < s.re) (h2 : s.re < 0) :
    MellinConvergent (fun x : ℝ => expNegSubOne (Real.pi * x)) (s / 2) := by
  rw [MellinConvergent.comp_mul_left Real.pi_pos]
  exact mellinConvergent_expNegSubOne (by simp; linarith) (by simp; linarith)

/-- **`Γ_ℝ` as a Mellin transform left of its pole.**  For `-2 < Re s < 0`, the Mellin transform
of `e^{-πx} - 1` at `s/2` is `Γ_ℝ(s) = π^{-s/2} Γ(s/2)`. -/
theorem mellin_exp_neg_pi_sub_one_half {s : ℂ} (h1 : -2 < s.re) (h2 : s.re < 0) :
    mellin (fun x : ℝ => expNegSubOne (Real.pi * x)) (s / 2) = Complex.Gammaℝ s := by
  rw [mellin_comp_mul_left _ _ Real.pi_pos,
    mellin_expNegSubOne (by simp; linarith) (by simp; linarith), Complex.Gammaℝ_def,
    smul_eq_mul, neg_div]

end GaloisForLFunctions.HTGeometry
