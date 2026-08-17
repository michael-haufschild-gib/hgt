import GaloisForLFunctions.HTGeometry.BesselOrderAbsoluteAsymptotic

/-!
# Half-line Gaussian moments with a complex parameter

The moment `∫_0^∞ v^{2k} e^{-wv²} dv` is defined for every `w` in the open right half plane, and one
integration by parts lowers `k` by one at the cost of the factor `(2k-1)/(2w)`.  The recursion starts
at the complex Gaussian integral, so every even moment is an explicit rational multiple of
`(π/w)^{1/2}`.

This is the exact evaluation that Watson's lemma consumes on the Gaussian half line.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Integrability

theorem norm_pow_mul_cexp_neg_mul_sq (w : ℂ) (m : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    ‖((v : ℂ) ^ m) * Complex.exp (-w * (v : ℂ) ^ 2)‖ = v ^ m * Real.exp (-(w.re * v ^ 2)) := by
  rw [norm_mul, _root_.HTGeometry.norm_cexp_neg_mul_sq, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hv]

theorem integrableOn_pow_mul_cexp_neg_mul_sq {w : ℂ} (hw : 0 < w.re) (m : ℕ) :
    IntegrableOn (fun v : ℝ => ((v : ℂ) ^ m) * Complex.exp (-w * (v : ℂ) ^ 2)) (Ioi 0) := by
  have hdom : Integrable (fun v : ℝ => v ^ ((m : ℕ) : ℝ) * Real.exp (-w.re * v ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq hw (by
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)
  have hmeas : AEStronglyMeasurable
      (fun v : ℝ => ((v : ℂ) ^ m) * Complex.exp (-w * (v : ℂ) ^ 2))
      (volume.restrict (Ioi (0 : ℝ))) := by
    fun_prop
  refine Integrable.mono' hdom.integrableOn hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (0 : ℝ) ≤ v := le_of_lt hv
  rw [norm_pow_mul_cexp_neg_mul_sq w m hv0, Real.rpow_natCast]
  have hexp : Real.exp (-(w.re * v ^ 2)) = Real.exp (-w.re * v ^ 2) := by ring_nf
  rw [hexp]

end Integrability

section Moments

/-- The even half-line Gaussian moment with a complex parameter. -/
def gaussianHalfMoment (w : ℂ) (k : ℕ) : ℂ :=
  ∫ v in Ioi (0 : ℝ), ((v : ℂ) ^ (2 * k)) * Complex.exp (-w * (v : ℂ) ^ 2)

theorem gaussianHalfMoment_zero {w : ℂ} (hw : 0 < w.re) :
    gaussianHalfMoment w 0 = ((Real.pi : ℂ) / w) ^ (1 / 2 : ℂ) / 2 := by
  rw [gaussianHalfMoment]
  have : ∀ v : ℝ, ((v : ℂ) ^ (2 * 0)) * Complex.exp (-w * (v : ℂ) ^ 2)
      = Complex.exp (-w * (v : ℂ) ^ 2) := by
    intro v
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi fun v _ => this v]
  exact integral_gaussian_complex_Ioi hw

theorem hasDerivAt_pow_succ_mul_cexp (w : ℂ) (n : ℕ) (v : ℝ) :
    HasDerivAt (fun u : ℝ => ((u : ℂ) ^ (n + 1)) * Complex.exp (-w * (u : ℂ) ^ 2))
      (((n : ℂ) + 1) * (v : ℂ) ^ n * Complex.exp (-w * (v : ℂ) ^ 2)
        + (v : ℂ) ^ (n + 1) * (Complex.exp (-w * (v : ℂ) ^ 2) * (-w * (2 * (v : ℂ))))) v := by
  have hpow : HasDerivAt (fun u : ℝ => ((u : ℂ) ^ (n + 1)))
      (((n : ℂ) + 1) * (v : ℂ) ^ n) v := by
    have hz : HasDerivAt (fun z : ℂ => z ^ (n + 1)) (((n : ℂ) + 1) * (v : ℂ) ^ n) (v : ℂ) := by
      simpa using hasDerivAt_pow (n + 1) (v : ℂ)
    exact hz.comp_ofReal
  exact hpow.mul (_root_.HTGeometry.hasDerivAt_cexp_neg_mul_sq w v)

/-- A power times a Gaussian tends to zero. -/
theorem tendsto_pow_mul_exp_neg_mul_sq {B : ℝ} (hB : 0 < B) (n : ℕ) :
    Tendsto (fun v : ℝ => v ^ n * Real.exp (-(B * v ^ 2))) atTop (𝓝 0) := by
  have hsq : Tendsto (fun v : ℝ => B * v ^ 2) atTop atTop := by
    have : Tendsto (fun v : ℝ => v ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
    exact Filter.Tendsto.const_mul_atTop hB this
  have h1 : Tendsto (fun v : ℝ => Real.exp (-(B * v ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hsq
  have h2 : Tendsto (fun v : ℝ => v ^ (2 * n) * Real.exp (-(B * v ^ 2))) atTop (𝓝 0) := by
    have hcomp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hsq
    have hscale : Tendsto (fun v : ℝ => (B ^ n)⁻¹ * ((B * v ^ 2) ^ n * Real.exp (-(B * v ^ 2))))
        atTop (𝓝 0) := by
      simpa using hcomp.const_mul ((B ^ n)⁻¹)
    refine hscale.congr fun v => ?_
    rw [mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul,
      ← pow_mul, mul_comm 2 n]
  refine squeeze_zero_norm' ?_ (by simpa using h1.add h2)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
  have hexp : (0 : ℝ) < Real.exp (-(B * v ^ 2)) := Real.exp_pos _
  have hpow : v ^ n ≤ 1 + v ^ (2 * n) := by
    rcases le_or_gt v 1 with h | h
    · have : v ^ n ≤ 1 := pow_le_one₀ hv h
      nlinarith [pow_nonneg hv (2 * n)]
    · have h1v : (1 : ℝ) ≤ v := h.le
      have : v ^ n ≤ v ^ (2 * n) := pow_le_pow_right₀ h1v (by omega)
      nlinarith
  rw [Real.norm_of_nonneg (by positivity)]
  calc v ^ n * Real.exp (-(B * v ^ 2))
      ≤ (1 + v ^ (2 * n)) * Real.exp (-(B * v ^ 2)) :=
        mul_le_mul_of_nonneg_right hpow hexp.le
    _ = Real.exp (-(B * v ^ 2)) + v ^ (2 * n) * Real.exp (-(B * v ^ 2)) := by ring

theorem tendsto_pow_mul_cexp_neg_mul_sq {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    Tendsto (fun v : ℝ => ((v : ℂ) ^ n) * Complex.exp (-w * (v : ℂ) ^ 2)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_pow_mul_exp_neg_mul_sq hw n)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
  rw [norm_pow_mul_cexp_neg_mul_sq w n hv]

/-- **The moment recursion.**  One integration by parts lowers the even moment by one. -/
theorem gaussianHalfMoment_succ {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    gaussianHalfMoment w (k + 1) = ((2 * (k : ℂ) + 1) / (2 * w)) * gaussianHalfMoment w k := by
  have hwne : w ≠ 0 := _root_.HTGeometry.ne_zero_of_re_pos hw
  have h2w : (2 : ℂ) * w ≠ 0 := by simp [hwne]
  have hint1 := integrableOn_pow_mul_cexp_neg_mul_sq hw (2 * k)
  have hint2 := integrableOn_pow_mul_cexp_neg_mul_sq hw (2 * (k + 1))
  have hpt : ∀ v : ℝ, (((2 * k : ℕ) : ℂ) + 1) * (v : ℂ) ^ (2 * k)
        * Complex.exp (-w * (v : ℂ) ^ 2)
      + (v : ℂ) ^ (2 * k + 1) * (Complex.exp (-w * (v : ℂ) ^ 2) * (-w * (2 * (v : ℂ))))
      = (((2 * k : ℕ) : ℂ) + 1) * ((v : ℂ) ^ (2 * k) * Complex.exp (-w * (v : ℂ) ^ 2))
        + (-2 * w) * ((v : ℂ) ^ (2 * (k + 1)) * Complex.exp (-w * (v : ℂ) ^ 2)) := by
    intro v
    have hpow : (v : ℂ) ^ (2 * (k + 1)) = (v : ℂ) ^ (2 * k + 1) * (v : ℂ) := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
    rw [hpow]
    ring
  have hint' : IntegrableOn (fun v : ℝ => (((2 * k : ℕ) : ℂ) + 1) * (v : ℂ) ^ (2 * k)
      * Complex.exp (-w * (v : ℂ) ^ 2)
      + (v : ℂ) ^ (2 * k + 1) * (Complex.exp (-w * (v : ℂ) ^ 2) * (-w * (2 * (v : ℂ)))))
      (Ioi 0) := by
    have h := (hint1.const_mul (((2 * k : ℕ) : ℂ) + 1)).add (hint2.const_mul (-2 * w))
    refine h.congr ?_
    filter_upwards with v
    exact (hpt v).symm
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun u : ℝ => ((u : ℂ) ^ (2 * k + 1)) * Complex.exp (-w * (u : ℂ) ^ 2))
    (f' := fun v : ℝ => (((2 * k : ℕ) : ℂ) + 1) * (v : ℂ) ^ (2 * k)
        * Complex.exp (-w * (v : ℂ) ^ 2)
      + (v : ℂ) ^ (2 * k + 1) * (Complex.exp (-w * (v : ℂ) ^ 2) * (-w * (2 * (v : ℂ)))))
    (a := 0) (m := 0)
    (by fun_prop)
    (fun v _ => hasDerivAt_pow_succ_mul_cexp w (2 * k) v)
    hint' (tendsto_pow_mul_cexp_neg_mul_sq hw (2 * k + 1))
  have hzero : ((0 : ℝ) : ℂ) ^ (2 * k + 1) * Complex.exp (-w * ((0 : ℝ) : ℂ) ^ 2) = 0 := by
    simp
  rw [hzero, sub_zero] at hFTC
  rw [setIntegral_congr_fun measurableSet_Ioi (fun v _ => hpt v),
    MeasureTheory.integral_add (hint1.const_mul _) (hint2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hFTC
  rw [← gaussianHalfMoment, ← gaussianHalfMoment] at hFTC
  have hcast : ((2 * k : ℕ) : ℂ) + 1 = 2 * (k : ℂ) + 1 := by push_cast; ring
  rw [hcast] at hFTC
  rw [div_mul_eq_mul_div, eq_div_iff h2w]
  linear_combination -hFTC

/-- **The closed form.**  Every even half-line Gaussian moment is an explicit rational multiple of
the Gaussian integral. -/
theorem gaussianHalfMoment_eq {w : ℂ} (hw : 0 < w.re) (k : ℕ) :
    gaussianHalfMoment w k
      = (∏ j ∈ Finset.range k, ((2 * (j : ℂ) + 1) / (2 * w)))
        * (((Real.pi : ℂ) / w) ^ (1 / 2 : ℂ) / 2) := by
  induction k with
  | zero => simpa using gaussianHalfMoment_zero hw
  | succ k ih =>
      rw [gaussianHalfMoment_succ hw k, ih, Finset.prod_range_succ]
      ring

end Moments

end

end GaloisForLFunctions.HTGeometry
