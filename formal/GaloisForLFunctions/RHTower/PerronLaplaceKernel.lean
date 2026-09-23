import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The Laplace kernel integral `∫₀^∞ t·e^{-ct} dt = 1/c²`

For complex `c` with `Re c > 0`: the antiderivative
`-(t/c + 1/c²)·e^{-ct}` closes the improper integral.  Evaluated at
`c = a + iτ` this identifies `(a+iτ)⁻²` as the Fourier transform of the
one-sided tent `t·e^{-at}·1_{t>0}` — the kernel of the smoothed Perron
formula whose inversion evaluates `(1/2πi)∫_{(a)} y^s/s² ds = (log y)⁺`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter

/-- The exponential-linear bound `v ≤ e^{v/2}` for `v ≥ 0`. -/
theorem le_exp_half {v : ℝ} (hv : 0 ≤ v) : v ≤ Real.exp (v / 2) := by
  have h1 : v / 4 + 1 ≤ Real.exp (v / 4) := by
    linarith [Real.add_one_le_exp (v / 4)]
  have h2 : (v / 4 + 1) ^ (2 : ℕ) ≤ Real.exp (v / 4) ^ (2 : ℕ) := by
    apply pow_le_pow_left₀ (by linarith) h1
  have h3 : Real.exp (v / 4) ^ (2 : ℕ) = Real.exp (v / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : v ≤ (v / 4 + 1) ^ (2 : ℕ) := by nlinarith [sq_nonneg (v / 4 - 1)]
  linarith

/-- Integrability of the tent integrand. -/
theorem integrableOn_mul_exp_neg_mul {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-(c * t)))
      (Set.Ioi (0 : ℝ)) := by
  have hg : IntegrableOn
      (fun t : ℝ => (1 / c.re) * Real.exp (-(c.re / 2) * t))
      (Set.Ioi (0 : ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 (by linarith)).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) * Complex.exp (-(c * t)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  apply Integrable.mono hg hmeas
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  rw [Set.mem_Ioi] at ht
  have hnorm : ‖(t : ℂ) * Complex.exp (-(c * t))‖
      = t * Real.exp (-(c.re * t)) := by
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
    congr 2
    simp [Complex.mul_re]
  rw [hnorm]
  have hb : t * Real.exp (-(c.re * t))
      ≤ (1 / c.re) * Real.exp (-(c.re / 2) * t) := by
    have h1 : c.re * t ≤ Real.exp (c.re * t / 2) :=
      le_exp_half (by positivity)
    have h2 : Real.exp (-(c.re * t))
        = Real.exp (-(c.re * t / 2)) * Real.exp (-(c.re * t / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : c.re * t * Real.exp (-(c.re * t))
        ≤ Real.exp (-(c.re * t / 2)) := by
      rw [h2, ← mul_assoc]
      calc c.re * t * Real.exp (-(c.re * t / 2))
            * Real.exp (-(c.re * t / 2))
          ≤ (Real.exp (c.re * t / 2) * Real.exp (-(c.re * t / 2)))
            * Real.exp (-(c.re * t / 2)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
        _ = Real.exp (-(c.re * t / 2)) := by
            rw [← Real.exp_add,
              show c.re * t / 2 + -(c.re * t / 2) = 0 by ring]
            simp
    have h4 : t * Real.exp (-(c.re * t))
        = (1 / c.re) * (c.re * t * Real.exp (-(c.re * t))) := by
      field_simp
    rw [h4]
    have h5 : -(c.re * t / 2) = -(c.re / 2) * t := by ring
    rw [← h5]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hgn : ‖(1 / c.re) * Real.exp (-(c.re / 2) * t)‖
      = (1 / c.re) * Real.exp (-(c.re / 2) * t) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  linarith [hgn.ge, hgn.le, hb]

set_option maxHeartbeats 1600000 in
/-- **The Laplace kernel integral**: `∫₀^∞ t·e^{-ct} dt = 1/c²` for
`Re c > 0`. -/
theorem integral_mul_exp_neg_mul_Ioi {c : ℂ} (hc : 0 < c.re) :
    ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) * Complex.exp (-(c * t))
      = 1 / c ^ (2 : ℕ) := by
  have hcne : c ≠ 0 := fun h => by rw [h] at hc; simp at hc
  -- the antiderivative
  have hF : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => -(((s : ℂ) / c + 1 / c ^ (2 : ℕ))
        * Complex.exp (-(c * s))))
      ((t : ℂ) * Complex.exp (-(c * t))) t := by
    intro t
    have hE : HasDerivAt (fun s : ℝ => Complex.exp (-(c * s)))
        (Complex.exp (-(c * t)) * -c) t := by
      have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(c * z)))
          (Complex.exp (-(c * (t : ℂ))) * -c) (t : ℂ) := by
        have h2 : HasDerivAt (fun z : ℂ => -(c * z)) (-c) (t : ℂ) := by
          have h2raw := ((hasDerivAt_id ((t : ℝ) : ℂ)).const_mul c).neg
          have hfun :
              -(fun z : ℂ => c * id z) = (fun z : ℂ => -(c * z)) := by
            funext z
            rfl
          rw [hfun] at h2raw
          apply h2raw.congr_deriv
          ring
        exact (Complex.hasDerivAt_exp (-(c * (t : ℂ)))).comp
          ((t : ℝ) : ℂ) h2
      exact h1.comp_ofReal
    have hA : HasDerivAt (fun s : ℝ => (s : ℂ) / c + 1 / c ^ (2 : ℕ))
        (1 / c) t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t :=
        (hasDerivAt_id ((t : ℝ) : ℂ)).comp_ofReal
      simpa using (h1.div_const c).add_const (1 / c ^ (2 : ℕ))
    have hprod := (hA.mul hE).neg
    have hfun :
        -((fun s : ℝ => (s : ℂ) / c + 1 / c ^ (2 : ℕ)) *
          (fun s : ℝ => Complex.exp (-(c * s)))) =
        (fun s : ℝ => -(((s : ℂ) / c + 1 / c ^ (2 : ℕ)) *
          Complex.exp (-(c * s)))) := by
      funext s
      rfl
    rw [hfun] at hprod
    apply hprod.congr_deriv
    field_simp [hcne]
    ring
  -- continuity at the origin
  have hcont : ContinuousWithinAt
      (fun s : ℝ => -(((s : ℂ) / c + 1 / c ^ (2 : ℕ))
        * Complex.exp (-(c * s)))) (Set.Ici 0) 0 := by
    apply Continuous.continuousWithinAt
    fun_prop
  -- vanishing at infinity
  have htend : Tendsto
      (fun s : ℝ => -(((s : ℂ) / c + 1 / c ^ (2 : ℕ))
        * Complex.exp (-(c * s)))) atTop (nhds 0) := by
    apply squeeze_zero_norm'
      (a := fun s : ℝ => (s / ‖c‖ + 1 / ‖c‖ ^ (2 : ℕ)) * Real.exp (-(c.re * s)))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      rw [norm_neg, norm_mul, Complex.norm_exp]
      have h1 : (-(c * (s : ℂ))).re = -(c.re * s) := by
        simp [Complex.mul_re]
      rw [h1]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      calc ‖(s : ℂ) / c + 1 / c ^ (2 : ℕ)‖
          ≤ ‖(s : ℂ) / c‖ + ‖(1 : ℂ) / c ^ (2 : ℕ)‖ := norm_add_le _ _
        _ ≤ |s| / ‖c‖ + 1 / ‖c‖ ^ (2 : ℕ) := by
            rw [norm_div, norm_div, norm_one, norm_pow, Complex.norm_real,
              Real.norm_eq_abs]
        _ ≤ s / ‖c‖ + 1 / ‖c‖ ^ (2 : ℕ) := by
            rw [abs_of_nonneg hs]
    · have h1 : Tendsto (fun s : ℝ => s * Real.exp (-(c.re * s)))
          atTop (nhds 0) := by
        have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
        have h3 : Tendsto (fun s : ℝ => c.re * s) atTop atTop :=
          Tendsto.const_mul_atTop hc tendsto_id
        have h4 := (h2.comp h3)
        have h5 : (fun s : ℝ => ((c.re * s) ^ (1 : ℕ)
            * Real.exp (-(c.re * s)))) = fun s : ℝ =>
            c.re * (s * Real.exp (-(c.re * s))) := by
          funext s
          ring
        rw [Function.comp_def, h5] at h4
        have h6 := h4.const_mul (1 / c.re)
        simpa [mul_comm, mul_assoc, ne_of_gt hc] using h6
      have h7 : Tendsto (fun s : ℝ => Real.exp (-(c.re * s)))
          atTop (nhds 0) := by
        have h8 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (Tendsto.const_mul_atTop hc tendsto_id)
        simpa [Function.comp_def] using h8
      have h9 := (h1.const_mul (1 / ‖c‖)).add
        (h7.const_mul (1 / ‖c‖ ^ (2 : ℕ)))
      have h10 : (fun s : ℝ => 1 / ‖c‖ * (s * Real.exp (-(c.re * s)))
          + 1 / ‖c‖ ^ (2 : ℕ) * Real.exp (-(c.re * s)))
          = fun s : ℝ => (s / ‖c‖ + 1 / ‖c‖ ^ (2 : ℕ))
            * Real.exp (-(c.re * s)) := by
        funext s
        ring
      rw [h10] at h9
      simpa using h9
  have hval := integral_Ioi_of_hasDerivAt_of_tendsto hcont
    (fun x _ => hF x) (integrableOn_mul_exp_neg_mul hc) htend
  rw [hval]
  simp [Complex.exp_zero]

end RHTower
