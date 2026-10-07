import Mathlib

/-!
# Argument variation of a polynomial along a segment and continuous logarithms

**Segment bound** (`abs_integral_im_logDeriv_le`).  If a complex polynomial `q` has no zero on the
real segment `[0,1]`, then the argument variation of `q` along it satisfies

`|∫₀¹ Im(q'(s)/q(s)) ds| ≤ π · deg q`.

Each root `r` contributes the angle subtended at `r` by `[0,1]`, namely
`arctan((1 − Re r)/Im r) − arctan(−Re r/Im r)`, which lies in `(−π, π)`.  A real root off the
segment contributes nothing.

**Exponential lift** (`exp_log_add_integral_logDeriv`).  For such `q`,
`exp(log q(0) + ∫₀¹ q'/q) = q(1)`.

**Continuous logarithms are differentiable** (`hasDerivAt_of_exp_eq`).  If `exp ∘ L = g` near `x₀`,
`L` is continuous at `x₀` and `g` is differentiable at `x₀` with `g(x₀) ≠ 0`, then
`L'(x₀) = g'(x₀)/g(x₀)`.
-/

open Complex Polynomial Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The angle subtended by the unit segment -/

theorem im_inv_sub (s : ℝ) (r : ℂ) :
    (1 / ((s : ℂ) - r)).im = r.im / ((s - r.re) ^ 2 + r.im ^ 2) := by
  rw [one_div, Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg, Complex.sub_re,
    Complex.ofReal_re]
  congr 1
  ring

theorem abs_integral_im_inv_sub_le (r : ℂ) :
    |∫ s in (0 : ℝ)..1, (1 / ((s : ℂ) - r)).im| ≤ Real.pi := by
  simp_rw [im_inv_sub]
  by_cases hr : r.im = 0
  · simp [hr, Real.pi_pos.le]
  · have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s => Real.arctan ((s - r.re) / r.im))
          (r.im / ((s - r.re) ^ 2 + r.im ^ 2)) s := by
      intro s _
      have hb : r.im ≠ 0 := hr
      have h := (Real.hasDerivAt_arctan ((s - r.re) / r.im)).comp s
        (((hasDerivAt_id s).sub_const r.re).div_const r.im)
      refine h.congr_deriv ?_
      have hpos : 0 < (s - r.re) ^ 2 + r.im ^ 2 := by positivity
      field_simp
      ring
    have hcont : ContinuousOn (fun s : ℝ => r.im / ((s - r.re) ^ 2 + r.im ^ 2)) (uIcc 0 1) := by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro s _
      have : 0 < r.im ^ 2 := by positivity
      positivity
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
    have h1 := Real.arctan_lt_pi_div_two ((1 - r.re) / r.im)
    have h2 := Real.neg_pi_div_two_lt_arctan ((1 - r.re) / r.im)
    have h3 := Real.arctan_lt_pi_div_two ((0 - r.re) / r.im)
    have h4 := Real.neg_pi_div_two_lt_arctan ((0 - r.re) / r.im)
    rw [abs_le]
    constructor <;> linarith

/-! ## The segment bound -/

theorem continuousOn_logDeriv_poly_segment {q : ℂ[X]}
    (hq : ∀ s ∈ Icc (0 : ℝ) 1, q.eval (s : ℂ) ≠ 0) :
    ContinuousOn (fun s : ℝ => (derivative q).eval (s : ℂ) / q.eval (s : ℂ)) (uIcc 0 1) := by
  rw [uIcc_of_le zero_le_one]
  apply ContinuousOn.div
  · exact ((derivative q).continuous.comp Complex.continuous_ofReal).continuousOn
  · exact (q.continuous.comp Complex.continuous_ofReal).continuousOn
  · exact hq

/-- **The segment bound.** -/
theorem abs_integral_im_logDeriv_le :
    ∀ (n : ℕ) (q : ℂ[X]), q.natDegree = n → (∀ s ∈ Icc (0 : ℝ) 1, q.eval (s : ℂ) ≠ 0) →
      |∫ s in (0 : ℝ)..1, ((derivative q).eval (s : ℂ) / q.eval (s : ℂ)).im| ≤ Real.pi * n := by
  intro n
  induction n with
  | zero =>
    intro q hdeg _
    obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hdeg
    simp
  | succ n ih =>
    intro q hdeg hq
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact hq 0 ⟨le_rfl, zero_le_one⟩ (by simp)
    have hdeg0 : q.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hq0, hdeg]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root q hdeg0
    set q₁ := q /ₘ (X - C r) with hq₁
    have hfac : (X - C r) * q₁ = q := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hr
    have hq₁0 : q₁ ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hfac
      exact hq0 hfac.symm
    have hdeg₁ : q₁.natDegree = n := by
      have := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hq₁0
      rw [hfac, Polynomial.natDegree_X_sub_C, hdeg] at this
      omega
    have hval : ∀ s : ℝ, q.eval (s : ℂ) = ((s : ℂ) - r) * q₁.eval (s : ℂ) := by
      intro s
      rw [← hfac, Polynomial.eval_mul]
      simp
    have hq₁ne : ∀ s ∈ Icc (0 : ℝ) 1, q₁.eval (s : ℂ) ≠ 0 := by
      intro s hs h
      exact hq s hs (by rw [hval, h, mul_zero])
    have hsr : ∀ s ∈ Icc (0 : ℝ) 1, (s : ℂ) - r ≠ 0 := by
      intro s hs h
      exact hq s hs (by rw [hval, h, zero_mul])
    have hsplit : ∀ s ∈ uIcc (0 : ℝ) 1,
        ((derivative q).eval (s : ℂ) / q.eval (s : ℂ)).im =
          (1 / ((s : ℂ) - r)).im + ((derivative q₁).eval (s : ℂ) / q₁.eval (s : ℂ)).im := by
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      have hd : (derivative q).eval (s : ℂ) =
          q₁.eval (s : ℂ) + ((s : ℂ) - r) * (derivative q₁).eval (s : ℂ) := by
        rw [← hfac, Polynomial.derivative_mul]
        simp
      rw [hd, hval, ← Complex.add_im]
      congr 1
      field_simp [hsr s hs, hq₁ne s hs]
    have hci : ∀ g : ℝ → ℂ, ContinuousOn g (uIcc 0 1) →
        IntervalIntegrable (fun s => (g s).im) MeasureTheory.volume 0 1 :=
      fun g hg => (Complex.continuous_im.comp_continuousOn hg).intervalIntegrable
    have hinv : ContinuousOn (fun s : ℝ => 1 / ((s : ℂ) - r)) (uIcc 0 1) := by
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      exact hsr s hs
    rw [intervalIntegral.integral_congr hsplit,
      intervalIntegral.integral_add (hci _ hinv) (hci _ (continuousOn_logDeriv_poly_segment hq₁ne))]
    have h1 := abs_integral_im_inv_sub_le r
    have h2 := ih q₁ hdeg₁ hq₁ne
    calc _ ≤ |∫ s in (0 : ℝ)..1, (1 / ((s : ℂ) - r)).im| +
          |∫ s in (0 : ℝ)..1, ((derivative q₁).eval (s : ℂ) / q₁.eval (s : ℂ)).im| :=
          abs_add_le _ _
      _ ≤ Real.pi + Real.pi * n := add_le_add h1 h2
      _ = Real.pi * ((n + 1 : ℕ) : ℝ) := by push_cast; ring

/-! ## The exponential lift along the segment -/

/-- The clamped logarithmic derivative: continuous on all of `ℝ`, equal to `q'/q` on `[0,1]`. -/
def clampedLogDeriv (q : ℂ[X]) (s : ℝ) : ℂ :=
  (derivative q).eval ((projIcc (0 : ℝ) 1 zero_le_one s : ℝ) : ℂ) /
    q.eval ((projIcc (0 : ℝ) 1 zero_le_one s : ℝ) : ℂ)

theorem continuous_clampedLogDeriv {q : ℂ[X]}
    (hq : ∀ s ∈ Icc (0 : ℝ) 1, q.eval (s : ℂ) ≠ 0) : Continuous (clampedLogDeriv q) := by
  unfold clampedLogDeriv
  have hp : Continuous fun s : ℝ => ((projIcc (0 : ℝ) 1 zero_le_one s : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_projIcc)
  exact ((derivative q).continuous.comp hp).div (q.continuous.comp hp)
    fun s => hq _ (projIcc (0 : ℝ) 1 zero_le_one s).2

theorem clampedLogDeriv_eq {q : ℂ[X]} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    clampedLogDeriv q s = (derivative q).eval (s : ℂ) / q.eval (s : ℂ) := by
  unfold clampedLogDeriv
  rw [projIcc_of_mem zero_le_one hs]

theorem integral_clampedLogDeriv (q : ℂ[X]) :
    ∫ s in (0 : ℝ)..1, clampedLogDeriv q s =
      ∫ s in (0 : ℝ)..1, (derivative q).eval (s : ℂ) / q.eval (s : ℂ) := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le zero_le_one] at hs
  exact clampedLogDeriv_eq hs

/-- `exp(log q(0) + ∫₀¹ q'/q) = q(1)` when `q` has no zero on `[0,1]`. -/
theorem exp_log_add_integral_logDeriv {q : ℂ[X]} (hq : ∀ s ∈ Icc (0 : ℝ) 1, q.eval (s : ℂ) ≠ 0) :
    Complex.exp (Complex.log (q.eval 0) +
        ∫ s in (0 : ℝ)..1, (derivative q).eval (s : ℂ) / q.eval (s : ℂ)) = q.eval 1 := by
  set h := clampedLogDeriv q with hh
  have hc : Continuous h := continuous_clampedLogDeriv hq
  set φ : ℝ → ℂ := fun s => q.eval (s : ℂ) * Complex.exp (-∫ t in (0 : ℝ)..s, h t) with hφ
  have hderiv : ∀ x : ℝ, HasDerivAt φ ((derivative q).eval (x : ℂ) *
      Complex.exp (-∫ t in (0 : ℝ)..x, h t) + q.eval (x : ℂ) *
        (Complex.exp (-∫ t in (0 : ℝ)..x, h t) * -h x)) x := by
    intro x
    have h1 : HasDerivAt (fun s : ℝ => q.eval (s : ℂ)) ((derivative q).eval (x : ℂ)) x := by
      simpa using (q.hasDerivAt (x : ℂ)).comp_ofReal
    have h2 : HasDerivAt (fun s => ∫ t in (0 : ℝ)..s, h t) (h x) x :=
      intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    exact h1.mul (h2.neg.cexp)
  have hzero : ∀ x ∈ Icc (0 : ℝ) 1, (derivative q).eval (x : ℂ) *
      Complex.exp (-∫ t in (0 : ℝ)..x, h t) + q.eval (x : ℂ) *
        (Complex.exp (-∫ t in (0 : ℝ)..x, h t) * -h x) = 0 := by
    intro x hx
    rw [hh, clampedLogDeriv_eq hx]
    field_simp [hq x hx]
    ring
  have hconst := constant_of_has_deriv_right_zero (f := φ) (a := 0) (b := 1)
    (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
    (fun x hx => by
      have := (hderiv x).hasDerivWithinAt (s := Ici x)
      rwa [hzero x (Ico_subset_Icc_self hx)] at this) 1 ⟨zero_le_one, le_rfl⟩
  simp only [hφ, intervalIntegral.integral_same, neg_zero, Complex.exp_zero, mul_one,
    Complex.ofReal_one, Complex.ofReal_zero] at hconst
  have hq0 : q.eval 0 ≠ 0 := by simpa using hq 0 ⟨le_rfl, zero_le_one⟩
  rw [Complex.exp_add, Complex.exp_log hq0, ← integral_clampedLogDeriv, ← hh, ← hconst]
  rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-! ## Continuous logarithms are differentiable -/

/-- A continuous logarithm of a differentiable nonvanishing function is differentiable, with
derivative the logarithmic derivative. -/
theorem hasDerivAt_of_exp_eq {g L : ℝ → ℂ} {x₀ : ℝ} {g' : ℂ} (hg : HasDerivAt g g' x₀)
    (hg0 : g x₀ ≠ 0) (hL : ContinuousAt L x₀) (hexp : ∀ᶠ x in 𝓝 x₀, Complex.exp (L x) = g x) :
    HasDerivAt L (g' / g x₀) x₀ := by
  -- the local branch `M(x) = L(x₀) + log(g(x)/g(x₀))`
  set M : ℝ → ℂ := fun x => L x₀ + Complex.log (g x / g x₀) with hM
  have hratio : HasDerivAt (fun x => g x / g x₀) (g' / g x₀) x₀ := hg.div_const _
  have hslit : g x₀ / g x₀ ∈ Complex.slitPlane := by
    rw [div_self hg0]
    exact Complex.one_mem_slitPlane
  have hMd : HasDerivAt M (g' / g x₀) x₀ := by
    have := (hratio.clog_real hslit).const_add (L x₀)
    rw [div_self hg0, div_one] at this
    exact this
  -- `L − M` is continuous at `x₀`, vanishes there and takes values in `2πiℤ` nearby
  have hMc : ContinuousAt M x₀ := hMd.continuousAt
  have hdiff : ContinuousAt (fun x => L x - M x) x₀ := hL.sub hMc
  have hM0 : M x₀ = L x₀ := by simp [hM, div_self hg0]
  have hsmall : ∀ᶠ x in 𝓝 x₀, ‖L x - M x‖ < 2 * Real.pi := by
    have := hdiff.eventually (Metric.ball_mem_nhds (L x₀ - M x₀) Real.two_pi_pos)
    filter_upwards [this] with x hx
    rw [hM0, sub_self, dist_zero_right] at hx
    exact hx
  have hgnear : ∀ᶠ x in 𝓝 x₀, g x ≠ 0 := hg.continuousAt.eventually_ne hg0
  have heq : L =ᶠ[𝓝 x₀] M := by
    filter_upwards [hexp, hsmall, hgnear] with x hx hxs hgx
    have hexpM : Complex.exp (M x) = g x := by
      have hexp0 : Complex.exp (L x₀) = g x₀ := hexp.self_of_nhds
      simp only [hM]
      rw [Complex.exp_add, Complex.exp_log (div_ne_zero hgx hg0), hexp0]
      field_simp
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hx.trans hexpM.symm)
    have hnorm : ‖L x - M x‖ = 2 * Real.pi * |(n : ℝ)| := by
      rw [hn]
      simp only [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [Complex.norm_ofNat]
      ring
    have hn0 : n = 0 := by
      rw [hnorm] at hxs
      have : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos]
      have : |n| < 1 := by exact_mod_cast this
      have h2 := abs_lt.mp this
      omega
    rw [hn, hn0]
    simp
  exact hMd.congr_of_eventuallyEq heq

end

end GaloisForLFunctions.HTGeometry
