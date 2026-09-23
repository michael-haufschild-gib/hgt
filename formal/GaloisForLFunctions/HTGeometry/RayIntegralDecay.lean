import GaloisForLFunctions.HTGeometry.GammaMonomialAnalytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrating a derivative bound along a horizontal ray

If `f` is analytic on a right half plane, its derivative is `O(‖s‖^{-(N+1)})` there, and `f` tends to
zero along every horizontal ray, then `f` itself is `O(‖s‖^{-N})`.  Integrating the bound from `s` to
`+∞` along the ray is legitimate because `‖s + x‖ ≥ (‖s‖ + x)/2` for `x ≥ 0` in a right half plane.

This converts an asymptotic expansion of a logarithmic derivative into one of the function itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology MeasureTheory

noncomputable section

/-- The elementary tail integral. -/
theorem integral_inv_sq_shift_le {a X : ℝ} (ha : 0 < a) (hX : 0 ≤ X) :
    ∫ x in (0:ℝ)..X, ((a + x) ^ (2 : ℕ))⁻¹ ≤ 1 / a := by
  have huIcc : Set.uIcc (0:ℝ) X = Set.Icc 0 X := Set.uIcc_of_le hX
  have hpos : ∀ x ∈ Set.Icc (0:ℝ) X, 0 < a + x := by
    intro x hx
    have := hx.1
    linarith
  have hder : ∀ x ∈ Set.uIcc (0:ℝ) X,
      HasDerivAt (fun y : ℝ => -(a + y)⁻¹) (((a + x) ^ (2 : ℕ))⁻¹) x := by
    intro x hx
    rw [huIcc] at hx
    have hne : a + x ≠ 0 := ne_of_gt (hpos x hx)
    have h1 : HasDerivAt (fun y : ℝ => a + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add a
    have h2 := (h1.inv hne).neg
    have hfun : (-(fun y : ℝ => a + y)⁻¹) = fun y : ℝ => -(a + y)⁻¹ := by
      funext y; simp
    rw [hfun] at h2
    have hval : -(-1 / (a + x) ^ (2 : ℕ)) = ((a + x) ^ (2 : ℕ))⁻¹ := by ring
    rwa [hval] at h2
  have hcont : ContinuousOn (fun x : ℝ => ((a + x) ^ (2 : ℕ))⁻¹) (Set.uIcc 0 X) := by
    rw [huIcc]
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    have := hpos x hx
    positivity
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (hcont.intervalIntegrable)
  rw [hval]
  have haX : (0 : ℝ) < a + X := by linarith
  have h1 : (0 : ℝ) < (a + X)⁻¹ := by positivity
  have h2 : a + 0 = a := by ring
  rw [h2, one_div]
  linarith

/-- On a right half plane the ray point is comparable to the sum of the norms. -/
theorem norm_add_real_ge_half {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    (‖s‖ + x) / 2 ≤ ‖s + (x : ℂ)‖ := by
  have h1 : ‖s‖ ≤ ‖s + (x : ℂ)‖ := by
    have hre : ‖s‖ ^ (2 : ℕ) ≤ ‖s + (x : ℂ)‖ ^ (2 : ℕ) := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
      nlinarith [hs, hx]
    nlinarith [norm_nonneg s, norm_nonneg (s + (x : ℂ)), hre]
  have h2 : x ≤ ‖s + (x : ℂ)‖ := by
    have : (s + (x : ℂ)).re = s.re + x := by simp
    calc x ≤ s.re + x := by linarith
      _ = (s + (x : ℂ)).re := this.symm
      _ ≤ |(s + (x : ℂ)).re| := le_abs_self _
      _ ≤ ‖s + (x : ℂ)‖ := Complex.abs_re_le_norm _
  linarith

/-- **Integrating a derivative bound along the ray.**  A function analytic on a right half plane
whose derivative is `O(‖s‖^{-(k+2)})` and which vanishes at the end of every horizontal ray is
`O(‖s‖^{-(k+1)})`. -/
theorem norm_le_of_deriv_decay {R₀ A : ℝ} (hR₀ : 0 ≤ R₀) (hA : 0 ≤ A) {k : ℕ} {f : ℂ → ℂ}
    (hana : ∀ z : ℂ, R₀ < z.re → AnalyticAt ℂ f z)
    (hb : ∀ z : ℂ, R₀ < z.re → ‖deriv f z‖ ≤ A / ‖z‖ ^ (k + 2))
    (hlim : ∀ s : ℂ, R₀ < s.re → Tendsto (fun x : ℝ => f (s + (x : ℂ))) atTop (nhds 0)) :
    ∀ s : ℂ, R₀ < s.re → ‖f s‖ ≤ 2 ^ (k + 2) * A / ‖s‖ ^ (k + 1) := by
  intro s hs
  have hsre : 0 < s.re := lt_of_le_of_lt hR₀ hs
  have hspos : (0 : ℝ) < ‖s‖ := by
    have h1 := Complex.abs_re_le_norm s
    have h2 : s.re ≤ |s.re| := le_abs_self _
    linarith
  have hray : ∀ x : ℝ, 0 ≤ x → R₀ < (s + (x : ℂ)).re := by
    intro x hx
    have : (s + (x : ℂ)).re = s.re + x := by simp
    rw [this]
    linarith
  set C : ℝ := 2 ^ (k + 2) * A / ‖s‖ ^ k with hC
  have hC0 : (0 : ℝ) ≤ C := by
    rw [hC]; positivity
  have key : ∀ X : ℝ, 0 ≤ X →
      ‖f (s + (X : ℂ)) - f s‖ ≤ 2 ^ (k + 2) * A / ‖s‖ ^ (k + 1) := by
    intro X hX
    have huIcc : Set.uIcc (0 : ℝ) X = Set.Icc 0 X := Set.uIcc_of_le hX
    have hder : ∀ x ∈ Set.uIcc (0 : ℝ) X,
        HasDerivAt (fun y : ℝ => f (s + (y : ℂ))) (deriv f (s + (x : ℂ))) x := by
      intro x hx
      rw [huIcc] at hx
      have hdf : HasDerivAt f (deriv f (s + (x : ℂ))) (s + (x : ℂ)) :=
        ((hana _ (hray x hx.1)).differentiableAt).hasDerivAt
      have hg : HasDerivAt (fun z : ℂ => s + z) 1 ((x : ℝ) : ℂ) :=
        (hasDerivAt_id ((x : ℝ) : ℂ)).const_add s
      have hcomp := hdf.comp ((x : ℝ) : ℂ) hg
      have hrw : (f ∘ fun z : ℂ => s + z) = fun z : ℂ => f (s + z) := by funext z; rfl
      rw [hrw, mul_one] at hcomp
      exact hcomp.comp_ofReal
    have hcont : ContinuousOn (fun x : ℝ => deriv f (s + (x : ℂ))) (Set.uIcc 0 X) := by
      rw [huIcc]
      intro x hx
      have hda : AnalyticAt ℂ (deriv f) (s + (x : ℂ)) := (hana _ (hray x hx.1)).deriv
      have hcc : ContinuousAt (deriv f) (s + (x : ℂ)) := hda.continuousAt
      have hsc : ContinuousAt (fun y : ℝ => s + (y : ℂ)) x := by fun_prop
      have hcomp : ContinuousAt (deriv f ∘ fun y : ℝ => s + (y : ℂ)) x :=
        ContinuousAt.comp hcc hsc
      have hrw : (deriv f ∘ fun y : ℝ => s + (y : ℂ)) = fun y : ℝ => deriv f (s + (y : ℂ)) := rfl
      rw [hrw] at hcomp
      exact hcomp.continuousWithinAt
    have hint : IntervalIntegrable (fun x : ℝ => deriv f (s + (x : ℂ))) volume 0 X :=
      hcont.intervalIntegrable
    have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
    have hzero : f (s + (((0 : ℝ)) : ℂ)) = f s := by norm_num
    rw [hzero] at hval
    have hnormb : ∀ x ∈ Set.Icc (0 : ℝ) X,
        ‖deriv f (s + (x : ℂ))‖ ≤ C * (((‖s‖ + x)) ^ (2 : ℕ))⁻¹ := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := hx.1
      have hbx := hb _ (hray x hx0)
      have hhalf := norm_add_real_ge_half hsre hx0
      have hsxpos : (0 : ℝ) < ‖s + (x : ℂ)‖ := by
        have : (0 : ℝ) < (‖s‖ + x) / 2 := by linarith
        linarith
      have hsum : (0 : ℝ) < ‖s‖ + x := by linarith
      have hpow : ((‖s‖ + x) / 2) ^ (k + 2) ≤ ‖s + (x : ℂ)‖ ^ (k + 2) :=
        pow_le_pow_left₀ (by linarith) hhalf _
      have hlow : (‖s‖ + x) ^ (k + 2) / 2 ^ (k + 2) ≤ ‖s + (x : ℂ)‖ ^ (k + 2) := by
        rw [div_pow] at hpow
        exact hpow
      have hbig : ‖s‖ ^ k * (‖s‖ + x) ^ (2 : ℕ) ≤ (‖s‖ + x) ^ (k + 2) := by
        have h1 : ‖s‖ ^ k ≤ (‖s‖ + x) ^ k := pow_le_pow_left₀ (le_of_lt hspos) (by linarith) _
        have h2 : (‖s‖ + x) ^ (k + 2) = (‖s‖ + x) ^ k * (‖s‖ + x) ^ (2 : ℕ) := by ring
        rw [h2]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      have hstep : A / ‖s + (x : ℂ)‖ ^ (k + 2) ≤ C * ((‖s‖ + x) ^ (2 : ℕ))⁻¹ := by
        rw [hC]
        rw [div_le_iff₀ (by positivity)]
        have hden : (0 : ℝ) < (‖s‖ + x) ^ (k + 2) := by positivity
        have hfrac : 2 ^ (k + 2) * A / ‖s‖ ^ k * ((‖s‖ + x) ^ (2 : ℕ))⁻¹ * ‖s + (x : ℂ)‖ ^ (k + 2)
            ≥ 2 ^ (k + 2) * A / ‖s‖ ^ k * ((‖s‖ + x) ^ (2 : ℕ))⁻¹
              * ((‖s‖ + x) ^ (k + 2) / 2 ^ (k + 2)) := by
          have hnn : (0 : ℝ) ≤ 2 ^ (k + 2) * A / ‖s‖ ^ k * ((‖s‖ + x) ^ (2 : ℕ))⁻¹ := by positivity
          exact mul_le_mul_of_nonneg_left hlow hnn
        have hval2 : 2 ^ (k + 2) * A / ‖s‖ ^ k * ((‖s‖ + x) ^ (2 : ℕ))⁻¹
              * ((‖s‖ + x) ^ (k + 2) / 2 ^ (k + 2))
            = A * ((‖s‖ + x) ^ (k + 2) / (‖s‖ ^ k * (‖s‖ + x) ^ (2 : ℕ))) := by
          field_simp
        have hAle : A ≤ A * ((‖s‖ + x) ^ (k + 2) / (‖s‖ ^ k * (‖s‖ + x) ^ (2 : ℕ))) := by
          have hratio : (1 : ℝ) ≤ (‖s‖ + x) ^ (k + 2) / (‖s‖ ^ k * (‖s‖ + x) ^ (2 : ℕ)) := by
            rw [le_div_iff₀ (by positivity)]
            linarith [hbig]
          nlinarith [hA, hratio]
        calc A ≤ A * ((‖s‖ + x) ^ (k + 2) / (‖s‖ ^ k * (‖s‖ + x) ^ (2 : ℕ))) := hAle
          _ = 2 ^ (k + 2) * A / ‖s‖ ^ k * ((‖s‖ + x) ^ (2 : ℕ))⁻¹
                * ((‖s‖ + x) ^ (k + 2) / 2 ^ (k + 2)) := hval2.symm
          _ ≤ 2 ^ (k + 2) * A / ‖s‖ ^ k * ((‖s‖ + x) ^ (2 : ℕ))⁻¹ * ‖s + (x : ℂ)‖ ^ (k + 2) := hfrac
      exact le_trans hbx hstep
    have hintnorm : IntervalIntegrable (fun x : ℝ => ‖deriv f (s + (x : ℂ))‖) volume 0 X :=
      hint.norm
    have hintmaj : IntervalIntegrable (fun x : ℝ => C * (((‖s‖ + x)) ^ (2 : ℕ))⁻¹) volume 0 X := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [huIcc]
      refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) ?_)
      intro x hx
      have : (0 : ℝ) < ‖s‖ + x := by have := hx.1; linarith
      positivity
    calc ‖f (s + (X : ℂ)) - f s‖ = ‖∫ x in (0:ℝ)..X, deriv f (s + (x : ℂ))‖ := by rw [hval]
      _ ≤ ∫ x in (0:ℝ)..X, ‖deriv f (s + (x : ℂ))‖ :=
          intervalIntegral.norm_integral_le_integral_norm hX
      _ ≤ ∫ x in (0:ℝ)..X, C * (((‖s‖ + x)) ^ (2 : ℕ))⁻¹ :=
          intervalIntegral.integral_mono_on hX hintnorm hintmaj hnormb
      _ = C * ∫ x in (0:ℝ)..X, (((‖s‖ + x)) ^ (2 : ℕ))⁻¹ := intervalIntegral.integral_const_mul _ _
      _ ≤ C * (1 / ‖s‖) := mul_le_mul_of_nonneg_left (integral_inv_sq_shift_le hspos hX) hC0
      _ = 2 ^ (k + 2) * A / ‖s‖ ^ (k + 1) := by
          rw [hC]
          field_simp
          ring
  have htend : Tendsto (fun X : ℝ => ‖f (s + (X : ℂ))‖ + 2 ^ (k + 2) * A / ‖s‖ ^ (k + 1)) atTop
      (nhds (0 + 2 ^ (k + 2) * A / ‖s‖ ^ (k + 1))) := by
    have h1 := (hlim s hs).norm
    rw [norm_zero] at h1
    exact h1.add tendsto_const_nhds
  have hev : ∀ᶠ X : ℝ in atTop,
      ‖f s‖ ≤ ‖f (s + (X : ℂ))‖ + 2 ^ (k + 2) * A / ‖s‖ ^ (k + 1) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with X hX
    have hk := key X hX
    have heq : f s = f (s + (X : ℂ)) - (f (s + (X : ℂ)) - f s) := by ring
    calc ‖f s‖ = ‖f (s + (X : ℂ)) - (f (s + (X : ℂ)) - f s)‖ := by rw [← heq]
      _ ≤ ‖f (s + (X : ℂ))‖ + ‖f (s + (X : ℂ)) - f s‖ := norm_sub_le _ _
      _ ≤ ‖f (s + (X : ℂ))‖ + 2 ^ (k + 2) * A / ‖s‖ ^ (k + 1) := by linarith
  have := ge_of_tendsto htend hev
  linarith [this]

end

end GaloisForLFunctions.HTGeometry
