import GaloisForLFunctions.Hurwitz.AnalyticContinuation

/-!
# Transversality of the continued Hurwitz zeta at the canonical anchor

The shift continuation was previously proved holomorphic only on the open upper half-plane,
although its canonical normalization at `a = 1` was already available.  For exponents with
positive real part, the zero-degree Taylor subtraction is normally differentiable on a full disk
about `1`.  This crosses the boundary of the upper-half-plane continuation and gives the exact
anchor derivative

`∂ₐ continuedHzeta(s, 1) = -s * riemannZeta(s + 1)`.

Continuity of all analytic shift jets then extends the entire upper-half-plane ladder to the
anchor:

`∂ₐ^r continuedHzeta(s, 1) = (-1)^r (s)_r riemannZeta(s + r)`.

Every positive-order anchor jet is nonzero when `Re s > 0`.

No zero-location or Riemann-hypothesis input is used.
-/

open Complex Filter Metric HurwitzLadder
open scoped Topology

namespace HurwitzZetaContinuation

/-- The canonical continued Hurwitz function is analytic at `a = 1`, and its derivative there is
the exponent-shifted absolutely convergent zeta value. -/
theorem continuedHzeta_analyticAt_one_and_hasDerivAt {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (continuedHzeta s) 1 ∧
      HasDerivAt (continuedHzeta s) (-s * riemannZeta (s + 1)) 1 := by
  let C : ℝ := ‖s‖ * Real.exp (Real.pi * |s.im|)
  let u : ℕ → ℝ := fun m => C * (((m + 1 : ℕ) : ℝ) / 2) ^ (-(s.re + 1))
  have hu : Summable u := by
    have hp : 1 < s.re + 1 := by linarith
    have hpser : Summable (fun n : ℕ => (n : ℝ) ^ (-(s.re + 1))) := by
      have h := (Real.summable_nat_rpow_inv (p := s.re + 1)).mpr hp
      exact h.congr (fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)])
    have hshift : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ)) ^ (-(s.re + 1))) := by
      simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hpser
    have heq : u = fun m : ℕ =>
        (C * (2 : ℝ) ^ (s.re + 1)) * (((m + 1 : ℕ) : ℝ)) ^ (-(s.re + 1)) := by
      funext m
      show C * (((m + 1 : ℕ) : ℝ) / 2) ^ (-(s.re + 1)) = _
      have hb : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by positivity
      rw [Real.div_rpow hb (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv]
      ring
    rw [heq]
    exact hshift.mul_left _
  have hterm : ∀ m : ℕ, ∀ a ∈ Metric.ball (1 : ℂ) (1 / 2 : ℝ),
      HasDerivAt (fun w => remainder 0 s w m)
        (-s * ((m : ℂ) + a) ^ (-(s + 1))) a := by
    intro m a ha
    have hdist : ‖a - 1‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using ha
    have hare : 0 < a.re := by
      have hre := Complex.abs_re_le_norm (a - 1)
      simp only [Complex.sub_re, Complex.one_re] at hre
      have habs := abs_lt.mp (lt_of_le_of_lt hre hdist)
      linarith
    have hb : ((m : ℂ) + a) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simp only [Complex.add_re, Complex.natCast_re]
      positivity
    have hraw := (Complex.hasStrictDerivAt_cpow_const (c := -s) hb).hasDerivAt.comp a
      ((hasDerivAt_const a (m : ℂ)).add (hasDerivAt_id a))
    have hconst : HasDerivAt
        (fun _ : ℂ => (((m + 1 : ℕ) : ℂ) ^ (-s))) 0 a := hasDerivAt_const _ _
    rw [show (fun w => remainder 0 s w m) =
        fun w => ((m : ℂ) + w) ^ (-s) - (((m + 1 : ℕ) : ℂ) ^ (-s)) by
      funext w
      rw [remainder, taylorPoly_zero]]
    convert! hraw.sub hconst using 1
    rw [show -(s + 1) = -s - 1 by ring]
    simp
  have hbound : ∀ m : ℕ, ∀ a ∈ Metric.ball (1 : ℂ) (1 / 2 : ℝ),
      ‖-s * ((m : ℂ) + a) ^ (-(s + 1))‖ ≤ u m := by
    intro m a ha
    have hdist : ‖a - 1‖ < (1 / 2 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using ha
    set z : ℂ := (m : ℂ) + a with hz
    have hbasepos : 0 < (((m + 1 : ℕ) : ℝ) / 2) := by positivity
    have hm : (((m + 1 : ℕ) : ℝ) / 2) ≤ ‖z‖ := by
      have hge : ‖((m + 1 : ℕ) : ℂ)‖ - ‖a - 1‖ ≤ ‖z‖ := by
        have htri := norm_add_le z (-(a - 1))
        have heq : z + -(a - 1) = ((m + 1 : ℕ) : ℂ) := by
          dsimp only [z]
          push_cast
          ring
        rw [heq, norm_neg] at htri
        linarith
      rw [Complex.norm_natCast] at hge
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      norm_num at hdist ⊢
      push_cast at hge ⊢
      linarith
    have hsnonpos : -(s.re + 1) ≤ 0 := by linarith
    have hcpow : ‖z ^ (-(s + 1))‖ ≤
        (((m + 1 : ℕ) : ℝ) / 2) ^ (-(s.re + 1)) *
          Real.exp (Real.pi * |s.im|) := by
      calc
        ‖z ^ (-(s + 1))‖
            ≤ ‖z‖ ^ (-(s + 1)).re / Real.exp (z.arg * (-(s + 1)).im) :=
              Complex.norm_cpow_le z (-(s + 1))
        _ = ‖z‖ ^ (-(s.re + 1)) * Real.exp (z.arg * s.im) := by
          rw [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.neg_im,
            Complex.add_im, Complex.one_im, add_zero, div_eq_mul_inv]
          congr 1
          rw [show z.arg * -s.im = -(z.arg * s.im) by ring,
            Real.exp_neg, inv_inv]
        _ ≤ (((m + 1 : ℕ) : ℝ) / 2) ^ (-(s.re + 1)) *
            Real.exp (Real.pi * |s.im|) := by
          refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hbasepos hm hsnonpos)
            (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _)
            (Real.rpow_nonneg hbasepos.le _)
          calc
            z.arg * s.im ≤ |z.arg * s.im| := le_abs_self _
            _ = |z.arg| * |s.im| := abs_mul _ _
            _ ≤ Real.pi * |s.im| :=
              mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi z) (abs_nonneg _)
    calc
      ‖-s * z ^ (-(s + 1))‖ = ‖s‖ * ‖z ^ (-(s + 1))‖ := by simp
      _ ≤ ‖s‖ * ((((m + 1 : ℕ) : ℝ) / 2) ^ (-(s.re + 1)) *
          Real.exp (Real.pi * |s.im|)) :=
        mul_le_mul_of_nonneg_left hcpow (norm_nonneg s)
      _ = u m := by dsimp only [u, C]; ring
  have hsum0 : Summable (fun m : ℕ => remainder 0 s (1 : ℂ) m) := by
    have hz : (fun m : ℕ => remainder 0 s (1 : ℂ) m) = 0 := by
      funext m
      rw [remainder, taylorPoly_at_one]
      push_cast
      simp
    rw [hz]
    exact summable_zero
  have hsumAll : ∀ a ∈ Metric.ball (1 : ℂ) (1 / 2 : ℝ),
      HasDerivAt (fun w : ℂ => ∑' m : ℕ, remainder 0 s w m)
        (∑' m : ℕ, -s * ((m : ℂ) + a) ^ (-(s + 1))) a := by
    intro a ha
    exact hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
      (convex_ball (1 : ℂ) (1 / 2 : ℝ)).isPreconnected hterm hbound
      (Metric.mem_ball_self (by norm_num)) hsum0 ha
  have hsum : HasDerivAt (fun a : ℂ => ∑' m : ℕ, remainder 0 s a m)
      (∑' m : ℕ, -s * ((m : ℂ) + 1) ^ (-(s + 1))) 1 :=
    hsumAll 1 (Metric.mem_ball_self (by norm_num))
  have hs1 : 1 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hderiv : (∑' m : ℕ, -s * ((m : ℂ) + 1) ^ (-(s + 1))) =
      -s * riemannZeta (s + 1) := by
    rw [tsum_mul_left]
    congr 1
    simpa only [Nat.cast_add, Nat.cast_one] using
      base_tsum_eq_riemannZeta hs1
  rw [hderiv] at hsum
  have heq : continuedAt 0 s =
      fun a : ℂ => (∑' m : ℕ, remainder 0 s a m) + riemannZeta s := by
    funext a
    rw [continuedAt, restoration_zero]
  have hcontinued : continuedHzeta s = continuedAt 0 s := by
    funext a
    rw [continuedHzeta, regularizationOrder_eq_zero hs]
  have han0 : AnalyticAt ℂ (continuedAt 0 s) 1 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))] with a ha
    rw [heq]
    exact ((hsumAll a ha).add_const (riemannZeta s)).differentiableAt
  constructor
  · rw [hcontinued]
    exact han0
  · rw [hcontinued, heq]
    exact hsum.add_const (riemannZeta s)

/-- Analyticity of the canonical continued Hurwitz function at its reference shift. -/
theorem continuedHzeta_analyticAt_one {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (continuedHzeta s) 1 :=
  (continuedHzeta_analyticAt_one_and_hasDerivAt hs).1

/-- Exact first shift derivative at the canonical reference shift. -/
theorem continuedHzeta_hasDerivAt_one {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (continuedHzeta s) (-s * riemannZeta (s + 1)) 1 :=
  (continuedHzeta_analyticAt_one_and_hasDerivAt hs).2

/-- A positive-real exponent avoids every root of every ascending Pochhammer coefficient. -/
theorem ascPochhammer_eval_ne_zero_of_pos_re (r : ℕ) {s : ℂ} (hs : 0 < s.re) :
    (ascPochhammer ℂ r).eval s ≠ 0 := by
  rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
  push Not
  intro j _ heq
  have hre := congrArg Complex.re heq
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

/-- **All-order canonical-anchor ladder.**  The upper-half-plane Hurwitz differential ladder
extends through `a = 1` for every exponent with positive real part. -/
theorem continuedHzeta_iteratedDeriv_at_one (r : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv r (continuedHzeta s) 1 =
      (-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s * riemannZeta (s + r) := by
  have hjet : AnalyticAt ℂ (iteratedDeriv r (continuedHzeta s)) 1 := by
    induction r with
    | zero => simpa [iteratedDeriv_zero] using continuedHzeta_analyticAt_one hs
    | succ r ih =>
        rw [iteratedDeriv_succ]
        exact ih.deriv
  have hshift : 0 < (s + (r : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    positivity
  have hrhs : AnalyticAt ℂ
      (fun a => (-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s *
        continuedHzeta (s + r) a) 1 :=
    (analyticAt_const : AnalyticAt ℂ
      (fun _ : ℂ => (-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s) 1).mul
        (continuedHzeta_analyticAt_one hshift)
  have hclosure : (1 : ℂ) ∈ closure UHP := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨1 + (ε / 2 : ℝ) * Complex.I, ?_, ?_⟩
    · simp only [UHP, Set.mem_setOf_eq, Complex.add_im, Complex.one_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
        Complex.I_re, mul_zero, zero_add]
      positivity
    · rw [dist_comm, dist_eq_norm]
      simp [Real.norm_eq_abs, abs_of_pos hε]
      linarith
  letI : (𝓝[UHP] (1 : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have heq : iteratedDeriv r (continuedHzeta s) =ᶠ[𝓝[UHP] (1 : ℂ)]
      (fun a => (-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s *
        continuedHzeta (s + r) a) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact continuedHzeta_iteratedDeriv r ha
  have hliml : Tendsto (iteratedDeriv r (continuedHzeta s)) (𝓝[UHP] (1 : ℂ))
      (𝓝 (iteratedDeriv r (continuedHzeta s) 1)) :=
    hjet.continuousAt.mono_left inf_le_left
  have hlimr : Tendsto
      (fun a => (-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s *
        continuedHzeta (s + r) a)
      (𝓝[UHP] (1 : ℂ))
      (𝓝 ((-1 : ℂ) ^ r * (ascPochhammer ℂ r).eval s *
        continuedHzeta (s + r) 1)) :=
    hrhs.continuousAt.mono_left inf_le_left
  have hvalue := tendsto_nhds_unique_of_eventuallyEq hliml hlimr heq
  simpa only [continuedHzeta_at_one] using hvalue

/-- Every positive-order anchor jet is nonzero for every positive-real exponent. -/
theorem continuedHzeta_iteratedDeriv_at_one_ne_zero {r : ℕ} (hr : 0 < r)
    {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv r (continuedHzeta s) 1 ≠ 0 := by
  rw [continuedHzeta_iteratedDeriv_at_one r hs]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (ascPochhammer_eval_ne_zero_of_pos_re r hs)) ?_
  apply riemannZeta_ne_zero_of_one_lt_re
  rw [Complex.add_re, Complex.natCast_re]
  exact lt_add_of_pos_of_le hs (by exact_mod_cast hr)

end HurwitzZetaContinuation
