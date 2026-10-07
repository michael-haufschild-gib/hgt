import GaloisForLFunctions.HTGeometry.CubicStripSeparation
import GaloisForLFunctions.RHTower.XiCubicLiftGrowth
import GaloisForLFunctions.RHTower.GlobalParityWall
import GaloisForLFunctions.RHTower.XiStripInverseDecay
import GaloisForLFunctions.RHTower.EMAnnulusSupply

/-!
# The actual Xi source admits no entire cubic lift

Odd Xi zeros select the simple branch of the cubic in both critical-strip tails.
Uniform decay excludes zeros of the double-branch factor in those tails, while
actual Xi growth forces infinitely many such zeros. Their confinement to a
bounded part of the strip gives the contradiction. No zero-simplicity or RH
hypothesis is used.
-/

namespace RHTower
open Complex Set Metric GaloisForLFunctions.HTGeometry

/-- The nonvanishing real exponential mark preserves every actual Xi zero order. -/
theorem xi_exp_marked_analyticOrder (a : ℝ) (z : ℂ) :
    analyticOrderAt (fun w => xi w * Complex.exp (-(a : ℂ) * w)) z =
      analyticOrderAt xi z := by
  have he : AnalyticAt ℂ (fun w : ℂ => Complex.exp (-(a : ℂ) * w)) z := by
    have hd : Differentiable ℂ (fun w : ℂ => Complex.exp (-(a : ℂ) * w)) := by fun_prop
    exact hd.analyticAt z
  have hm := analyticOrderAt_mul (xi_differentiable.analyticAt z) he
  change analyticOrderAt (fun w => xi w * Complex.exp (-(a : ℂ) * w)) z = _ at hm
  rw [hm, he.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _), add_zero]

/-- Uniform decay on the literal critical strip, with the full exponential mark retained. -/
theorem xi_exp_marked_strip_small (a : ℝ) (ha : 0 ≤ a) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → T ≤ |s.im| →
      ‖xi s * Complex.exp (-(a : ℂ) * s)‖ < ε := by
  obtain ⟨U, hU⟩ := exists_forall_norm_XiC_lt (1 / 2) hε
  refine ⟨max U 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro s hs0 hs1 hsT
  let w := (s - 1 / 2) * (-Complex.I)
  have hwre : w.re = s.im := by simp [w]
  have hwim : w.im = 1 / 2 - s.re := by simp [w]
  have hws : XiC w = xi s := by
    unfold XiC
    congr 1
    apply Complex.ext <;> simp [w]
  have hsmall : ‖xi s‖ < ε := by
    rw [← hws]
    exact hU w (by rw [hwim, abs_le]; constructor <;> linarith)
      (by rw [hwre]; exact (le_max_left _ _).trans hsT)
  have he : ‖Complex.exp (-(a : ℂ) * s)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) hs0
  rw [norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) he).trans_lt hsmall

/-- Every odd Xi zero selects the simple cubic branch, regardless of any lift symmetry. -/
theorem xi_cubic_factor_eq_three_at_odd_zero (a : ℝ) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hrel : ∀ z, (f z - 3) * f z ^ 2 = 4 * (xi z * Complex.exp (-(a : ℂ) * z)))
    {z : ℂ} (hz : xi z = 0) (ho : Odd (analyticOrderAt xi z).toNat) : f z = 3 :=
  cubic_simple_branch_of_odd_order (hf.analyticAt z) hrel (by rw [hz, zero_mul])
    (by simpa only [xi_exp_marked_analyticOrder] using ho)

/-- The hypothetical double-branch factor has only finitely many zeros on the actual Xi source. -/
theorem xi_cubic_factor_zeroSet_finite (a : ℝ) (ha : 0 ≤ a) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hrel : ∀ z, (f z - 3) * f z ^ 2 = 4 * (xi z * Complex.exp (-(a : ℂ) * z))) :
    {z : ℂ | f z = 0}.Finite := by
  obtain ⟨T, hT, hsmall⟩ := xi_exp_marked_strip_small a ha (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨t, ht, hz, ho⟩ := exists_odd_order_line_zero_gt T
  have hp : f (linePt t) = 3 := xi_cubic_factor_eq_three_at_odd_zero a hf hrel hz ho
  have hm : f ((starRingEnd ℂ) (linePt t)) = 3 :=
    xi_cubic_factor_eq_three_at_odd_zero a hf hrel
      (by rw [xi_conj, hz, map_zero]) (by rwa [xi_orderAt_conj])
  have hprod (z : ℂ) (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1) (hi : T ≤ |z.im|) :
      ‖(f z - 3) * f z ^ 2‖ < 2 := by
    rw [hrel, norm_mul]
    norm_num only [Complex.norm_ofNat]
    linarith [hsmall z h0 h1 hi]
  have hup : ∀ z ∈ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ T ≤ z.im}, f z ≠ 0 := by
    apply cubic_no_zero_on_small_connected_region
      (by simpa only [one_mul] using isPreconnected_vertical_strip_tail T 1)
      hf.continuous.continuousOn
    · intro z hz
      exact hprod z hz.1 hz.2.1 (hz.2.2.trans (le_abs_self _))
    · exact (show linePt t ∈ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ T ≤ z.im} by
        norm_num [linePt]
        exact ht.le)
    · exact hp
  have hlow : ∀ z ∈ {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ T ≤ -z.im}, f z ≠ 0 := by
    apply cubic_no_zero_on_small_connected_region
      (by simpa only [neg_one_mul] using isPreconnected_vertical_strip_tail T (-1))
      hf.continuous.continuousOn
    · intro z hz
      exact hprod z hz.1 hz.2.1 (hz.2.2.trans (neg_le_abs _))
    · exact (show (starRingEnd ℂ) (linePt t) ∈
          {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ T ≤ -z.im} by
        norm_num [linePt]
        exact ht.le)
    · exact hm
  refine (xi_zeros_finite_ball 0 (T + 2)).subset ?_
  intro z hz
  have hzero : f z = 0 := hz
  have hprod0 : (4 : ℂ) * (xi z * Complex.exp (-(a : ℂ) * z)) = 0 := by
    rw [← hrel, hzero]
    simp
  have hxiz : xi z = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hprod0).resolve_left (by norm_num))).resolve_right
      (Complex.exp_ne_zero _)
  have hr0 := xi_zero_re_pos hxiz
  have hr1 := xi_zero_re_lt_one hxiz
  have him : |z.im| < T := by
    by_contra hi
    have hi' := le_of_not_gt hi
    rcases le_or_gt 0 z.im with hs | hs
    · exact hup z ⟨hr0.le, hr1.le, by rwa [abs_of_nonneg hs] at hi'⟩ hzero
    · exact hlow z ⟨hr0.le, hr1.le, by rwa [abs_of_neg hs] at hi'⟩ hzero
  refine ⟨?_, hxiz⟩
  rw [mem_ball, dist_zero_right]
  have hn := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_pos hr0] at hn
  linarith

/-- No actual nonnegatively tilted Xi source lifts through the fixed cubic. -/
theorem no_entire_xi_cubic_lift (a : ℝ) (ha : 0 ≤ a) :
    ¬ ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ z, (h z ^ 3 - 3 * h z - 2) / 4 = xi z * Complex.exp (-(a : ℂ) * z) := by
  rintro ⟨h, hh, hrel⟩
  let f := fun z => h z + 1
  have hf : Differentiable ℂ f := by dsimp [f]; fun_prop
  have hfactor : ∀ z, (f z - 3) * f z ^ 2 = 4 * (xi z * Complex.exp (-(a : ℂ) * z)) := by
    intro z
    dsimp [f]
    linear_combination 4 * hrel z
  exact (xi_cubic_factor_zeroSet_infinite a hf hfactor)
    (xi_cubic_factor_zeroSet_finite a ha hf hfactor)

/-- The actual integer-marked Xi channels admit no entire cubic lift. -/
theorem no_entire_integer_marked_xi_cubic_lift {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      ∀ z, (h z ^ 3 - 3 * h z - 2) / 4 = xi z * Complex.exp (-z * (Real.log n : ℂ)) := by
  rintro ⟨h, hh, hrel⟩
  apply no_entire_xi_cubic_lift (Real.log n) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  refine ⟨h, hh, fun z => ?_⟩
  rw [hrel]
  congr 2
  ring

end RHTower
