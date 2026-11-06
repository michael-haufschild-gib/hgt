import GaloisForLFunctions.RHTower.XiCosineShiftLaguerreVinogradovKorobov
import GaloisForLFunctions.RHTower.XiLaguerreZeroSumIdentity

/-!
# Strict Laguerre positivity in the Vinogradov–Korobov window

The actual cosine producer has strictly positive first Laguerre expression above the
Vinogradov–Korobov depth boundary. Nearby Xi zeros lie below the shift; distant zeros
cannot obstruct the local diagonal cone. The inverse-square divisor expansion gives
strict positivity off the producer zeros, and the defect-trace law gives simplicity
at its zeros.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.EntireZeroDivisor
open _root_.RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

private def mittagTerm (f : ℂ → ℂ) (q : ZeroCopy f) (w : ℂ) : ℂ :=
  (w - zeroCopyPoint f q)⁻¹ + (zeroCopyPoint f q)⁻¹

private theorem mittagTerm_eq {f : ℂ → ℂ} (q : ZeroCopy f)
    (ha : zeroCopyPoint f q ≠ 0) {w : ℂ} (hw : w ≠ zeroCopyPoint f q) :
    mittagTerm f q w = w / (zeroCopyPoint f q * (w - zeroCopyPoint f q)) := by
  unfold mittagTerm
  have hwa := sub_ne_zero.mpr hw
  field_simp [ha, hwa]
  ring

private theorem hasDerivAt_mittagTerm {f : ℂ → ℂ} (q : ZeroCopy f)
    {w : ℂ} (hw : w ≠ zeroCopyPoint f q) :
    HasDerivAt (mittagTerm f q) (-((w - zeroCopyPoint f q) ^ 2)⁻¹) w := by
  have hd : HasDerivAt (fun u : ℂ => u - zeroCopyPoint f q) 1 w :=
    (hasDerivAt_id w).sub_const _
  have hi := (hd.inv (sub_ne_zero.mpr hw)).add_const (zeroCopyPoint f q)⁻¹
  have he : -(1 : ℂ) / (w - zeroCopyPoint f q) ^ 2 =
      -((w - zeroCopyPoint f q) ^ 2)⁻¹ := by rw [neg_div, one_div]
  rw [he] at hi
  exact hi

/-- Differentiating the locally normally convergent genus-one partial fraction. -/
private theorem hasSum_neg_inv_sq {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {z : ℂ} (hz : f z ≠ 0) :
    HasSum (fun q : ZeroCopy f => -((z - zeroCopyPoint f q) ^ 2)⁻¹)
      (deriv (logDeriv f) z) := by
  classical
  have hane := zeroCopyPoint_ne_zero hf hf0
  have hbase := OrderOneHadamard.summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hpoint := DeBruijn.apply_zeroCopyPoint hf
  have hneq : ∀ {w : ℂ}, f w ≠ 0 → ∀ q : ZeroCopy f, w ≠ zeroCopyPoint f q :=
    fun hw q heq => hw (heq ▸ hpoint q)
  have hlog : ∀ {w : ℂ}, f w ≠ 0 → logDeriv f w = ∑' q, mittagTerm f q w := by
    intro w hw
    rw [logDeriv_eq_tsum_of_even hC hf hf0 heven hbound hw]
    apply tsum_congr
    intro q
    rw [mittagTerm_eq q (hane q) (hneq hw q)]
    have he : zeroCopyPoint f q - w = -(w - zeroCopyPoint f q) := by ring
    rw [he, mul_neg, div_neg, neg_div, neg_neg]
  -- A zero-free disc gives uniform bounds for the finitely many nearby poles.
  have hfd : Differentiable ℂ f := fun w => (hf w (mem_univ w)).differentiableAt
  have hUopen : IsOpen {w : ℂ | f w ≠ 0} :=
    isOpen_ne_fun hfd.continuous continuous_const
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hUopen z hz
  set R : ℝ := ‖z‖ + d / 2 with hRdef
  have hRpos : 0 < R := by positivity
  have hd2 : 0 < d / 2 := by positivity
  -- every spectral point is at distance at least `d` from `z`
  have hfar : ∀ q : ZeroCopy f, d ≤ ‖z - zeroCopyPoint f q‖ := by
    intro q
    by_contra hlt
    push Not at hlt
    have hmem : zeroCopyPoint f q ∈ ball z d := by
      rw [mem_ball, dist_eq_norm, norm_sub_rev]
      exact hlt
    exact hball hmem (hpoint q)
  -- the finitely many small spectral points
  have hcof : ∀ᶠ q in cofinite, 2 * R ≤ ‖zeroCopyPoint f q‖ :=
    eventually_norm_ge_of_summable_inv_sq hane
      hbase (by positivity)
  have hfin : {q : ZeroCopy f | ‖zeroCopyPoint f q‖ < 2 * R}.Finite := by
    have := Filter.eventually_cofinite.mp hcof
    exact this.subset fun q hq => by
      simp only [Set.mem_setOf_eq] at hq ⊢
      exact not_le.mpr hq
  -- the summable majorant
  set u : ZeroCopy f → ℝ := fun q =>
    2 * R * (1 / ‖zeroCopyPoint f q‖ ^ (2 : ℕ))
      + (if ‖zeroCopyPoint f q‖ < 2 * R then 2 * R / (d / 2 * ‖zeroCopyPoint f q‖) else 0)
    with hudef
  have hu : Summable u := by
    refine (hbase.mul_left (2 * R)).add ?_
    refine summable_of_ne_finset_zero (s := hfin.toFinset) fun q hq => ?_
    have hq' : ¬ ‖zeroCopyPoint f q‖ < 2 * R := by
      intro h
      exact hq (hfin.mem_toFinset.mpr h)
    simp [hq']
  -- every point of the disc of radius `d/2` is at distance at least `d/2` from every spectral point
  have hdist : ∀ q : ZeroCopy f, ∀ w ∈ ball z (d / 2), d / 2 ≤ ‖w - zeroCopyPoint f q‖ := by
    intro q w hw
    have hwz : ‖w - z‖ < d / 2 := by
      rw [mem_ball, dist_eq_norm] at hw
      exact hw
    have h1 := hfar q
    have h2 := norm_sub_le_norm_sub_add_norm_sub z w (zeroCopyPoint f q)
    rw [norm_sub_rev z w] at h2
    linarith
  -- the bound on the disc of radius `d/2`
  have hbound : ∀ q : ZeroCopy f, ∀ w ∈ ball z (d / 2), ‖mittagTerm f q w‖ ≤ u q := by
    intro q w hw
    have hwz : ‖w - z‖ < d / 2 := by
      rw [mem_ball, dist_eq_norm] at hw
      exact hw
    have hwR : ‖w‖ ≤ R := by
      have := norm_sub_le_norm_sub_add_norm_sub w z 0
      simp only [sub_zero] at this
      rw [hRdef]
      linarith
    have haq : 0 < ‖zeroCopyPoint f q‖ := norm_pos_iff.mpr (hane q)
    have hwq : d / 2 ≤ ‖w - zeroCopyPoint f q‖ := hdist q w hw
    have hwq0 : w ≠ zeroCopyPoint f q := by
      intro h
      rw [h, sub_self, norm_zero] at hwq
      linarith
    have hwqpos : 0 < ‖w - zeroCopyPoint f q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwq0)
    rw [mittagTerm_eq q (hane q) hwq0, norm_div, norm_mul]
    rw [div_le_iff₀ (mul_pos haq hwqpos)]
    by_cases hsmall : ‖zeroCopyPoint f q‖ < 2 * R
    · -- small spectral point: use the disc distance
      have hu' : u q = 2 * R * (1 / ‖zeroCopyPoint f q‖ ^ (2 : ℕ))
          + 2 * R / (d / 2 * ‖zeroCopyPoint f q‖) := by simp [hudef, hsmall]
      rw [hu']
      have hA : 0 ≤ 2 * R * (1 / ‖zeroCopyPoint f q‖ ^ (2 : ℕ)) * (‖zeroCopyPoint f q‖ * ‖w - zeroCopyPoint f q‖) := by
        positivity
      have hB : ‖w‖ ≤ 2 * R / (d / 2 * ‖zeroCopyPoint f q‖) * (‖zeroCopyPoint f q‖ * ‖w - zeroCopyPoint f q‖) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        calc ‖w‖ * (d / 2 * ‖zeroCopyPoint f q‖)
            ≤ R * (‖w - zeroCopyPoint f q‖ * ‖zeroCopyPoint f q‖) := by
              have := mul_le_mul hwR hwq (by positivity) hRpos.le
              nlinarith [haq]
          _ = 2 * R * (‖zeroCopyPoint f q‖ * ‖w - zeroCopyPoint f q‖) / 2 := by ring
          _ ≤ 2 * R * (‖zeroCopyPoint f q‖ * ‖w - zeroCopyPoint f q‖) := by
              have : 0 ≤ 2 * R * (‖zeroCopyPoint f q‖ * ‖w - zeroCopyPoint f q‖) := by positivity
              linarith
      nlinarith [hA, hB]
    · -- large spectral point: `‖w − a‖ ≥ ‖a‖ / 2`
      push Not at hsmall
      have hu' : u q = 2 * R * (1 / ‖zeroCopyPoint f q‖ ^ (2 : ℕ)) := by
        have : ¬ ‖zeroCopyPoint f q‖ < 2 * R := not_lt.mpr hsmall
        simp [hudef, this]
      rw [hu']
      have hhalf : ‖zeroCopyPoint f q‖ / 2 ≤ ‖w - zeroCopyPoint f q‖ := by
        have := norm_sub_norm_le (zeroCopyPoint f q) w
        rw [norm_sub_rev] at this
        linarith
      rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      calc ‖w‖ * ‖zeroCopyPoint f q‖ ^ (2 : ℕ)
          ≤ R * ‖zeroCopyPoint f q‖ ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_right hwR (by positivity)
        _ = 2 * R * (‖zeroCopyPoint f q‖ * (‖zeroCopyPoint f q‖ / 2)) := by ring
        _ ≤ 2 * R * (‖zeroCopyPoint f q‖ * ‖w - zeroCopyPoint f q‖) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hhalf haq.le
  -- differentiability of the terms on the disc
  have hdiff : ∀ q : ZeroCopy f, DifferentiableOn ℂ (mittagTerm f q) (ball z (d / 2)) := by
    intro q w hw
    have hwq : w ≠ zeroCopyPoint f q := by
      intro h
      have := hdist q w hw
      rw [h, sub_self, norm_zero] at this
      linarith
    exact (hasDerivAt_mittagTerm q hwq).differentiableAt.differentiableWithinAt
  have hzball : z ∈ ball z (d / 2) := mem_ball_self hd2
  have hsum := hasSum_deriv_of_summable_norm hu hdiff isOpen_ball hbound hzball
  -- identify the derivative of the sum with the derivative of `logDeriv f`
  have hev : logDeriv f =ᶠ[𝓝 z] fun w => ∑' q : ZeroCopy f, mittagTerm f q w := by
    filter_upwards [isOpen_ball.mem_nhds hzball] with w hw
    have hw' : f w ≠ 0 := hball (ball_subset_ball (by linarith) hw)
    exact hlog hw'
  rw [hev.deriv_eq]
  refine hsum.congr_fun fun q => ?_
  exact (hasDerivAt_mittagTerm q (hneq hz q)).deriv.symm

private theorem laguerre_eq_zero_sum {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f univ) (hf0 : f 0 ≠ 0) (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {z : ℂ} (hz : f z ≠ 0) :
    deriv f z ^ 2 - f z * deriv (deriv f) z =
      f z ^ 2 * ∑' q : ZeroCopy f, ((z - zeroCopyPoint f q) ^ 2)⁻¹ := by
  have hs := hasSum_neg_inv_sq hC hf hf0 heven hbound hz
  have he : deriv (logDeriv f) z =
      -∑' q : ZeroCopy f, ((z - zeroCopyPoint f q) ^ 2)⁻¹ := by
    rw [← hs.tsum_eq, tsum_neg]
  have hd := (hf z (mem_univ z)).differentiableAt
  have hdd := (hf z (mem_univ z)).deriv.differentiableAt
  have he' : deriv (logDeriv f) z =
      (deriv (deriv f) z * f z - deriv f z * deriv f z) / f z ^ 2 :=
    deriv_div hdd hd hz
  rw [he'] at he
  have hm := (div_eq_iff (pow_ne_zero 2 hz)).mp he
  linear_combination -hm

/-- The strict diagonal cone gives positive inverse-square summands. -/
private theorem laguerre_pos_off_divisor {h x : ℝ} (hh : 0 < h)
    (hx : foldF h x ≠ 0)
    (hcone : ∀ z : ℂ, cosProducer h z = 0 → z.im ^ 2 < (z.re - x) ^ 2) :
    0 < foldFx h x ^ 2 - foldF h x * foldFxx h x := by
  have hk := DeBruijn.riemannKernel_mul_cosh_superExp h
  obtain ⟨C, hC, hbound⟩ := hk.exists_envelope
  have hE := cosProducer_eq_cosTransform_kernel h
  have han : AnalyticOnNhd ℂ (cosProducer h) univ := by
    rw [hE]
    exact hk.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have hf0 : cosProducer h 0 ≠ 0 := by rw [hE]; exact hk.cosTransform_zero_ne
  have heven : ∀ z, cosProducer h (-z) = cosProducer h z := by
    rw [hE]; exact hk.cosTransform_neg
  have hbound' := hbound
  rw [← hE] at hbound'
  have hx' : cosProducer h (x : ℂ) ≠ 0 := by
    rw [cosProducer_eq_foldF]; exact_mod_cast hx
  have hs := (hasSum_neg_inv_sq hC han hf0 heven hbound' hx').summable.neg
  have hs' : Summable (fun q : ZeroCopy (cosProducer h) =>
      (((x : ℂ) - zeroCopyPoint (cosProducer h) q) ^ 2)⁻¹) := by
    simpa only [neg_neg] using hs
  have hp : ∀ q : ZeroCopy (cosProducer h),
      0 < ((((x : ℂ) - zeroCopyPoint (cosProducer h) q) ^ 2)⁻¹).re := by
    intro q
    have hz := DeBruijn.apply_zeroCopyPoint han q
    have hc := hcone _ hz
    have hne : (x : ℂ) ≠ zeroCopyPoint (cosProducer h) q :=
      fun he => hx' (he ▸ hz)
    rw [Complex.inv_re]
    apply div_pos
    · simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
        Complex.sub_im, Complex.ofReal_im]
      nlinarith only [hc]
    · exact Complex.normSq_pos.mpr (pow_ne_zero 2 (sub_ne_zero.mpr hne))
  obtain ⟨r, hr⟩ := exists_foldF_eq_zero hh
  have hr' : cosProducer h (r : ℂ) = 0 := by
    rw [cosProducer_eq_foldF, hr, Complex.ofReal_zero]
  obtain ⟨q, -⟩ := DeBruijn.exists_zeroCopy_of_eq_zero han hf0 hr'
  have hpos : 0 < (∑' q : ZeroCopy (cosProducer h),
      (((x : ℂ) - zeroCopyPoint (cosProducer h) q) ^ 2)⁻¹).re := by
    rw [Complex.re_tsum hs']
    exact (Complex.reCLM.summable hs').tsum_pos (fun q => (hp q).le) q (hp q)
  have hid := congrArg Complex.re (laguerre_eq_zero_sum hC han hf0 heven hbound' hx')
  rw [deriv_cosProducer_real, deriv_deriv_cosProducer_real, cosProducer_eq_foldF] at hid
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at hid
  rw [hid]
  exact mul_pos (by positivity) hpos

/-- Near zeros lie below the shift; distant zeros miss both obstruction cones. -/
private theorem laguerre_pos_of_nearby_depth_lt {h x : ℝ} (hh : 0 < h)
    (hnear : ∀ w : ℂ, XiC w = 0 → |x - w.re| < 1 → |w.im| < h) :
    0 < foldFx h x ^ 2 - foldF h x * foldFxx h x := by
  have hsq : ∀ w : ℂ, XiC w = 0 → w.im ^ 2 < 1 / 4 := by
    intro w hw
    have hb := abs_im_lt_half_of_XiC_eq_zero hw
    nlinarith only [sq_abs w.im, abs_nonneg w.im, hb]
  by_cases hx : foldF h x = 0
  · have hc : ∀ w : ℂ, XiC w = 0 → w.im ^ 2 < (x - w.re) ^ 2 + h ^ 2 := by
      intro w hw
      by_cases hd : |x - w.re| < 1
      · have hb := hnear w hw hd
        have hb' : w.im ^ 2 < h ^ 2 := by
          nlinarith only [sq_abs w.im, abs_nonneg w.im, hb, hh]
        nlinarith only [hb', sq_nonneg (x - w.re)]
      · have hd' : 1 ≤ |x - w.re| := le_of_not_gt hd
        have hb := hsq w hw
        nlinarith only [hd', sq_abs (x - w.re), hb, sq_nonneg h]
    have hz : cosProducer h (x : ℂ) = 0 := by
      rw [cosProducer_eq_foldF, hx, Complex.ofReal_zero]
    have hd := deriv_cosineShiftXi_ne_zero_of_local hh hc hz
    change deriv (cosProducer h) x ≠ 0 at hd
    rw [deriv_cosProducer_real] at hd
    have hd' : foldFx h x ≠ 0 := by exact_mod_cast hd
    rw [hx, zero_mul, sub_zero]
    positivity
  · apply laguerre_pos_off_divisor hh hx
    intro z hz
    by_cases hi : z.im = 0
    · have hxz : z.re ≠ x := by
        intro he
        have he' : z = (x : ℂ) := Complex.ext (by simpa using he) (by simpa using hi)
        rw [he', cosProducer_eq_foldF] at hz
        exact hx (by exact_mod_cast hz)
      rw [hi]
      have : z.re - x ≠ 0 := sub_ne_zero.mpr hxz
      simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
        (show 0 < (z.re - x) ^ 2 by positivity)
    obtain ⟨w, hw, hdisk⟩ := DeBruijn.cosineShift_nonreal_zero_mem_defectDisk hh hi hz
    have hfar : 1 ≤ |x - w.re| := by
      by_contra hn
      have hb := hnear w hw (lt_of_not_ge hn)
      have hb' : w.im ^ 2 < h ^ 2 := by
        nlinarith only [sq_abs w.im, abs_nonneg w.im, hb, hh]
      nlinarith only [hdisk, hb', sq_nonneg (w.re - z.re), sq_nonneg z.im]
    have hw2 := hsq w hw
    have hclose : |w.re - z.re| < 1 / 2 := by
      apply abs_lt_of_sq_lt_sq (b := (1 / 2 : ℝ)) _ (by norm_num)
      nlinarith only [hdisk, hw2, sq_nonneg z.im, sq_nonneg h]
    have him : |z.im| < 1 / 2 := by
      apply abs_lt_of_sq_lt_sq (b := (1 / 2 : ℝ)) _ (by norm_num)
      nlinarith only [hdisk, hw2, sq_nonneg (w.re - z.re), sq_nonneg h]
    have hdist : 1 / 2 < |z.re - x| := by
      have ht := abs_sub_abs_le_abs_sub (x - w.re) (z.re - w.re)
      rw [show x - w.re - (z.re - w.re) = x - z.re by ring,
        abs_sub_comm z.re w.re, abs_sub_comm x z.re] at ht
      linarith only [ht, hfar, hclose]
    nlinarith only [him, hdist, abs_nonneg z.im, abs_nonneg (z.re - x),
      sq_abs z.im, sq_abs (z.re - x)]

/-- Strict Laguerre positivity for the actual cosine producer inside the VK boundary. -/
theorem exists_cosineProducer_strict_laguerre_vk :
    ∃ T : ℝ, ∀ h x : ℝ, T ≤ |x| →
      1 / 2 - vkHadamardWidth (|x| + 1) < h →
      0 < foldFx h x ^ 2 - foldF h x * foldFxx h x := by
  obtain ⟨γ, hγ, hdisp⟩ := abs_re_sub_half_le_vinogradovKorobov
  refine ⟨γ + 1, fun h x hx hh => ?_⟩
  have hlarge : Real.exp (Real.exp 1) ≤ |x| + 1 := by linarith only [hγ, hx]
  have hhpos : 0 < h := by
    have hb := vkHadamardWidth_le_quarter hlarge
    linarith only [hb, hh]
  apply laguerre_pos_of_nearby_depth_lt hhpos
  intro w hw hclose
  set ρ : ℂ := 1 / 2 + I * w
  have hρzero : xi ρ = 0 := by
    simpa only [XiC, ρ, mul_comm I w] using hw
  have hρre : ρ.re = 1 / 2 - w.im := by simp [ρ]; ring
  have hρim : ρ.im = w.re := by simp [ρ]
  have him := abs_im_lt_half_of_XiC_eq_zero hw
  have hρpos : 0 < ρ.re := by
    rw [hρre]; linarith only [him, le_abs_self w.im]
  have hρlt : ρ.re < 1 := by
    rw [hρre]; linarith only [him, neg_abs_le w.im]
  have hρone : ρ ≠ 1 := by
    intro he
    rw [he] at hρlt
    norm_num at hρlt
  have hζ := (xi_eq_zero_iff hρpos hρone).mp hρzero
  have hlow : γ ≤ |w.re| := by
    have ht := abs_sub_abs_le_abs_sub x w.re
    linarith only [ht, hx, hclose]
  have hupp : |w.re| ≤ |x| + 1 := by
    have ht := abs_sub_abs_le_abs_sub w.re x
    rw [abs_sub_comm w.re x] at ht
    linarith only [ht, hclose]
  have hd := hdisp ρ hρpos hρlt hζ (by rwa [hρim])
  rw [hρre, hρim, show (1 / 2 - w.im - 1 / 2 : ℝ) = -w.im by ring,
    abs_neg] at hd
  have hm := vkHadamardWidth_anti (hγ.trans hlow) hupp
  linarith only [hd, hm, hh]

/-- `(Im ξ′)² + Re ξ · Re ξ″` is strictly positive in the open VK region. -/
theorem exists_xi_strict_laguerre_vk :
    ∃ T : ℝ, ∀ s : ℂ, T ≤ |s.im| →
      1 - vkHadamardWidth (|s.im| + 1) < s.re →
      0 < (deriv xi s).im ^ 2 + (xi s).re * (deriv (deriv xi) s).re := by
  obtain ⟨T, hT⟩ := exists_cosineProducer_strict_laguerre_vk
  refine ⟨T, fun s hs hσ => ?_⟩
  have hp := hT (s.re - 1 / 2) s.im hs (by linarith only [hσ])
  have he : (((1 / 2 + (s.re - 1 / 2) : ℝ) : ℂ) + (s.im : ℂ) * I) = s := by
    apply Complex.ext <;> simp
  simp only [foldF, foldFx, foldFxx, he] at hp
  nlinarith only [hp]

#print axioms exists_cosineProducer_strict_laguerre_vk
#print axioms exists_xi_strict_laguerre_vk

end

end GaloisForLFunctions.ZeroConfigurationGeometry
