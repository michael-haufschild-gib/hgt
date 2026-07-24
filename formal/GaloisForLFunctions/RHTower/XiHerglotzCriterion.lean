import GaloisForLFunctions.RHTower.XiWeilCriterionConverse
import GaloisForLFunctions.RHTower.XiWardSpectralBudgetSumRule

/-!
# The Herglotz criterion: RH as a sign of one harmonic function

Pairing each divisor copy with its functional-equation reflection cancels the
genus-one regularization exactly, leaving

`logDeriv XiC z = ½ · ∑' q, ((z − pt q)⁻¹ + (z + pt q)⁻¹)`.

Each paired summand has strictly negative imaginary part as soon as `Im z`
exceeds the half-width of the critical strip, because both `Im z ∓ Im pt` are
then positive.  So `−logDeriv XiC` maps `{Im z > 1/2}` into the upper half plane.

A zero off the real axis destroys that sign just below itself: there the simple
pole contributes `Im (m/(z − pt₀)) = m/ε → +∞`.  Hence

**RH ⟺ `Im (logDeriv XiC z) ≤ 0` on the whole upper half plane.**

This replaces the quadratic Weil form by a single harmonic function whose sign is
already known on `Im z > 1/2` and vanishes on the real axis by Schwarz reality —
the residual region is the open half strip, on which the maximum principle applies
to `Im logDeriv XiC` away from its poles.
-/

open Complex Filter Topology Metric

namespace RHTower

noncomputable section

/-! ## §1 The reflection-paired trace -/

/-- Reflection pairs the regularized resolvent terms into a pole pair, cancelling
the centring term. -/
theorem relativeResolventTerm_add_reflect {z : ℂ} (q : XiZeroCopy)
    (hz : XiC z ≠ 0) :
    xiRelativeResolventTerm z q +
        xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q) =
      (z - xiSpectralPoint q)⁻¹ + (z + xiSpectralPoint q)⁻¹ := by
  have hpt : xiSpectralPoint (xiZeroCopyReflectEquiv q) = -xiSpectralPoint q :=
    xiSpectralPoint_reflect q
  have hne : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  have hnez : xiSpectralPoint q ≠ z := by
    intro h
    exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, h⟩)
  have hnez' : -xiSpectralPoint q ≠ z := by
    intro h
    exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr
      ⟨xiZeroCopyReflectEquiv q, by rw [hpt, h]⟩)
  have h1 : xiSpectralPoint q - z ≠ 0 := sub_ne_zero.mpr hnez
  have h2 : -xiSpectralPoint q - z ≠ 0 := sub_ne_zero.mpr hnez'
  have h3 : z - xiSpectralPoint q ≠ 0 := by
    intro h
    exact hnez (by linear_combination -h)
  have h4 : z + xiSpectralPoint q ≠ 0 := by
    intro h
    exact hnez' (by linear_combination -h)
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm, hpt,
    show (-xiSpectralPoint q)⁻¹ = -(xiSpectralPoint q)⁻¹ from by rw [inv_neg],
    show (-xiSpectralPoint q - z) = -(z + xiSpectralPoint q) from by ring,
    show (xiSpectralPoint q - z) = -(z - xiSpectralPoint q) from by ring,
    inv_neg, inv_neg]
  ring

/-- **The paired trace formula.**  Away from the divisor the logarithmic
derivative is the half-sum of the reflection-paired pole pairs; no centring term
survives. -/
theorem logDeriv_XiC_eq_half_tsum_pair {z : ℂ} (hz : XiC z ≠ 0) :
    logDeriv XiC z = (1 / 2 : ℂ) * ∑' q : XiZeroCopy,
      ((z - xiSpectralPoint q)⁻¹ + (z + xiSpectralPoint q)⁻¹) := by
  have hsum := summable_xiRelativeResolventTerm hz
  have hrefl : ∑' q : XiZeroCopy, xiRelativeResolventTerm z q =
      ∑' q : XiZeroCopy,
        xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q) :=
    (xiZeroCopyReflectEquiv.tsum_eq (xiRelativeResolventTerm z)).symm
  have hsum' : Summable fun q : XiZeroCopy =>
      xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q) :=
    (Equiv.summable_iff xiZeroCopyReflectEquiv).mpr hsum
  have hpair : ∑' q : XiZeroCopy,
      ((z - xiSpectralPoint q)⁻¹ + (z + xiSpectralPoint q)⁻¹) =
      2 * xiRelativeResolventTrace z := by
    rw [xiRelativeResolventTrace]
    rw [show (2 : ℂ) * ∑' q : XiZeroCopy, xiRelativeResolventTerm z q =
        (∑' q : XiZeroCopy, xiRelativeResolventTerm z q) +
          ∑' q : XiZeroCopy,
            xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q) from by
      rw [← hrefl]; ring]
    rw [← hsum.tsum_add hsum']
    exact tsum_congr fun q => (relativeResolventTerm_add_reflect q hz).symm
  rw [logDeriv_XiC_eq_relativeResolventTrace hz, hpair]
  ring

/-! ## §2 The sign above the strip -/

/-- Each paired summand has negative imaginary part above the strip. -/
theorem im_pair_neg_of_half_lt_im {z : ℂ} (hz : 1 / 2 < z.im) (q : XiZeroCopy) :
    ((z - xiSpectralPoint q)⁻¹ + (z + xiSpectralPoint q)⁻¹).im < 0 := by
  have hv := abs_lt.mp (abs_im_xiSpectralPoint_lt_half q)
  have hne : xiSpectralPoint q ≠ z := by
    intro h
    rw [← h] at hz
    linarith [hv.2]
  have hne' : -xiSpectralPoint q ≠ z := by
    intro h
    rw [← h] at hz
    simp only [Complex.neg_im] at hz
    linarith [hv.1]
  have h1 : z - xiSpectralPoint q ≠ 0 := by
    intro h
    exact hne (by linear_combination -h)
  have h2 : z + xiSpectralPoint q ≠ 0 := by
    intro h
    exact hne' (by linear_combination -h)
  have hn1 : 0 < Complex.normSq (z - xiSpectralPoint q) :=
    Complex.normSq_pos.mpr h1
  have hn2 : 0 < Complex.normSq (z + xiSpectralPoint q) :=
    Complex.normSq_pos.mpr h2
  rw [Complex.add_im, Complex.inv_im, Complex.inv_im, Complex.sub_im,
    Complex.add_im]
  have hd1 : 0 < (z.im - (xiSpectralPoint q).im) /
      Complex.normSq (z - xiSpectralPoint q) := by
    apply div_pos (by linarith [hv.2]) hn1
  have hd2 : 0 < (z.im + (xiSpectralPoint q).im) /
      Complex.normSq (z + xiSpectralPoint q) := by
    apply div_pos (by linarith [hv.1]) hn2
  have hr1 : -(z.im - (xiSpectralPoint q).im) /
      Complex.normSq (z - xiSpectralPoint q) =
      -((z.im - (xiSpectralPoint q).im) /
        Complex.normSq (z - xiSpectralPoint q)) := by
    rw [neg_div]
  have hr2 : -(z.im + (xiSpectralPoint q).im) /
      Complex.normSq (z + xiSpectralPoint q) =
      -((z.im + (xiSpectralPoint q).im) /
        Complex.normSq (z + xiSpectralPoint q)) := by
    rw [neg_div]
  rw [hr1, hr2]
  linarith

/-- **Anti-Herglotz above the strip.**  Unconditionally,
`Im (logDeriv XiC) ≤ 0` on `{Im z > 1/2}`: the strip confinement of the divisor
is exactly the statement that `−logDeriv XiC` is a Herglotz function there. -/
theorem im_logDeriv_XiC_nonpos_of_half_lt_im {z : ℂ} (hz : 1 / 2 < z.im) :
    (logDeriv XiC z).im ≤ 0 := by
  have hXz : XiC z ≠ 0 := by
    intro h
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp h
    have hv := abs_lt.mp (abs_im_xiSpectralPoint_lt_half q)
    rw [← hq] at hz
    linarith [hv.2]
  have hsum : Summable fun q : XiZeroCopy =>
      (z - xiSpectralPoint q)⁻¹ + (z + xiSpectralPoint q)⁻¹ := by
    have hs := summable_xiRelativeResolventTerm hXz
    have hs' : Summable fun q : XiZeroCopy =>
        xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q) :=
      (Equiv.summable_iff xiZeroCopyReflectEquiv).mpr hs
    apply (hs.add hs').congr
    intro q
    exact relativeResolventTerm_add_reflect q hXz
  rw [logDeriv_XiC_eq_half_tsum_pair hXz]
  rw [Complex.mul_im]
  have hre : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have him : ((1 : ℂ) / 2).im = 0 := by norm_num
  rw [hre, him, zero_mul, add_zero]
  have htsum : (∑' q : XiZeroCopy,
      ((z - xiSpectralPoint q)⁻¹ + (z + xiSpectralPoint q)⁻¹)).im ≤ 0 := by
    rw [Complex.im_tsum hsum]
    apply tsum_nonpos
    intro q
    exact le_of_lt (im_pair_neg_of_half_lt_im hz q)
  nlinarith [htsum]

/-! ## §3 The criterion -/

/-- **Under RH the sign holds on the whole upper half plane.** -/
theorem im_logDeriv_XiC_nonpos_of_rh (hRH : RiemannHypothesis) {z : ℂ}
    (hz : 0 < z.im) (hXz : XiC z ≠ 0) :
    (logDeriv XiC z).im ≤ 0 := by
  have hsum : Summable fun q : XiZeroCopy =>
      (z - xiSpectralPoint q)⁻¹ + (z + xiSpectralPoint q)⁻¹ := by
    have hs := summable_xiRelativeResolventTerm hXz
    have hs' : Summable fun q : XiZeroCopy =>
        xiRelativeResolventTerm z (xiZeroCopyReflectEquiv q) :=
      (Equiv.summable_iff xiZeroCopyReflectEquiv).mpr hs
    apply (hs.add hs').congr
    intro q
    exact relativeResolventTerm_add_reflect q hXz
  rw [logDeriv_XiC_eq_half_tsum_pair hXz, Complex.mul_im]
  have hre : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have him : ((1 : ℂ) / 2).im = 0 := by norm_num
  rw [hre, him, zero_mul, add_zero]
  have htsum : (∑' q : XiZeroCopy,
      ((z - xiSpectralPoint q)⁻¹ + (z + xiSpectralPoint q)⁻¹)).im ≤ 0 := by
    rw [Complex.im_tsum hsum]
    apply tsum_nonpos
    intro q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    have h1 : z - (t : ℂ) ≠ 0 := by
      intro h
      have him0 := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero,
        Complex.zero_im] at him0
      linarith
    have h2 : z + (t : ℂ) ≠ 0 := by
      intro h
      have him0 := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, add_zero,
        Complex.zero_im] at him0
      linarith
    have hn1 : 0 < Complex.normSq (z - (t : ℂ)) := Complex.normSq_pos.mpr h1
    have hn2 : 0 < Complex.normSq (z + (t : ℂ)) := Complex.normSq_pos.mpr h2
    have hq1 : 0 < z.im / Complex.normSq (z - (t : ℂ)) := div_pos hz hn1
    have hq2 : 0 < z.im / Complex.normSq (z + (t : ℂ)) := div_pos hz hn2
    rw [Complex.add_im, Complex.inv_im, Complex.inv_im, Complex.sub_im,
      Complex.add_im, ht]
    simp only [Complex.ofReal_im, sub_zero, add_zero, neg_div]
    linarith
  nlinarith [htsum]

/-- **The pole drives the imaginary part above any level.**  An off-critical
zero of `ξ` produces points arbitrarily close below its conjugate copy at which
`Im (logDeriv XiC)` exceeds any prescribed bound, while staying inside the open
upper half strip. -/
theorem exists_im_logDeriv_gt_of_rightHalf_zero {s : ℂ} (hs : s ∈ rightHalf)
    (hzero : xi s = 0) (C : ℝ) :
    ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧ XiC z ≠ 0 ∧
      C < (logDeriv XiC z).im := by
  -- the centred coordinate of the off-critical zero
  set pt₁ : ℂ := -Complex.I * (s - 1 / 2) with hpt
  have hre : 1 / 2 < s.re := hs
  have hXpt : XiC pt₁ = 0 := by
    show xi ((1 / 2 : ℂ) + pt₁ * Complex.I) = 0
    have harg : (1 / 2 : ℂ) + pt₁ * Complex.I = s := by
      rw [hpt,
        show (-Complex.I * (s - 1 / 2) * Complex.I) =
          -(Complex.I * Complex.I) * (s - 1 / 2) from by ring,
        Complex.I_mul_I]
      ring
    rw [harg]
    exact hzero
  have hptim : pt₁.im < 0 := by
    have hval : pt₁.im = -(s.re - 1 / 2) := by
      rw [hpt]
      simp [Complex.mul_im, Complex.sub_re]
    rw [hval]
    linarith
  -- pass to the conjugate copy, which lies in the upper half plane
  set pt₀ : ℂ := (starRingEnd ℂ) pt₁ with hpt₀
  have hX0 : XiC pt₀ = 0 := by
    rw [hpt₀, XiC_conj', hXpt, map_zero]
  have him : 0 < pt₀.im := by
    rw [hpt₀]
    simpa using hptim
  obtain ⟨R, hR, g, hgan, hg0, hfact⟩ := XiC_peel_ball pt₀
  set m := (analyticOrderAt XiC pt₀).toNat with hm
  have hmpos : 0 < m := XiC_order_toNat_pos hX0
  -- approach `pt₀` from directly below
  have hlogg : ContinuousAt (logDeriv g) pt₀ := by
    have hd1 : ContinuousAt (deriv g) pt₀ :=
      ((hgan pt₀ (mem_ball_self hR)).deriv).continuousAt
    have hd2 : ContinuousAt g pt₀ := (hgan pt₀ (mem_ball_self hR)).continuousAt
    unfold logDeriv
    exact ContinuousAt.div hd1 hd2 (hg0 pt₀ (mem_ball_self hR))
  set ray : ℝ → ℂ := fun t => pt₀ - (t : ℂ) * Complex.I with hray
  have hraycont : Continuous ray := by fun_prop
  have hrayt : Tendsto ray (𝓝[>] 0) (𝓝 pt₀) := by
    have h := (hraycont.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have h0 : ray 0 = pt₀ := by simp [hray]
    rwa [h0] at h
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < R := by
    have hc : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    exact hc.eventually (eventually_lt_nhds hR)
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < (ray t).im := by
    have hc : Tendsto (fun t : ℝ => (ray t).im) (𝓝[>] 0) (𝓝 pt₀.im) :=
      (Complex.continuous_im.tendsto pt₀).comp hrayt
    exact hc.eventually (eventually_gt_nhds him)
  have hball : ∀ᶠ t : ℝ in 𝓝[>] 0, ray t ∈ ball pt₀ R := by
    filter_upwards [hpos, hsmall] with t ht htR
    rw [mem_ball, dist_eq_norm, hray]
    simp only [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    exact htR
  have hnept : ∀ᶠ t : ℝ in 𝓝[>] 0, ray t ≠ pt₀ := by
    filter_upwards [hpos] with t ht
    rw [hray]
    intro hcon
    have : ((t : ℂ)) * Complex.I = 0 := by linear_combination -hcon
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by exact_mod_cast h : (t : ℝ) = 0) ht.ne'
    · exact Complex.I_ne_zero h
  have hXne : ∀ᶠ t : ℝ in 𝓝[>] 0, XiC (ray t) ≠ 0 := by
    filter_upwards [hball, hnept] with t htb htne
    rw [hfact (ray t) htb]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr htne)) (hg0 _ htb)
  -- the pole drives the imaginary part positive
  have hform : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (logDeriv XiC (ray t)).im = (m : ℝ) / t + (logDeriv g (ray t)).im := by
    filter_upwards [hpos, hball, hnept] with t ht htb htne
    rw [logDeriv_XiC_eq_pole_add hgan hg0 hfact htb htne, Complex.add_im]
    congr 1
    have hsub : ray t - pt₀ = -((t : ℂ) * Complex.I) := by
      rw [hray]; ring
    rw [hsub]
    have htC : ((t : ℂ)) ≠ 0 := by exact_mod_cast ht.ne'
    have hval : ((m : ℂ)) / (-((t : ℂ) * Complex.I)) =
        ((m : ℂ) / (t : ℂ)) * Complex.I := by
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hval, Complex.mul_im]
    simp only [Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    have htne : (t : ℝ) ≠ 0 := ht.ne'
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
    field_simp
  have hlim : Tendsto (fun t : ℝ => (m : ℝ) / t + (logDeriv g (ray t)).im)
      (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun t : ℝ => (m : ℝ) / t) (𝓝[>] 0) atTop := by
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
      have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hm0
      apply this.congr
      intro t
      rw [div_eq_mul_inv]
    have h2 : Tendsto (fun t : ℝ => (logDeriv g (ray t)).im) (𝓝[>] 0)
        (𝓝 (logDeriv g pt₀).im) :=
      (Complex.continuous_im.tendsto _).comp (hlogg.tendsto.comp hrayt)
    exact h1.atTop_add h2
  have hb : pt₀.im < 1 / 2 := by
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy pt₀).mp hX0
    have hv := abs_lt.mp (abs_im_xiSpectralPoint_lt_half q)
    rw [hq] at hv
    exact hv.2
  have hlow : ∀ᶠ t : ℝ in 𝓝[>] 0, (ray t).im < 1 / 2 := by
    have hc : Tendsto (fun t : ℝ => (ray t).im) (𝓝[>] 0) (𝓝 pt₀.im) :=
      (Complex.continuous_im.tendsto pt₀).comp hrayt
    exact hc.eventually (eventually_lt_nhds hb)
  obtain ⟨t, hft, hbt, hXt, hut, hlt⟩ :=
    (hform.and ((hlim.eventually (eventually_gt_atTop C)).and
      (hXne.and (hupper.and hlow)))).exists
  exact ⟨ray t, hut, hlt, hXt, by rw [hft]; exact hbt⟩


/-- **The Herglotz criterion.**  If `Im (logDeriv XiC)` is nonpositive on the
upper half plane, the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_im_logDeriv_nonpos
    (hsign : ∀ z : ℂ, 0 < z.im → XiC z ≠ 0 → (logDeriv XiC z).im ≤ 0) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hzero
  obtain ⟨z, hzim, -, hXz, hgt⟩ :=
    exists_im_logDeriv_gt_of_rightHalf_zero hs hzero 0
  linarith [hsign z hzim hXz]

/-- **The boundedness criterion.**  If `Im (logDeriv XiC)` is bounded above by
any constant on the open upper half strip, then the Riemann Hypothesis holds.
Only a pole — an off-critical zero — can violate a one-sided bound there, so RH
is equivalent to local boundedness above of a single harmonic function on a
strip whose two boundary behaviours are already certified. -/
theorem riemannHypothesis_of_im_logDeriv_bddAbove {C : ℝ}
    (hbd : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → XiC z ≠ 0 →
      (logDeriv XiC z).im ≤ C) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hzero
  obtain ⟨z, hzim, hzhalf, hXz, hgt⟩ :=
    exists_im_logDeriv_gt_of_rightHalf_zero hs hzero C
  linarith [hbd z hzim hzhalf hXz]

end

end RHTower
