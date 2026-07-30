import GaloisForLFunctions.RHTower.XiWeilResolventGram
import GaloisForLFunctions.RHTower.Peeling

/-!
# Rank-one detection of an off-critical zero by the Weil form

An off-critical zero makes the Weil form on the resolvent test algebra indefinite,
and a single base point already witnesses it.

Writing `A z = conj z / (z (z − conj z))`, Schwarz reality of the centered completed
zeta turns the diagonal Weil value into the real expression

`Q z = M₁ − 2 Re (A z · logDeriv XiC z)`,

with `M₁` the second inverse moment of the divisor.  Near a zero `pt₀` off the real
axis the logarithmic derivative has a simple pole of positive integer residue while
`A` stays finite and nonzero — the two poles of the conjugate pair are at distinct
points precisely because the zero is off the line.  Approaching `pt₀` along the ray
`pt₀ + t·A pt₀·m` therefore drives `Q` to `−∞`.
-/

open Complex Filter Topology Metric

namespace RHTower

noncomputable section

/-! ## §1 Local pole structure of `logDeriv XiC` -/

/-- Around any point the centered completed zeta peels on a small ball with a
nonvanishing analytic cofactor. -/
theorem XiC_peel_ball (pt₀ : ℂ) :
    ∃ R > 0, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball pt₀ R) ∧
      (∀ z ∈ ball pt₀ R, g z ≠ 0) ∧
      ∀ z ∈ ball pt₀ R,
        XiC z = (z - pt₀) ^ (analyticOrderAt XiC pt₀).toNat * g z := by
  have hm : analyticOrderAt XiC pt₀ =
      ((analyticOrderAt XiC pt₀).toNat : ℕ∞) :=
    (ENat.coe_toNat (XiC_order_ne_top pt₀)).symm
  obtain ⟨g, hgan, hg0, hfact, -⟩ :=
    exists_peel isOpen_univ XiC_analytic (Set.mem_univ pt₀) hm
  have hcont : ContinuousAt g pt₀ := (hgan pt₀ (Set.mem_univ pt₀)).continuousAt
  have hev : ∀ᶠ z in nhds pt₀, g z ≠ 0 := hcont.eventually_ne hg0
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨R, hR, g, fun z _ => hgan z (Set.mem_univ z), ?_, ?_⟩
  · intro z hz
    exact hball (by rwa [mem_ball] at hz)
  · intro z _
    exact hfact z (Set.mem_univ z)

/-- The vanishing order at a zero is positive. -/
theorem XiC_order_toNat_pos {pt₀ : ℂ} (h0 : XiC pt₀ = 0) :
    0 < (analyticOrderAt XiC pt₀).toNat := by
  obtain ⟨R, hR, g, hgan, hg0, hfact⟩ := XiC_peel_ball pt₀
  by_contra hcon
  push Not at hcon
  have hzero : (analyticOrderAt XiC pt₀).toNat = 0 := by omega
  have hval := hfact pt₀ (mem_ball_self hR)
  rw [hzero, pow_zero, one_mul] at hval
  exact hg0 pt₀ (mem_ball_self hR) (by rw [← hval, h0])

/-- **Pole splitting.**  On a punctured ball around a zero the logarithmic
derivative is the simple pole of residue the vanishing order plus an analytic
remainder. -/
theorem logDeriv_XiC_eq_pole_add {pt₀ : ℂ} {R : ℝ} {g : ℂ → ℂ}
    (hgan : AnalyticOnNhd ℂ g (ball pt₀ R))
    (hg0 : ∀ z ∈ ball pt₀ R, g z ≠ 0)
    (hfact : ∀ z ∈ ball pt₀ R,
      XiC z = (z - pt₀) ^ (analyticOrderAt XiC pt₀).toNat * g z)
    {z : ℂ} (hz : z ∈ ball pt₀ R) (hzne : z ≠ pt₀) :
    logDeriv XiC z =
      ((analyticOrderAt XiC pt₀).toNat : ℂ) / (z - pt₀) + logDeriv g z := by
  set m := (analyticOrderAt XiC pt₀).toNat with hm
  have hsub : z - pt₀ ≠ 0 := sub_ne_zero.mpr hzne
  have hpow : (z - pt₀) ^ m ≠ 0 := pow_ne_zero _ hsub
  have hgz : g z ≠ 0 := hg0 z hz
  have hopen : IsOpen (ball pt₀ R) := isOpen_ball
  have hev : XiC =ᶠ[nhds z]
      fun w : ℂ => (w - pt₀) ^ m * g w :=
    Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw => hfact w hw
  have hdpow : DifferentiableAt ℂ (fun w : ℂ => (w - pt₀) ^ m) z := by
    fun_prop
  have hdg : DifferentiableAt ℂ g z :=
    (hgan z hz).differentiableAt
  have hlog : logDeriv XiC z =
      logDeriv (fun w : ℂ => (w - pt₀) ^ m * g w) z := by
    rw [logDeriv, logDeriv, Pi.div_apply, Pi.div_apply, hev.deriv_eq,
      hfact z hz]
  rw [hlog, logDeriv_mul z hpow hgz hdpow hdg]
  congr 1
  have hderiv : HasDerivAt (fun w : ℂ => (w - pt₀) ^ m)
      ((m : ℂ) * (z - pt₀) ^ (m - 1)) z := by
    have h := ((hasDerivAt_id z).sub_const pt₀).pow m
    simpa using! h
  rw [logDeriv, Pi.div_apply, hderiv.deriv]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · simp [hm0]
  · rw [div_eq_div_iff hpow hsub]
    have hsplit : (z - pt₀) ^ m = (z - pt₀) ^ (m - 1) * (z - pt₀) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hsplit]
    ring

/-! ## §2 The diagonal Weil value as a real expression -/

/-- Schwarz reality of the logarithmic derivative in the centered coordinate.
The divisor is invariant under conjugation of the centered coordinate, so
reindexing the relative resolvent trace along that involution conjugates it. -/
theorem logDeriv_XiC_conj {z : ℂ} (hz : XiC z ≠ 0) :
    logDeriv XiC ((starRingEnd ℂ) z) = (starRingEnd ℂ) (logDeriv XiC z) := by
  have hzc : XiC ((starRingEnd ℂ) z) ≠ 0 := XiC_ne_zero_conj hz
  rw [logDeriv_XiC_eq_relativeResolventTrace hz,
    logDeriv_XiC_eq_relativeResolventTrace hzc, xiRelativeResolventTrace,
    xiRelativeResolventTrace, Complex.conj_tsum]
  rw [← (xiZeroCopyLineConjEquiv).tsum_eq
    (fun q => xiRelativeResolventTerm ((starRingEnd ℂ) z) q)]
  refine tsum_congr fun q => ?_
  rw [xiRelativeResolventTerm, xiRelativeResolventTerm,
    xiSpectralPoint_lineConj]
  rw [map_sub, map_inv₀, map_inv₀, map_sub]

/-- The coefficient carried by the diagonal Weil value. -/
def xiWeilDiagonalCoeff (z : ℂ) : ℂ :=
  (starRingEnd ℂ) z / (z * (z - (starRingEnd ℂ) z))

theorem xiWeilDiagonalCoeff_conj (z : ℂ) :
    (starRingEnd ℂ) (xiWeilDiagonalCoeff z) =
      -(z / ((starRingEnd ℂ) z * (z - (starRingEnd ℂ) z))) := by
  unfold xiWeilDiagonalCoeff
  rw [map_div₀, map_mul, map_sub, Complex.conj_conj,
    show ((starRingEnd ℂ) z - z) = -(z - (starRingEnd ℂ) z) from by ring,
    mul_neg, div_neg]

/-- **The diagonal Weil value is real and explicit**: the second inverse moment
minus twice the real part of one coefficient-weighted resolvent value. -/
theorem xiWeilPolarization_diagonal_eq_sub_two_re {z : ℂ} (hz : XiC z ≠ 0)
    (hz0 : z ≠ 0) (him : z.im ≠ 0) :
    xiWeilPolarization (xiCauchyRegularizedKernel z)
        (xiCauchyRegularizedKernel z) =
      xiSecondInverseMoment -
        2 * (((xiWeilDiagonalCoeff z * logDeriv XiC z).re : ℝ) : ℂ) := by
  have hbase := xiWeilPolarization_cauchyKernel_diagonal hz hz0 him
  have hA : (starRingEnd ℂ) z / (z * (z - (starRingEnd ℂ) z)) =
      xiWeilDiagonalCoeff z := rfl
  have hcoeff : (z / ((starRingEnd ℂ) z * (z - (starRingEnd ℂ) z))) =
      -((starRingEnd ℂ) (xiWeilDiagonalCoeff z)) := by
    rw [xiWeilDiagonalCoeff_conj, neg_neg]
  rw [hbase, hA, hcoeff, logDeriv_XiC_conj hz]
  set A := xiWeilDiagonalCoeff z with hAdef
  set L := logDeriv XiC z with hLdef
  have hsum : A * L + (starRingEnd ℂ) A * (starRingEnd ℂ) L =
      ((2 * (A * L).re : ℝ) : ℂ) := by
    rw [← map_mul, Complex.add_conj]
  have hre : xiSecondInverseMoment - A * L +
      -(starRingEnd ℂ) A * (starRingEnd ℂ) L =
      xiSecondInverseMoment -
        (A * L + (starRingEnd ℂ) A * (starRingEnd ℂ) L) := by
    ring
  rw [hre, hsum]
  push_cast
  ring

/-! ## §3 Rank-one detection -/

/-- The diagonal coefficient is nonzero away from the origin and the real axis. -/
theorem xiWeilDiagonalCoeff_ne_zero {z : ℂ} (hz0 : z ≠ 0) (him : z.im ≠ 0) :
    xiWeilDiagonalCoeff z ≠ 0 := by
  unfold xiWeilDiagonalCoeff
  apply div_ne_zero
  · simpa using hz0
  · apply mul_ne_zero hz0
    intro h
    have := sub_eq_zero.mp h
    have him' := congrArg Complex.im this
    rw [Complex.conj_im] at him'
    exact him (by linarith)

/-- Schwarz reality in the centered coordinate. -/
theorem XiC_conj' (z : ℂ) :
    XiC ((starRingEnd ℂ) z) = (starRingEnd ℂ) (XiC z) := by
  rw [XiC, XiC]
  have harg : 1 / 2 + (starRingEnd ℂ) z * Complex.I =
      1 - (starRingEnd ℂ) (1 / 2 + z * Complex.I) := by
    apply Complex.ext
    · simp
      ring
    · simp
  rw [harg, xi_one_sub, xi_conj]

/-- Continuity of the diagonal coefficient away from the origin and the real
axis. -/
theorem continuousAt_xiWeilDiagonalCoeff {z : ℂ} (hz0 : z ≠ 0) (him : z.im ≠ 0) :
    ContinuousAt xiWeilDiagonalCoeff z := by
  have hden : z * (z - (starRingEnd ℂ) z) ≠ 0 := by
    refine mul_ne_zero hz0 ?_
    intro h
    have hh := sub_eq_zero.mp h
    have him' := congrArg Complex.im hh
    rw [Complex.conj_im] at him'
    exact him (by linarith)
  unfold xiWeilDiagonalCoeff
  exact ContinuousAt.div (by fun_prop) (by fun_prop) hden

/-- **Rank-one detection of an off-critical zero.**  If the centered completed
zeta vanishes off the real axis then some single base point makes the diagonal
Weil value negative: the Weil form on the resolvent test algebra is not
positive semidefinite. -/
theorem exists_neg_weilDiagonal_of_offAxis_zero {pt₀ : ℂ}
    (h0 : XiC pt₀ = 0) (him : pt₀.im ≠ 0) (hne : pt₀ ≠ 0) :
    ∃ z : ℂ, XiC z ≠ 0 ∧ XiC ((starRingEnd ℂ) z) ≠ 0 ∧ z ≠ 0 ∧ z.im ≠ 0 ∧
      (xiWeilPolarization (xiCauchyRegularizedKernel z)
        (xiCauchyRegularizedKernel z)).re < 0 := by
  classical
  obtain ⟨R, hR, g, hgan, hg0, hfact⟩ := XiC_peel_ball pt₀
  set m := (analyticOrderAt XiC pt₀).toNat with hm
  have hmpos : 0 < m := XiC_order_toNat_pos h0
  set A₀ := xiWeilDiagonalCoeff pt₀ with hA₀
  have hA₀ne : A₀ ≠ 0 := xiWeilDiagonalCoeff_ne_zero hne him
  have hmC : ((m : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hmpos.ne'
  set d : ℂ := A₀ * (m : ℂ) with hd
  have hdne : d ≠ 0 := mul_ne_zero hA₀ne hmC
  set ray : ℝ → ℂ := fun t => pt₀ + (t : ℂ) * d with hrayd
  have hraycont : Continuous ray := by fun_prop
  have hray0 : ray 0 = pt₀ := by simp [hrayd]
  have hrayt : Tendsto ray (𝓝[>] 0) (𝓝 pt₀) := by
    have h := (hraycont.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rwa [hray0] at h
  -- eventual admissibility along the ray
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t * ‖d‖ < R := by
    have hc : Tendsto (fun t : ℝ => t * ‖d‖) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => t * ‖d‖) (𝓝 0) (𝓝 (0 * ‖d‖)) := by
        exact (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    exact hc.eventually (eventually_lt_nhds hR)
  have hball : ∀ᶠ t : ℝ in 𝓝[>] 0, ray t ∈ ball pt₀ R := by
    filter_upwards [hpos, hsmall] with t ht htR
    rw [mem_ball, dist_eq_norm, hrayd]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]
    exact htR
  have hne_pt : ∀ᶠ t : ℝ in 𝓝[>] 0, ray t ≠ pt₀ := by
    filter_upwards [hpos] with t ht
    rw [hrayd]
    simp only [ne_eq, add_eq_left, mul_eq_zero, not_or]
    exact ⟨by exact_mod_cast ht.ne', hdne⟩
  have hXne : ∀ᶠ t : ℝ in 𝓝[>] 0, XiC (ray t) ≠ 0 := by
    filter_upwards [hball, hne_pt] with t htb htne
    rw [hfact (ray t) htb]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr htne)) (hg0 _ htb)
  have hXcne : ∀ᶠ t : ℝ in 𝓝[>] 0, XiC ((starRingEnd ℂ) (ray t)) ≠ 0 := by
    filter_upwards [hXne] with t ht
    rw [XiC_conj']
    simpa using ht
  have hz0 : ∀ᶠ t : ℝ in 𝓝[>] 0, ray t ≠ 0 :=
    hrayt.eventually (eventually_ne_nhds hne)
  have himray : ∀ᶠ t : ℝ in 𝓝[>] 0, (ray t).im ≠ 0 := by
    have hc : Tendsto (fun t : ℝ => (ray t).im) (𝓝[>] 0) (𝓝 pt₀.im) :=
      (Complex.continuous_im.tendsto pt₀).comp hrayt
    exact hc.eventually (eventually_ne_nhds him)
  -- the diagonal value along the ray
  have hlogg : ContinuousAt (logDeriv g) pt₀ := by
    have hd1 : ContinuousAt (deriv g) pt₀ :=
      ((hgan pt₀ (mem_ball_self hR)).deriv).continuousAt
    have hd2 : ContinuousAt g pt₀ := (hgan pt₀ (mem_ball_self hR)).continuousAt
    unfold logDeriv
    exact ContinuousAt.div hd1 hd2 (hg0 pt₀ (mem_ball_self hR))
  have hAcont : ContinuousAt xiWeilDiagonalCoeff pt₀ :=
    continuousAt_xiWeilDiagonalCoeff hne him
  set u : ℝ → ℝ := fun t => (xiWeilDiagonalCoeff (ray t) / A₀).re with hu
  set v : ℝ → ℝ :=
    fun t => (xiWeilDiagonalCoeff (ray t) * logDeriv g (ray t)).re with hv
  have hutend : Tendsto u (𝓝[>] 0) (𝓝 1) := by
    have hA : Tendsto (fun t : ℝ => xiWeilDiagonalCoeff (ray t)) (𝓝[>] 0)
        (𝓝 A₀) := hAcont.tendsto.comp hrayt
    have hq : Tendsto (fun t : ℝ => xiWeilDiagonalCoeff (ray t) / A₀)
        (𝓝[>] 0) (𝓝 (A₀ / A₀)) := hA.div_const A₀
    rw [div_self hA₀ne] at hq
    have hre := (Complex.continuous_re.tendsto (1 : ℂ)).comp hq
    simpa [hu, Function.comp] using! hre
  have hvtend : Tendsto v (𝓝[>] 0) (𝓝 (A₀ * logDeriv g pt₀).re) := by
    have hA : Tendsto (fun t : ℝ => xiWeilDiagonalCoeff (ray t)) (𝓝[>] 0)
        (𝓝 A₀) := hAcont.tendsto.comp hrayt
    have hL : Tendsto (fun t : ℝ => logDeriv g (ray t)) (𝓝[>] 0)
        (𝓝 (logDeriv g pt₀)) := hlogg.tendsto.comp hrayt
    have hre := (Complex.continuous_re.tendsto
      (A₀ * logDeriv g pt₀)).comp (hA.mul hL)
    simpa [hv, Function.comp] using! hre
  have hform : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (xiWeilPolarization (xiCauchyRegularizedKernel (ray t))
        (xiCauchyRegularizedKernel (ray t))).re =
        xiSecondInverseMoment.re - 2 * ((1 / t) * u t + v t) := by
    filter_upwards [hpos, hball, hne_pt, hXne, hXcne, hz0, himray] with
      t ht htb htne htX htXc htz0 htim
    rw [xiWeilPolarization_diagonal_eq_sub_two_re htX htz0 htim,
      Complex.sub_re]
    have hcast : ((2 : ℂ) *
        (((xiWeilDiagonalCoeff (ray t) * logDeriv XiC (ray t)).re : ℝ) : ℂ)).re =
        2 * ((xiWeilDiagonalCoeff (ray t) * logDeriv XiC (ray t)).re) := by
      simp
    rw [hcast]
    congr 1
    have hpole := logDeriv_XiC_eq_pole_add hgan hg0 hfact htb htne
    rw [hpole]
    have hsub : ray t - pt₀ = (t : ℂ) * d := by
      rw [hrayd]
      ring
    rw [hsub, hd]
    have htC : ((t : ℂ)) ≠ 0 := by exact_mod_cast ht.ne'
    have htR : (t : ℝ) ≠ 0 := ht.ne'
    have hdiv : ((m : ℂ)) / ((t : ℂ) * (A₀ * (m : ℂ))) =
        (((1 / t : ℝ)) : ℂ) * (1 / A₀) := by
      push_cast
      field_simp
    rw [hdiv]
    have hexp : xiWeilDiagonalCoeff (ray t) *
        ((((1 / t : ℝ)) : ℂ) * (1 / A₀) + logDeriv g (ray t)) =
        (((1 / t : ℝ)) : ℂ) * (xiWeilDiagonalCoeff (ray t) / A₀) +
          xiWeilDiagonalCoeff (ray t) * logDeriv g (ray t) := by
      field_simp
    rw [hexp, Complex.add_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hu, hv]
  -- the value tends to `−∞`
  have hinv : Tendsto (fun t : ℝ => 1 / t) (𝓝[>] 0) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  have hprod : Tendsto (fun t : ℝ => (1 / t) * u t) (𝓝[>] 0) atTop :=
    hinv.atTop_mul_pos one_pos hutend
  have hsum : Tendsto (fun t : ℝ => (1 / t) * u t + v t) (𝓝[>] 0) atTop :=
    hprod.atTop_add hvtend
  have hscaled : Tendsto
      (fun t : ℝ => xiSecondInverseMoment.re - 2 * ((1 / t) * u t + v t))
      (𝓝[>] 0) atBot := by
    have h2 : Tendsto (fun t : ℝ => 2 * ((1 / t) * u t + v t)) (𝓝[>] 0) atTop :=
      hsum.const_mul_atTop (by norm_num)
    have h3 : Tendsto (fun t : ℝ => -(2 * ((1 / t) * u t + v t))) (𝓝[>] 0)
        atBot := tendsto_neg_atTop_atBot.comp h2
    have h4 := tendsto_atBot_add_const_left (𝓝[>] (0 : ℝ))
      xiSecondInverseMoment.re h3
    exact h4.congr fun t => by ring
  have hfinal : Tendsto (fun t : ℝ =>
      (xiWeilPolarization (xiCauchyRegularizedKernel (ray t))
        (xiCauchyRegularizedKernel (ray t))).re) (𝓝[>] 0) atBot :=
    hscaled.congr' (hform.mono fun t ht => ht.symm)
  obtain ⟨t, htneg, htX, htXc, htz0, htim⟩ :=
    ((hfinal.eventually (eventually_lt_atBot 0)).and
      (hXne.and (hXcne.and (hz0.and himray)))).exists
  exact ⟨ray t, htX, htXc, htz0, htim, htneg⟩

/-! ## §4 The criterion -/

/-- **Positivity of the Weil form forces the Riemann Hypothesis.**  If the
diagonal Weil value is nonnegative at every admissible base point off the real
axis, then `ξ` has no zero to the right of the critical line: an off-critical
zero would be detected by a single base point. -/
theorem riemannHypothesis_of_weilDiagonal_nonneg
    (hpos : ∀ z : ℂ, XiC z ≠ 0 → XiC ((starRingEnd ℂ) z) ≠ 0 → z ≠ 0 →
      z.im ≠ 0 →
      0 ≤ (xiWeilPolarization (xiCauchyRegularizedKernel z)
        (xiCauchyRegularizedKernel z)).re) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hzero
  set pt₀ : ℂ := -Complex.I * (s - 1 / 2) with hpt
  have hre : 1 / 2 < s.re := hs
  have hXpt : XiC pt₀ = 0 := by
    show xi ((1 / 2 : ℂ) + pt₀ * Complex.I) = 0
    have harg : (1 / 2 : ℂ) + pt₀ * Complex.I = s := by
      rw [hpt,
        show (-Complex.I * (s - 1 / 2) * Complex.I) =
          -(Complex.I * Complex.I) * (s - 1 / 2) from by ring,
        Complex.I_mul_I]
      ring
    rw [harg]
    exact hzero
  have hptim : pt₀.im ≠ 0 := by
    rw [hpt]
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.sub_re, Complex.sub_im]
    norm_num
    intro hcon
    have hval : s.re = 1 / 2 := by linarith [hcon]
    linarith [hre, hval]
  have hptne : pt₀ ≠ 0 := by
    intro h
    apply hptim
    rw [h]
    simp
  obtain ⟨z, hX, hXc, hz0, him, hneg⟩ :=
    exists_neg_weilDiagonal_of_offAxis_zero hXpt hptim hptne
  exact absurd (hpos z hX hXc hz0 him) (not_le.mpr hneg)

end

end RHTower
