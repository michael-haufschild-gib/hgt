import GaloisForLFunctions.RHTower.XiHerglotzCriterion

/-!
# RH as vertical monotonicity of `|Ξ|`

Along a vertical line the logarithmic derivative of the modulus is the imaginary
part of the logarithmic derivative up to sign,
`∂_y log |XiC (x + iy)| = −Im (logDeriv XiC (x + iy))`, so the Herglotz sign
condition says exactly that `y ↦ |XiC (x + iy)|` never decreases.

That reading makes the criterion elementary in one direction: an off-critical
zero sits at some `x₀ + iy₀` with `y₀ > 0`, where the modulus vanishes, while at
nearby smaller heights it is nonzero because zeros are isolated.  Monotonicity
along the vertical ray through `x₀` is therefore impossible, so

**vertical monotonicity of `|Ξ|` on every ray forces the Riemann Hypothesis.**

Under RH the same monotonicity is the transparent statement that
`|Ξ(x + iy)| = ∏ √((x − tₙ)² + y²)` (times a nonvanishing factor) increases in
`y`, each factor being the distance from `x + iy` to a real zero.
-/

open Complex Filter Topology Metric

namespace RHTower

noncomputable section

/-- Zeros of the centred completed zeta are isolated: below any zero on its own
vertical ray there are heights at which the modulus is positive. -/
theorem exists_pos_norm_below_zero {pt₀ : ℂ} (h0 : XiC pt₀ = 0)
    (him : 0 < pt₀.im) :
    ∃ y : ℝ, 0 < y ∧ y < pt₀.im ∧
      XiC ((pt₀.re : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨R, hR, g, hgan, hg0, hfact⟩ := XiC_peel_ball pt₀
  set m := (analyticOrderAt XiC pt₀).toNat with hm
  have hmpos : 0 < m := XiC_order_toNat_pos h0
  set t : ℝ := min (pt₀.im / 2) (R / 2) with ht
  have htpos : 0 < t := lt_min (by linarith) (by linarith)
  have htim : t < pt₀.im := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htR : t < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨pt₀.im - t, by linarith, by linarith, ?_⟩
  set z : ℂ := (pt₀.re : ℂ) + ((pt₀.im - t : ℝ) : ℂ) * Complex.I with hz
  have hzval : z = pt₀ - (t : ℂ) * Complex.I := by
    rw [hz]
    apply Complex.ext <;> simp
  have hmem : z ∈ ball pt₀ R := by
    rw [mem_ball, dist_eq_norm, hzval]
    simp only [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
    exact htR
  have hzne : z ≠ pt₀ := by
    rw [hzval]
    intro hcon
    have hcon' : ((t : ℂ)) * Complex.I = 0 := by linear_combination -hcon
    rcases mul_eq_zero.mp hcon' with h | h
    · exact absurd (by exact_mod_cast h : (t : ℝ) = 0) htpos.ne'
    · exact Complex.I_ne_zero h
  rw [hfact z hmem]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzne)) (hg0 z hmem)

/-- **The vertical monotonicity criterion.**  If for every real abscissa the
modulus `y ↦ ‖XiC (x + iy)‖` never decreases on the nonnegative ray, then the
Riemann Hypothesis holds: an off-critical zero would force the modulus to drop
to zero at its own height while being positive just below it. -/
theorem riemannHypothesis_of_norm_XiC_vertical_monotone
    (hmono : ∀ x y₁ y₂ : ℝ, 0 ≤ y₁ → y₁ ≤ y₂ →
      ‖XiC ((x : ℂ) + (y₁ : ℂ) * Complex.I)‖ ≤
        ‖XiC ((x : ℂ) + (y₂ : ℂ) * Complex.I)‖) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hzero
  -- centred coordinate of the off-critical zero, conjugated into the upper half
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
  set pt₀ : ℂ := (starRingEnd ℂ) pt₁ with hpt₀
  have hX0 : XiC pt₀ = 0 := by
    rw [hpt₀, XiC_conj', hXpt, map_zero]
  have him : 0 < pt₀.im := by
    rw [hpt₀]
    simpa using hptim
  obtain ⟨y, hypos, hylt, hyne⟩ := exists_pos_norm_below_zero hX0 him
  -- the modulus is positive below the zero and vanishes at it
  have hzero_at : XiC ((pt₀.re : ℂ) + ((pt₀.im : ℝ) : ℂ) * Complex.I) = 0 := by
    have hre_eq : ((pt₀.re : ℂ)) + ((pt₀.im : ℝ) : ℂ) * Complex.I = pt₀ := by
      apply Complex.ext <;> simp
    rw [hre_eq]
    exact hX0
  have hstep := hmono pt₀.re y pt₀.im (le_of_lt hypos) (le_of_lt hylt)
  rw [hzero_at, norm_zero] at hstep
  exact hyne (norm_eq_zero.mp (le_antisymm hstep (norm_nonneg _)))

/-! ## §2 The converse: RH forces vertical monotonicity -/

/-- Real-part derivative of a complex path. -/
private theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {y : ℝ}
    (h : HasDerivAt f f' y) : HasDerivAt (fun t => (f t).re) f'.re y := by
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h).congr_of_eventuallyEq
    (Eventually.of_forall fun _ => rfl)

/-- Imaginary-part derivative of a complex path. -/
private theorem hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {y : ℝ}
    (h : HasDerivAt f f' y) : HasDerivAt (fun t => (f t).im) f'.im y := by
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h).congr_of_eventuallyEq
    (Eventually.of_forall fun _ => rfl)

/-- The vertical path and its derivative. -/
private theorem hasDerivAt_verticalPath (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) Complex.I y := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y :=
    Complex.ofRealCLM.hasDerivAt
  simpa using ((h.mul_const Complex.I).const_add ((x : ℂ)))

/-- **The vertical derivative identity.**  Off the divisor,
`d/dy ‖XiC(x+iy)‖² = −2‖XiC(x+iy)‖² · Im (logDeriv XiC (x+iy))`: the growth of
the modulus along a vertical line is governed by the Herglotz sign. -/
theorem hasDerivAt_normSq_vertical {x y : ℝ}
    (hne : XiC ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0) :
    HasDerivAt (fun t : ℝ => Complex.normSq (XiC ((x : ℂ) + (t : ℂ) * Complex.I)))
      (-2 * Complex.normSq (XiC ((x : ℂ) + (y : ℂ) * Complex.I)) *
        (logDeriv XiC ((x : ℂ) + (y : ℂ) * Complex.I)).im) y := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz
  set w : ℂ := XiC z with hw
  have hXan : HasDerivAt XiC (deriv XiC z) z :=
    ((XiC_analytic z (Set.mem_univ z)).differentiableAt).hasDerivAt
  have hpath := hasDerivAt_verticalPath x y
  have hcomp : HasDerivAt (fun t : ℝ => XiC ((x : ℂ) + (t : ℂ) * Complex.I))
      (Complex.I • deriv XiC z) y := by
    have hraw := hXan.scomp y hpath
    exact hraw.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)
  have hd : Complex.I • deriv XiC z = Complex.I * (logDeriv XiC z * w) := by
    rw [smul_eq_mul]
    congr 1
    rw [logDeriv, Pi.div_apply, div_mul_cancel₀ _ hne]
  rw [hd] at hcomp
  have hre := hasDerivAt_re hcomp
  have him := hasDerivAt_im hcomp
  have hsq : HasDerivAt
      (fun t : ℝ => Complex.normSq (XiC ((x : ℂ) + (t : ℂ) * Complex.I)))
      (2 * w.re * (Complex.I * (logDeriv XiC z * w)).re +
        2 * w.im * (Complex.I * (logDeriv XiC z * w)).im) y := by
    have hform : (fun t : ℝ =>
        Complex.normSq (XiC ((x : ℂ) + (t : ℂ) * Complex.I))) =
        fun t : ℝ => (XiC ((x : ℂ) + (t : ℂ) * Complex.I)).re *
            (XiC ((x : ℂ) + (t : ℂ) * Complex.I)).re +
          (XiC ((x : ℂ) + (t : ℂ) * Complex.I)).im *
            (XiC ((x : ℂ) + (t : ℂ) * Complex.I)).im := by
      funext t
      rw [Complex.normSq_apply]
    rw [hform]
    have h1 := hre.mul hre
    have h2 := him.mul him
    have h := h1.add h2
    have h' := h.congr_deriv
      (g' := 2 * w.re * (Complex.I * (logDeriv XiC z * w)).re +
        2 * w.im * (Complex.I * (logDeriv XiC z * w)).im) (by ring)
    exact h'.congr_of_eventuallyEq
      (Eventually.of_forall fun _ => rfl)
  convert hsq using 1
  have hkey : 2 * w.re * (Complex.I * (logDeriv XiC z * w)).re +
      2 * w.im * (Complex.I * (logDeriv XiC z * w)).im =
      -2 * Complex.normSq w * (logDeriv XiC z).im := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply]
    ring
  rw [← hkey]

/-- **RH forces vertical monotonicity.**  Under the Riemann Hypothesis the
modulus `y ↦ ‖XiC (x + iy)‖` is monotone on `[0, ∞)` for every abscissa: off the
real axis there are no zeros, and the derivative identity turns the certified
Herglotz sign into a nonnegative derivative. -/
theorem norm_XiC_vertical_monotoneOn_of_rh (hRH : RiemannHypothesis) (x : ℝ) :
    MonotoneOn (fun y : ℝ =>
      Complex.normSq (XiC ((x : ℂ) + (y : ℂ) * Complex.I))) (Set.Ici 0) := by
  have hne : ∀ y : ℝ, 0 < y → XiC ((x : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro y hy hcon
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hcon
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [ht] at hq
    have him := congrArg Complex.im hq
    simp only [Complex.ofReal_im, Complex.add_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re] at him
    linarith
  have hcont : ContinuousOn (fun y : ℝ =>
      Complex.normSq (XiC ((x : ℂ) + (y : ℂ) * Complex.I))) (Set.Ici 0) := by
    apply Continuous.continuousOn
    have hpath : Continuous fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I := by
      fun_prop
    exact (Complex.continuous_normSq.comp
      ((XiC_analytic.continuousOn).comp_continuous hpath
        (fun t => Set.mem_univ _)))
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont
  · intro y hy
    have hy0 : 0 < y := by
      rw [interior_Ici] at hy
      exact hy
    exact ((hasDerivAt_normSq_vertical (hne y hy0)).differentiableAt).differentiableWithinAt
  · intro y hy
    have hy0 : 0 < y := by
      rw [interior_Ici] at hy
      exact hy
    have hd := hasDerivAt_normSq_vertical (hne y hy0)
    rw [hd.deriv]
    have hsign : (logDeriv XiC ((x : ℂ) + (y : ℂ) * Complex.I)).im ≤ 0 := by
      apply im_logDeriv_XiC_nonpos_of_rh hRH _ (hne y hy0)
      simp [Complex.add_im, Complex.mul_im, hy0]
    have hns : 0 ≤ Complex.normSq (XiC ((x : ℂ) + (y : ℂ) * Complex.I)) :=
      Complex.normSq_nonneg _
    nlinarith [hsign, hns]

end

end RHTower
