import GaloisForLFunctions.RHTower.XiShiftedHardEdgeComplexPaleyWienerPeriodization
import GaloisForLFunctions.RHTower.WindowBudget
import GaloisForLFunctions.HTGeometry.SectorPowerMassLower
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Complex Cayley geometry for the shifted-Xi hard edge

The central divisor limit needs two facts which the real hard-edge argument does not see:

* throughout `|Im z| < 1`, the real part of the principal complex arctangent has an exact
  two-boundary-angle formula and cannot collapse at large real height;
* the mass-scaled complex Cayley phase converges pointwise to its spectral argument.

Both statements are unconditional analytic identities.  No zero-location hypothesis enters.
-/

open scoped Real

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Real part of the principal complex arctangent is half the principal argument of its defining
Möbius ratio. -/
theorem complex_arctan_re_eq_arg_ratio_div_two (z : ℂ) :
    (Complex.arctan z).re =
      Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I)) / 2 := by
  rw [Complex.arctan]
  simp [Complex.mul_re, Complex.log_im]
  ring

/-- Principal arguments subtract without a branch correction when numerator and denominator both
lie in the open right half-plane. -/
theorem complex_arg_div_eq_sub_of_re_pos
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    Complex.arg (u / v) = Complex.arg u - Complex.arg v := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hu
    exact lt_irrefl 0 hu
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hv
    exact lt_irrefl 0 hv
  have huArg : |Complex.arg u| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have hvArg : |Complex.arg v| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv)
  have hvArgNe : Complex.arg v ≠ Real.pi := by
    intro h
    rw [h, abs_of_pos Real.pi_pos] at hvArg
    linarith [Real.pi_pos]
  have hargInv : Complex.arg v⁻¹ = -Complex.arg v := by
    rw [Complex.arg_inv, if_neg hvArgNe]
  have hmem : Complex.arg u + Complex.arg v⁻¹ ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hargInv]
    rcases abs_lt.mp huArg with ⟨huLower, huUpper⟩
    rcases abs_lt.mp hvArg with ⟨hvLower, hvUpper⟩
    constructor <;> linarith
  rw [div_eq_mul_inv, Complex.arg_mul hu0 (inv_ne_zero hv0) hmem, hargInv]
  simp only [sub_eq_add_neg]

/-- **Exact strip formula for the real complex arctangent.**  The two summands are the boundary
angles to the horizontal edges `Im z = ±1`. -/
theorem complex_arctan_re_eq_average_boundary_arctan
    {z : ℂ} (hz : |z.im| < 1) :
    (Complex.arctan z).re =
      (Real.arctan (z.re / (1 - z.im)) +
        Real.arctan (z.re / (1 + z.im))) / 2 := by
  let u : ℂ := 1 + z * Complex.I
  let v : ℂ := 1 - z * Complex.I
  have hstrip := abs_lt.mp hz
  have huRe : 0 < u.re := by
    simp only [u, Complex.add_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, zero_sub]
    linarith
  have hvRe : 0 < v.re := by
    simp only [v, Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, zero_sub]
    linarith
  have huArg : Complex.arg u = Real.arctan (z.re / (1 - z.im)) := by
    rw [complexArg_eq_arctan_of_re_pos huRe]
    congr 1
    simp [u, Complex.mul_re, Complex.mul_im]
    ring
  have hvArg : Complex.arg v = -Real.arctan (z.re / (1 + z.im)) := by
    rw [complexArg_eq_arctan_of_re_pos hvRe]
    simp only [v, Complex.sub_im, Complex.sub_re, Complex.one_im, Complex.one_re,
      Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, zero_sub, sub_neg_eq_add]
    change Real.arctan (-z.re / (1 + z.im)) =
      -Real.arctan (z.re / (1 + z.im))
    rw [show -z.re / (1 + z.im) = -(z.re / (1 + z.im)) by ring,
      Real.arctan_neg]
  rw [complex_arctan_re_eq_arg_ratio_div_two]
  change Complex.arg (u / v) / 2 = _
  rw [complex_arg_div_eq_sub_of_re_pos huRe hvRe, huArg, hvArg]
  ring

/-- In the full horizontal strip, real spectral height survives the complex arctangent. -/
theorem arctan_abs_re_div_two_le_abs_complex_arctan_re
    {z : ℂ} (hz : |z.im| < 1) :
    Real.arctan (|z.re| / 2) ≤ |(Complex.arctan z).re| := by
  have hstrip := abs_lt.mp hz
  have hd₁pos : 0 < 1 - z.im := by linarith
  have hd₂pos : 0 < 1 + z.im := by linarith
  have hd₁le : 1 - z.im ≤ 2 := by linarith
  have hd₂le : 1 + z.im ≤ 2 := by linarith
  rw [complex_arctan_re_eq_average_boundary_arctan hz]
  by_cases hx : 0 ≤ z.re
  · have hq₁ : z.re / 2 ≤ z.re / (1 - z.im) :=
      div_le_div_of_nonneg_left hx hd₁pos hd₁le
    have hq₂ : z.re / 2 ≤ z.re / (1 + z.im) :=
      div_le_div_of_nonneg_left hx hd₂pos hd₂le
    have ha₁ := Real.arctan_mono hq₁
    have ha₂ := Real.arctan_mono hq₂
    have hnonneg : 0 ≤
        (Real.arctan (z.re / (1 - z.im)) +
          Real.arctan (z.re / (1 + z.im))) / 2 := by
      have hq₁nonneg : 0 ≤ z.re / (1 - z.im) := div_nonneg hx hd₁pos.le
      have hq₂nonneg : 0 ≤ z.re / (1 + z.im) := div_nonneg hx hd₂pos.le
      positivity
    rw [abs_of_nonneg hx, abs_of_nonneg hnonneg]
    linarith
  · have hxneg : z.re < 0 := lt_of_not_ge hx
    let x : ℝ := -z.re
    have hxpos : 0 < x := by simp only [x]; linarith
    have hq₁ : x / 2 ≤ x / (1 - z.im) :=
      div_le_div_of_nonneg_left hxpos.le hd₁pos hd₁le
    have hq₂ : x / 2 ≤ x / (1 + z.im) :=
      div_le_div_of_nonneg_left hxpos.le hd₂pos hd₂le
    have ha₁ := Real.arctan_mono hq₁
    have ha₂ := Real.arctan_mono hq₂
    have hrewrite₁ : Real.arctan (z.re / (1 - z.im)) =
        -Real.arctan (x / (1 - z.im)) := by
      rw [show z.re = -x by simp [x], neg_div, Real.arctan_neg]
    have hrewrite₂ : Real.arctan (z.re / (1 + z.im)) =
        -Real.arctan (x / (1 + z.im)) := by
      rw [show z.re = -x by simp [x], neg_div, Real.arctan_neg]
    have hpos : 0 ≤
        (Real.arctan (x / (1 - z.im)) +
          Real.arctan (x / (1 + z.im))) / 2 := by positivity
    rw [abs_of_neg hxneg, show -z.re = x by rfl, hrewrite₁, hrewrite₂]
    rw [show (-Real.arctan (x / (1 - z.im)) +
          -Real.arctan (x / (1 + z.im))) / 2 =
        -((Real.arctan (x / (1 - z.im)) +
          Real.arctan (x / (1 + z.im))) / 2) by ring,
      abs_neg, abs_of_nonneg hpos]
    linarith

/-- Algebraic lower bound convenient for polynomial Fourier decay. -/
theorem min_abs_re_two_div_four_le_abs_complex_arctan_re
    {z : ℂ} (hz : |z.im| < 1) :
    min |z.re| 2 / 4 ≤ |(Complex.arctan z).re| := by
  have hfirst := arctan_abs_re_div_two_le_abs_complex_arctan_re hz
  let t : ℝ := |z.re| / 2
  have ht : 0 ≤ t := by positivity
  by_cases htle : t ≤ 1
  · have hhalf := arctan_ge_half_self ht htle
    have habsLe : |z.re| ≤ 2 := by
      dsimp only [t] at htle
      linarith
    calc
      min |z.re| 2 / 4 = t / 2 := by
        rw [min_eq_left habsLe]
        dsimp only [t]
        ring
      _ ≤ Real.arctan t := hhalf
      _ ≤ |(Complex.arctan z).re| := by simpa only [t] using hfirst
  · have hone : 1 ≤ t := le_of_not_ge htle
    have habsGe : 2 ≤ |z.re| := by
      dsimp only [t] at hone
      linarith
    have hatanOne : Real.arctan 1 ≤ Real.arctan t := Real.arctan_mono hone
    have hpi : (1 : ℝ) / 2 ≤ Real.pi / 4 := by
      linarith [Real.pi_gt_three]
    calc
      min |z.re| 2 / 4 = (1 : ℝ) / 2 := by
        rw [min_eq_right habsGe]
        norm_num
      _ ≤ Real.arctan 1 := by simpa using hpi
      _ ≤ Real.arctan t := hatanOne
      _ ≤ |(Complex.arctan z).re| := by simpa only [t] using hfirst

/-- The mass-scaled complex Cayley phase retains at least one quarter of the smaller of spectral
height and hard-edge mass. -/
theorem min_abs_re_mass_div_four_le_abs_routeUComplexHardEdgePhase_re
    (r : ℝ) {alpha : ℂ} (halpha : |alpha.im| < 1 / 2) :
    min |alpha.re| (routeUHardEdgeMass r) / 4 ≤
      |(routeUComplexHardEdgePhase r alpha).re| := by
  let a : ℝ := routeUHardEdgeMass r
  let w : ℂ := alpha / (a : ℂ)
  have ha : 1 ≤ a := by simp [a, routeUHardEdgeMass]
  have hapos : 0 < a := zero_lt_one.trans_le ha
  have hwi : |w.im| = |alpha.im| / a := by
    simpa only [w, a] using abs_im_div_routeUHardEdgeMass r alpha
  have hwstrip : |w.im| < 1 := by
    rw [hwi]
    apply (div_lt_iff₀ hapos).2
    nlinarith
  have hbase := min_abs_re_two_div_four_le_abs_complex_arctan_re hwstrip
  have hwre : |w.re| = |alpha.re| / a := by
    have hre : w.re = alpha.re / a := by
      dsimp only [w]
      rw [Complex.div_re]
      simp [Complex.normSq_apply]
      field_simp [hapos.ne']
    rw [hre, abs_div, abs_of_pos hapos]
  have hphase :
      |(routeUComplexHardEdgePhase r alpha).re| =
        a * |(Complex.arctan w).re| := by
    rw [routeUComplexHardEdgePhase]
    change |((a : ℂ) * Complex.arctan w).re| = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, abs_mul, abs_of_pos hapos]
  rcases le_total |alpha.re| a with hlow | hhigh
  · have hwle : |w.re| ≤ 1 := by
      rw [hwre]
      exact (div_le_one hapos).2 hlow
    have hmin : min |w.re| 2 = |w.re| :=
      min_eq_left (hwle.trans (by norm_num))
    rw [min_eq_left hlow, hphase]
    calc
      |alpha.re| / 4 = a * (|w.re| / 4) := by
        rw [hwre]
        field_simp [hapos.ne']
      _ = a * (min |w.re| 2 / 4) := by rw [hmin]
      _ ≤ a * |(Complex.arctan w).re| := by gcongr
  · have hwge : 1 ≤ |w.re| := by
      rw [hwre]
      exact (one_le_div hapos).2 hhigh
    have hmin : 1 ≤ min |w.re| 2 := le_min hwge (by norm_num)
    rw [min_eq_right hhigh, hphase]
    calc
      a / 4 = a * (1 / 4) := by ring
      _ ≤ a * (min |w.re| 2 / 4) := by gcongr
      _ ≤ a * |(Complex.arctan w).re| := by gcongr

/-- **Premise-free Xi phase-height survival.** -/
theorem min_abs_xiSpectralPoint_re_mass_div_four_le_abs_phase_re
    (r : ℝ) (q : XiZeroCopy) :
    min |(xiSpectralPoint q).re| (routeUHardEdgeMass r) / 4 ≤
      |(routeUComplexHardEdgePhase r (xiSpectralPoint q)).re| := by
  have hsupport := xi_divisor_support_re_mem_open_unit q.1
  have him : (xiSpectralPoint q).im = 1 / 2 - ((q.1 : ℂ)).re := by
    rw [xiSpectralPoint]
    simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_im,
      Complex.I_re, Complex.I_im]
  have hhalf : |(xiSpectralPoint q).im| < 1 / 2 := by
    rw [him, abs_lt]
    constructor <;> linarith
  exact min_abs_re_mass_div_four_le_abs_routeUComplexHardEdgePhase_re r
    hhalf

/-- The principal complex arctangent has derivative one at the origin. -/
theorem hasDerivAt_complex_arctan_zero :
    HasDerivAt Complex.arctan 1 0 := by
  let p : ℂ → ℂ := fun z => 1 + z * Complex.I
  let m : ℂ → ℂ := fun z => 1 - z * Complex.I
  have hp : HasDerivAt p Complex.I 0 := by
    simpa only [p, id_eq, one_mul] using
      ((hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).mul_const Complex.I).const_add 1
  have hm : HasDerivAt m (-Complex.I) 0 := by
    have hraw := (hasDerivAt_const (x := (0 : ℂ)) (c := (1 : ℂ))).sub
      ((hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).mul_const Complex.I)
    have h : HasDerivAt ((fun _ : ℂ => 1) - fun z => z * Complex.I)
        (-Complex.I) 0 := hraw.congr_deriv (by ring)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    rfl
  have hm0 : m 0 ≠ 0 := by simp [m]
  have hratio : HasDerivAt (fun z => p z / m z) (2 * Complex.I) 0 := by
    have hraw := hp.fun_div hm hm0
    have hder :
        (Complex.I * m 0 - p 0 * (-Complex.I)) / m 0 ^ 2 =
          2 * Complex.I := by
      simp [p, m]
      ring
    exact hraw.congr_deriv hder
  have honeSlit : (1 : ℂ) ∈ Complex.slitPlane := by
    simpa using Complex.one_mem_slitPlane
  have hlog : HasDerivAt (fun z => Complex.log (p z / m z)) (2 * Complex.I) 0 := by
    simpa [p, m] using hratio.clog (by simpa [p, m] using honeSlit)
  have hscaled := hlog.const_mul (-Complex.I / 2)
  change HasDerivAt
    (fun z : ℂ => -Complex.I / 2 *
      Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))) 1 0
  have hder : (-Complex.I / 2) * (2 * Complex.I) = 1 := by
    rw [show (-Complex.I / 2) * (2 * Complex.I) = -(Complex.I * Complex.I) by ring,
      Complex.I_mul_I]
    norm_num
  simpa only [p, m] using hscaled.congr_deriv hder

/-- Pointwise recovery of every complex spectral coordinate by the integral hard-edge Cayley
phase. -/
theorem tendsto_routeUComplexHardEdgePhase_natCast
    (alpha : ℂ) :
    Filter.Tendsto
      (fun k : ℕ => routeUComplexHardEdgePhase (k : ℝ) alpha)
      Filter.atTop (nhds alpha) := by
  by_cases halpha : alpha = 0
  · subst alpha
    have hzero : Complex.arctan 0 = 0 := by
      rw [Complex.arctan]
      simp
    simp [routeUComplexHardEdgePhase, hzero]
  · have hmass : Filter.Tendsto (fun k : ℕ => (1 + (k : ℝ)))
        Filter.atTop Filter.atTop := by
      simpa only [add_comm] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop
    have hinv : Filter.Tendsto (fun k : ℕ => alpha / (1 + (k : ℝ) : ℂ))
        Filter.atTop (nhds 0) := by
      have hrecipReal : Filter.Tendsto
          (fun k : ℕ => 1 / (1 + (k : ℝ))) Filter.atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop hmass
      have hrecipComplex : Filter.Tendsto
          (fun k : ℕ => (((1 / (1 + (k : ℝ))) : ℝ) : ℂ))
          Filter.atTop (nhds 0) :=
        (Complex.continuous_ofReal.tendsto 0).comp hrecipReal
      have hmul := (tendsto_const_nhds (x := alpha)).mul hrecipComplex
      have hmul0 : Filter.Tendsto
          (fun k : ℕ => alpha * (((1 / (1 + (k : ℝ))) : ℝ) : ℂ))
          Filter.atTop (nhds 0) := by simpa only [mul_zero] using hmul
      apply hmul0.congr'
      filter_upwards with k
      push_cast
      simp only [one_mul, div_eq_mul_inv]
    have hne : ∀ k : ℕ, alpha / (1 + (k : ℝ) : ℂ) ≠ 0 := by
      intro k
      have hden : (1 + (k : ℝ) : ℂ) ≠ 0 := by
        intro hzero
        have hre := congrArg Complex.re hzero
        norm_num at hre
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      exact div_ne_zero halpha hden
    have hinvNE : Filter.Tendsto
        (fun k : ℕ => alpha / (1 + (k : ℝ) : ℂ))
        Filter.atTop (nhdsWithin 0 {0}ᶜ) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hinv, Filter.Eventually.of_forall fun k => by simpa using hne k⟩
    have hslope := hasDerivAt_complex_arctan_zero.tendsto_slope_zero.comp hinvNE
    have hzero : Complex.arctan 0 = 0 := by
      rw [Complex.arctan]
      simp
    have hquot : Filter.Tendsto
        (fun k : ℕ =>
          (alpha / (1 + (k : ℝ) : ℂ))⁻¹ *
            Complex.arctan (alpha / (1 + (k : ℝ) : ℂ)))
        Filter.atTop (nhds 1) := by
      apply hslope.congr'
      filter_upwards with k
      simp only [Function.comp_apply, zero_add, hzero, sub_zero, smul_eq_mul]
    have hmul := (tendsto_const_nhds (x := alpha)).mul hquot
    have hmul' : Filter.Tendsto
        (fun k : ℕ => alpha *
          ((alpha / (1 + (k : ℝ) : ℂ))⁻¹ *
            Complex.arctan (alpha / (1 + (k : ℝ) : ℂ))))
        Filter.atTop (nhds alpha) := by simpa only [mul_one] using hmul
    apply hmul'.congr'
    filter_upwards with k
    rw [routeUComplexHardEdgePhase, routeUHardEdgeMass,
      abs_of_nonneg (show 0 ≤ (k : ℝ) by positivity)]
    push_cast
    field_simp [halpha, show (1 + (k : ℂ)) ≠ 0 by
      intro hzero
      have hre := congrArg Complex.re hzero
      norm_num at hre
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith]

end RHTower
