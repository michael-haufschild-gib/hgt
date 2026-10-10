import GaloisForLFunctions.RHTower.GaussianMellinBarnesKernel
import GaloisForLFunctions.RHTower.GaussianFormationReflectedHermiteBiehler
import GaloisForLFunctions.RHTower.XiExplicitFormulaLogDeriv
import GaloisForLFunctions.RHTower.XiHadamardFinitePart
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.RHTower.FarFieldAnchor

/-!
# The exact zero field of the Gaussian Euler–continuum formation

Let `E(y, a) = ∫₁^∞ e^{-yu²} u^{a-1} du` (entire in `a`; `E(y, a) = ½ y^{-a/2} Γ(a/2, y)`), and
`K(y,w) = ½ Γ(w/2) y^{-w/2}` the Gaussian Mellin–Barnes kernel.  For `y > 0`, `c > 0`,
`Re s + c > 1`:

`Σ_n Λ(n) n^{-s} e^{-yn²} − E(y, 1−s) = A_{y,c}(s) − Σ_ρ [e^{-y}/(ρ−½) + E(y, ρ−s)]`,

where `ρ` runs over the zeros of `ξ` with multiplicity, the sum converges absolutely, and
`A_{y,c}(s) = (1/2π) ∫ K(y,c+iv) (1/z + Γℝ'/Γℝ(z))|_{z=s+c+iv} dv` is the archimedean transform.
There is no remainder term.  Proof: integrate `K · ξ'/ξ(s+·)` along `Re w = c`; on that line
`ξ'/ξ = 1/z + 1/(z−1) + Γℝ'/Γℝ − L(Λ, ·)` and also `ξ'/ξ = Σ_ρ [1/(ρ−½) + 1/(z−ρ)]`
(absolutely convergent); each partial fraction transforms into `e^{-y}/(ρ−½) + E(y, ρ−s)`.

With `y = πx` the left side is the Gaussian prime current minus the continuum current of the
formation `Φₓ`, so `Φₓ'/Φₓ = h∞'/h∞ − A + Σ_ρ [e^{-πx}/(ρ−½) + E(πx, ρ−s)]`.

Zero germs.  `E(y, a) → −1/a` as `y → 0⁺` when `Re a < 0`: a zero left of `s` contributes its
exact pole `1/(s−ρ)` in the undamped limit.  The incomplete-Gamma recursion
`E(y,a) = −e^{-y}/a + (2y/a) E(y, a+2)` controls the germs uniformly.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-- Every Xi zero copy has `|Im ρ| > 1`, hence `‖ρ - 1/2‖ > 1`. -/
theorem one_lt_norm_xiZero_sub_half (q : XiZeroCopy) : 1 < ‖xiZero q - 1 / 2‖ := by
  have hz : xi (xiZero q) = 0 := xi_xiZero q
  have him : 1 < |(xiZero q).im| := by
    by_contra h
    push Not at h
    exact xi_ne_zero_of_abs_im_le_one h hz
  have h1 : |(xiZero q - 1 / 2).im| ≤ ‖xiZero q - 1 / 2‖ := Complex.abs_im_le_norm _
  have h2 : (xiZero q - 1 / 2).im = (xiZero q).im := by simp
  rw [h2] at h1
  linarith

/-- `Σ ‖(ρ - 1/2)⁻¹‖²` converges over the Xi zero copies. -/
theorem summable_norm_inv_xiZero_sub_half_sq :
    Summable (fun q : XiZeroCopy => ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2) := by
  have hbase := summable_norm_inv_xiZero_pow (k := 2) le_rfl
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_) (hbase.mul_left 4)
  have hd := one_lt_norm_xiZero_sub_half q
  have hρ : ‖xiZero q‖ ≤ 2 * ‖xiZero q - 1 / 2‖ := by
    have : xiZero q = (xiZero q - 1 / 2) + 1 / 2 := by ring
    calc ‖xiZero q‖ = ‖(xiZero q - 1 / 2) + 1 / 2‖ := by rw [← this]
      _ ≤ ‖xiZero q - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * ‖xiZero q - 1 / 2‖ := by
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [this]; linarith
  have hρpos : 0 < ‖xiZero q‖ := by
    have : xiZero q ≠ 0 := by
      intro h0
      have := one_lt_norm_xiZero_sub_half q
      rw [h0] at this; norm_num at this
    exact norm_pos_iff.2 this
  rw [norm_pow, norm_inv, norm_inv]
  have hdpos : 0 < ‖xiZero q - 1 / 2‖ := by linarith
  rw [inv_pow, inv_pow]
  rw [show (4 : ℝ) * (‖xiZero q‖ ^ 2)⁻¹ = (‖xiZero q‖ ^ 2 / 4)⁻¹ by field_simp]
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg (‖xiZero q‖), hρ]

/-- Uniform bound for one paired partial-fraction term on a right half-plane:
`‖(ρ-½)⁻¹ + (z-ρ)⁻¹‖ ≤ (2‖z-½‖ + 2‖z-½‖²/(Re z - 1)) ‖(ρ-½)⁻¹‖²` for `Re z > 1`. -/
theorem norm_xiPartialFractionTerm_le (q : XiZeroCopy) {z : ℂ} (hz : 1 < z.re) :
    ‖(xiZero q - 1 / 2)⁻¹ + (z - xiZero q)⁻¹‖ ≤
      (2 * ‖z - 1 / 2‖ + 2 * ‖z - 1 / 2‖ ^ 2 / (z.re - 1)) * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
  set d : ℂ := xiZero q - 1 / 2 with hd
  set e : ℂ := z - 1 / 2 with he
  have hdnorm : 1 < ‖d‖ := one_lt_norm_xiZero_sub_half q
  have hd0 : d ≠ 0 := by intro h; rw [h, norm_zero] at hdnorm; linarith
  have hre : (xiZero q).re < 1 := (xi_divisor_support_re_mem_open_unit q.1).2
  have hed : z - xiZero q = e - d := by rw [he, hd]; ring
  have hgap : z.re - 1 ≤ ‖e - d‖ := by
    rw [← hed]
    have := Complex.re_le_norm (z - xiZero q)
    simp at this
    have : (z - xiZero q).re = z.re - (xiZero q).re := by simp
    linarith [Complex.re_le_norm (z - xiZero q)]
  have hgap0 : 0 < z.re - 1 := by linarith
  have hed0 : e - d ≠ 0 := by
    intro h; rw [h, norm_zero] at hgap; linarith
  have hterm : d⁻¹ + (z - xiZero q)⁻¹ = e / (d * (e - d)) := by
    rw [hed]; field_simp; ring
  rw [hterm, norm_div, norm_mul, norm_inv]
  have hdpos : 0 < ‖d‖ := by linarith
  have hedpos : 0 < ‖e - d‖ := by linarith
  rw [div_le_iff₀ (by positivity)]
  have he0 : 0 ≤ ‖e‖ := norm_nonneg _
  by_cases hcase : 2 * ‖e‖ ≤ ‖d‖
  · have hlow : ‖d‖ / 2 ≤ ‖e - d‖ := by
      have := norm_sub_norm_le d e
      have h2 : ‖d - e‖ = ‖e - d‖ := norm_sub_rev d e
      linarith
    have key : ‖e‖ ≤ 2 * ‖e‖ * ‖d‖⁻¹ ^ 2 * (‖d‖ * ‖e - d‖) := by
      have : 2 * ‖e‖ * ‖d‖⁻¹ ^ 2 * (‖d‖ * ‖e - d‖) = 2 * ‖e‖ * (‖e - d‖ / ‖d‖) := by
        field_simp
      rw [this]
      have : 1 ≤ 2 * (‖e - d‖ / ‖d‖) := by
        have h1 : ‖d‖ / 2 / ‖d‖ ≤ ‖e - d‖ / ‖d‖ := div_le_div_of_nonneg_right hlow hdpos.le
        have h2 : ‖d‖ / 2 / ‖d‖ = 1 / 2 := by field_simp
        linarith
      nlinarith
    have hextra : 0 ≤ 2 * ‖e‖ ^ 2 / (z.re - 1) * ‖d‖⁻¹ ^ 2 * (‖d‖ * ‖e - d‖) := by positivity
    nlinarith
  · push Not at hcase
    have key : ‖e‖ ≤ 2 * ‖e‖ ^ 2 / (z.re - 1) * ‖d‖⁻¹ ^ 2 * (‖d‖ * ‖e - d‖) := by
      have : 2 * ‖e‖ ^ 2 / (z.re - 1) * ‖d‖⁻¹ ^ 2 * (‖d‖ * ‖e - d‖) =
          ‖e‖ * (2 * ‖e‖ / ‖d‖) * (‖e - d‖ / (z.re - 1)) := by
        field_simp
      rw [this]
      have h1 : 1 ≤ 2 * ‖e‖ / ‖d‖ := by rw [le_div_iff₀ hdpos]; linarith
      have h2 : 1 ≤ ‖e - d‖ / (z.re - 1) := by rw [le_div_iff₀ hgap0]; linarith
      have := mul_le_mul h1 h2 zero_le_one (by positivity)
      nlinarith
    have hextra : 0 ≤ 2 * ‖e‖ * ‖d‖⁻¹ ^ 2 * (‖d‖ * ‖e - d‖) := by positivity
    nlinarith


/-- Gaussian decay beats every power on `[1,∞)`. -/
theorem integrableOn_rpow_mul_exp_neg_sq_Ioi_one {y : ℝ} (hy : 0 < y) (r : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ r * Real.exp (-y * u ^ 2)) (Ioi 1) := by
  set n : ℕ := ⌈max r 0⌉₊ with hn
  have hbase : IntegrableOn (fun u : ℝ => u ^ (n : ℝ) * Real.exp (-y * u ^ 2)) (Ioi 1) :=
    (integrable_rpow_mul_exp_neg_mul_sq hy (s := (n : ℝ))
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith)).integrableOn
  refine hbase.mono' ?_ ?_
  · exact ((continuous_id.continuousOn.rpow_const (fun u hu => Or.inl
      (ne_of_gt (lt_trans one_pos hu)))).mul (by fun_prop : Continuous fun u : ℝ =>
        Real.exp (-y * u ^ 2)).continuousOn).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
    have hu0 : 0 < u := lt_trans one_pos hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    calc r ≤ max r 0 := le_max_left _ _
      _ ≤ n := Nat.le_ceil _

theorem integrableOn_gaussian_cpow_Ioi_one {y : ℝ} (hy : 0 < y) (a : ℂ) :
    IntegrableOn (fun u : ℝ => (Real.exp (-y * u ^ 2) : ℂ) * (u : ℂ) ^ (a - 1)) (Ioi 1) := by
  refine (integrableOn_rpow_mul_exp_neg_sq_Ioi_one hy (a.re - 1)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro u hu
    have hu0 : 0 < u := lt_trans one_pos hu
    exact ((by fun_prop : Continuous fun u : ℝ => (Real.exp (-y * u ^ 2) : ℂ)).continuousAt.mul
      (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
        (Complex.ofReal_mem_slitPlane.2 hu0))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans one_pos hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    simp only [Complex.sub_re, Complex.one_re]
    rw [mul_comm]

/-- **Incomplete-Gamma recursion.**  For `y > 0` and `a ≠ 0`,
`E(y,a) = −e^{−y}/a + (2y/a) E(y,a+2)`, by integration by parts against `d(u^a/a)`. -/
theorem gaussianIncompleteMellin_recursion {y : ℝ} (hy : 0 < y) {a : ℂ} (ha : a ≠ 0) :
    gaussianIncompleteMellin y a = -(Real.exp (-y) : ℂ) / a + (2 * y / a) * gaussianIncompleteMellin y (a + 2) := by
  set U : ℝ → ℂ := fun x => (Real.exp (-y * x ^ 2) : ℂ) with hU
  set U' : ℝ → ℂ := fun x => ((-2 * y * x : ℝ) : ℂ) * (Real.exp (-y * x ^ 2) : ℂ) with hU'
  set V : ℝ → ℂ := fun x => (x : ℂ) ^ a / a with hV
  set V' : ℝ → ℂ := fun x => (x : ℂ) ^ (a - 1) with hV'
  have hUd : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt U (U' x) x := by
    intro x _
    have h := ((hasDerivAt_pow 2 x).const_mul (-y)).exp
    have h2 := h.ofReal_comp
    convert h2 using 1
    simp [hU', mul_comm, mul_left_comm, mul_assoc]
  have hVd : ∀ x ∈ Ioi (1 : ℝ), HasDerivAt V (V' x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans one_pos hx
    have hc : HasDerivAt (fun z : ℂ => z ^ a) (a * (x : ℂ) ^ (a - 1)) (x : ℂ) :=
      (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.2 hx0)).hasDerivAt
    have h2 := (hc.comp_ofReal).div_const a
    have heq : V' x = a * (x : ℂ) ^ (a - 1) / a := by
      show (x : ℂ) ^ (a - 1) = a * (x : ℂ) ^ (a - 1) / a
      field_simp
    rw [heq]
    exact h2
  have hint1 : IntegrableOn (U * V') (Ioi 1) := integrableOn_gaussian_cpow_Ioi_one hy a
  have hint2 : IntegrableOn (U' * V) (Ioi 1) := by
    have h := (integrableOn_gaussian_cpow_Ioi_one hy (a + 2)).const_mul (-2 * y / a : ℂ)
    refine IntegrableOn.congr_fun h (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (x : ℂ) ≠ 0 := by
      have : (0 : ℝ) < x := lt_trans one_pos hx
      exact_mod_cast this.ne'
    simp only [Pi.mul_apply, hU', hV]
    rw [show a + 2 - 1 = a + 1 by ring, Complex.cpow_add _ _ hx0, Complex.cpow_one]
    push_cast
    field_simp
  have hlim1 : Tendsto (U * V) (𝓝[>] (1 : ℝ)) (𝓝 ((Real.exp (-y) : ℂ) / a)) := by
    have hc : ContinuousAt (U * V) 1 := by
      refine ContinuousAt.mul (by fun_prop) ?_
      exact (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
        (Complex.ofReal_mem_slitPlane.2 one_pos)).div_const a
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    convert h using 2
    simp [hU, hV, div_eq_mul_inv]
  have hlim2 : Tendsto (U * V) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a.re y hy
    have hdecay' : Tendsto (fun x : ℝ => x ^ a.re * Real.exp (-y * x) / ‖a‖) atTop (𝓝 0) := by
      simpa using hdecay.div_const ‖a‖
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hdecay'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
    simp only [Pi.mul_apply, hU, hV, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hexp : Real.exp (-y * x ^ 2) ≤ Real.exp (-y * x) := by
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg hy.le (mul_nonneg hx0.le (sub_nonneg.2 hx))]
    have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
    rw [mul_div_assoc', div_le_div_iff_of_pos_right ha0, mul_comm]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul hUd hVd hint1 hint2 hlim1 hlim2
  have hE : gaussianIncompleteMellin y a = ∫ x in Ioi (1 : ℝ), U x * V' x := by
    rw [gaussianIncompleteMellin, integral_Ici_eq_integral_Ioi]
  have hE2 : ∫ x in Ioi (1 : ℝ), U' x * V x = (-2 * y / a) * gaussianIncompleteMellin y (a + 2) := by
    rw [gaussianIncompleteMellin, integral_Ici_eq_integral_Ioi, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (x : ℂ) ≠ 0 := by
      have : (0 : ℝ) < x := lt_trans one_pos hx
      exact_mod_cast this.ne'
    simp only [hU', hV]
    rw [show a + 2 - 1 = a + 1 by ring, Complex.cpow_add _ _ hx0, Complex.cpow_one]
    push_cast
    field_simp
  rw [hE, hparts, hE2]
  push_cast
  ring


/-- **Zero-germ limit.**  For `Re a < 0`, `E(y,a) → −1/a` as `y → 0⁺`: a zero `ρ` strictly left of
`s` (`a = ρ − s`) contributes its exact pole term `1/(s−ρ)` in the undamped limit. -/
theorem tendsto_gaussianIncompleteMellin_of_re_neg {a : ℂ} (ha : a.re < 0) :
    Tendsto (fun y : ℝ => gaussianIncompleteMellin y a) (𝓝[>] 0) (𝓝 (-a⁻¹)) := by
  have hlim : ∫ u in Ici (1 : ℝ), (u : ℂ) ^ (a - 1) = -a⁻¹ := by
    have h := integral_Ioi_cpow_of_lt (a := a - 1) (c := 1) (by simp; linarith) one_pos
    rw [integral_Ici_eq_integral_Ioi, h]
    simp
    field_simp
  rw [← hlim, integral_Ici_eq_integral_Ioi]
  have hfun : (fun y : ℝ => gaussianIncompleteMellin y a) = fun y : ℝ =>
      ∫ u in Ioi (1 : ℝ), (Real.exp (-y * u ^ 2) : ℂ) * (u : ℂ) ^ (a - 1) := by
    funext y; rw [gaussianIncompleteMellin, integral_Ici_eq_integral_Ioi]
  rw [hfun]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => u ^ (a.re - 1)) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun y => ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro u hu
    have hu0 : 0 < u := lt_trans one_pos hu
    exact ((by fun_prop : Continuous fun u : ℝ => (Real.exp (-y * u ^ 2) : ℂ)).continuousAt.mul
      (Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
        (Complex.ofReal_mem_slitPlane.2 hu0))).continuousWithinAt
  · filter_upwards [self_mem_nhdsWithin] with y hy
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans one_pos hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    simp only [Complex.sub_re, Complex.one_re]
    have hy0 : (0 : ℝ) < y := hy
    have : Real.exp (-y * u ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
    calc Real.exp (-y * u ^ 2) * u ^ (a.re - 1) ≤ 1 * u ^ (a.re - 1) := by
          gcongr
      _ = u ^ (a.re - 1) := one_mul _
  · exact integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hc : Continuous fun y : ℝ => (Real.exp (-y * u ^ 2) : ℂ) * (u : ℂ) ^ (a - 1) := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this


/-- Upper incomplete Gamma integral `Γ(α, y) = ∫_y^∞ e^{-v} v^{α-1} dv`. -/
def upperIncGamma (α : ℂ) (y : ℝ) : ℂ :=
  ∫ v in Ioi y, (Real.exp (-v) : ℂ) * (v : ℂ) ^ (α - 1)

/-- **Incomplete-Gamma normal form of the zero germ.**  For `y > 0`,
`E(y, a) = ½ y^{-a/2} Γ(a/2, y)`. -/
theorem gaussianIncompleteMellin_eq_upperIncGamma {y : ℝ} (hy : 0 < y) (a : ℂ) :
    gaussianIncompleteMellin y a = (1 / 2 : ℂ) * (y : ℂ) ^ (-(a / 2)) * upperIncGamma (a / 2) y := by
  have himage : (fun u : ℝ => y * u ^ 2) '' Ioi 1 = Ioi y := by
    ext v
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have : 0 < u ^ 2 - 1 := by nlinarith
      nlinarith [mul_pos hy this]
    · intro hv
      refine ⟨Real.sqrt (v / y), ?_, ?_⟩
      · rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_lt_sqrt (by norm_num) (by rw [lt_div_iff₀ hy]; linarith)
      · rw [Real.sq_sqrt (div_nonneg (by linarith) hy.le)]; field_simp
  have hderiv : ∀ u ∈ Ioi (1 : ℝ), HasDerivWithinAt (fun u : ℝ => y * u ^ 2) (2 * y * u) (Ioi 1) u := by
    intro u _
    have := ((hasDerivAt_pow 2 u).const_mul y).hasDerivWithinAt (s := Ioi 1)
    have heq : y * ((2 : ℕ) * u ^ (2 - 1)) = 2 * y * u := by push_cast; ring
    rw [heq] at this
    exact this
  have hinj : InjOn (fun u : ℝ => y * u ^ 2) (Ioi 1) := by
    intro u hu w hw h
    have hu0 : 0 < u := lt_trans one_pos hu
    have hw0 : 0 < w := lt_trans one_pos hw
    have : u ^ 2 = w ^ 2 := by
      have := mul_left_cancel₀ hy.ne' h
      exact this
    nlinarith [sq_nonneg (u - w), sq_nonneg (u + w)]
  have hsub := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun v : ℝ => (Real.exp (-v) : ℂ) * (v : ℂ) ^ (a / 2 - 1))
  rw [himage] at hsub
  rw [upperIncGamma, hsub, gaussianIncompleteMellin, integral_Ici_eq_integral_Ioi, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  have hu0 : 0 < u := lt_trans one_pos hu
  simp only [real_smul]
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * y * u)]
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have huc : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  have hpow : ((y * u ^ 2 : ℝ) : ℂ) ^ (a / 2 - 1) =
      (y : ℂ) ^ (a / 2 - 1) * (u : ℂ) ^ (a - 2) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hy.le (sq_nonneg u)]
    congr 1
    rw [sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hu0.le hu0.le,
      ← Complex.cpow_add _ _ huc]
    ring_nf
  rw [hpow]
  have hy1 : (y : ℂ) ^ (-(a / 2)) * (y : ℂ) ^ (a / 2 - 1) = (y : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hyc, show -(a / 2) + (a / 2 - 1) = (-1 : ℂ) by ring,
      Complex.cpow_neg_one]
  have hu1 : (u : ℂ) * (u : ℂ) ^ (a - 2) = (u : ℂ) ^ (a - 1) := by
    rw [show a - 1 = (a - 2) + 1 by ring, Complex.cpow_add _ _ huc, Complex.cpow_one, mul_comm]
  have hexp : Real.exp (-y * u ^ 2) = Real.exp (-(y * u ^ 2)) := by ring_nf
  rw [hexp, show ((2 * y * u : ℝ) : ℂ) = 2 * (y : ℂ) * (u : ℂ) by push_cast; ring]
  calc (Real.exp (-(y * u ^ 2)) : ℂ) * (u : ℂ) ^ (a - 1)
      = (Real.exp (-(y * u ^ 2)) : ℂ) * ((u : ℂ) * (u : ℂ) ^ (a - 2)) := by rw [hu1]
    _ = 1 / 2 * ((y : ℂ) ^ (-(a / 2)) * (y : ℂ) ^ (a / 2 - 1)) * (2 * y) *
          ((Real.exp (-(y * u ^ 2)) : ℂ) * ((u : ℂ) * (u : ℂ) ^ (a - 2))) := by
        rw [hy1]; field_simp
    _ = _ := by ring

/-- `h∞'/h∞ = 1/z + Γℝ'/Γℝ` on `Re z > 0`. -/
theorem logDeriv_gaussianArchimedeanHalfFactor_eq_gammaReal {z : ℂ} (hz : 0 < z.re) :
    logDeriv gaussianArchimedeanHalfFactor z = z⁻¹ + logDeriv Complex.Gammaℝ z := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hfun : gaussianArchimedeanHalfFactor = fun w => ((1 / 2 : ℂ) * w) * Complex.Gammaℝ w := by
    funext w; rw [gaussianArchimedeanHalfFactor_eq_gammaReal]
  have hG0 : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hz
  have hGd : DifferentiableAt ℂ Complex.Gammaℝ z := by
    have h1 := (differentiableAt_gaussianArchimedeanHalfFactor hz)
    have : Complex.Gammaℝ = fun w => gaussianArchimedeanHalfFactor w / ((1 / 2 : ℂ) * w) := by
      funext w
      by_cases hw : w = 0
      · subst hw; simp [Complex.Gammaℝ_def]
      · rw [gaussianArchimedeanHalfFactor_eq_gammaReal]; field_simp
    rw [this]
    exact h1.div (by fun_prop) (by simp [hz0])
  rw [hfun, logDeriv_mul (f := fun w : ℂ => (1 / 2 : ℂ) * w) (g := Complex.Gammaℝ) z
    (by simp [hz0]) hG0 (by fun_prop) hGd, logDeriv_const_mul z _ (by norm_num),
    show (fun w : ℂ => w) = id from rfl, logDeriv_id, one_div]

/-! ## The Hadamard side -/

/-- **Zero-side Mellin–Barnes transform.**  For `y > 0`, `c > 0` and `Re s + c > 1`,
`(1/2π)∫ K(c+iv) ξ'/ξ(s+c+iv) dv = Σ_ρ [e^{-y}/(ρ-½) + E(y, ρ - s)]`. -/
theorem mellinBarnes_logDeriv_xi {y c : ℝ} (hy : 0 < y) (hc : 0 < c) {s : ℂ}
    (hs : 1 < s.re + c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, gaussianMBKernel y (c + v * I) * logDeriv xi (s + (c + v * I)) =
      ∑' q : XiZeroCopy, ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) + gaussianIncompleteMellin y (xiZero q - s)) := by
  set δ : ℝ := s.re + c - 1 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set A : ℝ := ‖s - 1 / 2 + c‖ with hA
  set F : XiZeroCopy → ℝ → ℂ := fun q v =>
    gaussianMBKernel y (c + v * I) * ((xiZero q - 1 / 2)⁻¹ + (s + (c + v * I) - xiZero q)⁻¹) with hF
  have hzre : ∀ v : ℝ, 1 < (s + (c + v * I)).re := by
    intro v; simp; linarith
  have hzbound : ∀ v : ℝ, ‖s + (c + v * I) - 1 / 2‖ ≤ A + |v| := by
    intro v
    have : s + (c + v * I) - 1 / 2 = (s - 1 / 2 + c) + v * I := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [hA]; gcongr
    simp [Complex.norm_real]
  -- pointwise bound for each term
  set P : ℝ → ℝ := fun v => 2 * (A + |v|) + 2 * (A + |v|) ^ 2 / δ with hP
  have hPle : ∀ v : ℝ, P v ≤ (2 + 2 * (A + 1) ^ 2 / δ + 2 * (A + 1)) * (1 + |v|) ^ 2 := by
    intro v
    have hA0 : 0 ≤ A := norm_nonneg _
    have hv0 : 0 ≤ |v| := abs_nonneg v
    have h1 : A + |v| ≤ (A + 1) * (1 + |v|) := by nlinarith
    have h2 : (A + |v|) ^ 2 ≤ (A + 1) ^ 2 * (1 + |v|) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h1 2
      nlinarith
    have h3 : (1 + |v|) ≤ (1 + |v|) ^ 2 := by nlinarith
    simp only [hP]
    have h4 : 2 * (A + |v|) ≤ 2 * (A + 1) * (1 + |v|) ^ 2 := by nlinarith
    have h5 : 2 * (A + |v|) ^ 2 / δ ≤ 2 * (A + 1) ^ 2 / δ * (1 + |v|) ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδpos]; nlinarith
    nlinarith
  set C : ℝ := 2 + 2 * (A + 1) ^ 2 / δ + 2 * (A + 1) with hC
  have hFbound : ∀ q v, ‖F q v‖ ≤
      C * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 * (‖gaussianMBKernel y (c + v * I)‖ * (1 + |v|) ^ 2) := by
    intro q v
    simp only [hF, norm_mul]
    have hterm := norm_xiPartialFractionTerm_le q (hzre v)
    have hre : (s + (c + v * I)).re - 1 = δ := by simp [hδ]
    rw [hre] at hterm
    have hmono : 2 * ‖s + (c + v * I) - 1 / 2‖ + 2 * ‖s + (c + v * I) - 1 / 2‖ ^ 2 / δ ≤ P v := by
      simp only [hP]
      have h := hzbound v
      have h0 : 0 ≤ ‖s + (c + v * I) - 1 / 2‖ := norm_nonneg _
      gcongr
    calc ‖gaussianMBKernel y (c + v * I)‖ * ‖(xiZero q - 1 / 2)⁻¹ + (s + (c + v * I) - xiZero q)⁻¹‖
        ≤ ‖gaussianMBKernel y (c + v * I)‖ * (P v * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2) := by
          gcongr; exact hterm.trans (by gcongr)
      _ ≤ ‖gaussianMBKernel y (c + v * I)‖ * (C * (1 + |v|) ^ 2 * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2) := by
          gcongr; exact hPle v
      _ = _ := by ring
  have hFmeas : ∀ q, AEStronglyMeasurable (F q) volume := by
    intro q
    refine Continuous.aestronglyMeasurable ?_
    refine (continuous_gaussianMBKernel_line hy hc).mul (continuous_const.add ?_)
    refine Continuous.inv₀ (by fun_prop) (fun v => ?_)
    intro h0
    have h1 := hzre v
    have hre : (s + (c + v * I) - xiZero q).re = 0 := by rw [h0]; simp
    have hρ : (xiZero q).re < 1 := (xi_divisor_support_re_mem_open_unit q.1).2
    simp at hre
    linarith
  have hFint : ∀ q, Integrable (F q) := by
    intro q
    refine Integrable.mono' ((integrable_norm_gaussianMBKernel_mul_pow hy hc 2).const_mul (C * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2))
      (hFmeas q) (Eventually.of_forall fun v => hFbound q v)
  have hsumm : Summable (fun q => ∫ v : ℝ, ‖F q v‖) := by
    refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun v => norm_nonneg _)
      (fun q => ?_) ((summable_norm_inv_xiZero_sub_half_sq.mul_left C).mul_right
        (∫ v : ℝ, ‖gaussianMBKernel y (c + v * I)‖ * (1 + |v|) ^ 2))
    calc ∫ v : ℝ, ‖F q v‖ ≤ ∫ v : ℝ, C * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 *
          (‖gaussianMBKernel y (c + v * I)‖ * (1 + |v|) ^ 2) :=
          integral_mono (hFint q).norm ((integrable_norm_gaussianMBKernel_mul_pow hy hc 2).const_mul _) (fun v => hFbound q v)
      _ = C * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 * ∫ v : ℝ, ‖gaussianMBKernel y (c + v * I)‖ * (1 + |v|) ^ 2 :=
          integral_const_mul _ _
  have hswap := integral_tsum_of_summable_integral_norm hFint hsumm
  have hpoint : ∀ v : ℝ, gaussianMBKernel y (c + v * I) * logDeriv xi (s + (c + v * I)) =
      ∑' q, F q v := by
    intro v
    rw [logDeriv_xi_eq_partialFraction (xi_ne_zero_of_one_lt_re (hzre v)), ← tsum_mul_left]
    rfl
  have hterm : ∀ q : XiZeroCopy, ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, F q v =
      (Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) + gaussianIncompleteMellin y (xiZero q - s) := by
    intro q
    have hρ : (xiZero q).re < 1 := (xi_divisor_support_re_mem_open_unit q.1).2
    have ha : (xiZero q - s).re < c := by simp; linarith
    have hint1 : Integrable (fun v : ℝ => gaussianMBKernel y (c + v * I)) := by
      refine (integrable_norm_gaussianMBKernel_mul_pow hy hc 0).mono' (continuous_gaussianMBKernel_line hy hc).aestronglyMeasurable
        (Eventually.of_forall fun v => by simp)
    have hint2 : Integrable (fun v : ℝ => gaussianMBKernel y (c + v * I) / ((c + v * I) - (xiZero q - s))) := by
      have : (fun v : ℝ => gaussianMBKernel y (c + v * I) / ((c + v * I) - (xiZero q - s))) =
          fun v => F q v - gaussianMBKernel y (c + v * I) * (xiZero q - 1 / 2)⁻¹ := by
        funext v
        simp only [hF]
        have : (c : ℂ) + v * I - (xiZero q - s) = s + (c + v * I) - xiZero q := by ring
        rw [this]; ring
      rw [this]
      exact (hFint q).sub (hint1.mul_const _)
    have hsplit : ∫ v : ℝ, F q v = (∫ v : ℝ, gaussianMBKernel y (c + v * I)) * (xiZero q - 1 / 2)⁻¹ +
        ∫ v : ℝ, gaussianMBKernel y (c + v * I) / ((c + v * I) - (xiZero q - s)) := by
      rw [← integral_mul_const, ← integral_add (hint1.mul_const _) hint2]
      congr 1
      funext v
      simp only [hF]
      have : (c : ℂ) + v * I - (xiZero q - s) = s + (c + v * I) - xiZero q := by ring
      rw [this]; ring
    rw [hsplit, mul_add, gaussianIncompleteMellin_eq_line_integral hy hc ha, ← mul_assoc, gaussianMBKernel_line_integral hy hc]
    ring
  calc ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, gaussianMBKernel y (c + v * I) * logDeriv xi (s + (c + v * I))
      = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∑' q, ∫ v : ℝ, F q v := by
        rw [hswap]; congr 1; exact integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∑' q, ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, F q v := by rw [tsum_mul_left]
    _ = _ := tsum_congr hterm


/-- Polynomial growth of `ξ'/ξ` on a vertical line right of `Re = 1`, from the partial fractions. -/
theorem norm_logDeriv_xi_line_le {s : ℂ} {c : ℝ} (hs : 1 < s.re + c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖logDeriv xi (s + (c + v * I))‖ ≤ C * (1 + |v|) ^ 2 := by
  set δ : ℝ := s.re + c - 1 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set A : ℝ := ‖s - 1 / 2 + c‖ with hA
  set C0 : ℝ := 2 + 2 * (A + 1) ^ 2 / δ + 2 * (A + 1) with hC0
  set W : ℝ := ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hW
  have hW0 : 0 ≤ W := tsum_nonneg fun q => by positivity
  have hC00 : 0 ≤ C0 := by rw [hC0]; positivity
  refine ⟨C0 * W, mul_nonneg hC00 hW0, fun v => ?_⟩
  have hzre : 1 < (s + (c + v * I)).re := by simp; linarith
  have hre : (s + (c + v * I)).re - 1 = δ := by simp [hδ]
  have hzb : ‖s + (c + v * I) - 1 / 2‖ ≤ A + |v| := by
    have : s + (c + v * I) - 1 / 2 = (s - 1 / 2 + c) + v * I := by ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [hA]; gcongr
    simp [Complex.norm_real]
  have hP : 2 * ‖s + (c + v * I) - 1 / 2‖ + 2 * ‖s + (c + v * I) - 1 / 2‖ ^ 2 / δ ≤
      C0 * (1 + |v|) ^ 2 := by
    have hA0 : 0 ≤ A := norm_nonneg _
    have hv0 : 0 ≤ |v| := abs_nonneg v
    have h0 : 0 ≤ ‖s + (c + v * I) - 1 / 2‖ := norm_nonneg _
    have h1 : ‖s + (c + v * I) - 1 / 2‖ ≤ (A + 1) * (1 + |v|) := by nlinarith
    have h2 : ‖s + (c + v * I) - 1 / 2‖ ^ 2 ≤ (A + 1) ^ 2 * (1 + |v|) ^ 2 := by
      have := pow_le_pow_left₀ h0 h1 2
      nlinarith
    have h3 : (1 + |v|) ≤ (1 + |v|) ^ 2 := by nlinarith
    have h4 : 2 * ‖s + (c + v * I) - 1 / 2‖ ≤ 2 * (A + 1) * (1 + |v|) ^ 2 := by nlinarith
    have h5 : 2 * ‖s + (c + v * I) - 1 / 2‖ ^ 2 / δ ≤ 2 * (A + 1) ^ 2 / δ * (1 + |v|) ^ 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδpos]; nlinarith
    rw [hC0]; nlinarith
  have hsum : Summable (fun q : XiZeroCopy =>
      ‖(xiZero q - 1 / 2)⁻¹ + (s + (c + v * I) - xiZero q)⁻¹‖) := by
    refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
      (summable_norm_inv_xiZero_sub_half_sq.mul_left (C0 * (1 + |v|) ^ 2))
    have ht := norm_xiPartialFractionTerm_le q hzre
    rw [hre] at ht
    exact ht.trans (by gcongr)
  rw [logDeriv_xi_eq_partialFraction (xi_ne_zero_of_one_lt_re hzre)]
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  calc ∑' q, ‖(xiZero q - 1 / 2)⁻¹ + (s + (c + v * I) - xiZero q)⁻¹‖
      ≤ ∑' q, C0 * (1 + |v|) ^ 2 * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
        refine hsum.tsum_le_tsum (fun q => ?_)
          (summable_norm_inv_xiZero_sub_half_sq.mul_left _)
        have ht := norm_xiPartialFractionTerm_le q hzre
        rw [hre] at ht
        exact ht.trans (by gcongr)
    _ = C0 * W * (1 + |v|) ^ 2 := by rw [tsum_mul_left, hW]; ring

theorem continuous_logDeriv_xi_rightLine {s : ℂ} {c : ℝ} (hs : 1 < s.re + c) :
    Continuous (fun v : ℝ => logDeriv xi (s + (c + v * I))) := by
  have hcont : Continuous (fun v : ℝ => s + (c + v * I)) := by fun_prop
  have hd : Continuous (deriv xi) := (xi_differentiable.contDiff (n := 1)).continuous_deriv le_rfl
  simp only [logDeriv_apply]
  refine (hd.comp hcont).div (xi_differentiable.continuous.comp hcont) (fun v => ?_)
  exact xi_ne_zero_of_one_lt_re (by simp; linarith)

/-- Archimedean current `A(z) = 1/z + Γℝ'/Γℝ(z)` (equal to `h∞'/h∞` on `Re z > 0`). -/
def gaussianArchimedeanCurrent (z : ℂ) : ℂ := z⁻¹ + logDeriv Complex.Gammaℝ z

/-- Archimedean Mellin–Barnes transform on the line `Re w = c`. -/
def gaussianArchimedeanMB (y c : ℝ) (s : ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ v : ℝ, gaussianMBKernel y (c + v * I) * gaussianArchimedeanCurrent (s + (c + v * I))

theorem continuous_LSeries_vonMangoldt_line {s : ℂ} {c : ℝ} (hs : 1 < s.re + c) :
    Continuous (fun v : ℝ =>
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + (c + v * I))) := by
  have hd := LSeries_differentiableOn (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
  refine continuous_iff_continuousAt.2 fun v => ?_
  have hzre : 1 < (s + (c + v * I)).re := by simp; linarith
  have hmem : LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) <
      ((s + (c + v * I)).re : EReal) := by
    refine lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      (fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))) ?_
    exact_mod_cast hzre
  have hopen : IsOpen {w : ℂ | LSeries.abscissaOfAbsConv
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < (w.re : EReal)} :=
    isOpen_lt continuous_const (continuous_coe_real_ereal.comp Complex.continuous_re)
  exact ContinuousAt.comp (g := LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)))
    (f := fun v : ℝ => s + (c + v * I))
    (hd.differentiableAt (hopen.mem_nhds hmem)).continuousAt
    (by fun_prop : Continuous fun v : ℝ => s + (c + v * I)).continuousAt

/-- `Σ Λ(n) n^{-σ}` converges for `σ > 1`, in the weighted form used by the Gaussian kernel. -/
theorem summable_vonMangoldt_rpow_neg {s : ℂ} {c : ℝ} (hs : 1 < s.re + c) :
    Summable fun n : ℕ => ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * (n : ℝ) ^ (-(s.re + c)) := by
  have hsum := (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := ((s.re + c : ℝ) : ℂ)) (by simpa using hs)).norm
  refine hsum.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_neg hn.ne', Complex.ofReal_re, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- **Exact Gaussian explicit formula.**  For `y > 0`, `c > 0`, `Re s + c > 1`:
`Σ Λ(n) n^{-s} e^{-yn²} − E(y,1−s) = A_y(s) − Σ_ρ [e^{-y}/(ρ−½) + E(y,ρ−s)]`. -/
theorem gaussianPrimeCurrent_sub_continuum_eq {y c : ℝ} (hy : 0 < y) (hc : 0 < c) {s : ℂ}
    (hs : 1 < s.re + c) :
    ∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
          (Real.exp (-(y * (n : ℝ) ^ 2)) : ℂ) - gaussianIncompleteMellin y (1 - s) =
      gaussianArchimedeanMB y c s -
        ∑' q : XiZeroCopy, ((Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) + gaussianIncompleteMellin y (xiZero q - s)) := by
  set L : ℂ → ℂ := LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) with hL
  set δ : ℝ := s.re + c - 1 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hzre : ∀ v : ℝ, 1 < (s + (c + v * I)).re := by intro v; simp; linarith
  have hKint := (integrable_norm_gaussianMBKernel_mul_pow hy hc 0)
  have hKcont := continuous_gaussianMBKernel_line hy hc
  have hKi : Integrable (fun v : ℝ => gaussianMBKernel y (c + v * I)) :=
    hKint.mono' hKcont.aestronglyMeasurable (Eventually.of_forall fun v => by simp)
  have hLint : Integrable (fun v : ℝ => gaussianMBKernel y (c + v * I) * L (s + (c + v * I))) := by
    refine (hKi.norm.mul_const (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
        (n : ℝ) ^ (s.re + c))).mono'
      (hKcont.mul (continuous_LSeries_vonMangoldt_line hs)).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [norm_mul]
    have hb := norm_LSeries_vonMangoldt_le (hzre v)
    have hre : (s + (c + v * I)).re = s.re + c := by simp
    rw [hre] at hb
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hden : ∀ v : ℝ, (c + v * I) - (1 - s) ≠ 0 := by
    intro v h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hPint : Integrable (fun v : ℝ => gaussianMBKernel y (c + v * I) / ((c + v * I) - (1 - s))) := by
    refine (hKi.norm.mul_const δ⁻¹).mono' ?_ (Eventually.of_forall fun v => ?_)
    · exact (hKcont.div (by fun_prop) hden).aestronglyMeasurable
    · rw [norm_div, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hre : δ ≤ ‖(c + v * I) - (1 - s)‖ := by
        have := Complex.re_le_norm ((c + v * I) - (1 - s))
        simp at this
        rw [hδ]; linarith
      exact inv_anti₀ hδpos hre
  have hXint : Integrable (fun v : ℝ => gaussianMBKernel y (c + v * I) * logDeriv xi (s + (c + v * I))) := by
    obtain ⟨C, hC0, hCb⟩ := norm_logDeriv_xi_line_le hs
    refine ((integrable_norm_gaussianMBKernel_mul_pow hy hc 2).mul_const C).mono'
      (hKcont.mul (continuous_logDeriv_xi_rightLine hs)).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [norm_mul]
    calc ‖gaussianMBKernel y (c + v * I)‖ * ‖logDeriv xi (s + (c + v * I))‖
        ≤ ‖gaussianMBKernel y (c + v * I)‖ * (C * (1 + |v|) ^ 2) :=
          mul_le_mul_of_nonneg_left (hCb v) (norm_nonneg _)
      _ = ‖gaussianMBKernel y (c + v * I)‖ * (1 + |v|) ^ 2 * C := by ring
  have hAint : Integrable (fun v : ℝ =>
      gaussianMBKernel y (c + v * I) * gaussianArchimedeanCurrent (s + (c + v * I))) := by
    have heq : (fun v : ℝ => gaussianMBKernel y (c + v * I) * gaussianArchimedeanCurrent (s + (c + v * I))) =
        fun v : ℝ => gaussianMBKernel y (c + v * I) * logDeriv xi (s + (c + v * I)) -
          gaussianMBKernel y (c + v * I) / ((c + v * I) - (1 - s)) +
          gaussianMBKernel y (c + v * I) * L (s + (c + v * I)) := by
      funext v
      rw [logDeriv_xi_eq_arithmetic (hzre v), gaussianArchimedeanCurrent]
      have : (c : ℂ) + v * I - (1 - s) = s + (c + v * I) - 1 := by ring
      rw [this]
      field_simp
      ring
    rw [heq]
    exact (hXint.sub hPint).add hLint
  have hsplit : ∫ v : ℝ, gaussianMBKernel y (c + v * I) * logDeriv xi (s + (c + v * I)) =
      (∫ v : ℝ, gaussianMBKernel y (c + v * I) * gaussianArchimedeanCurrent (s + (c + v * I))) +
        (∫ v : ℝ, gaussianMBKernel y (c + v * I) / ((c + v * I) - (1 - s))) -
        ∫ v : ℝ, gaussianMBKernel y (c + v * I) * L (s + (c + v * I)) := by
    have hfun : (fun v : ℝ => gaussianMBKernel y (c + v * I) * logDeriv xi (s + (c + v * I))) =
        fun v : ℝ => (gaussianMBKernel y (c + v * I) * gaussianArchimedeanCurrent (s + (c + v * I)) +
          gaussianMBKernel y (c + v * I) / ((c + v * I) - (1 - s))) -
          gaussianMBKernel y (c + v * I) * L (s + (c + v * I)) := by
      funext v
      rw [logDeriv_xi_eq_arithmetic (hzre v), gaussianArchimedeanCurrent]
      have : (c : ℂ) + v * I - (1 - s) = s + (c + v * I) - 1 := by ring
      rw [this]
      field_simp
      ring
    have h1 := integral_sub (hAint.add hPint) hLint
    have h2 := integral_add hAint hPint
    simp only [Pi.add_apply] at h1
    rw [hfun, h1, h2]
  have hzero := mellinBarnes_logDeriv_xi hy hc hs
  have hcont := gaussianIncompleteMellin_eq_line_integral hy hc (a := 1 - s) (by simp; linarith)
  have hprime := tsum_term_mul_exp_neg_eq_line_integral hy hc
    (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s (summable_vonMangoldt_rpow_neg hs)
  rw [hsplit, mul_sub, mul_add] at hzero
  rw [hprime, hcont, gaussianArchimedeanMB]
  rw [← hzero]
  ring



/-! ## The formation identity -/

/-- The Gaussian prime current is the Gaussian-damped von Mangoldt `L`-series term sum. -/
theorem gaussianVonMangoldtCurrent_eq_tsum_term (x : ℝ) (s : ℂ) :
    gaussianVonMangoldtCurrent x s =
      ∑' n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
        (Real.exp (-((Real.pi * x) * (n : ℝ) ^ 2)) : ℂ) := by
  rw [gaussianVonMangoldtCurrent_eq_tsum_cpow]
  set f : ℕ → ℂ := fun n => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n *
    (Real.exp (-((Real.pi * x) * (n : ℝ) ^ 2)) : ℂ) with hf
  have hsupp : Function.support f ⊆ {n : ℕ | 2 ≤ n} := by
    intro n hn
    by_contra h2
    simp only [Set.mem_setOf_eq, not_le] at h2
    apply hn
    interval_cases n
    · simp [hf, LSeries.term_def]
    · simp [hf, LSeries.term_def]
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun n => ?_
  have hn0 : (n.1 : ℂ) ≠ 0 := by
    have : (0 : ℕ) < n.1 := lt_of_lt_of_le (by norm_num) n.2
    exact_mod_cast this.ne'
  simp only [hf, LSeries.term_def, if_neg (show n.1 ≠ 0 by have := n.2; omega)]
  rw [Complex.cpow_neg, div_eq_mul_inv]
  have : -Real.pi * x * (n.1 : ℝ) ^ 2 = -((Real.pi * x) * (n.1 : ℝ) ^ 2) := by ring
  rw [this]
  ring

/-- The continuum current is the incomplete Gaussian Mellin transform at `1 - s`. -/
theorem gaussianContinuumCurrent_eq_incompleteMellin (x : ℝ) (s : ℂ) :
    gaussianContinuumCurrent x s = gaussianIncompleteMellin (Real.pi * x) (1 - s) := by
  rw [gaussianContinuumCurrent, gaussianIncompleteMellin]
  refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
  rw [gaussianContinuumIntegrand, show 1 - s - 1 = -s by ring,
    show -Real.pi * x * u ^ 2 = -(Real.pi * x) * u ^ 2 by ring]

/-- **Exact zero field of the Gaussian formation.**  For `x > 0` and `Re s > 0`,
`Φₓ'/Φₓ(s) = A(s) − A_{πx,2}(s) + Σ_ρ [e^{-πx}/(ρ−½) + E(πx, ρ−s)]`, with `A = h∞'/h∞`. -/
theorem logDeriv_gaussianFormation_eq_zeroField {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    logDeriv (gaussianEulerContinuumFormation x) s =
      gaussianArchimedeanCurrent s - gaussianArchimedeanMB (Real.pi * x) 2 s +
        ∑' q : XiZeroCopy, ((Real.exp (-(Real.pi * x)) : ℂ) / (xiZero q - 1 / 2) +
          gaussianIncompleteMellin (Real.pi * x) (xiZero q - s)) := by
  have hy : 0 < Real.pi * x := mul_pos Real.pi_pos hx
  have hmain := gaussianPrimeCurrent_sub_continuum_eq hy (c := 2) (by norm_num) (s := s)
    (by linarith)
  rw [logDeriv_gaussianEulerContinuumFormation hx hs,
    logDeriv_gaussianArchimedeanHalfFactor_eq_gammaReal hs, gaussianVonMangoldtCurrent_eq_tsum_term,
    gaussianContinuumCurrent_eq_incompleteMellin, gaussianArchimedeanCurrent]
  linear_combination (-1 : ℂ) * hmain

end

end RHTower
