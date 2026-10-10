import GaloisForLFunctions.RHTower.GaussianCentralGapExplicitCriterion

/-!
# The Bohr spectrum of the central Gaussian prime gap is the set of critical zeros

Let `G(y) = Σ Λ(n) n^{-1/2} e^{-yn²} − ∫₁^∞ u^{-1/2} e^{-yu²} du` and read it in the logarithmic
damping variable `u = log(1/y)`.

* **Gamma form of the incomplete Mellin transform** (`norm_gaussianIncompleteMellin_sub_gamma_le`).
  For `Re b > 0`, `E(y, b) = ½ y^{-b/2} Γ(b/2) − ½ y^{-b/2} ∫₀^y e^{-v} v^{b/2-1} dv`, and the last
  term has norm at most `1/Re b`.
* **Critical germ expansion** (`norm_criticalZeroGerm_sub_gamma_le`).  For `Re a = 0`, `a ≠ 0`, two
  recursion steps give `e^{-y}/a + E(y, a) = ½ Γ(a/2) y^{-a/2} + R` with
  `|R| ≤ (2y + y²)/(|a||a+2|)`.
* **Almost-periodic form under RH** (`gaussianCentralGap_eq_archimedean_sub_bohrSeries`).  With
  `μ_ρ = Im ρ / 2`,
  `G(e^{-u}) = A_{e^{-u}}(½) − Σ_ρ ½ Γ(i μ_ρ) e^{i μ_ρ u} − R(u)`, where the series converges
  absolutely and `R(u) = O(e^{-u})`.
* **Bohr spectrum** (`tendsto_windowAverage_gaussianCentralGap_mul_exp`).  Under RH, for every real
  `τ` the window averages `T⁻¹ ∫₀^T G(e^{-u}) e^{-iτu} du` converge to
  `A(½)·[τ = 0] − ½ Γ(iτ) · #{ρ : Im ρ = 2τ}`.  So the frequencies of the Gaussian prime gap are
  exactly the halved ordinates of the critical zeros, and their amplitudes are the multiplicities
  weighted by `½ Γ(iτ)`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

open XiAtlasFinitePart

/-! ## The Gamma form of the incomplete Mellin transform -/

theorem norm_integral_Ioc_exp_neg_mul_cpow_le {y : ℝ} (hy : 0 < y) {α : ℂ} (hα : 0 < α.re) :
    ‖∫ v in Ioc 0 y, (Real.exp (-v) : ℂ) * (v : ℂ) ^ (α - 1)‖ ≤ y ^ α.re / α.re := by
  have hint : IntervalIntegrable (fun v : ℝ => v ^ (α.re - 1)) volume 0 y :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hval : ∫ v in (0 : ℝ)..y, v ^ (α.re - 1) = y ^ α.re / α.re := by
    rw [integral_rpow (Or.inl (by linarith))]
    simp only [sub_add_cancel]
    rw [Real.zero_rpow hα.ne', sub_zero]
  rw [← hval, intervalIntegral.integral_of_le hy.le]
  refine norm_integral_le_of_norm_le ((intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le).1 hint)
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
  have hv0 : 0 < v := hv.1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hv0]
  simp only [Complex.sub_re, Complex.one_re]
  have := Real.exp_le_one_iff.2 (show -v ≤ 0 by linarith)
  have h0 : 0 ≤ v ^ (α.re - 1) := Real.rpow_nonneg hv0.le _
  nlinarith

/-- **Gamma form.**  For `y > 0` and `Re b > 0`,
`‖E(y, b) − ½ y^{-b/2} Γ(b/2)‖ ≤ 1/Re b`. -/
theorem norm_gaussianIncompleteMellin_sub_gamma_le {y : ℝ} (hy : 0 < y) {b : ℂ} (hb : 0 < b.re) :
    ‖gaussianIncompleteMellin y b - (1 / 2 : ℂ) * (y : ℂ) ^ (-(b / 2)) * Complex.Gamma (b / 2)‖ ≤
      1 / b.re := by
  have hb2 : 0 < (b / 2).re := by simp; linarith
  have hsplit : Complex.Gamma (b / 2) =
      (∫ v in Ioc 0 y, (Real.exp (-v) : ℂ) * (v : ℂ) ^ (b / 2 - 1)) + upperIncGamma (b / 2) y := by
    rw [Complex.Gamma_eq_integral hb2, Complex.GammaIntegral, upperIncGamma,
      ← Set.Ioc_union_Ioi_eq_Ioi hy.le]
    have hconv := Complex.GammaIntegral_convergent hb2
    rw [setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hconv.mono_set Set.Ioc_subset_Ioi_self) (hconv.mono_set (Set.Ioi_subset_Ioi hy.le))]
  rw [gaussianIncompleteMellin_eq_upperIncGamma hy, hsplit]
  have hrw : (1 / 2 : ℂ) * (y : ℂ) ^ (-(b / 2)) * upperIncGamma (b / 2) y -
      (1 / 2 : ℂ) * (y : ℂ) ^ (-(b / 2)) *
        ((∫ v in Ioc 0 y, (Real.exp (-v) : ℂ) * (v : ℂ) ^ (b / 2 - 1)) + upperIncGamma (b / 2) y) =
      -((1 / 2 : ℂ) * (y : ℂ) ^ (-(b / 2)) *
        ∫ v in Ioc 0 y, (Real.exp (-v) : ℂ) * (v : ℂ) ^ (b / 2 - 1)) := by ring
  rw [hrw, norm_neg, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hL := norm_integral_Ioc_exp_neg_mul_cpow_le hy hb2
  have hre : (-(b / 2)).re = -(b.re / 2) := by simp
  have hre2 : (b / 2).re = b.re / 2 := by simp
  rw [hre]
  rw [hre2] at hL
  have hy1 : y ^ (-(b.re / 2)) * y ^ (b.re / 2) = 1 := by
    rw [← Real.rpow_add hy]; simp
  have hpos : 0 ≤ y ^ (-(b.re / 2)) := Real.rpow_nonneg hy.le _
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf]
  calc 1 / 2 * y ^ (-(b.re / 2)) * ‖∫ v in Ioc 0 y, (Real.exp (-v) : ℂ) * (v : ℂ) ^ (b / 2 - 1)‖
      ≤ 1 / 2 * y ^ (-(b.re / 2)) * (y ^ (b.re / 2) / (b.re / 2)) := by gcongr
    _ = 1 / b.re := by
        field_simp
        linarith [hy1, mul_comm (y ^ (b.re / 2)) (y ^ (-(b.re / 2)))]

/-! ## Critical zero germs -/

/-- **Critical germ expansion.**  For `Re a = 0`, `a ≠ 0` and `y > 0`,
`‖e^{-y}/a + E(y, a) − ½ Γ(a/2) y^{-a/2}‖ ≤ (2y + y²)/(‖a‖‖a+2‖)`. -/
theorem norm_criticalZeroGerm_sub_gamma_le {y : ℝ} (hy : 0 < y) {a : ℂ} (ha : a.re = 0)
    (ha0 : a ≠ 0) :
    ‖(Real.exp (-y) : ℂ) / a + gaussianIncompleteMellin y a -
        (1 / 2 : ℂ) * Complex.Gamma (a / 2) * (y : ℂ) ^ (-(a / 2))‖ ≤
      (2 * y + y ^ 2) / (‖a‖ * ‖a + 2‖) := by
  have ha2 : a + 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [ha] at this
  have hb : 0 < (a + 2 + 2).re := by simp [ha]
  have hE4 := norm_gaussianIncompleteMellin_sub_gamma_le hy hb
  have hre4 : (a + 2 + 2).re = 4 := by simp [ha]; norm_num
  rw [hre4] at hE4
  rw [gaussianIncompleteMellin_recursion hy ha0, gaussianIncompleteMellin_recursion hy ha2]
  set e : ℂ := (Real.exp (-y) : ℂ) with he
  set E4 : ℂ := gaussianIncompleteMellin y (a + 2 + 2) with hE4def
  set M4 : ℂ := (1 / 2 : ℂ) * (y : ℂ) ^ (-((a + 2 + 2) / 2)) * Complex.Gamma ((a + 2 + 2) / 2)
    with hM4
  -- the main term reproduces `½ Γ(a/2) y^{-a/2}`
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have hpow : (y : ℂ) ^ (-((a + 2 + 2) / 2)) = (y : ℂ) ^ (-(a / 2)) * ((y : ℂ) ^ 2)⁻¹ := by
    rw [show -((a + 2 + 2) / 2) = -(a / 2) + (-2 : ℂ) by ring, Complex.cpow_add _ _ hy0]
    congr 1
    rw [Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
  have ha2' : a / 2 ≠ 0 := div_ne_zero ha0 two_ne_zero
  have ha21 : a / 2 + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [ha] at this
  have hgam : Complex.Gamma ((a + 2 + 2) / 2) = (a / 2 + 1) * (a / 2) * Complex.Gamma (a / 2) := by
    rw [show (a + 2 + 2) / 2 = (a / 2 + 1) + 1 by ring, Complex.Gamma_add_one _ ha21,
      Complex.Gamma_add_one _ ha2']
    ring
  have hmain : 2 * (y : ℂ) / a * (2 * (y : ℂ) / (a + 2) * M4) =
      (1 / 2 : ℂ) * Complex.Gamma (a / 2) * (y : ℂ) ^ (-(a / 2)) := by
    rw [hM4, hpow, hgam]
    field_simp
  have hexp : e / a + (-e / a + 2 * (y : ℂ) / a * (-e / (a + 2) + 2 * (y : ℂ) / (a + 2) * E4)) -
      (1 / 2 : ℂ) * Complex.Gamma (a / 2) * (y : ℂ) ^ (-(a / 2)) =
      -(2 * (y : ℂ) * e / (a * (a + 2))) + 4 * (y : ℂ) ^ 2 / (a * (a + 2)) * (E4 - M4) := by
    rw [← hmain]
    field_simp
    ring
  rw [hexp]
  have he1 : ‖e‖ ≤ 1 := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hnb : 0 < ‖a + 2‖ := norm_pos_iff.2 ha2
  have hprod : 0 < ‖a‖ * ‖a + 2‖ := mul_pos hna hnb
  have h1 : ‖-(2 * (y : ℂ) * e / (a * (a + 2)))‖ ≤ 2 * y / (‖a‖ * ‖a + 2‖) := by
    rw [norm_neg, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy, Complex.norm_two]
    apply div_le_div_of_nonneg_right _ hprod.le
    have := mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ 2 * y)
    linarith
  have h2 : ‖4 * (y : ℂ) ^ 2 / (a * (a + 2)) * (E4 - M4)‖ ≤ y ^ 2 / (‖a‖ * ‖a + 2‖) := by
    rw [norm_mul, norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hy]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    rw [h4]
    have hE : ‖E4 - M4‖ ≤ 1 / 4 := hE4
    calc 4 * y ^ 2 / (‖a‖ * ‖a + 2‖) * ‖E4 - M4‖ ≤ 4 * y ^ 2 / (‖a‖ * ‖a + 2‖) * (1 / 4) := by
          gcongr
      _ = y ^ 2 / (‖a‖ * ‖a + 2‖) := by ring
  calc _ ≤ ‖-(2 * (y : ℂ) * e / (a * (a + 2)))‖ + ‖4 * (y : ℂ) ^ 2 / (a * (a + 2)) * (E4 - M4)‖ :=
        norm_add_le _ _
    _ ≤ 2 * y / (‖a‖ * ‖a + 2‖) + y ^ 2 / (‖a‖ * ‖a + 2‖) := add_le_add h1 h2
    _ = (2 * y + y ^ 2) / (‖a‖ * ‖a + 2‖) := by ring

/-! ## Window averages -/

/-- The window average `T⁻¹ ∫₀^T f`. -/
def gaussianWindowAverage (f : ℝ → ℂ) (T : ℝ) : ℂ :=
  (T : ℂ)⁻¹ * ∫ u in (0 : ℝ)..T, f u

theorem norm_cexp_ofReal_mul_I_mul (μ u : ℝ) : ‖Complex.exp ((μ : ℂ) * I * (u : ℂ))‖ = 1 := by
  rw [show (μ : ℂ) * I * (u : ℂ) = ((μ * u : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The window average of a character is bounded by `1`. -/
theorem norm_gaussianWindowAverage_cexp_le (μ : ℝ) {T : ℝ} (hT : 0 < T) :
    ‖gaussianWindowAverage (fun u => Complex.exp ((μ : ℂ) * I * (u : ℂ))) T‖ ≤ 1 := by
  rw [gaussianWindowAverage, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hT]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (C := 1)
    (f := fun u : ℝ => Complex.exp ((μ : ℂ) * I * (u : ℂ)))
    (fun u _ => (norm_cexp_ofReal_mul_I_mul μ u).le)
  rw [sub_zero, abs_of_pos hT, one_mul] at h
  calc T⁻¹ * ‖∫ u in (0 : ℝ)..T, Complex.exp ((μ : ℂ) * I * (u : ℂ))‖ ≤ T⁻¹ * T := by gcongr
    _ = 1 := inv_mul_cancel₀ hT.ne'

/-- **Window average of a character**: `T⁻¹ ∫₀^T e^{iμu} du → [μ = 0]`. -/
theorem tendsto_gaussianWindowAverage_cexp (μ : ℝ) :
    Tendsto (gaussianWindowAverage fun u => Complex.exp ((μ : ℂ) * I * (u : ℂ))) atTop
      (𝓝 (if μ = 0 then 1 else 0)) := by
  by_cases hμ : μ = 0
  · rw [if_pos hμ]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    rw [gaussianWindowAverage, hμ]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
      sub_zero, Complex.real_smul, mul_one]
    rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 hT.ne')]
  · rw [if_neg hμ]
    have hc : (μ : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.2 hμ) I_ne_zero
    have hμ0 : 0 < |μ| := abs_pos.2 hμ
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hz : Tendsto (fun T : ℝ => 2 / |μ| * T⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (2 / |μ|)
    refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hz
    · filter_upwards [eventually_gt_atTop 0] with T hT
      rw [gaussianWindowAverage, integral_exp_mul_complex hc, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, norm_div]
      have hnum : ‖Complex.exp ((μ : ℂ) * I * (T : ℂ)) - Complex.exp ((μ : ℂ) * I * ((0 : ℝ) : ℂ))‖
          ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_cexp_ofReal_mul_I_mul, norm_cexp_ofReal_mul_I_mul]
        norm_num
      have hden : ‖(μ : ℂ) * I‖ = |μ| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      rw [hden]
      calc T⁻¹ * (‖Complex.exp ((μ : ℂ) * I * (T : ℂ)) -
            Complex.exp ((μ : ℂ) * I * ((0 : ℝ) : ℂ))‖ / |μ|) ≤ T⁻¹ * (2 / |μ|) := by
            gcongr
        _ = 2 / |μ| * T⁻¹ := by ring

/-- **Cesàro.**  A continuous function tending to `0` has window averages tending to `0`. -/
theorem tendsto_gaussianWindowAverage_of_tendsto_zero {g : ℝ → ℂ} (hg : Continuous g)
    (h0 : Tendsto g atTop (𝓝 0)) : Tendsto (gaussianWindowAverage g) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨U₀, hU₀⟩ := (Metric.tendsto_atTop.1 h0) (ε / 2) (by positivity)
  set U : ℝ := max U₀ 0 with hU
  have hU0 : 0 ≤ U := le_max_right _ _
  set C : ℝ := ‖∫ u in (0 : ℝ)..U, g u‖ with hC
  refine ⟨max (U + 1) (2 * (C + 1) / ε), fun T hT => ?_⟩
  have hTU : U + 1 ≤ T := (le_max_left _ _).trans hT
  have hTC : 2 * (C + 1) / ε ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith
  rw [dist_zero_right, gaussianWindowAverage, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hT0,
    ← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable 0 U)
      (hg.intervalIntegrable U T)]
  have htail : ‖∫ u in U..T, g u‖ ≤ ε / 2 * |T - U| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    rw [Set.uIoc_of_le (by linarith)] at hu
    have := hU₀ u (by have := le_max_left U₀ 0; linarith [hu.1])
    rw [dist_zero_right] at this
    exact this.le
  rw [abs_of_pos (by linarith : 0 < T - U)] at htail
  have hsum : ‖(∫ u in (0 : ℝ)..U, g u) + ∫ u in U..T, g u‖ ≤ C + ε / 2 * T := by
    refine (norm_add_le _ _).trans ?_
    nlinarith
  have hC0 : 0 ≤ C := norm_nonneg _
  have hCT : C < ε / 2 * T := by
    rw [div_le_iff₀ hε] at hTC
    nlinarith
  calc T⁻¹ * ‖(∫ u in (0 : ℝ)..U, g u) + ∫ u in U..T, g u‖ ≤ T⁻¹ * (C + ε / 2 * T) := by gcongr
    _ < T⁻¹ * (ε / 2 * T + ε / 2 * T) := by gcongr
    _ = ε := by field_simp; ring

/-- **Bohr coefficients of an absolutely convergent exponential series.**  If
`Σ ‖c_q‖ < ∞`, then `T⁻¹ ∫₀^T (Σ_q c_q e^{iμ_q u}) e^{-iτu} du → Σ_{μ_q = τ} c_q`. -/
theorem tendsto_gaussianWindowAverage_tsum_cexp {ι : Type*} [Countable ι] (c : ι → ℂ)
    (hc : Summable fun q => ‖c q‖) (μ : ι → ℝ) (τ : ℝ) :
    Tendsto (gaussianWindowAverage fun u =>
        (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) *
          Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) atTop
      (𝓝 (∑' q, if μ q = τ then c q else 0)) := by
  -- the shifted characters as continuous maps
  let F : ι → C(ℝ, ℂ) := fun q =>
    ⟨fun u => c q * Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ)), by fun_prop⟩
  have hF : ∀ q u, F q u = c q * Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ)) := fun _ _ => rfl
  have hpt : ∀ u : ℝ, (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) *
      Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ)) = ∑' q, F q u := by
    intro u
    rw [← tsum_mul_right]
    refine tsum_congr fun q => ?_
    rw [hF, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hnormF : ∀ q (K : TopologicalSpace.Compacts ℝ), ‖(F q).restrict K‖ ≤ ‖c q‖ := by
    intro q K
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_
    rw [ContinuousMap.restrict_apply, hF, norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
  have hint : ∀ T : ℝ, ∫ u in (0 : ℝ)..T, (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) *
      Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ)) =
      ∑' q, c q * ∫ u in (0 : ℝ)..T, Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ)) := by
    intro T
    simp_rw [hpt]
    rw [← intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hnormF q _) hc)]
    refine tsum_congr fun q => ?_
    exact intervalIntegral.integral_const_mul (c q)
      (fun u : ℝ => Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ)))
  have havg : ∀ T : ℝ, gaussianWindowAverage (fun u =>
      (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) *
        Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) T =
      ∑' q, c q * gaussianWindowAverage
        (fun u => Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ))) T := by
    intro T
    rw [gaussianWindowAverage, hint, ← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [gaussianWindowAverage]
    ring
  rw [show (gaussianWindowAverage fun u =>
      (∑' q, c q * Complex.exp ((μ q : ℂ) * I * (u : ℂ))) *
        Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) = fun T => ∑' q, c q * gaussianWindowAverage
        (fun u => Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ))) T from funext havg]
  have hlim : ∀ q, (if μ q = τ then c q else 0) = c q * (if μ q - τ = 0 then 1 else 0) := by
    intro q
    by_cases h : μ q = τ
    · rw [if_pos h, if_pos (sub_eq_zero.2 h), mul_one]
    · rw [if_neg h, if_neg (fun h' => h (sub_eq_zero.1 h')), mul_zero]
  rw [tsum_congr hlim]
  refine tendsto_tsum_of_dominated_convergence hc
    (fun q => (tendsto_gaussianWindowAverage_cexp (μ q - τ)).const_mul (c q)) ?_
  filter_upwards [eventually_gt_atTop 0] with T hT q
  rw [norm_mul]
  calc ‖c q‖ * ‖gaussianWindowAverage (fun u => Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ))) T‖
      ≤ ‖c q‖ * 1 := by gcongr; exact norm_gaussianWindowAverage_cexp_le _ hT
    _ = ‖c q‖ := mul_one _

/-! ## The almost-periodic form of the central gap under RH -/

/-- Half the ordinate of a zero copy. -/
def xiZeroHalfOrdinate (q : XiZeroCopy) : ℝ := (xiZero q).im / 2

/-- The Bohr amplitude `½ Γ(i μ_ρ)` of a zero copy, `μ_ρ = Im ρ / 2`. -/
def criticalBohrAmplitude (q : XiZeroCopy) : ℂ :=
  (1 / 2 : ℂ) * Complex.Gamma ((xiZeroHalfOrdinate q : ℂ) * I)

/-- The critical germ of a zero copy at damping `y`. -/
def criticalZeroGerm (y : ℝ) (q : XiZeroCopy) : ℂ :=
  (Real.exp (-y) : ℂ) / (xiZero q - 1 / 2) + gaussianIncompleteMellin y (xiZero q - ((1 / 2 : ℝ) : ℂ))

theorem xiZero_sub_half_eq_of_riemannHypothesis (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    xiZero q - 1 / 2 = (((xiZero q).im : ℝ) : ℂ) * I := by
  have hre : (xiZero q).re = 1 / 2 := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  apply Complex.ext <;> simp [hre]

theorem norm_cpow_neg_ofReal_mul_I {y : ℝ} (hy : 0 < y) (μ : ℝ) :
    ‖(y : ℂ) ^ (-((μ : ℂ) * I))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp

theorem exp_neg_cpow_eq_cexp (u μ : ℝ) :
    ((Real.exp (-u) : ℝ) : ℂ) ^ (-((μ : ℂ) * I)) = Complex.exp ((μ : ℂ) * I * (u : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'),
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  congr 1
  push_cast
  ring

/-- **Critical germ = Bohr term + O(y).**  Under RH,
`‖germ_ρ(y) − ½ Γ(i μ_ρ) y^{-i μ_ρ}‖ ≤ (2y + y²) ‖(ρ − ½)⁻¹‖²`. -/
theorem norm_criticalZeroGerm_sub_bohr_le (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y)
    (q : XiZeroCopy) :
    ‖criticalZeroGerm y q - criticalBohrAmplitude q * (y : ℂ) ^ (-((xiZeroHalfOrdinate q : ℂ) * I))‖ ≤
      (2 * y + y ^ 2) * ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 := by
  set a : ℂ := xiZero q - 1 / 2 with ha
  have hcast : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  have haI := xiZero_sub_half_eq_of_riemannHypothesis hRH q
  have hare : a.re = 0 := by rw [ha, haI]; simp
  have him : 1 < |(xiZero q).im| := by
    by_contra h
    push Not at h
    exact xi_ne_zero_of_abs_im_le_one h (xi_xiZero q)
  have ha0 : a ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    rw [ha, haI] at this
    simp at this
    rw [this, abs_zero] at him
    linarith
  have hhalf : a / 2 = (xiZeroHalfOrdinate q : ℂ) * I := by
    rw [ha, haI, xiZeroHalfOrdinate]; push_cast; ring
  have h := norm_criticalZeroGerm_sub_gamma_le hy hare ha0
  rw [hhalf] at h
  have hgerm : criticalZeroGerm y q = (Real.exp (-y) : ℂ) / a + gaussianIncompleteMellin y a := by
    rw [criticalZeroGerm, hcast]
  rw [hgerm, criticalBohrAmplitude, mul_assoc]
  rw [mul_assoc] at h
  refine h.trans ?_
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
  have hnab : ‖a‖ ≤ ‖a + 2‖ := by
    have h1 : ‖a‖ ^ 2 ≤ ‖a + 2‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, hare, Complex.re_ofNat, Complex.im_ofNat]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  rw [norm_inv, inv_pow, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  rw [sq]
  exact mul_le_mul_of_nonneg_left hnab (norm_nonneg _)

theorem summable_norm_inv_xiZero_sq :
    Summable fun q : XiZeroCopy => ‖(xiZero q)⁻¹‖ ^ 2 :=
  (summable_norm_inv_xiZero_pow (k := 2) le_rfl).congr fun _ => norm_pow _ _

/-- Under RH the Bohr amplitudes are absolutely summable. -/
theorem summable_norm_criticalBohrAmplitude (hRH : RiemannHypothesis) :
    Summable fun q : XiZeroCopy => ‖criticalBohrAmplitude q‖ := by
  have hq : ∀ q : XiZeroCopy, (xiZero q).re = 1 / 2 :=
    fun q => xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    ((summable_norm_inv_xiZero_sq.mul_left (2 * (1 + 1))).add
      (summable_norm_inv_xiZero_sub_half_sq.mul_left (2 * 1 + 1 ^ 2)))
  have h1 := norm_criticalZeroGerm_sub_bohr_le hRH one_pos q
  have h2 := norm_criticalZeroGerm_le one_pos q (hq q)
  rw [Complex.ofReal_one, Complex.one_cpow, mul_one] at h1
  have h3 : ‖criticalBohrAmplitude q‖ ≤ ‖criticalZeroGerm 1 q‖ +
      ‖criticalZeroGerm 1 q - criticalBohrAmplitude q‖ := by
    have := norm_sub_le (criticalZeroGerm 1 q) (criticalZeroGerm 1 q - criticalBohrAmplitude q)
    rwa [sub_sub_cancel] at this
  have h4 : ‖criticalZeroGerm 1 q‖ ≤ 2 * (1 + 1) * ‖(xiZero q)⁻¹‖ ^ 2 := h2
  linarith

/-- **Almost-periodic form under RH.**  For `y > 0`,
`G(y) = A_y(½) − Σ_ρ ½ Γ(i μ_ρ) y^{-i μ_ρ} − Σ_ρ (germ_ρ(y) − ½ Γ(i μ_ρ) y^{-i μ_ρ})`. -/
theorem gaussianCentralGap_eq_archimedean_sub_bohrSeries (hRH : RiemannHypothesis) {y : ℝ}
    (hy : 0 < y) :
    ((gaussianWeightedPrimeMass (1 / 2) y - gaussianWeightedContinuumMass (1 / 2) y : ℝ) : ℂ) =
      gaussianArchimedeanMB y 2 ((1 / 2 : ℝ) : ℂ) -
        (∑' q : XiZeroCopy, criticalBohrAmplitude q *
          (y : ℂ) ^ (-((xiZeroHalfOrdinate q : ℂ) * I))) -
        ∑' q : XiZeroCopy, (criticalZeroGerm y q - criticalBohrAmplitude q *
          (y : ℂ) ^ (-((xiZeroHalfOrdinate q : ℂ) * I))) := by
  have hgap := gaussianWeightedGap_eq_MB_sub_germField (σ := 1 / 2) (by norm_num) hy
  have hS : Summable fun q : XiZeroCopy => criticalBohrAmplitude q *
      (y : ℂ) ^ (-((xiZeroHalfOrdinate q : ℂ) * I)) := by
    refine Summable.of_norm ((summable_norm_criticalBohrAmplitude hRH).congr fun q => ?_)
    rw [norm_mul, norm_cpow_neg_ofReal_mul_I hy, mul_one]
  have hR : Summable fun q : XiZeroCopy => criticalZeroGerm y q - criticalBohrAmplitude q *
      (y : ℂ) ^ (-((xiZeroHalfOrdinate q : ℂ) * I)) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun q => norm_nonneg _)
      (fun q => norm_criticalZeroGerm_sub_bohr_le hRH hy q)
      (summable_norm_inv_xiZero_sub_half_sq.mul_left _))
  rw [hgap, sub_sub, ← hS.tsum_add hR]
  congr 1
  refine tsum_congr fun q => ?_
  rw [add_sub_cancel, criticalZeroGerm]

/-- **Bohr spectrum of the central Gaussian gap.**  Under RH, for every real `τ`,
`T⁻¹ ∫₀^T G(e^{-u}) e^{-iτu} du → A(½)·[τ = 0] − Σ_{Im ρ = 2τ} ½ Γ(iτ)`. -/
theorem tendsto_gaussianWindowAverage_gaussianCentralGap (hRH : RiemannHypothesis) (τ : ℝ) :
    Tendsto (gaussianWindowAverage fun u =>
        ((gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
          gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) : ℝ) : ℂ) *
          Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ))) atTop
      (𝓝 ((if τ = 0 then gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ) else 0) -
        ∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = τ then criticalBohrAmplitude q else 0)) := by
  set A : ℂ := gaussianArchimedeanCurrent ((1 / 2 : ℝ) : ℂ) with hA
  set S : ℝ → ℂ := fun u => ∑' q : XiZeroCopy, criticalBohrAmplitude q *
    Complex.exp ((xiZeroHalfOrdinate q : ℂ) * I * (u : ℂ)) with hSdef
  set f : ℝ → ℂ := fun u => ((gaussianWeightedPrimeMass (1 / 2) (Real.exp (-u)) -
    gaussianWeightedContinuumMass (1 / 2) (Real.exp (-u)) : ℝ) : ℂ) with hfdef
  set E : ℝ → ℂ := fun u => Complex.exp (((-τ : ℝ) : ℂ) * I * (u : ℂ)) with hEdef
  have hsum := summable_norm_criticalBohrAmplitude hRH
  have hScont : Continuous S := by
    refine continuous_tsum (fun q => by fun_prop) hsum (fun q u => ?_)
    rw [norm_mul, norm_cexp_ofReal_mul_I_mul, mul_one]
  have hfcont : Continuous f := by
    have h := continuous_gaussianBudgetProfile (σ := 1 / 2) (by norm_num) (-1) 0 0
    have heq : f = fun u => ((gaussianBudgetProfile (-1) (1 / 2) 0 0 u : ℝ) : ℂ) := by
      funext u
      simp [hfdef, gaussianBudgetProfile]
    rw [heq]
    exact Complex.continuous_ofReal.comp h
  have hEcont : Continuous E := by fun_prop
  -- the remainder after the archimedean constant and the Bohr series
  set h : ℝ → ℂ := fun u => f u - A + S u with hhdef
  have hhcont : Continuous h := (hfcont.sub continuous_const).add hScont
  have hexpand : ∀ u : ℝ, h u = (gaussianArchimedeanMB (Real.exp (-u)) 2 ((1 / 2 : ℝ) : ℂ) - A) -
      ∑' q : XiZeroCopy, (criticalZeroGerm (Real.exp (-u)) q - criticalBohrAmplitude q *
        ((Real.exp (-u) : ℝ) : ℂ) ^ (-((xiZeroHalfOrdinate q : ℂ) * I))) := by
    intro u
    have he := gaussianCentralGap_eq_archimedean_sub_bohrSeries hRH (Real.exp_pos (-u))
    have hSu : S u = ∑' q : XiZeroCopy, criticalBohrAmplitude q *
        ((Real.exp (-u) : ℝ) : ℂ) ^ (-((xiZeroHalfOrdinate q : ℂ) * I)) := by
      rw [hSdef]
      exact tsum_congr fun q => by rw [exp_neg_cpow_eq_cexp]
    simp only [hhdef, hfdef]
    rw [he, hSu]
    ring
  have hexp0 : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ Real.tendsto_exp_neg_atTop_nhds_zero
      (Eventually.of_forall fun u => Real.exp_pos _)
  have hMB : Tendsto (fun u : ℝ => gaussianArchimedeanMB (Real.exp (-u)) 2 ((1 / 2 : ℝ) : ℂ) - A)
      atTop (𝓝 0) := by
    have h1 := (tendsto_gaussianArchimedeanCurrent_sub_MB two_pos
      (s := ((1 / 2 : ℝ) : ℂ)) (by norm_num)).comp hexp0
    have h2 := h1.neg
    rw [neg_zero] at h2
    refine h2.congr fun u => ?_
    simp only [Function.comp, hA]
    ring
  have hRem : Tendsto (fun u : ℝ => ∑' q : XiZeroCopy, (criticalZeroGerm (Real.exp (-u)) q -
      criticalBohrAmplitude q * ((Real.exp (-u) : ℝ) : ℂ) ^ (-((xiZeroHalfOrdinate q : ℂ) * I))))
      atTop (𝓝 0) := by
    set K : ℝ := ∑' q : XiZeroCopy, ‖(xiZero q - 1 / 2)⁻¹‖ ^ 2 with hK
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun u : ℝ => (2 * Real.exp (-u) + Real.exp (-u) ^ 2) * K) atTop (𝓝 0) := by
      have h0 := Real.tendsto_exp_neg_atTop_nhds_zero
      simpa using ((h0.const_mul 2).add (h0.pow 2)).mul_const K
    refine squeeze_zero (fun u => norm_nonneg _) (fun u => ?_) hlim
    have hy := Real.exp_pos (-u)
    refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun q => norm_nonneg _)
      (fun q => norm_criticalZeroGerm_sub_bohr_le hRH hy q)
      (summable_norm_inv_xiZero_sub_half_sq.mul_left _))).trans ?_
    rw [hK, ← tsum_mul_left]
    exact (Summable.of_nonneg_of_le (fun q => norm_nonneg _)
      (fun q => norm_criticalZeroGerm_sub_bohr_le hRH hy q)
      (summable_norm_inv_xiZero_sub_half_sq.mul_left _)).tsum_le_tsum
      (fun q => norm_criticalZeroGerm_sub_bohr_le hRH hy q)
      (summable_norm_inv_xiZero_sub_half_sq.mul_left _)
  have hh0 : Tendsto h atTop (𝓝 0) := by
    have := hMB.sub hRem
    rw [sub_zero] at this
    exact this.congr fun u => (hexpand u).symm
  have hhE0 : Tendsto (fun u => h u * E u) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (tendsto_zero_iff_norm_tendsto_zero.1 hh0)
    refine this.congr fun u => ?_
    rw [norm_mul, hEdef]
    simp only
    rw [norm_cexp_ofReal_mul_I_mul, mul_one]
  -- split the window average
  have hsplit : ∀ T : ℝ, gaussianWindowAverage (fun u => f u * E u) T =
      gaussianWindowAverage (fun u => h u * E u) T + A * gaussianWindowAverage E T -
        gaussianWindowAverage (fun u => S u * E u) T := by
    intro T
    have hpt : (fun u => f u * E u) = fun u => (h u * E u + A * E u) - S u * E u := by
      funext u; simp only [hhdef]; ring
    have i1 : IntervalIntegrable (fun u => h u * E u + A * E u) volume 0 T :=
      ((hhcont.mul hEcont).add (continuous_const.mul hEcont)).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun u => S u * E u) volume 0 T :=
      (hScont.mul hEcont).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun u => h u * E u) volume 0 T :=
      (hhcont.mul hEcont).intervalIntegrable _ _
    have i4 : IntervalIntegrable (fun u => A * E u) volume 0 T :=
      (continuous_const.mul hEcont).intervalIntegrable _ _
    rw [gaussianWindowAverage, hpt, intervalIntegral.integral_sub i1 i2,
      intervalIntegral.integral_add i3 i4, intervalIntegral.integral_const_mul]
    simp only [gaussianWindowAverage]
    ring
  have hfun : (gaussianWindowAverage fun u => f u * E u) = fun T =>
      gaussianWindowAverage (fun u => h u * E u) T + A * gaussianWindowAverage E T -
        gaussianWindowAverage (fun u => S u * E u) T := funext hsplit
  have hlim1 : Tendsto (gaussianWindowAverage fun u => h u * E u) atTop (𝓝 0) :=
    tendsto_gaussianWindowAverage_of_tendsto_zero (hhcont.mul hEcont) hhE0
  have hlim2 := (tendsto_gaussianWindowAverage_cexp (-τ)).const_mul A
  have hlim3 := tendsto_gaussianWindowAverage_tsum_cexp criticalBohrAmplitude hsum
    xiZeroHalfOrdinate τ
  have htot := (hlim1.add hlim2).sub hlim3
  have hval : (if τ = 0 then A else 0) - ∑' q : XiZeroCopy,
      (if xiZeroHalfOrdinate q = τ then criticalBohrAmplitude q else 0) =
      (0 + A * (if -τ = 0 then 1 else 0)) - ∑' q : XiZeroCopy,
      (if xiZeroHalfOrdinate q = τ then criticalBohrAmplitude q else 0) := by
    by_cases hτ : τ = 0
    · rw [if_pos hτ, if_pos (by rw [hτ, neg_zero]), mul_one, zero_add]
    · rw [if_neg hτ, if_neg (by intro h; exact hτ (neg_eq_zero.1 h)), mul_zero, zero_add]
  rw [hfun, hval]
  exact htot

/-! ## Zero detection -/

/-- A zero of `ξ` has positive divisor multiplicity. -/
theorem xiDivisor_pos_of_xi_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) :
    0 < (MeromorphicOn.divisor xi Set.univ) ρ := by
  rw [MeromorphicOn.divisor_apply (fun z _ => (xi_analyticAt z).meromorphicAt) (Set.mem_univ ρ),
    (xi_analyticAt ρ).meromorphicOrderAt_eq]
  have hne : analyticOrderAt xi ρ ≠ 0 := (xi_analyticAt ρ).analyticOrderAt_ne_zero.mpr hρ
  have htop : analyticOrderAt xi ρ ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]; exact xi_not_eventually_zero ρ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn] at hne ⊢
  have hn0 : n ≠ 0 := by rintro rfl; exact hne rfl
  rw [ENat.map_coe, WithTop.untop₀_coe]
  exact_mod_cast Nat.pos_of_ne_zero hn0

/-- Every zero of `ξ` is the value of a zero copy. -/
theorem exists_xiZeroCopy_eq_of_xi_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) :
    ∃ q : XiZeroCopy, xiZero q = ρ := by
  have hpos := xiDivisor_pos_of_xi_eq_zero hρ
  have hmem : ρ ∈ (MeromorphicOn.divisor xi Set.univ).support := Function.mem_support.mpr hpos.ne'
  exact ⟨⟨⟨ρ, hmem⟩, ⟨0, Int.lt_toNat.mpr (by simpa using hpos)⟩⟩, rfl⟩

/-- The number of zero copies with half-ordinate `τ`, i.e. the multiplicity of `½ + 2iτ`. -/
def halfOrdinateMultiplicity (τ : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = τ then (1 : ℝ) else 0

theorem summable_halfOrdinate_indicator (hRH : RiemannHypothesis) (τ : ℝ) :
    Summable fun q : XiZeroCopy => if xiZeroHalfOrdinate q = τ then (1 : ℝ) else 0 := by
  refine Summable.of_nonneg_of_le (fun q => by split_ifs <;> norm_num) (fun q => ?_)
    (summable_norm_inv_xiZero_sub_half_sq.mul_left (4 * τ ^ 2))
  split_ifs with h
  · have haI := xiZero_sub_half_eq_of_riemannHypothesis hRH q
    have him : (xiZero q).im = 2 * τ := by rw [xiZeroHalfOrdinate] at h; linarith
    have hn : ‖xiZero q - 1 / 2‖ = 2 * |τ| := by
      rw [haI, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, him,
        abs_mul, abs_two]
    have hτ : τ ≠ 0 := by
      intro h0
      have hz := xi_xiZero q
      have hlow : |(xiZero q).im| ≤ 1 := by rw [him, h0]; norm_num
      exact xi_ne_zero_of_abs_im_le_one hlow hz
    rw [norm_inv, inv_pow, hn, mul_pow, sq_abs]
    have h4 : 0 < 2 ^ 2 * τ ^ 2 := by have := pow_pos (abs_pos.2 hτ) 2; rw [sq_abs] at this; positivity
    rw [show (4 : ℝ) * τ ^ 2 = 2 ^ 2 * τ ^ 2 by norm_num, mul_inv_cancel₀ h4.ne']
  · positivity

/-- **The Bohr coefficient counts the zero.**
`Σ_{μ_ρ = τ} ½ Γ(i μ_ρ) = ½ Γ(iτ) · #{ρ : Im ρ = 2τ}`. -/
theorem tsum_bohrAmplitude_eq_gamma_mul_multiplicity (τ : ℝ) :
    (∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = τ then criticalBohrAmplitude q else 0) =
      (1 / 2 : ℂ) * Complex.Gamma ((τ : ℂ) * I) * (halfOrdinateMultiplicity τ : ℂ) := by
  rw [halfOrdinateMultiplicity, Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  split_ifs with h
  · rw [criticalBohrAmplitude, h]; push_cast; ring
  · simp

/-- **Zero detection.**  Under RH, for `τ ≠ 0`, `½ + 2iτ` is a zero of `ξ` iff the `τ`-Bohr
coefficient of the central Gaussian prime gap is nonzero. -/
theorem xi_eq_zero_iff_bohrCoefficient_ne_zero (hRH : RiemannHypothesis) {τ : ℝ} (hτ : τ ≠ 0) :
    xi (1 / 2 + 2 * (τ : ℂ) * I) = 0 ↔
      (∑' q : XiZeroCopy, if xiZeroHalfOrdinate q = τ then criticalBohrAmplitude q else 0) ≠ 0 := by
  rw [tsum_bohrAmplitude_eq_gamma_mul_multiplicity τ]
  have hΓ : Complex.Gamma ((τ : ℂ) * I) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm => ?_
    have := congrArg Complex.im hm
    simp at this
    exact hτ this
  have hsum := summable_halfOrdinate_indicator hRH τ
  constructor
  · intro hz
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_eq_of_xi_eq_zero hz
    have hμ : xiZeroHalfOrdinate q = τ := by
      rw [xiZeroHalfOrdinate, hq]; simp
    have hle : (1 : ℝ) ≤ halfOrdinateMultiplicity τ := by
      have := hsum.le_tsum q (fun j _ => by split_ifs <;> norm_num)
      rwa [if_pos hμ] at this
    refine mul_ne_zero (mul_ne_zero (by norm_num) hΓ) ?_
    exact_mod_cast (show halfOrdinateMultiplicity τ ≠ 0 by linarith)
  · intro hne
    have hm : halfOrdinateMultiplicity τ ≠ 0 := by
      intro h0; apply hne; rw [h0]; simp
    by_contra hz
    apply hm
    have hall : ∀ q : XiZeroCopy, ¬ xiZeroHalfOrdinate q = τ := by
      intro q hq
      apply hz
      have haI := xiZero_sub_half_eq_of_riemannHypothesis hRH q
      have him : (xiZero q).im = 2 * τ := by rw [xiZeroHalfOrdinate] at hq; linarith
      have hq' : xiZero q = 1 / 2 + 2 * (τ : ℂ) * I := by
        rw [← sub_eq_iff_eq_add', haI, him]; push_cast; ring
      rw [← hq']
      exact xi_xiZero q
    rw [halfOrdinateMultiplicity]
    simp [hall]

end

end RHTower
