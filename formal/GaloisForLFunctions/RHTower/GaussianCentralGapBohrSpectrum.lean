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
  simp_rw [havg]
  have hlim : ∀ q, (if μ q = τ then c q else 0) = c q * (if μ q - τ = 0 then 1 else 0) := by
    intro q
    by_cases h : μ q = τ
    · rw [if_pos h, if_pos (sub_eq_zero.2 h), mul_one]
    · rw [if_neg h, if_neg (fun h' => h (sub_eq_zero.1 h')), mul_zero]
  simp_rw [hlim]
  refine tendsto_tsum_of_dominated_convergence hc
    (fun q => (tendsto_gaussianWindowAverage_cexp (μ q - τ)).const_mul (c q)) ?_
  filter_upwards [eventually_gt_atTop 0] with T hT q
  rw [norm_mul]
  calc ‖c q‖ * ‖gaussianWindowAverage (fun u => Complex.exp (((μ q - τ : ℝ) : ℂ) * I * (u : ℂ))) T‖
      ≤ ‖c q‖ * 1 := by gcongr; exact norm_gaussianWindowAverage_cexp_le _ hT
    _ = ‖c q‖ := mul_one _

end

end RHTower
