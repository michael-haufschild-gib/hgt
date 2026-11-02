import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfAHorizonBlock
import GaloisForLFunctions.HTGeometry.UnitIntervalRiemannLimit

/-!
# Below the grid the horizon block is sharp

Below the atom grid the horizon block is the Riemann sum of the synthesized test, and this file
makes that quantitative.

* **Lipschitz profile** (`lipschitzWith_horizonProfile`). For a `C²` window profile `g` on
  `[−A, 0]` and `0 ≤ Re s ≤ 2`, the Riemann-sum profile `F_s(x) = g(log x) x^{s−1}` has derivative
  `(g'(log x) + (s − 1) g(log x)) x^{s−2}`, hence is Lipschitz with constant
  `(L_g + |s − 1| B_g) e^{2A}`.
* **Effective Riemann sum** (`norm_riemannSum_sub_le`):
  `|N⁻¹ Σ_{r ≤ N} F_s(r/N) − ĝ(s)| ≤ (L_g + |s − 1| B_g) e^{2A}/N`. At `s = ½ + iτ` this is
  `|N^{−s} D_x(τ) − ĥ(½ + iτ)|`; at `s = 1`, for `g = h²`, it is the Riemann sum of `∫ H²`.
* **The part below the grid** (`abs_lowPart_sub_le`): with `T₀ = N e^{−A}` and `1 ≤ R ≤ T₀`,
  `|∫_{|τ| ≤ T₀} |φ̂(wτ)|² |D_x|²/N − 2π (∫φ)² ∫ H²| ≤ K (√(c/N) + R²/N + 1/R)`. The three terms
  are the atom transform near the origin, the Riemann sums on `|τ| ≤ R`, and the Kuzmin–Landau tail.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

variable {g h φ : ℝ → ℝ} {A : ℝ}

/-! ### The Riemann-sum profile is Lipschitz -/

theorem deriv_eq_zero_of_notMem_window (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) {y : ℝ}
    (hy : y ∉ Set.Icc (-A) 0) : deriv g y = 0 := by
  have hev : g =ᶠ[𝓝 y] fun _ => 0 := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hy
    rcases hy with h1 | h1
    · exact (gt_mem_nhds h1).mono fun t ht => hsupp t fun hm => by linarith [hm.1]
    · exact (lt_mem_nhds h1).mono fun t ht => hsupp t fun hm => by linarith [hm.2]
  rw [hev.deriv_eq, deriv_const]

theorem hasDerivAt_horizonProfile (hg : ContDiff ℝ 2 g) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (horizonProfile g s)
      ((((deriv g (Real.log x) : ℝ) : ℂ) + (s - 1) * (g (Real.log x) : ℂ)) *
        ((x : ℝ) : ℂ) ^ (s - 2)) x := by
  have hev : horizonProfile g s =ᶠ[𝓝 x] fun t => (g (Real.log t) : ℂ) * ((t : ℝ) : ℂ) ^ (s - 1) :=
    (lt_mem_nhds hx).mono fun t ht => by simp only [horizonProfile, if_pos ht]
  have h1 : HasDerivAt (fun t => (g (Real.log t) : ℂ)) ((deriv g (Real.log x) * x⁻¹ : ℝ) : ℂ) x :=
    (((hg.differentiable (by norm_num)) (Real.log x)).hasDerivAt.comp x
      (Real.hasDerivAt_log hx.ne')).ofReal_comp
  have hslit : ((x : ℝ) : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  have h2 := ((hasDerivAt_id ((x : ℝ) : ℂ)).cpow_const (c := s - 1) hslit).comp_ofReal
  have hx0 : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e : ((x : ℝ) : ℂ) ^ (s - 1) = ((x : ℝ) : ℂ) ^ (s - 2) * x := by
    rw [show s - 1 = (s - 2) + 1 by ring, Complex.cpow_add _ _ hx0, Complex.cpow_one]
  refine HasDerivAt.congr_of_eventuallyEq ((h1.mul h2).congr_deriv ?_) hev
  simp only [id]
  rw [show s - 1 - 1 = s - 2 by ring, e]
  push_cast
  field_simp

theorem differentiable_horizonProfile (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (s : ℂ) : Differentiable ℝ (horizonProfile g s) := by
  intro x
  rcases le_or_gt x 0 with hx | hx
  · have hev : horizonProfile g s =ᶠ[𝓝 x] fun _ => 0 :=
      (gt_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos (-A)))).mono fun t ht =>
        horizonProfile_eq_zero_of_lt hsupp s ht
    exact (hasDerivAt_const x (0 : ℂ)).differentiableAt.congr_of_eventuallyEq hev
  · exact (hasDerivAt_horizonProfile hg s hx).differentiableAt

theorem norm_deriv_horizonProfile_le (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hA : 0 ≤ A) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg)
    {Lg : NNReal} (hLg : LipschitzWith Lg g) {s : ℂ} (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2) (x : ℝ) :
    ‖deriv (horizonProfile g s) x‖ ≤ ((Lg : ℝ) + ‖s - 1‖ * Bg) * Real.exp (2 * A) := by
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  rcases le_or_gt x 0 with hx | hx
  · have hev : horizonProfile g s =ᶠ[𝓝 x] fun _ => 0 :=
      (gt_mem_nhds (lt_of_le_of_lt hx (Real.exp_pos (-A)))).mono fun t ht =>
        horizonProfile_eq_zero_of_lt hsupp s ht
    rw [hev.deriv_eq, deriv_const, norm_zero]; positivity
  rw [(hasDerivAt_horizonProfile hg s hx).deriv]
  by_cases hw : Real.log x ∈ Set.Icc (-A) 0
  · rw [norm_mul]
    have hxpow : ‖((x : ℝ) : ℂ) ^ (s - 2)‖ ≤ Real.exp (2 * A) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have hre : (s - 2).re = s.re - 2 := by simp
      rw [hre]
      have hxA : Real.exp (-A) ≤ x := by
        rw [← Real.exp_log hx]; exact Real.exp_le_exp.mpr hw.1
      calc x ^ (s.re - 2) ≤ (Real.exp (-A)) ^ (s.re - 2) :=
            Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hxA (by linarith)
        _ = Real.exp (-A * (s.re - 2)) := by rw [← Real.exp_mul]
        _ ≤ Real.exp (2 * A) := Real.exp_le_exp.mpr (by nlinarith)
    have hnum : ‖((deriv g (Real.log x) : ℝ) : ℂ) + (s - 1) * (g (Real.log x) : ℂ)‖ ≤
        (Lg : ℝ) + ‖s - 1‖ * Bg := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [Complex.norm_real]; exact norm_deriv_le_of_lipschitz hLg
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hBg _) (norm_nonneg _)
    exact mul_le_mul hnum hxpow (norm_nonneg _) (by positivity)
  · rw [deriv_eq_zero_of_notMem_window hsupp hw, hsupp _ hw]
    simp only [Complex.ofReal_zero, mul_zero, add_zero, zero_mul, norm_zero]
    positivity

/-- **The Riemann-sum profile is Lipschitz** with constant `(L_g + |s − 1| B_g) e^{2A}`. -/
theorem lipschitzWith_horizonProfile (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hA : 0 ≤ A) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg)
    {Lg : NNReal} (hLg : LipschitzWith Lg g) {s : ℂ} (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2) :
    LipschitzWith (Real.toNNReal (((Lg : ℝ) + ‖s - 1‖ * Bg) * Real.exp (2 * A)))
      (horizonProfile g s) := by
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  refine lipschitzWith_of_nnnorm_deriv_le (differentiable_horizonProfile hg hsupp s) fun x => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  exact norm_deriv_horizonProfile_le hg hsupp hA hBg hLg hs0 hs2 x

/-- **Effective Riemann sum**: `|N⁻¹ Σ_{r ≤ N} F_s(r/N) − ĝ(s)| ≤ (L_g + |s − 1| B_g) e^{2A}/N`. -/
theorem norm_riemannSum_sub_le (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0) (hA : 0 ≤ A) {Bg : ℝ} (hBg : ∀ y, |g y| ≤ Bg)
    {Lg : NNReal} (hLg : LipschitzWith Lg g) {s : ℂ} (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖((N : ℝ) : ℂ)⁻¹ * ∑ r ∈ Icc 1 N, horizonProfile g s (r / N) - horizonTransform g s‖ ≤
      ((Lg : ℝ) + ‖s - 1‖ * Bg) * Real.exp (2 * A) / N := by
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0)
  have hlip := lipschitzWith_horizonProfile hg hsupp hA hBg hLg hs0 hs2
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h := HTGeometry.unitRiemannSum_error_le hlip M
  rw [Real.coe_toNNReal _ (by positivity)] at h
  have hM : ((M : ℝ) + 1) = ((M + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hM] at h
  -- the two Riemann sums agree since `F_s(0) = F_s(1) = 0`
  have hg0 : g 0 = 0 := horizon_zero_at_zero hsupp fun u v => by
    simpa [Real.dist_eq] using hLg.dist_le_mul u v
  have hF0 : horizonProfile g s 0 = 0 := by simp [horizonProfile]
  have hF1 : horizonProfile g s 1 = 0 := by simp [horizonProfile, hg0]
  have hsum : ∑ r ∈ Icc 1 (M + 1), horizonProfile g s (r / ((M + 1 : ℕ) : ℝ)) =
      ∑ i ∈ Finset.range (M + 1), horizonProfile g s (i / ((M + 1 : ℕ) : ℝ)) := by
    have e1 : ∑ r ∈ Icc 1 (M + 1), horizonProfile g s (r / ((M + 1 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.range (M + 1), horizonProfile g s (((k + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ)) := by
      rw [show Icc 1 (M + 1) = Finset.Ico 1 (M + 2) by ext; simp; omega,
        Finset.sum_Ico_eq_sum_range]
      refine sum_congr (by congr 1) fun k _ => ?_
      congr 2; push_cast; ring
    have e2 := Finset.sum_range_sub (fun k => horizonProfile g s ((k : ℝ) / ((M + 1 : ℕ) : ℝ))) (M + 1)
    rw [div_self (by positivity : ((M + 1 : ℕ) : ℝ) ≠ 0), Nat.cast_zero, zero_div, hF0, hF1,
      sub_zero, Finset.sum_sub_distrib] at e2
    rw [e1]
    linear_combination e2
  have hint : ∫ x in (0 : ℝ)..1, horizonProfile g s x = horizonTransform g s := by
    rw [← integral_horizonProfile hg.continuous hsupp hA s, intervalIntegral.integral_of_le zero_le_one,
      ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    exact horizonProfile_eq_zero_of_notMem hsupp s hx
  unfold HTGeometry.unitRiemannSum at h
  rw [hint, Complex.real_smul] at h
  rw [hsum]
  convert h using 3
  push_cast
  ring

/-! ### The Dirichlet polynomial against its Riemann limit -/

/-- `|ĥ(½ + iτ)|² ≤ C_d/(1 + τ²)`: the Kuzmin–Landau bound passes to the limit. -/
theorem normSq_horizonTransform_le (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {Bh L : ℝ} (hB : ∀ y, |h y| ≤ Bh)
    (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) (τ : ℝ) :
    ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 ≤
      2 * (Bh ^ 2 * Real.exp A + 16 * Real.pi ^ 2 * windowConst A Bh L ^ 2) / (1 + τ ^ 2) := by
  have hlim : Tendsto (fun N : ℕ => ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N) atTop
      (𝓝 (‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2)) := by
    refine ((tendsto_horizonDirichlet hh.continuous hsupp hA _).norm.pow 2).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (norm_sq_div_eq hN _ τ).symm
  refine le_of_tendsto hlim ?_
  have hT : Tendsto (fun N : ℕ => (N : ℝ) * Real.exp (-A)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (Real.exp_pos _)
  filter_upwards [hT.eventually (eventually_ge_atTop |τ|), eventually_ge_atTop 1] with N h1 h2
  exact horizonDirichlet_sq_div_le hsupp hA hB hL h2 h1

/-- On the critical line the Dirichlet polynomial of the block is its Riemann limit up to
`E = (L_h + (½ + |τ|) B_h) e^{2A}/N`. -/
theorem abs_normSq_div_sub_le (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh) {Lh : NNReal}
    (hLh : LipschitzWith Lh h) {N : ℕ} (hN : 1 ≤ N) (τ : ℝ) {C : ℝ}
    (hC : ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ≤ C) :
    |‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N -
        ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2| ≤
      ((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * Real.exp (2 * A) / N *
        (((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * Real.exp (2 * A) / N + 2 * C) := by
  have hB0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set s : ℂ := 1 / 2 + Complex.I * τ with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hs1 : ‖s - 1‖ ≤ 1 / 2 + |τ| := by
    rw [hs, show (1 / 2 : ℂ) + Complex.I * τ - 1 = -(1 / 2 : ℂ) + Complex.I * τ by ring]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hR := norm_riemannSum_sub_le hh hsupp hA hB hLh (s := s) (by rw [hsre]; norm_num)
    (by rw [hsre]; norm_num) hN
  rw [riemannSum_horizonProfile h s hN] at hR
  set a := ((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (horizonWeights h N) (gammaOf s) with ha
  set b := horizonTransform h s with hb
  set E := ((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * Real.exp (2 * A) / N with hE
  have hab : ‖a - b‖ ≤ E := by
    refine hR.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
      hN0.le)
    gcongr
  rw [norm_sq_div_eq hN]
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hab
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC
  have ha' : ‖a‖ ≤ E + C := by
    calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
      _ ≤ E + C := add_le_add hab hC
  have hdiff : |‖a‖ - ‖b‖| ≤ E := (abs_norm_sub_norm_le a b).trans hab
  rw [show ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ‖a‖ + ‖b‖)]
  calc |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) ≤ E * (E + C + C) :=
        mul_le_mul hdiff (add_le_add ha' hC) (by positivity) hE0
    _ = E * (E + 2 * C) := by ring

/-! ### The part below the grid -/

/-- The part of the block energy below the grid, `|τ| ≤ N e^{−A}`. -/
def lowPart (φ h : ℝ → ℝ) (c : ℝ) (N : ℕ) (A : ℝ) : ℝ :=
  ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-A))) ((N : ℝ) * Real.exp (-A)),
    ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 * (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N)

/-- The integrable weight `d(τ) = (1 + |τ|)^{−3/2}`. -/
def decayWeight (τ : ℝ) : ℝ := ((1 + |τ|) * Real.sqrt (1 + |τ|))⁻¹

theorem decayWeight_eq (τ : ℝ) : decayWeight τ = (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) := by
  have hp : 0 < 1 + |τ| := by positivity
  rw [decayWeight, Real.norm_eq_abs, Real.rpow_neg hp.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hp, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem integrable_decayWeight : Integrable decayWeight := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 3 / 2 := by rw [Module.finrank_self]; norm_num
  exact (integrable_one_add_norm hr).congr (Eventually.of_forall fun τ => (decayWeight_eq τ).symm)

theorem decayWeight_nonneg (τ : ℝ) : 0 ≤ decayWeight τ := by unfold decayWeight; positivity

theorem sqrt_abs_div_le_decayWeight (τ : ℝ) :
    Real.sqrt |τ| / (1 + τ ^ 2) ≤ 2 * decayWeight τ := by
  set t := |τ| with ht
  have ht0 : 0 ≤ t := abs_nonneg τ
  have hτ2 : τ ^ 2 = t ^ 2 := (sq_abs τ).symm
  have hs1 := Real.sq_sqrt ht0
  have hs2 := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + t)
  have hsq0 := Real.sqrt_nonneg t
  have hsq1 := Real.sqrt_nonneg (1 + t)
  have hamgm : Real.sqrt t * Real.sqrt (1 + t) ≤ 1 + t := by
    nlinarith [sq_nonneg (Real.sqrt t - Real.sqrt (1 + t))]
  rw [decayWeight, hτ2, div_le_iff₀ (by positivity), ← ht]
  rw [show 2 * ((1 + t) * Real.sqrt (1 + t))⁻¹ * (1 + t ^ 2) =
    2 * (1 + t ^ 2) / ((1 + t) * Real.sqrt (1 + t)) by ring]
  have hpos : 0 < (1 + t) * Real.sqrt (1 + t) := by
    have : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.mpr (by linarith)
    positivity
  rw [le_div_iff₀ hpos]
  have hm := mul_le_mul_of_nonneg_left hamgm (by linarith : (0 : ℝ) ≤ 1 + t)
  have e : Real.sqrt t * ((1 + t) * Real.sqrt (1 + t)) =
      (1 + t) * (Real.sqrt t * Real.sqrt (1 + t)) := by ring
  rw [e]
  nlinarith [sq_nonneg (1 - t)]

theorem inv_one_add_sq_le_decayWeight {R τ : ℝ} (hR : 1 ≤ R) (hτ : R < |τ|) :
    (1 + τ ^ 2)⁻¹ ≤ 2 / Real.sqrt R * decayWeight τ := by
  set t := |τ| with ht
  have hτ2 : τ ^ 2 = t ^ 2 := (sq_abs τ).symm
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr (by linarith)
  have hs1 : Real.sqrt R ≤ Real.sqrt (1 + t) := Real.sqrt_le_sqrt (by linarith)
  have hst : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.mpr (by linarith)
  rw [decayWeight, hτ2, ← ht]
  rw [show 2 / Real.sqrt R * ((1 + t) * Real.sqrt (1 + t))⁻¹ =
    2 / (Real.sqrt R * ((1 + t) * Real.sqrt (1 + t))) by field_simp]
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have h1 : Real.sqrt R * Real.sqrt (1 + t) ≤ 1 + t := by
    calc Real.sqrt R * Real.sqrt (1 + t) ≤ Real.sqrt (1 + t) * Real.sqrt (1 + t) :=
          mul_le_mul_of_nonneg_right hs1 hst.le
      _ = 1 + t := Real.mul_self_sqrt (by linarith)
  nlinarith

/-- The atom transform near the origin: `|φ̂(x) − φ̂(0)| ≤ |x| ∫|φ|` for `φ` on `[0, 1]`. -/
theorem norm_paperFT_sub_zero_le (hφ : Continuous φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (x : ℝ) : ‖paperFT (cx φ) (x : ℂ) - paperFT (cx φ) 0‖ ≤ |x| * ∫ u, |φ u| := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  have hi : ∀ z : ℂ, Integrable fun u : ℝ => cx φ u * Complex.exp (Complex.I * z * u) := by
    intro z
    refine Continuous.integrable_of_hasCompactSupport (by unfold cx; fun_prop) ?_
    exact (hφc.comp_left Complex.ofReal_zero).mul_right
  rw [paperFT_def, paperFT_def, ← integral_sub (hi _) (hi _), ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) ((hφ.abs.integrable_of_hasCompactSupport
      hφc.abs).const_mul _) (Eventually.of_forall fun u => ?_))
  simp only [cx]
  rw [mul_zero, zero_mul, Complex.exp_zero, mul_one, ← mul_sub_one, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]
  by_cases hu : u ∈ Set.Icc (0 : ℝ) 1
  · have he : ‖Complex.exp (Complex.I * x * u) - 1‖ ≤ |x| := by
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x * u)
      rw [show Complex.I * ((x * u : ℝ) : ℂ) = Complex.I * x * u by push_cast; ring,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg hu.1] at this
      exact this.trans (mul_le_of_le_one_right (abs_nonneg _) hu.2)
    calc |φ u| * ‖Complex.exp (Complex.I * x * u) - 1‖ ≤ |φ u| * |x| :=
          mul_le_mul_of_nonneg_left he (abs_nonneg _)
      _ = |x| * |φ u| := by ring
  · rw [hφsupp u hu, abs_zero, zero_mul, mul_zero]

/-- `|‖φ̂(wτ)‖² − (∫φ)²| ≤ 4 (∫|φ|)² √(w|τ|)`. -/
theorem abs_normSq_paperFT_sub_le (hφ : Continuous φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {w : ℝ} (hw : 0 ≤ w) (τ : ℝ) :
    |‖paperFT (cx φ) (((w : ℝ) : ℂ) * τ)‖ ^ 2 - (∫ u, φ u) ^ 2| ≤
      4 * (∫ u, |φ u|) ^ 2 * Real.sqrt (w * |τ|) := by
  set I₀ := ∫ u, |φ u| with hI₀
  have hI₀0 : 0 ≤ I₀ := integral_nonneg fun u => abs_nonneg _
  set a := paperFT (cx φ) (((w : ℝ) : ℂ) * τ) with ha
  set b := paperFT (cx φ) 0 with hb
  have hb' : ‖b‖ ^ 2 = (∫ u, φ u) ^ 2 := by
    rw [hb, paperFT_def]
    simp only [cx, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hna : ‖a‖ ≤ I₀ := by
    have := RHTower.norm_paperFT_real_le_integral_norm (f := cx φ) (w * τ)
    rw [show (((w * τ : ℝ)) : ℂ) = ((w : ℝ) : ℂ) * τ by push_cast; ring] at this
    simpa [cx, Complex.norm_real, Real.norm_eq_abs] using this
  have hnb : ‖b‖ ≤ I₀ := by
    have := RHTower.norm_paperFT_real_le_integral_norm (f := cx φ) 0
    simpa [cx, Complex.norm_real, Real.norm_eq_abs] using this
  have hd1 : ‖a - b‖ ≤ |w * τ| * I₀ := by
    have := norm_paperFT_sub_zero_le hφ hφsupp (w * τ)
    rwa [show (((w * τ : ℝ)) : ℂ) = ((w : ℝ) : ℂ) * τ by push_cast; ring] at this
  have hd2 : ‖a - b‖ ≤ 2 * I₀ := (norm_sub_le _ _).trans (by linarith)
  have hwt : |w * τ| = w * |τ| := by rw [abs_mul, abs_of_nonneg hw]
  have hsq : ‖a - b‖ ≤ 2 * I₀ * Real.sqrt (w * |τ|) := by
    rcases le_or_gt (w * |τ|) 1 with h1 | h1
    · have : w * |τ| ≤ Real.sqrt (w * |τ|) := by
        have h0 : 0 ≤ w * |τ| := by positivity
        calc w * |τ| = Real.sqrt (w * |τ|) * Real.sqrt (w * |τ|) := (Real.mul_self_sqrt h0).symm
          _ ≤ Real.sqrt (w * |τ|) * 1 :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr h1) (Real.sqrt_nonneg _)
          _ = Real.sqrt (w * |τ|) := mul_one _
      rw [hwt] at hd1
      calc ‖a - b‖ ≤ w * |τ| * I₀ := hd1
        _ ≤ Real.sqrt (w * |τ|) * I₀ := mul_le_mul_of_nonneg_right this hI₀0
        _ ≤ 2 * I₀ * Real.sqrt (w * |τ|) := by nlinarith [Real.sqrt_nonneg (w * |τ|)]
    · have : 1 ≤ Real.sqrt (w * |τ|) := Real.one_le_sqrt.mpr h1.le
      calc ‖a - b‖ ≤ 2 * I₀ := hd2
        _ ≤ 2 * I₀ * Real.sqrt (w * |τ|) := le_mul_of_one_le_right (by positivity) this
  rw [← hb', show ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ‖a‖ + ‖b‖)]
  calc |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) ≤ (2 * I₀ * Real.sqrt (w * |τ|)) * (I₀ + I₀) :=
        mul_le_mul ((abs_norm_sub_norm_le a b).trans hsq) (add_le_add hna hnb) (by positivity)
          (by positivity)
    _ = 4 * I₀ ^ 2 * Real.sqrt (w * |τ|) := by ring

/-- The synthesized test on the critical line: `∫ |ĥ(½ + iτ)|² dτ = 2π ∫ e^y h(y)² dy`. -/
theorem integral_normSq_horizonTransform (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∫ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 =
      2 * Real.pi * ∫ y, Real.exp y * h y ^ 2 := by
  have hH : ContDiff ℝ 2 (cx (halfWeight h)) := by
    unfold cx halfWeight
    exact Complex.ofRealCLM.contDiff.comp
      ((Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul hh)
  have hHc : HasCompactSupport (cx (halfWeight h)) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) fun y hy => ?_
    simp [cx, halfWeight, hsupp y hy]
  have hpl := RHTower.LebesgueAtomWeil.integral_norm_sq_paperFT_eq hH hHc
  have e1 : ∀ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 =
      ‖paperFT (cx (halfWeight h)) τ‖ ^ 2 := fun τ => by
    rw [← paperFT_halfWeight_gammaOf, gammaOf_half_add]
  have e2 : ∫ u : ℝ, ‖cx (halfWeight h) u‖ ^ 2 = ∫ y, Real.exp y * h y ^ 2 := by
    congr 1; funext y
    simp only [cx, halfWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  simp_rw [e1]
  rw [← e2, ← hpl]
  field_simp

/-- The pointwise comparison below the grid, for abstract integrands: the atom factor near the
origin, the Riemann sums on `|τ| ≤ R`, and the common Kuzmin–Landau tail beyond `R`. -/
theorem abs_indicator_sub_le {P Dn Hh : ℝ → ℝ} {I₁s I₀s Cd sw R T₀ Y : ℝ} (hR : 1 ≤ R)
    (hRT : R ≤ T₀) (hI₁ : 0 ≤ I₁s) (hI : I₁s ≤ I₀s) (hCd0 : 0 ≤ Cd) (hsw : 0 ≤ sw)
    (hD0 : ∀ τ, 0 ≤ Dn τ) (hH0 : ∀ τ, 0 ≤ Hh τ) (hP0 : ∀ τ, 0 ≤ P τ) (hPle : ∀ τ, P τ ≤ I₀s)
    (hHle : ∀ τ, Hh τ ≤ Cd / (1 + τ ^ 2)) (hDle : ∀ τ, |τ| ≤ T₀ → Dn τ ≤ Cd / (1 + τ ^ 2))
    (hP1 : ∀ τ, |P τ - I₁s| ≤ 4 * I₀s * (sw * Real.sqrt |τ|))
    (hDH : ∀ τ, |τ| ≤ R → |Dn τ - Hh τ| ≤ Y) (τ : ℝ) :
    |Set.indicator (Set.Icc (-T₀) T₀) (fun τ => P τ * Dn τ) τ - I₁s * Hh τ| ≤
      (8 * I₀s * Cd * sw + 4 * I₀s * Cd / Real.sqrt R) * decayWeight τ +
        Set.indicator (Set.Icc (-R) R) (fun _ => I₀s * Y) τ := by
  have hd0 := decayWeight_nonneg τ
  have hI₀ : 0 ≤ I₀s := hI₁.trans hI
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr (by linarith)
  have hq : 0 ≤ Cd / (1 + τ ^ 2) := by positivity
  by_cases hτR : |τ| ≤ R
  · have hmem : τ ∈ Set.Icc (-T₀) T₀ := abs_le.mp (hτR.trans hRT)
    rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem (show τ ∈ Set.Icc (-R) R from abs_le.mp hτR)]
    have hA1 : |P τ - I₁s| * Dn τ ≤ 8 * I₀s * Cd * sw * decayWeight τ :=
      calc |P τ - I₁s| * Dn τ ≤ (4 * I₀s * (sw * Real.sqrt |τ|)) * (Cd / (1 + τ ^ 2)) :=
            mul_le_mul (hP1 τ) (hDle τ (abs_le.mpr hmem)) (hD0 τ) (by positivity)
        _ = 4 * I₀s * Cd * sw * (Real.sqrt |τ| / (1 + τ ^ 2)) := by ring
        _ ≤ 4 * I₀s * Cd * sw * (2 * decayWeight τ) :=
            mul_le_mul_of_nonneg_left (sqrt_abs_div_le_decayWeight τ) (by positivity)
        _ = 8 * I₀s * Cd * sw * decayWeight τ := by ring
    have hA2 : I₁s * |Dn τ - Hh τ| ≤ I₀s * Y :=
      mul_le_mul hI (hDH τ hτR) (abs_nonneg _) hI₀
    have hsplit : P τ * Dn τ - I₁s * Hh τ = (P τ - I₁s) * Dn τ + I₁s * (Dn τ - Hh τ) := by ring
    have h4 : 0 ≤ 4 * I₀s * Cd / Real.sqrt R * decayWeight τ := by positivity
    rw [hsplit]
    calc |(P τ - I₁s) * Dn τ + I₁s * (Dn τ - Hh τ)| ≤ |P τ - I₁s| * Dn τ + I₁s * |Dn τ - Hh τ| := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_nonneg (hD0 τ), abs_of_nonneg hI₁]
      _ ≤ _ := by nlinarith
  · have hτR' : R < |τ| := not_le.mp hτR
    rw [Set.indicator_of_notMem (show τ ∉ Set.Icc (-R) R from fun hm => hτR (abs_le.mpr hm)),
      add_zero]
    have hf_le : |Set.indicator (Set.Icc (-T₀) T₀) (fun τ => P τ * Dn τ) τ| ≤
        I₀s * (Cd / (1 + τ ^ 2)) := by
      by_cases hm : τ ∈ Set.Icc (-T₀) T₀
      · rw [Set.indicator_of_mem hm, abs_of_nonneg (mul_nonneg (hP0 τ) (hD0 τ))]
        exact mul_le_mul (hPle τ) (hDle τ (abs_le.mpr hm)) (hD0 τ) hI₀
      · rw [Set.indicator_of_notMem hm, abs_zero]; positivity
    have hinv := inv_one_add_sq_le_decayWeight hR hτR'
    have h8 : 0 ≤ 8 * I₀s * Cd * sw * decayWeight τ := by positivity
    have hg : I₁s * Hh τ ≤ I₀s * (Cd / (1 + τ ^ 2)) := mul_le_mul hI (hHle τ) (hH0 τ) hI₀
    have hgn : 0 ≤ I₁s * Hh τ := mul_nonneg hI₁ (hH0 τ)
    have htail : 2 * (I₀s * (Cd / (1 + τ ^ 2))) ≤ 4 * I₀s * Cd / Real.sqrt R * decayWeight τ := by
      have e : 2 * (I₀s * (Cd / (1 + τ ^ 2))) = 2 * I₀s * Cd * (1 + τ ^ 2)⁻¹ := by ring
      rw [e]
      calc 2 * I₀s * Cd * (1 + τ ^ 2)⁻¹ ≤ 2 * I₀s * Cd * (2 / Real.sqrt R * decayWeight τ) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 4 * I₀s * Cd / Real.sqrt R * decayWeight τ := by ring
    calc |Set.indicator (Set.Icc (-T₀) T₀) (fun τ => P τ * Dn τ) τ - I₁s * Hh τ|
        ≤ |Set.indicator (Set.Icc (-T₀) T₀) (fun τ => P τ * Dn τ) τ| + I₁s * Hh τ := by
          refine (abs_sub _ _).trans (le_of_eq ?_); rw [abs_of_nonneg hgn]
      _ ≤ _ := by nlinarith

theorem integral_lowDominator (a X R : ℝ) (hR : 0 ≤ R) :
    ∫ τ, (a * decayWeight τ + Set.indicator (Set.Icc (-R) R) (fun _ => X) τ) =
      a * (∫ τ, decayWeight τ) + X * (2 * R) := by
  rw [integral_add (integrable_decayWeight.const_mul _)
      ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc),
    integral_const_mul, integral_indicator measurableSet_Icc, setIntegral_const,
    measureReal_def, Real.volume_Icc, smul_eq_mul, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- **The part below the grid is sharp.** For `1 ≤ R ≤ N e^{−A}`,
`|∫_{|τ| ≤ N e^{−A}} |φ̂(wτ)|² |D_x|²/N − (∫φ)² ∫ |ĥ(½ + iτ)|²| ≤ K (√(c/N) + R^{−1/2} + R²/N)`. -/
theorem abs_lowPart_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 0 < c → ∀ N : ℕ, 1 ≤ N → ∀ R : ℝ, 1 ≤ R →
      R ≤ N * Real.exp (-A) →
      |lowPart φ h c N A - (∫ u, φ u) ^ 2 *
          ∫ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2| ≤
        K * (Real.sqrt (c / N) + 1 / Real.sqrt R + R ^ 2 / N) := by
  have hφc : HasCompactSupport φ := HasCompactSupport.intro isCompact_Icc fun u hu => hφsupp u hu
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hB0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  obtain ⟨Cd, hCd⟩ : ∃ Cd, Cd = 2 * (Bh ^ 2 * Real.exp A + 16 * Real.pi ^ 2 *
    windowConst A Bh L ^ 2) := ⟨_, rfl⟩
  have hCd0 : 0 ≤ Cd := by rw [hCd]; positivity
  obtain ⟨I₀, hI₀⟩ : ∃ I₀, I₀ = ∫ u, |φ u| := ⟨_, rfl⟩
  have hI₀0 : 0 ≤ I₀ := by rw [hI₀]; exact integral_nonneg fun u => abs_nonneg _
  have hI₁ : (∫ u, φ u) ^ 2 ≤ I₀ ^ 2 := by
    rw [hI₀, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) abs_integral_le_integral_abs 2
  obtain ⟨C₄, hC₄⟩ : ∃ C₄, C₄ = ∫ τ, decayWeight τ := ⟨_, rfl⟩
  have hC₄0 : 0 ≤ C₄ := by rw [hC₄]; exact integral_nonneg decayWeight_nonneg
  obtain ⟨C₅, hC₅⟩ : ∃ C₅, C₅ = ((Lh : ℝ) + 2 * Bh) * Real.exp (2 * A) := ⟨_, rfl⟩
  have hC₅0 : 0 ≤ C₅ := by rw [hC₅]; positivity
  have hHle : ∀ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 ≤ Cd / (1 + τ ^ 2) :=
    fun τ => hCd ▸ normSq_horizonTransform_le hh hA hsupp hB hL τ
  have hHn : ∀ τ : ℝ, ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ≤ Real.sqrt Cd := fun τ =>
    Real.le_sqrt_of_sq_le ((hHle τ).trans (div_le_self hCd0 (by nlinarith [sq_nonneg τ])))
  refine ⟨8 * I₀ ^ 2 * Cd * C₄ + 4 * I₀ ^ 2 * Cd * C₄ +
    2 * I₀ ^ 2 * C₅ * (C₅ + 2 * Real.sqrt Cd), by positivity, fun c hc N hN R hR hRT => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw0 : 0 ≤ c / N := by positivity
  have hRN : R ≤ N := hRT.trans (mul_le_of_le_one_right hN0.le
    (Real.exp_le_one_iff.mpr (by linarith)))
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr (by linarith)
  -- the Riemann-sum error on `|τ| ≤ R`
  have hDH : ∀ τ : ℝ, |τ| ≤ R → |‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N -
      ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2| ≤
        C₅ * R / N * (C₅ + 2 * Real.sqrt Cd) := by
    intro τ hτ
    refine (abs_normSq_div_sub_le hh hA hsupp hB hLh hN τ (hHn τ)).trans ?_
    have hE1 : ((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * Real.exp (2 * A) / N ≤ C₅ * R / N := by
      rw [hC₅]
      refine div_le_div_of_nonneg_right ?_ hN0.le
      rw [mul_assoc, mul_comm _ R, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      have : (Lh : ℝ) ≤ Lh * R := le_mul_of_one_le_right (NNReal.coe_nonneg _) hR
      nlinarith
    have hE2 : C₅ * R / N ≤ C₅ := by
      rw [div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hRN hC₅0
    exact mul_le_mul hE1 (by linarith) (by positivity) (by positivity)
  have hpt := abs_indicator_sub_le (P := fun τ : ℝ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2)
    (Dn := fun τ : ℝ => ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N)
    (Hh := fun τ : ℝ => ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2)
    (I₁s := (∫ u, φ u) ^ 2) (I₀s := I₀ ^ 2) (sw := Real.sqrt (c / N))
    (T₀ := (N : ℝ) * Real.exp (-A)) hR hRT (sq_nonneg _) hI₁ hCd0 (Real.sqrt_nonneg _)
    (fun τ => by positivity) (fun τ => by positivity) (fun τ => by positivity)
    (fun τ => by
      have := RHTower.norm_paperFT_real_le_integral_norm (f := cx φ) (c / N * τ)
      rw [show (((c / N * τ : ℝ)) : ℂ) = ((c / N : ℝ) : ℂ) * τ by push_cast; ring] at this
      have h' : ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ≤ I₀ := by
        rw [hI₀]; simpa [cx, Complex.norm_real, Real.norm_eq_abs] using this
      exact pow_le_pow_left₀ (norm_nonneg _) h' 2)
    hHle (fun τ hτ => hCd ▸ horizonDirichlet_sq_div_le hsupp hA hB hL hN hτ)
    (fun τ => by
      have := abs_normSq_paperFT_sub_le hφ.continuous hφsupp hw0 τ
      rwa [← hI₀, Real.sqrt_mul hw0] at this)
    hDH
  -- integrability
  have hPc : Continuous fun τ : ℝ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 :=
    ((paperFT_cx_continuous hφ.continuous hφc).comp
      (continuous_const.mul Complex.continuous_ofReal)).norm.pow 2
  have hDc : Continuous fun τ : ℝ => ‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N :=
    (continuous_norm_sq_dirichletPoly N _).div_const _
  have hfi : Integrable (Set.indicator (Set.Icc (-((N : ℝ) * Real.exp (-A)))
      ((N : ℝ) * Real.exp (-A))) fun τ : ℝ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (horizonWeights h N) τ‖ ^ 2 / N)) :=
    (hPc.mul hDc).integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hHc : Continuous fun τ : ℝ => ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 := by
    have hHw : Continuous (halfWeight h) :=
      (Real.continuous_exp.comp (continuous_id.div_const 2)).mul hh.continuous
    have hHwc : HasCompactSupport (halfWeight h) :=
      HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) fun y hy => by
        simp [halfWeight, hsupp y hy]
    refine ((paperFT_cx_continuous hHw hHwc).comp Complex.continuous_ofReal).norm.pow 2
      |>.congr fun τ => ?_
    simp only [Function.comp_apply]
    rw [← paperFT_halfWeight_gammaOf, gammaOf_half_add]
    rfl
  have hgi : Integrable fun τ : ℝ => (∫ u, φ u) ^ 2 *
      ‖horizonTransform h (1 / 2 + Complex.I * τ)‖ ^ 2 := by
    refine Integrable.const_mul ?_ _
    refine (integrable_inv_one_add_sq.const_mul Cd).mono' hHc.aestronglyMeasurable
      (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa [div_eq_mul_inv] using hHle τ
  have hei : Integrable fun τ : ℝ => (8 * I₀ ^ 2 * Cd * Real.sqrt (c / N) +
      4 * I₀ ^ 2 * Cd / Real.sqrt R) * decayWeight τ +
        Set.indicator (Set.Icc (-R) R) (fun _ => I₀ ^ 2 * (C₅ * R / N * (C₅ + 2 * Real.sqrt Cd))) τ :=
    (integrable_decayWeight.const_mul _).add
      ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc)
  rw [lowPart, ← integral_indicator measurableSet_Icc, ← integral_const_mul,
    ← integral_sub hfi hgi]
  refine (abs_integral_le_integral_abs).trans ((integral_mono (hfi.sub hgi).abs hei hpt).trans ?_)
  rw [integral_lowDominator _ _ _ (by linarith), ← hC₄]
  have e1 : I₀ ^ 2 * (C₅ * R / N * (C₅ + 2 * Real.sqrt Cd)) * (2 * R) =
      2 * I₀ ^ 2 * C₅ * (C₅ + 2 * Real.sqrt Cd) * (R ^ 2 / N) := by field_simp
  have e2 : (8 * I₀ ^ 2 * Cd * Real.sqrt (c / N) + 4 * I₀ ^ 2 * Cd / Real.sqrt R) * C₄ =
      8 * I₀ ^ 2 * Cd * C₄ * Real.sqrt (c / N) + 4 * I₀ ^ 2 * Cd * C₄ * (1 / Real.sqrt R) := by
    field_simp
  rw [e1, e2]
  have h1 : 0 ≤ Real.sqrt (c / N) := Real.sqrt_nonneg _
  have h2 : 0 ≤ 1 / Real.sqrt R := by positivity
  have h3 : 0 ≤ R ^ 2 / N := by positivity
  have k1 : 0 ≤ 8 * I₀ ^ 2 * Cd * C₄ := by positivity
  have k2 : 0 ≤ 4 * I₀ ^ 2 * Cd * C₄ := by positivity
  have k3 : 0 ≤ 2 * I₀ ^ 2 * C₅ * (C₅ + 2 * Real.sqrt Cd) := by positivity
  nlinarith [mul_nonneg k1 h2, mul_nonneg k1 h3, mul_nonneg k2 h1, mul_nonneg k2 h3,
    mul_nonneg k3 h1, mul_nonneg k3 h2]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
