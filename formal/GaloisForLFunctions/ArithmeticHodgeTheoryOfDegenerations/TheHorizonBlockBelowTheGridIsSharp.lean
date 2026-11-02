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

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
