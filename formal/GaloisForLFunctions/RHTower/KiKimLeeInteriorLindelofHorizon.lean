import GaloisForLFunctions.RHTower.DeBruijnCollisionMassAndCriticalHeat
import GaloisForLFunctions.RHTower.XiSliceHeatRateInteriorLindelof

/-!
# Breaking the `3/2` Heat Horizon: Real and Simple Zeros of `H_t` Above `27/40`

Let `H_t` (`riemannHeat t`) be the de Bruijn–Newman heat deformation of `Ξ`. Differentiating the
one-sided Gaussian average `Q(v) = halfGaussTransform t (xiLine X) v` across the entire interval
`v ∈ [−1/2, 1/2]` gives the Weyl reality and simplicity horizon `3/2`
(`riemannHeat_zeros_real_simple_weyl`): at the left endpoint `v = −1/2`, keeping the saddle
`u(−1/2) = c − 1/2` inside the Euler region forces `c > 1`, and bounding the strip at `v = −1/2`
against Weyl's exponent forces `c > 3/2`.

This module lowers the unconditional reality and simplicity horizon from `3/2 = 1.50` to
`27/40 = 0.675` (`riemannHeat_zeros_real_simple_interiorLindelof`), strictly below `3/4` and `1`,
by combining two mechanisms:

1. **Two-Regime Horizon Decomposition (`re_slope_mul_conj_pos_interior`, `norm_neg_lt_norm_pos_interior`).**
   By `H_t(X + iy) = Q(−y) + conj Q(y)` and reflection symmetry, nonvanishing for `0 < |y| ≤ 1/2`
   and simplicity at `y = 0` reduce to `Re(Q'(0) conj Q(0)) > 0` together with `‖Q(−y)‖ < ‖Q(y)‖`
   for `0 < y ≤ 1/2`:
   * **Regime I (`|v| ≤ δ₀`):** Differentiate `‖Q(v)‖²` only on a narrow near-axis collar
     `[−δ₀, δ₀]`. Because `δ₀` is small, `u(v) = v + c` stays strictly inside `Re s > 1` whenever
     `c > 1/2`, and optimal Gaussian Chernoff tilting (`chernoff_lowerTail_le`) replaces the
     hard-coded `4/3` lower-tail barrier by `c > 1/2`.
   * **Regime II (`δ₀ ≤ y ≤ 1/2`):** Instead of differentiating `Q` at `−y` (where `u(−y)` leaves
     the Euler region), compare both `‖Q(y)‖` and `‖Q(−y)‖` directly against the **same**
     positive-shift Euler anchor `u_+ = y + c > 1/2 + 2η`. On the window, `g_t(w + y) e^{(w − u_+)α}`
     carries the exponential suppression factor `e^{−2yα} ≤ e^{−2δ₀α}`, while on `(0, w₁]` and
     `(W, ∞)` the shift `+y` strictly improves Gaussian decay, yielding `‖Q(−y)‖ ≪ P_+ ≍ ‖Q(y)‖`.

2. **Two-Piece Interior Lindelöf Strip Comparison (`exists_norm_xiLine_le_strip_interiorLindelof`).**
   Replacing `exists_norm_riemannZeta_ge_three_halves` (`u ≥ 1`) by the near-one Euler lower bound
   `inv_le_norm_riemannZeta_saddle` (`u ≥ 1/2 + 2η`) and interpolating `ζ` across `Re s = 5/7` via
   `μ(1/2) ≤ 1/6` and `μ(5/7) ≤ 1/14` (`exists_norm_riemannZeta_le_profile_one`,
   `exists_norm_riemannZeta_le_profile_two`) makes the Gaussian strip exponent negative on all of
   `[0, 1/2]` as soon as `(c − w)² > 4c μ(1/2 + w)`, whose exact threshold is `c > 27/40`.

3. **Small-Time Collision Mass and Nonreal Zero Count Corollary
   (`exists_nonrealZeroCount_and_collisionMass_le_interiorLindelof`).**
   Coupling `riemannHeat_zeros_real_simple_interiorLindelof` with the uniform Jensen disk zero-count
   bound lowers the small-time (`0 < t ≤ 1/8`) exponential radius in the unconditional upper bound
   on `nonrealZeroCount t`, `∑_{s > t} collisionMass s`, and `collisionMass t` from
   `2π e^{(3/2 + ε)/t}` to `2π e^{(27/40 + ε)/t}`.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-! ## 1. Two-piece interior Lindelöf strip exponent and strip comparison -/

/-- Slope of the second Phragmén–Lindelöf chord between `Re s = 5/7` (`w = 3/14`) and
`Re s = 1 + 2η` (`w = 1/2 + 2η`). -/
def interiorStripRateTwo (η : ℝ) : ℝ := (1 / 14 + 2 * η) / (2 / 7 + 2 * η)

/-- Two-piece Lindelöf strip exponent on `[0, 1/2 + 2η]`, interpolating `μ(1/2) ≤ 1/6`,
`μ(5/7) ≤ 1/14`, and `μ(1 + 2η) = 0`. -/
def interiorStripExp (η w : ℝ) : ℝ :=
  if w ≤ 3 / 14 then 1 / 6 + η - 4 / 9 * w
  else interiorStripRateTwo η * (1 / 2 + 2 * η - w)

theorem interiorStripRateTwo_pos {η : ℝ} (hη : 0 ≤ η) : 0 < interiorStripRateTwo η := by
  unfold interiorStripRateTwo; positivity

theorem interiorStripExp_nonneg {η w : ℝ} (hη : 0 ≤ η) (hw : w ≤ 1 / 2 + 2 * η) :
    0 ≤ interiorStripExp η w := by
  unfold interiorStripExp
  split_ifs with h
  · linarith
  · exact mul_nonneg (interiorStripRateTwo_pos hη).le (by linarith)

theorem interiorStripExp_le_half {η w : ℝ} (hη0 : 0 ≤ η) (hη8 : η ≤ 1 / 8)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2 + 2 * η) :
    interiorStripExp η w ≤ 1 / 2 := by
  unfold interiorStripExp
  split_ifs with h
  · linarith
  · have hrate : interiorStripRateTwo η * (1 / 2 + 2 * η - w) ≤
        interiorStripRateTwo η * (2 / 7 + 2 * η) :=
      mul_le_mul_of_nonneg_left (by linarith) (interiorStripRateTwo_pos hη0).le
    have hsimp : interiorStripRateTwo η * (2 / 7 + 2 * η) = 1 / 14 + 2 * η := by
      unfold interiorStripRateTwo
      exact div_mul_cancel₀ _ (by positivity)
    linarith

theorem four_mul_interiorStripExp_piece2_le {η w : ℝ} (hη : 0 ≤ η)
    (hw3 : 3 / 14 ≤ w) (hw1 : w ≤ 1 / 2 + 2 * η) :
    4 * (interiorStripRateTwo η * (1 / 2 + 2 * η - w)) ≤ 1 / 2 - w + 8 * η := by
  have hden : 0 < 2 / 7 + 2 * η := by positivity
  have hsub0 : 0 ≤ 1 / 2 + 2 * η - w := by linarith
  have hsub_le : 1 / 2 + 2 * η - w ≤ 2 / 7 + 2 * η := by linarith
  have hdiff : 4 * (interiorStripRateTwo η * (1 / 2 + 2 * η - w)) - (1 / 2 + 2 * η - w) =
      (6 * η) * ((1 / 2 + 2 * η - w) / (2 / 7 + 2 * η)) := by
    unfold interiorStripRateTwo
    field_simp [hden.ne']
    ring
  have hfrac : (1 / 2 + 2 * η - w) / (2 / 7 + 2 * η) ≤ 1 := (div_le_one hden).mpr hsub_le
  have hmul : (6 * η) * ((1 / 2 + 2 * η - w) / (2 / 7 + 2 * η)) ≤ 6 * η := by
    nlinarith
  linarith

/-- **Two-piece interior Lindelöf strip comparison.**
For `0 < η ≤ 1/4`, `X ≥ 16`, `0 ≤ w ≤ 1/2 + 2η`, and any Euler anchor `1/2 + 2η ≤ u ≤ X`,
`‖xiLine X w‖ ≤ K * X^{interiorStripExp η w} * (X / 2π)^{(w − u)/2} * ‖xiLine X u‖`. -/
theorem exists_norm_xiLine_le_strip_interiorLindelof {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η →
      1 / 2 + 2 * η ≤ u → u ≤ X →
        ‖xiLine X w‖ ≤ K * X ^ (interiorStripExp η w) *
          (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖ := by
  obtain ⟨C₁, hC₁, hp₁⟩ := exists_norm_riemannZeta_le_profile_one hη (by linarith)
  obtain ⟨C₂, hC₂, hp₂⟩ := exists_norm_riemannZeta_le_profile_two (η := 2 * η)
    (by positivity) (by linarith)
  set C := max C₁ C₂
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  set c := 1 / (1 + 1 / (2 * η))
  have hc : 0 < c := by positivity
  refine ⟨2 * Real.exp 6 * C / c, by positivity, fun X w u hX hw0 hwη hu1 huX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hu0 : 0 ≤ u := by linarith
  rw [norm_xiLine_eq_factors hX0 hw0, norm_xiLine_eq_factors hX0 hu0]
  set sw : ℂ := ((w + 1 / 2 : ℝ) : ℂ) + X * I with hsw
  set su : ℂ := ((u + 1 / 2 : ℝ) : ℂ) + X * I with hsu
  set Pw := ‖sw * (sw - 1) / 2‖ with hPw
  set Pu := ‖su * (su - 1) / 2‖ with hPu
  set Gw := ‖Complex.Gamma ((((w + 1 / 2) / 2 : ℝ) : ℂ) + ((X / 2 : ℝ) : ℂ) * I)‖ with hGw
  set Gu := ‖Complex.Gamma ((((u + 1 / 2) / 2 : ℝ) : ℂ) + ((X / 2 : ℝ) : ℂ) * I)‖ with hGu
  set Zw := ‖riemannZeta sw‖ with hZw
  set Zu := ‖riemannZeta su‖ with hZu
  have hsuim : X ≤ ‖su‖ := by
    have := Complex.abs_im_le_norm su; simpa [hsu, abs_of_pos hX0] using this
  have hsu1im : X ≤ ‖su - 1‖ := by
    have := Complex.abs_im_le_norm (su - 1); simpa [hsu, abs_of_pos hX0] using this
  have hsw_le : ‖sw‖ ≤ X + 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0, Complex.norm_I, mul_one]
    linarith
  have hsw1_le : ‖sw - 1‖ ≤ X + 1 := by
    have e : sw - 1 = (((w - 1 / 2 : ℝ)) : ℂ) + X * I := by rw [hsw]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hX0, Complex.norm_I, mul_one]
    have : |w - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hPwu : Pw ≤ 2 * Pu := by
    rw [hPw, hPu, norm_div, norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
    have h1 : ‖sw‖ * ‖sw - 1‖ ≤ (X + 2) * (X + 1) :=
      mul_le_mul hsw_le hsw1_le (norm_nonneg _) (by linarith)
    have h2 : X * X ≤ ‖su‖ * ‖su - 1‖ := mul_le_mul hsuim hsu1im hX0.le (norm_nonneg _)
    have h3 : (X + 2) * (X + 1) ≤ 2 * (X * X) := by nlinarith
    linarith
  have hGamma : Gw ≤ (X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu := by
    have h := norm_Gamma_vertical_le_rpow_mul (a := (w + 1 / 2) / 2) (b := (u + 1 / 2) / 2)
      (y := X / 2) (by linarith) (by linarith) (by linarith)
    have hab : (w + 1 / 2) / 2 - (u + 1 / 2) / 2 = (w - u) / 2 := by ring
    rw [hab] at h
    have hexp : Real.exp (6 * ((u + 1 / 2) / 2 - (w + 1 / 2) / 2) / (X / 2)) ≤ Real.exp 6 := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc Gw ≤ (X / 2) ^ ((w - u) / 2) *
          Real.exp (6 * ((u + 1 / 2) / 2 - (w + 1 / 2) / 2) / (X / 2)) * Gu := h
      _ ≤ (X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu := by gcongr
  have hZw_le : Zw ≤ C * X ^ (interiorStripExp η w) := by
    unfold interiorStripExp
    split_ifs with hw3
    · have h := hp₁ (w + 1 / 2) X (by linarith) (by linarith) (by linarith)
      have e : 1 / 6 + η - 4 / 9 * (w + 1 / 2 - 1 / 2) = 1 / 6 + η - 4 / 9 * w := by ring
      rw [e] at h
      have h' : Zw ≤ C₁ * X ^ (1 / 6 + η - 4 / 9 * w) := by simpa [hZw, hsw] using h
      exact h'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have h := hp₂ (w + 1 / 2) X (by linarith) (by linarith) (by linarith)
      have e : (1 / 14 + 2 * η) * (1 + 2 * η - (w + 1 / 2)) / (2 / 7 + 2 * η) =
          interiorStripRateTwo η * (1 / 2 + 2 * η - w) := by
        unfold interiorStripRateTwo; field_simp; ring
      rw [e] at h
      have h' : Zw ≤ C₂ * X ^ (interiorStripRateTwo η * (1 / 2 + 2 * η - w)) := by
        simpa [hZw, hsw] using h
      exact h'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hZu_ge : c ≤ Zu := by
    have hsad := inv_le_norm_riemannZeta_saddle X hη hu1
    have hsu_eq : (((1 / 2 + u : ℝ) : ℂ) + (X : ℂ) * I) = su := by rw [hsu]; push_cast; ring
    rw [hsu_eq] at hsad
    exact hsad
  have hpi : Real.pi ^ (-((w + 1 / 2) / 2)) =
      Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
  have hpow : (X / 2) ^ ((w - u) / 2) * Real.pi ^ ((u - w) / 2) =
      (X / (2 * Real.pi)) ^ ((w - u) / 2) := by
    have e : (u - w) / 2 = -((w - u) / 2) := by ring
    rw [e, Real.rpow_neg Real.pi_pos.le, ← Real.inv_rpow Real.pi_pos.le,
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  have hPu0 : 0 ≤ Pu := norm_nonneg _
  have hGu0 : 0 ≤ Gu := norm_nonneg _
  have hZw0 : 0 ≤ Zw := norm_nonneg _
  rw [hpi]
  calc Pw * (Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2)) * Gw * Zw
      ≤ (2 * Pu) * (Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2)) *
          ((X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu) * (C * X ^ (interiorStripExp η w)) := by
        gcongr
    _ = 2 * Real.exp 6 * C * X ^ (interiorStripExp η w) *
          ((X / 2) ^ ((w - u) / 2) * Real.pi ^ ((u - w) / 2)) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu) := by ring
    _ = 2 * Real.exp 6 * C * X ^ (interiorStripExp η w) * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu) := by rw [hpow]
    _ ≤ 2 * Real.exp 6 * C * X ^ (interiorStripExp η w) * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu * (Zu / c)) := by
        have h1 : 1 ≤ Zu / c := by rw [le_div_iff₀ hc]; linarith
        have h0 : 0 ≤ Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu := by positivity
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right h0 h1) (by positivity)
    _ = 2 * Real.exp 6 * C / c * X ^ (interiorStripExp η w) *
          (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu * Zu) := by
        field_simp

/-! ## 2. Optimal Chernoff lower tail and unified strip estimates -/

/-- Optimal Gaussian Chernoff lower-tail factor for an anchor separated from `w₁` by `γ ≥ 0`. -/
def chernoffLowerR1 (γ t : ℝ) : ℝ := Real.exp (-(γ ^ 2 / (4 * t)))

/-- **Optimal Chernoff lower tail.** Whenever `1/2 + η' + γ ≤ y + 2tα` (`γ ≥ 0`), choosing the
Chernoff parameter `(y + 2tα − (1/2 + η')) / (2t)` gives exact `e^{−γ²/(4t)}` suppression relative
to `N e^{−tα²}` for every `c > 1/2`. -/
theorem chernoff_lowerTail_le {η' γ t α y N : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (hsep : 1 / 2 + η' + γ ≤ y + 2 * t * α) (hN : 0 ≤ N) :
    N * Real.exp (-((y + 2 * t * α) * α)) *
        ∫ w in Iic (1 / 2 + η' : ℝ), gaussDensity t (w - y) * Real.exp (w * α) ≤
      N * Real.exp (-(t * α ^ 2)) * chernoffLowerR1 γ t := by
  set b := 1 / 2 + η'
  set u := y + 2 * t * α
  set Δ := u - b
  have hΔγ : γ ≤ Δ := by dsimp only [Δ, u, b]; linarith
  have hΔ0 : 0 ≤ Δ := hγ.trans hΔγ
  set lam := Δ / (2 * t)
  have hlam : 0 ≤ lam := div_nonneg hΔ0 (by positivity)
  have h := setIntegral_Iic_gaussDensity_sub_mul_rexp_le ht y α b lam hlam
  calc N * Real.exp (-(u * α)) * ∫ w in Iic b, gaussDensity t (w - y) * Real.exp (w * α)
      ≤ N * Real.exp (-(u * α)) *
          Real.exp (lam * b + y * (α - lam) + t * (α - lam) ^ 2) := by gcongr
    _ = N * Real.exp (-(t * α ^ 2) - Δ ^ 2 / (4 * t)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        dsimp only [lam, Δ, u]
        field_simp [ht.ne']
        ring
    _ ≤ N * Real.exp (-(t * α ^ 2) - γ ^ 2 / (4 * t)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hN
        have hsq : γ ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hγ hΔγ 2
        have hdiv : γ ^ 2 / (4 * t) ≤ Δ ^ 2 / (4 * t) :=
          div_le_div_of_nonneg_right hsq (by positivity)
        linarith
    _ = N * Real.exp (-(t * α ^ 2)) * chernoffLowerR1 γ t := by
        rw [chernoffLowerR1, mul_assoc N, ← Real.exp_add]; ring_nf

/-- **Unified pointwise strip bound against an arbitrary Euler anchor `u`.**
Whenever `-(w − v)² + 4c · interiorStripExp η w + 2c(w − u) + c² ≤ −m`, the Gaussian-weighted
strip value `g_t(w − v) ‖xiLine X w‖` is bounded by `e^{−m/(4t)}` times the `u`-anchored scale. -/
theorem gaussDensity_mul_norm_xiLine_le_anchor {K η m t X v u w : ℝ} (ht : 0 < t)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (interiorStripExp η w) *
        (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 16 ≤ X) (hα : 0 ≤ (horizontalSlope X).re)
    (hu1 : 1 / 2 + 2 * η ≤ u) (huX : u ≤ X)
    (hη0 : 0 ≤ η) (hη8 : η ≤ 1 / 8)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2 + 2 * η)
    (hexp_le : -(w - v) ^ 2 + 4 * (2 * t * (horizontalSlope X).re) * interiorStripExp η w +
      2 * (2 * t * (horizontalSlope X).re) * (w - u) +
      (2 * t * (horizontalSlope X).re) ^ 2 ≤ -m) :
    gaussDensity t (w - v) * ‖xiLine X w‖ ≤
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) *
        Real.exp (-(m / (4 * t))) *
        (‖xiLine X u‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2))) := by
  set α := (horizontalSlope X).re with hαdef
  set c := 2 * t * α with hcdef
  set N := ‖xiLine X u‖ with hN
  have hX0 : 0 < X := by linarith
  have hF := hK X w u hX hw0 hw1 hu1 huX
  have hXe : X / (2 * Real.pi) = Real.exp (2 * α) := by
    have := height_eq hX0
    rw [← hαdef] at this
    rw [this]; field_simp
  have hpow1 : (X / (2 * Real.pi)) ^ ((w - u) / 2) = Real.exp (α * (w - u)) := by
    rw [hXe, ← Real.exp_mul]; congr 1; ring
  have hXsplit : X = (2 * Real.pi) * (X / (2 * Real.pi)) := by field_simp
  set E := interiorStripExp η w with hE
  have hE0 : 0 ≤ E := interiorStripExp_nonneg hη0 hw1
  have hE2 : E ≤ 1 / 2 := interiorStripExp_le_half hη0 hη8 hw0 hw1
  have hpow2 : X ^ E ≤ (2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) * Real.exp (α * (2 * E)) := by
    rw [hXsplit, Real.mul_rpow (by positivity) (by positivity), hXe, ← Real.exp_mul]
    have e : 2 * α * E = α * (2 * E) := by ring
    rw [e]
    gcongr
    · linarith [Real.pi_gt_three]
    · linarith
  have hg : gaussDensity t (w - v) =
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - v) ^ 2 / (4 * t))) := rfl
  have hexp : Real.exp (-((w - v) ^ 2 / (4 * t))) * Real.exp (α * (2 * E)) *
      Real.exp (α * (w - u)) ≤ Real.exp (-(m / (4 * t))) * Real.exp (-(t * α ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hαt : α = c / (2 * t) := by rw [hcdef]; field_simp
    have h4t : 0 < 4 * t := by positivity
    have hL : -((w - v) ^ 2 / (4 * t)) + α * (2 * E) + α * (w - u) =
        (-(w - v) ^ 2 + 4 * c * E + 2 * c * (w - u) + c ^ 2 - c ^ 2) / (4 * t) := by
      rw [hαt]; field_simp; ring
    have hR : -(m / (4 * t)) + -(t * α ^ 2) = (-m - c ^ 2) / (4 * t) := by
      rw [hαt]; field_simp; ring
    rw [hL, hR]
    exact div_le_div_of_nonneg_right (by linarith) h4t.le
  calc gaussDensity t (w - v) * ‖xiLine X w‖
      ≤ ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - v) ^ 2 / (4 * t)))) *
          (K * ((2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) * Real.exp (α * (2 * E))) *
            Real.exp (α * (w - u)) * N) := by
        rw [hg]
        refine mul_le_mul_of_nonneg_left (hF.trans ?_) (by positivity)
        rw [hpow1]
        gcongr
    _ = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) *
          (Real.exp (-((w - v) ^ 2 / (4 * t))) * Real.exp (α * (2 * E)) *
            Real.exp (α * (w - u))) * N := by ring
    _ ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) *
          (Real.exp (-(m / (4 * t))) * Real.exp (-(t * α ^ 2))) * N := by gcongr
    _ = _ := by ring

/-- **The three strip terms for an anchor `u`.** -/
theorem interior_strip_terms_le_anchor {K η m t X v u : ℝ} (ht : 0 < t) (hη : 0 < η)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (interiorStripExp η w) *
        (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 16 ≤ X) (hv : |v| ≤ 1 / 2) (hα : 0 ≤ (horizontalSlope X).re)
    (hu1 : 1 / 2 + 2 * η ≤ u) (huX : u ≤ X) (hη8 : η ≤ 1 / 8)
    (hexp : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      -(w - v) ^ 2 + 4 * (2 * t * (horizontalSlope X).re) * interiorStripExp η w +
        2 * (2 * t * (horizontalSlope X).re) * (w - u) +
        (2 * t * (horizontalSlope X).re) ^ 2 ≤ -m) :
    (∫ w in Ioc (0 : ℝ) (1 / 2 + 2 * η), (|(w - v) / (2 * t)| + ‖horizontalSlope X‖) *
        gaussDensity t (w - v) * ‖xiLine X w‖) ≤
      ‖xiLine X u‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K (2 * η) m t (horizontalSlope X).re ∧
    (∫ w in Ioc (0 : ℝ) (1 / 2 + 2 * η), gaussDensity t (w - v) * ‖xiLine X w‖) ≤
      ‖xiLine X u‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K (2 * η) m t (horizontalSlope X).re ∧
    gaussDensity t (1 / 2 + 2 * η - v) * ‖xiLine X (1 / 2 + 2 * η)‖ ≤
      ‖xiLine X u‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K (2 * η) m t (horizontalSlope X).re := by
  set α := (horizontalSlope X).re
  set P := ‖xiLine X u‖ * Real.exp (-(t * α ^ 2)) with hP
  set Q := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) *
    Real.exp (-(m / (4 * t))) with hQ
  set A := (1 + 2 * η) / (2 * t) + α + 1 with hA
  have hQ0 : 0 ≤ Q := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hA1 : 1 ≤ A := by
    have : 0 ≤ (1 + 2 * η) / (2 * t) := by positivity
    linarith
  have hpt : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η), gaussDensity t (w - v) * ‖xiLine X w‖ ≤ Q * P :=
    fun w hw => gaussDensity_mul_norm_xiLine_le_anchor ht hK hK0 hX hα hu1 huX hη.le hη8
      hw.1 hw.2 (hexp w hw)
  have hslope : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      (|(w - v) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - v) * ‖xiLine X w‖ ≤
        A * (Q * P) := by
    intro w hw
    have hwt : |(w - v) / (2 * t)| ≤ (1 + 2 * η) / (2 * t) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
      gcongr
      rw [abs_le] at hv ⊢
      constructor <;> linarith [hw.1, hw.2]
    have ha := norm_horizontalSlope_le hα
    have hAB : |(w - v) / (2 * t)| + ‖horizontalSlope X‖ ≤ A := by rw [hA]; linarith
    rw [mul_assoc]
    have hGF : 0 ≤ gaussDensity t (w - v) * ‖xiLine X w‖ :=
      mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)
    exact mul_le_mul hAB (hpt w hw) hGF (by linarith)
  have hvol : volume.real (Ioc (0 : ℝ) (1 / 2 + 2 * η)) = 1 / 2 + 2 * η := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hint_bound : ∀ (f : ℝ → ℝ) (B : ℝ), (∀ w, 0 ≤ f w) →
      (∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η), f w ≤ B) →
      ∫ w in Ioc (0 : ℝ) (1 / 2 + 2 * η), f w ≤ (1 / 2 + 2 * η) * B := by
    intro f B hf0 hfB
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := f) (C := B)
      measure_Ioc_lt_top (fun w hw => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 w)]; exact hfB w (Ioc_subset_Icc_self hw))
    rw [hvol] at h
    have := le_abs_self (∫ w in Ioc (0 : ℝ) (1 / 2 + 2 * η), f w)
    rw [← Real.norm_eq_abs] at this
    linarith
  have herr : sharpStripErr K (2 * η) m t α = (1 + 2 * η) * A * Q := by
    rw [sharpStripErr, hA, hQ]
  have hQP : 0 ≤ Q * P := mul_nonneg hQ0 hP0
  refine ⟨?_, ?_, ?_⟩
  · refine (hint_bound _ _ (fun w => mul_nonneg (mul_nonneg (by positivity)
      (gaussDensity_pos ht _).le) (norm_nonneg _)) hslope).trans ?_
    rw [herr]
    have hAQP : 0 ≤ A * (Q * P) := mul_nonneg (by linarith) hQP
    have h2 : (1 / 2 + 2 * η) * (A * (Q * P)) ≤ (1 + 2 * η) * (A * (Q * P)) :=
      mul_le_mul_of_nonneg_right (by linarith) hAQP
    calc (1 / 2 + 2 * η) * (A * (Q * P)) ≤ (1 + 2 * η) * (A * (Q * P)) := h2
      _ = P * ((1 + 2 * η) * A * Q) := by ring
  · refine (hint_bound _ _ (fun w => mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _))
      hpt).trans ?_
    rw [herr]
    have h1 : Q * P ≤ A * (Q * P) := le_mul_of_one_le_left hQP hA1
    nlinarith
  · have h0 := hpt (1 / 2 + 2 * η) ⟨by linarith, le_rfl⟩
    have h1 : Q * P ≤ A * (Q * P) := le_mul_of_one_le_left hQP hA1
    have h2 : A * (Q * P) ≤ (1 + 2 * η) * (A * (Q * P)) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    rw [herr]
    calc gaussDensity t (1 / 2 + 2 * η - v) * ‖xiLine X (1 / 2 + 2 * η)‖ ≤ Q * P := h0
      _ ≤ P * ((1 + 2 * η) * A * Q) := by nlinarith

/-! ## 3. Regime I (near-axis slope positivity) and Regime II (off-axis amplitude dominance) -/

/-- **Regime I: Slope positivity `Re(Q'(v) conj Q(v)) > 0` on the near-axis collar `|v| ≤ δ₀`.** -/
theorem re_slope_mul_conj_pos_interior {K η δ₀ γ m t X v : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hγ : 0 ≤ γ)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (interiorStripExp η w) *
        (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 200 ≤ X) (hvδ : |v| ≤ δ₀) (hδ₀2 : δ₀ ≤ 1 / 2)
    (hα1 : 1 ≤ (horizontalSlope X).re)
    (hsep : 1 / 2 + 2 * η + γ ≤ -δ₀ + 2 * t * (horizontalSlope X).re)
    (hm : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      m ≤ (2 * t * (horizontalSlope X).re - w) ^ 2 -
        4 * (2 * t * (horizontalSlope X).re) * interiorStripExp η w -
        2 * δ₀ * (2 * t * (horizontalSlope X).re))
    (hW9 : 9 / 2 ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)
    (hWX : 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2)
    (hS1 : chernoffLowerR1 γ t + kklR2 t (horizontalSlope X).re + sharpR3 (2 * η) t +
      sharpStripErr K (2 * η) m t (horizontalSlope X).re +
      Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re ≤ 1 / 5)
    (hS2 : 2 * sharpStripErr K (2 * η) m t (horizontalSlope X).re +
      Real.exp (9 / 2 * (1 / (2 * η) + 3)) *
        (kklRC t (horizontalSlope X).re + kklRB t (horizontalSlope X).re) +
      (1 / (2 * η) + 3) * (1 + sharpR3 (2 * η) t) < 18 / 25 * (horizontalSlope X).re) :
    0 < ((∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) * xiLine X w) *
      starRingEnd ℂ (halfGaussTransform t (xiLine X) v)).re := by
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  have hv : |v| ≤ 1 / 2 := hvδ.trans hδ₀2
  have hv_lo : -δ₀ ≤ v := (abs_le.mp hvδ).1
  set a := horizontalSlope X with hadef
  set α := a.re with hαdef
  set u := v + 2 * t * α with hudef
  set N := ‖xiLine X u‖ with hN
  set W := 2 * t * α + α ^ 2 with hWdef
  set η' := 2 * η with hη'
  have hη'pos : 0 < η' := by positivity
  set b := 9 / 2 * (1 / η' + 3) with hbdef
  have hv2 := (abs_le.mp hv).2
  have hWu : u ≤ W := by rw [hudef, hWdef]; nlinarith
  have hu_sep : 1 / 2 + η' + γ ≤ u := by rw [hudef, hη']; linarith
  have hu : u ∈ Icc (1 / 2 + η') (X / 32 - 1 / 2) :=
    ⟨by linarith, hWu.trans hWX⟩
  have hw1W : 1 / 2 + η' ≤ W := hu.1.trans hWu
  have hN0 : 0 ≤ N := norm_nonneg _
  have hNpos : 0 < N := by
    rw [hN, norm_pos_iff]
    unfold xiLine
    rw [xiLine_point]
    exact xi_ne_zero_of_one_lt_re (by simp; linarith [hu.1])
  set P := N * Real.exp (-(t * α ^ 2)) with hP
  have hP0 : 0 < P := by positivity
  have hmodel : ∀ w ∈ Icc (1 / 2 + η') W, ‖xiLine X w - xiLine X u *
      Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
        ‖xiLine X u‖ * Real.exp ((w - u) * a.re) * (Real.exp ((1 / η' + 3) * |w - u|) - 1) :=
    fun w hw => norm_xiLine_sub_model_le_near hX hη'pos hu ⟨hw.1, hw.2.trans hWX⟩
  have hderiv : ∀ w ∈ Icc (1 / 2 + η') W, ‖xiLineDeriv X w - a * xiLine X w‖ ≤
      (1 / η' + 3) * ‖xiLine X w‖ :=
    fun w hw => norm_xiLineDeriv_sub_le_near hX hη'pos hw.1 (hw.2.trans hWX)
  have hQ := norm_halfGaussTransform_sub_main_le ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) (y := v) (by positivity) (by linarith) hw1W hmodel
  have hD := norm_slope_sub_mul_le ht (hasDerivAt_xiLine X) (continuous_xiLineDeriv X)
    (integrable_exp_mul_norm_xiLine ht X) (y := v) (by linarith) hw1W hderiv
  have hT1 := chernoff_lowerTail_le ht hγ hu_sep hN0
  have hT2 := upperTail_le ht hv hN0 (α := α)
  have hT3 := sharp_modelError_le (η := η') (α := α) (y := v) ht hη'pos hN0
  have hM := sharp_windowMass_le (η := η') ht hη'pos hX hu hWX
  have hcX : u ≤ X := by have := hu.2; linarith
  have hexp_strip : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      -(w - v) ^ 2 + 4 * (2 * t * α) * interiorStripExp η w +
        2 * (2 * t * α) * (w - u) + (2 * t * α) ^ 2 ≤ -m := by
    intro w hw
    have hc_sub : 0 ≤ 2 * t * α - w - δ₀ := by linarith [hw.2]
    have hsq : (2 * t * α - w - δ₀) ^ 2 ≤ (2 * t * α - w + v) ^ 2 := by
      nlinarith [hv_lo, hc_sub]
    have hδ0 : 0 ≤ δ₀ := (abs_nonneg v).trans hvδ
    have hid : -(w - v) ^ 2 + 2 * (2 * t * α) * (w - u) + (2 * t * α) ^ 2 =
        -(2 * t * α - w + v) ^ 2 := by rw [hudef]; ring
    have hlow := hm w hw
    nlinarith [hw.1, sq_nonneg δ₀]
  obtain ⟨hSA, hOA, hB1⟩ := interior_strip_terms_le_anchor ht hη hK hK0 (by linarith) hv hα0
    hu.1 hcX hη8 hexp_strip
  have hFWb : ‖xiLine X W‖ ≤ (Real.exp b * N) * Real.exp ((W - u) * (α + 1 / 8)) :=
    norm_xiLine_far_end_le hX hη'pos hu hW9 hWu hWX
  obtain ⟨hSC, hOC, hB2⟩ := far_terms_le_of_bound (b := b) ht ht8 hX hv hα1 hW9 hFWb
  have hph := gaussPhase_ge ht8 ht
  have hmain := norm_main_eq (t := t) (X := X) (y := v) (xiLine X u)
  rw [← hadef, ← hαdef, ← hudef] at hmain
  have hmain' : ‖xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (v * a + t * a ^ 2)‖ = P * Real.exp (-(t * (Real.pi / 4) ^ 2)) := by
    rw [hmain, hP, hN]
  set S₁ := chernoffLowerR1 γ t + kklR2 t α + sharpR3 η' t + sharpStripErr K η' m t α +
    Real.exp b * kklRC t α with hS₁
  set S₂ := 2 * sharpStripErr K η' m t α + Real.exp b * (kklRC t α + kklRB t α) +
    (1 / η' + 3) * (1 + sharpR3 η' t) with hS₂
  refine re_mul_conj_pos_of_estimates (Main := xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (v * a + t * a ^ 2)) (E₁ := P * S₁) (E₂ := P * S₂) hα0 ?_ ?_ ?_ ?_
  · refine hQ.trans ?_
    have e : ‖xiLine X u‖ * Real.exp (-(u * a.re)) *
        ((∫ w in Iic (1 / 2 + η' : ℝ), gaussDensity t (w - v) * Real.exp (w * a.re)) +
          (∫ w in Ioi W, gaussDensity t (w - v) * Real.exp (w * a.re)) +
          ∫ w, gaussDensity t (w - v) * Real.exp (w * a.re) *
            (Real.exp ((1 / η' + 3) * |w - u|) - 1)) =
        N * Real.exp (-(u * α)) * (∫ w in Iic (1 / 2 + η' : ℝ),
            gaussDensity t (w - v) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) * (∫ w in Ioi W, gaussDensity t (w - v) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) *
          ∫ w, gaussDensity t (w - v) * Real.exp (w * α) *
            (Real.exp ((1 / η' + 3) * |w - u|) - 1) := by ring
    rw [e]
    have hOC' : ∫ w in Ioi W, gaussDensity t (w - v) * ‖xiLine X w‖ ≤
        P * (Real.exp b * kklRC t α) := hOC.trans (le_of_eq (by rw [hP]; ring))
    rw [← hudef] at hT1 hT3
    have hsum : P * chernoffLowerR1 γ t + P * kklR2 t α + P * sharpR3 η' t +
        P * sharpStripErr K η' m t α + P * (Real.exp b * kklRC t α) = P * S₁ := by
      rw [hS₁]; ring
    linarith
  · refine hD.trans ?_
    have hSC' : ∫ w in Ioi W, (|(w - v) / (2 * t)| + ‖a‖) * gaussDensity t (w - v) *
        ‖xiLine X w‖ ≤ P * (Real.exp b * kklRC t α) := hSC.trans (le_of_eq (by rw [hP]; ring))
    have hB2' : gaussDensity t (W - v) * ‖xiLine X W‖ ≤ P * (Real.exp b * kklRB t α) :=
      hB2.trans (le_of_eq (by rw [hP]; ring))
    have hM' : (1 / η' + 3) * ∫ w in Ioc (1 / 2 + η') W, gaussDensity t (w - v) * ‖xiLine X w‖ ≤
        (1 / η' + 3) * (P * (1 + sharpR3 η' t)) := by gcongr
    have hsum : P * sharpStripErr K η' m t α + P * (Real.exp b * kklRC t α) +
        P * sharpStripErr K η' m t α + P * (Real.exp b * kklRB t α) +
        (1 / η' + 3) * (P * (1 + sharpR3 η' t)) = P * S₂ := by rw [hS₂]; ring
    linarith
  · rw [hmain']
    have h1 := mul_le_mul_of_nonneg_left hph hP0.le
    have : P * S₁ ≤ P * (1 / 5) := mul_le_mul_of_nonneg_left hS1 hP0.le
    linarith
  · rw [hmain']
    have h1 := mul_le_mul_of_nonneg_left hph hP0.le
    have h2 : P * S₁ ≤ P * (1 / 5) := mul_le_mul_of_nonneg_left hS1 hP0.le
    have h3 : P * S₂ < P * (18 / 25 * α) := mul_lt_mul_of_pos_left hS2 hP0
    have h4 : 18 / 25 * P ≤ P * Real.exp (-(t * (Real.pi / 4) ^ 2)) - P * S₁ := by linarith
    have h5 : α * (18 / 25 * P) ≤ α * (P * Real.exp (-(t * (Real.pi / 4) ^ 2)) - P * S₁) :=
      mul_le_mul_of_nonneg_left h4 hα0
    have h6 : P * (18 / 25 * α) = α * (18 / 25 * P) := by ring
    linarith

/-- **Regime II: Direct off-axis amplitude dominance `‖Q(−y)‖ < ‖Q(y)‖` on `δ₀ ≤ y ≤ 1/2`.**
Both `Q(y)` and `Q(−y)` are estimated against the positive-shift Euler anchor `u_+ = y + 2tα`,
eliminating any need for `−y + 2tα` to enter `Re s > 1`. -/
theorem norm_neg_lt_norm_pos_interior {K η δ₀ γ m t X y : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hδ₀ : 0 < δ₀) (hγ : 0 ≤ γ)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (interiorStripExp η w) *
        (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 200 ≤ X) (hyδ : δ₀ ≤ y) (hy2 : y ≤ 1 / 2)
    (hα1 : 1 ≤ (horizontalSlope X).re)
    (hsep : 1 / 2 + 2 * η + γ ≤ δ₀ + 2 * t * (horizontalSlope X).re)
    (hm : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      m ≤ (2 * t * (horizontalSlope X).re - w) ^ 2 -
        4 * (2 * t * (horizontalSlope X).re) * interiorStripExp η w)
    (hW9 : 9 / 2 ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)
    (hWX : 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2)
    (hS1 : chernoffLowerR1 γ t + kklR2 t (horizontalSlope X).re + sharpR3 (2 * η) t +
      sharpStripErr K (2 * η) m t (horizontalSlope X).re +
      Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re ≤ 1 / 5)
    (hS_neg : sharpStripErr K (2 * η) m t (horizontalSlope X).re +
      Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * (horizontalSlope X).re) * (1 + sharpR3 (2 * η) t) +
      Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re < 18 / 25) :
    ‖halfGaussTransform t (xiLine X) (-y)‖ < ‖halfGaussTransform t (xiLine X) y‖ := by
  have hy0 : 0 ≤ y := hδ₀.le.trans hyδ
  have hy_abs : |y| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, hy2⟩
  have hny_abs : |-y| ≤ 1 / 2 := by rwa [abs_neg]
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  set a := horizontalSlope X with hadef
  set α := a.re with hαdef
  set u := y + 2 * t * α with hudef
  set N := ‖xiLine X u‖ with hN
  set W := 2 * t * α + α ^ 2 with hWdef
  set η' := 2 * η with hη'
  have hη'pos : 0 < η' := by positivity
  set η₁ := 1 / η' + 3 with hη₁
  set b := 9 / 2 * η₁ with hbdef
  have hWu : u ≤ W := by rw [hudef, hWdef]; nlinarith
  have hu_sep : 1 / 2 + η' + γ ≤ u := by rw [hudef, hη']; linarith
  have hu : u ∈ Icc (1 / 2 + η') (X / 32 - 1 / 2) := ⟨by linarith, hWu.trans hWX⟩
  have hw1W : 1 / 2 + η' ≤ W := hu.1.trans hWu
  have hN0 : 0 ≤ N := norm_nonneg _
  have hNpos : 0 < N := by
    rw [hN, norm_pos_iff]; unfold xiLine; rw [xiLine_point]
    exact xi_ne_zero_of_one_lt_re (by simp; linarith [hu.1])
  set P := N * Real.exp (-(t * α ^ 2)) with hP
  have hP0 : 0 < P := by positivity
  have hcX : u ≤ X := by have := hu.2; linarith
  -- 1. Lower bound on `‖Q(y)‖`: `18/25 * P ≤ ‖Q(y)‖`.
  have hmodel : ∀ w ∈ Icc (1 / 2 + η') W, ‖xiLine X w - xiLine X u *
      Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
        ‖xiLine X u‖ * Real.exp ((w - u) * a.re) * (Real.exp (η₁ * |w - u|) - 1) :=
    fun w hw => norm_xiLine_sub_model_le_near hX hη'pos hu ⟨hw.1, hw.2.trans hWX⟩
  have hQy := norm_halfGaussTransform_sub_main_le ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) (y := y) (by positivity) (by linarith) hw1W hmodel
  have hT1 := chernoff_lowerTail_le ht hγ hu_sep hN0
  have hT2 := upperTail_le ht hy_abs hN0 (α := α)
  have hT3 := sharp_modelError_le (η := η') (α := α) (y := y) ht hη'pos hN0
  have hexp_pos : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      -(w - y) ^ 2 + 4 * (2 * t * α) * interiorStripExp η w +
        2 * (2 * t * α) * (w - u) + (2 * t * α) ^ 2 ≤ -m := by
    intro w hw
    have hc_sub : 0 ≤ 2 * t * α - w := by linarith [hw.2, hsep]
    have hsq : (2 * t * α - w) ^ 2 ≤ (2 * t * α - w + y) ^ 2 := by nlinarith [hy0, hc_sub]
    have hid : -(w - y) ^ 2 + 2 * (2 * t * α) * (w - u) + (2 * t * α) ^ 2 =
        -(2 * t * α - w + y) ^ 2 := by rw [hudef]; ring
    linarith [hm w hw]
  obtain ⟨_, hOA_pos, _⟩ := interior_strip_terms_le_anchor ht hη hK hK0 (by linarith) hy_abs hα0
    hu.1 hcX hη8 hexp_pos
  have hFWb : ‖xiLine X W‖ ≤ (Real.exp b * N) * Real.exp ((W - u) * (α + 1 / 8)) :=
    norm_xiLine_far_end_le hX hη'pos hu hW9 hWu hWX
  obtain ⟨_, hOC_pos, _⟩ := far_terms_le_of_bound (b := b) ht ht8 hX hy_abs hα1 hW9 hFWb
  have hQy_low : 18 / 25 * P ≤ ‖halfGaussTransform t (xiLine X) y‖ := by
    set Main := xiLine X u * Complex.exp (-((u : ℂ) * a)) * Complex.exp (y * a + t * a ^ 2)
    have hmain := norm_main_eq (t := t) (X := X) (y := y) (xiLine X u)
    rw [← hadef, ← hαdef, ← hudef] at hmain
    have hmain' : ‖Main‖ = P * Real.exp (-(t * (Real.pi / 4) ^ 2)) := by rw [hmain, hP, hN]
    have hph := mul_le_mul_of_nonneg_left (gaussPhase_ge ht8 ht) hP0.le
    have hOC' : ∫ w in Ioi W, gaussDensity t (w - y) * ‖xiLine X w‖ ≤
        P * (Real.exp b * kklRC t α) := hOC_pos.trans (le_of_eq (by rw [hP]; ring))
    rw [← hudef] at hT1 hT3
    have hdiff : ‖halfGaussTransform t (xiLine X) y - Main‖ ≤ P * (1 / 5) := by
      refine hQy.trans ?_
      have e : ‖xiLine X u‖ * Real.exp (-(u * a.re)) *
          ((∫ w in Iic (1 / 2 + η' : ℝ), gaussDensity t (w - y) * Real.exp (w * a.re)) +
            (∫ w in Ioi W, gaussDensity t (w - y) * Real.exp (w * a.re)) +
            ∫ w, gaussDensity t (w - y) * Real.exp (w * a.re) *
              (Real.exp (η₁ * |w - u|) - 1)) =
          N * Real.exp (-(u * α)) * (∫ w in Iic (1 / 2 + η' : ℝ),
              gaussDensity t (w - y) * Real.exp (w * α)) +
          N * Real.exp (-(u * α)) * (∫ w in Ioi W, gaussDensity t (w - y) * Real.exp (w * α)) +
          N * Real.exp (-(u * α)) *
            ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
              (Real.exp (η₁ * |w - u|) - 1) := by ring
      rw [e]
      have hS1P := mul_le_mul_of_nonneg_left hS1 hP0.le
      linarith
    have htri := norm_sub_norm_le Main (halfGaussTransform t (xiLine X) y)
    rw [norm_sub_rev, hmain'] at htri
    linarith
  -- 2. Upper bound on `‖Q(−y)‖`: split `(0, ∞) = (0, w₁] ∪ (w₁, W] ∪ (W, ∞)` against anchor `u`.
  have hGF_neg := integrable_gaussDensity_sub_mul ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) (-y)
  have hsplit : halfGaussTransform t (xiLine X) (-y) =
      (∫ w in Ioc 0 (1 / 2 + η'), (gaussDensity t (w - (-y)) : ℂ) * xiLine X w) +
      (∫ w in Ioc (1 / 2 + η') W, (gaussDensity t (w - (-y)) : ℂ) * xiLine X w) +
      (∫ w in Ioi W, (gaussDensity t (w - (-y)) : ℂ) * xiLine X w) := by
    unfold halfGaussTransform
    exact setIntegral_Ioi_split (by linarith) hw1W hGF_neg.integrableOn
  -- 2a. Strip `(0, w₁]` at `−y` against `u = y + 2tα`.
  have hexp_neg : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      -(w - (-y)) ^ 2 + 4 * (2 * t * α) * interiorStripExp η w +
        2 * (2 * t * α) * (w - u) + (2 * t * α) ^ 2 ≤ -m := by
    intro w hw
    have hid : -(w - (-y)) ^ 2 + 2 * (2 * t * α) * (w - u) + (2 * t * α) ^ 2 =
        -(2 * t * α - w) ^ 2 - 2 * y * (w + 2 * t * α) - y ^ 2 := by rw [hudef]; ring
    have hc0 : 0 ≤ 2 * t * α := by positivity
    nlinarith [hm w hw, hw.1, hy0, sq_nonneg y]
  obtain ⟨_, hOA_neg, _⟩ := interior_strip_terms_le_anchor ht hη hK hK0 (by linarith) hny_abs hα0
    hu.1 hcX hη8 hexp_neg
  -- 2b. Far `(W, ∞)` at `−y`: `g_t(w + y) ≤ g_t(w − y)` for `w > W > 0` and `y ≥ 0`.
  have hOC_neg : ∫ w in Ioi W, gaussDensity t (w - (-y)) * ‖xiLine X w‖ ≤
      P * (Real.exp b * kklRC t α) := by
    have hGF_pos := (integrable_gaussDensity_sub_mul ht (continuous_xiLine X)
      (integrable_exp_mul_norm_xiLine ht X) y).norm.congr
      (Eventually.of_forall fun w => norm_gauss_mul t y w ht _)
    refine (integral_mono_of_nonneg (Eventually.of_forall fun w =>
      mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)) hGF_pos.integrableOn ?_).trans
      (hOC_pos.trans (le_of_eq (by rw [hP]; ring)))
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
    have hw0 : 0 < w := lt_of_lt_of_le (by linarith) (hW9.trans hw.le)
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    unfold gaussDensity
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have hsq : (w - y) ^ 2 ≤ (w - (-y)) ^ 2 := by nlinarith
    have hdiv : (w - y) ^ 2 / (4 * t) ≤ (w - (-y)) ^ 2 / (4 * t) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    linarith
  -- 2c. Window `(w₁, W]` at `−y`: shift mismatch from `u = y + 2tα` gives `e^{η₁ − 2δ₀α}`.
  have hWin_neg : ∫ w in Ioc (1 / 2 + η') W, gaussDensity t (w - (-y)) * ‖xiLine X w‖ ≤
      P * (Real.exp (η₁ - 2 * δ₀ * α) * (1 + sharpR3 η' t)) := by
    set u_neg := -y + 2 * t * α
    have hη₁0 : 0 ≤ η₁ := by positivity
    have hint1 := integrable_gaussDensity_sub_mul_rexp ht (-y) α
    have hint2 := integrable_modelError ht (-y) α u_neg η₁ hη₁0
    have hmaj : Integrable (fun w => N * Real.exp (-(u * α)) * Real.exp η₁ *
        (gaussDensity t (w - (-y)) * Real.exp (w * α) +
          gaussDensity t (w - (-y)) * Real.exp (w * α) * (Real.exp (η₁ * |w - u_neg|) - 1))) :=
      (hint1.add hint2).const_mul _
    have hnonneg : ∀ w, 0 ≤ N * Real.exp (-(u * α)) * Real.exp η₁ *
        (gaussDensity t (w - (-y)) * Real.exp (w * α) +
          gaussDensity t (w - (-y)) * Real.exp (w * α) * (Real.exp (η₁ * |w - u_neg|) - 1)) := by
      intro w
      have h1 : 1 ≤ Real.exp (η₁ * |w - u_neg|) := Real.one_le_exp (by positivity)
      have := gaussDensity_sub_mul_rexp_nonneg ht (-y) α w
      positivity
    calc ∫ w in Ioc (1 / 2 + η') W, gaussDensity t (w - (-y)) * ‖xiLine X w‖
        ≤ ∫ w in Ioc (1 / 2 + η') W, N * Real.exp (-(u * α)) * Real.exp η₁ *
            (gaussDensity t (w - (-y)) * Real.exp (w * α) +
              gaussDensity t (w - (-y)) * Real.exp (w * α) *
                (Real.exp (η₁ * |w - u_neg|) - 1)) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun w =>
            mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)) hmaj.integrableOn ?_
          refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun w hw => ?_)
          have hm_w := hmodel w (Ioc_subset_Icc_self hw)
          have hn : ‖xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * a)‖ =
              N * Real.exp ((w - u) * α) := by
            rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
          have htri := norm_sub_norm_le (xiLine X w)
            (xiLine X u * Complex.exp (((w - u : ℝ) : ℂ) * a))
          rw [hn] at htri
          have hFw : ‖xiLine X w‖ ≤ N * Real.exp ((w - u) * α) * Real.exp (η₁ * |w - u|) := by
            nlinarith
          have habs_le : |w - u| ≤ |w - u_neg| + 1 := by
            have heq : w - u = (w - u_neg) + (-2 * y) := by dsimp only [u_neg]; rw [hudef]; ring
            have h2y : |-2 * y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
            calc |w - u| = |(w - u_neg) + (-2 * y)| := by rw [heq]
              _ ≤ |w - u_neg| + |-2 * y| := abs_add_le _ _
              _ ≤ |w - u_neg| + 1 := by linarith
          have hexp_abs : Real.exp (η₁ * |w - u|) ≤ Real.exp η₁ * Real.exp (η₁ * |w - u_neg|) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by nlinarith)
          have hsplit_exp : Real.exp ((w - u) * α) = Real.exp (-(u * α)) * Real.exp (w * α) := by
            rw [← Real.exp_add]; ring_nf
          have hG := (gaussDensity_pos ht (w - (-y))).le
          calc gaussDensity t (w - (-y)) * ‖xiLine X w‖
              ≤ gaussDensity t (w - (-y)) * (N * (Real.exp (-(u * α)) * Real.exp (w * α)) *
                  (Real.exp η₁ * Real.exp (η₁ * |w - u_neg|))) := by
                rw [hsplit_exp] at hFw
                exact mul_le_mul_of_nonneg_left
                  (hFw.trans (mul_le_mul_of_nonneg_left hexp_abs (by positivity))) hG
            _ = _ := by ring
      _ ≤ ∫ w, N * Real.exp (-(u * α)) * Real.exp η₁ *
            (gaussDensity t (w - (-y)) * Real.exp (w * α) +
              gaussDensity t (w - (-y)) * Real.exp (w * α) *
                (Real.exp (η₁ * |w - u_neg|) - 1)) :=
          setIntegral_le_integral hmaj (Eventually.of_forall hnonneg)
      _ = Real.exp (η₁ - 2 * y * α) *
            ((N * Real.exp (-(u_neg * α)) * ∫ w, gaussDensity t (w - (-y)) * Real.exp (w * α)) +
              (N * Real.exp (-(u_neg * α)) * ∫ w, gaussDensity t (w - (-y)) * Real.exp (w * α) *
                (Real.exp (η₁ * |w - u_neg|) - 1))) := by
          rw [integral_const_mul, integral_add hint1 hint2]
          have hexp_shift : Real.exp (-(u * α)) * Real.exp η₁ =
              Real.exp (η₁ - 2 * y * α) * Real.exp (-(u_neg * α)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1; dsimp only [u_neg]; rw [hudef]; ring
          rw [mul_assoc (N : ℝ), hexp_shift]
          ring
      _ ≤ Real.exp (η₁ - 2 * δ₀ * α) *
            (N * Real.exp (-(t * α ^ 2)) + N * Real.exp (-(t * α ^ 2)) * sharpR3 η' t) := by
          have htilt : N * Real.exp (-(u_neg * α)) *
              ∫ w, gaussDensity t (w - (-y)) * Real.exp (w * α) = N * Real.exp (-(t * α ^ 2)) := by
            dsimp only [u_neg]; exact tiltedMass_eq ht
          have hme := sharp_modelError_le (η := η') (α := α) (y := -y) (N := N) ht hη'pos hN0
          have hexp_δ : Real.exp (η₁ - 2 * y * α) ≤ Real.exp (η₁ - 2 * δ₀ * α) :=
            Real.exp_le_exp.mpr (by nlinarith)
          rw [htilt]
          refine mul_le_mul hexp_δ (add_le_add le_rfl hme) ?_ (Real.exp_pos _).le
          exact add_nonneg (by positivity)
            (mul_nonneg (by positivity) (integral_nonneg fun w => mul_nonneg
              (gaussDensity_sub_mul_rexp_nonneg ht (-y) α w)
              (by linarith [Real.one_le_exp (show 0 ≤ η₁ * |w - u_neg| by positivity)])))
      _ = P * (Real.exp (η₁ - 2 * δ₀ * α) * (1 + sharpR3 η' t)) := by rw [hP]; ring
  -- Combine the three pieces of `‖Q(−y)‖`.
  have hQneg_le : ‖halfGaussTransform t (xiLine X) (-y)‖ ≤
      P * (sharpStripErr K η' m t α + Real.exp (η₁ - 2 * δ₀ * α) * (1 + sharpR3 η' t) +
        Real.exp b * kklRC t α) := by
    rw [hsplit]
    have hn1 : ‖∫ w in Ioc 0 (1 / 2 + η'), (gaussDensity t (w - (-y)) : ℂ) * xiLine X w‖ ≤
        ∫ w in Ioc 0 (1 / 2 + η'), gaussDensity t (w - (-y)) * ‖xiLine X w‖ :=
      (norm_integral_le_integral_norm _).trans
        (le_of_eq (by congr 1; funext w; exact norm_gauss_mul t (-y) w ht _))
    have hn2 : ‖∫ w in Ioc (1 / 2 + η') W, (gaussDensity t (w - (-y)) : ℂ) * xiLine X w‖ ≤
        ∫ w in Ioc (1 / 2 + η') W, gaussDensity t (w - (-y)) * ‖xiLine X w‖ :=
      (norm_integral_le_integral_norm _).trans
        (le_of_eq (by congr 1; funext w; exact norm_gauss_mul t (-y) w ht _))
    have hn3 : ‖∫ w in Ioi W, (gaussDensity t (w - (-y)) : ℂ) * xiLine X w‖ ≤
        ∫ w in Ioi W, gaussDensity t (w - (-y)) * ‖xiLine X w‖ :=
      (norm_integral_le_integral_norm _).trans
        (le_of_eq (by congr 1; funext w; exact norm_gauss_mul t (-y) w ht _))
    have htri : ‖(∫ w in Ioc 0 (1 / 2 + η'), (gaussDensity t (w - (-y)) : ℂ) * xiLine X w) +
        (∫ w in Ioc (1 / 2 + η') W, (gaussDensity t (w - (-y)) : ℂ) * xiLine X w) +
        (∫ w in Ioi W, (gaussDensity t (w - (-y)) : ℂ) * xiLine X w)‖ ≤
        (∫ w in Ioc 0 (1 / 2 + η'), gaussDensity t (w - (-y)) * ‖xiLine X w‖) +
        (∫ w in Ioc (1 / 2 + η') W, gaussDensity t (w - (-y)) * ‖xiLine X w‖) +
        (∫ w in Ioi W, gaussDensity t (w - (-y)) * ‖xiLine X w‖) :=
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
        (add_le_add (add_le_add hn1 hn2) hn3)
    exact htri.trans (by linarith)
  have hlt_P := mul_lt_mul_of_pos_left hS_neg hP0
  linarith

/-! ## 4. Parameter choice above `27/40`, asymptotic error decay, and horizon assembly -/

/-- **Parameters for the `27/40` interior Lindelöf horizon.**
For every `c₀ > 27/40`, there exist `η, δ₀, m > 0` such that:
* the near-axis collar `|v| ≤ δ₀` keeps `v + c ≥ 1/2 + 2η + 1/10` for all `c ≥ c₀`; and
* `(c − w)² − 4c · interiorStripExp η w − 2δ₀ c ≥ m` on `[0, 1/2 + 2η]` for all `c ≥ c₀`. -/
theorem exists_interiorLindelof_params {c₀ : ℝ} (hc₀ : 27 / 40 < c₀) :
    ∃ η δ₀ m : ℝ, 0 < η ∧ η ≤ 1 / 40 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 40 ∧ 0 < m ∧
      1 / 2 + 2 * η + 1 / 10 ≤ -δ₀ + c₀ ∧
      (∀ c : ℝ, c₀ ≤ c → ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
        m ≤ (c - w) ^ 2 - 4 * c * interiorStripExp η w - 2 * δ₀ * c) := by
  set d := c₀ - 27 / 40 with hd
  have hd0 : 0 < d := by linarith
  set η := min (1 / 40) (d / 40) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη40 : η ≤ 1 / 40 := min_le_left _ _
  have hηd : η ≤ d / 40 := min_le_right _ _
  refine ⟨η, η, d / 4, hη0, hη40, hη0, hη40, by positivity, by linarith, fun c hc w hw => ?_⟩
  have hc_pos : 1 / 2 ≤ c := by linarith
  have hcd : d ≤ c - 27 / 40 := by linarith
  unfold interiorStripExp
  split_ifs with hw3
  · have hid : (c - w) ^ 2 - 4 * c * (1 / 6 + η - 4 / 9 * w) - 2 * η * c =
        (w - c / 9) ^ 2 + c * (80 / 81 * (c - 27 / 40) - 6 * η) := by ring
    rw [hid]
    have hgap : d / 2 ≤ 80 / 81 * (c - 27 / 40) - 6 * η := by linarith
    nlinarith [sq_nonneg (w - c / 9), mul_le_mul hc_pos hgap (by positivity) (by linarith)]
  · have hp2 := four_mul_interiorStripExp_piece2_le hη0.le (le_of_not_ge hw3) hw.2
    have hmul : 4 * c * (interiorStripRateTwo η * (1 / 2 + 2 * η - w)) ≤
        c * (1 / 2 - w + 8 * η) := by
      have := mul_le_mul_of_nonneg_left hp2 (by linarith : 0 ≤ c)
      linarith
    have hid : (c - w) ^ 2 - c * (1 / 2 - w + 8 * η) - 2 * η * c =
        (w - c / 2) ^ 2 + c * (3 / 4 * (c - 2 / 3) - 10 * η) := by ring
    have hgap : d / 2 ≤ 3 / 4 * (c - 2 / 3) - 10 * η := by linarith
    nlinarith [sq_nonneg (w - c / 2), mul_le_mul hc_pos hgap (by positivity) (by linarith)]

/-- Explicit bounds on the window and strip error terms for `c₀ / (2α) ≤ t ≤ 20 / α` at any
`c₀ ≥ 1/2`. -/
theorem interior_error_bounds {c₀ η' γ m K α t : ℝ} (hη' : 0 < η') (hη'4 : η' ≤ 1 / 4)
    (hγ : 0 ≤ γ) (hm : 0 < m) (hK0 : 0 ≤ K) (hc₀ : 1 / 2 ≤ c₀) (hα : 160 ≤ α)
    (hη₁ : 20 * (1 / η' + 3) ^ 2 ≤ α) (ht1 : c₀ / (2 * α) ≤ t) (ht2 : t ≤ 20 / α) :
    chernoffLowerR1 γ t ≤ Real.exp (-(γ ^ 2 / 80) * α) ∧
    kklR2 t α ≤ Real.exp (-α ^ 2 + 1) ∧
    sharpR3 η' t ≤ 2 * (1 / η' + 3) * Real.sqrt (20 / α) * Real.exp 4 ∧
    sharpStripErr K η' m t α ≤ 40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) ∧
    kklRC t α ≤ 16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) ∧
    kklRB t α ≤ 2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
      (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α) := by
  have hα0 : 0 < α := by linarith
  have hc0 : 0 < c₀ := by linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
  have htα : t * α ≤ 20 := (le_div_iff₀ hα0).mp ht2
  have hinvt : 1 / t ≤ 2 * α / c₀ := by rw [div_le_div_iff₀ ht0 hc0]; linarith
  have hinvt2 : α / 20 ≤ 1 / t := by rw [div_le_div_iff₀ (by norm_num) ht0]; linarith
  have hinvt_le : 1 / t ≤ 4 * α := by
    refine hinvt.trans ?_
    rw [div_le_iff₀ hc0]; nlinarith
  have hg : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) ≤ 2 * α := by
    refine (rpow_neg_half_le_one_add_inv (by positivity)).trans ?_
    have hpi := Real.pi_gt_three
    have h1 : (4 * Real.pi * t)⁻¹ ≤ α := by
      have : (4 * Real.pi * t)⁻¹ = (4 * Real.pi)⁻¹ * (1 / t) := by field_simp
      rw [this]
      have h4pi : (4 * Real.pi)⁻¹ ≤ 1 / 12 := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      nlinarith [mul_le_mul h4pi hinvt_le (by positivity) (by norm_num)]
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold chernoffLowerR1
    apply Real.exp_le_exp.mpr
    have : γ ^ 2 / 80 * α ≤ γ ^ 2 / (4 * t) := by
      rw [show γ ^ 2 / (4 * t) = γ ^ 2 / 4 * (1 / t) by field_simp]
      have := mul_le_mul_of_nonneg_left hinvt2 (by positivity : 0 ≤ γ ^ 2 / 4)
      linarith
    linarith
  · unfold kklR2
    apply Real.exp_le_exp.mpr
    have ht8 : t ≤ 1 / 8 := ht2.trans (by rw [div_le_iff₀ hα0]; linarith)
    linarith
  · unfold sharpR3
    set η₁ := 1 / η' + 3
    have hη₁0 : 0 ≤ η₁ := by positivity
    have hst : Real.sqrt t ≤ Real.sqrt (20 / α) := Real.sqrt_le_sqrt ht2
    have hsmall : η₁ * Real.sqrt (20 / α) ≤ 1 := by
      have h1 : η₁ ^ 2 * (20 / α) ≤ 1 := by rw [mul_div_assoc', div_le_one hα0]; linarith
      rw [show η₁ * Real.sqrt (20 / α) = Real.sqrt (η₁ ^ 2 * (20 / α)) by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hη₁0]]
      exact (Real.sqrt_le_sqrt h1).trans Real.sqrt_one.le
    have hexp : t * (1 / Real.sqrt t + η₁) ^ 2 = (1 + η₁ * Real.sqrt t) ^ 2 := by
      have h : (Real.sqrt t) ^ 2 * (1 / Real.sqrt t + η₁) ^ 2 = (1 + η₁ * Real.sqrt t) ^ 2 := by
        field_simp
      rwa [Real.sq_sqrt ht0.le] at h
    rw [hexp]
    have hle : (1 + η₁ * Real.sqrt t) ^ 2 ≤ 4 := by
      have : η₁ * Real.sqrt t ≤ 1 := (mul_le_mul_of_nonneg_left hst hη₁0).trans hsmall
      have : 0 ≤ η₁ * Real.sqrt t := by positivity
      nlinarith
    exact mul_le_mul (mul_le_mul_of_nonneg_left hst (by positivity))
      (Real.exp_le_exp.mpr hle) (by positivity) (by positivity)
  · unfold sharpStripErr
    have hfac1 : (1 + η') / (2 * t) + α + 1 ≤ 5 * α := by
      have : (1 + η') / (2 * t) ≤ 3 * α := by
        rw [show (1 + η') / (2 * t) = (1 + η') / 2 * (1 / t) by field_simp]
        have := mul_le_mul_of_nonneg_left hinvt_le (by positivity : 0 ≤ (1 + η') / 2)
        nlinarith
      linarith
    have hfac2 : (2 * Real.pi) ^ ((1 / 2 + η') / 2) ≤ 2 * Real.pi :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)).trans
        (Real.rpow_one _).le
    have hfac3 : Real.exp (-(m / (4 * t))) ≤ Real.exp (-(m / 80) * α) := by
      apply Real.exp_le_exp.mpr
      have : m / 80 * α ≤ m / (4 * t) := by
        rw [show m / (4 * t) = m / 4 * (1 / t) by field_simp]
        have := mul_le_mul_of_nonneg_left hinvt2 (by positivity : 0 ≤ m / 4)
        linarith
      linarith
    have hη1 : 1 + η' ≤ 2 := by linarith
    calc (1 + η') * ((1 + η') / (2 * t) + α + 1) * ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K *
          (2 * Real.pi) ^ ((1 / 2 + η') / 2) * Real.exp (-(m / (4 * t))))
        ≤ 2 * (5 * α) * ((2 * α) * K * (2 * Real.pi) * Real.exp (-(m / 80) * α)) := by gcongr
      _ = 40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) := by ring
  · unfold kklRC
    have hfac : 1 / (2 * t) + α + 1 ≤ 4 * α := by
      rw [show 1 / (2 * t) = 1 / 2 * (1 / t) by field_simp]
      linarith
    have ht8 : t ≤ 1 / 8 := ht2.trans (by rw [div_le_iff₀ hα0]; linarith)
    have hexp : -(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t ≤
        -(15 / 8) * α ^ 2 + 20 * α + 164 := by
      have : t * α ^ 2 ≤ 20 * α := by nlinarith
      nlinarith
    calc 2 * Real.exp 1 * 2 * (1 / (2 * t) + α + 1) *
          Real.exp (-(15 / 8) * α ^ 2 + t * α ^ 2 + 15 / 16 + 8 * t * α + 18 * t)
        ≤ 2 * Real.exp 1 * 2 * (4 * α) * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) := by gcongr
      _ = _ := by ring
  · unfold kklRB
    have hexp : -((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + t * α ^ 2 ≤
        -((α ^ 2 - 1 / 2) ^ 2 * α / 80) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α := by
      have h1 : (α ^ 2 - 1 / 2) ^ 2 * α / 80 ≤ (α ^ 2 - 1 / 2) ^ 2 / (4 * t) := by
        rw [show (α ^ 2 - 1 / 2) ^ 2 / (4 * t) = (α ^ 2 - 1 / 2) ^ 2 / 4 * (1 / t) by field_simp]
        have := mul_le_mul_of_nonneg_left hinvt2 (by positivity : 0 ≤ (α ^ 2 - 1 / 2) ^ 2 / 4)
        nlinarith
      have h2 : t * α ^ 2 ≤ 20 * α := by nlinarith
      linarith
    calc (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-((α ^ 2 - 1 / 2) ^ 2 / (4 * t)) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + t * α ^ 2)
        ≤ (2 * α) * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
            (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α) := by gcongr
      _ = _ := by ring

private theorem self_le_exp_interior (x : ℝ) : x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

/-- Asymptotic smallness of all Regime I and Regime II error envelopes as `α → ∞`. -/
theorem eventually_interior_errors_small {η' δ₀ γ m K b : ℝ} (hη' : 0 < η') (hδ₀ : 0 < δ₀)
    (hγ : 0 < γ) (hm : 0 < m) :
    ∀ᶠ α : ℝ in atTop, 160 ≤ α ∧ 20 * (1 / η' + 3) ^ 2 ≤ α ∧
      Real.exp (-(γ ^ 2 / 80) * α) + Real.exp (-α ^ 2 + 1) +
        2 * (1 / η' + 3) * Real.sqrt (20 / α) * Real.exp 4 +
        40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp b * (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) ≤ 1 / 5 ∧
      2 * (40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α)) +
        Real.exp b * (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
          2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
            (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) +
        (1 / η' + 3) * (1 + 2 * (1 / η' + 3) * Real.sqrt (20 / α) * Real.exp 4) <
        18 / 25 * α ∧
      40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp (1 / η' + 3 - 2 * δ₀ * α) *
          (1 + 2 * (1 / η' + 3) * Real.sqrt (20 / α) * Real.exp 4) +
        Real.exp b * (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) <
        18 / 25 := by
  set η₁ := 1 / η' + 3
  have t1 : Tendsto (fun α : ℝ => Real.exp (-(γ ^ 2 / 80) * α)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h0 : Tendsto (fun α : ℝ => γ ^ 2 / 80 * α) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    exact (tendsto_neg_atTop_atBot.comp h0).congr fun α => by ring
  have t2 : Tendsto (fun α : ℝ => Real.exp (-α ^ 2 + 1)) atTop (𝓝 0) := by
    refine (tendsto_mul_exp_quadratic 1 (c := 1) one_pos 0 1).congr fun α => ?_
    simp only [one_mul, zero_mul, add_zero]; ring_nf
  have t3 : Tendsto (fun α : ℝ => 2 * η₁ * Real.sqrt (20 / α) * Real.exp 4) atTop (𝓝 0) := by
    have h1 : Tendsto (fun α : ℝ => 20 / α) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    simpa [mul_assoc] using (h2.const_mul (2 * η₁)).mul_const (Real.exp 4)
  have t4 : Tendsto (fun α : ℝ => 40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun α : ℝ => m / 80 * α) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    have h2 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp h1
    have h3 := h2.const_mul (40 * Real.pi * K * (80 / m) ^ 2)
    rw [mul_zero] at h3
    refine h3.congr fun α => ?_
    simp only [Function.comp]; field_simp
  have t5 : Tendsto (fun α : ℝ => Real.exp b *
      (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164))) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic (Real.exp b * 16 * Real.exp 1) (c := 15 / 8)
      (by norm_num) 21 164 ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with α _
      positivity
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with α _
      have h1 : α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) ≤
          Real.exp (164 + 21 * α - 15 / 8 * α ^ 2) := by
        calc α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)
            ≤ Real.exp α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) := by
              gcongr; exact self_le_exp_interior α
          _ = _ := by rw [← Real.exp_add]; congr 1; ring
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ Real.exp b * 16 * Real.exp 1)
      calc Real.exp b * (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164))
          = Real.exp b * 16 * Real.exp 1 * (α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) := by
            ring
        _ ≤ _ := h2
  have t6 : Tendsto (fun α : ℝ => Real.exp b * (2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
      (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α))) atTop (𝓝 0) := by
    refine tendsto_of_le_mul_exp_quadratic (2 * Real.exp b) (c := 1) one_pos 0 0 ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with α _
      positivity
    · filter_upwards [eventually_ge_atTop (100 : ℝ)] with α hα
      have hpoly : -((α ^ 2 - 1 / 2) ^ 2 * α / 80) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α + α ≤
          0 + 0 * α - 1 * α ^ 2 := by
        have ha2 : α ^ 2 / 2 ≤ α ^ 2 - 1 / 2 := by nlinarith
        have hsq : (α ^ 2 / 2) ^ 2 ≤ (α ^ 2 - 1 / 2) ^ 2 := by
          have : 0 ≤ α ^ 2 / 2 := by positivity
          nlinarith
        have h5 : α ^ 5 / 320 ≤ (α ^ 2 - 1 / 2) ^ 2 * α / 80 := by
          have := mul_le_mul_of_nonneg_right hsq (by linarith : (0 : ℝ) ≤ α)
          nlinarith
        have h3 : (α ^ 2 + 1 / 2) * (α + 1 / 8) ≤ 4 * α ^ 3 := by nlinarith
        have h6 : 4 * α ^ 3 + 21 * α + α ^ 2 ≤ α ^ 5 / 320 := by
          have hα2 : 10000 ≤ α ^ 2 := by nlinarith
          have hα3 : 0 ≤ α ^ 3 := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hα2 hα3]
        linarith
      have h1 : 2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
          (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α) ≤ 2 * Real.exp (0 + 0 * α - 1 * α ^ 2) := by
        calc 2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
              (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)
            ≤ 2 * (Real.exp α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
                (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) := by
              rw [mul_assoc]; gcongr; exact self_le_exp_interior α
          _ = 2 * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
                (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α + α) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ 2 * Real.exp (0 + 0 * α - 1 * α ^ 2) := by gcongr
      calc Real.exp b * (2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
            (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α))
          ≤ Real.exp b * (2 * Real.exp (0 + 0 * α - 1 * α ^ 2)) := by gcongr
        _ = 2 * Real.exp b * Real.exp (0 + 0 * α - 1 * α ^ 2) := by ring
  have t7 : Tendsto (fun α : ℝ => Real.exp (η₁ - 2 * δ₀ * α)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h0 : Tendsto (fun α : ℝ => 2 * δ₀ * α) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    exact (tendsto_const_nhds.sub_atTop h0).congr fun α => rfl
  have e1 := t1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e2 := t2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e3 := t3.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e4 := t4.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e5 := t5.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e6 := t6.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  have e7 := t7.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 25))
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, eventually_ge_atTop (160 : ℝ),
    eventually_ge_atTop (20 * η₁ ^ 2), eventually_gt_atTop (25 / 18 * (2 * η₁ + 1))]
    with α h1 h2 h3 h4 h5 h6 h7 h160 hη₁α hbig
  have hη₁0 : 0 ≤ η₁ := by positivity
  refine ⟨h160, hη₁α, by linarith, ?_, ?_⟩
  · have h3' : η₁ * (1 + 2 * η₁ * Real.sqrt (20 / α) * Real.exp 4) ≤ η₁ * (1 + 1) := by
      gcongr; linarith
    have hsplit : Real.exp b * (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
        2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) + (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) =
        Real.exp b * (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) +
        Real.exp b * (2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
          (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) := by ring
    rw [hsplit]
    linarith
  · have h7' : Real.exp (η₁ - 2 * δ₀ * α) *
        (1 + 2 * η₁ * Real.sqrt (20 / α) * Real.exp 4) ≤ (1 / 25) * 2 := by
      exact mul_le_mul h7.le (by linarith) (by positivity) (by norm_num)
    linarith

/-- **Large-height collar slope positivity and full-strip nonvanishing above `27/40`.** -/
theorem re_slope_zero_and_ne_zero_interiorLindelof {c₀ η δ₀ m K α₀ t X : ℝ}
    (hη : 0 < η) (hη40 : η ≤ 1 / 40) (hδ₀ : 0 < δ₀) (hδ₀40 : δ₀ ≤ 1 / 40) (hm : 0 < m)
    (hc₀ : 27 / 40 < c₀)
    (hsep : 1 / 2 + 2 * η + 1 / 10 ≤ -δ₀ + c₀)
    (hmc : ∀ c : ℝ, c₀ ≤ c → ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      m ≤ (c - w) ^ 2 - 4 * c * interiorStripExp η w - 2 * δ₀ * c)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (interiorStripExp η w) *
        (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K)
    (hα₀ : ∀ α ≥ α₀, 160 ≤ α ∧ 20 * (1 / (2 * η) + 3) ^ 2 ≤ α ∧
      Real.exp (-((1 / 10 : ℝ) ^ 2 / 80) * α) + Real.exp (-α ^ 2 + 1) +
        2 * (1 / (2 * η) + 3) * Real.sqrt (20 / α) * Real.exp 4 +
        40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp (9 / 2 * (1 / (2 * η) + 3)) *
          (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) ≤ 1 / 5 ∧
      2 * (40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α)) +
        Real.exp (9 / 2 * (1 / (2 * η) + 3)) *
          (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
            2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
              (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) +
        (1 / (2 * η) + 3) * (1 + 2 * (1 / (2 * η) + 3) * Real.sqrt (20 / α) * Real.exp 4) <
        18 / 25 * α ∧
      40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * α) *
          (1 + 2 * (1 / (2 * η) + 3) * Real.sqrt (20 / α) * Real.exp 4) +
        Real.exp (9 / 2 * (1 / (2 * η) + 3)) *
          (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) <
        18 / 25)
    (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX₀ : 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ X)
    (hXc : 2 * Real.pi * Real.exp (c₀ / t) ≤ X) :
    0 < ((∫ w in Ioi (0 : ℝ), (((w - 0) / (2 * t) * gaussDensity t (w - 0) : ℝ) : ℂ) *
      xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) 0)).re ∧
    ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 / 2 → riemannHeat t ((X : ℂ) + I * y) ≠ 0 := by
  have h2π : 0 < 2 * Real.pi := by positivity
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX₀
  set α := (horizontalSlope X).re with hαdef
  have hαlog : α = Real.log (X / (2 * Real.pi)) / 2 := by rw [hαdef, horizontalSlope_re]
  have hαge : ∀ L : ℝ, 2 * Real.pi * Real.exp L ≤ X → L / 2 ≤ α := by
    intro L hL
    have h1 : Real.exp L ≤ X / (2 * Real.pi) := by rw [le_div_iff₀ h2π]; linarith
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    rw [hαlog]; linarith
  have hαbig : max α₀ 160 ≤ α := by have := hαge _ hX₀; linarith
  have hα160 : 160 ≤ α := (le_max_right _ _).trans hαbig
  have hαα₀ : α₀ ≤ α := (le_max_left _ _).trans hαbig
  have hα0 : 0 < α := by linarith
  have hX200 : 200 ≤ X := by
    have h1 : (1 : ℝ) + 320 ≤ Real.exp (2 * max α₀ 160) := by
      have := Real.add_one_le_exp (2 * max α₀ 160)
      have : (320 : ℝ) ≤ 2 * max α₀ 160 := by linarith [le_max_right α₀ 160]
      linarith
    have := Real.pi_gt_three
    nlinarith
  have hct : c₀ / (2 * α) ≤ t := by
    have h := hαge _ hXc
    rw [div_le_iff₀ (by positivity)]
    have : c₀ / t / 2 * t = c₀ / 2 := by field_simp
    nlinarith
  rcases le_or_gt (20 / α) t with h20 | h20
  · -- Large-product regime `t α ≥ 20`: slope positivity holds on all of `[−1/2, 1/2]`.
    have htα : 20 ≤ t * α := by rw [div_le_iff₀ hα0] at h20; linarith
    have hall : ∀ v : ℝ, |v| ≤ 1 / 2 →
        0 < ((∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) *
          xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) v)).re := fun v hv =>
      re_slope_mul_conj_pos ht ht8 hX200 hv (by linarith) (by linarith)
        (window_fits ht8 ht hX0 (by linarith))
        ((kklError_le_uniform ht le_rfl ht8 (by linarith)).trans
          (kklErrorUniform_le_of_mul_ge ht ht8 htα))
    refine ⟨hall 0 (by simp), fun y hy0 hy => riemannHeat_ne_zero_of_re_slope_pos ht hall hy0 hy⟩
  · -- Sharp regime `c₀ ≤ 2tα < 40`: combine Regime I (`|v| ≤ δ₀`) and Regime II (`δ₀ ≤ |y| ≤ 1/2`).
    obtain ⟨-, hη₁α, hsum1, hsum2, hsum_neg⟩ := hα₀ α hαα₀
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := interior_error_bounds (c₀ := c₀) (η' := 2 * η)
      (γ := 1 / 10) (m := m) (K := K) (by positivity) (by linarith) (by norm_num) hm hK0
      (by linarith) hα160 hη₁α hct h20.le
    have h2tα : c₀ ≤ 2 * t * α := by rw [div_le_iff₀ (by positivity)] at hct; linarith
    have hW9 : 9 / 2 ≤ 2 * t * α + α ^ 2 := by
      have : (0 : ℝ) ≤ 2 * t * α := by positivity
      have : (9 : ℝ) / 2 ≤ α ^ 2 := by nlinarith only [hα160]
      linarith
    have hWX := window_fits ht8 ht hX0 (by linarith)
    set b := 9 / 2 * (1 / (2 * η) + 3)
    have heb := (Real.exp_pos b).le
    have hS1 : chernoffLowerR1 (1 / 10) t + kklR2 t α + sharpR3 (2 * η) t +
        sharpStripErr K (2 * η) m t α + Real.exp b * kklRC t α ≤ 1 / 5 := by
      have := mul_le_mul_of_nonneg_left b5 heb
      linarith
    have hS2 : 2 * sharpStripErr K (2 * η) m t α + Real.exp b * (kklRC t α + kklRB t α) +
        (1 / (2 * η) + 3) * (1 + sharpR3 (2 * η) t) < 18 / 25 * α :=
      combine_weyl_S2 b4 b5 b6 b3 heb (by positivity) hsum2
    have hS_neg : sharpStripErr K (2 * η) m t α +
        Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * α) * (1 + sharpR3 (2 * η) t) +
        Real.exp b * kklRC t α < 18 / 25 := by
      have h5' := mul_le_mul_of_nonneg_left b5 heb
      have hmid : Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * α) * (1 + sharpR3 (2 * η) t) ≤
          Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * α) *
            (1 + 2 * (1 / (2 * η) + 3) * Real.sqrt (20 / α) * Real.exp 4) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      linarith
    -- Regime I: slope positivity on `[−δ₀, δ₀]`.
    have hcollar : ∀ v : ℝ, |v| ≤ δ₀ →
        0 < ((∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) *
          xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) v)).re := fun v hvδ =>
      re_slope_mul_conj_pos_interior ht ht8 hη (by linarith) (by norm_num) hK hK0 hX200
        hvδ (by linarith) (by linarith) (by linarith) (hmc _ h2tα) hW9 hWX hS1 hS2
    -- Strict norm inequality `‖Q(−y)‖ < ‖Q(y)‖` on all of `0 < y ≤ 1/2`.
    set Q := halfGaussTransform t (xiLine X)
    have hnorm_pos : ∀ y : ℝ, 0 < y → y ≤ 1 / 2 → ‖Q (-y)‖ < ‖Q y‖ := by
      intro y hy_pos hy2
      rcases le_or_gt y δ₀ with hy_col | hy_off
      · have hQd : ∀ v ∈ Icc (-δ₀) δ₀, HasDerivAt Q
            (∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) *
              xiLine X w) v := fun v _ =>
          hasDerivAt_halfGaussTransform ht (continuous_xiLine X)
            (integrable_exp_mul_norm_xiLine ht X) v
        exact norm_lt_norm_of_re_mul_conj_pos hQd (fun v hv => hcollar v (abs_le.mpr hv))
          hy_pos hy_col
      · exact norm_neg_lt_norm_pos_interior ht ht8 hη (by linarith) hδ₀ (by norm_num) hK hK0 hX200
          hy_off.le hy2 (by linarith) (by linarith)
          (fun w hw => (hmc _ h2tα w hw).trans (by nlinarith))
          hW9 hWX hS1 hS_neg
    refine ⟨hcollar 0 (by rw [abs_zero]; exact hδ₀.le), fun y hy0 hy => ?_⟩
    rw [riemannHeat_eq_halfGaussAverage ht X y]
    apply add_conj_ne_zero_of_norm_ne
    have hy' := abs_le.mp hy
    rcases lt_or_gt_of_ne hy0 with hneg | hpos
    · have h := hnorm_pos (-y) (by linarith) (by linarith)
      rw [neg_neg] at h
      exact ne_of_gt h
    · exact ne_of_lt (hnorm_pos y hpos hy'.2)

/-- **The heat horizon at `27/40` (`0.675`), real and simple.**
For every `ε > 0`, there exists `X₀` such that for all `0 < t ≤ 1/8`, every zero `z` of
`riemannHeat t` with `|Re z| ≥ X₀` and `|Re z| ≥ 2π e^{(27/40 + ε)/t}` is real and simple. -/
theorem riemannHeat_zeros_real_simple_interiorLindelof {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| →
      2 * Real.pi * Real.exp ((27 / 40 + ε) / t) ≤ |z.re| →
        z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0 := by
  set c₀ := 27 / 40 + ε
  have hc₀ : 27 / 40 < c₀ := by dsimp only [c₀]; linarith
  obtain ⟨η, δ₀, m, hη, hη40, hδ₀, hδ₀40, hm, hsep, hmc⟩ :=
    exists_interiorLindelof_params hc₀
  obtain ⟨K, hKpos, hK⟩ := exists_norm_xiLine_le_strip_interiorLindelof hη (by linarith)
  obtain ⟨α₀, hα₀⟩ := eventually_atTop.mp
    (eventually_interior_errors_small (η' := 2 * η) (δ₀ := δ₀) (γ := 1 / 10) (m := m) (K := K)
      (b := 9 / 2 * (1 / (2 * η) + 3)) (by positivity) hδ₀ (by norm_num) hm)
  set X₀ := 2 * Real.pi * Real.exp (2 * max α₀ 160)
  refine ⟨X₀, fun t ht ht8 z hz hX₀ hXc => ?_⟩
  have hpack : ∀ X : ℝ, X₀ ≤ X → 2 * Real.pi * Real.exp (c₀ / t) ≤ X →
      0 < ((∫ w in Ioi (0 : ℝ), (((w - 0) / (2 * t) * gaussDensity t (w - 0) : ℝ) : ℂ) *
        xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) 0)).re ∧
      ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 / 2 → riemannHeat t ((X : ℂ) + I * y) ≠ 0 :=
    fun X hX1 hX2 => re_slope_zero_and_ne_zero_interiorLindelof hη hη40 hδ₀ hδ₀40 hm hc₀ hsep hmc
      hK hKpos.le hα₀ ht ht8 hX1 hX2
  have him := riemannHeat_zeros_im_sq_le ht hz
  have him2 : z.im ^ 2 ≤ 1 / 4 := him.trans (max_le (by linarith) (by norm_num))
  have him' : |z.im| ≤ 1 / 2 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  have hreal : z.im = 0 := by
    by_contra hne
    rcases le_or_gt 0 z.re with h0 | h0
    · rw [abs_of_nonneg h0] at hX₀ hXc
      apply (hpack z.re hX₀ hXc).2 z.im hne him'
      rw [← hz]; congr 1; apply Complex.ext <;> simp
    · rw [abs_of_neg h0] at hX₀ hXc
      apply (hpack (-z.re) hX₀ hXc).2 (-z.im) (by simpa using hne) (by simpa using him')
      rw [← hz, ← riemannHeat_neg ht.le]; congr 1; apply Complex.ext <;> simp
  refine ⟨hreal, ?_⟩
  have hzre : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hreal]
  rcases le_or_gt 0 z.re with h0 | h0
  · rw [abs_of_nonneg h0] at hX₀ hXc
    rw [hzre]
    exact deriv_riemannHeat_ne_zero_of_re_slope_pos_zero ht (hpack z.re hX₀ hXc).1
      (by rw [← hzre]; exact hz)
  · rw [abs_of_neg h0] at hX₀ hXc
    have hz' : riemannHeat t ((-z.re : ℝ) : ℂ) = 0 := by
      rw [ofReal_neg, riemannHeat_neg ht.le, ← hzre]; exact hz
    have hsimple := deriv_riemannHeat_ne_zero_of_re_slope_pos_zero ht (hpack (-z.re) hX₀ hXc).1 hz'
    rw [ofReal_neg, deriv_riemannHeat_neg ht.le, ← hzre] at hsimple
    exact fun h => hsimple (by rw [h, neg_zero])

/-- Reality projection of `riemannHeat_zeros_real_simple_interiorLindelof`. -/
theorem riemannHeat_zeros_real_interiorLindelof {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| →
      2 * Real.pi * Real.exp ((27 / 40 + ε) / t) ≤ |z.re| → z.im = 0 := by
  obtain ⟨X₀, hX₀⟩ := riemannHeat_zeros_real_simple_interiorLindelof hε
  exact ⟨X₀, fun t ht ht8 z hz h1 h2 => (hX₀ t ht ht8 z hz h1 h2).1⟩

/-- Concrete specialization at `17/25 = 0.68 > 27/40 = 0.675`, matching the horizontal slice rate
`(17/25) / log t` (`exists_xiSliceHeatTransfer_pos_heat_interior`) without any factor-of-2 window
loss. -/
theorem riemannHeat_zeros_real_simple_seventeenTwentyFifths :
    ∃ X₀ : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| →
      2 * Real.pi * Real.exp ((17 / 25 : ℝ) / t) ≤ |z.re| →
        z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0 := by
  obtain ⟨X₀, hX₀⟩ := riemannHeat_zeros_real_simple_interiorLindelof (ε := 1 / 200) (by norm_num)
  refine ⟨X₀, fun t ht ht8 z hz h1 h2 => hX₀ t ht ht8 z hz h1 ?_⟩
  rwa [show (27 / 40 + 1 / 200 : ℝ) = 17 / 25 by norm_num]

/-! ## 5. Sharpened small-time collision localization and nonreal zero count bounds -/

/-- **Interior-Lindelöf spatial localization of collision points.**
For every `ε > 0`, there is `X₀ ≥ 1` such that for every `t > 0` and every collision point
`z ∈ realMultipleZeros t`, `z.im = 0` and `|z.re| < max X₀ (2π e^{(27/40 + ε)/t})`. -/
theorem exists_realMultipleZeros_abs_lt_interiorLindelof {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ t : ℝ, 0 < t → ∀ z ∈ realMultipleZeros t,
      z.im = 0 ∧ |z.re| < max X₀ (2 * Real.pi * Real.exp ((27 / 40 + ε) / t)) := by
  obtain ⟨X₁, hX₁⟩ := riemannHeat_zeros_real_simple_interiorLindelof hε
  refine ⟨max X₁ 1, le_max_right _ _, fun t ht z hz => ?_⟩
  rcases le_or_gt t (1 / 8) with ht8 | ht8
  · obtain ⟨hz0, hzim, hdz⟩ := (mem_realMultipleZeros ht ht8).mp hz
    refine ⟨hzim, ?_⟩
    by_contra hge
    push Not at hge
    have h1 : X₁ ≤ |z.re| := (le_max_left X₁ 1).trans ((le_max_left _ _).trans hge)
    have h2 : 2 * Real.pi * Real.exp ((27 / 40 + ε) / t) ≤ |z.re| :=
      (le_max_right _ _).trans hge
    exact (hX₁ t ht ht8 z hz0 h1 h2).2 hdz
  · simp only [realMultipleZeros, dif_neg (not_and.mpr fun _ => not_le.mpr ht8)] at hz
    exact absurd hz (Finset.notMem_empty _)

/-- **Sharpened unconditional small-time bound on `nonrealZeroCount t`, remaining collision mass
`∑_{s > t} collisionMass s`, and instantaneous `collisionMass t`.**
For every `ε > 0`, there exist `C₀ > 0` and `X₀ ≥ 1` such that for all `0 < t ≤ 1/8`, with
`R(t) = max X₀ (2π e^{(27/40 + ε)/t}) + 1` (lowering the exponent from `3/2` to `27/40`):
1. `nonrealZeroCount t ≤ C₀ * R(t) * log(2 + 3 R(t))`,
2. `∑_{s > t} collisionMass s ≤ C₀ * R(t) * log(2 + 3 R(t))`, and
3. `collisionMass t ≤ C₀ * R(t) * log(2 + 3 R(t))`. -/
theorem exists_nonrealZeroCount_and_collisionMass_le_interiorLindelof {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ X₀ : ℝ, 0 < C₀ ∧ 1 ≤ X₀ ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 / 8 →
      let R := max X₀ (2 * Real.pi * Real.exp ((27 / 40 + ε) / t)) + 1
      ((nonrealZeroCount t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) ∧
      ((∑ s ∈ (finite_collisionTimes ht).toFinset, collisionMass s : ℕ) : ℝ) ≤
        C₀ * R * Real.log (2 + 3 * R) ∧
      ((collisionMass t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) := by
  obtain ⟨C₀, hC₀, hball⟩ := exists_sum_zeroMult_riemannHeat_ball_le
  obtain ⟨X₁, hX₁⟩ := riemannHeat_zeros_real_simple_interiorLindelof hε
  set X₀ := max X₁ 1
  have hX₀1 : 1 ≤ X₀ := le_max_right _ _
  refine ⟨C₀, X₀, hC₀, hX₀1, fun t ht ht8 => ?_⟩
  intro R
  have hR1 : 1 ≤ R := by
    have : 1 ≤ max X₀ (2 * Real.pi * Real.exp ((27 / 40 + ε) / t)) :=
      hX₀1.trans (le_max_left _ _)
    linarith
  have hN : ((nonrealZeroCount t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) := by
    rw [nonrealZeroCount_eq ht]
    refine hball t ht.le ht8 R hR1 _ fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := (riemannHeat_nonreal_zeros_finite ht).mem_toFinset.mp hz
    have hre : |z.re| < max X₀ (2 * Real.pi * Real.exp ((27 / 40 + ε) / t)) := by
      by_contra hge
      push Not at hge
      have h1 : X₁ ≤ |z.re| := (le_max_left X₁ 1).trans ((le_max_left _ _).trans hge)
      have h2 : 2 * Real.pi * Real.exp ((27 / 40 + ε) / t) ≤ |z.re| :=
        (le_max_right _ _).trans hge
      exact hzim (hX₁ t ht ht8 z hz0 h1 h2).1
    have him : |z.im| ≤ 1 / 2 := abs_im_le_half_of_riemannHeat_eq_zero ht hz0
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ < R := by simp only [R]; linarith
  have hC : ((collisionMass t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) := by
    have hle : ((collisionMass t : ℕ) : ℝ) ≤
        ((∑ z ∈ realMultipleZeros t, zeroMult (riemannHeat t) z : ℕ) : ℝ) := by
      exact_mod_cast collisionMass_le_sum_zeroMult t
    refine hle.trans (hball t ht.le ht8 R hR1 _ fun z hz => ?_)
    obtain ⟨hz0, hzim, hdz⟩ := (mem_realMultipleZeros ht ht8).mp hz
    have hre : |z.re| < max X₀ (2 * Real.pi * Real.exp ((27 / 40 + ε) / t)) := by
      by_contra hge
      push Not at hge
      have h1 : X₁ ≤ |z.re| := (le_max_left X₁ 1).trans ((le_max_left _ _).trans hge)
      have h2 : 2 * Real.pi * Real.exp ((27 / 40 + ε) / t) ≤ |z.re| :=
        (le_max_right _ _).trans hge
      exact (hX₁ t ht ht8 z hz0 h1 h2).2 hdz
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ < R := by rw [hzim, abs_zero]; simp only [R]; linarith
  refine ⟨hN, ?_, hC⟩
  have hN' := hN
  rwa [nonrealZeroCount_eq_sum_collisionMass ht] at hN'

end

end RHTower.DeBruijn
