import GaloisForLFunctions.RHTower.MarkovSpectralFirstMomentAndSecondOrderChordPBAP

/-!
# Exact Second-Derivative Peano Parabola Bounds, Spectral Second-Moment Control of `weilSymmetricLogNumerator`, and the Pure Second-Moment `(61 / 120) ∫ ‖f.1‖² - (7 / 16) spectralSecondMoment f.1` Coercivity Law

In Module 50, we proved two key results:
1. Using the first derivative of `cos (r * log t)`, `weilSymmetricLogNumerator f.1` is globally
   `spectralFirstMoment f.1`-logarithmic-Lipschitz, which via the $p = 3/2$ series gives
   `-spectralFirstMoment f.1 ≤ secantNumeratorCellDefect f.1 N`.
2. Using the divided-difference factorization
   `g x - cellSecant g n x = cellParabola n x * ((g x - g (n - 1)) / (x - (n - 1)) - (g n - g x) / (n - x))`,
   any profile with `O(1 / (n - 1) ^ 2)` second-order curvature triggers the convergent $p = 5/2$
   series `∑_{n=2}^N 1 / ((n - 1) ^ 2 * √(n - 1)) ≤ (2 + √2) / 2 ≤ 7 / 4`, improving the
   coefficient from `1` to `7 / 24 ≈ 0.29167`.

In this module, we close the bridge between these two results and eliminate `spectralFirstMoment`
into the positive $L^2$ surplus:

1. **Section 1 (Exact Second-Derivative Peano Parabola Bounds on `[n - 1, n]` via Divided-Difference MVT):**
   - For any twice-differentiable profile `g` on `[n - 1, n]` with `g'' t ≤ B` (or `|g'' t| ≤ B`),
     we apply the Mean Value Theorem (`exists_hasDerivAt_eq_slope`) to the parabola-shifted
     function `h t := g t + (B / 2) * cellParabola n t` together with Module 50's divided-difference
     factorization `sub_cellSecant_eq_cellParabola_mul_slope_diff` to prove the sharp Peano bound
     (`neg_half_mul_cellParabola_le_sub_cellSecant_of_deriv2_le` and
     `abs_sub_cellSecant_le_half_mul_cellParabola_of_abs_deriv2_le`):
     `-(B / 2) * cellParabola n x ≤ g x - cellSecant g n x` and
     `|g x - cellSecant g n x| ≤ (B / 2) * cellParabola n x`.

2. **Section 2 (Second-Order Curvature of `t ↦ cos (r * log t)` on `[n - 1, n]` and the
   `(r^2 + |r|) / (2 (n - 1)^2)` Peano Bound):**
   - Differentiating `cosLogProfile r t := cos (r * log t)` twice with respect to `t > 0` gives
     `cosLogProfileDeriv2 r t = (-r ^ 2 * cos (r * log t) + r * sin (r * log t)) * (t ^ 2)⁻¹`,
     which has an **exact `1 / t ^ 2` factor** (`hasDerivAt_cosLogProfile`,
     `hasDerivAt_cosLogProfileDeriv`).
   - On every unit cell `[n - 1, n]` (`n ≥ 2`), `|cosLogProfileDeriv2 r t| ≤ (r ^ 2 + |r|) / (n - 1) ^ 2`
     (`abs_cosLogProfileDeriv2_le_of_mem_Icc`), so Section 1 immediately yields
     (`abs_cosLogProfile_sub_cellSecant_le_cellParabola`):
     `|cosLogProfile r x - cellSecant (cosLogProfile r) n x| ≤ ((r ^ 2 + |r|) / (2 * (n - 1) ^ 2)) * cellParabola n x`.

3. **Section 3 (The Spectral Second Moment `spectralSecondMoment`, Plancherel Absorption of
   `spectralFirstMoment`, and the Pure Second-Moment `(61 / 120) ∫ ‖f.1‖² > (1 / 2) ∫ ‖f.1‖²` Surplus):**
   - Integrating Section 2 against `(1 / (2 * π)) * ‖paperFT f.1 r‖ ^ 2 * 2` gives the global
     `O(1 / (n - 1) ^ 2)` Peano bound for `weilSymmetricLogNumerator f.1` with
     `M = spectralSecondMoment f.1 + spectralFirstMoment f.1`
     (`abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectral_second_add_first`), and hence
     `-(7 / 24) * (spectralSecondMoment f.1 + spectralFirstMoment f.1) ≤ secantNumeratorCellDefect f.1 N`
     (`neg_seven_twenty_fourths_spectral_second_add_first_le_secantNumeratorCellDefect`).
   - Using the Plancherel identity `(1 / (2 * π)) * ∫ r, ‖paperFT f.1 r‖ ^ 2 * 2 = 2 * ∫ u, ‖f.1 u‖ ^ 2`
     (`one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq`) and the spectral AM-GM inequality
     `2 * |r| ≤ r ^ 2 + 1`, we prove
     `spectralFirstMoment f.1 ≤ (1 / 2) * spectralSecondMoment f.1 + ∫ u, ‖f.1 u‖ ^ 2`
     (`spectralFirstMoment_le_half_spectralSecondMoment_add_l2`).
   - Absorbing `(7 / 24) * ∫ ‖f.1‖²` into the `(4 / 5) * ∫ ‖f.1‖²` positive surplus leaves
     `4 / 5 - 7 / 24 = 61 / 120 > 1 / 2` and `(7 / 24) * (3 / 2) = 7 / 16`, yielding the pure
     second-moment coercivity theorems
     (`sixty_one_one_twentieths_l2_sub_seven_sixteenths_spectralSecondMoment_le_rightCellQuadratureDefect`
     and `half_l2_sub_seven_sixteenths_spectralSecondMoment_le_rightCellQuadratureDefect`):
     `(61 / 120) * ∫ ‖f.1‖² - (7 / 16) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
     and
     `(1 / 2) * ∫ ‖f.1‖² - (7 / 16) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`!
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: Exact Second-Derivative Peano Parabola Bounds on `[n - 1, n]` via Divided-Difference MVT -/

/-- At the left endpoint `x = n - 1`, `cellParabola n (n - 1) = 0`. -/
@[simp]
theorem cellParabola_left_eq_zero (n : ℕ) :
    cellParabola n ((n : ℝ) - 1) = 0 := by
  unfold cellParabola
  ring

/-- At the right endpoint `x = n`, `cellParabola n n = 0`. -/
@[simp]
theorem cellParabola_right_eq_zero (n : ℕ) :
    cellParabola n (n : ℝ) = 0 := by
  unfold cellParabola
  ring

/-- Because `cellParabola n` vanishes at both endpoints `n - 1` and `n`, its linear secant
interpolant `cellSecant (cellParabola n) n` is identically zero. -/
@[simp]
theorem cellSecant_cellParabola_eq_zero (n : ℕ) (x : ℝ) :
    cellSecant (cellParabola n) n x = 0 := by
  unfold cellSecant
  rw [cellParabola_left_eq_zero, cellParabola_right_eq_zero]
  ring

/-- First derivative of `cellParabola n t = (t - (n - 1)) * (n - t)`. -/
theorem hasDerivAt_cellParabola (n : ℕ) (t : ℝ) :
    HasDerivAt (cellParabola n) (2 * (n : ℝ) - 1 - 2 * t) t := by
  unfold cellParabola
  have h1 : HasDerivAt (fun y : ℝ => y - ((n : ℝ) - 1)) 1 t :=
    (hasDerivAt_id t).sub_const ((n : ℝ) - 1)
  have h2 : HasDerivAt (fun y : ℝ => (n : ℝ) - y) (0 - 1) t :=
    (hasDerivAt_const t (n : ℝ)).sub (hasDerivAt_id t)
  exact (h1.mul h2).congr_deriv (by ring)

/-- Second derivative of `cellParabola n`: the derivative of `y ↦ 2 * n - 1 - 2 * y` is `-2`. -/
theorem hasDerivAt_cellParabola_deriv (n : ℕ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * (n : ℝ) - 1 - 2 * y) (-2) t := by
  have h1 : HasDerivAt (fun y : ℝ => 2 * y) (2 * 1) t :=
    (hasDerivAt_id t).const_mul 2
  have h2 : HasDerivAt (fun y : ℝ => 2 * (n : ℝ) - 1 - 2 * y) (0 - 2 * 1) t :=
    (hasDerivAt_const t (2 * (n : ℝ) - 1)).sub h1
  exact h2.congr_deriv (by ring)

/-- **Sharp Second-Derivative Peano Parabola Lower Bound on `[n - 1, n]`**:
if `g` has first derivative `g'` and second derivative `g'' ≤ B` on `[n - 1, n]`, then for every
`x ∈ [n - 1, n]`,
`-(B / 2) * cellParabola n x ≤ g x - cellSecant g n x`. -/
theorem neg_half_mul_cellParabola_le_sub_cellSecant_of_deriv2_le
    {g g' g'' : ℝ → ℝ} (n : ℕ) {B : ℝ}
    (hd1 : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt g (g' t) t)
    (hd2 : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt g' (g'' t) t)
    (hB : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), g'' t ≤ B)
    {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    -(B / 2) * cellParabola n x ≤ g x - cellSecant g n x := by
  rcases eq_or_lt_of_le hx.1 with rfl | hx1
  · rw [cellParabola_left_eq_zero, mul_zero]
    unfold cellSecant
    linarith
  rcases eq_or_lt_of_le hx.2 with rfl | hx2
  · rw [cellParabola_right_eq_zero, mul_zero]
    unfold cellSecant
    linarith
  have hx_oo : x ∈ Ioo ((n : ℝ) - 1) (n : ℝ) := ⟨hx1, hx2⟩
  let h : ℝ → ℝ := fun t => g t + (B / 2) * cellParabola n t
  let h' : ℝ → ℝ := fun t => g' t + (B / 2) * (2 * (n : ℝ) - 1 - 2 * t)
  let h'' : ℝ → ℝ := fun t => g'' t + (B / 2) * (-2)
  have h_deriv : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt h (h' t) t :=
    fun t ht => (hd1 t ht).add ((hasDerivAt_cellParabola n t).const_mul (B / 2))
  have h'_deriv : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt h' (h'' t) t :=
    fun t ht => (hd2 t ht).add ((hasDerivAt_cellParabola_deriv n t).const_mul (B / 2))
  obtain ⟨c₁, hc₁, hc₁_slope⟩ := exists_hasDerivAt_eq_slope h h' hx1
    (fun t ht => (h_deriv t ⟨ht.1, ht.2.trans hx.2⟩).continuousAt.continuousWithinAt)
    (fun t ht => h_deriv t ⟨ht.1.le, ht.2.le.trans hx.2⟩)
  obtain ⟨c₂, hc₂, hc₂_slope⟩ := exists_hasDerivAt_eq_slope h h' hx2
    (fun t ht => (h_deriv t ⟨hx.1.trans ht.1, ht.2⟩).continuousAt.continuousWithinAt)
    (fun t ht => h_deriv t ⟨hx.1.trans ht.1.le, ht.2.le⟩)
  have hc12 : c₁ < c₂ := hc₁.2.trans hc₂.1
  obtain ⟨ξ, hξ, hξ_slope⟩ := exists_hasDerivAt_eq_slope h' h'' hc12
    (fun t ht => (h'_deriv t ⟨hc₁.1.le.trans ht.1, ht.2.trans hc₂.2.le⟩).continuousAt.continuousWithinAt)
    (fun t ht => h'_deriv t ⟨(hc₁.1.trans ht.1).le, (ht.2.trans hc₂.2).le⟩)
  have hξ_mem : ξ ∈ Icc ((n : ℝ) - 1) (n : ℝ) :=
    ⟨(hc₁.1.trans hξ.1).le, (hξ.2.trans hc₂.2).le⟩
  have hBξ : h'' ξ ≤ 0 := by
    dsimp [h'']
    linarith [hB ξ hξ_mem]
  have hc12_pos : 0 < c₂ - c₁ := sub_pos.mpr hc12
  have hdiff_eq : h' c₂ - h' c₁ = h'' ξ * (c₂ - c₁) :=
    ((eq_div_iff hc12_pos.ne').mp hξ_slope).symm
  have hslope_nonneg : 0 ≤ h' c₁ - h' c₂ := by
    have hle : h' c₂ - h' c₁ ≤ 0 := by
      rw [hdiff_eq]
      exact mul_nonpos_of_nonpos_of_nonneg hBξ hc12_pos.le
    linarith
  have hfact := sub_cellSecant_eq_cellParabola_mul_slope_diff h n hx_oo
  rw [← hc₁_slope, ← hc₂_slope] at hfact
  have hnonneg : 0 ≤ h x - cellSecant h n x := by
    rw [hfact]
    exact mul_nonneg (cellParabola_nonneg_of_mem_Icc hx) hslope_nonneg
  have hsec_eq : h x - cellSecant h n x =
      g x - cellSecant g n x + (B / 2) * cellParabola n x := by
    dsimp [h, cellSecant]
    rw [cellParabola_left_eq_zero, cellParabola_right_eq_zero]
    ring
  linarith

/-- **Sharp Two-Sided Second-Derivative Peano Parabola Bound on `[n - 1, n]`**:
if `g` has first derivative `g'` and second derivative `g''` with `|g'' t| ≤ B` on `[n - 1, n]`,
then for every `x ∈ [n - 1, n]`,
`|g x - cellSecant g n x| ≤ (B / 2) * cellParabola n x`. -/
theorem abs_sub_cellSecant_le_half_mul_cellParabola_of_abs_deriv2_le
    {g g' g'' : ℝ → ℝ} (n : ℕ) {B : ℝ}
    (hd1 : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt g (g' t) t)
    (hd2 : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), HasDerivAt g' (g'' t) t)
    (hB : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), |g'' t| ≤ B)
    {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |g x - cellSecant g n x| ≤ (B / 2) * cellParabola n x := by
  have hlow := neg_half_mul_cellParabola_le_sub_cellSecant_of_deriv2_le n hd1 hd2
    (fun t ht => (le_abs_self _).trans (hB t ht)) hx
  have hneg := neg_half_mul_cellParabola_le_sub_cellSecant_of_deriv2_le
    (g := fun t => -g t) (g' := fun t => -g' t) (g'' := fun t => -g'' t) n
    (fun t ht => (hd1 t ht).neg) (fun t ht => (hd2 t ht).neg)
    (fun t ht => (neg_le_abs _).trans (hB t ht)) hx
  have hsec_neg : (-g x) - cellSecant (fun t => -g t) n x = -(g x - cellSecant g n x) := by
    unfold cellSecant
    ring
  rw [hsec_neg] at hneg
  exact abs_le.mpr ⟨by linarith [hlow], by linarith [hneg]⟩

/-! ## Section 2: Second-Order Curvature of `t ↦ cos (r * log t)` on `[n - 1, n]` and the `(r^2 + |r|) / (2 (n - 1)^2)` Peano Bound -/

/-- The elementary logarithmic cosine profile `cosLogProfile r t := cos (r * log t)`. -/
def cosLogProfile (r t : ℝ) : ℝ :=
  Real.cos (r * Real.log t)

/-- First derivative of `cosLogProfile r` with respect to `t`. -/
def cosLogProfileDeriv (r t : ℝ) : ℝ :=
  -r * Real.sin (r * Real.log t) * t⁻¹

/-- Second derivative of `cosLogProfile r` with respect to `t`:
`(-r ^ 2 * cos (r * log t) + r * sin (r * log t)) * (t ^ 2)⁻¹`. -/
def cosLogProfileDeriv2 (r t : ℝ) : ℝ :=
  (-r ^ 2 * Real.cos (r * Real.log t) + r * Real.sin (r * Real.log t)) * (t ^ 2)⁻¹

/-- For `0 < t`, `cosLogProfile r` has derivative `cosLogProfileDeriv r t` at `t`. -/
theorem hasDerivAt_cosLogProfile (r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cosLogProfile r) (cosLogProfileDeriv r t) t := by
  unfold cosLogProfile cosLogProfileDeriv
  exact (((Real.hasDerivAt_log ht.ne').const_mul r).cos).congr_deriv (by ring)

/-- For `0 < t`, `cosLogProfileDeriv r` has derivative `cosLogProfileDeriv2 r t` at `t`. -/
theorem hasDerivAt_cosLogProfileDeriv (r : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cosLogProfileDeriv r) (cosLogProfileDeriv2 r t) t := by
  unfold cosLogProfileDeriv cosLogProfileDeriv2
  have h1 : HasDerivAt (fun y : ℝ => -r * Real.sin (r * Real.log y))
      (-r * (Real.cos (r * Real.log t) * (r * t⁻¹))) t :=
    (((Real.hasDerivAt_log ht.ne').const_mul r).sin).const_mul (-r)
  have h2 : HasDerivAt (fun y : ℝ => y⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht.ne'
  refine (h1.mul h2).congr_deriv ?_
  have ht0 : t ≠ 0 := ht.ne'
  field_simp [ht0]

/-- **Pointwise `(r ^ 2 + |r|) / (n - 1) ^ 2` Bound on `cosLogProfileDeriv2 r t` for `t ∈ [n - 1, n]`
(`2 ≤ n`)**: -/
theorem abs_cosLogProfileDeriv2_le_of_mem_Icc
    (r : ℝ) {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |cosLogProfileDeriv2 r t| ≤ (r ^ 2 + |r|) / ((n : ℝ) - 1) ^ 2 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have ht_pos : 0 < t := lt_of_lt_of_le hn1_pos ht.1
  unfold cosLogProfileDeriv2
  rw [abs_mul, abs_inv, abs_of_pos (sq_pos_of_pos ht_pos), ← div_eq_mul_inv]
  have hnum : |-r ^ 2 * Real.cos (r * Real.log t) + r * Real.sin (r * Real.log t)| ≤
      r ^ 2 + |r| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg r), abs_mul]
    have hcos : |Real.cos (r * Real.log t)| ≤ 1 := Real.abs_cos_le_one _
    have hsin : |Real.sin (r * Real.log t)| ≤ 1 := Real.abs_sin_le_one _
    nlinarith [sq_nonneg r, abs_nonneg r]
  have hsq_le : ((n : ℝ) - 1) ^ 2 ≤ t ^ 2 :=
    sq_le_sq' (by linarith) ht.1
  exact (div_le_div_of_nonneg_right hnum (sq_nonneg t)).trans
    (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn1_pos) hsq_le)

/-- **Exact Peano Parabola Bound for `cosLogProfile r` on `[n - 1, n]` (`2 ≤ n`)**:
`|cosLogProfile r x - cellSecant (cosLogProfile r) n x| ≤ ((r ^ 2 + |r|) / (2 * (n - 1) ^ 2)) * cellParabola n x`. -/
theorem abs_cosLogProfile_sub_cellSecant_le_cellParabola
    (r : ℝ) {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |cosLogProfile r x - cellSecant (cosLogProfile r) n x| ≤
      ((r ^ 2 + |r|) / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht_pos : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), 0 < t :=
    fun t ht => by linarith [ht.1]
  have h := abs_sub_cellSecant_le_half_mul_cellParabola_of_abs_deriv2_le n
    (fun t ht => hasDerivAt_cosLogProfile r (ht_pos t ht))
    (fun t ht => hasDerivAt_cosLogProfileDeriv r (ht_pos t ht))
    (fun t ht => abs_cosLogProfileDeriv2_le_of_mem_Icc r hn ht) hx
  have halg : ((r ^ 2 + |r|) / ((n : ℝ) - 1) ^ 2) / 2 =
      (r ^ 2 + |r|) / (2 * ((n : ℝ) - 1) ^ 2) := by
    rw [div_div, mul_comm (((n : ℝ) - 1) ^ 2) 2]
  rwa [halg] at h

/-! ## Section 3: The Spectral Second Moment `spectralSecondMoment`, Plancherel Absorption of `spectralFirstMoment`, and the Pure Second-Moment `(61 / 120) ∫ ‖f.1‖² - (7 / 16) spectralSecondMoment f.1` Coercivity Law -/

/-- **The Spectral Second Moment `spectralSecondMoment f`**:
`(1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * r ^ 2)`. -/
def spectralSecondMoment (f : ℝ → ℂ) : ℝ :=
  (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * r ^ 2)

/-- `spectralSecondMoment f` is always nonnegative. -/
theorem spectralSecondMoment_nonneg (f : ℝ → ℂ) :
    0 ≤ spectralSecondMoment f := by
  unfold spectralSecondMoment
  refine mul_nonneg (div_nonneg zero_le_one Real.two_pi_pos.le)
    (integral_nonneg fun r => mul_nonneg (sq_nonneg _) (by positivity))

/-- For every `f : WeilTestFn`, `r ↦ ‖paperFT f.1 r‖ ^ 2` is integrable on `ℝ`. -/
theorem integrable_paperFT_norm_sq (f : WeilTestFn) :
    Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f.1 f.1) :=
    EF.weilTest_contDiff f.2.1 f.2.1.continuous f.2.2
  have hkc : HasCompactSupport (EF.weilTest f.1 f.1) :=
    EF.weilTest_hasCompactSupport f.2.2 f.2.2
  have hFk : Integrable (𝓕 (EF.weilTest f.1 f.1)) :=
    EF.integrable_fourier_of_contDiff_two hkd hkc
  have hP : Integrable fun r : ℝ => paperFT (EF.weilTest f.1 f.1) r :=
    EF.integrable_paperFT_ofReal hFk
  have hPn : ∀ r : ℝ, paperFT (EF.weilTest f.1 f.1) r = ((‖paperFT f.1 r‖ ^ 2 : ℝ) : ℂ) := fun r => by
    rw [EF.paperFT_weilTest f.2.1.continuous f.2.1.continuous f.2.2 f.2.2, Complex.conj_ofReal,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine hP.norm.congr (Eventually.of_forall fun r => ?_)
  simp only
  rw [hPn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- For every `f : WeilTestFn` and `t : ℝ`, `r ↦ ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r t)` is
integrable on `ℝ`. -/
theorem integrable_paperFT_norm_sq_mul_two_cosLogProfile (f : WeilTestFn) (t : ℝ) :
    Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r t) := by
  have hsq := integrable_paperFT_norm_sq f
  refine (hsq.mul_const 2).mono' ?_ (Eventually.of_forall fun r => ?_)
  · exact hsq.aestronglyMeasurable.mul (by unfold cosLogProfile; fun_prop)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hle : |cosLogProfile r t| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [sq_nonneg ‖paperFT f.1 r‖]

/-- **Spectral Representation of `weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x`**: -/
theorem weilSymmetricLogNumerator_sub_cellSecant_eq_spectral
    (f : WeilTestFn) (n : ℕ) (x : ℝ) :
    weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x =
      (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 *
        (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x)) := by
  have hcos : ∀ t : ℝ, Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r t) :=
    integrable_paperFT_norm_sq_mul_two_cosLogProfile f
  have hval : ∀ t : ℝ, weilSymmetricLogNumerator f.1 t =
      (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r t) :=
    fun t => weilSymmetricLogNumerator_eq_spectral_cos f t
  have hlin :
      (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x))) =
      fun r : ℝ =>
        ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r x) -
          (((n : ℝ) - x) * (‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r ((n : ℝ) - 1))) +
            (x - ((n : ℝ) - 1)) * (‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r (n : ℝ)))) := by
    ext r
    unfold cellSecant
    ring
  have hint_add := integral_add
    ((hcos ((n : ℝ) - 1)).const_mul ((n : ℝ) - x))
    ((hcos (n : ℝ)).const_mul (x - ((n : ℝ) - 1)))
  have hint_sub := integral_sub (hcos x)
    (((hcos ((n : ℝ) - 1)).const_mul ((n : ℝ) - x)).add ((hcos (n : ℝ)).const_mul (x - ((n : ℝ) - 1))))
  dsimp at hint_add hint_sub
  rw [hlin, hint_sub, hint_add, integral_const_mul, integral_const_mul]
  unfold cellSecant
  rw [hval x, hval ((n : ℝ) - 1), hval (n : ℝ)]
  ring

/-- **Pointwise `(spectralSecondMoment f.1 + spectralFirstMoment f.1) / (2 (n - 1)^2)` Peano Bound
for `weilSymmetricLogNumerator f.1` on `[n - 1, n]` (`2 ≤ n`)**: -/
theorem abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectral_second_add_first
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤
      ((spectralSecondMoment f.1 + spectralFirstMoment f.1) / (2 * ((n : ℝ) - 1) ^ 2)) *
        cellParabola n x := by
  have hcos : ∀ t : ℝ, Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r t) :=
    integrable_paperFT_norm_sq_mul_two_cosLogProfile f
  have hint_diff : Integrable fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 * (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x)) := by
    have hlin :
        (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x))) =
        fun r : ℝ =>
          ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r x) -
            (((n : ℝ) - x) * (‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r ((n : ℝ) - 1))) +
              (x - ((n : ℝ) - 1)) * (‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r (n : ℝ)))) := by
      ext r
      unfold cellSecant
      ring
    rw [hlin]
    exact (hcos x).sub (((hcos ((n : ℝ) - 1)).const_mul _).add ((hcos (n : ℝ)).const_mul _))
  rw [weilSymmetricLogNumerator_sub_cellSecant_eq_spectral f n x,
    abs_mul, abs_of_pos (div_pos one_pos Real.two_pi_pos)]
  have hrhs_eq :
      ((spectralSecondMoment f.1 + spectralFirstMoment f.1) / (2 * ((n : ℝ) - 1) ^ 2)) *
        cellParabola n x =
      (1 / (2 * π)) * ∫ r : ℝ,
        (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2) + ‖paperFT f.1 r‖ ^ 2 * (2 * |r|)) *
          (cellParabola n x / (2 * ((n : ℝ) - 1) ^ 2)) := by
    unfold spectralSecondMoment spectralFirstMoment
    rw [integral_mul_const, integral_add hint2 hint1]
    ring
  rw [hrhs_eq]
  refine mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs.trans ?_)
    (div_nonneg zero_le_one Real.two_pi_pos.le)
  refine integral_mono hint_diff.abs ((hint2.add hint1).mul_const _) fun r => ?_
  dsimp
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpeano := abs_cosLogProfile_sub_cellSecant_le_cellParabola r hn hx
  have hweight : 0 ≤ ‖paperFT f.1 r‖ ^ 2 * 2 := mul_nonneg (sq_nonneg _) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hpeano hweight
  have halg : ‖paperFT f.1 r‖ ^ 2 * 2 * (((r ^ 2 + |r|) / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x) =
      (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2) + ‖paperFT f.1 r‖ ^ 2 * (2 * |r|)) *
        (cellParabola n x / (2 * ((n : ℝ) - 1) ^ 2)) := by ring
  linarith

/-- **Cutoff-Independent `-(7 / 24) (spectralSecondMoment f.1 + spectralFirstMoment f.1) ≤ secantNumeratorCellDefect f.1 N`**: -/
theorem neg_seven_twenty_fourths_spectral_second_add_first_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(7 / 24) * (spectralSecondMoment f.1 + spectralFirstMoment f.1) ≤
      secantNumeratorCellDefect f.1 N := by
  refine neg_seven_twenty_fourths_mul_le_secantNumeratorCellDefect_of_inv_sq_semiconcave
    f (add_nonneg (spectralSecondMoment_nonneg f.1) (spectralFirstMoment_nonneg f.1)) N
    fun n hn x hx => ?_
  rw [Finset.mem_Icc] at hn
  have h := abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectral_second_add_first
    f hint1 hint2 hn.1 hx
  linarith [(abs_le.mp h).1]

/-- **Plancherel Identity for `paperFT f.1`**:
`(1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * 2 = 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq (f : WeilTestFn) :
    (1 / (2 * π)) * (∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * 2) = 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have h := (weilSymmetricLogNumerator_eq_spectral_cos f 1).symm
  rw [weilSymmetricLogNumerator_one_eq_two_mul_integral_norm_sq] at h
  simpa [Real.log_one, mul_zero, Real.cos_zero, mul_one] using h

/-- **Spectral AM-GM / Cauchy–Schwarz Interpolation**:
`spectralFirstMoment f.1 ≤ (1 / 2) * spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2`. -/
theorem spectralFirstMoment_le_half_spectralSecondMoment_add_l2
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    spectralFirstMoment f.1 ≤
      (1 / 2) * spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  have hsq := integrable_paperFT_norm_sq f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hrhs :
      (1 / 2) * spectralSecondMoment f.1 + (∫ u : ℝ, ‖f.1 u‖ ^ 2) =
      (1 / (2 * π)) * ∫ r : ℝ,
        ((1 / 2) * (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) +
          (1 / 2) * (‖paperFT f.1 r‖ ^ 2 * 2)) := by
    unfold spectralSecondMoment
    rw [integral_add (hint2.const_mul (1 / 2)) ((hsq.mul_const 2).const_mul (1 / 2)),
      integral_const_mul, integral_const_mul]
    linarith [hplanch]
  rw [hrhs, spectralFirstMoment]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one Real.two_pi_pos.le)
  refine integral_mono hint1 ((hint2.const_mul (1 / 2)).add ((hsq.mul_const 2).const_mul (1 / 2)))
    fun r => ?_
  dsimp
  have hamgm : 0 ≤ (|r| - 1) ^ 2 := sq_nonneg (|r| - 1)
  have hr2 : |r| ^ 2 = r ^ 2 := sq_abs r
  have h2r : 2 * |r| ≤ r ^ 2 + 1 := by linarith
  nlinarith [sq_nonneg ‖paperFT f.1 r‖]

/-- **Pure Second-Moment `(61 / 120) ∫ ‖f.1‖² - (7 / 16) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect`**:
absorbing the low-frequency part of `spectralFirstMoment f.1` into the `(4 / 5) ∫ ‖f.1‖²` positive
surplus leaves `4 / 5 - 7 / 24 = 61 / 120 > 1 / 2` and `(7 / 24) * (3 / 2) = 7 / 16`! -/
theorem sixty_one_one_twentieths_l2_sub_seven_sixteenths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (61 / 120) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (7 / 16) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_seven_twenty_fourths_spectral_second_add_first_le_secantNumeratorCellDefect
    f hint1 hint2 N
  have h3 := spectralFirstMoment_le_half_spectralSecondMoment_add_l2 f hint1 hint2
  linarith

/-- **Simplified `(1 / 2) ∫ ‖f.1‖² - (7 / 16) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect`**: -/
theorem half_l2_sub_seven_sixteenths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (1 / 2) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (7 / 16) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h := sixty_one_one_twentieths_l2_sub_seven_sixteenths_spectralSecondMoment_le_rightCellQuadratureDefect
    f hint1 hint2 hN1 hN0 hN
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  linarith

end RHTower

end
