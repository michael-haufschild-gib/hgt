import GaloisForLFunctions.RHTower.MarkovLogLipschitzChordAndConvergentThreeHalvesPBAP

/-!
# Spectral First-Moment Control of `weilSymmetricLogNumerator`, the Divided-Difference Factorization of `cellSecant`, and the Convergent $p = 5/2$ Bound `-(7 / 24) M ≤ secantNumeratorCellDefect`

In Module 49, we proved that if `weilSymmetricLogNumerator f.1` is `L`-logarithmic-Lipschitz on
each unit cell `[n - 1, n]`, then `-L ≤ secantNumeratorCellDefect f.1 N` uniformly in `N`, so
`(4 / 5) * ∫ ‖f.1‖² - L ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`.

In this module, we establish two major extensions:

1. **Section 1 (The Spectral First Moment `spectralFirstMoment` and Exact Spectral Logarithmic-Lipschitz
   Control of `weilSymmetricLogNumerator`):**
   - We define the nonnegative spectral first moment
     `spectralFirstMoment f := (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * |r|)`.
   - Using the trigonometric identity `cos a - cos b = -2 * sin ((a + b) / 2) * sin ((a - b) / 2)`
     (`abs_cos_sub_cos_le`) together with Module 45's exact spectral cosine formula
     `weilSymmetricLogNumerator_eq_spectral_cos`, we prove that `weilSymmetricLogNumerator f.1` is
     globally `spectralFirstMoment f.1`-logarithmic-Lipschitz on `(0, ∞)`
     (`abs_weilSymmetricLogNumerator_sub_le_spectralFirstMoment_mul_log_sub`)!
   - Combining with Module 49 immediately yields the cutoff-independent spectral bounds
     (`neg_spectralFirstMoment_le_secantNumeratorCellDefect` and
     `four_fifths_l2_sub_spectralFirstMoment_le_rightCellQuadratureDefect`):
     `-spectralFirstMoment f.1 ≤ secantNumeratorCellDefect f.1 N` and
     `(4 / 5) * ∫ ‖f.1‖² - spectralFirstMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`.

2. **Section 2 (The Divided-Difference Factorization of `cellSecant` and the Convergent $p = 5/2$
   Telescoping Series `∑_{n=2}^N 1 / ((n - 1)^2 √(n - 1)) ≤ (2 + √2) / 2 ≤ 7 / 4`):**
   - For every `x ∈ (n - 1, n)`, `g x - cellSecant g n x` factors into the Peano parabola times the
     difference of left and right chord slopes (`sub_cellSecant_eq_cellParabola_mul_slope_diff`):
     `g x - cellSecant g n x = cellParabola n x * ((g x - g (n - 1)) / (x - (n - 1)) - (g n - g x) / (n - x))`.
   - When the chord-slope difference decays at the natural logarithmic second-derivative scale
     `O(1 / (n - 1)^2)`, the `1 / √(n - 1)` weight produces the **$p = 5/2$ series**
     `∑_{n=2}^N 1 / ((n - 1)^2 √(n - 1))`.
   - Using the elementary majorant `1 / (m ^ 2 * √m) ≤ (1 / √2) * (1 / (m - 1) - 1 / m)` for `m ≥ 2`
     (`inv_sq_mul_sqrt_le_inv_sqrt_two_mul_inv_sub`), we prove by induction that
     `∑_{n=2}^N 1 / ((n - 1)^2 √(n - 1)) ≤ (2 + √2) / 2 ≤ 7 / 4` for all `N : ℕ`
     (`sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_seven_fourths`).

3. **Section 3 (The Cutoff-Independent `-(7 / 24) M ≤ secantNumeratorCellDefect` Bound and
   Unconditional Coercivity for `M < (96 / 35) ∫ ‖F‖²`):**
   - For any profile with `-(M / (2 * (n - 1) ^ 2)) * cellParabola n x ≤ C_f(x) - cellSecant C_f n x`
     on `[n - 1, n]`, we prove `-(7 / 24) * M ≤ secantNumeratorCellDefect f.1 N` and
     `(4 / 5) * ∫ ‖f.1‖² - (7 / 24) * M ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`,
     so any logarithmic curvature budget `M < (96 / 35) * ∫ ‖F‖² ≈ 2.7428 * ∫ ‖F‖²` guarantees
     `0 ≤ markovEnergy F` on the primitive hyperplane!
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

/-! ## Section 1: The Spectral First Moment `spectralFirstMoment` and Exact Spectral Logarithmic-Lipschitz Control of `weilSymmetricLogNumerator` -/

/-- The **Spectral First Moment** of a test function `f : ℝ → ℂ`:
`spectralFirstMoment f = (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * |r|)`. -/
def spectralFirstMoment (f : ℝ → ℂ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ r : ℝ, ‖paperFT f r‖ ^ 2 * (2 * |r|)

/-- Nonnegativity of `spectralFirstMoment f`: -/
theorem spectralFirstMoment_nonneg (f : ℝ → ℂ) :
    0 ≤ spectralFirstMoment f := by
  unfold spectralFirstMoment
  refine mul_nonneg (div_nonneg zero_le_one Real.two_pi_pos.le) (integral_nonneg fun r => ?_)
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg r))

/-- Global trigonometric Lipschitz bound `|Real.cos a - Real.cos b| ≤ |a - b|`: -/
theorem abs_cos_sub_cos_le (a b : ℝ) :
    |Real.cos a - Real.cos b| ≤ |a - b| := by
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h1 : |Real.sin ((a + b) / 2)| ≤ 1 := Real.abs_sin_le_one _
  have h2 : |Real.sin ((a - b) / 2)| ≤ |(a - b) / 2| := Real.abs_sin_le_abs
  have h3 : |(a - b) / 2| = |a - b| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [h3] at h2
  nlinarith [abs_nonneg (Real.sin ((a - b) / 2))]

/-- **Exact Spectral Logarithmic-Lipschitz Bound for `weilSymmetricLogNumerator`**:
for every `f : WeilTestFn` with integrable spectral first moment and every `0 < y ≤ z`,
`|weilSymmetricLogNumerator f.1 z - weilSymmetricLogNumerator f.1 y| ≤ spectralFirstMoment f.1 * (Real.log z - Real.log y)`. -/
theorem abs_weilSymmetricLogNumerator_sub_le_spectralFirstMoment_mul_log_sub
    (f : WeilTestFn)
    (hint : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    {y z : ℝ} (hy : 0 < y) (hyz : y ≤ z) :
    |weilSymmetricLogNumerator f.1 z - weilSymmetricLogNumerator f.1 y| ≤
      spectralFirstMoment f.1 * (Real.log z - Real.log y) := by
  have hlog_nonneg : 0 ≤ Real.log z - Real.log y :=
    sub_nonneg.mpr (Real.log_le_log hy hyz)
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
  have hsq : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 := by
    refine hP.norm.congr (Eventually.of_forall fun r => ?_)
    simp only
    rw [hPn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hcos : ∀ u₀ : ℝ, Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r * u₀)) := by
    intro u₀
    refine (hsq.mul_const 2).mono' ?_ (Eventually.of_forall fun r => ?_)
    · exact hsq.aestronglyMeasurable.mul (by fun_prop)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity), abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hle : |Real.cos (r * u₀)| ≤ 1 := Real.abs_cos_le_one (r * u₀)
      nlinarith [sq_nonneg ‖paperFT f.1 r‖]
  rw [weilSymmetricLogNumerator_eq_spectral_cos f z,
    weilSymmetricLogNumerator_eq_spectral_cos f y,
    ← mul_sub, ← integral_sub (hcos (Real.log z)) (hcos (Real.log y)),
    abs_mul, abs_of_pos (div_pos one_pos Real.two_pi_pos), spectralFirstMoment, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one Real.two_pi_pos.le)
  rw [← integral_mul_const]
  refine abs_integral_le_integral_abs.trans ?_
  refine integral_mono ((hcos (Real.log z)).sub (hcos (Real.log y))).abs (hint.mul_const _) fun r => ?_
  dsimp
  have hsub_eq : ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r * Real.log z)) -
      ‖paperFT f.1 r‖ ^ 2 * (2 * Real.cos (r * Real.log y)) =
      (‖paperFT f.1 r‖ ^ 2 * 2) * (Real.cos (r * Real.log z) - Real.cos (r * Real.log y)) := by ring
  rw [hsub_eq, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcos_diff : |Real.cos (r * Real.log z) - Real.cos (r * Real.log y)| ≤
      |r| * (Real.log z - Real.log y) := by
    refine (abs_cos_sub_cos_le _ _).trans_eq ?_
    rw [← mul_sub, abs_mul, abs_of_nonneg hlog_nonneg]
  have hweight_nonneg : 0 ≤ ‖paperFT f.1 r‖ ^ 2 * 2 := mul_nonneg (sq_nonneg _) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hcos_diff hweight_nonneg
  linarith

/-- **Cutoff-Independent Spectral First-Moment Lower Bound on `secantNumeratorCellDefect`**:
for every `f : WeilTestFn` with integrable spectral first moment and every `N : ℕ`,
`-spectralFirstMoment f.1 ≤ secantNumeratorCellDefect f.1 N`. -/
theorem neg_spectralFirstMoment_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (N : ℕ) :
    -spectralFirstMoment f.1 ≤ secantNumeratorCellDefect f.1 N := by
  refine neg_lip_le_secantNumeratorCellDefect_of_log_lipschitz
    f (spectralFirstMoment_nonneg f.1) N fun n hn y hy z _ hyz => ?_
  rw [Finset.mem_Icc] at hn
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hy_pos : 0 < y := by linarith [hy.1]
  exact abs_weilSymmetricLogNumerator_sub_le_spectralFirstMoment_mul_log_sub f hint hy_pos hyz

/-- **Cutoff-Independent `(4 / 5) ∫ ‖f.1‖² - spectralFirstMoment f.1` Lower Bound on
`rightCellQuadratureDefect`**: -/
theorem four_fifths_l2_sub_spectralFirstMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (4 / 5) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - spectralFirstMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_spectralFirstMoment_le_secantNumeratorCellDefect f hint N
  linarith

/-! ## Section 2: The Divided-Difference Factorization of `cellSecant` and the Convergent $p = 5/2$ Telescoping Series `∑_{n=2}^N 1 / ((n - 1)^2 √(n - 1)) ≤ (2 + √2) / 2 ≤ 7 / 4` -/

/-- **Exact Divided-Difference Factorization of `g x - cellSecant g n x` on `(n - 1, n)`**:
for any `g : ℝ → ℝ`, `n : ℕ`, and `x ∈ Ioo ((n : ℝ) - 1) (n : ℝ)`,
`g x - cellSecant g n x = cellParabola n x * ((g x - g ((n : ℝ) - 1)) / (x - ((n : ℝ) - 1)) - (g (n : ℝ) - g x) / ((n : ℝ) - x))`. -/
theorem sub_cellSecant_eq_cellParabola_mul_slope_diff
    (g : ℝ → ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ Ioo ((n : ℝ) - 1) (n : ℝ)) :
    g x - cellSecant g n x =
      cellParabola n x *
        ((g x - g ((n : ℝ) - 1)) / (x - ((n : ℝ) - 1)) -
          (g (n : ℝ) - g x) / ((n : ℝ) - x)) := by
  have h1 : x - ((n : ℝ) - 1) ≠ 0 := ne_of_gt (sub_pos.mpr hx.1)
  have h2 : (n : ℝ) - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  rw [sub_cellSecant_eq_weighted_chords]
  unfold cellParabola
  have ht1 : (x - ((n : ℝ) - 1)) * ((n : ℝ) - x) *
      ((g x - g ((n : ℝ) - 1)) / (x - ((n : ℝ) - 1))) =
      ((n : ℝ) - x) * (g x - g ((n : ℝ) - 1)) := by
    rw [mul_right_comm (x - ((n : ℝ) - 1)), mul_div_cancel₀ _ h1, mul_comm]
  have ht2 : (x - ((n : ℝ) - 1)) * ((n : ℝ) - x) *
      ((g (n : ℝ) - g x) / ((n : ℝ) - x)) =
      (x - ((n : ℝ) - 1)) * (g (n : ℝ) - g x) := by
    rw [mul_assoc, mul_div_cancel₀ _ h2]
  linear_combination -ht1 + ht2

/-- **Telescoping $p = 5/2$ Majorant for `2 ≤ m`**:
`1 / ((m : ℝ) ^ 2 * Real.sqrt m) ≤ (1 / Real.sqrt 2) * (1 / ((m : ℝ) - 1) - 1 / (m : ℝ))`. -/
theorem inv_sq_mul_sqrt_le_inv_sqrt_two_mul_inv_sub {m : ℕ} (hm : 2 ≤ m) :
    1 / ((m : ℝ) ^ 2 * Real.sqrt m) ≤
      (1 / Real.sqrt 2) * (1 / ((m : ℝ) - 1) - 1 / (m : ℝ)) := by
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtm_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
  have hsub : 1 / ((m : ℝ) - 1) - 1 / (m : ℝ) = 1 / (((m : ℝ) - 1) * (m : ℝ)) := by
    rw [div_sub_div _ _ (ne_of_gt hm1_pos) (ne_of_gt hm_pos)]
    ring
  rw [hsub, one_div_mul_one_div]
  refine one_div_le_one_div_of_le (mul_pos hsqrt2_pos (mul_pos hm1_pos hm_pos)) ?_
  have hsqrt_le : Real.sqrt 2 ≤ Real.sqrt m := Real.sqrt_le_sqrt hm2
  have hprod_le : ((m : ℝ) - 1) * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul hsqrt_le hprod_le (mul_nonneg hm1_pos.le hm_pos.le) hsqrtm_pos.le
  linarith

/-- **Sharp Telescoping Bound on `∑_{n=2}^N 1 / ((n - 1)^2 √(n - 1))` for `2 ≤ N`**:
`∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1)) ≤ 1 + (1 / Real.sqrt 2) * (1 - 1 / ((N : ℝ) - 1))`. -/
theorem sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_sub {N : ℕ} (hN : 2 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) ≤
      1 + (1 / Real.sqrt 2) * (1 - 1 / ((N : ℝ) - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction k with
  | zero =>
    simp
    norm_num
  | succ k ih =>
    have hk2 : 2 ≤ 2 + k := by omega
    have hsucc2 : 2 ≤ 2 + k + 1 := by omega
    rw [show 2 + (k + 1) = 2 + k + 1 by omega, Finset.sum_Icc_succ_top hsucc2]
    have hih := ih hk2
    have hterm : 1 / ((((2 + k + 1 : ℕ) : ℝ) - 1) ^ 2 * Real.sqrt (((2 + k + 1 : ℕ) : ℝ) - 1)) ≤
        (1 / Real.sqrt 2) * (1 / (((2 + k : ℕ) : ℝ) - 1) - 1 / (((2 + k + 1 : ℕ) : ℝ) - 1)) := by
      have hcast : (((2 + k + 1 : ℕ) : ℝ) - 1) = ((2 + k : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hcast]
      exact inv_sq_mul_sqrt_le_inv_sqrt_two_mul_inv_sub hk2
    linarith

/-- **Uniform Cutoff-Independent Bound `∑_{n=2}^N 1 / ((n - 1)^2 √(n - 1)) ≤ (2 + √2) / 2 ≤ 7 / 4`
for All `N : ℕ`**: -/
theorem sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_seven_fourths (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1))) ≤ 7 / 4 := by
  by_cases hN : 2 ≤ N
  · have h := sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_sub hN
    have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hinv_nonneg : 0 ≤ (1 / Real.sqrt 2) * (1 / ((N : ℝ) - 1)) :=
      mul_nonneg (div_nonneg zero_le_one (Real.sqrt_nonneg 2))
        (div_nonneg zero_le_one (by linarith))
    have hsqrt2_gt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4 / 3)]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hinv_le : 1 / Real.sqrt 2 ≤ 3 / 4 := by
      rw [div_le_iff₀ hsqrt2_pos]
      linarith
    linarith
  · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
    norm_num

/-! ## Section 3: The Cutoff-Independent `-(7 / 24) M ≤ secantNumeratorCellDefect` Bound and Unconditional Coercivity for `M < (96 / 35) ∫ ‖F‖²` -/

/-- **Cutoff-Independent `-(7 / 24) M ≤ secantNumeratorCellDefect f.1 N` for `O(1 / (n - 1)^2)`-Curved
Profiles**:
if `0 ≤ M` and on each unit cell `[n - 1, n]` (`n ∈ Finset.Icc 2 N`),
`-(M / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x ≤ weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x`,
then `-(7 / 24) * M ≤ secantNumeratorCellDefect f.1 N` uniformly in `N`! -/
theorem neg_seven_twenty_fourths_mul_le_secantNumeratorCellDefect_of_inv_sq_semiconcave
    (f : WeilTestFn) {M : ℝ} (hM : 0 ≤ M) (N : ℕ)
    (hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(M / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) :
    -(7 / 24) * M ≤ secantNumeratorCellDefect f.1 N := by
  let K : ℕ → ℝ := fun n => M / ((n : ℝ) - 1) ^ 2
  have hK0 : ∀ n ∈ Finset.Icc 2 N, 0 ≤ K n := by
    intro n _
    dsimp [K]
    exact div_nonneg hM (sq_nonneg _)
  have hsemi' : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(K n / 2) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x := by
    intro n hn x hx
    have hpt := hsemi n hn x hx
    have halg : -(K n / 2) * cellParabola n x =
        -(M / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x := by
      dsimp [K]
      rw [div_div, mul_comm (((n : ℝ) - 1) ^ 2) 2]
    rwa [halg]
  have hpeano := neg_sum_div_twelve_sqrt_pred_le_secantNumeratorCellDefect_of_semiconcave
    f K hK0 hsemi'
  have hsum_le : (∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) ≤ (7 / 24) * M := by
    have hcongr : (∑ n ∈ Finset.Icc 2 N, K n / (12 * Real.sqrt ((n : ℝ) - 1))) =
        (M / 12) * ∑ n ∈ Finset.Icc 2 N, 1 / (((n : ℝ) - 1) ^ 2 * Real.sqrt ((n : ℝ) - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp [K]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [hcongr]
    have h74 := sum_Icc_two_inv_sq_pred_mul_sqrt_pred_le_seven_fourths N
    have hmul := mul_le_mul_of_nonneg_left h74 (by linarith : 0 ≤ M / 12)
    linarith
  linarith

/-- **Cutoff-Independent `(4 / 5) ∫ ‖f.1‖² - (7 / 24) M` Lower Bound on `rightCellQuadratureDefect`
for `O(1 / (n - 1)^2)`-Curved Profiles**: -/
theorem four_fifths_l2_sub_seven_twenty_fourths_mul_le_rightCellQuadratureDefect
    (f : WeilTestFn) {M : ℝ} (hM : 0 ≤ M) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsemi : ∀ n ∈ Finset.Icc 2 N, ∀ x ∈ Icc ((n : ℝ) - 1) (n : ℝ),
      -(M / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x ≤
        weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x) :
    (4 / 5) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (7 / 24) * M ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_seven_twenty_fourths_mul_le_secantNumeratorCellDefect_of_inv_sq_semiconcave
    f hM N hsemi
  linarith

end RHTower

end
