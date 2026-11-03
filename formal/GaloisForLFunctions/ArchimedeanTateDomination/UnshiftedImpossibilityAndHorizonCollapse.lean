import GaloisForLFunctions.ArchimedeanTateDomination.TateGammaFamilies
import GaloisForLFunctions.RHTower.WeilConeDegreeTwinRigidity
import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity

/-!
# Unshifted impossibility across all windows and doubly-exponential horizon collapse

This module establishes two unconditional obstructions to archimedean Tate domination across the
full window tower `{W_A}_{A ≥ 0}`:

* **Composite Weil-cone obstruction** (`jordanTotient_six`, `not_weilPositiveDegree_two_mul_jordanTotient`):
  for every `k > 0`, `J_k(6) = (2^k − 1)(3^k − 1) > 0` whereas `Λ(6) = 0`, so `2 J_k` lies outside
  the degree-`α` Weil cone for every `α > 0`.
* **Exponential count blowup vs polynomial unshifted pole** (`tatePointCount_harmonicPlateauTest_ge`,
  `not_forall_window_domination_archGamma_pole`, `not_forall_window_domination_smul_archWindowForm`,
  `not_forall_window_domination_backwardTateGamma_unshiftedPole`,
  `not_forall_window_domination_symTateGamma_unshiftedPole`): on the smooth harmonic plateau
  `harmonicPlateauTest A` (`e^{u/2}` cut off smoothly in `[−A, 0]`), `archGammaForm` is bounded
  uniformly in `A` and `|windowPoleForm| ≤ 2 A²`, whereas `tatePointCount A (harmonicPlateauTest A) k`
  grows like `e^{k A}` for every `k > 0`. Hence no combination `α · archGammaForm + β · windowPoleForm`
  (nor any nonnegative multiple of `backwardTateGammaForm k` or `symTateGammaForm k` plus
  `β · windowPoleForm`) dominates `tatePointCount` across all windows at any fixed `k > 0`.
* **Doubly-exponential horizon collapse on Riemann's kernel** (`exists_horizon_le_doubleExp`,
  `not_exists_uniform_horizon_linearArchimedean`, `not_exists_uniform_horizon_backwardTateGamma`,
  `not_exists_uniform_horizon_symTateGamma`): translating the truncated Riemann kernel `Φ χ_{A/2}`
  into `[−A, 0]` (`windowRiemannKernel A`), Selberg's `Λ₂(2) = (log 2)²` second jet forces a uniform
  `c_* k²` excess over the 1-jet while `weilQuad` is `O(exp(−exp(A − 2)))`, forcing any domination
  horizon `k₀(A)` to collapse faster than `C_* exp(−exp(A − 2))`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.ArchimedeanTateDomination

open CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ SpacingScaleHarmonicAnalysis
open ArithmeticDegenerationTheory
open _root_.RHTower _root_.RHTower.WeilMarkovPole

/-! ### Composite Weil-cone rigidity at `n = 6` -/

/-- Möbius inversion identity `Σ_{d ∣ n} J_k(d) = n^k` for `n ≠ 0`. -/
theorem sum_divisors_jordanTotient (k : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, jordanTotient k d = (n : ℝ) ^ k := by
  refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (R := ℝ) (f := jordanTotient k) (g := fun m : ℕ => (m : ℝ) ^ k)).mpr (fun m _ => ?_) n
    (Nat.pos_of_ne_zero hn)
  rw [jordanTotient,
    Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℝ) * (b : ℝ) ^ k)]

/-- At `n = 6`, Jordan's totient factors as `(2^k − 1)(3^k − 1)` for every real `k`. -/
theorem jordanTotient_six (k : ℝ) :
    jordanTotient k 6 = ((2 : ℝ) ^ k - 1) * ((3 : ℝ) ^ k - 1) := by
  have hs := sum_divisors_jordanTotient k (n := 6) (by omega)
  have hdiv : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
  rw [hdiv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at hs
  have hj1 := jordanTotient_one k
  have hj2 := jordanTotient_prime_pow Nat.prime_two k le_rfl
  have hj3 := jordanTotient_prime_pow Nat.prime_three k le_rfl
  simp only [pow_one, Nat.sub_self, Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul] at hj2 hj3
  norm_num at hs hj2 hj3
  have h6 : (6 : ℝ) ^ k = (2 : ℝ) ^ k * (3 : ℝ) ^ k := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.mul_rpow zero_le_two (by norm_num)]
  rw [hj1, hj2, hj3, h6] at hs
  linear_combination hs

theorem jordanTotient_six_pos {k : ℝ} (hk : 0 < k) : 0 < jordanTotient k 6 := by
  rw [jordanTotient_six]
  exact mul_pos (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hk))
    (sub_pos.mpr (Real.one_lt_rpow (by norm_num) hk))

private theorem vonMangoldt_six : ArithmeticFunction.vonMangoldt 6 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_apply, if_neg]
  rintro ⟨p, a, hp, ha, hpa⟩
  have hp' : Nat.Prime p := hp.nat_prime
  have hp2 : 2 ≤ p := hp'.two_le
  rcases eq_or_lt_of_le (by omega : 1 ≤ a) with rfl | ha2
  · simp only [pow_one] at hpa
    exact absurd (hpa ▸ hp') (by decide)
  · rcases eq_or_lt_of_le hp2 with rfl | hp3
    · rcases eq_or_lt_of_le (by omega : 2 ≤ a) with rfl | ha3
      · omega
      · have : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha3
        omega
    · have : 3 ^ 2 ≤ p ^ a :=
        le_trans (Nat.pow_le_pow_left hp3 2) (Nat.pow_le_pow_right (by omega) ha2)
      omega

/-- **Composite Weil-cone obstruction**: for every `k > 0` and every degree `α > 0`, the arithmetic
Tate weights `2 J_k` do not belong to `WeilPositiveDegree α`. -/
theorem not_weilPositiveDegree_two_mul_jordanTotient {k α : ℝ} (hk : 0 < k) (hα : 0 < α) :
    ¬ _root_.RHTower.WeilPositiveDegree α (fun n => 2 * jordanTotient k n) := by
  intro hW
  have h6 := _root_.RHTower.eq_smul_vonMangoldt_of_weilPositiveDegree hα hW 6 (by omega)
  rw [vonMangoldt_six, mul_zero] at h6
  linarith [jordanTotient_six_pos hk]

/-! ### Smooth harmonic plateau tests and uniform archimedean bounds -/

/-- Smooth cutoff supported in `[−A, 0]` and equal to `1` on `[−A + 1, −1]`. -/
def windowBulkCutoff (A u : ℝ) : ℝ :=
  _root_.RHTower.bulkCutoff (A / 2) (u + A / 2)

/-- Smooth harmonic plateau `e^{u/2} χ_{[−A, 0]}(u)`, approximating the constant profile `1` in
half-density coordinates. -/
def harmonicPlateauTest (A u : ℝ) : ℝ :=
  Real.exp (u / 2) * windowBulkCutoff A u

/-- Explicit derivative of `harmonicPlateauTest A`. -/
def harmonicPlateauDeriv (A u : ℝ) : ℝ :=
  1 / 2 * Real.exp (u / 2) * windowBulkCutoff A u +
    Real.exp (u / 2) * _root_.RHTower.bulkCutoffDeriv (A / 2) (u + A / 2)

theorem windowBulkCutoff_nonneg (A u : ℝ) : 0 ≤ windowBulkCutoff A u :=
  _root_.RHTower.bulkCutoff_nonneg _ _

theorem windowBulkCutoff_le_one (A u : ℝ) : windowBulkCutoff A u ≤ 1 :=
  _root_.RHTower.bulkCutoff_le_one _ _

theorem windowBulkCutoff_eq_zero_of_notMem {A : ℝ} (hA : 0 ≤ A) {u : ℝ} (hu : u ∉ Icc (-A) 0) :
    windowBulkCutoff A u = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at hu
  refine _root_.RHTower.bulkCutoff_eq_zero ?_
  rcases hu with hlt | hgt
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem windowBulkCutoff_eq_zero_of_nonneg {A : ℝ} (hA : 0 ≤ A) {u : ℝ} (hu : 0 ≤ u) :
    windowBulkCutoff A u = 0 := by
  refine _root_.RHTower.bulkCutoff_eq_zero ?_
  rw [abs_of_nonneg (by linarith)]; linarith

theorem windowBulkCutoff_eq_one_of_mem {A u : ℝ} (hu : u ∈ Icc (-A + 1) (-1)) :
    windowBulkCutoff A u = 1 := by
  refine _root_.RHTower.bulkCutoff_eq_one ?_
  rw [abs_le]
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

theorem isWindowTest_harmonicPlateauTest {A : ℝ} (hA : 0 ≤ A) :
    IsWindowTest A (harmonicPlateauTest A) := by
  refine ⟨(Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul
    ((_root_.RHTower.contDiff_bulkCutoff (A / 2)).comp (contDiff_id.add contDiff_const)),
    fun u hu => ?_⟩
  rw [harmonicPlateauTest, windowBulkCutoff_eq_zero_of_notMem hA hu, mul_zero]

theorem harmonicPlateauTest_nonneg (A u : ℝ) : 0 ≤ harmonicPlateauTest A u :=
  mul_nonneg (Real.exp_pos _).le (windowBulkCutoff_nonneg A u)

theorem harmonicPlateauTest_le_exp (A u : ℝ) : harmonicPlateauTest A u ≤ Real.exp (u / 2) :=
  mul_le_of_le_one_right (Real.exp_pos _).le (windowBulkCutoff_le_one A u)

theorem harmonicPlateauTest_eq_zero_of_nonneg {A : ℝ} (hA : 0 ≤ A) {u : ℝ} (hu : 0 ≤ u) :
    harmonicPlateauTest A u = 0 := by
  rw [harmonicPlateauTest, windowBulkCutoff_eq_zero_of_nonneg hA hu, mul_zero]

theorem harmonicPlateauTest_eq_exp_of_mem {A u : ℝ} (hu : u ∈ Icc (-A + 1) (-1)) :
    harmonicPlateauTest A u = Real.exp (u / 2) := by
  rw [harmonicPlateauTest, windowBulkCutoff_eq_one_of_mem hu, mul_one]

theorem hasDerivAt_harmonicPlateauTest (A u : ℝ) :
    HasDerivAt (harmonicPlateauTest A) (harmonicPlateauDeriv A u) u := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (Real.exp (u / 2) * (1 / 2)) u :=
    ((hasDerivAt_id u).div_const 2).exp
  have hb : HasDerivAt (windowBulkCutoff A)
      (_root_.RHTower.bulkCutoffDeriv (A / 2) (u + A / 2)) u :=
    (_root_.RHTower.hasDerivAt_bulkCutoff (A / 2) (u + A / 2)).comp_add_const u (A / 2)
  exact (he.mul hb).congr_deriv (by unfold harmonicPlateauDeriv; ring)

theorem deriv_harmonicPlateauTest (A u : ℝ) :
    deriv (harmonicPlateauTest A) u = harmonicPlateauDeriv A u :=
  (hasDerivAt_harmonicPlateauTest A u).deriv

theorem abs_deriv_harmonicPlateauTest_le {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) (A u : ℝ) :
    |deriv (harmonicPlateauTest A) u| ≤ (1 / 2 + 2 * Λ) * Real.exp (u / 2) := by
  rw [deriv_harmonicPlateauTest]
  unfold harmonicPlateauDeriv
  have he := Real.exp_pos (u / 2)
  have hb0 := windowBulkCutoff_nonneg A u
  have hb1 := windowBulkCutoff_le_one A u
  have hbd := _root_.RHTower.abs_bulkCutoffDeriv_le hΛ (A / 2) (u + A / 2)
  have h1 : |1 / 2 * Real.exp (u / 2) * windowBulkCutoff A u| ≤ 1 / 2 * Real.exp (u / 2) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num), abs_of_pos he, abs_of_nonneg hb0]
    exact mul_le_of_le_one_right (by positivity) hb1
  have h2 : |Real.exp (u / 2) * _root_.RHTower.bulkCutoffDeriv (A / 2) (u + A / 2)| ≤
      2 * Λ * Real.exp (u / 2) := by
    rw [abs_mul, abs_of_pos he, mul_comm]
    exact mul_le_mul_of_nonneg_right hbd he.le
  linarith [abs_add_le (1 / 2 * Real.exp (u / 2) * windowBulkCutoff A u)
    (Real.exp (u / 2) * _root_.RHTower.bulkCutoffDeriv (A / 2) (u + A / 2))]

theorem deriv_harmonicPlateauTest_eq_zero_of_pos {A : ℝ} (hA : 0 ≤ A) {u : ℝ} (hu : 0 < u) :
    deriv (harmonicPlateauTest A) u = 0 := by
  rw [deriv_harmonicPlateauTest]
  unfold harmonicPlateauDeriv
  rw [windowBulkCutoff_eq_zero_of_nonneg hA hu.le, mul_zero, zero_add]
  have hbd : _root_.RHTower.bulkCutoffDeriv (A / 2) (u + A / 2) = 0 := by
    unfold _root_.RHTower.bulkCutoffDeriv
    have hsub : A / 2 - (u + A / 2) = -u := by ring
    rw [hsub, Real.smoothTransition.zero_of_nonpos (x := -u) (by linarith), zero_mul, add_zero,
      GaloisForLFunctions.HTGeometry.deriv_smoothTransition_eq_zero_of_notMem (x := -u)
        (fun hm => by linarith [hm.1]), neg_zero, zero_mul]
  rw [hbd, mul_zero]

theorem integral_harmonicPlateauTest_sq_le {A : ℝ} (hA : 0 ≤ A) :
    ∫ u, harmonicPlateauTest A u ^ 2 ≤ ∫ u, Real.exp (-|u|) := by
  have hH := isWindowTest_harmonicPlateauTest hA
  refine integral_mono (integrable_sq hH.continuous hH.hasCompactSupport)
    _root_.RHTower.integrable_exp_neg_abs fun u => ?_
  dsimp only
  rcases le_or_gt 0 u with hu | hu
  · rw [harmonicPlateauTest_eq_zero_of_nonneg hA hu, sq, zero_mul]
    exact (Real.exp_pos _).le
  · have hle := harmonicPlateauTest_le_exp A u
    have hsq := pow_le_pow_left₀ (harmonicPlateauTest_nonneg A u) hle 2
    have hexp : Real.exp (u / 2) ^ 2 = Real.exp (-|u|) := by
      rw [sq, ← Real.exp_add, abs_of_neg hu]; congr 1; ring
    rwa [hexp] at hsq

theorem exists_integral_deriv_harmonicPlateauTest_sq_le :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ A : ℝ, 0 ≤ A → ∫ u, deriv (harmonicPlateauTest A) u ^ 2 ≤ C₁ := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set K := 1 / 2 + 2 * Λ
  have hK : 0 ≤ K := by positivity
  refine ⟨K ^ 2 * ∫ u, Real.exp (-|u|),
    mul_nonneg (sq_nonneg K) (integral_nonneg fun _ => (Real.exp_pos _).le), fun A hA => ?_⟩
  have hH := isWindowTest_harmonicPlateauTest hA
  have hd_cont : Continuous (deriv (harmonicPlateauTest A)) :=
    (hH.contDiff.continuous_deriv one_le_two)
  have hd_supp : HasCompactSupport (deriv (harmonicPlateauTest A)) :=
    hH.hasCompactSupport.deriv
  have hint := integrable_sq hd_cont hd_supp
  rw [← integral_const_mul]
  refine integral_mono hint (_root_.RHTower.integrable_exp_neg_abs.const_mul (K ^ 2)) fun u => ?_
  dsimp only
  rcases lt_or_ge 0 u with hu | hu
  · rw [deriv_harmonicPlateauTest_eq_zero_of_pos hA hu, sq, zero_mul]
    exact mul_nonneg (sq_nonneg K) (Real.exp_pos _).le
  · have hd := abs_deriv_harmonicPlateauTest_le hΛ A u
    have hsq : deriv (harmonicPlateauTest A) u ^ 2 ≤ (K * Real.exp (u / 2)) ^ 2 := by
      rw [← sq_abs (deriv (harmonicPlateauTest A) u)]
      exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    have hexp : (K * Real.exp (u / 2)) ^ 2 = K ^ 2 * Real.exp (-|u|) := by
      rw [mul_pow, sq (Real.exp _), ← Real.exp_add, abs_of_nonpos hu]; congr 2; ring
    rwa [hexp] at hsq

private theorem integral_harmonicPlateauTest_sub_shift_sq_le_small {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) {A : ℝ} (hA : 0 ≤ A)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ∫ u, (harmonicPlateauTest A u - harmonicPlateauTest A (u + x)) ^ 2 ≤
      (1 / 2 + 2 * Λ) ^ 2 * Real.exp 1 * (∫ u, Real.exp (-|u|)) * x ^ 2 := by
  set K := 1 / 2 + 2 * Λ
  have hK0 : 0 ≤ K := by
    dsimp only [K]; linarith [abs_nonneg (deriv Real.smoothTransition 0), hΛ 0]
  have hH := isWindowTest_harmonicPlateauTest hA
  have hint := integrable_sub_shift_sq hH.continuous hH.hasCompactSupport x
  have hdom := _root_.RHTower.integrable_exp_neg_abs.const_mul (K ^ 2 * Real.exp 1 * x ^ 2)
  have hm := integral_mono hint hdom fun u => ?_
  · rw [integral_const_mul] at hm
    linarith
  · dsimp only
    rcases le_or_gt 0 u with hu | hu
    · rw [harmonicPlateauTest_eq_zero_of_nonneg hA hu,
        harmonicPlateauTest_eq_zero_of_nonneg hA (by linarith), sub_self, sq, zero_mul]
      have hK2 : 0 ≤ K ^ 2 * Real.exp 1 * x ^ 2 := by positivity
      exact mul_nonneg hK2 (Real.exp_pos _).le
    · have hmvt : |harmonicPlateauTest A (u + x) - harmonicPlateauTest A u| ≤
          K * Real.exp ((u + 1) / 2) * x := by
        have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (f := harmonicPlateauTest A) (f' := deriv (harmonicPlateauTest A))
          (s := Icc u (u + x)) (C := K * Real.exp ((u + 1) / 2))
          (fun t _ => (deriv_harmonicPlateauTest A t ▸
            hasDerivAt_harmonicPlateauTest A t).hasDerivWithinAt)
          (fun t ht => by
            rw [Real.norm_eq_abs]
            exact (abs_deriv_harmonicPlateauTest_le hΛ A t).trans
              (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [ht.2])) hK0))
          (convex_Icc u (u + x)) (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
        simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hx0] using h
      rw [abs_sub_comm] at hmvt
      have hsq : (harmonicPlateauTest A u - harmonicPlateauTest A (u + x)) ^ 2 ≤
          (K * Real.exp ((u + 1) / 2) * x) ^ 2 := by
        rw [← sq_abs (harmonicPlateauTest A u - harmonicPlateauTest A (u + x))]
        exact pow_le_pow_left₀ (abs_nonneg _) hmvt 2
      have hexp : (K * Real.exp ((u + 1) / 2) * x) ^ 2 =
          K ^ 2 * Real.exp 1 * x ^ 2 * Real.exp (-|u|) := by
        have he : Real.exp ((u + 1) / 2) ^ 2 = Real.exp 1 * Real.exp (-|u|) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add, abs_of_neg hu]; congr 1; ring
        calc (K * Real.exp ((u + 1) / 2) * x) ^ 2
            = K ^ 2 * Real.exp ((u + 1) / 2) ^ 2 * x ^ 2 := by ring
          _ = K ^ 2 * (Real.exp 1 * Real.exp (-|u|)) * x ^ 2 := by rw [he]
          _ = K ^ 2 * Real.exp 1 * x ^ 2 * Real.exp (-|u|) := by ring
      rwa [hexp] at hsq

private theorem integral_sub_shift_sq_le_four_mul {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (x : ℝ) :
    ∫ u, (g u - g (u + x)) ^ 2 ≤ 4 * ∫ u, g u ^ 2 := by
  have i1 := integrable_sq hg hgc
  have i2 : Integrable fun u => g (u + x) ^ 2 := i1.comp_add_right x
  have isub := integrable_sub_shift_sq hg hgc x
  have isum : Integrable fun u => 2 * g u ^ 2 + 2 * g (u + x) ^ 2 :=
    (i1.const_mul 2).add (i2.const_mul 2)
  have hm := integral_mono isub isum fun u => by
    dsimp only
    nlinarith only [sq_nonneg (g u + g (u + x))]
  rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul,
    integral_add_right_eq_self (fun u => g u ^ 2) x] at hm
  linarith

private theorem archLevyDensity_le_mul_div {x : ℝ} (hx : 0 < x) :
    archLevyDensity x ≤ Real.exp (-(1 / 2 * x)) * (1 + 2 * x) / (2 * x) := by
  unfold archLevyDensity
  have hden : 2 * x / (1 + 2 * x) ≤ 1 - Real.exp (-2 * x) := by
    have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
    have h2 : Real.exp (-2 * x) ≤ 1 / (1 + 2 * x) := by
      rw [show -2 * x = -(2 * x) by ring, Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) h1
    have h3 : 2 * x / (1 + 2 * x) = 1 - 1 / (1 + 2 * x) := by field_simp; ring
    linarith
  have hdiv := div_le_div_of_nonneg_left (Real.exp_pos (-x / 2)).le (by positivity) hden
  refine hdiv.trans_eq ?_
  rw [show -x / 2 = -(1 / 2 * x) by ring]
  field_simp

/-- The archimedean Lévy jump energy of `harmonicPlateauTest A` is bounded uniformly in `A ≥ 0`. -/
theorem exists_levyJump_harmonicPlateauTest_le :
    ∃ C_J : ℝ, 0 ≤ C_J ∧ ∀ A : ℝ, 0 ≤ A → levyJump (harmonicPlateauTest A) ≤ C_J := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  set E₀ := ∫ u, Real.exp (-|u|)
  have hE₀ : 0 ≤ E₀ := integral_nonneg fun _ => (Real.exp_pos _).le
  set M₀ := 3 / 2 * (1 / 2 + 2 * Λ) ^ 2 * Real.exp 1 * E₀ + 6 * E₀
  have hM₀ : 0 ≤ M₀ := by positivity
  have hint_half : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2 * x))) (Ioi 0) := by
    have hG : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ ((1 : ℝ) - 1)) (Ioi 0) :=
      Real.GammaIntegral_convergent zero_lt_one
    have hG1 : IntegrableOn (fun y : ℝ => Real.exp (-y)) (Ioi 0) :=
      IntegrableOn.congr_fun hG (fun y _ => by
        show Real.exp (-y) * y ^ ((1 : ℝ) - 1) = Real.exp (-y)
        rw [sub_self, Real.rpow_zero, mul_one]) measurableSet_Ioi
    exact (integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => Real.exp (-y)) 0
      (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by simpa using hG1)
  have hdom : IntegrableOn (fun x : ℝ => M₀ * Real.exp (-(1 / 2 * x))) (Ioi 0) :=
    hint_half.const_mul M₀
  refine ⟨∫ x in Ioi (0 : ℝ), M₀ * Real.exp (-(1 / 2 * x)),
    setIntegral_nonneg measurableSet_Ioi fun _ _ => mul_nonneg hM₀ (Real.exp_pos _).le,
    fun A hA => ?_⟩
  have hH := isWindowTest_harmonicPlateauTest hA
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      archLevyDensity x * (∫ u, (harmonicPlateauTest A u - harmonicPlateauTest A (u + x)) ^ 2) ≤
        M₀ * Real.exp (-(1 / 2 * x)) := fun x hx => by
    have hx0 : 0 < x := hx
    have hω := archLevyDensity_le_mul_div hx0
    have hnn_int : 0 ≤ ∫ u, (harmonicPlateauTest A u - harmonicPlateauTest A (u + x)) ^ 2 :=
      integral_nonneg fun _ => sq_nonneg _
    rcases le_or_gt x 1 with hx1 | hx1
    · have hsmall := integral_harmonicPlateauTest_sub_shift_sq_le_small hΛ hA hx0 hx1
      have hω1 : archLevyDensity x ≤ 3 / (2 * x) * Real.exp (-(1 / 2 * x)) := by
        refine hω.trans ?_
        have : 1 + 2 * x ≤ 3 := by linarith
        calc Real.exp (-(1 / 2 * x)) * (1 + 2 * x) / (2 * x)
            ≤ Real.exp (-(1 / 2 * x)) * 3 / (2 * x) :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left this (Real.exp_pos _).le) (by positivity)
          _ = 3 / (2 * x) * Real.exp (-(1 / 2 * x)) := by ring
      set C_s := (1 / 2 + 2 * Λ) ^ 2 * Real.exp 1 * E₀
      have hCs : 0 ≤ C_s := by positivity
      calc archLevyDensity x * ∫ u, (harmonicPlateauTest A u - harmonicPlateauTest A (u + x)) ^ 2
          ≤ (3 / (2 * x) * Real.exp (-(1 / 2 * x))) * (C_s * x ^ 2) :=
            mul_le_mul hω1 hsmall hnn_int (by positivity)
        _ = 3 / 2 * C_s * x * Real.exp (-(1 / 2 * x)) := by field_simp
        _ ≤ 3 / 2 * C_s * 1 * Real.exp (-(1 / 2 * x)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hx1 (by positivity)) (Real.exp_pos _).le
        _ ≤ M₀ * Real.exp (-(1 / 2 * x)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            dsimp only [M₀, C_s]; linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hE₀]
    · have hlarge : ∫ u, (harmonicPlateauTest A u - harmonicPlateauTest A (u + x)) ^ 2 ≤
          4 * E₀ := (integral_sub_shift_sq_le_four_mul hH.continuous hH.hasCompactSupport x).trans
        (mul_le_mul_of_nonneg_left (integral_harmonicPlateauTest_sq_le hA) (by norm_num))
      have hω2 : archLevyDensity x ≤ 3 / 2 * Real.exp (-(1 / 2 * x)) := by
        refine hω.trans ?_
        have : 1 + 2 * x ≤ 3 * x := by linarith
        calc Real.exp (-(1 / 2 * x)) * (1 + 2 * x) / (2 * x)
            ≤ Real.exp (-(1 / 2 * x)) * (3 * x) / (2 * x) :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left this (Real.exp_pos _).le) (by positivity)
          _ = 3 / 2 * Real.exp (-(1 / 2 * x)) := by field_simp
      calc archLevyDensity x * ∫ u, (harmonicPlateauTest A u - harmonicPlateauTest A (u + x)) ^ 2
          ≤ (3 / 2 * Real.exp (-(1 / 2 * x))) * (4 * E₀) :=
            mul_le_mul hω2 hlarge hnn_int (by positivity)
        _ = 6 * E₀ * Real.exp (-(1 / 2 * x)) := by ring
        _ ≤ M₀ * Real.exp (-(1 / 2 * x)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
            dsimp only [M₀]; linarith [show 0 ≤ 3 / 2 * (1 / 2 + 2 * Λ) ^ 2 * Real.exp 1 * E₀ by positivity]
  have hl_le : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal
      (archLevyDensity x * ∫ u, (harmonicPlateauTest A u - harmonicPlateauTest A (u + x)) ^ 2)) ≤
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (M₀ * Real.exp (-(1 / 2 * x))) :=
    setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal (hpt x hx)
  have hl_eq : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (M₀ * Real.exp (-(1 / 2 * x)))) =
      ENNReal.ofReal (∫ x in Ioi (0 : ℝ), M₀ * Real.exp (-(1 / 2 * x))) :=
    (ofReal_integral_eq_lintegral_ofReal hdom
      (ae_of_all _ fun _ => mul_nonneg hM₀ (Real.exp_pos _).le)).symm
  have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hl_le.trans_eq hl_eq)
  rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun _ _ =>
    mul_nonneg hM₀ (Real.exp_pos _).le)] at htr
  exact htr

/-- `|archGammaForm (harmonicPlateauTest A)|` is bounded uniformly across all `A ≥ 0`. -/
theorem exists_abs_archGammaForm_harmonicPlateauTest_le :
    ∃ C_Γ : ℝ, 0 ≤ C_Γ ∧ ∀ A : ℝ, 0 ≤ A → |archGammaForm (harmonicPlateauTest A)| ≤ C_Γ := by
  obtain ⟨C_J, hCJ0, hCJ⟩ := exists_levyJump_harmonicPlateauTest_le
  set E₀ := ∫ u, Real.exp (-|u|)
  have hE₀ : 0 ≤ E₀ := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨|EF.gammaBracket 0| * E₀ + C_J, by positivity, fun A hA => ?_⟩
  unfold archGammaForm
  have hsq0 : 0 ≤ ∫ u, harmonicPlateauTest A u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hJ0 : 0 ≤ levyJump (harmonicPlateauTest A) := ENNReal.toReal_nonneg
  have h1 : |EF.gammaBracket 0 * ∫ u, harmonicPlateauTest A u ^ 2| ≤ |EF.gammaBracket 0| * E₀ := by
    rw [abs_mul, abs_of_nonneg hsq0]
    exact mul_le_mul_of_nonneg_left (integral_harmonicPlateauTest_sq_le hA) (abs_nonneg _)
  have h2 : |levyJump (harmonicPlateauTest A)| ≤ C_J := by
    rw [abs_of_nonneg hJ0]; exact hCJ A hA
  linarith [abs_add_le (EF.gammaBracket 0 * ∫ u, harmonicPlateauTest A u ^ 2)
    (levyJump (harmonicPlateauTest A))]

/-- On `harmonicPlateauTest A`, `windowPoleForm` is nonnegative and bounded by `2 A²`. -/
theorem windowPoleForm_harmonicPlateauTest_bounds {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ windowPoleForm (harmonicPlateauTest A) ∧
      |windowPoleForm (harmonicPlateauTest A)| ≤ 2 * A ^ 2 := by
  have hH := isWindowTest_harmonicPlateauTest hA
  rw [windowPoleForm_eq_exp_prod hH]
  have hp_nn : 0 ≤ ∫ u, harmonicPlateauTest A u * Real.exp (u / 2) :=
    integral_nonneg fun u => mul_nonneg (harmonicPlateauTest_nonneg A u) (Real.exp_pos _).le
  have hm_nn : 0 ≤ ∫ u, harmonicPlateauTest A u * Real.exp (-u / 2) :=
    integral_nonneg fun u => mul_nonneg (harmonicPlateauTest_nonneg A u) (Real.exp_pos _).le
  have hnn : 0 ≤ 2 * ((∫ u, harmonicPlateauTest A u * Real.exp (u / 2)) *
      ∫ u, harmonicPlateauTest A u * Real.exp (-u / 2)) := by positivity
  refine ⟨hnn, ?_⟩
  rw [abs_of_nonneg hnn]
  have hind_int : Integrable (Set.indicator (Icc (-A) 0) fun _ : ℝ => (1 : ℝ)) :=
    (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)).integrable_indicator
      measurableSet_Icc
  have hind_val : (∫ u, Set.indicator (Icc (-A) 0) (fun _ : ℝ => (1 : ℝ)) u) = A := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const,
      Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, mul_one]
    ring
  have hp_le : (∫ u, harmonicPlateauTest A u * Real.exp (u / 2)) ≤ A := by
    refine (integral_mono
      ((hH.continuous.mul (by fun_prop : Continuous fun u : ℝ => Real.exp (u / 2))).integrable_of_hasCompactSupport
        hH.hasCompactSupport.mul_right)
      hind_int fun u => ?_).trans_eq hind_val
    dsimp only [Pi.mul_apply]
    by_cases hu : u ∈ Icc (-A) 0
    · rw [Set.indicator_of_mem hu]
      calc harmonicPlateauTest A u * Real.exp (u / 2)
          ≤ Real.exp (u / 2) * Real.exp (u / 2) :=
            mul_le_mul_of_nonneg_right (harmonicPlateauTest_le_exp A u) (Real.exp_pos _).le
        _ = Real.exp u := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ 1 := Real.exp_le_one_iff.mpr hu.2
    · rw [Set.indicator_of_notMem hu, hH.vanish u hu, zero_mul]
  have hm_le : (∫ u, harmonicPlateauTest A u * Real.exp (-u / 2)) ≤ A := by
    refine (integral_mono
      ((hH.continuous.mul (by fun_prop : Continuous fun u : ℝ => Real.exp (-u / 2))).integrable_of_hasCompactSupport
        hH.hasCompactSupport.mul_right)
      hind_int fun u => ?_).trans_eq hind_val
    dsimp only [Pi.mul_apply]
    by_cases hu : u ∈ Icc (-A) 0
    · rw [Set.indicator_of_mem hu]
      calc harmonicPlateauTest A u * Real.exp (-u / 2)
          ≤ Real.exp (u / 2) * Real.exp (-u / 2) :=
            mul_le_mul_of_nonneg_right (harmonicPlateauTest_le_exp A u) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, show u / 2 + -u / 2 = 0 by ring, Real.exp_zero]
    · rw [Set.indicator_of_notMem hu, hH.vanish u hu, zero_mul]
  have hprod : (∫ u, harmonicPlateauTest A u * Real.exp (u / 2)) *
      (∫ u, harmonicPlateauTest A u * Real.exp (-u / 2)) ≤ A * A :=
    mul_le_mul hp_le hm_le hm_nn hA
  nlinarith

/-! ### Exponential point-count growth and unshifted impossibility -/

/-- Elementary divisor-sum lower bound: for `k ≥ 0` and `N ≥ 2`,
`(N : ℝ)^k / (2 · 2^k) − 1 ≤ Σ_{2 ≤ d ≤ N} J_k(d) / d`. -/
theorem sum_Icc_jordanTotient_div_ge {k : ℝ} (hk : 0 ≤ k) {N : ℕ} (hN : 2 ≤ N) :
    (N : ℝ) ^ k / (2 * (2 : ℝ) ^ k) - 1 ≤
      ∑ d ∈ Finset.Icc 2 N, jordanTotient k d / (d : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdouble : ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ k ≤
      (N : ℝ) * ∑ d ∈ Finset.Icc 1 N, jordanTotient k d / (d : ℝ) := by
    have hpow : ∀ m ∈ Finset.Icc 1 N, (m : ℝ) ^ k =
        ∑ d ∈ Finset.Icc 1 N, if d ∣ m then jordanTotient k d else 0 := fun m hm => by
      have hm0 : m ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
      rw [← sum_divisors_jordanTotient k hm0, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega),
          (Nat.le_of_dvd (Finset.mem_Icc.mp hm).1 hd).trans (Finset.mem_Icc.mp hm).2⟩, hd⟩
      · rintro ⟨_, hd⟩
        exact ⟨hd, hm0⟩
    rw [Finset.sum_congr rfl hpow, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun d hd => ?_
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    have hinner : (∑ m ∈ Finset.Icc 1 N, if d ∣ m then jordanTotient k d else 0) =
        jordanTotient k d * (((Finset.Icc 1 N).filter (fun m => d ∣ m)).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [hinner]
    have hcard_nat : ((Finset.Icc 1 N).filter (fun m => d ∣ m)).card ≤ N / d := by
      have hinj : ((Finset.Icc 1 N).filter (fun m => d ∣ m)).card ≤
          (Finset.Icc 1 (N / d)).card := by
        refine Finset.card_le_card_of_injOn (fun m => m / d) (fun m hm => ?_) (fun m₁ hm₁ m₂ hm₂ h => ?_)
        · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
          exact ⟨Nat.div_pos (Nat.le_of_dvd hm.1.1 hm.2) hd1, Nat.div_le_div_right hm.1.2⟩
        · simp only [Finset.mem_coe, Finset.mem_filter] at hm₁ hm₂
          dsimp only at h
          rw [← Nat.mul_div_cancel' hm₁.2, h, Nat.mul_div_cancel' hm₂.2]
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hinj
    have hcard_real : (((Finset.Icc 1 N).filter (fun m => d ∣ m)).card : ℝ) ≤ (N : ℝ) / d :=
      (Nat.cast_le.mpr hcard_nat).trans (Nat.cast_div_le (m := N) (n := d))
    calc jordanTotient k d * (((Finset.Icc 1 N).filter (fun m => d ∣ m)).card : ℝ)
        ≤ jordanTotient k d * ((N : ℝ) / d) :=
          mul_le_mul_of_nonneg_left hcard_real (jordanTotient_nonneg hk d)
      _ = (N : ℝ) * (jordanTotient k d / (d : ℝ)) := by ring
  set M := (N + 1) / 2
  have hMN : M ≤ N := by omega
  have h1M : 1 ≤ M := by omega
  have hlow_sum : (N : ℝ) * ((N : ℝ) ^ k / (2 * (2 : ℝ) ^ k)) ≤
      ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ k := by
    have hsub : ∑ m ∈ Finset.Icc M N, (m : ℝ) ^ k ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc h1M le_rfl)
        fun m _ _ => Real.rpow_nonneg (Nat.cast_nonneg m) k
    have hterm : ∀ m ∈ Finset.Icc M N, ((N : ℝ) / 2) ^ k ≤ (m : ℝ) ^ k := fun m hm => by
      have hmM : M ≤ m := (Finset.mem_Icc.mp hm).1
      have hNM : (N : ℝ) / 2 ≤ M := by
        have : N ≤ 2 * M := by omega
        have hR : (N : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast this
        linarith
      exact Real.rpow_le_rpow (by positivity) (hNM.trans (by exact_mod_cast hmM)) hk
    have hconst : (((Finset.Icc M N).card : ℝ) * ((N : ℝ) / 2) ^ k) ≤
        ∑ m ∈ Finset.Icc M N, (m : ℝ) ^ k := by
      have := Finset.sum_le_sum hterm
      rwa [Finset.sum_const, nsmul_eq_mul] at this
    have hcard : (N : ℝ) / 2 ≤ ((Finset.Icc M N).card : ℝ) := by
      rw [Nat.card_Icc]
      have : N ≤ 2 * (N + 1 - M) := by omega
      have hR : (N : ℝ) ≤ 2 * ((N + 1 - M : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hdiv_pow : ((N : ℝ) / 2) ^ k = (N : ℝ) ^ k / (2 : ℝ) ^ k :=
      Real.div_rpow hNpos.le zero_le_two k
    calc (N : ℝ) * ((N : ℝ) ^ k / (2 * (2 : ℝ) ^ k))
        = (N : ℝ) / 2 * ((N : ℝ) / 2) ^ k := by rw [hdiv_pow]; ring
      _ ≤ ((Finset.Icc M N).card : ℝ) * ((N : ℝ) / 2) ^ k :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ ∑ m ∈ Finset.Icc M N, (m : ℝ) ^ k := hconst
      _ ≤ ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ k := hsub
  have h1_sum : (N : ℝ) ^ k / (2 * (2 : ℝ) ^ k) ≤
      ∑ d ∈ Finset.Icc 1 N, jordanTotient k d / (d : ℝ) :=
    le_of_mul_le_mul_left (hlow_sum.trans hdouble) hNpos
  rw [← Finset.sum_Ioc_add_eq_sum_Icc hN1] at h1_sum
  have hset : Finset.Ioc 1 N = Finset.Icc 2 N := by
    ext d; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hset, jordanTotient_one, Nat.cast_one, div_one] at h1_sum
  linarith

/-- On `harmonicPlateauTest A` (`A ≥ 6`), `tatePointCount A (harmonicPlateauTest A) k` grows
exponentially as `e^{−2} (e^{k(A−5)} / 2^k − 2)` for every `k ≥ 0`. -/
theorem tatePointCount_harmonicPlateauTest_ge {A : ℝ} (hA : 6 ≤ A) {k : ℝ} (hk : 0 ≤ k) :
    Real.exp (-2) * (Real.exp (k * (A - 5)) / (2 : ℝ) ^ k - 2) ≤
      tatePointCount A (harmonicPlateauTest A) k := by
  have hA0 : 0 ≤ A := by linarith
  have hH := isWindowTest_harmonicPlateauTest hA0
  rw [tatePointCount_eq_sum hA0 hH k]
  set N := ⌊Real.exp (A - 4)⌋₊
  have hexp2 : (4 : ℝ) ≤ Real.exp (A - 4) := by
    have h1 : (2 : ℝ) ≤ A - 4 := by linarith
    have h2 : (4 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp 1
      have he2 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_pos 1]
    exact h2.trans (Real.exp_le_exp.mpr h1)
  have hN2 : 2 ≤ N := (Nat.le_floor_iff (Real.exp_pos _).le).mpr (by norm_num; linarith)
  have hN_le : N ≤ windowLevel A :=
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hsub : ∑ n ∈ Finset.Icc 2 N,
      jordanTotient k n / Real.sqrt n *
        (∫ u, harmonicPlateauTest A u * harmonicPlateauTest A (u + Real.log n)) ≤
      ∑ n ∈ Finset.Icc 2 (windowLevel A),
        jordanTotient k n / Real.sqrt n *
          (∫ u, harmonicPlateauTest A u * harmonicPlateauTest A (u + Real.log n)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hN_le) fun n _ _ =>
      mul_nonneg (div_nonneg (jordanTotient_nonneg hk n) (Real.sqrt_nonneg _))
        (integral_nonneg fun u =>
          mul_nonneg (harmonicPlateauTest_nonneg A u) (harmonicPlateauTest_nonneg A _))
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      Real.exp (-2) * (jordanTotient k n / (n : ℝ)) ≤
        jordanTotient k n / Real.sqrt n *
          (∫ u, harmonicPlateauTest A u * harmonicPlateauTest A (u + Real.log n)) := fun n hn => by
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hsq_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hlog_le : Real.log n ≤ A - 4 := by
      rw [Real.log_le_iff_le_exp hnpos]
      exact (Nat.cast_le.mpr hnN).trans (Nat.floor_le (Real.exp_pos _).le)
    have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hint_prod := integrable_mul_shift hH.continuous hH.hasCompactSupport (Real.log n)
    have hcorr_ge : Real.exp (-2) * Real.sqrt n / (n : ℝ) ≤
        ∫ u, harmonicPlateauTest A u * harmonicPlateauTest A (u + Real.log n) := by
      have hset_le := setIntegral_le_integral (s := Ioc (-2 - Real.log n) (-1 - Real.log n))
        hint_prod (Eventually.of_forall fun u =>
          mul_nonneg (harmonicPlateauTest_nonneg A u) (harmonicPlateauTest_nonneg A _))
      have hconst_le : (∫ _ in Ioc (-2 - Real.log n) (-1 - Real.log n),
          Real.exp (-2) * Real.sqrt n / (n : ℝ)) ≤
          ∫ u in Ioc (-2 - Real.log n) (-1 - Real.log n),
            harmonicPlateauTest A u * harmonicPlateauTest A (u + Real.log n) := by
        refine setIntegral_mono_on
          (integrableOn_const (hs := measure_Ioc_lt_top.ne)) hint_prod.integrableOn
          measurableSet_Ioc fun u hu => ?_
        have hu_mem : u ∈ Icc (-A + 1) (-1) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hux_mem : u + Real.log n ∈ Icc (-A + 1) (-1) :=
          ⟨by linarith [hu.1], by linarith [hu.2]⟩
        rw [harmonicPlateauTest_eq_exp_of_mem hu_mem, harmonicPlateauTest_eq_exp_of_mem hux_mem]
        have hexp_prod : Real.exp (u / 2) * Real.exp ((u + Real.log n) / 2) =
            Real.exp u * Real.sqrt n := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnpos, ← Real.exp_add, ← Real.exp_add]
          congr 1; ring
        rw [hexp_prod]
        have hexp_u : Real.exp (-2) / (n : ℝ) ≤ Real.exp u := by
          have : Real.exp (-2 - Real.log n) ≤ Real.exp u := Real.exp_le_exp.mpr hu.1.le
          rwa [sub_eq_add_neg, Real.exp_add, Real.exp_neg (Real.log n), Real.exp_log hnpos,
            ← div_eq_mul_inv] at this
        calc Real.exp (-2) * Real.sqrt n / (n : ℝ)
            = (Real.exp (-2) / (n : ℝ)) * Real.sqrt n := by ring
          _ ≤ Real.exp u * Real.sqrt n := mul_le_mul_of_nonneg_right hexp_u hsq_pos.le
      rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul] at hconst_le
      have hlen : -1 - Real.log n - (-2 - Real.log n) = 1 := by ring
      rw [hlen, one_mul] at hconst_le
      exact hconst_le.trans hset_le
    calc Real.exp (-2) * (jordanTotient k n / (n : ℝ))
        = jordanTotient k n / Real.sqrt n * (Real.exp (-2) * Real.sqrt n / (n : ℝ)) := by
          field_simp [hsq_pos.ne']
      _ ≤ jordanTotient k n / Real.sqrt n *
          (∫ u, harmonicPlateauTest A u * harmonicPlateauTest A (u + Real.log n)) :=
          mul_le_mul_of_nonneg_left hcorr_ge
            (div_nonneg (jordanTotient_nonneg hk n) hsq_pos.le)
  have hsum_ge : Real.exp (-2) * ∑ n ∈ Finset.Icc 2 N, jordanTotient k n / (n : ℝ) ≤
      ∑ n ∈ Finset.Icc 2 N, jordanTotient k n / Real.sqrt n *
        (∫ u, harmonicPlateauTest A u * harmonicPlateauTest A (u + Real.log n)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hdiv_ge := sum_Icc_jordanTotient_div_ge hk hN2
  have hN_exp : Real.exp (A - 5) ≤ (N : ℝ) := by
    have hfl : Real.exp (A - 4) - 1 < (N : ℝ) := Nat.sub_one_lt_floor _
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have hexp_split : Real.exp (A - 4) = Real.exp 1 * Real.exp (A - 5) := by
      rw [← Real.exp_add]; congr 1; ring
    have h5 : (1 : ℝ) ≤ Real.exp (A - 5) := Real.one_le_exp (by linarith)
    nlinarith
  have hpow_ge : Real.exp (k * (A - 5)) ≤ (N : ℝ) ^ k := by
    rw [mul_comm, Real.exp_mul]
    exact Real.rpow_le_rpow (Real.exp_pos _).le hN_exp hk
  have hpow_div : Real.exp (k * (A - 5)) / (2 * (2 : ℝ) ^ k) - 1 ≤
      (N : ℝ) ^ k / (2 * (2 : ℝ) ^ k) - 1 := by
    have hden : 0 < 2 * (2 : ℝ) ^ k := by positivity
    linarith [div_le_div_of_nonneg_right hpow_ge hden.le]
  have hcomb := (mul_le_mul_of_nonneg_left (hpow_div.trans hdiv_ge) (Real.exp_pos (-2)).le).trans
    (hsum_ge.trans hsub)
  have hrew : 2 * (Real.exp (-2) * (Real.exp (k * (A - 5)) / (2 * (2 : ℝ) ^ k) - 1)) =
      Real.exp (-2) * (Real.exp (k * (A - 5)) / (2 : ℝ) ^ k - 2) := by
    field_simp [(Real.rpow_pos_of_pos two_pos k).ne']
  linarith

/-- Cubic lower bound `t³ / 6 ≤ e^t` for `t ≥ 0`. -/
private theorem pow_three_div_six_le_exp {t : ℝ} (ht : 0 ≤ t) : t ^ 3 / 6 ≤ Real.exp t := by
  have hs := Real.sum_le_exp_of_nonneg ht 4
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    at hs
  norm_num [Nat.factorial] at hs
  nlinarith [sq_nonneg t]

/-- **Unshifted archimedean–polar impossibility across all windows**: for every fixed `k > 0`
and arbitrary real weights `α, β ∈ ℝ`, no linear combination `α · archGammaForm H + β · windowPoleForm H`
dominates `tatePointCount A H k` on every window `W_A`. -/
theorem not_forall_window_domination_archGamma_pole {k : ℝ} (hk : 0 < k) (α β : ℝ) :
    ¬ (∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ α * archGammaForm H + β * windowPoleForm H) := by
  intro hdom
  obtain ⟨C_Γ, hCΓ0, hCΓ⟩ := exists_abs_archGammaForm_harmonicPlateauTest_le
  set K₁ := |α| * C_Γ + 2 * Real.exp (-2) + 1
  set K₂ := 2 * |β| + 1
  have hK₁ : 0 < K₁ := by positivity
  have hK₂ : 0 < K₂ := by positivity
  have he2 : 0 < Real.exp (-2) := Real.exp_pos (-2)
  have h2k : 0 < (2 : ℝ) ^ k := Real.rpow_pos_of_pos two_pos k
  set c := Real.exp (-2) * k ^ 3 / (6 * (2 : ℝ) ^ k)
  have hc : 0 < c := by positivity
  set A := max 6 ((250 * K₂ + K₁) / c + 6)
  have hA6 : 6 ≤ A := le_max_left _ _
  have hAc : (250 * K₂ + K₁) / c + 6 ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := by linarith
  have hle := hdom A hA0 (harmonicPlateauTest A) (isWindowTest_harmonicPlateauTest hA0)
  have hlow := tatePointCount_harmonicPlateauTest_ge hA6 hk.le
  have hcub : c * (A - 5) ^ 3 - 2 * Real.exp (-2) ≤
      Real.exp (-2) * (Real.exp (k * (A - 5)) / (2 : ℝ) ^ k - 2) := by
    have hp := pow_three_div_six_le_exp (mul_nonneg hk.le (by linarith : 0 ≤ A - 5))
    have hdiv := div_le_div_of_nonneg_right hp h2k.le
    have hmul := mul_le_mul_of_nonneg_left hdiv he2.le
    have heq : Real.exp (-2) * ((k * (A - 5)) ^ 3 / 6 / (2 : ℝ) ^ k) = c * (A - 5) ^ 3 := by
      dsimp only [c]; ring
    linarith
  have hup : α * archGammaForm (harmonicPlateauTest A) +
      β * windowPoleForm (harmonicPlateauTest A) ≤ |α| * C_Γ + 2 * |β| * A ^ 2 := by
    have h1 : α * archGammaForm (harmonicPlateauTest A) ≤ |α| * C_Γ :=
      (le_abs_self _).trans ((abs_mul _ _).le.trans
        (mul_le_mul_of_nonneg_left (hCΓ A hA0) (abs_nonneg _)))
    have h2 : β * windowPoleForm (harmonicPlateauTest A) ≤ 2 * |β| * A ^ 2 := by
      have hp := (windowPoleForm_harmonicPlateauTest_bounds hA0).2
      calc β * windowPoleForm (harmonicPlateauTest A)
          ≤ |β * windowPoleForm (harmonicPlateauTest A)| := le_abs_self _
        _ = |β| * |windowPoleForm (harmonicPlateauTest A)| := abs_mul _ _
        _ ≤ |β| * (2 * A ^ 2) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = 2 * |β| * A ^ 2 := by ring
    linarith
  have hA_sq : A ^ 2 ≤ 36 * (A - 5) ^ 2 := by
    have : A ≤ 6 * (A - 5) := by linarith
    nlinarith
  have hA5_1 : 1 ≤ A - 5 := by linarith
  have hA5_c : (250 * K₂ + K₁) / c ≤ A - 5 := by linarith
  have hmul_c : 250 * K₂ + K₁ ≤ c * (A - 5) := by linarith [(div_le_iff₀ hc).mp hA5_c]
  have hcub_gt : |α| * C_Γ + 2 * |β| * A ^ 2 < c * (A - 5) ^ 3 - 2 * Real.exp (-2) := by
    have hsq_pos : 0 < (A - 5) ^ 2 := by positivity
    have h1 : (250 * K₂ + K₁) * (A - 5) ^ 2 ≤ c * (A - 5) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hmul_c hsq_pos.le
      linarith [show c * (A - 5) * (A - 5) ^ 2 = c * (A - 5) ^ 3 by ring]
    have h2 : K₁ ≤ K₁ * (A - 5) ^ 2 :=
      le_mul_of_one_le_right hK₁.le (by nlinarith)
    have h3 : 2 * |β| * A ^ 2 < 250 * K₂ * (A - 5) ^ 2 := by
      have : 2 * |β| < K₂ := by dsimp only [K₂]; linarith
      nlinarith [abs_nonneg β]
    dsimp only [K₁] at h2
    linarith
  linarith

/-- For every `k > 0` and every scalar `φ ∈ ℝ`, `φ · archWindowForm H` fails to dominate
`tatePointCount A H k` across all windows. -/
theorem not_forall_window_domination_smul_archWindowForm {k : ℝ} (hk : 0 < k) (φ : ℝ) :
    ¬ (∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ φ * archWindowForm H) := by
  intro hdom
  refine not_forall_window_domination_archGamma_pole hk φ φ fun A hA H hH => ?_
  have h := hdom A hA H hH
  rw [archWindowForm, mul_add] at h
  exact h

/-- For every `k > 0`, `α ≥ 0`, and `β ∈ ℝ`, `α · backwardTateGammaForm k H + β · windowPoleForm H`
fails to dominate `tatePointCount A H k` across all windows. -/
theorem not_forall_window_domination_backwardTateGamma_unshiftedPole {k α : ℝ} (hk : 0 < k)
    (hα : 0 ≤ α) (β : ℝ) :
    ¬ (∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ α * backwardTateGammaForm k H + β * windowPoleForm H) := by
  intro hdom
  obtain ⟨C_Γ, hCΓ0, hCΓ⟩ := exists_abs_archGammaForm_harmonicPlateauTest_le
  set K₁ := |α * k| * C_Γ + 2 * Real.exp (-2) + 1
  set K₂ := 2 * |β| + 1
  have hK₁ : 0 < K₁ := by positivity
  have hK₂ : 0 < K₂ := by positivity
  have he2 : 0 < Real.exp (-2) := Real.exp_pos (-2)
  have h2k : 0 < (2 : ℝ) ^ k := Real.rpow_pos_of_pos two_pos k
  set c := Real.exp (-2) * k ^ 3 / (6 * (2 : ℝ) ^ k)
  have hc : 0 < c := by positivity
  set A := max 6 ((250 * K₂ + K₁) / c + 6)
  have hA6 : 6 ≤ A := le_max_left _ _
  have hAc : (250 * K₂ + K₁) / c + 6 ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := by linarith
  have hle1 := hdom A hA0 (harmonicPlateauTest A) (isWindowTest_harmonicPlateauTest hA0)
  have hmono := mul_le_mul_of_nonneg_left
    (backwardTateGammaForm_le_mul_archGammaForm_of_nonneg (harmonicPlateauTest_nonneg A) k) hα
  have hle : tatePointCount A (harmonicPlateauTest A) k ≤
      (α * k) * archGammaForm (harmonicPlateauTest A) +
        β * windowPoleForm (harmonicPlateauTest A) := by linarith
  have hlow := tatePointCount_harmonicPlateauTest_ge hA6 hk.le
  have hcub : c * (A - 5) ^ 3 - 2 * Real.exp (-2) ≤
      Real.exp (-2) * (Real.exp (k * (A - 5)) / (2 : ℝ) ^ k - 2) := by
    have hp := pow_three_div_six_le_exp (mul_nonneg hk.le (by linarith : 0 ≤ A - 5))
    have hdiv := div_le_div_of_nonneg_right hp h2k.le
    have hmul := mul_le_mul_of_nonneg_left hdiv he2.le
    have heq : Real.exp (-2) * ((k * (A - 5)) ^ 3 / 6 / (2 : ℝ) ^ k) = c * (A - 5) ^ 3 := by
      dsimp only [c]; ring
    linarith
  have hup : (α * k) * archGammaForm (harmonicPlateauTest A) +
      β * windowPoleForm (harmonicPlateauTest A) ≤ |α * k| * C_Γ + 2 * |β| * A ^ 2 := by
    have h1 : (α * k) * archGammaForm (harmonicPlateauTest A) ≤ |α * k| * C_Γ :=
      (le_abs_self _).trans ((abs_mul _ _).le.trans
        (mul_le_mul_of_nonneg_left (hCΓ A hA0) (abs_nonneg _)))
    have h2 : β * windowPoleForm (harmonicPlateauTest A) ≤ 2 * |β| * A ^ 2 := by
      have hp := (windowPoleForm_harmonicPlateauTest_bounds hA0).2
      calc β * windowPoleForm (harmonicPlateauTest A)
          ≤ |β * windowPoleForm (harmonicPlateauTest A)| := le_abs_self _
        _ = |β| * |windowPoleForm (harmonicPlateauTest A)| := abs_mul _ _
        _ ≤ |β| * (2 * A ^ 2) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = 2 * |β| * A ^ 2 := by ring
    linarith
  have hA_sq : A ^ 2 ≤ 36 * (A - 5) ^ 2 := by
    have : A ≤ 6 * (A - 5) := by linarith
    nlinarith
  have hA5_1 : 1 ≤ A - 5 := by linarith
  have hA5_c : (250 * K₂ + K₁) / c ≤ A - 5 := by linarith
  have hmul_c : 250 * K₂ + K₁ ≤ c * (A - 5) := by linarith [(div_le_iff₀ hc).mp hA5_c]
  have hsq_pos : 0 < (A - 5) ^ 2 := by positivity
  have h1 : (250 * K₂ + K₁) * (A - 5) ^ 2 ≤ c * (A - 5) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hmul_c hsq_pos.le
    linarith [show c * (A - 5) * (A - 5) ^ 2 = c * (A - 5) ^ 3 by ring]
  have h2 : K₁ ≤ K₁ * (A - 5) ^ 2 := le_mul_of_one_le_right hK₁.le (by nlinarith)
  have h3 : 2 * |β| * A ^ 2 < 250 * K₂ * (A - 5) ^ 2 := by
    have : 2 * |β| < K₂ := by dsimp only [K₂]; linarith
    nlinarith [abs_nonneg β]
  dsimp only [K₁] at h2
  linarith

/-- For every `k > 0`, `α ≥ 0`, and `β ∈ ℝ`, `α · symTateGammaForm k H + β · windowPoleForm H`
fails to dominate `tatePointCount A H k` across all windows. -/
theorem not_forall_window_domination_symTateGamma_unshiftedPole {k α : ℝ} (hk : 0 < k)
    (hα : 0 ≤ α) (β : ℝ) :
    ¬ (∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        tatePointCount A H k ≤ α * symTateGammaForm k H + β * windowPoleForm H) := by
  intro hdom
  obtain ⟨C_Γ, hCΓ0, hCΓ⟩ := exists_abs_archGammaForm_harmonicPlateauTest_le
  set K₁ := |α * k| * C_Γ + 2 * Real.exp (-2) + 1
  set K₂ := 2 * |β| + 1
  have hK₁ : 0 < K₁ := by positivity
  have hK₂ : 0 < K₂ := by positivity
  have he2 : 0 < Real.exp (-2) := Real.exp_pos (-2)
  have h2k : 0 < (2 : ℝ) ^ k := Real.rpow_pos_of_pos two_pos k
  set c := Real.exp (-2) * k ^ 3 / (6 * (2 : ℝ) ^ k)
  have hc : 0 < c := by positivity
  set A := max 6 ((250 * K₂ + K₁) / c + 6)
  have hA6 : 6 ≤ A := le_max_left _ _
  have hAc : (250 * K₂ + K₁) / c + 6 ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := by linarith
  have hle1 := hdom A hA0 (harmonicPlateauTest A) (isWindowTest_harmonicPlateauTest hA0)
  have hmono := mul_le_mul_of_nonneg_left
    (symTateGammaForm_le_mul_archGammaForm_of_nonneg (harmonicPlateauTest_nonneg A) hk.le) hα
  have hle : tatePointCount A (harmonicPlateauTest A) k ≤
      (α * k) * archGammaForm (harmonicPlateauTest A) +
        β * windowPoleForm (harmonicPlateauTest A) := by linarith
  have hlow := tatePointCount_harmonicPlateauTest_ge hA6 hk.le
  have hcub : c * (A - 5) ^ 3 - 2 * Real.exp (-2) ≤
      Real.exp (-2) * (Real.exp (k * (A - 5)) / (2 : ℝ) ^ k - 2) := by
    have hp := pow_three_div_six_le_exp (mul_nonneg hk.le (by linarith : 0 ≤ A - 5))
    have hdiv := div_le_div_of_nonneg_right hp h2k.le
    have hmul := mul_le_mul_of_nonneg_left hdiv he2.le
    have heq : Real.exp (-2) * ((k * (A - 5)) ^ 3 / 6 / (2 : ℝ) ^ k) = c * (A - 5) ^ 3 := by
      dsimp only [c]; ring
    linarith
  have hup : (α * k) * archGammaForm (harmonicPlateauTest A) +
      β * windowPoleForm (harmonicPlateauTest A) ≤ |α * k| * C_Γ + 2 * |β| * A ^ 2 := by
    have h1 : (α * k) * archGammaForm (harmonicPlateauTest A) ≤ |α * k| * C_Γ :=
      (le_abs_self _).trans ((abs_mul _ _).le.trans
        (mul_le_mul_of_nonneg_left (hCΓ A hA0) (abs_nonneg _)))
    have h2 : β * windowPoleForm (harmonicPlateauTest A) ≤ 2 * |β| * A ^ 2 := by
      have hp := (windowPoleForm_harmonicPlateauTest_bounds hA0).2
      calc β * windowPoleForm (harmonicPlateauTest A)
          ≤ |β * windowPoleForm (harmonicPlateauTest A)| := le_abs_self _
        _ = |β| * |windowPoleForm (harmonicPlateauTest A)| := abs_mul _ _
        _ ≤ |β| * (2 * A ^ 2) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = 2 * |β| * A ^ 2 := by ring
    linarith
  have hA_sq : A ^ 2 ≤ 36 * (A - 5) ^ 2 := by
    have : A ≤ 6 * (A - 5) := by linarith
    nlinarith
  have hA5_1 : 1 ≤ A - 5 := by linarith
  have hA5_c : (250 * K₂ + K₁) / c ≤ A - 5 := by linarith
  have hmul_c : 250 * K₂ + K₁ ≤ c * (A - 5) := by linarith [(div_le_iff₀ hc).mp hA5_c]
  have hsq_pos : 0 < (A - 5) ^ 2 := by positivity
  have h1 : (250 * K₂ + K₁) * (A - 5) ^ 2 ≤ c * (A - 5) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hmul_c hsq_pos.le
    linarith [show c * (A - 5) * (A - 5) ^ 2 = c * (A - 5) ^ 3 by ring]
  have h2 : K₁ ≤ K₁ * (A - 5) ^ 2 := le_mul_of_one_le_right hK₁.le (by nlinarith)
  have h3 : 2 * |β| * A ^ 2 < 250 * K₂ * (A - 5) ^ 2 := by
    have : 2 * |β| < K₂ := by dsimp only [K₂]; linarith
    nlinarith [abs_nonneg β]
  dsimp only [K₁] at h2
  linarith

/-! ### Doubly-exponential horizon collapse on Riemann's near-radical kernel -/

/-- The truncated Riemann kernel `Φ χ_{A/2}` translated into the window `[−A, 0]`. -/
def windowRiemannKernel (A u : ℝ) : ℝ :=
  _root_.RHTower.truncatedRiemannKernelReal (A / 2) (u + A / 2)

theorem windowRiemannKernel_nonneg (A u : ℝ) : 0 ≤ windowRiemannKernel A u :=
  _root_.RHTower.truncatedRiemannKernelReal_nonneg _ _

theorem contDiff_truncatedRiemannKernelReal (R : ℝ) :
    ContDiff ℝ 2 (_root_.RHTower.truncatedRiemannKernelReal R) := by
  have heq : _root_.RHTower.truncatedRiemannKernelReal R =
      fun u => (_root_.RHTower.truncatedRiemannKernel R u).re := by
    funext u; rw [_root_.RHTower.truncatedRiemannKernel_eq, Complex.ofReal_re]
  rw [heq]
  exact Complex.reCLM.contDiff.comp (_root_.RHTower.contDiff_nearRadicalTest R _)

theorem isWindowTest_windowRiemannKernel {A : ℝ} (hA : 0 ≤ A) :
    IsWindowTest A (windowRiemannKernel A) := by
  refine ⟨(contDiff_truncatedRiemannKernelReal (A / 2)).comp (contDiff_id.add contDiff_const),
    fun u hu => ?_⟩
  simp only [mem_Icc, not_and_or, not_le] at hu
  unfold windowRiemannKernel _root_.RHTower.truncatedRiemannKernelReal
  have hb : _root_.RHTower.bulkCutoff (A / 2) (u + A / 2) = 0 := by
    refine _root_.RHTower.bulkCutoff_eq_zero ?_
    rcases hu with hlt | hgt
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [hb, mul_zero]

/-- Doubly-exponential upper bound on the dimension-zero Weil form of `windowRiemannKernel A`. -/
theorem exists_weilQuad_windowRiemannKernel_le_doubleExp :
    ∃ A₀ C₀ : ℝ, 0 ≤ A₀ ∧ 0 ≤ C₀ ∧
      ∀ A : ℝ, A₀ ≤ A → weilQuad (windowRiemannKernel A) ≤ C₀ * Real.exp (-Real.exp (A - 2)) := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨M, hM0, hM⟩ := _root_.RHTower.exists_integral_norm_sq_truncatedRiemannKernel_le
  set S := _root_.RHTower.zetaInvSqSum
  have hS0 : 0 ≤ S := _root_.RHTower.zetaInvSqSum_nonneg
  set Ystar := max 100 (Real.log (720 * _root_.RHTower.nearRadicalConst S Λ + 1))
  set A₀ := max (2 * (Real.log 2 + 1)) (2 + |Real.log Ystar| + 1)
  have hA₀_nn : 0 ≤ A₀ := le_trans (by positivity) (le_max_left _ _)
  refine ⟨A₀, M + 1, hA₀_nn, by linarith, fun A hA => ?_⟩
  set R := A / 2
  have hAY : 2 + |Real.log Ystar| + 1 ≤ A := (le_max_right _ _).trans hA
  set Y₀ := Real.exp (A - 2) with hY₀_def
  have hY₀_eq : Y₀ = Real.exp (2 * (R - 1)) := by
    rw [hY₀_def]; congr 1; dsimp only [R]; ring
  have hYstar_pos : 0 < Ystar := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hY₀_ge : Ystar ≤ Y₀ := by
    have : Real.log Ystar ≤ A - 2 := by linarith [le_abs_self (Real.log Ystar)]
    calc Ystar = Real.exp (Real.log Ystar) := (Real.exp_log hYstar_pos).symm
      _ ≤ Y₀ := Real.exp_le_exp.mpr this
  have hY100 : 100 ≤ Y₀ := (le_max_left _ _).trans hY₀_ge
  have hYlog : Real.log (720 * _root_.RHTower.nearRadicalConst S Λ + 1) ≤ Y₀ :=
    (le_max_right _ _).trans hY₀_ge
  have hY40 : 40 ≤ Y₀ := by linarith
  have hkY : ((0 + 2 : ℕ) : ℝ) + 1 ≤ Y₀ / 10 := by push_cast; linarith
  have hW_norm : ‖zetaZeroConfig.W (_root_.RHTower.truncatedRiemannKernel R)
      (_root_.RHTower.truncatedRiemannKernel R)‖ ≤ (M + 1) * Real.exp (-Y₀) := by
    have hW := _root_.RHTower.norm_W_nearRadicalTest_le_ratio (K := 0) R
      (fun _ : Fin 1 => (1 : ℂ)) hΛ (by rwa [← hY₀_eq]) (by rwa [← hY₀_eq])
    rw [← hY₀_eq] at hW
    have hrat := _root_.RHTower.nearRadical_ratio_le (k := 0 + 2) hS0 hΛ0 hkY hY100 hYlog
    have hI0 : 0 ≤ ∫ u : ℝ, ‖_root_.RHTower.nearRadicalTest R (fun _ : Fin 1 => (1 : ℂ)) u‖ ^ 2 :=
      integral_nonneg fun _ => by positivity
    have hIM : ∫ u : ℝ, ‖_root_.RHTower.nearRadicalTest R (fun _ : Fin 1 => (1 : ℂ)) u‖ ^ 2 ≤ M :=
      hM R
    calc ‖zetaZeroConfig.W (_root_.RHTower.truncatedRiemannKernel R)
          (_root_.RHTower.truncatedRiemannKernel R)‖
        ≤ Real.exp (-Y₀) * ∫ u : ℝ, ‖_root_.RHTower.nearRadicalTest R (fun _ : Fin 1 => (1 : ℂ)) u‖ ^ 2 :=
          hW.trans (mul_le_mul_of_nonneg_right hrat hI0)
      _ ≤ Real.exp (-Y₀) * (M + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ = (M + 1) * Real.exp (-Y₀) := mul_comm _ _
  have htrans : windowRiemannKernel A =
      fun u => _root_.RHTower.truncatedRiemannKernelReal R (u - -R) := by
    funext u; unfold windowRiemannKernel; dsimp only [R]; ring_nf
  rw [htrans, weilQuad_comp_sub,
    ArithmeticCastelnuovoSeveri.LogCells.weilQuad_eq_zetaW
      (contDiff_truncatedRiemannKernelReal R)
      (_root_.RHTower.hasCompactSupport_truncatedRiemannKernelReal R)]
  have hcx : (fun u => (_root_.RHTower.truncatedRiemannKernelReal R u : ℂ)) =
      _root_.RHTower.truncatedRiemannKernel R :=
    funext fun u => (_root_.RHTower.truncatedRiemannKernel_eq R u).symm
  rw [hcx]
  exact (Complex.re_le_norm _).trans hW_norm

/-- **Doubly-exponential horizon collapse**: there exist explicit constants `A₀ ≥ 0` and `Cstar > 0`
such that for every window `A ≥ A₀` and every `k > 0`, if `tatePointCount A (windowRiemannKernel A) k`
is dominated by `k · archWindowForm (windowRiemannKernel A)`, then
`k ≤ Cstar exp(−exp(A − 2))`. -/
theorem exists_horizon_le_doubleExp :
    ∃ A₀ Cstar : ℝ, 0 ≤ A₀ ∧ 0 < Cstar ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ k : ℝ, 0 < k →
        tatePointCount A (windowRiemannKernel A) k ≤
          k * archWindowForm (windowRiemannKernel A) →
        k ≤ Cstar * Real.exp (-Real.exp (A - 2)) := by
  have hc2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c₀, hc₀, hc₀R⟩ := _root_.RHTower.exists_weilTest_truncatedRiemannKernel_ge hc2
  obtain ⟨A₁, C₀, hA₁, hC₀, hQ_bound⟩ := exists_weilQuad_windowRiemannKernel_le_doubleExp
  set A₀ := max (2 * (Real.log 2 + 1)) A₁
  have hA₀_nn : 0 ≤ A₀ := le_trans (by positivity) (le_max_left _ _)
  set cstar := Real.log 2 ^ 2 / Real.sqrt 2 * c₀
  have hcstar : 0 < cstar := by positivity
  refine ⟨A₀, (C₀ + 1) / cstar, hA₀_nn, div_pos (by linarith) hcstar, fun A hA k hk hdom => ?_⟩
  have hA0 : 0 ≤ A := hA₀_nn.trans hA
  set R := A / 2
  have hRc : Real.log 2 + 1 ≤ R := by
    have := (le_max_left _ _).trans hA; dsimp only [R]; linarith
  have hQ_le : weilQuad (windowRiemannKernel A) ≤ (C₀ + 1) * Real.exp (-Real.exp (A - 2)) := by
    refine (hQ_bound A ((le_max_right _ _).trans hA)).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hH := isWindowTest_windowRiemannKernel hA0
  have hlev2 : 2 ≤ windowLevel A := by
    have hA2 : Real.log 2 ≤ A := by dsimp only [R] at hRc; linarith
    have hexp2 : (2 : ℝ) ≤ Real.exp A := by
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
        _ ≤ Real.exp A := Real.exp_le_exp.mpr hA2
    exact (Nat.le_floor_iff (Real.exp_pos A).le).mpr (by exact_mod_cast hexp2)
  have hcorr2 : c₀ ≤ ∫ u, windowRiemannKernel A u * windowRiemannKernel A (u + Real.log (2 : ℕ)) := by
    have hc_eq : (EF.weilTest (_root_.RHTower.truncatedRiemannKernel R)
        (_root_.RHTower.truncatedRiemannKernel R) (Real.log (2 : ℕ))).re =
        ∫ u, _root_.RHTower.truncatedRiemannKernelReal R u *
          _root_.RHTower.truncatedRiemannKernelReal R (u + Real.log (2 : ℕ)) := by
      have hcx : _root_.RHTower.truncatedRiemannKernel R =
          fun u => (_root_.RHTower.truncatedRiemannKernelReal R u : ℂ) :=
        funext (_root_.RHTower.truncatedRiemannKernel_eq R)
      rw [hcx, (weilTest_ofReal_log (_root_.RHTower.truncatedRiemannKernelReal R) 2).1,
        Complex.ofReal_re]
    have hshift : (∫ u, _root_.RHTower.truncatedRiemannKernelReal R u *
        _root_.RHTower.truncatedRiemannKernelReal R (u + Real.log (2 : ℕ))) =
        ∫ u, windowRiemannKernel A u * windowRiemannKernel A (u + Real.log (2 : ℕ)) := by
      have := integral_add_right_eq_self (μ := volume)
        (fun t => _root_.RHTower.truncatedRiemannKernelReal R t *
          _root_.RHTower.truncatedRiemannKernelReal R (t + Real.log (2 : ℕ))) R
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      unfold windowRiemannKernel; dsimp only [R]; congr 2; ring
    rw [← hshift, ← hc_eq]
    simpa only [Nat.cast_ofNat] using hc₀R R hRc
  have h1 : 1 ≤ windowLevel A := by omega
  have hset : Finset.Ioc 1 (windowLevel A) = Finset.Icc 2 (windowLevel A) := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have hvon : ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt (windowRiemannKernel A) u *
      windowRiemannKernel A u =
      ∑ n ∈ Finset.Icc 2 (windowLevel A),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          ∫ u, windowRiemannKernel A u * windowRiemannKernel A (u + Real.log n) := by
    rw [integral_windowRep_vonMangoldt_eq_sum hH, ← Finset.sum_Ioc_add_eq_sum_Icc h1]
    simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul, add_zero, hset]
  have hdiff : tatePointCount A (windowRiemannKernel A) k -
      2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt (windowRiemannKernel A) u *
        windowRiemannKernel A u =
      2 * ∑ n ∈ Finset.Icc 2 (windowLevel A),
        (jordanTotient k n - k * ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
          ∫ u, windowRiemannKernel A u * windowRiemannKernel A (u + Real.log n) := by
    have hmul : 2 * k * ∑ n ∈ Finset.Icc 2 (windowLevel A),
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (∫ u, windowRiemannKernel A u * windowRiemannKernel A (u + Real.log n)) =
        2 * ∑ n ∈ Finset.Icc 2 (windowLevel A),
          k * (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            ∫ u, windowRiemannKernel A u * windowRiemannKernel A (u + Real.log n)) := by
      rw [mul_assoc, Finset.mul_sum]
    rw [tatePointCount_eq_sum hA0 hH k, hvon, hmul, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1; refine Finset.sum_congr rfl fun _ _ => by ring
  have hselberg : cstar * k ^ 2 ≤ tatePointCount A (windowRiemannKernel A) k -
      2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt (windowRiemannKernel A) u *
        windowRiemannKernel A u := by
    rw [hdiff]
    have hmem2 : (2 : ℕ) ∈ Finset.Icc 2 (windowLevel A) := Finset.mem_Icc.mpr ⟨le_rfl, hlev2⟩
    have hterm_nn : ∀ n ∈ Finset.Icc 2 (windowLevel A),
        0 ≤ (jordanTotient k n - k * ArithmeticFunction.vonMangoldt n) / Real.sqrt n *
          ∫ u, windowRiemannKernel A u * windowRiemannKernel A (u + Real.log n) := fun n hn => by
      have hn2 := (Finset.mem_Icc.mp hn).1
      have hJ : 0 ≤ jordanTotient k n - k * ArithmeticFunction.vonMangoldt n :=
        le_trans (mul_nonneg (by positivity) (genVonMangoldt_nonneg 2 n))
          (jordanTotient_sub_linear_ge_selberg hk.le hn2)
      exact mul_nonneg (div_nonneg hJ (Real.sqrt_nonneg _))
        (integral_nonneg fun u =>
          mul_nonneg (windowRiemannKernel_nonneg A u) (windowRiemannKernel_nonneg A _))
    have hsingle := Finset.single_le_sum hterm_nn hmem2
    have hJ2 := jordanTotient_sub_linear_ge_selberg hk.le (le_rfl : 2 ≤ 2)
    rw [genVonMangoldt_two_two] at hJ2
    have hsq2 : 0 < Real.sqrt (2 : ℕ) := Real.sqrt_pos.mpr (by norm_num)
    have ht2 : k ^ 2 / 2 * Real.log 2 ^ 2 / Real.sqrt (2 : ℕ) * c₀ ≤
        (jordanTotient k 2 - k * ArithmeticFunction.vonMangoldt 2) / Real.sqrt (2 : ℕ) *
          ∫ u, windowRiemannKernel A u * windowRiemannKernel A (u + Real.log (2 : ℕ)) :=
      mul_le_mul (div_le_div_of_nonneg_right hJ2 hsq2.le) hcorr2 hc₀.le
        (div_nonneg (le_trans (by positivity) hJ2) hsq2.le)
    have heq : 2 * (k ^ 2 / 2 * Real.log 2 ^ 2 / Real.sqrt (2 : ℕ) * c₀) = cstar * k ^ 2 := by
      dsimp only [cstar]; norm_num; ring
    linarith
  have hupper : tatePointCount A (windowRiemannKernel A) k -
      2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt (windowRiemannKernel A) u *
        windowRiemannKernel A u ≤ k * ((C₀ + 1) * Real.exp (-Real.exp (A - 2))) := by
    have hQ_id := weilQuad_eq_archWindowForm_sub_vonMangoldt hH
    have hQ_mul := mul_le_mul_of_nonneg_left hQ_le hk.le
    have hrel : k * weilQuad (windowRiemannKernel A) =
        k * archWindowForm (windowRiemannKernel A) -
          2 * k * ∫ u, windowRepFun A ArithmeticFunction.vonMangoldt (windowRiemannKernel A) u *
            windowRiemannKernel A u := by
      rw [hQ_id]; ring
    linarith
  have hk_mul : cstar * k ≤ (C₀ + 1) * Real.exp (-Real.exp (A - 2)) := by
    have : k * (cstar * k) ≤ k * ((C₀ + 1) * Real.exp (-Real.exp (A - 2))) := by
      linarith [show cstar * k ^ 2 = k * (cstar * k) by ring]
    exact le_of_mul_le_mul_left this hk
  rw [div_mul_eq_mul_div, le_div_iff₀ hcstar, mul_comm]
  exact hk_mul

/-- **No uniform horizon for `k · archWindowForm`**: there is no window-independent `k₀ > 0` on
which `k · archWindowForm H` dominates `tatePointCount A H k` across all windows. -/
theorem not_exists_uniform_horizon_linearArchimedean :
    ¬ ∃ k₀ > 0, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        ∀ k ∈ Ioc 0 k₀, tatePointCount A H k ≤ k * archWindowForm H := by
  rintro ⟨k₀, hk₀, hdom⟩
  obtain ⟨A₀, Cstar, hA₀, hCstar, hcol⟩ := exists_horizon_le_doubleExp
  set X := Real.log (2 * Cstar / k₀ + 1)
  set A := max A₀ (X + 3)
  have hAA₀ : A₀ ≤ A := le_max_left _ _
  have hAX : X + 3 ≤ A := le_max_right _ _
  have hle := hcol A hAA₀ k₀ hk₀
    (hdom A (hA₀.trans hAA₀) (windowRiemannKernel A)
      (isWindowTest_windowRiemannKernel (hA₀.trans hAA₀)) k₀ ⟨hk₀, le_rfl⟩)
  have hX_lt : X < Real.exp (A - 2) := by
    have h1 : X + 1 ≤ A - 2 := by linarith
    have h2 : X + 1 ≤ Real.exp (X + 1) := by
      rcases le_or_gt 0 (X + 1) with hx | hx
      · linarith [Real.add_one_le_exp (X + 1)]
      · linarith [Real.exp_pos (X + 1)]
    exact (lt_add_one X).trans_le (h2.trans (Real.exp_le_exp.mpr h1))
  have hexp_gt : 2 * Cstar / k₀ + 1 < Real.exp (Real.exp (A - 2)) := by
    calc 2 * Cstar / k₀ + 1 = Real.exp X := (Real.exp_log (by positivity)).symm
      _ < Real.exp (Real.exp (A - 2)) := Real.exp_lt_exp.mpr hX_lt
  have hsmall : Cstar * Real.exp (-Real.exp (A - 2)) < k₀ / 2 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
    have h1 : 2 * Cstar < k₀ * Real.exp (Real.exp (A - 2)) := by
      have := (div_lt_iff₀ hk₀).mp (by linarith : 2 * Cstar / k₀ < Real.exp (Real.exp (A - 2)))
      linarith
    linarith
  linarith

/-- **No uniform horizon for `backwardTateGammaForm + k · windowPoleForm`**. -/
theorem not_exists_uniform_horizon_backwardTateGamma :
    ¬ ∃ k₀ > 0, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        ∀ k ∈ Ioc 0 k₀,
          tatePointCount A H k ≤ backwardTateGammaForm k H + k * windowPoleForm H := by
  rintro ⟨k₀, hk₀, hdom⟩
  obtain ⟨A₀, Cstar, hA₀, hCstar, hcol⟩ := exists_horizon_le_doubleExp
  set X := Real.log (2 * Cstar / k₀ + 1)
  set A := max A₀ (X + 3)
  have hAA₀ : A₀ ≤ A := le_max_left _ _
  have hAX : X + 3 ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := hA₀.trans hAA₀
  have h1 := hdom A hA0 (windowRiemannKernel A) (isWindowTest_windowRiemannKernel hA0)
    k₀ ⟨hk₀, le_rfl⟩
  have h2 := backwardTateGammaForm_le_mul_archGammaForm_of_nonneg
    (windowRiemannKernel_nonneg A) k₀
  have hlin : tatePointCount A (windowRiemannKernel A) k₀ ≤
      k₀ * archWindowForm (windowRiemannKernel A) := by
    rw [archWindowForm, mul_add]; linarith
  have hle := hcol A hAA₀ k₀ hk₀ hlin
  have hX_lt : X < Real.exp (A - 2) := by
    have hp1 : X + 1 ≤ A - 2 := by linarith
    have hp2 : X + 1 ≤ Real.exp (X + 1) := by
      rcases le_or_gt 0 (X + 1) with hx | hx
      · linarith [Real.add_one_le_exp (X + 1)]
      · linarith [Real.exp_pos (X + 1)]
    exact (lt_add_one X).trans_le (hp2.trans (Real.exp_le_exp.mpr hp1))
  have hexp_gt : 2 * Cstar / k₀ + 1 < Real.exp (Real.exp (A - 2)) := by
    calc 2 * Cstar / k₀ + 1 = Real.exp X := (Real.exp_log (by positivity)).symm
      _ < Real.exp (Real.exp (A - 2)) := Real.exp_lt_exp.mpr hX_lt
  have hsmall : Cstar * Real.exp (-Real.exp (A - 2)) < k₀ / 2 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
    have hp1 : 2 * Cstar < k₀ * Real.exp (Real.exp (A - 2)) := by
      have := (div_lt_iff₀ hk₀).mp (by linarith : 2 * Cstar / k₀ < Real.exp (Real.exp (A - 2)))
      linarith
    linarith
  linarith

/-- **No uniform horizon for `symTateGammaForm + k · windowPoleForm`**. -/
theorem not_exists_uniform_horizon_symTateGamma :
    ¬ ∃ k₀ > 0, ∀ A : ℝ, 0 ≤ A → ∀ H : ℝ → ℝ, IsWindowTest A H →
        ∀ k ∈ Ioc 0 k₀,
          tatePointCount A H k ≤ symTateGammaForm k H + k * windowPoleForm H := by
  rintro ⟨k₀, hk₀, hdom⟩
  obtain ⟨A₀, Cstar, hA₀, hCstar, hcol⟩ := exists_horizon_le_doubleExp
  set X := Real.log (2 * Cstar / k₀ + 1)
  set A := max A₀ (X + 3)
  have hAA₀ : A₀ ≤ A := le_max_left _ _
  have hAX : X + 3 ≤ A := le_max_right _ _
  have hA0 : 0 ≤ A := hA₀.trans hAA₀
  have h1 := hdom A hA0 (windowRiemannKernel A) (isWindowTest_windowRiemannKernel hA0)
    k₀ ⟨hk₀, le_rfl⟩
  have h2 := symTateGammaForm_le_mul_archGammaForm_of_nonneg
    (windowRiemannKernel_nonneg A) hk₀.le
  have hlin : tatePointCount A (windowRiemannKernel A) k₀ ≤
      k₀ * archWindowForm (windowRiemannKernel A) := by
    rw [archWindowForm, mul_add]; linarith
  have hle := hcol A hAA₀ k₀ hk₀ hlin
  have hX_lt : X < Real.exp (A - 2) := by
    have hp1 : X + 1 ≤ A - 2 := by linarith
    have hp2 : X + 1 ≤ Real.exp (X + 1) := by
      rcases le_or_gt 0 (X + 1) with hx | hx
      · linarith [Real.add_one_le_exp (X + 1)]
      · linarith [Real.exp_pos (X + 1)]
    exact (lt_add_one X).trans_le (hp2.trans (Real.exp_le_exp.mpr hp1))
  have hexp_gt : 2 * Cstar / k₀ + 1 < Real.exp (Real.exp (A - 2)) := by
    calc 2 * Cstar / k₀ + 1 = Real.exp X := (Real.exp_log (by positivity)).symm
      _ < Real.exp (Real.exp (A - 2)) := Real.exp_lt_exp.mpr hX_lt
  have hsmall : Cstar * Real.exp (-Real.exp (A - 2)) < k₀ / 2 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)]
    have hp1 : 2 * Cstar < k₀ * Real.exp (Real.exp (A - 2)) := by
      have := (div_lt_iff₀ hk₀).mp (by linarith : 2 * Cstar / k₀ < Real.exp (Real.exp (A - 2)))
      linarith
    linarith
  linarith

end GaloisForLFunctions.ArchimedeanTateDomination

#print axioms GaloisForLFunctions.ArchimedeanTateDomination.not_weilPositiveDegree_two_mul_jordanTotient
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.not_forall_window_domination_archGamma_pole
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.exists_horizon_le_doubleExp
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.not_exists_uniform_horizon_backwardTateGamma
