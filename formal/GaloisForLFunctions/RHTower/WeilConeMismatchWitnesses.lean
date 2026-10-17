import GaloisForLFunctions.RHTower.PrimeBlindPoleCurvatureFloor
import GaloisForLFunctions.RHTower.WeilPositivityMertensConstantObstruction
import GaloisForLFunctions.RHTower.WeilSymbolMertensExpansion
import GaloisForLFunctions.RHTower.DilationFreeSetMeasure

/-!
# The Bochner cone and the pointwise cone of Weil tests are different

Positivity methods on the modular surface (maximum principles, transfer-operator positivity,
Perron–Frobenius) act on the *pointwise cone*: functions or measures that are nonnegative on an arc
or a domain.  The Weil criterion lives on the *Bochner cone*: autocorrelations `k_f = f ⋆ f̃` of
tests `f`, whose Fourier transforms are nonnegative.  This module records, with explicit witnesses
built from one smooth bump, that neither cone contains the other, and where they meet.

* **Bochner, not pointwise.**  The test `f(u) = b(u) − b(u − 3)` (a bump minus its translate) is a
  `C²` compactly supported Weil test whose autocorrelation is negative at lag `3`:
  `k_f(3) = −∫ b²` (`weilTest_twoSignedTest_three`, `weilTest_self_re_neg_twoSignedWeilTest`).
* **Pointwise, not Bochner.**  The profile `g(u) = b(u − 3) + b(u + 3)` is nonnegative and smooth,
  but it is the autocorrelation of no Weil test: an autocorrelation satisfies
  `|k_f(x)| ≤ k_f(0) = ∫|f|²`, while `g(0) = 0 < 1 = g(3)` (`twoHumpProfile_ne_weilTest_self`).
* **Where they meet.**  A nonnegative test whose autocorrelation vanishes at every lag `log n`,
  `n ≥ 2`, is positive only on a set of measure at most `log 2` (`nonneg_primeBlind_window`,
  from `DilationFree.volume_pos_le_log_two_of_primeBlind`): the two cones intersect, among
  prime-blind tests, only in the one-window sector.

Hence a positivity statement proved on the pointwise cone transfers to the Weil criterion only on
the window sector; a producer needs a transfer from the Bochner cone to a pointwise cone that is
compatible with blindness.
-/

open Complex MeasureTheory Set Filter ComplexConjugate

noncomputable section

namespace RHTower

open Zeta23 RHTower.WeilOneSided

/-! ## The reference bump -/

/-- A smooth bump on `ℝ` centred at `0`: equal to `1` on `[−½, ½]`, supported in `(−1, 1)`. -/
def mismatchBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem mismatchBump_rIn : mismatchBump.rIn = 1 / 2 := rfl

theorem mismatchBump_rOut : mismatchBump.rOut = 1 := rfl

theorem mismatchBump_eq_one_of_abs_le {t : ℝ} (ht : |t| ≤ 1 / 2) : (mismatchBump t : ℝ) = 1 := by
  apply mismatchBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, mismatchBump_rIn]
  exact ht

theorem mismatchBump_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) : (mismatchBump t : ℝ) = 0 := by
  apply mismatchBump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, mismatchBump_rOut]
  exact ht

/-- The bump and a translate by at least `2` have disjoint supports. -/
theorem mismatchBump_mul_shift_eq_zero {t c : ℝ} (hc : 2 ≤ |c|) :
    (mismatchBump t : ℝ) * mismatchBump (t - c) = 0 := by
  by_cases h : (mismatchBump t : ℝ) = 0
  · rw [h, zero_mul]
  · have hmem : t ∈ Function.support (mismatchBump : ℝ → ℝ) := h
    rw [mismatchBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, mismatchBump_rOut]
      at hmem
    have hz : (mismatchBump (t - c) : ℝ) = 0 := by
      apply mismatchBump_eq_zero_of_one_le_abs
      have := abs_sub_abs_le_abs_sub c t
      rw [abs_sub_comm] at this
      linarith
    rw [hz, mul_zero]

theorem hasCompactSupport_mismatchBump_shift (c : ℝ) :
    HasCompactSupport (fun u : ℝ => ((mismatchBump (u - c) : ℝ) : ℂ)) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := c - 1) (b := c + 1)) ?_
  intro u hu
  have hu' : (mismatchBump (u - c) : ℝ) ≠ 0 := by
    intro h; apply hu; simp [h]
  have hmem : u - c ∈ Function.support (mismatchBump : ℝ → ℝ) := hu'
  rw [mismatchBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, mismatchBump_rOut,
    abs_lt] at hmem
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

theorem contDiff_mismatchBump_shift (c : ℝ) :
    ContDiff ℝ 2 (fun u : ℝ => ((mismatchBump (u - c) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (mismatchBump.contDiff.comp (contDiff_id.sub contDiff_const))

theorem integrable_mismatchBump_sq : Integrable (fun u : ℝ => (mismatchBump u : ℝ) ^ 2) := by
  have hc : Continuous (fun u : ℝ => (mismatchBump u : ℝ) ^ 2) := mismatchBump.continuous.pow 2
  have hs : HasCompactSupport (fun u : ℝ => (mismatchBump u : ℝ) ^ 2) :=
    mismatchBump.hasCompactSupport.comp_left (g := fun x : ℝ => x ^ 2) (zero_pow two_ne_zero)
  exact hc.integrable_of_hasCompactSupport hs

theorem setIntegral_Icc_mismatchBump_sq :
    ∫ u in Icc (-1 / 2 : ℝ) (1 / 2), (mismatchBump u : ℝ) ^ 2 = 1 := by
  have h1 : ∀ u ∈ Icc (-1 / 2 : ℝ) (1 / 2), (mismatchBump u : ℝ) ^ 2 = 1 := fun u hu => by
    rw [mismatchBump_eq_one_of_abs_le (abs_le.2 ⟨by linarith [hu.1], hu.2⟩)]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Icc h1, setIntegral_const, measureReal_def,
    Real.volume_Icc, smul_eq_mul, mul_one, ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-- `∫ b² ≥ 1`. -/
theorem one_le_integral_mismatchBump_sq : 1 ≤ ∫ u : ℝ, (mismatchBump u : ℝ) ^ 2 := by
  rw [← setIntegral_Icc_mismatchBump_sq]
  exact setIntegral_le_integral integrable_mismatchBump_sq
    (Eventually.of_forall fun u => sq_nonneg _)

/-! ## Bochner, not pointwise -/

/-- The two-signed test `f(u) = b(u) − b(u − 3)`. -/
def twoSignedTest (u : ℝ) : ℂ := ((mismatchBump u : ℝ) : ℂ) - ((mismatchBump (u - 3) : ℝ) : ℂ)

theorem contDiff_twoSignedTest : ContDiff ℝ 2 twoSignedTest := by
  have h0 := contDiff_mismatchBump_shift 0
  simp only [sub_zero] at h0
  exact h0.sub (contDiff_mismatchBump_shift 3)

theorem hasCompactSupport_twoSignedTest : HasCompactSupport twoSignedTest := by
  have h0 := hasCompactSupport_mismatchBump_shift 0
  simp only [sub_zero] at h0
  exact h0.sub (hasCompactSupport_mismatchBump_shift 3)

/-- The two-signed test as a Weil test. -/
def twoSignedWeilTest : WeilTestFn :=
  ⟨twoSignedTest, contDiff_twoSignedTest, hasCompactSupport_twoSignedTest⟩

/-- The autocorrelation of the two-signed test at lag `3` is `−∫ b²`. -/
theorem weilTest_twoSignedTest_three :
    EF.weilTest twoSignedTest twoSignedTest 3 = -((∫ u : ℝ, (mismatchBump u : ℝ) ^ 2 : ℝ) : ℂ) := by
  rw [weilTest_apply_eq]
  have hpt : ∀ t : ℝ, twoSignedTest t * conj (twoSignedTest (t - 3)) =
      -((((mismatchBump (t - 3) : ℝ) ^ 2 : ℝ)) : ℂ) := by
    intro t
    have h1 : (mismatchBump t : ℝ) * mismatchBump (t - 3) = 0 :=
      mismatchBump_mul_shift_eq_zero (by norm_num)
    have h2 : (mismatchBump t : ℝ) * mismatchBump (t - 3 - 3) = 0 := by
      rw [show t - 3 - 3 = t - 6 by ring]
      exact mismatchBump_mul_shift_eq_zero (by norm_num)
    have h3 : (mismatchBump (t - 3) : ℝ) * mismatchBump (t - 3 - 3) = 0 :=
      mismatchBump_mul_shift_eq_zero (by norm_num)
    have h1' : ((mismatchBump t : ℝ) : ℂ) * ((mismatchBump (t - 3) : ℝ) : ℂ) = 0 := by
      exact_mod_cast h1
    have h2' : ((mismatchBump t : ℝ) : ℂ) * ((mismatchBump (t - 3 - 3) : ℝ) : ℂ) = 0 := by
      exact_mod_cast h2
    have h3' : ((mismatchBump (t - 3) : ℝ) : ℂ) * ((mismatchBump (t - 3 - 3) : ℝ) : ℂ) = 0 := by
      exact_mod_cast h3
    simp only [twoSignedTest, map_sub, Complex.conj_ofReal]
    push_cast
    linear_combination h1' - h2' + h3'
  simp_rw [hpt]
  rw [integral_neg, ← integral_complex_ofReal]
  congr 1
  have := integral_sub_right_eq_self (μ := volume) (fun u : ℝ => (mismatchBump u : ℝ) ^ 2) (3 : ℝ)
  exact_mod_cast this

/-- **Bochner, not pointwise.**  A Weil test whose autocorrelation is negative somewhere. -/
theorem weilTest_self_re_neg_twoSignedWeilTest :
    (EF.weilTest twoSignedWeilTest.1 twoSignedWeilTest.1 3).re < 0 := by
  show (EF.weilTest twoSignedTest twoSignedTest 3).re < 0
  rw [weilTest_twoSignedTest_three]
  simp only [Complex.neg_re, Complex.ofReal_re, neg_lt_zero]
  linarith [one_le_integral_mismatchBump_sq]

/-! ## Pointwise, not Bochner -/

/-- The nonnegative two-hump profile `g(u) = b(u − 3) + b(u + 3)`. -/
def twoHumpProfile (u : ℝ) : ℂ :=
  ((mismatchBump (u - 3) : ℝ) : ℂ) + ((mismatchBump (u + 3) : ℝ) : ℂ)

theorem twoHumpProfile_re_nonneg (u : ℝ) : 0 ≤ (twoHumpProfile u).re := by
  simp only [twoHumpProfile, Complex.add_re, Complex.ofReal_re]
  exact add_nonneg mismatchBump.nonneg mismatchBump.nonneg

theorem twoHumpProfile_im (u : ℝ) : (twoHumpProfile u).im = 0 := by
  simp [twoHumpProfile]

theorem contDiff_twoHumpProfile : ContDiff ℝ 2 twoHumpProfile := by
  have h := contDiff_mismatchBump_shift (-3)
  simp only [sub_neg_eq_add] at h
  exact (contDiff_mismatchBump_shift 3).add h

theorem hasCompactSupport_twoHumpProfile : HasCompactSupport twoHumpProfile := by
  have h := hasCompactSupport_mismatchBump_shift (-3)
  simp only [sub_neg_eq_add] at h
  exact (hasCompactSupport_mismatchBump_shift 3).add h

theorem twoHumpProfile_zero : twoHumpProfile 0 = 0 := by
  unfold twoHumpProfile
  rw [mismatchBump_eq_zero_of_one_le_abs (by norm_num),
    mismatchBump_eq_zero_of_one_le_abs (by norm_num)]
  simp

theorem twoHumpProfile_three : twoHumpProfile 3 = 1 := by
  unfold twoHumpProfile
  rw [show (3 : ℝ) - 3 = 0 by ring, mismatchBump_eq_one_of_abs_le (by norm_num),
    mismatchBump_eq_zero_of_one_le_abs (by norm_num)]
  simp

/-- **Pointwise, not Bochner.**  The nonnegative smooth profile `g` is the autocorrelation of no
Weil test: autocorrelations are bounded by their value at `0`, and `g(0) = 0 < 1 = g(3)`. -/
theorem twoHumpProfile_ne_weilTest_self (f : WeilTestFn) :
    EF.weilTest f.1 f.1 ≠ twoHumpProfile := by
  intro h
  have h0 : EF.weilTest f.1 f.1 0 = 0 := by rw [h, twoHumpProfile_zero]
  have hmass : testMass f = 0 := by
    have := weilTest_self_zero (f := f.1)
    rw [h0] at this
    unfold testMass
    exact_mod_cast this.symm
  have h3 := norm_weilTest_self_le_testMass f 3
  rw [h, twoHumpProfile_three, norm_one, hmass] at h3
  linarith

/-! ## Where the cones meet -/

/-- **The meeting locus is the window sector.**  A nonnegative test whose autocorrelation vanishes
at every lag `log n`, `n ≥ 2`, is positive on a set of measure at most `log 2`. -/
theorem nonneg_primeBlind_window {g : ℝ → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hint : ∀ n : ℕ, 2 ≤ n → Integrable (fun x => g (x + Real.log n) * g x))
    (hblind : ∀ n : ℕ, 2 ≤ n → ∫ x, g (x + Real.log n) * g x = 0) :
    volume {x | 0 < g x} ≤ ENNReal.ofReal (Real.log 2) :=
  DilationFree.volume_pos_le_log_two_of_primeBlind hg hg0 hint hblind

end RHTower
