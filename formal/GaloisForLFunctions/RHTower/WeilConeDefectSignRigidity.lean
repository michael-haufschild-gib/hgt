import GaloisForLFunctions.RHTower.WeilConePoleDualityAnatomy
import GaloisForLFunctions.RHTower.MarkovShiftPolarizationAndEvenPrimitivePBAP
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheEvolutionStartsPositive

/-!
# The defect measure of a weight system carries no sign

For real weights `λ` on `n ≥ 2` let `σ_λ` be the difference of the spectral measures of `W_λ` and
`W_Λ`. On an autocorrelation `k = f ⋆ f̃` it is paired as
`∫ |f̂|² dσ_λ = W_λ(k) − W_Λ(k) = −Σ_{n≥2} (λ(n) − Λ(n)) n^{−½} (k(log n) + k(−log n))`
(`weilDefect_eq`): the Fourier transform of `σ_λ` is carried by `±log n`, `n ≥ 2`.

* **No sign** (`eq_vonMangoldt_of_weilDefect_nonneg`, `eq_vonMangoldt_of_weilDefect_nonpos`): if
  `σ_λ ≥ 0` on every autocorrelation, or `σ_λ ≤ 0` on every autocorrelation, then `λ = Λ`. For a bump
  `g` of width `1/(n₀ + 1)`, the even and odd shifts of `g` by `log n₀` see only the atom at `n₀`,
  with the opposite values `∓(λ − Λ)(n₀) n₀^{−½} ‖g‖²/2` (`weilDefect_evenAtomTest`,
  `weilDefect_oddAtomTest`).
* **No proportional move** (`eq_one_and_eq_vonMangoldt_of_weilFunctional_eq_mul`): if `W_λ = c·W_Λ`
  on autocorrelations, then `c = 1` and `λ = Λ`. A bump supported in `(−1/6, 1/6)` is prime-blind,
  and short tests have `W_Λ > 0`.
* **Atomicity on the cone** (`weilDefect_eq_zero_of_weilPositiveFull`): the Weil cone is `{Λ}`
  unconditionally, so every cone element has `σ_λ = 0`.
-/

open Complex MeasureTheory Set Filter Zeta23
open scoped Real

namespace RHTower.PoleDualityAnatomy

open RHTower.WeilOneSided

noncomputable section

/-- `W_λ − W_Λ` on a test `k` (real parts): the pairing of the defect measure `σ_λ`. -/
def weilDefect (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℝ :=
  (weilFullFunctional lam k).re -
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) k).re

/-- The weight of the atom at `n` in `W_λ − W_Λ`. -/
def defectWeight (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0

/-- **The defect is carried by `±log n`**: `W_λ(k) − W_Λ(k) = −Σ_n a_n (k(log n) + k(−log n))`. -/
theorem weilDefect_eq (lam : ℕ → ℝ) {k : ℝ → ℂ} (hk : HasCompactSupport k) :
    weilDefect lam k = -(∑' n : ℕ, ((defectWeight lam n : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n))).re := by
  rw [weilDefect, weilFullFunctional_eq_sub lam hk, weilFullFunctional_vonMangoldt]
  simp only [defectWeight, Complex.sub_re]
  ring

/-- A test that sees only the atom at `n₀` has the defect of that single atom. -/
theorem weilDefect_eq_single (lam : ℕ → ℝ) {k : ℝ → ℂ} (hk : HasCompactSupport k) {n₀ : ℕ}
    (hn₀ : 2 ≤ n₀) {v : ℝ}
    (hv : ∀ n : ℕ, 2 ≤ n → k (Real.log n) + k (-Real.log n) = if n = n₀ then (v : ℂ) else 0) :
    weilDefect lam k = -(defectWeight lam n₀ * v) := by
  rw [weilDefect_eq lam hk, tsum_eq_single n₀]
  · rw [hv n₀ hn₀, if_pos rfl, ← Complex.ofReal_mul, Complex.ofReal_re]
  · intro n hn
    by_cases h2 : 2 ≤ n
    · rw [hv n h2, if_neg hn, mul_zero]
    · simp [defectWeight, h2]

/-! ### A bump and its autocorrelation -/

/-- A smooth bump of radius `δ` centred at the origin. -/
def bump {δ : ℝ} (hδ : 0 < δ) : ℝ → ℝ :=
  (⟨δ / 2, δ, by positivity, by linarith⟩ : ContDiffBump (0 : ℝ))

theorem contDiff_bump {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ 2 (bump hδ) :=
  ContDiffBump.contDiff _

theorem hasCompactSupport_bump {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (bump hδ) :=
  ContDiffBump.hasCompactSupport _

theorem bump_eq_zero {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : δ ≤ |x|) : bump hδ x = 0 := by
  by_contra hne
  have hmem : x ∈ Function.support (bump hδ) := hne
  rw [bump, ContDiffBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
  linarith

theorem bump_zero {δ : ℝ} (hδ : 0 < δ) : bump hδ 0 = 1 :=
  ContDiffBump.one_of_mem_closedBall _ (Metric.mem_closedBall_self (by positivity))

/-- The autocorrelation of the bump vanishes off `(−2δ, 2δ)`. -/
theorem autoCorr_bump_eq_zero {δ : ℝ} (hδ : 0 < δ) {y : ℝ} (hy : 2 * δ ≤ |y|) :
    autoCorr (bump hδ) y = 0 := by
  unfold autoCorr
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  change bump hδ t * bump hδ (t - y) = 0
  rcases le_or_gt δ |t| with ht | ht
  · rw [bump_eq_zero hδ ht, zero_mul]
  · have : δ ≤ |t - y| := by
      have := abs_sub_abs_le_abs_sub y t
      rw [abs_sub_comm] at this
      linarith
    rw [bump_eq_zero hδ this, mul_zero]

/-- The bump has positive energy `ρ(0) = ∫ g² > 0`. -/
theorem autoCorr_bump_zero_pos {δ : ℝ} (hδ : 0 < δ) : 0 < autoCorr (bump hδ) 0 := by
  unfold autoCorr
  simp only [sub_zero]
  have hc : Continuous fun t => bump hδ t * bump hδ t :=
    (contDiff_bump hδ).continuous.mul (contDiff_bump hδ).continuous
  have hcs : HasCompactSupport fun t => bump hδ t * bump hδ t :=
    (hasCompactSupport_bump hδ).mul_left
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun t => mul_self_nonneg _) (x := 0) ?_
  rw [bump_zero hδ, mul_one]
  exact one_ne_zero

/-! ### Separation of the logarithms -/

/-- Logarithms of distinct positive integers `n, n₀` are at least `1/(n₀ + 1)` apart. -/
theorem one_div_succ_le_abs_log_sub_log {n n₀ : ℕ} (hn : 1 ≤ n) (hn₀ : 1 ≤ n₀) (hne : n ≠ n₀) :
    1 / ((n₀ : ℝ) + 1) ≤ |Real.log n - Real.log n₀| := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀R : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `n + 1 ≤ n₀`: `log n₀ − log n ≥ 1 − n/n₀ ≥ 1/n₀`
    have hle : (n : ℝ) + 1 ≤ n₀ := by exact_mod_cast hlt
    have h0 : 0 < 1 / ((n₀ : ℝ) + 1) := by positivity
    have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < n₀ / n by positivity)
    rw [Real.log_div (by positivity) (by positivity), inv_div] at hlog
    have h1 : 1 / ((n₀ : ℝ) + 1) ≤ 1 - n / n₀ := by
      have h2 : 1 - (n : ℝ) / n₀ = (n₀ - n) / n₀ := by field_simp
      rw [h2, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · -- `n₀ + 1 ≤ n`: `log n − log n₀ ≥ 1 − n₀/n ≥ 1/(n₀ + 1)`
    have hle : (n₀ : ℝ) + 1 ≤ n := by exact_mod_cast hgt
    have h0 : 0 < 1 / ((n₀ : ℝ) + 1) := by positivity
    have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < n / n₀ by positivity)
    rw [Real.log_div (by positivity) (by positivity), inv_div] at hlog
    have h1 : 1 / ((n₀ : ℝ) + 1) ≤ 1 - n₀ / n := by
      have h2 : 1 - (n₀ : ℝ) / n = (n - n₀) / n := by field_simp
      rw [h2, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [abs_of_nonneg (by linarith)]
    linarith

/-! ### The two shifted tests at an atom -/

section Shifts

variable {n₀ : ℕ} (hn₀ : 2 ≤ n₀)

/-- The bump width `δ = 1/(2(n₀ + 1))`. -/
def shiftWidth (n₀ : ℕ) : ℝ := 1 / (2 * ((n₀ : ℝ) + 1))

theorem shiftWidth_pos (n₀ : ℕ) : 0 < shiftWidth n₀ := by unfold shiftWidth; positivity

theorem two_mul_shiftWidth (n₀ : ℕ) : 2 * shiftWidth n₀ = 1 / ((n₀ : ℝ) + 1) := by
  unfold shiftWidth; field_simp

include hn₀ in
/-- For `n₀ ≥ 2` the doubled width `1/(n₀+1) ≤ 1/3` is below every `log n`, `n ≥ 2`. -/
theorem two_mul_shiftWidth_le_log {n : ℕ} (hn : 2 ≤ n) : 2 * shiftWidth n₀ ≤ Real.log n := by
  rw [two_mul_shiftWidth]
  have h1 : 1 / ((n₀ : ℝ) + 1) ≤ 1 / 3 := by
    have : (2 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have h3 := Real.log_two_gt_d9
  linarith

/-- The bump used at the atom `n₀`. -/
def atomBump (n₀ : ℕ) : ℝ → ℝ := bump (shiftWidth_pos n₀)

/-- The even shift of the bump by `log n₀`. -/
def evenAtomTest (n₀ : ℕ) : ℝ → ℂ := fun u => (evenShift (atomBump n₀) (Real.log n₀) u : ℂ)

/-- The odd shift of the bump by `log n₀`. -/
def oddAtomTest (n₀ : ℕ) : ℝ → ℂ := fun u => (oddShift (atomBump n₀) (Real.log n₀) u : ℂ)

theorem contDiff_atomBump (n₀ : ℕ) : ContDiff ℝ 2 (atomBump n₀) := contDiff_bump _

theorem hasCompactSupport_atomBump (n₀ : ℕ) : HasCompactSupport (atomBump n₀) :=
  hasCompactSupport_bump _

theorem contDiff_evenAtomTest (n₀ : ℕ) : ContDiff ℝ 2 (evenAtomTest n₀) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_evenShift (contDiff_atomBump n₀) _)

theorem hasCompactSupport_evenAtomTest (n₀ : ℕ) : HasCompactSupport (evenAtomTest n₀) :=
  (hasCompactSupport_evenShift (hasCompactSupport_atomBump n₀) _).comp_left Complex.ofReal_zero

theorem contDiff_oddAtomTest (n₀ : ℕ) : ContDiff ℝ 2 (oddAtomTest n₀) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_oddShift (contDiff_atomBump n₀) _)

theorem hasCompactSupport_oddAtomTest (n₀ : ℕ) : HasCompactSupport (oddAtomTest n₀) :=
  (hasCompactSupport_oddShift (hasCompactSupport_atomBump n₀) _).comp_left Complex.ofReal_zero

include hn₀ in
/-- The autocorrelation `ρ` of the atom bump at the lags `±log n` and `±log n ± log n₀`. -/
theorem autoCorr_atomBump_lags {n : ℕ} (hn : 2 ≤ n) :
    autoCorr (atomBump n₀) (Real.log n) = 0 ∧ autoCorr (atomBump n₀) (-Real.log n) = 0 ∧
      autoCorr (atomBump n₀) (Real.log n + Real.log n₀) = 0 ∧
      autoCorr (atomBump n₀) (-Real.log n - Real.log n₀) = 0 ∧
      autoCorr (atomBump n₀) (Real.log n - Real.log n₀) =
        (if n = n₀ then autoCorr (atomBump n₀) 0 else 0) ∧
      autoCorr (atomBump n₀) (-Real.log n + Real.log n₀) =
        (if n = n₀ then autoCorr (atomBump n₀) 0 else 0) := by
  have hw := two_mul_shiftWidth_le_log hn₀ hn
  have hw₀ := two_mul_shiftWidth_le_log hn₀ hn₀
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogn₀ : 0 ≤ Real.log n₀ := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n₀ by omega))
  have hz : ∀ y : ℝ, 2 * shiftWidth n₀ ≤ |y| → autoCorr (atomBump n₀) y = 0 :=
    fun y hy => autoCorr_bump_eq_zero _ hy
  refine ⟨hz _ (by rw [abs_of_nonneg hlogn]; exact hw),
    hz _ (by rw [abs_neg, abs_of_nonneg hlogn]; exact hw),
    hz _ (by rw [abs_of_nonneg (by linarith)]; linarith),
    hz _ (by rw [show -Real.log n - Real.log n₀ = -(Real.log n + Real.log n₀) by ring, abs_neg,
      abs_of_nonneg (by linarith)]; linarith), ?_, ?_⟩
  · by_cases hne : n = n₀
    · rw [if_pos hne, hne, sub_self]
    · rw [if_neg hne]
      refine hz _ ?_
      rw [two_mul_shiftWidth]
      exact one_div_succ_le_abs_log_sub_log (by omega) (by omega) hne
  · by_cases hne : n = n₀
    · rw [if_pos hne, hne, neg_add_cancel]
    · rw [if_neg hne]
      refine hz _ ?_
      rw [two_mul_shiftWidth, show -Real.log n + Real.log n₀ = -(Real.log n - Real.log n₀) by ring,
        abs_neg]
      exact one_div_succ_le_abs_log_sub_log (by omega) (by omega) hne

include hn₀ in
/-- The even shift sees the atom at `n₀` with defect `−a_{n₀} ρ(0)/2`. -/
theorem weilDefect_evenAtomTest (lam : ℕ → ℝ) :
    weilDefect lam (EF.weilTest (evenAtomTest n₀) (evenAtomTest n₀)) =
      -(defectWeight lam n₀ * (autoCorr (atomBump n₀) 0 / 2)) := by
  have hc := (contDiff_atomBump n₀).continuous
  have hcs := hasCompactSupport_atomBump n₀
  have hk : HasCompactSupport (EF.weilTest (evenAtomTest n₀) (evenAtomTest n₀)) :=
    EF.weilTest_hasCompactSupport (hasCompactSupport_evenAtomTest n₀)
      (hasCompactSupport_evenAtomTest n₀)
  refine weilDefect_eq_single lam hk hn₀ fun n hn => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := autoCorr_atomBump_lags hn₀ hn
  unfold evenAtomTest
  rw [weilTest_evenShift hc hcs, weilTest_evenShift hc hcs, h1, h2, h3, h4, h5, h6]
  split_ifs <;> push_cast <;> ring

include hn₀ in
/-- The odd shift sees the atom at `n₀` with defect `+a_{n₀} ρ(0)/2`. -/
theorem weilDefect_oddAtomTest (lam : ℕ → ℝ) :
    weilDefect lam (EF.weilTest (oddAtomTest n₀) (oddAtomTest n₀)) =
      -(defectWeight lam n₀ * (-(autoCorr (atomBump n₀) 0 / 2))) := by
  have hc := (contDiff_atomBump n₀).continuous
  have hcs := hasCompactSupport_atomBump n₀
  have hk : HasCompactSupport (EF.weilTest (oddAtomTest n₀) (oddAtomTest n₀)) :=
    EF.weilTest_hasCompactSupport (hasCompactSupport_oddAtomTest n₀)
      (hasCompactSupport_oddAtomTest n₀)
  refine weilDefect_eq_single lam hk hn₀ fun n hn => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := autoCorr_atomBump_lags hn₀ hn
  unfold oddAtomTest
  rw [weilTest_oddShift hc hcs, weilTest_oddShift hc hcs, h1, h2, h3, h5, h4, h6]
  split_ifs <;> push_cast <;> ring

end Shifts

/-! ### No sign -/

/-- A vanishing atom weight means `λ(n) = Λ(n)`. -/
theorem eq_of_defectWeight_eq_zero {lam : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n)
    (h : defectWeight lam n = 0) : lam n = ArithmeticFunction.vonMangoldt n := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  rw [defectWeight, if_pos hn, div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h hs.ne'

/-- The atom weight vanishes as soon as the defect has one sign on the two shifted tests. -/
theorem defectWeight_eq_zero_of_signs {lam : ℕ → ℝ} {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (h : (0 ≤ weilDefect lam (EF.weilTest (evenAtomTest n₀) (evenAtomTest n₀)) ∧
        0 ≤ weilDefect lam (EF.weilTest (oddAtomTest n₀) (oddAtomTest n₀))) ∨
      (weilDefect lam (EF.weilTest (evenAtomTest n₀) (evenAtomTest n₀)) ≤ 0 ∧
        weilDefect lam (EF.weilTest (oddAtomTest n₀) (oddAtomTest n₀)) ≤ 0)) :
    defectWeight lam n₀ = 0 := by
  rw [weilDefect_evenAtomTest hn₀, weilDefect_oddAtomTest hn₀] at h
  have hρ := autoCorr_bump_zero_pos (shiftWidth_pos n₀)
  change 0 < autoCorr (atomBump n₀) 0 at hρ
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : defectWeight lam n₀ * autoCorr (atomBump n₀) 0 = 0 := by nlinarith
    exact (mul_eq_zero.mp this).resolve_right hρ.ne'
  · have : defectWeight lam n₀ * autoCorr (atomBump n₀) 0 = 0 := by nlinarith
    exact (mul_eq_zero.mp this).resolve_right hρ.ne'

/-- **A nonnegative defect measure vanishes**: if `W_λ ≥ W_Λ` on every autocorrelation of a
`C²_c` test, then `λ = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilDefect_nonneg {lam : ℕ → ℝ}
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → 0 ≤ weilDefect lam (EF.weilTest f f)) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := fun n hn =>
  eq_of_defectWeight_eq_zero hn (defectWeight_eq_zero_of_signs hn (Or.inl
    ⟨h _ (contDiff_evenAtomTest n) (hasCompactSupport_evenAtomTest n),
      h _ (contDiff_oddAtomTest n) (hasCompactSupport_oddAtomTest n)⟩))

/-- **A nonpositive defect measure vanishes**: if `W_λ ≤ W_Λ` on every autocorrelation of a
`C²_c` test, then `λ = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilDefect_nonpos {lam : ℕ → ℝ}
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → weilDefect lam (EF.weilTest f f) ≤ 0) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := fun n hn =>
  eq_of_defectWeight_eq_zero hn (defectWeight_eq_zero_of_signs hn (Or.inr
    ⟨h _ (contDiff_evenAtomTest n) (hasCompactSupport_evenAtomTest n),
      h _ (contDiff_oddAtomTest n) (hasCompactSupport_oddAtomTest n)⟩))

/-! ### No proportional move -/

/-- The bump of radius `1/6`, as a complex test. -/
def shortTest : ℝ → ℂ := fun u => (bump (show (0 : ℝ) < 1 / 6 by norm_num) u : ℂ)

/-- The short test is blind to every prime atom. -/
theorem weilDefect_shortTest (lam : ℕ → ℝ) :
    weilDefect lam (EF.weilTest shortTest shortTest) = 0 := by
  have hb := contDiff_bump (show (0 : ℝ) < 1 / 6 by norm_num)
  have hbs := hasCompactSupport_bump (show (0 : ℝ) < 1 / 6 by norm_num)
  have hk : HasCompactSupport (EF.weilTest shortTest shortTest) :=
    EF.weilTest_hasCompactSupport (hbs.comp_left Complex.ofReal_zero)
      (hbs.comp_left Complex.ofReal_zero)
  rw [weilDefect_eq lam hk]
  have hz : ∀ n : ℕ, ((defectWeight lam n : ℝ) : ℂ) *
      (EF.weilTest shortTest shortTest (Real.log n) +
        EF.weilTest shortTest shortTest (-Real.log n)) = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have h3 := Real.log_two_gt_d9
      have hpos : 0 ≤ Real.log n := by linarith
      have hz1 : autoCorr (bump (show (0 : ℝ) < 1 / 6 by norm_num)) (Real.log n) = 0 :=
        autoCorr_bump_eq_zero _ (by rw [abs_of_nonneg hpos]; linarith)
      have hz2 : autoCorr (bump (show (0 : ℝ) < 1 / 6 by norm_num)) (-Real.log n) = 0 :=
        autoCorr_bump_eq_zero _ (by rw [abs_neg, abs_of_nonneg hpos]; linarith)
      have e1 : EF.weilTest shortTest shortTest (Real.log n) =
          ((autoCorr (bump (show (0 : ℝ) < 1 / 6 by norm_num)) (Real.log n) : ℝ) : ℂ) :=
        weilTest_liftC _ _
      have e2 : EF.weilTest shortTest shortTest (-Real.log n) =
          ((autoCorr (bump (show (0 : ℝ) < 1 / 6 by norm_num)) (-Real.log n) : ℝ) : ℂ) :=
        weilTest_liftC _ _
      rw [e1, e2, hz1, hz2]
      simp
    · simp [defectWeight, hn]
  simp only [hz, tsum_zero, Complex.zero_re, neg_zero]

/-- The short test has positive Weil energy. -/
theorem weilFunctional_shortTest_pos :
    0 < (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest shortTest shortTest)).re := by
  have hb := contDiff_bump (show (0 : ℝ) < 1 / 6 by norm_num)
  have hbs := hasCompactSupport_bump (show (0 : ℝ) < 1 / 6 by norm_num)
  have hpos := GaloisForLFunctions.GrowingWindowsOfSpecZ.weilQuad_pos_of_short
    (G := bump (show (0 : ℝ) < 1 / 6 by norm_num)) ⟨hb, hbs⟩
    (fun h0 => by
      have := congrFun h0 0
      rw [bump_zero] at this
      exact one_ne_zero this)
    (c := 1 / 4) (L := 1 / 2) (by norm_num) (fun u hu => bump_eq_zero _ (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith))
  exact hpos

/-- **No proportional move**: if `W_λ = c·W_Λ` on every autocorrelation (the spectral measure of
`λ` is `c μ_ζ`), then `c = 1` and `λ = Λ` on `n ≥ 2`. -/
theorem eq_one_and_eq_vonMangoldt_of_weilFunctional_eq_mul {lam : ℕ → ℝ} {c : ℝ}
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      (weilFullFunctional lam (EF.weilTest f f)).re =
        c * (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest f f)).re) :
    c = 1 ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hb := contDiff_bump (show (0 : ℝ) < 1 / 6 by norm_num)
  have hbs := hasCompactSupport_bump (show (0 : ℝ) < 1 / 6 by norm_num)
  have hQ := weilFunctional_shortTest_pos
  have hD := weilDefect_shortTest lam
  have hS := h shortTest (Complex.ofRealCLM.contDiff.comp hb) (hbs.comp_left Complex.ofReal_zero)
  rw [weilDefect] at hD
  have hc1 : c = 1 := by
    have : (c - 1) * (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest shortTest shortTest)).re = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_right hQ.ne'
    linarith
  refine ⟨hc1, eq_vonMangoldt_of_weilDefect_nonneg fun f hf hfc => ?_⟩
  rw [weilDefect, h f hf hfc, hc1, one_mul, sub_self]

/-! ### Atomicity on the cone -/

/-- **Every element of the Weil cone has zero defect measure.** -/
theorem weilDefect_eq_zero_of_weilPositiveFull {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {k : ℝ → ℂ} (hk : HasCompactSupport k) : weilDefect lam k = 0 := by
  have hl := RHTower.WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hW
  rw [weilDefect_eq lam hk]
  have hz : ∀ n : ℕ, defectWeight lam n = 0 := fun n => by
    by_cases hn : 2 ≤ n
    · rw [defectWeight, if_pos hn, hl n hn, sub_self, zero_div]
    · rw [defectWeight, if_neg hn]
  simp only [hz, Complex.ofReal_zero, zero_mul, tsum_zero, Complex.zero_re, neg_zero]

end

end RHTower.PoleDualityAnatomy
