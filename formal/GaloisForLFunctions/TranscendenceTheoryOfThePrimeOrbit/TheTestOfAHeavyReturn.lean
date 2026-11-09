import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheReciprocityOfReturns
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.ReturnBoundsAreLabelStatements
import GaloisForLFunctions.RHTower.JointAncestryPrimeSumOneLine
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The test of a heavy return

A fixed smooth bump `b`, equal to `1` on `[−log 8, −1/10]` and supported in
`(−log 8 − 1/20, −1/20)`, translated to `log y`, is the test `φ_y(u) = b(u − log y)` of the
reciprocity of returns. Its orbit polynomial is a smoothed sum over the prime powers in
`(y/9, y)`.

* **The test is admissible** (`contDiff_heavyTest`, `heavyTest_eq_zero_of_nonpos`,
  `heavyTest_support`): `C²`, compactly supported in `(0, log y]` for `y ≥ 9`, and its decay mass
  does not depend on `y` (`decayMass_heavyTest`).
* **The pole at `t = 0`** (`orbitPoly_heavyTest_zero_ge`). `P_{φ_y}(0) ≥ (9/50)√y` for large `y`:
  Chebyshev's `θ(x) ≥ 2x/5` on `(y/8, ye^{−1/10}]` against `θ(x) ≤ x log 4`.
* **A heavy return copies the pole** (`re_orbitPoly_heavyTest_ge`). At a `δ`-return of a
  `κ`-heavy subset of the primes `≤ y`,
  `Re P_{φ_y}(t) ≥ (1 − 2π²δ²) P_{φ_y}(0) − 2(κ(2y^{1/4} log y + 16√y) + 6 log y)`:
  the returned primes lose `2π²δ²` of their weight, the missing primes at most their weight, the
  prime powers `O(log y)` (`ψ − θ ≤ 2√y log y`).
-/

open Complex MeasureTheory Real Finset
open scoped Real ContDiff

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

open PrimeTorusTheory (dist01)

/-! ## The window bump -/

theorem log_eight_gt : 2 < Real.log 8 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [h]; linarith [Real.log_two_gt_d9]

theorem log_eight_lt : Real.log 8 < 21 / 10 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  rw [h]; linarith [Real.log_two_lt_d9]

/-- The window bump: `1` on `[−log 8, −1/10]`, supported in `(−log 8 − 1/20, −1/20)`. -/
def windowBump : ContDiffBump (-(Real.log 8 + 1 / 10) / 2 : ℝ) where
  rIn := (Real.log 8 - 1 / 10) / 2
  rOut := (Real.log 8 - 1 / 10) / 2 + 1 / 20
  rIn_pos := by linarith [log_eight_gt]
  rIn_lt_rOut := by linarith

theorem windowBump_eq_one {x : ℝ} (h1 : -Real.log 8 ≤ x) (h2 : x ≤ -(1 / 10)) :
    windowBump x = 1 := by
  apply windowBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  simp only [windowBump]
  constructor <;> linarith

theorem windowBump_support {x : ℝ} (h : windowBump x ≠ 0) :
    -Real.log 8 - 1 / 20 < x ∧ x < -(1 / 20) := by
  have hx : x ∈ Function.support windowBump := h
  rw [windowBump.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at hx
  simp only [windowBump] at hx
  constructor <;> linarith [hx.1, hx.2]

/-! ## The test -/

/-- The heavy-return test at length `y`: `u ↦ b(u − log y)`. -/
def heavyTest (y : ℝ) : ℝ → ℂ := fun u => ((windowBump (u - Real.log y) : ℝ) : ℂ)

theorem contDiff_windowBump (n : ℕ) : ContDiff ℝ n (windowBump : ℝ → ℝ) := windowBump.contDiff

theorem contDiff_heavyTest (y : ℝ) : ContDiff ℝ 2 (heavyTest y) := by
  unfold heavyTest
  exact Complex.ofRealCLM.contDiff.comp
    ((contDiff_windowBump 2).comp (contDiff_id.sub contDiff_const))

theorem heavyTest_support (y : ℝ) {u : ℝ} (h : heavyTest y u ≠ 0) :
    Real.log y - Real.log 8 - 1 / 20 < u ∧ u < Real.log y - 1 / 20 := by
  have h' : windowBump (u - Real.log y) ≠ 0 := by
    intro h0; apply h; simp [heavyTest, h0]
  have := windowBump_support h'
  constructor <;> linarith [this.1, this.2]

theorem log_nine_sub_log_eight : 1 / 20 < Real.log 9 - Real.log 8 := by
  rw [← Real.log_div (by norm_num) (by norm_num)]
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
  norm_num at h ⊢
  linarith

theorem heavyTest_eq_zero_of_nonpos {y : ℝ} (hy : 9 ≤ y) {u : ℝ} (hu : u ≤ 0) :
    heavyTest y u = 0 := by
  by_contra h
  have := (heavyTest_support y h).1
  have h9 : Real.log 9 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  linarith [log_nine_sub_log_eight]

theorem heavyTest_abs_le {y : ℝ} (hy : 9 ≤ y) {u : ℝ} (h : heavyTest y u ≠ 0) :
    |u| ≤ Real.log y := by
  have hs := heavyTest_support y h
  have h9 : Real.log 9 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hl9 : Real.log 8 + 1 / 20 < 2 * Real.log y := by linarith [log_nine_sub_log_eight, log_eight_gt]
  rw [abs_le]; constructor <;> linarith [hs.1, hs.2]

theorem hasCompactSupport_heavyTest {y : ℝ} (hy : 9 ≤ y) : HasCompactSupport (heavyTest y) :=
  Zeta23.hasCompactSupport_of_support_subset_abs fun u hu => heavyTest_abs_le hy hu

/-! ## The decay mass does not depend on `y` -/

theorem deriv_ofReal_comp_sub {f : ℝ → ℝ} (hf : Differentiable ℝ f) (c : ℝ) :
    deriv (fun u => ((f (u - c) : ℝ) : ℂ)) = fun u => ((deriv f (u - c) : ℝ) : ℂ) := by
  funext u
  exact (((hf (u - c)).hasDerivAt.comp_sub_const u c).ofReal_comp).deriv

theorem differentiable_deriv_windowBump : Differentiable ℝ (deriv (windowBump : ℝ → ℝ)) := by
  have hb : ContDiff ℝ ∞ (windowBump : ℝ → ℝ) := windowBump.contDiff
  simpa using (hb.iterate_deriv 1).differentiable (by simp)

theorem deriv_deriv_heavyTest (y : ℝ) :
    deriv (deriv (heavyTest y)) =
      fun u => ((deriv (deriv (windowBump : ℝ → ℝ)) (u - Real.log y) : ℝ) : ℂ) := by
  have h1 : deriv (heavyTest y) = fun u => ((deriv windowBump (u - Real.log y) : ℝ) : ℂ) :=
    deriv_ofReal_comp_sub ((contDiff_windowBump 1).differentiable (by norm_num)) _
  rw [h1]
  exact deriv_ofReal_comp_sub differentiable_deriv_windowBump _

/-- The decay mass of the test is the decay mass of the bump, for every `y`. -/
theorem decayMass_heavyTest (y : ℝ) : decayMass (heavyTest y) = decayMass (heavyTest 1) := by
  unfold decayMass
  rw [deriv_deriv_heavyTest, deriv_deriv_heavyTest]
  simp only [heavyTest, Real.log_one, sub_zero]
  congr 2
  · exact integral_sub_right_eq_self (fun u => ‖((windowBump u : ℝ) : ℂ)‖) (Real.log y)
  · exact integral_sub_right_eq_self
      (fun u => ‖((deriv (deriv (windowBump : ℝ → ℝ)) u : ℝ) : ℂ)‖) (Real.log y)

/-! ## The weights of the orbit polynomial -/

/-- The weight `w_y(n) = Λ(n) n^{−½} b(log n − log y)`. -/
def heavyWeight (y : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n * windowBump (Real.log n - Real.log y)

theorem heavyWeight_nonneg (y : ℝ) (n : ℕ) : 0 ≤ heavyWeight y n :=
  mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    windowBump.nonneg

theorem heavyWeight_eq_zero_of_lt {y : ℕ} (hy : 1 ≤ y) {n : ℕ} (hn : y < n) :
    heavyWeight (y : ℝ) n = 0 := by
  unfold heavyWeight
  have : windowBump (Real.log n - Real.log y) = 0 := by
    by_contra h
    have := (windowBump_support h).2
    have hlog : Real.log y < Real.log n :=
      Real.log_lt_log (by exact_mod_cast hy) (by exact_mod_cast hn)
    linarith
  rw [this, mul_zero]

theorem orbitPoly_heavyTest_eq {y : ℕ} (hy : 1 ≤ y) (t : ℝ) :
    orbitPoly (heavyTest y) t = ∑ n ∈ range (y + 1), ((heavyWeight y n : ℝ) : ℂ) *
      Complex.exp (-((t * Real.log n : ℝ) : ℂ) * I) := by
  unfold orbitPoly
  rw [tsum_eq_sum (s := range (y + 1))]
  · refine sum_congr rfl fun n _ => ?_
    simp only [heavyTest, heavyWeight]; push_cast; ring
  · intro n hn
    have hlt : y < n := by simpa using hn
    have h0 := heavyWeight_eq_zero_of_lt hy hlt
    simp only [heavyWeight] at h0
    have : (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        heavyTest (y : ℝ) (Real.log n)) = ((heavyWeight y n : ℝ) : ℂ) := by
      simp only [heavyTest, heavyWeight]; push_cast; ring
    rw [this, heavyWeight_eq_zero_of_lt hy hlt]; simp

theorem re_orbitPoly_heavyTest {y : ℕ} (hy : 1 ≤ y) (t : ℝ) :
    (orbitPoly (heavyTest y) t).re =
      ∑ n ∈ range (y + 1), heavyWeight y n * Real.cos (t * Real.log n) := by
  rw [orbitPoly_heavyTest_eq hy, Complex.re_sum]
  refine sum_congr rfl fun n _ => ?_
  have e : -((t * Real.log n : ℝ) : ℂ) * I = ((-(t * Real.log n) : ℝ) : ℂ) * I := by push_cast; ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-! ## The pole at `t = 0` -/

theorem heavyWeight_prime_ge {y : ℕ} {p : ℕ} (hp : p.Prime) (hpy : p ≤ y)
    (h1 : (y : ℝ) / 8 < p) (h2 : (p : ℝ) ≤ y * Real.exp (-(1 / 10))) :
    Real.log p / Real.sqrt y ≤ heavyWeight y p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hp.pos.trans_le hpy
  have hb : windowBump (Real.log p - Real.log y) = 1 := by
    apply windowBump_eq_one
    · have : Real.log ((y : ℝ) / 8) < Real.log p := Real.log_lt_log (by positivity) h1
      rw [Real.log_div hy0.ne' (by norm_num)] at this; linarith
    · have : Real.log p ≤ Real.log (y * Real.exp (-(1 / 10))) := Real.log_le_log hp0 h2
      rw [Real.log_mul hy0.ne' (Real.exp_pos _).ne', Real.log_exp] at this; linarith
  unfold heavyWeight
  rw [hb, mul_one, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  exact div_le_div_of_nonneg_left hlog (Real.sqrt_pos.mpr hp0)
    (Real.sqrt_le_sqrt (by exact_mod_cast hpy))

/-- The primes `p` with `y/8 < p ≤ ye^{−1/10}` carry `log`-mass at least `θ(ye^{−1/10}) − θ(y/8)`. -/
theorem theta_sub_le_sum_window (y : ℕ) :
    Chebyshev.theta (y * Real.exp (-(1 / 10))) - Chebyshev.theta ((y : ℝ) / 8) ≤
      ∑ p ∈ (Nat.primesLE ⌊(y : ℝ) * Real.exp (-(1 / 10))⌋₊).filter (fun p => (y : ℝ) / 8 < p),
        Real.log p := by
  set X := (y : ℝ) * Real.exp (-(1 / 10))
  rw [Chebyshev.theta_eq_sum_primesLE X, Chebyshev.theta_eq_sum_primesLE ((y : ℝ) / 8),
    ← sum_filter_add_sum_filter_not (Nat.primesLE ⌊X⌋₊) (fun p => (y : ℝ) / 8 < p)]
  have hsub : ((Nat.primesLE ⌊X⌋₊).filter (fun p => ¬ (y : ℝ) / 8 < p)) ⊆
      Nat.primesLE ⌊(y : ℝ) / 8⌋₊ := fun p hp => by
    rw [mem_filter] at hp
    rw [Nat.primesLE, Nat.mem_primesBelow] at hp ⊢
    refine ⟨?_, hp.1.2⟩
    have : (p : ℝ) ≤ (y : ℝ) / 8 := not_lt.mp hp.2
    have : p ≤ ⌊(y : ℝ) / 8⌋₊ := Nat.le_floor this
    omega
  have hle := sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
    Real.log_nonneg (by
      rw [Nat.primesLE, Nat.mem_primesBelow] at hp
      exact_mod_cast hp.2.one_lt.le)
  linarith

/-- **The pole at `t = 0`.** For large `y`, `P_{φ_y}(0) ≥ √y/4`. -/
theorem eventually_orbitPoly_heavyTest_zero_ge :
    ∀ᶠ y : ℕ in Filter.atTop, Real.sqrt y / 4 ≤ (orbitPoly (heavyTest y) 0).re := by
  have hlo := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).bound
    (show (0 : ℝ) < 1 / 100 by norm_num)
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      ‖Real.log x‖ ≤ 1 / 100 * ‖x ^ (1 / 2 : ℝ)‖ ∧ (10 : ℝ) ^ 4 ≤ x :=
    hlo.and (Filter.eventually_ge_atTop _)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev] with y ⟨hlog, hy⟩
  set Y : ℝ := (y : ℝ)
  have hY0 : 0 < Y := by linarith
  have hy1 : 1 ≤ y := by
    have : (1 : ℝ) ≤ Y := by linarith
    exact_mod_cast this
  have hsq : Y ^ (1 / 2 : ℝ) = Real.sqrt Y := (Real.sqrt_eq_rpow Y).symm
  have hlogY : Real.log Y ≤ Real.sqrt Y / 100 := by
    have h0 : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg h0, Real.norm_eq_abs, hsq,
      abs_of_nonneg (Real.sqrt_nonneg _)] at hlog
    linarith
  have hsqY : 100 ≤ Real.sqrt Y := by
    rw [show (100 : ℝ) = Real.sqrt (10 ^ 4) by
      rw [show ((10 : ℝ) ^ 4) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hy
  have hYsq : Real.sqrt Y * Real.sqrt Y = Y := Real.mul_self_sqrt hY0.le
  -- the window
  set X := Y * Real.exp (-(1 / 10))
  have he : (9 / 10 : ℝ) ≤ Real.exp (-(1 / 10)) := by
    have := Real.add_one_le_exp (-(1 / 10) : ℝ); linarith
  have he1 : Real.exp (-(1 / 10)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hX1 : 1 ≤ X := by nlinarith
  have hXY : X ≤ Y := by nlinarith
  have hθX := Chebyshev.theta_ge' hX1
  have hθ8 := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ Y / 8 by positivity)
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlogX : Real.log X ≤ Real.log Y := Real.log_le_log (by linarith) hXY
  have hlogX2 : Real.log (X + 2) ≤ Real.log 2 + Real.log Y := by
    rw [← Real.log_mul (by norm_num) hY0.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hsqX : Real.sqrt X ≤ Real.sqrt Y := Real.sqrt_le_sqrt hXY
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hmass : Y / 4 ≤ Chebyshev.theta X - Chebyshev.theta (Y / 8) := by
    have h1 : 2 * Real.sqrt X * Real.log X ≤ 2 * Real.sqrt Y * (Real.sqrt Y / 100) := by
      have := mul_le_mul hsqX (hlogX.trans hlogY) hlogX0 (Real.sqrt_nonneg _)
      linarith
    nlinarith
  have hwin := theta_sub_le_sum_window y
  -- the weights on the window
  have hS : ∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p => Y / 8 < p), Real.log p / Real.sqrt Y ≤
      ∑ n ∈ range (y + 1), heavyWeight y n := by
    have hsub : (Nat.primesLE ⌊X⌋₊).filter (fun p => Y / 8 < p) ⊆ range (y + 1) := fun p hp => by
      rw [mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
      have : p ≤ ⌊X⌋₊ := by omega
      have : (p : ℝ) ≤ X := (Nat.le_floor_iff (by linarith)).mp this |>.trans le_rfl
      have : p ≤ y := by exact_mod_cast this.trans hXY
      simp; omega
    refine (sum_le_sum fun p hp => ?_).trans
      (sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => heavyWeight_nonneg _ _)
    rw [mem_filter, Nat.primesLE, Nat.mem_primesBelow] at hp
    have hpX : (p : ℝ) ≤ X := Nat.le_floor_iff (by linarith) |>.mp (by omega)
    exact heavyWeight_prime_ge hp.1.2 (by exact_mod_cast hpX.trans hXY) hp.2 hpX
  rw [re_orbitPoly_heavyTest hy1 0]
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [← sum_div] at hS
  calc Real.sqrt Y / 4 = (Y / 4) / Real.sqrt Y := by
        field_simp; nlinarith [hYsq]
    _ ≤ (∑ p ∈ (Nat.primesLE ⌊X⌋₊).filter (fun p => Y / 8 < p), Real.log p) / Real.sqrt Y :=
        div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    _ ≤ _ := hS

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
