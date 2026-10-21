import GaloisForLFunctions.SquareRootThreshold.ZetaHidingRequiresLoudTwins
import GaloisForLFunctions.SquareRootThreshold.GridHiddenChainsHaveAnExplicitContinuumLag

/-!
# Fejér power lag windows

The weight `sin^{2k}(πu/V)` vanishes to order `2k` at both ends of `[0, V]`. Its kernel
`K_k(z) = ∫_0^V sin^{2k}(πu/V) e^{zu} du` (`fejerPowWin`; `K_0 = E_V`, `K_1 = F_V`) satisfies the
**recursion** (`fejerPowWin_succ`)
`(z² + ((2k+2)π/V)²) K_{k+1}(z) = (2k+2)(2k+1)(π/V)² K_k(z)`,
obtained from one application of the fundamental theorem of calculus to `e^{zu}(f' − z f)`,
`f = sin^{2k+2}(πu/V)`, since `f'' = (2k+2)(2k+1)(π/V)² sin^{2k} − ((2k+2)π/V)² sin^{2k+2}`. Hence
`K_k(z) = (2k)! (π/V)^{2k} E_V(z)/∏_{j=1}^k (z² + (2πj/V)²)`, and:

* **decay of order `2k + 1`** (`norm_fejerPowWin_le_decay`): once `V|z| ≥ 4πk`,
  `|K_k(z)| ≤ (4/3)^k (2k)! (π/V)^{2k} (e^{Re z·V} + 1)/|z|^{2k+1}`;
* **the real kernel** (`norm_fejerPowWin_ofReal_ge`): for `x > 0`,
  `K_k(x) ≥ (2k)! (π/V)^{2k} (e^{xV} − 1)/(x (x² + (2πk/V)²)^k)`;
* **the archimedean kernel** (`norm_fejerPowWin_neg_le`): `|K_k(−σ)| ≤ 2(2k)!(π/V)^{2k}/σ^{2k+1}`;
* **the trivial bound** `|K_k(w)| ≤ V max(1, e^{Re w·V})` (`norm_fejerPowWin_le_max`).

**Record-potential law of order `k`** (`norm_evenCoeff_mul_fejerPowWin_le`). If the difference tests
are Weil nonnegative on `[0, V]`, then
`G_k(s) = ∫_0^V sin^{2k}(πu/V) e^{−su}(φ(0) − φ(u)) du = φ(0)K_k(−s) − Σ_z D(z)K_k(z − s)`
(`integral_fejerPowWindow_eq`) satisfies `|G_k(σ + it)| ≤ G_k(σ)`, and the term of any exponent is
bounded by the potential of all others. Against the uniform window the competitors at distance `d`
are damped by `d^{−(2k+1)}` instead of `d^{−1}`, at the price of the factor
`(4/3)^k (2k)! (π/V)^{2k}`, which is that of the record itself up to `(κ² + 4π²k²)^k/κ^{2k}`
when it is evaluated at depth `κ/V`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The kernel `K_k(z) = ∫_0^V sin^{2k}(πu/V) e^{zu} du` -/

/-- The Fejér power kernel `K_k(z) = ∫_0^V sin^{2k}(πu/V) e^{zu} du`; `K_0 = E_V`, and `K_1` is the
Fejér kernel `F_V`. -/
def fejerPowWin (k : ℕ) (V : ℝ) (z : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..V, ((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) * cexp (z * u)

theorem fejerPowWin_zero (V : ℝ) (z : ℂ) : fejerPowWin 0 V z = lapWin V z := by
  simp [fejerPowWin, lapWin]

/-- **Recursion.** `(z² + ((2k+2)π/V)²) K_{k+1}(z) = (2k+2)(2k+1)(π/V)² K_k(z)`: the function
`e^{zu}(f' − z f)`, `f = sin^{2k+2}(πu/V)`, vanishes at `0` and `V` and has derivative
`e^{zu}(f'' − z² f)`, with `f'' = (2k+2)(2k+1)(π/V)² sin^{2k} − ((2k+2)π/V)² sin^{2k+2}`. -/
theorem fejerPowWin_succ {V : ℝ} (hV : 0 < V) (k : ℕ) (z : ℂ) :
    (z ^ 2 + (((2 * k + 2) * π / V : ℝ) : ℂ) ^ 2) * fejerPowWin (k + 1) V z =
      (((2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 : ℝ) : ℂ) * fejerPowWin k V z := by
  set a : ℝ := π / V with ha
  have hSa : ∀ u : ℝ, π * u / V = a * u := fun u => by rw [ha]; ring
  set m : ℝ := 2 * k + 2 with hm
  set f : ℝ → ℂ := fun u => ((Real.sin (a * u) ^ (2 * k + 2) : ℝ) : ℂ) with hf
  set f' : ℝ → ℂ := fun u => ((m * a * (Real.sin (a * u) ^ (2 * k + 1) * Real.cos (a * u)) : ℝ) : ℂ)
    with hf'
  set f'' : ℝ → ℂ := fun u => ((m * (m - 1) * a ^ 2 * Real.sin (a * u) ^ (2 * k) -
    (m * a) ^ 2 * Real.sin (a * u) ^ (2 * k + 2) : ℝ) : ℂ) with hf''
  have hSd : ∀ u : ℝ, HasDerivAt (fun x => Real.sin (a * x)) (Real.cos (a * u) * a) u := fun u => by
    simpa using ((hasDerivAt_id u).const_mul a).sin
  have hCd : ∀ u : ℝ, HasDerivAt (fun x => Real.cos (a * x)) (-Real.sin (a * u) * a) u :=
    fun u => by simpa using ((hasDerivAt_id u).const_mul a).cos
  have hfd : ∀ u, HasDerivAt f (f' u) u := fun u => by
    have h := ((hSd u).fun_pow (2 * k + 2)).ofReal_comp
    refine h.congr_deriv ?_
    simp only [hf', hm]; push_cast; ring
  have hf'd : ∀ u, HasDerivAt f' (f'' u) u := fun u => by
    have h := ((((hSd u).fun_pow (2 * k + 1)).fun_mul (hCd u)).const_mul (m * a)).ofReal_comp
    refine h.congr_deriv ?_
    simp only [hf'']
    congr 1
    have hpyth : Real.cos (a * u) ^ 2 = 1 - Real.sin (a * u) ^ 2 := Real.cos_sq' _
    rw [Nat.add_sub_cancel, hm]
    push_cast
    linear_combination ((2 * (k : ℝ) + 2) * a * (2 * k + 1) * a * Real.sin (a * u) ^ (2 * k)) * hpyth
  have hEd : ∀ u : ℝ, HasDerivAt (fun x : ℝ => cexp (z * x)) (cexp (z * u) * z) u := fun u => by
    simpa using ((hasDerivAt_id u).ofReal_comp.const_mul z).cexp
  -- `g = e^{zu}(f' − z f)` has derivative `e^{zu}(f'' − z² f)`
  have hgd : ∀ u : ℝ, HasDerivAt (fun x : ℝ => cexp (z * x) * (f' x - z * f x))
      (cexp (z * u) * (f'' u - z ^ 2 * f u)) u := fun u => by
    have h := (hEd u).fun_mul ((hf'd u).fun_sub ((hfd u).const_mul z))
    refine h.congr_deriv ?_
    ring
  have hcont : Continuous fun u : ℝ => cexp (z * u) * (f'' u - z ^ 2 * f u) := by
    simp only [hf'', hf]; fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := V)
    (fun u _ => hgd u) (hcont.intervalIntegrable _ _)
  have hsinV : Real.sin (a * V) = 0 := by rw [ha, div_mul_cancel₀ _ hV.ne', Real.sin_pi]
  have hg0 : cexp (z * V) * (f' V - z * f V) - cexp (z * (0 : ℝ)) * (f' 0 - z * f 0) = 0 := by
    have hc : Complex.sin ((a : ℂ) * V) = 0 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, hsinV, Complex.ofReal_zero]
    simp [hf, hf', hc]
  rw [hg0] at hFTC
  -- expand the integral
  have hK : ∀ j : ℕ, fejerPowWin j V z =
      ∫ u in (0 : ℝ)..V, ((Real.sin (a * u) ^ (2 * j) : ℝ) : ℂ) * cexp (z * u) := fun j => by
    simp only [fejerPowWin, hSa]
  have hsplit : ∀ u : ℝ, cexp (z * u) * (f'' u - z ^ 2 * f u) =
      ((m * (m - 1) * a ^ 2 : ℝ) : ℂ) * (((Real.sin (a * u) ^ (2 * k) : ℝ) : ℂ) * cexp (z * u)) -
        (((m * a) ^ 2 : ℝ) + z ^ 2) * (((Real.sin (a * u) ^ (2 * (k + 1)) : ℝ) : ℂ) *
          cexp (z * u)) := fun u => by
    simp only [hf'', hf, show 2 * (k + 1) = 2 * k + 2 by ring]; push_cast; ring
  simp_rw [hsplit] at hFTC
  have hi1 : IntervalIntegrable (fun u : ℝ => ((m * (m - 1) * a ^ 2 : ℝ) : ℂ) *
      (((Real.sin (a * u) ^ (2 * k) : ℝ) : ℂ) * cexp (z * u))) volume 0 V :=
    (by fun_prop : Continuous fun u : ℝ => ((m * (m - 1) * a ^ 2 : ℝ) : ℂ) *
      (((Real.sin (a * u) ^ (2 * k) : ℝ) : ℂ) * cexp (z * u))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun u : ℝ => (((m * a) ^ 2 : ℝ) + z ^ 2) *
      (((Real.sin (a * u) ^ (2 * (k + 1)) : ℝ) : ℂ) * cexp (z * u))) volume 0 V :=
    (by fun_prop : Continuous fun u : ℝ => (((m * a) ^ 2 : ℝ) + z ^ 2) *
      (((Real.sin (a * u) ^ (2 * (k + 1)) : ℝ) : ℂ) * cexp (z * u))).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← hK, ← hK] at hFTC
  have e3 : ((2 * k + 2) * π / V : ℝ) = m * a := by rw [hm, ha]; ring
  have e4 : ((2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 : ℝ) = m * (m - 1) * a ^ 2 := by
    rw [hm, ha]; ring
  rw [e3, e4]
  push_cast at hFTC ⊢
  linear_combination -hFTC

theorem abs_sin_pow_le_one (x : ℝ) (k : ℕ) : |Real.sin x ^ (2 * k)| ≤ 1 := by
  rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one x)

theorem sin_pow_nonneg (x : ℝ) (k : ℕ) : 0 ≤ Real.sin x ^ (2 * k) := by
  rw [pow_mul]; positivity

/-- `|K_k(w)| ≤ ∫_0^V e^{Re w · u} du`. -/
theorem norm_fejerPowWin_le {V : ℝ} (hV : 0 ≤ V) (k : ℕ) (w : ℂ) :
    ‖fejerPowWin k V w‖ ≤ ∫ u in (0 : ℝ)..V, Real.exp (w.re * u) := by
  refine (intervalIntegral.norm_integral_le_integral_norm hV).trans ?_
  refine intervalIntegral.integral_mono_on hV ((by fun_prop : Continuous fun u : ℝ =>
    ‖((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) * cexp (w * u)‖).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun u : ℝ => Real.exp (w.re * u)).intervalIntegrable _ _)
    fun u _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have : (w * (u : ℂ)).re = w.re * u := by simp
  rw [this]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (abs_sin_pow_le_one _ k)

/-- `|K_k(w)| ≤ V max(1, e^{Re w·V})`. -/
theorem norm_fejerPowWin_le_max {V : ℝ} (hV : 0 ≤ V) (k : ℕ) (w : ℂ) :
    ‖fejerPowWin k V w‖ ≤ V * max 1 (Real.exp (w.re * V)) := by
  refine (norm_fejerPowWin_le hV k w).trans ?_
  have h : ∫ u in (0 : ℝ)..V, Real.exp (w.re * u) ≤ ∫ _u in (0 : ℝ)..V, max 1 (Real.exp (w.re * V)) :=
    intervalIntegral.integral_mono_on hV
      ((by fun_prop : Continuous fun u : ℝ => Real.exp (w.re * u)).intervalIntegrable _ _)
      intervalIntegrable_const fun u hu => by
        rcases le_or_gt 0 w.re with h | h
        · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 h)).trans (le_max_right _ _)
        · exact (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg h.le hu.1)).trans
            (le_max_left _ _)
  simpa using h

/-- `|K_k(w)| ≤ V e^{|Re w| V}`. -/
theorem norm_fejerPowWin_le_const {V : ℝ} (hV : 0 ≤ V) (k : ℕ) (w : ℂ) :
    ‖fejerPowWin k V w‖ ≤ V * Real.exp (|w.re| * V) := by
  refine (norm_fejerPowWin_le_max hV k w).trans (mul_le_mul_of_nonneg_left (max_le ?_ ?_) hV)
  · exact Real.one_le_exp (by positivity)
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self _) hV)

/-- The step `|z² + b²| ≥ ¾|z|²` for `2b ≤ |z|`. -/
theorem norm_sq_add_sq_ge {z : ℂ} {b : ℝ} (hb : 0 ≤ b) (hzb : 2 * b ≤ ‖z‖) :
    3 / 4 * ‖z‖ ^ 2 ≤ ‖z ^ 2 + ((b : ℝ) : ℂ) ^ 2‖ := by
  have h3 := norm_sub_norm_le (z ^ 2) (-(((b : ℝ) : ℂ) ^ 2))
  rw [sub_neg_eq_add, norm_neg, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hb] at h3
  nlinarith

/-- **Decay.** `|K_k(z)| ≤ (4/3)^k (2k)! (π/V)^{2k} |E_V(z)|/|z|^{2k}` once `V|z| ≥ 4πk`. -/
theorem norm_fejerPowWin_le_pow {V : ℝ} (hV : 0 < V) (k : ℕ) {z : ℂ} (hz : 4 * π * k ≤ V * ‖z‖) :
    ‖fejerPowWin k V z‖ ≤
      (4 / 3) ^ k * (2 * k).factorial * (π / V) ^ (2 * k) * ‖lapWin V z‖ / ‖z‖ ^ (2 * k) := by
  induction k with
  | zero => simp [fejerPowWin_zero]
  | succ k ih =>
    have hk : 4 * π * k ≤ V * ‖z‖ := le_trans (by push_cast; nlinarith [Real.pi_pos]) hz
    have ih := ih hk
    set b : ℝ := (2 * k + 2) * π / V with hbdef
    have hb0 : 0 ≤ b := by rw [hbdef]; positivity
    have hzb : 2 * b ≤ ‖z‖ := by
      rw [hbdef, show 2 * ((2 * k + 2) * π / V) = 4 * π * ((k + 1 : ℕ) : ℝ) / V by push_cast; ring,
        div_le_iff₀ hV]
      linarith [hz]
    have hz0 : 0 < ‖z‖ := by
      have : 0 < 2 * b := by rw [hbdef]; positivity
      linarith
    have hq := norm_sq_add_sq_ge hb0 hzb
    have hrec := congrArg norm (fejerPowWin_succ hV k z)
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      at hrec
    have hq0 : 0 < ‖z ^ 2 + ((b : ℝ) : ℂ) ^ 2‖ := lt_of_lt_of_le (by positivity) hq
    have hK : ‖fejerPowWin (k + 1) V z‖ =
        (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 * ‖fejerPowWin k V z‖ /
          ‖z ^ 2 + ((b : ℝ) : ℂ) ^ 2‖ := by
      rw [eq_div_iff hq0.ne']; linear_combination hrec
    rw [hK, div_le_iff₀ hq0]
    have hfac : ((2 * (k + 1)).factorial : ℝ) = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    set X := (4 / 3) ^ k * (2 * k).factorial * (π / V) ^ (2 * k) * ‖lapWin V z‖ / ‖z‖ ^ (2 * k)
      with hX
    have hX0 : 0 ≤ X := by rw [hX]; positivity
    have hgoal : (4 / 3) ^ (k + 1) * ((2 * (k + 1)).factorial : ℝ) * (π / V) ^ (2 * (k + 1)) *
        ‖lapWin V z‖ / ‖z‖ ^ (2 * (k + 1)) =
        4 / 3 * ((2 * k + 2) * (2 * k + 1) * (π / V) ^ 2) * X / ‖z‖ ^ 2 := by
      rw [hX, hfac, show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_add, pow_succ]; ring
    rw [hgoal]
    have hc0 : 0 ≤ (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 := by positivity
    calc (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 * ‖fejerPowWin k V z‖
        ≤ (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 * X := mul_le_mul_of_nonneg_left ih hc0
      _ = 4 / 3 * ((2 * k + 2) * (2 * k + 1) * (π / V) ^ 2) * X / ‖z‖ ^ 2 *
            (3 / 4 * ‖z‖ ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)

/-- **Decay, explicit.** `|K_k(z)| ≤ (4/3)^k (2k)! (π/V)^{2k} (e^{Re z·V} + 1)/|z|^{2k+1}` once
`V|z| ≥ 4πk` and `z ≠ 0`. -/
theorem norm_fejerPowWin_le_decay {V : ℝ} (hV : 0 < V) (k : ℕ) {z : ℂ} (hz0 : z ≠ 0)
    (hz : 4 * π * k ≤ V * ‖z‖) :
    ‖fejerPowWin k V z‖ ≤ (4 / 3) ^ k * (2 * k).factorial * (π / V) ^ (2 * k) *
      (Real.exp (z.re * V) + 1) / ‖z‖ ^ (2 * k + 1) := by
  refine (norm_fejerPowWin_le_pow hV k hz).trans ?_
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have h := norm_lapWin_le_div V hz0
  calc (4 / 3) ^ k * ((2 * k).factorial : ℝ) * (π / V) ^ (2 * k) * ‖lapWin V z‖ / ‖z‖ ^ (2 * k)
      ≤ (4 / 3) ^ k * ((2 * k).factorial : ℝ) * (π / V) ^ (2 * k) *
          ((Real.exp (z.re * V) + 1) / ‖z‖) / ‖z‖ ^ (2 * k) := by gcongr
    _ = _ := by rw [pow_succ]; field_simp

/-- **The real kernel.** For `x > 0`,
`|K_k(x)| ≥ (2k)! (π/V)^{2k} (e^{xV} − 1)/(x (x² + (2πk/V)²)^k)`. -/
theorem norm_fejerPowWin_ofReal_ge {V : ℝ} (hV : 0 < V) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    (2 * k).factorial * (π / V) ^ (2 * k) * ((Real.exp (x * V) - 1) / x) /
        (x ^ 2 + (2 * π * k / V) ^ 2) ^ k ≤ ‖fejerPowWin k V x‖ := by
  induction k with
  | zero => simp [fejerPowWin_zero, norm_lapWin_ofReal_pos hV.le hx]
  | succ k ih =>
    set b : ℝ := (2 * k + 2) * π / V with hbdef
    have hrec := congrArg norm (fejerPowWin_succ hV k (x : ℂ))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      at hrec
    have hq : ‖(x : ℂ) ^ 2 + ((b : ℝ) : ℂ) ^ 2‖ = x ^ 2 + b ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hq] at hrec
    have hq0 : 0 < x ^ 2 + b ^ 2 := by positivity
    have hK : ‖fejerPowWin (k + 1) V x‖ =
        (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 * ‖fejerPowWin k V x‖ / (x ^ 2 + b ^ 2) := by
      rw [eq_div_iff hq0.ne']; linear_combination hrec
    rw [hK]
    have hfac : ((2 * (k + 1)).factorial : ℝ) = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hb : (2 * π * ((k + 1 : ℕ) : ℝ) / V) = b := by rw [hbdef]; push_cast; ring
    rw [hb, hfac]
    have hmono : (x ^ 2 + (2 * π * k / V) ^ 2) ^ k ≤ (x ^ 2 + b ^ 2) ^ k := by
      have h1 : 2 * π * k / V ≤ b := by
        rw [hbdef, div_le_div_iff_of_pos_right hV]; nlinarith [Real.pi_pos]
      have h2 := pow_le_pow_left₀ (by positivity) h1 2
      exact pow_le_pow_left₀ (by positivity) (by linarith) k
    have hE : 0 ≤ (Real.exp (x * V) - 1) / x :=
      div_nonneg (by linarith [Real.one_le_exp (mul_nonneg hx.le hV.le)]) hx.le
    have hA : 0 < (x ^ 2 + (2 * π * k / V) ^ 2) ^ k := by positivity
    have ih' : (2 * k).factorial * (π / V) ^ (2 * k) * ((Real.exp (x * V) - 1) / x) /
        (x ^ 2 + b ^ 2) ^ k ≤ ‖fejerPowWin k V x‖ :=
      le_trans (div_le_div_of_nonneg_left (by positivity) hA hmono) ih
    rw [le_div_iff₀ hq0]
    calc (2 * k + 2) * (2 * k + 1) * (2 * k).factorial * (π / V) ^ (2 * (k + 1)) *
          ((Real.exp (x * V) - 1) / x) / (x ^ 2 + b ^ 2) ^ (k + 1) * (x ^ 2 + b ^ 2)
        = (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 * ((2 * k).factorial * (π / V) ^ (2 * k) *
            ((Real.exp (x * V) - 1) / x) / (x ^ 2 + b ^ 2) ^ k) := by
          rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, pow_succ]
          field_simp
          ring
      _ ≤ (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 * ‖fejerPowWin k V x‖ :=
          mul_le_mul_of_nonneg_left ih' (by positivity)

/-- **The archimedean kernel.** For `σ > 0`, `|K_k(−σ)| ≤ 2 (2k)! (π/V)^{2k}/σ^{2k+1}`. -/
theorem norm_fejerPowWin_neg_le {V : ℝ} (hV : 0 < V) (k : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ‖fejerPowWin k V (-(σ : ℂ))‖ ≤ 2 * (2 * k).factorial * (π / V) ^ (2 * k) / σ ^ (2 * k + 1) := by
  induction k with
  | zero =>
    have := norm_lapWin_neg_le hV.le (s := (σ : ℂ)) (by simpa using hσ)
    simpa [fejerPowWin_zero] using this
  | succ k ih =>
    set b : ℝ := (2 * k + 2) * π / V with hbdef
    have hrec := congrArg norm (fejerPowWin_succ hV k (-(σ : ℂ)))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      at hrec
    have hq : ‖(-(σ : ℂ)) ^ 2 + ((b : ℝ) : ℂ) ^ 2‖ = σ ^ 2 + b ^ 2 := by
      rw [neg_sq, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hq] at hrec
    have hq0 : 0 < σ ^ 2 + b ^ 2 := by positivity
    have hK : ‖fejerPowWin (k + 1) V (-(σ : ℂ))‖ =
        (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 * ‖fejerPowWin k V (-(σ : ℂ))‖ /
          (σ ^ 2 + b ^ 2) := by
      rw [eq_div_iff hq0.ne']; linear_combination hrec
    rw [hK, div_le_iff₀ hq0]
    have hfac : ((2 * (k + 1)).factorial : ℝ) = (2 * k + 2) * (2 * k + 1) * (2 * k).factorial := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [hfac]
    have hc0 : 0 ≤ (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 := by positivity
    calc (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 * ‖fejerPowWin k V (-(σ : ℂ))‖
        ≤ (2 * k + 2) * (2 * k + 1) * (π / V) ^ 2 *
            (2 * (2 * k).factorial * (π / V) ^ (2 * k) / σ ^ (2 * k + 1)) :=
          mul_le_mul_of_nonneg_left ih hc0
      _ = 2 * ((2 * k + 2) * (2 * k + 1) * (2 * k).factorial) * (π / V) ^ (2 * (k + 1)) /
            σ ^ (2 * (k + 1) + 1) * σ ^ 2 := by
          rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by ring, show 2 * (k + 1) = 2 * k + 2 by ring,
            pow_add, pow_add]
          field_simp
          ring
      _ ≤ 2 * ((2 * k + 2) * (2 * k + 1) * (2 * k).factorial) * (π / V) ^ (2 * (k + 1)) /
            σ ^ (2 * (k + 1) + 1) * (σ ^ 2 + b ^ 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg b]) (by positivity)

/-! ### The Fejér power window of the lag function -/

/-- `∫_0^V sin^{2k}(πu/V) e^{−su} φ(u) du = Σ_z D(z) K_k(z − s)`. -/
theorem integral_fejerPow_lag_eq (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V) (k : ℕ)
    (s : ℂ) :
    ∫ u in (0 : ℝ)..V, ((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) * cexp (-s * u) *
        ((2 * (lagStructure Z b u).re : ℝ) : ℂ) =
      ∑' z : ℂ, evenCoeff Z b z * fejerPowWin k V (z - s) := by
  classical
  set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
  haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
  set ω : ℝ → ℂ := fun u => ((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) with hω
  have hD : Summable fun t : ι => ‖evenCoeff Z b t‖ :=
    (summable_norm_evenCoeff Z hZ hb hbs).subtype ι
  have hrep : ∀ u : ℝ, ω u * cexp (-s * u) * ((2 * (lagStructure Z b u).re : ℝ) : ℂ) =
      ∑' t : ι, evenCoeff Z b t * (ω u * cexp (((t : ℂ) - s) * u)) := by
    intro u
    have hsub : Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * u)) ⊆ ι :=
      fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * u) = 0 by rw [h0, zero_mul])
    rw [(two_re_lagStructure_eq Z hZ hb hbs u).2, ← tsum_subtype_eq_of_support_subset hsub,
      ← tsum_mul_left]
    refine tsum_congr fun t => ?_
    have : cexp (-s * u) * cexp ((t : ℂ) * u) = cexp (((t : ℂ) - s) * u) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [← this]; ring
  have hω1 : ∀ u, ‖ω u‖ ≤ 1 := fun u => by
    rw [hω, Complex.norm_real, Real.norm_eq_abs]; exact abs_sin_pow_le_one _ k
  have hpt : ∀ (t : ι) (u : ℝ), u ∈ Icc (0 : ℝ) V →
      ‖evenCoeff Z b t * (ω u * cexp (((t : ℂ) - s) * u))‖ ≤ ‖evenCoeff Z b t‖ *
        Real.exp ((1 / 2 + |s.re|) * V) := by
    intro t u hu
    rw [norm_mul, norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (mul_le_of_le_one_left (Real.exp_pos _).le (hω1 u)).trans (Real.exp_le_exp.mpr ?_)
    have hre := abs_re_le_of_evenCoeff_ne_zero t.2
    have e : ((((t : ℂ) - s) * (u : ℂ))).re = ((t : ℂ).re - s.re) * u := by simp
    rw [e]
    have h1 : (t : ℂ).re - s.re ≤ 1 / 2 + |s.re| := by
      linarith [(abs_le.mp hre).2, neg_abs_le s.re]
    calc ((t : ℂ).re - s.re) * u ≤ (1 / 2 + |s.re|) * u :=
          mul_le_mul_of_nonneg_right h1 hu.1
      _ ≤ (1 / 2 + |s.re|) * V :=
          mul_le_mul_of_nonneg_left hu.2 (by positivity)
  have hωc : Continuous ω := by rw [hω]; fun_prop
  have hF : ∀ t : ι, Integrable (fun u : ℝ => evenCoeff Z b t * (ω u * cexp (((t : ℂ) - s) * u)))
      (volume.restrict (Ioc 0 V)) := fun t =>
    ((continuous_const.mul (hωc.mul (by fun_prop))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hsum : Summable fun t : ι =>
      ∫ u in Ioc 0 V, ‖evenCoeff Z b t * (ω u * cexp (((t : ℂ) - s) * u))‖ := by
    refine Summable.of_nonneg_of_le (fun t => setIntegral_nonneg measurableSet_Ioc
      fun _ _ => norm_nonneg _) (fun t => ?_) (hD.mul_right (V * Real.exp ((1 / 2 + |s.re|) * V)))
    rw [← intervalIntegral.integral_of_le hV]
    calc ∫ u in (0 : ℝ)..V, ‖evenCoeff Z b t * (ω u * cexp (((t : ℂ) - s) * u))‖
        ≤ ∫ _u in (0 : ℝ)..V, ‖evenCoeff Z b t‖ * Real.exp ((1 / 2 + |s.re|) * V) :=
          intervalIntegral.integral_mono_on hV ((continuous_const.mul (hωc.mul
            (by fun_prop))).norm.intervalIntegrable _ _) intervalIntegrable_const (hpt t)
      _ = ‖evenCoeff Z b t‖ * (V * Real.exp ((1 / 2 + |s.re|) * V)) := by simp
  have hsupp : Function.support (fun z : ℂ => evenCoeff Z b z * fejerPowWin k V (z - s)) ⊆ ι :=
    fun z hz h0 => hz (show evenCoeff Z b z * fejerPowWin k V (z - s) = 0 by rw [h0, zero_mul])
  show ∫ u in (0 : ℝ)..V, ω u * cexp (-s * u) * ((2 * (lagStructure Z b u).re : ℝ) : ℂ) = _
  simp_rw [hrep]
  rw [intervalIntegral.integral_of_le hV, ← integral_tsum_of_summable_integral_norm hF hsum,
    ← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun t => ?_
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hV, fejerPowWin]

/-- **The Fejér power window, termwise.**
`∫_0^V sin^{2k}(πu/V) e^{−su}(φ(0) − φ(u)) du = φ(0) K_k(−s) − Σ_z D(z) K_k(z − s)`. -/
theorem integral_fejerPowWindow_eq (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V) (k : ℕ)
    (s : ℂ) :
    ∫ u in (0 : ℝ)..V, cexp (-s * u) * ((Real.sin (π * u / V) ^ (2 * k) *
        (2 * (lagStructure Z b 0).re - 2 * (lagStructure Z b u).re) : ℝ) : ℂ) =
      (2 * (lagStructure Z b 0).re : ℝ) * fejerPowWin k V (-s) -
        ∑' z : ℂ, evenCoeff Z b z * fejerPowWin k V (z - s) := by
  set M : ℝ := 2 * (lagStructure Z b 0).re with hM
  have hφc : Continuous fun u : ℝ => 2 * (lagStructure Z b u).re :=
    continuous_const.mul (Complex.continuous_re.comp (continuous_lagStructure Z hZ hb hbs))
  have e : ∀ u : ℝ, cexp (-s * u) * ((Real.sin (π * u / V) ^ (2 * k) *
      (M - 2 * (lagStructure Z b u).re) : ℝ) : ℂ) =
      (M : ℂ) * (((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) * cexp (-s * u)) -
        ((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) * cexp (-s * u) *
          ((2 * (lagStructure Z b u).re : ℝ) : ℂ) := fun u => by push_cast; ring
  rw [intervalIntegral.integral_congr fun u _ => e u]
  have hi1 : IntervalIntegrable (fun u : ℝ => (M : ℂ) *
      (((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) * cexp (-s * u))) volume 0 V :=
    (by fun_prop : Continuous fun u : ℝ => (M : ℂ) *
      (((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) * cexp (-s * u))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun u : ℝ => ((Real.sin (π * u / V) ^ (2 * k) : ℝ) : ℂ) *
      cexp (-s * u) * ((2 * (lagStructure Z b u).re : ℝ) : ℂ)) volume 0 V :=
    (Continuous.mul (by fun_prop) (Complex.continuous_ofReal.comp hφc)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    integral_fejerPow_lag_eq Z hZ hb hbs hV k s, fejerPowWin]

/-- **Fejér power record-potential law.** If the difference tests are Weil nonnegative on
`[0, V]`, then for every exponent `z₀` and `s = σ + it`, with `M = 2 Re S(0)`:
`|D(z₀) K_k(z₀ − s)| ≤ |M|(|K_k(−σ)| + |K_k(−s)|) + Σ_z |D(z)||K_k(z − σ)|
  + Σ_{z ≠ z₀} |D(z)||K_k(z − s)|`. -/
theorem norm_evenCoeff_mul_fejerPowWin_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V) (k : ℕ)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    (z₀ : ℂ) (σ t : ℝ) :
    ‖evenCoeff Z b z₀ * fejerPowWin k V (z₀ - (σ + t * I))‖ ≤
      |2 * (lagStructure Z b 0).re| *
          (‖fejerPowWin k V (-σ)‖ + ‖fejerPowWin k V (-(σ + t * I))‖) +
      ∑' z : ℂ, ‖evenCoeff Z b z‖ * ‖fejerPowWin k V (z - σ)‖ +
      ∑' z : ℂ, (if z = z₀ then 0 else
        ‖evenCoeff Z b z‖ * ‖fejerPowWin k V (z - (σ + t * I))‖) := by
  classical
  set D := evenCoeff Z b with hDdef
  set M : ℝ := 2 * (lagStructure Z b 0).re with hM
  have hg : ∀ u ∈ Icc (0 : ℝ) V,
      0 ≤ Real.sin (π * u / V) ^ (2 * k) * (M - 2 * (lagStructure Z b u).re) := fun u hu => by
    have := hm u hu
    rw [re_W_lag_eq Z hZ hb hbs u] at this
    exact mul_nonneg (sin_pow_nonneg _ k) this
  have hG := integral_fejerPowWindow_eq Z hZ hb hbs hV k
  have hsumL : ∀ s : ℂ, Summable fun z : ℂ => ‖D z‖ * ‖fejerPowWin k V (z - s)‖ := fun s =>
    summable_norm_evenCoeff_mul Z hZ hb hbs (C := V * Real.exp ((1 / 2 + |s.re|) * V))
      (fun _ => norm_nonneg _) fun z hz => (norm_fejerPowWin_le_const hV k _).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by
          rw [Complex.sub_re]
          exact (abs_sub _ _).trans (by linarith [abs_re_le_of_evenCoeff_ne_zero hz]))
          hV)) hV)
  have hsumC : ∀ s : ℂ, Summable fun z : ℂ => D z * fejerPowWin k V (z - s) := fun s =>
    (hsumL s).of_norm_bounded fun z => (norm_mul _ _).le
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hpos := norm_integral_cexp_mul_le hV hg s
  rw [hsre] at hpos
  have hGs := hG s
  have hGσ := hG σ
  have hsplit := (hsumC s).tsum_eq_add_tsum_ite z₀
  have hrest : ‖∑' z : ℂ, (if z = z₀ then 0 else D z * fejerPowWin k V (z - s))‖ ≤
      ∑' z : ℂ, (if z = z₀ then 0 else ‖D z‖ * ‖fejerPowWin k V (z - s)‖) := by
    have hn : ∀ z : ℂ, ‖(if z = z₀ then 0 else D z * fejerPowWin k V (z - s))‖ =
        (if z = z₀ then 0 else ‖D z‖ * ‖fejerPowWin k V (z - s)‖) := fun z => by
      split_ifs <;> simp
    have hs' : Summable fun z : ℂ => (if z = z₀ then 0 else ‖D z‖ * ‖fejerPowWin k V (z - s)‖) :=
      (hsumL s).of_nonneg_of_le (fun z => by split_ifs <;> positivity)
        fun z => by split_ifs <;> first | positivity | exact le_rfl
    refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr hn)
    simp_rw [hn]
    exact hs'
  have hGre : ((M : ℂ) * fejerPowWin k V (-(σ : ℂ)) - ∑' z : ℂ, D z * fejerPowWin k V (z - σ)).re ≤
      |M| * ‖fejerPowWin k V (-σ)‖ + ∑' z : ℂ, ‖D z‖ * ‖fejerPowWin k V (z - σ)‖ := by
    rw [Complex.sub_re]
    have h1 : ((M : ℂ) * fejerPowWin k V (-(σ : ℂ))).re ≤ |M| * ‖fejerPowWin k V (-σ)‖ := by
      refine (Complex.re_le_norm _).trans_eq ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : -(∑' z : ℂ, D z * fejerPowWin k V (z - σ)).re ≤
        ∑' z : ℂ, ‖D z‖ * ‖fejerPowWin k V (z - σ)‖ := by
      refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ?_)
      refine (norm_tsum_le_tsum_norm (hsumC σ).norm).trans_eq ?_
      simp
    linarith
  set Gs := ∫ u in (0 : ℝ)..V, cexp (-s * u) *
    ((Real.sin (π * u / V) ^ (2 * k) * (M - 2 * (lagStructure Z b u).re) : ℝ) : ℂ) with hGsdef
  set R := ∑' z : ℂ, (if z = z₀ then 0 else D z * fejerPowWin k V (z - s)) with hRdef
  have hkey : D z₀ * fejerPowWin k V (z₀ - s) = M * fejerPowWin k V (-s) - Gs - R := by
    rw [hGs, hsplit]; ring
  rw [hkey]
  have htri : ‖(M : ℂ) * fejerPowWin k V (-s) - Gs - R‖ ≤
      ‖(M : ℂ) * fejerPowWin k V (-s)‖ + ‖Gs‖ + ‖R‖ :=
    (norm_sub_le _ _).trans (by linarith [norm_sub_le ((M : ℂ) * fejerPowWin k V (-s)) Gs])
  have hMn : ‖(M : ℂ) * fejerPowWin k V (-s)‖ = |M| * ‖fejerPowWin k V (-s)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hGb : ‖Gs‖ ≤ |M| * ‖fejerPowWin k V (-σ)‖ +
      ∑' z : ℂ, ‖D z‖ * ‖fejerPowWin k V (z - σ)‖ := by
    refine hpos.trans ?_
    rw [hGσ]
    exact hGre
  have hs1 : (-s : ℂ) = -(σ + t * I) := by rw [hs]
  rw [← hs1]
  linarith

end GaloisForLFunctions.SquareRootThreshold
