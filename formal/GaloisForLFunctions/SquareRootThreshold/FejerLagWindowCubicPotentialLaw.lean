import GaloisForLFunctions.SquareRootThreshold.FiniteLagWindowRecordPotentialLaw

/-!
# The Fejér lag window: a cubic record potential

The finite Laplace window of `FiniteLagWindowRecordPotentialLaw` weighs the lags `u ∈ [0, V]`
uniformly; its kernel `E_V(z) = (e^{zV} − 1)/z` decays like `|z|^{−1}`, so the potential of the
competitors of a zero is harmonic and the loudness ratio `N` enters linearly. Any weight
`w ≥ 0` keeps the positivity: if `φ(0) − φ ≥ 0` on `[0, V]`, then
`|∫_0^V w(u) e^{−su}(φ(0) − φ(u)) du| ≤ ∫_0^V w(u) e^{−σu}(φ(0) − φ(u)) du`.

**The Fejér weight** `w(u) = sin²(πu/V)` vanishes to second order at both ends. Since
`sin²(πu/V) = ½ − ¼e^{2πiu/V} − ¼e^{−2πiu/V}`, its kernel is
`F_V(z) = ½E_V(z) − ¼E_V(z + 2πi/V) − ¼E_V(z − 2πi/V) = 2π²(e^{zV} − 1)/(z(V²z² + 4π²))`
(`fejerWin`, `fejerWin_eq`): it decays like `|z|^{−3}` once `V|z| ≥ 4π`
(`norm_fejerWin_le_cube`).

**Cubic record-potential law** (`norm_evenCoeff_mul_fejerWin_le`,
`fejer_loudness_bound_of_lag_nonneg`). With the gaps `η` (exponents from the real axis) and `g`
(others from `s = σ + i Im z₀`), `Vη, Vg ≥ 4π`, `κ₃ = 1/η³ + 1/g³`, `θ = Re z₀ − σ`, loudness
ratio `N` at lag `V` and `(8/3)κ₃ N θ(V²θ² + 4π²) ≤ V²`, nonnegativity of the difference family
on `[0, V]` forces
`(4/3)κ₃ N |D(z₀)| (e^{θV} − 2) ≤ |M|(1/σ³ + 8/(3η³)) + (4/3)κ₃ Σ_z |D(z)|`.
With `θ = κ/V` the side condition reads `V³ ≥ (8/3)κ₃ N κ(κ² + 4π²)`: the loudness ratio enters
through `N^{1/3}` instead of `N` (`exists_lag_neg_of_fejer_loudness`). The gaps enter through
`V ≳ 1/g`: the lag must resolve the record from its loud neighbours, at the scale of the
square-root threshold `V ≍ log T` when the neighbours have the spacing `2π/log T` of `ζ`.
For `ζ` (`η = 4`): `zeta_fejer_crowding_of_lag_primeWindow_nonneg`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The Fejér kernel -/

/-- The Fejér kernel `F_V(z) = ∫_0^V sin²(πu/V) e^{zu} du`, written through `E_V`. -/
def fejerWin (V : ℝ) (z : ℂ) : ℂ :=
  lapWin V z / 2 - lapWin V (z + 2 * π * I / V) / 4 - lapWin V (z - 2 * π * I / V) / 4

/-- `sin²(πu/V) e^{−su} = ½e^{−su} − ¼e^{−(s − 2πi/V)u} − ¼e^{−(s + 2πi/V)u}`. -/
theorem sin_sq_mul_cexp_eq (V u : ℝ) (s : ℂ) :
    ((Real.sin (π * u / V) ^ 2 : ℝ) : ℂ) * cexp (-s * u) =
      cexp (-s * u) / 2 - cexp (-(s - 2 * π * I / V) * u) / 4 -
        cexp (-(s + 2 * π * I / V) * u) / 4 := by
  have hsin : ((Real.sin (π * u / V) ^ 2 : ℝ) : ℂ) =
      1 / 2 - cexp (2 * π * I / V * u) / 4 - cexp (-(2 * π * I / V) * u) / 4 := by
    have hc : ((Real.cos (2 * (π * u / V)) : ℝ) : ℂ) =
        (cexp (2 * π * I / V * u) + cexp (-(2 * π * I / V) * u)) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos]
      congr 3 <;> push_cast <;> ring
    rw [Real.sin_sq, Real.cos_sq, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_div, hc]
    push_cast
    ring
  rw [hsin]
  have h1 : cexp (2 * π * I / V * u) * cexp (-s * u) = cexp (-(s - 2 * π * I / V) * u) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : cexp (-(2 * π * I / V) * u) * cexp (-s * u) = cexp (-(s + 2 * π * I / V) * u) := by
    rw [← Complex.exp_add]; congr 1; ring
  linear_combination (-(1 : ℂ) / 4) * h1 - (1 / 4 : ℂ) * h2

/-- **Closed form.** `F_V(z) = 2π²(e^{zV} − 1)/(z(V²z² + 4π²))` for `z ≠ 0`, `V²z² + 4π² ≠ 0`. -/
theorem fejerWin_eq {V : ℝ} (hV : 0 < V) {z : ℂ} (h0 : z ≠ 0)
    (h1 : (V : ℂ) ^ 2 * z ^ 2 + 4 * π ^ 2 ≠ 0) :
    fejerWin V z = 2 * π ^ 2 * (cexp (z * V) - 1) / (z * ((V : ℂ) ^ 2 * z ^ 2 + 4 * π ^ 2)) := by
  have hV0 : (V : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
  set a : ℂ := 2 * π * I / V with ha
  have hprod : (z + a) * (z - a) * V ^ 2 = (V : ℂ) ^ 2 * z ^ 2 + 4 * π ^ 2 := by
    rw [ha]; field_simp; ring_nf; rw [Complex.I_sq]; ring
  have hza : z + a ≠ 0 := fun h => h1 (by rw [← hprod, h]; ring)
  have hzb : z - a ≠ 0 := fun h => h1 (by rw [← hprod, h]; ring)
  have hexp : ∀ c : ℂ, c = a ∨ c = -a → cexp ((z + c) * V) = cexp (z * V) := by
    rintro c (rfl | rfl)
    · rw [add_mul, Complex.exp_add, ha, show 2 * ↑π * I / ↑V * ↑V = 2 * π * I by field_simp,
        Complex.exp_two_pi_mul_I, mul_one]
    · rw [add_mul, Complex.exp_add, ha, show -(2 * ↑π * I / ↑V) * ↑V = -(2 * π * I) by
        field_simp, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
  have e1 := hexp a (Or.inl rfl)
  have e2 := hexp (-a) (Or.inr rfl)
  have hzb' : z + -a ≠ 0 := by rwa [← sub_eq_add_neg]
  rw [fejerWin, lapWin_eq V h0, lapWin_eq V hza, show z - 2 * π * I / V = z + -a by
    rw [ha]; ring, lapWin_eq V hzb', e1, e2, ← sub_eq_add_neg]
  have hz2 : z ^ 2 - a ^ 2 ≠ 0 := by
    rw [show z ^ 2 - a ^ 2 = (z + a) * (z - a) by ring]; exact mul_ne_zero hza hzb
  have step1 : 1 / (z * 2) - 1 / ((z + a) * 4) - 1 / ((z - a) * 4) =
      -a ^ 2 / (2 * z * (z ^ 2 - a ^ 2)) := by
    field_simp
    ring
  have ha2 : a ^ 2 = -(4 * π ^ 2) / (V : ℂ) ^ 2 := by
    rw [ha, div_pow, mul_pow, mul_pow, Complex.I_sq]; ring
  have hz2' : z ^ 2 - -(4 * π ^ 2) / (V : ℂ) ^ 2 ≠ 0 := by rwa [← ha2]
  have step2 : -a ^ 2 / (2 * z * (z ^ 2 - a ^ 2)) =
      2 * π ^ 2 / (z * ((V : ℂ) ^ 2 * z ^ 2 + 4 * π ^ 2)) := by
    have h1' : (V : ℂ) ^ 2 * z ^ 2 + (π : ℂ) ^ 2 * 4 ≠ 0 := by
      rw [mul_comm ((π : ℂ) ^ 2)]; exact h1
    rw [ha2]
    field_simp
    linear_combination 4 * mul_inv_cancel₀ h1'
  calc (cexp (z * V) - 1) / z / 2 - (cexp (z * V) - 1) / (z + a) / 4 -
        (cexp (z * V) - 1) / (z - a) / 4
      = (cexp (z * V) - 1) * (1 / (z * 2) - 1 / ((z + a) * 4) - 1 / ((z - a) * 4)) := by
        field_simp
    _ = _ := by rw [step1, step2]; ring

/-- `|V²z² + 4π²| ≥ ¾ V²|z|²` once `V|z| ≥ 4π`. -/
theorem norm_sq_add_ge {V : ℝ} {z : ℂ} (hz : 4 * π ≤ V * ‖z‖) :
    3 / 4 * (V ^ 2 * ‖z‖ ^ 2) ≤ ‖(V : ℂ) ^ 2 * z ^ 2 + 4 * π ^ 2‖ := by
  have h1 : ‖(V : ℂ) ^ 2 * z ^ 2‖ = V ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h2 : ‖(4 * π ^ 2 : ℂ)‖ = 4 * π ^ 2 := by
    rw [show (4 * π ^ 2 : ℂ) = ((4 * π ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h3 := norm_sub_norm_le ((V : ℂ) ^ 2 * z ^ 2) (-(4 * π ^ 2 : ℂ))
  rw [sub_neg_eq_add, norm_neg, h1, h2] at h3
  have h4 : 16 * π ^ 2 ≤ V ^ 2 * ‖z‖ ^ 2 := by nlinarith [Real.pi_pos]
  linarith

/-- **Cubic decay.** `|F_V(z)| ≤ (8π²/3)(e^{Re z·V} + 1)/(V²|z|³)` once `V|z| ≥ 4π`. -/
theorem norm_fejerWin_le_cube {V : ℝ} (hV : 0 < V) {z : ℂ} (hz : 4 * π ≤ V * ‖z‖) :
    ‖fejerWin V z‖ ≤ 8 * π ^ 2 / 3 * (Real.exp (z.re * V) + 1) / (V ^ 2 * ‖z‖ ^ 3) := by
  have hz0 : 0 < ‖z‖ := by
    by_contra h; push Not at h
    have : ‖z‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this, mul_zero] at hz; linarith [Real.pi_pos]
  have hq := norm_sq_add_ge hz
  have hq0 : 0 < ‖(V : ℂ) ^ 2 * z ^ 2 + 4 * π ^ 2‖ := lt_of_lt_of_le (by positivity) hq
  rw [fejerWin_eq hV (norm_pos_iff.mp hz0) (norm_pos_iff.mp hq0), norm_div,
    norm_mul (2 * (π : ℂ) ^ 2) (cexp (z * V) - 1), norm_mul z ((V : ℂ) ^ 2 * z ^ 2 + 4 * π ^ 2)]
  have hnum : ‖(2 * π ^ 2 : ℂ)‖ * ‖cexp (z * V) - 1‖ ≤ 2 * π ^ 2 * (Real.exp (z.re * V) + 1) := by
    have : ‖(2 * π ^ 2 : ℂ)‖ = 2 * π ^ 2 := by
      rw [show (2 * π ^ 2 : ℂ) = ((2 * π ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [this]
    refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans_eq ?_) (by positivity)
    simp [Complex.norm_exp]
  calc ‖(2 * π ^ 2 : ℂ)‖ * ‖cexp (z * V) - 1‖ / (‖z‖ * ‖(V : ℂ) ^ 2 * z ^ 2 + 4 * π ^ 2‖)
      ≤ 2 * π ^ 2 * (Real.exp (z.re * V) + 1) / (‖z‖ * (3 / 4 * (V ^ 2 * ‖z‖ ^ 2))) :=
        div_le_div₀ (by positivity) hnum (by positivity) (mul_le_mul_of_nonneg_left hq hz0.le)
    _ = 8 * π ^ 2 / 3 * (Real.exp (z.re * V) + 1) / (V ^ 2 * ‖z‖ ^ 3) := by
        field_simp; ring

/-- For `θ > 0`, `F_V(θ) = 2π²(e^{θV} − 1)/(θ(V²θ² + 4π²)) > 0`. -/
theorem norm_fejerWin_ofReal_pos {V : ℝ} (hV : 0 < V) {θ : ℝ} (hθ : 0 < θ) :
    ‖fejerWin V θ‖ = 2 * π ^ 2 * (Real.exp (θ * V) - 1) / (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2)) := by
  have hθ0 : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ.ne'
  have hq : (V : ℂ) ^ 2 * (θ : ℂ) ^ 2 + 4 * π ^ 2 ≠ 0 := by
    have : (0 : ℝ) < V ^ 2 * θ ^ 2 + 4 * π ^ 2 := by positivity
    exact_mod_cast this.ne'
  rw [fejerWin_eq hV hθ0 hq]
  have e : (2 * π ^ 2 * (cexp ((θ : ℂ) * V) - 1) / ((θ : ℂ) * ((V : ℂ) ^ 2 * (θ : ℂ) ^ 2 +
      4 * π ^ 2)) : ℂ) = ((2 * π ^ 2 * (Real.exp (θ * V) - 1) /
        (θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2)) : ℝ) : ℂ) := by
    push_cast; rw [← Complex.ofReal_mul]
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  have : 1 ≤ Real.exp (θ * V) := Real.one_le_exp (by positivity)
  exact div_nonneg (by nlinarith [Real.pi_pos]) (by positivity)

/-- For `σ > 0`, `|F_V(−σ)| ≤ 2π²/(V²σ³)`. -/
theorem norm_fejerWin_neg_le {V : ℝ} (hV : 0 < V) {σ : ℝ} (hσ : 0 < σ) :
    ‖fejerWin V (-(σ : ℂ))‖ ≤ 2 * π ^ 2 / (V ^ 2 * σ ^ 3) := by
  have hσ0 : (-(σ : ℂ)) ≠ 0 := by rw [neg_ne_zero]; exact_mod_cast hσ.ne'
  have hq : (V : ℂ) ^ 2 * (-(σ : ℂ)) ^ 2 + 4 * π ^ 2 ≠ 0 := by
    have : (0 : ℝ) < V ^ 2 * σ ^ 2 + 4 * π ^ 2 := by positivity
    rw [neg_sq]; exact_mod_cast this.ne'
  rw [fejerWin_eq hV hσ0 hq]
  have e : (2 * π ^ 2 * (cexp (-(σ : ℂ) * V) - 1) / (-(σ : ℂ) * ((V : ℂ) ^ 2 * (-(σ : ℂ)) ^ 2 +
      4 * π ^ 2)) : ℂ) = ((2 * π ^ 2 * (1 - Real.exp (-σ * V)) /
        (σ * (V ^ 2 * σ ^ 2 + 4 * π ^ 2)) : ℝ) : ℂ) := by
    push_cast
    rw [show -(σ : ℂ) * V = ((-σ * V : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp]
    field_simp
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  have h1 : Real.exp (-σ * V) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h2 : 0 < Real.exp (-σ * V) := Real.exp_pos _
  rw [abs_of_nonneg (div_nonneg (by nlinarith [Real.pi_pos]) (by positivity))]
  calc 2 * π ^ 2 * (1 - Real.exp (-σ * V)) / (σ * (V ^ 2 * σ ^ 2 + 4 * π ^ 2))
      ≤ 2 * π ^ 2 * 1 / (σ * (V ^ 2 * σ ^ 2)) :=
        div_le_div₀ (by positivity) (by nlinarith [Real.pi_pos]) (by positivity)
          (mul_le_mul_of_nonneg_left (by nlinarith [Real.pi_pos]) hσ.le)
    _ = 2 * π ^ 2 / (V ^ 2 * σ ^ 3) := by field_simp

/-! ### The Fejér window of the lag function -/

/-- The plain window `G(s) = ∫_0^V e^{−su}(φ(0) − φ(u)) du = φ(0) E_V(−s) − Σ_z D(z) E_V(z − s)`. -/
theorem integral_lagWindow_sub_eq (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V) (s : ℂ) :
    ∫ u in (0 : ℝ)..V, cexp (-s * u) *
        ((2 * (lagStructure Z b 0).re - 2 * (lagStructure Z b u).re : ℝ) : ℂ) =
      (2 * (lagStructure Z b 0).re : ℝ) * lapWin V (-s) -
        ∑' z : ℂ, evenCoeff Z b z * lapWin V (z - s) := by
  have hφc : Continuous fun u : ℝ => 2 * (lagStructure Z b u).re :=
    continuous_const.mul (Complex.continuous_re.comp (continuous_lagStructure Z hZ hb hbs))
  have e : ∀ u : ℝ, cexp (-s * u) *
      ((2 * (lagStructure Z b 0).re - 2 * (lagStructure Z b u).re : ℝ) : ℂ) =
      ((2 * (lagStructure Z b 0).re : ℝ) : ℂ) * cexp (-s * u) -
        cexp (-s * u) * ((2 * (lagStructure Z b u).re : ℝ) : ℂ) := fun u => by push_cast; ring
  rw [intervalIntegral.integral_congr fun u _ => e u]
  have hi1 : IntervalIntegrable (fun u : ℝ => ((2 * (lagStructure Z b 0).re : ℝ) : ℂ) *
      cexp (-s * u)) volume 0 V :=
    (Continuous.mul continuous_const (by fun_prop)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun u : ℝ => cexp (-s * u) *
      ((2 * (lagStructure Z b u).re : ℝ) : ℂ)) volume 0 V :=
    (Continuous.mul (by fun_prop) (Complex.continuous_ofReal.comp hφc)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul,
    integral_lagWindow_eq Z hZ hb hbs hV s, lapWin]

/-- Summability of `|D(z)| |K(z − s)|` for a kernel bounded on the strip. -/
theorem summable_evenCoeff_mul_lapWin (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V) (s : ℂ) :
    Summable fun z : ℂ => evenCoeff Z b z * lapWin V (z - s) :=
  (summable_norm_evenCoeff_mul Z hZ hb hbs (C := V * Real.exp ((1 / 2 + |s.re|) * V))
    (fun _ => norm_nonneg _) fun z hz => (norm_lapWin_le_const hV _).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by
        rw [Complex.sub_re]
        exact (abs_sub _ _).trans (by linarith [abs_re_le_of_evenCoeff_ne_zero hz])) hV)) hV)).of_norm_bounded
    fun z => (norm_mul _ _).le

/-- **The Fejér window, termwise.**
`∫_0^V sin²(πu/V) e^{−su}(φ(0) − φ(u)) du = φ(0) F_V(−s) − Σ_z D(z) F_V(z − s)`. -/
theorem integral_fejerWindow_eq (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V) (s : ℂ) :
    ∫ u in (0 : ℝ)..V, cexp (-s * u) * ((Real.sin (π * u / V) ^ 2 *
        (2 * (lagStructure Z b 0).re - 2 * (lagStructure Z b u).re) : ℝ) : ℂ) =
      (2 * (lagStructure Z b 0).re : ℝ) * fejerWin V (-s) -
        ∑' z : ℂ, evenCoeff Z b z * fejerWin V (z - s) := by
  set M : ℝ := 2 * (lagStructure Z b 0).re with hM
  have hgc : Continuous fun u : ℝ => M - 2 * (lagStructure Z b u).re := continuous_const.sub
    (continuous_const.mul (Complex.continuous_re.comp (continuous_lagStructure Z hZ hb hbs)))
  set a : ℂ := 2 * π * I / V with ha
  have hpt : ∀ u : ℝ, cexp (-s * u) *
      ((Real.sin (π * u / V) ^ 2 * (M - 2 * (lagStructure Z b u).re) : ℝ) : ℂ) =
      cexp (-s * u) * ((M - 2 * (lagStructure Z b u).re : ℝ) : ℂ) / 2 -
        cexp (-(s - a) * u) * ((M - 2 * (lagStructure Z b u).re : ℝ) : ℂ) / 4 -
        cexp (-(s + a) * u) * ((M - 2 * (lagStructure Z b u).re : ℝ) : ℂ) / 4 := fun u => by
    rw [Complex.ofReal_mul, ← mul_assoc, mul_comm (cexp (-s * u)), sin_sq_mul_cexp_eq V u s]
    ring
  rw [intervalIntegral.integral_congr fun u _ => hpt u]
  have hint : ∀ c : ℂ, IntervalIntegrable (fun u : ℝ => cexp (-c * u) *
      ((M - 2 * (lagStructure Z b u).re : ℝ) : ℂ) / 4) volume 0 V := fun c =>
    ((Continuous.mul (by fun_prop) (Complex.continuous_ofReal.comp hgc)).div_const
      _).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun u : ℝ => cexp (-s * u) *
      ((M - 2 * (lagStructure Z b u).re : ℝ) : ℂ) / 2) volume 0 V :=
    ((Continuous.mul (by fun_prop) (Complex.continuous_ofReal.comp hgc)).div_const
      _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hint2.sub (hint (s - a))) (hint (s + a)),
    intervalIntegral.integral_sub hint2 (hint (s - a)), intervalIntegral.integral_div,
    intervalIntegral.integral_div, intervalIntegral.integral_div]
  have hG := fun c : ℂ => integral_lagWindow_sub_eq Z hZ hb hbs hV c
  rw [hG s, hG (s - a), hG (s + a)]
  have hs1 := summable_evenCoeff_mul_lapWin Z hZ hb hbs hV s
  have hs2 := summable_evenCoeff_mul_lapWin Z hZ hb hbs hV (s - a)
  have hs3 := summable_evenCoeff_mul_lapWin Z hZ hb hbs hV (s + a)
  have hcomb : ∑' z : ℂ, evenCoeff Z b z * fejerWin V (z - s) =
      (∑' z : ℂ, evenCoeff Z b z * lapWin V (z - s)) / 2 -
        (∑' z : ℂ, evenCoeff Z b z * lapWin V (z - (s - a))) / 4 -
        (∑' z : ℂ, evenCoeff Z b z * lapWin V (z - (s + a))) / 4 := by
    rw [← tsum_div_const, ← tsum_div_const, ← tsum_div_const,
      ← (hs1.div_const 2).tsum_sub (hs2.div_const 4),
      ← ((hs1.div_const 2).sub (hs2.div_const 4)).tsum_sub (hs3.div_const 4)]
    refine tsum_congr fun z => ?_
    rw [fejerWin, show z - (s - a) = z - s + a by ring, show z - (s + a) = z - s - a by ring, ha]
    ring
  rw [hcomb, fejerWin, show -(s - a) = -s + a by ring, show -(s + a) = -s - a by ring, ← ha]
  ring

/-- `|F_V(w)| ≤ V e^{|Re w| V}`. -/
theorem norm_fejerWin_le_const {V : ℝ} (hV : 0 ≤ V) (w : ℂ) :
    ‖fejerWin V w‖ ≤ V * Real.exp (|w.re| * V) := by
  have h : ∀ c : ℂ, c.re = 0 → ‖lapWin V (w + c)‖ ≤ V * Real.exp (|w.re| * V) := fun c hc => by
    have := norm_lapWin_le_const hV (w + c); rwa [Complex.add_re, hc, add_zero] at this
  have ha : (2 * π * I / V : ℂ).re = 0 := by simp
  have h1 := h 0 (by simp)
  have h2 := h _ ha
  have h3 := h (-(2 * π * I / V)) (by rw [Complex.neg_re, ha, neg_zero])
  rw [add_zero] at h1
  rw [fejerWin, ← sub_eq_add_neg] at *
  calc ‖lapWin V w / 2 - lapWin V (w + 2 * π * I / V) / 4 - lapWin V (w - 2 * π * I / V) / 4‖
      ≤ ‖lapWin V w‖ / 2 + ‖lapWin V (w + 2 * π * I / V)‖ / 4 +
          ‖lapWin V (w - 2 * π * I / V)‖ / 4 := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans_eq ?_) ?_)
        · simp
        · simp
    _ ≤ V * Real.exp (|w.re| * V) := by
        rw [sub_eq_add_neg] at h3
        rw [sub_eq_add_neg]
        linarith

/-! ### The cubic record-potential law -/

/-- **Fejér record-potential law.** If the difference tests are Weil nonnegative on `[0, V]`,
then for every exponent `z₀` and `s = σ + it`, with `M = 2 Re S(0)`:
`|D(z₀) F_V(z₀ − s)| ≤ |M|(|F_V(−σ)| + |F_V(−s)|) + Σ_z |D(z)||F_V(z − σ)|
  + Σ_{z ≠ z₀} |D(z)||F_V(z − s)|`. -/
theorem norm_evenCoeff_mul_fejerWin_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 ≤ V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    (z₀ : ℂ) (σ t : ℝ) :
    ‖evenCoeff Z b z₀ * fejerWin V (z₀ - (σ + t * I))‖ ≤
      |2 * (lagStructure Z b 0).re| * (‖fejerWin V (-σ)‖ + ‖fejerWin V (-(σ + t * I))‖) +
      ∑' z : ℂ, ‖evenCoeff Z b z‖ * ‖fejerWin V (z - σ)‖ +
      ∑' z : ℂ, (if z = z₀ then 0 else ‖evenCoeff Z b z‖ * ‖fejerWin V (z - (σ + t * I))‖) := by
  classical
  set D := evenCoeff Z b with hDdef
  set M : ℝ := 2 * (lagStructure Z b 0).re with hM
  have hg : ∀ u ∈ Icc (0 : ℝ) V,
      0 ≤ Real.sin (π * u / V) ^ 2 * (M - 2 * (lagStructure Z b u).re) := fun u hu => by
    have := hm u hu
    rw [re_W_lag_eq Z hZ hb hbs u] at this
    exact mul_nonneg (sq_nonneg _) this
  have hG := integral_fejerWindow_eq Z hZ hb hbs hV
  have hsumL : ∀ s : ℂ, Summable fun z : ℂ => ‖D z‖ * ‖fejerWin V (z - s)‖ := fun s =>
    summable_norm_evenCoeff_mul Z hZ hb hbs (C := V * Real.exp ((1 / 2 + |s.re|) * V))
      (fun _ => norm_nonneg _) fun z hz => (norm_fejerWin_le_const hV _).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by
          rw [Complex.sub_re]
          exact (abs_sub _ _).trans (by linarith [abs_re_le_of_evenCoeff_ne_zero hz]))
          hV)) hV)
  have hsumC : ∀ s : ℂ, Summable fun z : ℂ => D z * fejerWin V (z - s) := fun s =>
    (hsumL s).of_norm_bounded fun z => (norm_mul _ _).le
  set s : ℂ := σ + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hpos := norm_integral_cexp_mul_le hV hg s
  rw [hsre] at hpos
  have hGs := hG s
  have hGσ := hG σ
  have hsplit := (hsumC s).tsum_eq_add_tsum_ite z₀
  have hrest : ‖∑' z : ℂ, (if z = z₀ then 0 else D z * fejerWin V (z - s))‖ ≤
      ∑' z : ℂ, (if z = z₀ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) := by
    have hn : ∀ z : ℂ, ‖(if z = z₀ then 0 else D z * fejerWin V (z - s))‖ =
        (if z = z₀ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) := fun z => by
      split_ifs <;> simp
    have hs' : Summable fun z : ℂ => (if z = z₀ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) :=
      (hsumL s).of_nonneg_of_le (fun z => by split_ifs <;> positivity)
        fun z => by split_ifs <;> first | positivity | exact le_rfl
    refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr hn)
    simp_rw [hn]
    exact hs'
  have hGre : ((M : ℂ) * fejerWin V (-(σ : ℂ)) - ∑' z : ℂ, D z * fejerWin V (z - σ)).re ≤
      |M| * ‖fejerWin V (-σ)‖ + ∑' z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ := by
    rw [Complex.sub_re]
    have h1 : ((M : ℂ) * fejerWin V (-(σ : ℂ))).re ≤ |M| * ‖fejerWin V (-σ)‖ := by
      refine (Complex.re_le_norm _).trans_eq ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h2 : -(∑' z : ℂ, D z * fejerWin V (z - σ)).re ≤
        ∑' z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ := by
      refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ?_)
      refine (norm_tsum_le_tsum_norm (hsumC σ).norm).trans_eq ?_
      simp
    linarith
  set Gs := ∫ u in (0 : ℝ)..V, cexp (-s * u) *
    ((Real.sin (π * u / V) ^ 2 * (M - 2 * (lagStructure Z b u).re) : ℝ) : ℂ) with hGsdef
  set R := ∑' z : ℂ, (if z = z₀ then 0 else D z * fejerWin V (z - s)) with hRdef
  have hkey : D z₀ * fejerWin V (z₀ - s) = M * fejerWin V (-s) - Gs - R := by
    rw [hGs, hsplit]; ring
  rw [hkey]
  have htri : ‖(M : ℂ) * fejerWin V (-s) - Gs - R‖ ≤ ‖(M : ℂ) * fejerWin V (-s)‖ + ‖Gs‖ + ‖R‖ :=
    (norm_sub_le _ _).trans (by linarith [norm_sub_le ((M : ℂ) * fejerWin V (-s)) Gs])
  have hMn : ‖(M : ℂ) * fejerWin V (-s)‖ = |M| * ‖fejerWin V (-s)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hGb : ‖Gs‖ ≤ |M| * ‖fejerWin V (-σ)‖ + ∑' z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ := by
    refine hpos.trans ?_
    rw [hGσ]
    exact hGre
  have hs1 : (-s : ℂ) = -(σ + t * I) := by rw [hs]
  rw [← hs1]
  linarith

/-! ### Explicit lags -/

/-- `|F_V(z − u)| ≤ (8π²/3)(e^{(Re z − Re u)V} + 1)/(V²c³)` when `|z − u| ≥ c` and `Vc ≥ 4π`. -/
theorem norm_fejerWin_sub_le {V c : ℝ} (hV : 0 < V) (hc : 0 < c) (hVc : 4 * π ≤ V * c) {z u : ℂ}
    (hzu : c ≤ ‖z - u‖) :
    ‖fejerWin V (z - u)‖ ≤ 8 * π ^ 2 / 3 * (Real.exp ((z.re - u.re) * V) + 1) / (V ^ 2 * c ^ 3) := by
  have h4 : 4 * π ≤ V * ‖z - u‖ := hVc.trans (mul_le_mul_of_nonneg_left hzu hV.le)
  refine (norm_fejerWin_le_cube hV h4).trans ?_
  rw [Complex.sub_re]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hzu 3) (by positivity))

/-- **Fejér loudness bound.** Let the difference tests be Weil nonnegative on `[0, V]`, `V > 0`.
Let `|Im z| ≥ η` on the exponents and at `z₀`, let the exponents `z ≠ z₀` keep distance `g` from
`s = σ + i Im z₀`, `Vη, Vg ≥ 4π`, `κ₃ = 1/η³ + 1/g³`, `θ = Re z₀ − σ > 0`,
`(8/3)κ₃ N θ(V²θ² + 4π²) ≤ V²`, and loudness at lag `V` at most `N` times that of `z₀`. Then
`(4/3)κ₃ N |D(z₀)| (e^{θV} − 2) ≤ |M|(1/σ³ + 8/(3η³)) + (4/3)κ₃ Σ_z |D(z)|`. -/
theorem fejer_loudness_bound_of_lag_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 < V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {η g σ N : ℝ} (hη : 0 < η) (hηz : ∀ z, evenCoeff Z b z ≠ 0 → η ≤ |z.im|)
    (hVη : 4 * π ≤ V * η) (hg : 0 < g) (hVg : 4 * π ≤ V * g) {z₀ : ℂ} (hη₀ : η ≤ |z₀.im|)
    (hσ : 0 < σ) (hθ : σ < z₀.re)
    (hsep : ∀ z, z ≠ z₀ → evenCoeff Z b z ≠ 0 → g ≤ ‖z - (σ + z₀.im * I)‖)
    (hθN : 8 / 3 * (1 / η ^ 3 + 1 / g ^ 3) * N * ((z₀.re - σ) * (V ^ 2 * (z₀.re - σ) ^ 2 +
      4 * π ^ 2)) ≤ V ^ 2)
    (hL : ∑' z : ℂ, ‖evenCoeff Z b z‖ * Real.exp (z.re * V) ≤
      N * ‖evenCoeff Z b z₀‖ * Real.exp (z₀.re * V)) :
    4 / 3 * (1 / η ^ 3 + 1 / g ^ 3) * N * ‖evenCoeff Z b z₀‖ *
        (Real.exp ((z₀.re - σ) * V) - 2) ≤
      |2 * (lagStructure Z b 0).re| * (1 / σ ^ 3 + 8 / (3 * η ^ 3)) +
        4 / 3 * (1 / η ^ 3 + 1 / g ^ 3) * ∑' z : ℂ, ‖evenCoeff Z b z‖ := by
  classical
  set D := evenCoeff Z b with hDdef
  set M : ℝ := 2 * (lagStructure Z b 0).re with hM
  set κ : ℝ := 1 / η ^ 3 + 1 / g ^ 3 with hκ
  set θ : ℝ := z₀.re - σ with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  set s : ℂ := σ + z₀.im * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hcore := norm_evenCoeff_mul_fejerWin_le Z hZ hb hbs hV.le hm z₀ σ z₀.im
  rw [← hs] at hcore
  have hz₀s : z₀ - s = (θ : ℂ) := by apply Complex.ext <;> simp [hs, hθdef]
  set Q : ℝ := θ * (V ^ 2 * θ ^ 2 + 4 * π ^ 2) with hQ
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hLHS : ‖D z₀ * fejerWin V (z₀ - s)‖ = ‖D z₀‖ * (2 * π ^ 2 * (Real.exp (θ * V) - 1) / Q) := by
    rw [norm_mul, hz₀s, norm_fejerWin_ofReal_pos hV hθ0]
  set c : ℝ := 8 * π ^ 2 / 3 with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  -- the archimedean-pole kernels
  have hE1 : ‖fejerWin V (-(σ : ℂ))‖ ≤ 2 * π ^ 2 / (V ^ 2 * σ ^ 3) := norm_fejerWin_neg_le hV hσ
  have hE2 : ‖fejerWin V (-s)‖ ≤ c * 2 / (V ^ 2 * η ^ 3) := by
    have hsη : η ≤ ‖(0 : ℂ) - s‖ := by
      rw [zero_sub, norm_neg]
      exact hη₀.trans (by have := Complex.abs_im_le_norm s; simpa [hs] using this)
    have := norm_fejerWin_sub_le hV hη hVη (z := 0) (u := s) hsη
    rw [zero_sub] at this
    refine this.trans ?_
    rw [Complex.zero_re, hsre, ← hc]
    have : Real.exp ((0 - σ) * V) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    gcongr
    linarith
  -- the potentials
  set T : ℝ := ∑' z : ℂ, ‖D z‖ * (Real.exp ((z.re - σ) * V) + 1) with hT
  have hsL : Summable fun z : ℂ => ‖D z‖ * Real.exp (z.re * V) :=
    summable_norm_evenCoeff_mul Z hZ hb hbs (C := Real.exp (1 / 2 * V))
      (fun _ => (Real.exp_pos _).le) fun z hz => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans (abs_re_le_of_evenCoeff_ne_zero hz)) hV.le)
  have hsD := summable_norm_evenCoeff Z hZ hb hbs
  have hTeq : T = Real.exp (-σ * V) * ∑' z : ℂ, ‖D z‖ * Real.exp (z.re * V) +
      ∑' z : ℂ, ‖D z‖ := by
    rw [hT, ← tsum_mul_left, ← (hsL.mul_left _).tsum_add hsD]
    refine tsum_congr fun z => ?_
    rw [show (z.re - σ) * V = -σ * V + z.re * V by ring, Real.exp_add]
    ring
  have hsT : Summable fun z : ℂ => ‖D z‖ * (Real.exp ((z.re - σ) * V) + 1) := by
    refine ((hsL.mul_left (Real.exp (-σ * V))).add hsD).congr fun z => ?_
    rw [show (z.re - σ) * V = -σ * V + z.re * V by ring, Real.exp_add]
    ring
  have hkern : ∀ {z u : ℂ} {r : ℝ}, 0 < r → 4 * π ≤ V * r → u.re = σ → r ≤ ‖z - u‖ →
      ‖D z‖ * ‖fejerWin V (z - u)‖ ≤
        c / (V ^ 2 * r ^ 3) * (‖D z‖ * (Real.exp ((z.re - σ) * V) + 1)) :=
    fun {z u r} hr hVr hu hgap => by
      have := norm_fejerWin_sub_le hV hr hVr hgap
      rw [hu, ← hc] at this
      calc ‖D z‖ * ‖fejerWin V (z - u)‖ ≤
            ‖D z‖ * (c * (Real.exp ((z.re - σ) * V) + 1) / (V ^ 2 * r ^ 3)) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = _ := by ring
  have hP1 : ∑' z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ ≤ c / (V ^ 2 * η ^ 3) * T := by
    rw [hT, ← tsum_mul_left]
    have hle1 : ∀ z : ℂ, ‖D z‖ * ‖fejerWin V (z - σ)‖ ≤
        c / (V ^ 2 * η ^ 3) * (‖D z‖ * (Real.exp ((z.re - σ) * V) + 1)) := fun z => by
      by_cases hz : D z = 0
      · simp [hz]
      · exact hkern hη hVη (by simp) ((hηz z hz).trans (by
          have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this))
    exact Summable.tsum_le_tsum hle1 ((hsT.mul_left _).of_nonneg_of_le
      (fun _ => by positivity) hle1) (hsT.mul_left _)
  have hP2 : ∑' z : ℂ, (if z = z₀ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) ≤
      c / (V ^ 2 * g ^ 3) * T := by
    rw [hT, ← tsum_mul_left]
    have hle2 : ∀ z : ℂ, (if z = z₀ then 0 else ‖D z‖ * ‖fejerWin V (z - s)‖) ≤
        c / (V ^ 2 * g ^ 3) * (‖D z‖ * (Real.exp ((z.re - σ) * V) + 1)) := fun z => by
      split_ifs with hzz
      · positivity
      · by_cases hz : D z = 0
        · simp [hz]
        · exact hkern hg hVg hsre (hsep z hzz hz)
    exact Summable.tsum_le_tsum hle2 ((hsT.mul_left _).of_nonneg_of_le
      (fun z => by split_ifs <;> positivity) hle2) (hsT.mul_left _)
  have hTb : T ≤ N * ‖D z₀‖ * Real.exp (θ * V) + ∑' z : ℂ, ‖D z‖ := by
    rw [hTeq]
    have h1 : Real.exp (-σ * V) * ∑' z : ℂ, ‖D z‖ * Real.exp (z.re * V) ≤
        N * ‖D z₀‖ * Real.exp (θ * V) := by
      calc Real.exp (-σ * V) * ∑' z : ℂ, ‖D z‖ * Real.exp (z.re * V)
          ≤ Real.exp (-σ * V) * (N * ‖D z₀‖ * Real.exp (z₀.re * V)) :=
            mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
        _ = N * ‖D z₀‖ * Real.exp (θ * V) := by
            rw [hθdef, show (z₀.re - σ) * V = -σ * V + z₀.re * V by ring, Real.exp_add]; ring
    linarith
  -- assemble, in units of `2π²/V²`
  set u : ℝ := 2 * π ^ 2 / V ^ 2 with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hcu1 : c / (V ^ 2 * η ^ 3) = u * (4 / 3) * (1 / η ^ 3) := by
    rw [hc, hu]; field_simp; ring
  have hcu2 : c / (V ^ 2 * g ^ 3) = u * (4 / 3) * (1 / g ^ 3) := by
    rw [hc, hu]; field_simp; ring
  have hE1' : 2 * π ^ 2 / (V ^ 2 * σ ^ 3) = u * (1 / σ ^ 3) := by rw [hu]; field_simp
  have hE2' : c * 2 / (V ^ 2 * η ^ 3) = u * (8 / (3 * η ^ 3)) := by rw [hc, hu]; field_simp
  have hT0 : 0 ≤ T := tsum_nonneg fun z => by positivity
  have hbig : ‖D z₀‖ * (2 * π ^ 2 * (Real.exp (θ * V) - 1) / Q) ≤
      u * (|M| * (1 / σ ^ 3 + 8 / (3 * η ^ 3)) + 4 / 3 * κ * T) := by
    rw [← hLHS]
    refine hcore.trans ?_
    have hM0 := abs_nonneg M
    have h1 : |M| * (‖fejerWin V (-(σ : ℂ))‖ + ‖fejerWin V (-s)‖) ≤
        u * (|M| * (1 / σ ^ 3 + 8 / (3 * η ^ 3))) := by
      calc |M| * (‖fejerWin V (-(σ : ℂ))‖ + ‖fejerWin V (-s)‖) ≤
            |M| * (u * (1 / σ ^ 3) + u * (8 / (3 * η ^ 3))) :=
            mul_le_mul_of_nonneg_left (add_le_add (hE1.trans_eq hE1') (hE2.trans_eq hE2')) hM0
        _ = _ := by ring
    have h2 : c / (V ^ 2 * η ^ 3) * T + c / (V ^ 2 * g ^ 3) * T = u * (4 / 3 * κ * T) := by
      rw [hcu1, hcu2, hκ]; ring
    linarith
  have hexp : 0 ≤ Real.exp (θ * V) - 1 := by
    linarith [Real.one_le_exp (mul_nonneg hθ0.le hV.le)]
  -- `1/Q ≥ (8/3)κN/V²`
  have hθN' : 8 / 3 * κ * N * Q ≤ V ^ 2 := by rw [hQ]; exact hθN
  have hlow : u * (8 / 3 * κ * N * ‖D z₀‖ * (Real.exp (θ * V) - 1)) ≤
      ‖D z₀‖ * (2 * π ^ 2 * (Real.exp (θ * V) - 1) / Q) := by
    have hX : 0 ≤ ‖D z₀‖ * (Real.exp (θ * V) - 1) := mul_nonneg (norm_nonneg _) hexp
    have : u * (8 / 3 * κ * N) ≤ 2 * π ^ 2 / Q := by
      rw [hu, le_div_iff₀ hQ0]
      calc 2 * π ^ 2 / V ^ 2 * (8 / 3 * κ * N) * Q = 2 * π ^ 2 / V ^ 2 * (8 / 3 * κ * N * Q) := by
            ring
        _ ≤ 2 * π ^ 2 / V ^ 2 * V ^ 2 := mul_le_mul_of_nonneg_left hθN' (by positivity)
        _ = 2 * π ^ 2 := by field_simp
    calc u * (8 / 3 * κ * N * ‖D z₀‖ * (Real.exp (θ * V) - 1))
        = u * (8 / 3 * κ * N) * (‖D z₀‖ * (Real.exp (θ * V) - 1)) := by ring
      _ ≤ 2 * π ^ 2 / Q * (‖D z₀‖ * (Real.exp (θ * V) - 1)) :=
          mul_le_mul_of_nonneg_right this hX
      _ = _ := by ring
  have hfin : u * (8 / 3 * κ * N * ‖D z₀‖ * (Real.exp (θ * V) - 1)) ≤
      u * (|M| * (1 / σ ^ 3 + 8 / (3 * η ^ 3)) +
        4 / 3 * κ * (N * ‖D z₀‖ * Real.exp (θ * V) + ∑' z : ℂ, ‖D z‖)) :=
    hlow.trans (hbig.trans (mul_le_mul_of_nonneg_left (by
      have := mul_le_mul_of_nonneg_left hTb (show (0 : ℝ) ≤ 4 / 3 * κ by positivity)
      linarith) hu0.le))
  have hfin' := le_of_mul_le_mul_left hfin hu0
  linarith

/-- **Explicit first negative lag (Fejér).** Under the hypotheses of
`fejer_loudness_bound_of_lag_nonneg`, if `(4/3)κ₃ N |D(z₀)|(e^{θV} − 2)` exceeds
`|M|(1/σ³ + 8/(3η³)) + (4/3)κ₃ Σ_z |D(z)|`, some lag `v ∈ [0, V]` has `Re W(f_v, f_v) < 0`. -/
theorem exists_lag_neg_of_fejer_loudness (Z : ZeroConfig) (hZ : TemperedConfig Z) {b : ℝ → ℂ}
    (hb : ContDiff ℝ 2 b) {w : ℝ} (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 < V)
    {η g σ N : ℝ} (hη : 0 < η) (hηz : ∀ z, evenCoeff Z b z ≠ 0 → η ≤ |z.im|)
    (hVη : 4 * π ≤ V * η) (hg : 0 < g) (hVg : 4 * π ≤ V * g) {z₀ : ℂ} (hη₀ : η ≤ |z₀.im|)
    (hσ : 0 < σ) (hθ : σ < z₀.re)
    (hsep : ∀ z, z ≠ z₀ → evenCoeff Z b z ≠ 0 → g ≤ ‖z - (σ + z₀.im * I)‖)
    (hθN : 8 / 3 * (1 / η ^ 3 + 1 / g ^ 3) * N * ((z₀.re - σ) * (V ^ 2 * (z₀.re - σ) ^ 2 +
      4 * π ^ 2)) ≤ V ^ 2)
    (hL : ∑' z : ℂ, ‖evenCoeff Z b z‖ * Real.exp (z.re * V) ≤
      N * ‖evenCoeff Z b z₀‖ * Real.exp (z₀.re * V))
    (hbig : |2 * (lagStructure Z b 0).re| * (1 / σ ^ 3 + 8 / (3 * η ^ 3)) +
        4 / 3 * (1 / η ^ 3 + 1 / g ^ 3) * ∑' z : ℂ, ‖evenCoeff Z b z‖ <
      4 / 3 * (1 / η ^ 3 + 1 / g ^ 3) * N * ‖evenCoeff Z b z₀‖ *
        (Real.exp ((z₀.re - σ) * V) - 2)) :
    ∃ v ∈ Icc (0 : ℝ) V, (Z.W (twoBump b v (-1)) (twoBump b v (-1))).re < 0 := by
  by_contra h
  push Not at h
  exact (fejer_loudness_bound_of_lag_nonneg Z hZ hb hbs hV h hη hηz hVη hg hVg hη₀ hσ hθ hsep
    hθN hL).not_gt hbig

/-- **The Fejér crowding law for `ζ`.** If the dyadic window functionals of a width
`w ∈ (0, ½ log 2)` are nonnegative for all `v ∈ [0, V]`, `V ≥ π`, every off-line exponent `z₀`
satisfies, with `η = 4`, separation `g` (`Vg ≥ 4π`) of the others from `σ + i Im z₀`,
`κ₃ = 1/64 + 1/g³` and the side condition `(8/3)κ₃ N θ(V²θ² + 4π²) ≤ V²`:
`(4/3)κ₃ N |D(z₀)| (e^{θV} − 2) ≤ |M|(1/σ³ + 1/24) + (4/3)κ₃ Σ|D|`. -/
theorem zeta_fejer_crowding_of_lag_primeWindow_nonneg {w V : ℝ} (hw : 0 < w)
    (hw2 : 2 * w < Real.log 2) (hV : π ≤ V)
    (hP : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (lagPrimeWindowRHS v w (EF.weilTest
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)))).re)
    {g σ N : ℝ} (hg : 0 < g) (hVg : 4 * π ≤ V * g) {z₀ : ℂ}
    (hz₀ : evenCoeff zetaZeroConfig (modScaledBump w 0) z₀ ≠ 0) (hσ : 0 < σ) (hθ : σ < z₀.re)
    (hsep : ∀ z, z ≠ z₀ → evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 →
      g ≤ ‖z - (σ + z₀.im * I)‖)
    (hθN : 8 / 3 * (1 / 4 ^ 3 + 1 / g ^ 3) * N * ((z₀.re - σ) * (V ^ 2 * (z₀.re - σ) ^ 2 +
      4 * π ^ 2)) ≤ V ^ 2)
    (hL : ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
      N * ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₀‖ * Real.exp (z₀.re * V)) :
    4 / 3 * (1 / 4 ^ 3 + 1 / g ^ 3) * N * ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₀‖ *
        (Real.exp ((z₀.re - σ) * V) - 2) ≤
      |2 * (lagStructure zetaZeroConfig (modScaledBump w 0) 0).re| *
          (1 / σ ^ 3 + 8 / (3 * 4 ^ 3)) +
        4 / 3 * (1 / 4 ^ 3 + 1 / g ^ 3) *
          ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ := by
  have hV0 : 0 < V := lt_of_lt_of_le Real.pi_pos hV
  have hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re := fun v hv => by
    rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump w 0) v (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
      (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
        (modScaledBump_support hw 0)) v (-1)),
      literatureRHS_twoBump_eq_lagPrimeWindowRHS (modScaledBump_support hw 0) hw2 hv.1]
    exact hP v hv
  exact fejer_loudness_bound_of_lag_nonneg zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w 0) (modScaledBump_support hw 0) hV0 hm (by norm_num)
    (fun z hz => four_le_abs_im_of_evenCoeff_zeta hz) (by nlinarith [Real.pi_pos]) hg hVg
    (four_le_abs_im_of_evenCoeff_zeta hz₀) hσ hθ hsep hθN hL

end GaloisForLFunctions.SquareRootThreshold
