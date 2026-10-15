import GaloisForLFunctions.RHTower.EvenSectorFarBumpPoleFreeCombination
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares

/-!
# Laplace transforms of window sums and their Abel limits

For a continuous compactly supported kernel `q` and real weights with `Σ |lam(n)| n^{−σ} < ∞`
(`σ > 1`), the window sum `Q_lam(a) = Σ_{n ≥ 2} lam(n) n^{−1/2} q(log n − a)` has Laplace transform

`∫ Q_lam(a) e^{−(1/2+s)a} da = (∫ q(u) e^{(1/2+s)u} du) · F(s)`,
`F(s) = Σ_{n ≥ 2} lam(n) n^{−1−s}`

(`integral_kernelSum_mul_exp`).  So in Abel means every window profile sees the same density
`s F(s)`.  For the cross kernel `h = g ⋆ φ̃` of a real even test the profile constant is
`∫ h(u) e^{u/2} du = P J` (`farCrossLaplace_zero`), the product of the pole values of `g` and `φ`,
and it moves by `O(s)` (`abs_farCrossLaplace_sub_le`); the same holds for `k = φ ⋆ φ̃`
(`abs_farLaplace_sub_le`).  Integrals over `(−∞, a₀)` of window sums are bounded uniformly in the
Laplace exponent (`abs_setIntegral_Iio_mul_exp_le`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open OddSector WeilOneSided WeilPoleWeight

/-! ## Laplace transforms of kernel window sums -/

theorem integrable_kernel_log_sub {q : ℝ → ℝ} (hq : Continuous q) (hqc : HasCompactSupport q)
    (μ L : ℝ) : Integrable fun a => q (L - a) * Real.exp (-μ * a) := by
  have hF : Integrable fun u => q u * Real.exp (μ * u) :=
    (hq.mul (by fun_prop)).integrable_of_hasCompactSupport hqc.mul_right
  refine ((hF.comp_sub_left L).const_mul (Real.exp (-μ * L))).congr
    (Eventually.of_forall fun a => ?_)
  show Real.exp (-μ * L) * (q (L - a) * Real.exp (μ * (L - a))) = q (L - a) * Real.exp (-μ * a)
  rw [mul_left_comm, ← Real.exp_add]
  congr 2; ring

theorem integral_kernel_log_sub (q : ℝ → ℝ) (μ L : ℝ) :
    ∫ a, q (L - a) * Real.exp (-μ * a) = Real.exp (-μ * L) * ∫ u, q u * Real.exp (μ * u) := by
  have hpt : (fun a => q (L - a) * Real.exp (-μ * a)) =
      fun a => Real.exp (-μ * L) * (q (L - a) * Real.exp (μ * (L - a))) := by
    funext a; rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  rw [hpt, integral_const_mul]
  congr 1
  exact integral_sub_left_eq_self (fun u => q u * Real.exp (μ * u)) volume L

/-- The window sum `Σ_{n ≥ 2} lam(n) n^{−1/2} q(log n − a)`. -/
def windowKernelSum (lam : ℕ → ℝ) (q : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then lam n / Real.sqrt n else 0) * q (Real.log n - a)

theorem farCrossSum_eq_kernelSum (lam : ℕ → ℝ) (g : ℝ → ℝ) :
    farCrossSum lam g = windowKernelSum lam (farCrossKernel g) := rfl

theorem coeff_mul_exp_eq (lam : ℕ → ℝ) (s : ℝ) (n : ℕ) :
    (if 2 ≤ n then lam n / Real.sqrt n else 0) * Real.exp (-(1 / 2 + s) * Real.log n) =
      (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + s) := by
  split_ifs with hn
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have e : -(1 / 2 + s) * Real.log n + Real.log n * (1 + s) = Real.log n * (1 / 2) := by ring
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0,
      div_mul_eq_mul_div, div_eq_div_iff (Real.exp_pos _).ne' (Real.exp_pos _).ne', mul_assoc,
      ← Real.exp_add, e]
  · simp

theorem summable_abs_coeff_mul_exp {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℝ} (hs : 0 < s) :
    Summable fun n : ℕ => |(if 2 ≤ n then lam n / Real.sqrt n else 0)| *
      Real.exp (-(1 / 2 + s) * Real.log n) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hsl (1 + s) (by linarith))
  rw [← abs_of_pos (Real.exp_pos (-(1 / 2 + s) * Real.log n)), ← abs_mul, coeff_mul_exp_eq]
  have hp : 0 ≤ (n : ℝ) ^ (1 + s) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  split_ifs
  · rw [abs_div, abs_of_nonneg hp]
  · rw [zero_div, abs_zero]; positivity

/-- **Laplace transform of a window sum.**  For `s > 0`,
`∫ Q_lam(a) e^{−(1/2+s)a} da = (∫ q(u) e^{(1/2+s)u} du) F(s)`, the integrand being integrable. -/
theorem integral_kernelSum_mul_exp {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {q : ℝ → ℝ}
    (hq : Continuous q) (hqc : HasCompactSupport q) {s : ℝ} (hs : 0 < s) :
    Integrable (fun a => windowKernelSum lam q a * Real.exp (-(1 / 2 + s) * a)) ∧
      ∫ a, windowKernelSum lam q a * Real.exp (-(1 / 2 + s) * a) =
        (∫ u, q u * Real.exp ((1 / 2 + s) * u)) * oddDirichlet lam s := by
  set c : ℕ → ℝ := fun n => if 2 ≤ n then lam n / Real.sqrt n else 0 with hc
  set f : ℕ → ℝ → ℝ := fun n a => c n * (q (Real.log n - a) *
    Real.exp (-(1 / 2 + s) * a)) with hf
  have hfi : ∀ n, Integrable (f n) := fun n =>
    (integrable_kernel_log_sub hq hqc (1 / 2 + s) (Real.log n)).const_mul (c n)
  have hfint : ∀ n, ∫ a, f n a =
      c n * (Real.exp (-(1 / 2 + s) * Real.log n) * ∫ u, q u * Real.exp ((1 / 2 + s) * u)) := by
    intro n
    simp only [hf]
    rw [integral_const_mul, integral_kernel_log_sub]
  have hfn : ∀ n, ∫ a, ‖f n a‖ = |c n| * (Real.exp (-(1 / 2 + s) * Real.log n) *
      ∫ u, |q u| * Real.exp ((1 / 2 + s) * u)) := by
    intro n
    have e : (fun a => ‖f n a‖) = fun a => |c n| * (|q (Real.log n - a)| *
        Real.exp (-(1 / 2 + s) * a)) := by
      funext a
      simp only [hf, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [e, integral_const_mul, integral_kernel_log_sub (fun u => |q u|)]
  have hsum : Summable fun n => ∫ a, ‖f n a‖ :=
    ((summable_abs_coeff_mul_exp hsl hs).mul_right
      (∫ u, |q u| * Real.exp ((1 / 2 + s) * u))).congr fun n => by rw [hfn n]; ring
  have hint := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hfi hsum
  have hS : (fun a => windowKernelSum lam q a * Real.exp (-(1 / 2 + s) * a)) =
      fun a => ∑' n, f n a := by
    funext a
    unfold windowKernelSum
    rw [← tsum_mul_right]
    refine tsum_congr fun n => ?_
    simp only [hf, hc]
    ring
  refine ⟨by rw [hS]; exact hint, ?_⟩
  rw [hS, ← integral_tsum_of_summable_integral_norm hfi hsum]
  calc ∑' n, ∫ a, f n a
      = ∑' n : ℕ, (if 2 ≤ n then lam n else 0) / (n : ℝ) ^ (1 + s) *
          ∫ u, q u * Real.exp ((1 / 2 + s) * u) :=
        tsum_congr fun n => by rw [hfint n, ← coeff_mul_exp_eq lam s n]; ring
    _ = (∫ u, q u * Real.exp ((1 / 2 + s) * u)) * oddDirichlet lam s := by
        rw [tsum_mul_right]; unfold oddDirichlet; exact mul_comm _ _

theorem kernelSum_eq_zero_of_le (lam : ℕ → ℝ) {q : ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hq : ∀ u, D < |u| → q u = 0) {a : ℝ} (ha : a ≤ -D) : windowKernelSum lam q a = 0 := by
  unfold windowKernelSum
  refine (tsum_congr fun n => ?_).trans tsum_zero
  split_ifs with hn
  · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    rw [hq _ (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
  · rw [zero_mul]

/-! ## The cross kernel -/

theorem continuous_farCrossKernel {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) : Continuous (farCrossKernel g) := by
  have h2 : ContDiff ℝ 2 fun u => (g u : ℂ) := contDiff_ofReal_comp hg
  have hφ : Continuous fun u => (farBump u : ℂ) :=
    Complex.continuous_ofReal.comp continuous_farBump
  have hw := (EF.weilTest_contDiff h2 hφ (hgc.comp_left Complex.ofReal_zero)).continuous
  have e : farCrossKernel g = fun u => (EF.weilTest (fun u => (g u : ℂ))
      (fun u => (farBump u : ℂ)) u).re := by
    funext u; rw [weilTest_ofReal_ofReal_eq, Complex.ofReal_re]; rfl
  rw [e]
  exact Complex.continuous_re.comp hw

theorem hasCompactSupport_farCrossKernel {g : ℝ → ℝ} {R : ℝ} (hgs : ∀ x, R < |x| → g x = 0) :
    HasCompactSupport (farCrossKernel g) :=
  hasCompactSupport_of_abs_gt_eq_zero (R := R + 1) fun _ hy => farCrossKernel_eq_zero hgs hy

/-- `H(s) = ∫ h(u) e^{(1/2+s)u} du` for the cross kernel `h = g ⋆ φ̃`. -/
def farCrossLaplace (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ u, farCrossKernel g u * Real.exp ((1 / 2 + s) * u)

/-- `H(0) = P J`: the transform of a cross-correlation at `−i/2` is `ĝ(−i/2) φ̂(i/2)`. -/
theorem farCrossLaplace_zero {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hge : ∀ x, g (-x) = g x) :
    farCrossLaplace g 0 = (∫ x, g x * Real.exp (-x / 2)) * farJ := by
  have hc : Continuous fun u => (g u : ℂ) := Complex.continuous_ofReal.comp hg
  have hcs : HasCompactSupport fun u => (g u : ℂ) := hgc.comp_left Complex.ofReal_zero
  have hφ : Continuous fun u => (farBump u : ℂ) :=
    Complex.continuous_ofReal.comp continuous_farBump
  have hφs : HasCompactSupport fun u => (farBump u : ℂ) :=
    hasCompactSupport_farBump.comp_left Complex.ofReal_zero
  have hk : EF.weilTest (fun u => (g u : ℂ)) (fun u => (farBump u : ℂ)) =
      fun u => (farCrossKernel g u : ℂ) := by
    funext u; rw [weilTest_ofReal_ofReal_eq]; rfl
  have h1 := EF.paperFT_weilTest hc hφ hcs hφs (-I / 2)
  rw [hk, conj_neg_I_div_two, paperFT_ofRealFun_neg_I_div_two, paperFT_ofRealFun_neg_I_div_two,
    paperFT_ofRealFun_I_div_two, Complex.conj_ofReal] at h1
  have hP : ∫ u, g u * Real.exp (u / 2) = ∫ u, g u * Real.exp (-u / 2) := by
    rw [← integral_neg_eq_self (fun u => g u * Real.exp (u / 2))]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show g (-u) * Real.exp (-u / 2) = g u * Real.exp (-u / 2)
    rw [hge]
  rw [hP] at h1
  have h3 : ∫ u, farCrossKernel g u * Real.exp (u / 2) =
      (∫ u, g u * Real.exp (-u / 2)) * ∫ u, farBump u * Real.exp (-u / 2) := by
    exact_mod_cast h1
  unfold farCrossLaplace
  rw [show (∫ x, g x * Real.exp (-x / 2)) * farJ =
    (∫ u, g u * Real.exp (-u / 2)) * ∫ u, farBump u * Real.exp (-u / 2) from rfl, ← h3]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show farCrossKernel g u * Real.exp ((1 / 2 + 0) * u) = farCrossKernel g u * Real.exp (u / 2)
  rw [show (1 / 2 + 0 : ℝ) * u = u / 2 by ring]

theorem abs_exp_sub_one_le_mul_exp (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_total 0 x with hx | hx
  · have h := Real.add_one_le_exp (-x)
    have hpos := Real.exp_pos x
    have h1 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [abs_of_nonneg (by linarith [Real.add_one_le_exp x]), abs_of_nonneg hx]
    nlinarith
  · have h := Real.add_one_le_exp x
    have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
    rw [abs_of_nonpos (by linarith), abs_of_nonpos hx]
    have : 1 ≤ Real.exp (-x) := Real.one_le_exp_iff.mpr (by linarith)
    nlinarith

/-- `|H(s) − H(0)| ≤ s · (R + 1) e^{R+1} ∫ |h(u)| e^{u/2} du` for `0 ≤ s ≤ 1`. -/
theorem abs_farCrossLaplace_sub_le {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R)
    (hgs : ∀ x, R < |x| → g x = 0) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |farCrossLaplace g s - farCrossLaplace g 0| ≤
      s * (R + 1) * Real.exp (R + 1) * ∫ u, |farCrossKernel g u| * Real.exp (u / 2) := by
  have hgc := hasCompactSupport_of_abs_gt_eq_zero hgs
  have hh := continuous_farCrossKernel hg hgc
  have hhc := hasCompactSupport_farCrossKernel hgs
  have hi : ∀ μ : ℝ, Integrable fun u => farCrossKernel g u * Real.exp (μ * u) := fun μ =>
    (hh.mul (by fun_prop)).integrable_of_hasCompactSupport hhc.mul_right
  have hia : Integrable fun u => |farCrossKernel g u| * Real.exp (u / 2) :=
    (hh.abs.mul (by fun_prop)).integrable_of_hasCompactSupport hhc.abs.mul_right
  have hd : Integrable fun u => farCrossKernel g u * Real.exp ((1 / 2 + s) * u) -
      farCrossKernel g u * Real.exp ((1 / 2 + 0) * u) := (hi _).sub (hi _)
  unfold farCrossLaplace
  rw [← integral_sub (hi _) (hi _), ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono hd.abs
    (hia.const_mul _) fun u => ?_)
  show |farCrossKernel g u * Real.exp ((1 / 2 + s) * u) -
      farCrossKernel g u * Real.exp ((1 / 2 + 0) * u)| ≤
    s * (R + 1) * Real.exp (R + 1) * (|farCrossKernel g u| * Real.exp (u / 2))
  rcases le_or_gt |u| (R + 1) with hu | hu
  · have e : farCrossKernel g u * Real.exp ((1 / 2 + s) * u) -
        farCrossKernel g u * Real.exp ((1 / 2 + 0) * u) =
        farCrossKernel g u * Real.exp (u / 2) * (Real.exp (s * u) - 1) := by
      rw [mul_sub, mul_one, mul_assoc, ← Real.exp_add]
      ring_nf
    rw [e, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 := abs_exp_sub_one_le_mul_exp (s * u)
    have h2 : |s * u| ≤ s * (R + 1) := by
      rw [abs_mul, abs_of_nonneg hs0]; exact mul_le_mul_of_nonneg_left hu hs0
    have h3 : Real.exp |s * u| ≤ Real.exp (R + 1) := Real.exp_le_exp.mpr (by nlinarith)
    have h4 : |Real.exp (s * u) - 1| ≤ s * (R + 1) * Real.exp (R + 1) :=
      h1.trans (mul_le_mul h2 h3 (Real.exp_pos _).le (by positivity))
    have h5 : 0 ≤ |farCrossKernel g u| * Real.exp (u / 2) := by positivity
    calc |farCrossKernel g u| * Real.exp (u / 2) * |Real.exp (s * u) - 1|
        ≤ |farCrossKernel g u| * Real.exp (u / 2) * (s * (R + 1) * Real.exp (R + 1)) :=
          mul_le_mul_of_nonneg_left h4 h5
      _ = _ := by ring
  · rw [farCrossKernel_eq_zero hgs hu]; simp

/-- `K(σ) ≥ e^{−σ/6} K(0)`. -/
theorem farLaplace_ge {σ : ℝ} (hσ : 0 ≤ σ) :
    Real.exp (-(σ / 6)) * farLaplace 0 ≤ farLaplace σ := by
  unfold farLaplace
  rw [← integral_const_mul]
  refine integral_mono ((integrable_farKernel_mul_exp _).const_mul _)
    (integrable_farKernel_mul_exp _) fun u => ?_
  show Real.exp (-(σ / 6)) * (farKernel u * Real.exp ((1 / 2 + 0) * u)) ≤
    farKernel u * Real.exp ((1 / 2 + σ) * u)
  have hk := farKernel_nonneg u
  rcases le_or_gt (2 * (nodeBump 2).rOut) |u| with hu | hu
  · rw [farKernel_eq_zero hu]; simp
  · have hr := nodeBump_rOut_le 2
    have hu6 : -(1 / 6) ≤ u := by have := neg_abs_le u; linarith
    have he : Real.exp (-(σ / 6)) * Real.exp ((1 / 2 + 0) * u) ≤ Real.exp ((1 / 2 + σ) * u) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    calc Real.exp (-(σ / 6)) * (farKernel u * Real.exp ((1 / 2 + 0) * u))
        = farKernel u * (Real.exp (-(σ / 6)) * Real.exp ((1 / 2 + 0) * u)) := by ring
      _ ≤ farKernel u * Real.exp ((1 / 2 + σ) * u) := mul_le_mul_of_nonneg_left he hk

/-- `|K(σ) − J²| ≤ (σ/3) J²` for `0 ≤ σ ≤ 1`. -/
theorem abs_farLaplace_sub_le {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    |farLaplace σ - farJ ^ 2| ≤ σ / 3 * farJ ^ 2 := by
  have hup := farLaplace_le hσ0
  have hlo := farLaplace_ge hσ0
  rw [farLaplace_zero] at hup hlo
  have hJ := sq_nonneg farJ
  have h1 : Real.exp (σ / 6) ≤ 1 + σ / 3 := by
    have h := Real.add_one_le_exp (-(σ / 6))
    have hpos := Real.exp_pos (σ / 6)
    have hm : Real.exp (σ / 6) * Real.exp (-(σ / 6)) = 1 := by rw [← Real.exp_add]; simp
    have h2 : Real.exp (σ / 6) ≤ 2 := by
      have := Real.exp_le_exp.mpr (show σ / 6 ≤ 1 / 2 by linarith)
      have h3 : Real.exp (1 / 2) ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h4 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
      linarith
    nlinarith
  have h2 : 1 - σ / 6 ≤ Real.exp (-(σ / 6)) := by linarith [Real.add_one_le_exp (-(σ / 6))]
  rw [abs_le]
  constructor <;> nlinarith

/-! ## Integrals over a left half-line -/

/-- If `f(a) e^{−μ₀ a}` is integrable and `f` vanishes left of `−D`, then for `0 ≤ μ ≤ 2` the
integral of `f(a) e^{−μ a}` over `(−∞, a₀)` is bounded uniformly in `μ`. -/
theorem abs_setIntegral_Iio_mul_exp_le {f : ℝ → ℝ} {μ₀ : ℝ} (hμ₀ : 0 ≤ μ₀) (hμ₀2 : μ₀ ≤ 2)
    (hf : Integrable fun a => f a * Real.exp (-μ₀ * a)) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ a, a < -D → f a = 0) (a₀ : ℝ) {μ : ℝ} (hμ : 0 ≤ μ) (hμ2 : μ ≤ 2) :
    IntegrableOn (fun a => f a * Real.exp (-μ * a)) (Iio a₀) ∧
      |∫ a in Iio a₀, f a * Real.exp (-μ * a)| ≤
        Real.exp (2 * D + 2 * |a₀|) * ∫ a, |f a * Real.exp (-μ₀ * a)| := by
  have hpt : ∀ a ∈ Iio a₀, |f a * Real.exp (-μ * a)| ≤
      Real.exp (2 * D + 2 * |a₀|) * |f a * Real.exp (-μ₀ * a)| := by
    intro a ha
    have ha' : a < a₀ := ha
    rcases lt_or_ge a (-D) with h | h
    · rw [hfD a h]; simp
    · have e : f a * Real.exp (-μ * a) = f a * Real.exp (-μ₀ * a) * Real.exp ((μ₀ - μ) * a) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
      rw [e, abs_mul (f a * Real.exp (-μ₀ * a)), abs_of_pos (Real.exp_pos _), mul_comm]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
      have h1 : a ≤ |a₀| := ha'.le.trans (le_abs_self a₀)
      have h2 : -D ≤ a := h
      rcases le_total 0 a with ha0 | ha0
      · nlinarith [abs_nonneg a₀]
      · nlinarith [abs_nonneg a₀]
  have hmeas : AEStronglyMeasurable (fun a => f a * Real.exp (-μ * a))
      (volume.restrict (Iio a₀)) := by
    have : (fun a => f a * Real.exp (-μ * a)) =
        fun a => f a * Real.exp (-μ₀ * a) * Real.exp ((μ₀ - μ) * a) := by
      funext a; rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [this]
    exact (hf.aestronglyMeasurable.mul (by fun_prop : Continuous fun a : ℝ =>
      Real.exp ((μ₀ - μ) * a)).aestronglyMeasurable).restrict
  have hdom : IntegrableOn (fun a => Real.exp (2 * D + 2 * |a₀|) * |f a * Real.exp (-μ₀ * a)|)
      (Iio a₀) := (hf.abs.const_mul _).integrableOn
  have hint : IntegrableOn (fun a => f a * Real.exp (-μ * a)) (Iio a₀) :=
    hdom.mono' hmeas ((ae_restrict_iff' measurableSet_Iio).mpr
      (Eventually.of_forall fun a ha => by rw [Real.norm_eq_abs]; exact hpt a ha))
  refine ⟨hint, ?_⟩
  calc |∫ a in Iio a₀, f a * Real.exp (-μ * a)|
      ≤ ∫ a in Iio a₀, |f a * Real.exp (-μ * a)| := abs_integral_le_integral_abs
    _ ≤ ∫ a in Iio a₀, Real.exp (2 * D + 2 * |a₀|) * |f a * Real.exp (-μ₀ * a)| :=
        setIntegral_mono_on hint.abs hdom measurableSet_Iio hpt
    _ ≤ ∫ a, Real.exp (2 * D + 2 * |a₀|) * |f a * Real.exp (-μ₀ * a)| :=
        setIntegral_le_integral (hf.abs.const_mul _) (Eventually.of_forall fun a => by positivity)
    _ = Real.exp (2 * D + 2 * |a₀|) * ∫ a, |f a * Real.exp (-μ₀ * a)| := integral_const_mul _ _

end RHTower.EvenSector

end
