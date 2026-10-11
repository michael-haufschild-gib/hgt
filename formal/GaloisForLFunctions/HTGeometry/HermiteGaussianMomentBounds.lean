import GaloisForLFunctions.RHTower.HermiteGaussianEnvelope
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exponential moments of Hermite–Gaussians and two-sided Hermite bounds

Let `He_n` be the probabilists' Hermite polynomials (`Polynomial.hermite`) and
`g_n(x) = He_n(x) e^{−x²/2}`.

**Exponential moments** (`integral_exp_mul_hermiteGauss`).  For all real `r`,

  `∫ e^{rx} g_n(x) dx = √(2π) · rⁿ · e^{r²/2}`.

Proof: `g_{n+1} = −g_n'` (`hasDerivAt_hermiteGauss`, from `He_{n+1} = X He_n − He_n'`), so
integration by parts on `ℝ` gives `∫ e^{rx} g_{n+1} = r ∫ e^{rx} g_n`; the case `n = 0` is the
Gaussian integral after completing the square.

**Three-term recurrence** (`aeval_hermite_add_two`).  `He_{n+2}(x) = x He_{n+1}(x) − (n+1) He_n(x)`,
from `He_{n+1}' = (n+1) He_n` (`derivative_hermite_add_one`).

**Two-sided bounds.**  For `k ≤ n`:

* beyond `2√n` the Hermite polynomial dominates a power: `(x/2)^k ≤ He_k(x)` for `x ≥ 2√n`
  (`pow_half_le_aeval_hermite`);
* everywhere `|He_k(x)| ≤ (|x| + 2√n)^k` (`abs_aeval_hermite_le`).

Both follow from the recurrence by induction: `He_{k+1} ≥ (x − 2k/x) He_k ≥ (x/2) He_k` when
`x² ≥ 4k`, and `|x| A^k + k A^{k−1} ≤ A^{k+1}` when `A = |x| + 2√n`.
-/

open Polynomial MeasureTheory Filter Topology Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `He_{n+1}' = (n+1) He_n`. -/
theorem derivative_hermite_add_one (n : ℕ) :
    derivative (hermite (n + 1)) = ((n : ℤ[X]) + 1) * hermite n := by
  induction n with
  | zero => simp [hermite_zero]
  | succ n ih =>
    rw [hermite_succ (n + 1), derivative_sub, derivative_mul, derivative_X, one_mul, ih,
      hermite_succ n]
    have h2 : derivative (((n : ℤ[X]) + 1) * hermite n) = ((n : ℤ[X]) + 1) * derivative (hermite n) := by
      rw [derivative_mul]
      simp
    rw [h2]
    push_cast
    ring

/-- `aeval x He_{n+1}' = (n+1) · aeval x He_n` over `ℝ`. -/
theorem aeval_derivative_hermite_add_one (n : ℕ) (x : ℝ) :
    aeval x (derivative (hermite (n + 1))) = ((n : ℝ) + 1) * aeval x (hermite n) := by
  rw [derivative_hermite_add_one]
  simp

/-- **Three-term recurrence** `He_{n+2}(x) = x He_{n+1}(x) − (n+1) He_n(x)`. -/
theorem aeval_hermite_add_two (n : ℕ) (x : ℝ) :
    aeval x (hermite (n + 2)) = x * aeval x (hermite (n + 1)) - ((n : ℝ) + 1) * aeval x (hermite n) := by
  rw [hermite_succ (n + 1), map_sub, map_mul, aeval_X, aeval_derivative_hermite_add_one]

/-- **Lower bound beyond `2√n`.**  For `k ≤ n` and `x ≥ 2√n`, `(x/2)^k ≤ He_k(x)`, and
`(x/2) He_k(x) ≤ He_{k+1}(x)` for `k + 1 ≤ n`. -/
theorem pow_half_le_aeval_hermite {n : ℕ} {x : ℝ} (hx : 2 * Real.sqrt n ≤ x) :
    ∀ k ≤ n, (x / 2) ^ k ≤ aeval x (hermite k) ∧
      (k + 1 ≤ n → x / 2 * aeval x (hermite k) ≤ aeval x (hermite (k + 1))) := by
  have hx0 : 0 ≤ x := le_trans (by positivity) hx
  have hxsq : (n : ℝ) * 4 ≤ x ^ 2 := by
    have h := mul_self_le_mul_self (by positivity) hx
    have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
    nlinarith
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp [hermite_zero], fun _ => ?_⟩
    simp [hermite_zero]
    linarith
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hstep := ih2 hk
    refine ⟨?_, fun hk2 => ?_⟩
    · calc (x / 2) ^ (k + 1) = x / 2 * (x / 2) ^ k := by ring
        _ ≤ x / 2 * aeval x (hermite k) := mul_le_mul_of_nonneg_left ih1 (by positivity)
        _ ≤ _ := hstep
    · rw [aeval_hermite_add_two]
      have hk0 : 0 ≤ aeval x (hermite k) := le_trans (by positivity) ih1
      have hk1 : 0 ≤ aeval x (hermite (k + 1)) := le_trans (mul_nonneg (by positivity) hk0) hstep
      have hkn : ((k : ℝ) + 1) * 4 ≤ x ^ 2 := by
        have : ((k : ℝ) + 1) ≤ n := by exact_mod_cast (by omega : k + 1 ≤ n)
        nlinarith
      have hA := mul_le_mul_of_nonneg_left hstep hx0
      have hB := mul_le_mul_of_nonneg_right hkn hk0
      nlinarith

/-- **Upper bound.**  For `k ≤ n`, `|He_k(x)| ≤ (|x| + 2√n)^k`. -/
theorem abs_aeval_hermite_le {n : ℕ} (x : ℝ) :
    ∀ k ≤ n, |aeval x (hermite k)| ≤ (|x| + 2 * Real.sqrt n) ^ k ∧
      (k + 1 ≤ n → |aeval x (hermite (k + 1))| ≤ (|x| + 2 * Real.sqrt n) ^ (k + 1)) := by
  set A := |x| + 2 * Real.sqrt n with hA
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := by positivity
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp [hermite_zero], fun _ => ?_⟩
    simp only [hermite_one, aeval_X, zero_add, pow_one, hA]
    linarith
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hk1 := ih2 hk
    refine ⟨hk1, fun hk2 => ?_⟩
    rw [aeval_hermite_add_two]
    have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : k + 1 ≤ n)
    have hkey : |x| * A ^ (k + 1) + ((k : ℝ) + 1) * A ^ k ≤ A ^ (k + 2) := by
      have h4 : ((k : ℝ) + 1) ≤ A * (2 * Real.sqrt n) := by
        have : 2 * Real.sqrt n ≤ A := by rw [hA]; linarith [abs_nonneg x]
        nlinarith
      have hAk : 0 ≤ A ^ k := pow_nonneg hA0 k
      calc |x| * A ^ (k + 1) + ((k : ℝ) + 1) * A ^ k
          ≤ |x| * A ^ (k + 1) + A * (2 * Real.sqrt n) * A ^ k := by
            linarith [mul_le_mul_of_nonneg_right h4 hAk]
        _ = A ^ k * A * (|x| + 2 * Real.sqrt n) := by ring
        _ = A ^ (k + 2) := by rw [← hA]; ring
    calc |x * aeval x (hermite (k + 1)) - ((k : ℝ) + 1) * aeval x (hermite k)|
        ≤ |x| * |aeval x (hermite (k + 1))| + ((k : ℝ) + 1) * |aeval x (hermite k)| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
      _ ≤ |x| * A ^ (k + 1) + ((k : ℝ) + 1) * A ^ k := by
          gcongr
      _ ≤ A ^ (k + 2) := hkey

/-- The Hermite–Gaussian `g_n(x) = He_n(x) e^{−x²/2}`. -/
def hermiteGauss (n : ℕ) (x : ℝ) : ℝ :=
  aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))

/-- `g_n' = −g_{n+1}`. -/
theorem hasDerivAt_hermiteGauss (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteGauss n) (-hermiteGauss (n + 1) x) x := by
  have h1 : HasDerivAt (fun y => aeval y (hermite n)) (aeval x (derivative (hermite n))) x := by
    simpa using (hermite n).hasDerivAt_aeval x
  have h2 := ((hasDerivAt_pow 2 x).const_mul (-(1 / 2 : ℝ))).exp
  have hfun : hermiteGauss n = fun y => aeval y (hermite n) * Real.exp (-(1 / 2) * y ^ 2) := by
    funext y
    unfold hermiteGauss
    congr 2
    ring
  rw [hfun]
  refine (h1.mul h2).congr_deriv ?_
  rw [hermiteGauss, hermite_succ, map_sub, map_mul, aeval_X,
    show -(x ^ 2 / 2) = -(1 / 2) * x ^ 2 by ring]
  push_cast
  ring

theorem exp_mul_le_exp_sq_add (r x : ℝ) : Real.exp (r * x) ≤ Real.exp (r ^ 2) * Real.exp (x ^ 2 / 4) := by
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (x / 2 - r)])

/-- `x ↦ e^{rx} P(x) e^{−x²/2}` is integrable for every polynomial `P`. -/
theorem integrable_exp_mul_poly_gauss (r : ℝ) (P : ℝ[X]) :
    Integrable fun x : ℝ => Real.exp (r * x) * (P.eval x * Real.exp (-(x ^ 2 / 2))) := by
  have hg := (RHTower.integrable_polyEval_mul_gauss P (b := 1 / 4) (by norm_num)).norm.const_mul
    (Real.exp (r ^ 2))
  refine hg.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp]
  have h1 := exp_mul_le_exp_sq_add r x
  have h2 : Real.exp (x ^ 2 / 4) * Real.exp (-(x ^ 2 / 2)) = Real.exp (-(1 / 4 * x ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (r * x) * (|P.eval x| * Real.exp (-(x ^ 2 / 2)))
      ≤ Real.exp (r ^ 2) * Real.exp (x ^ 2 / 4) * (|P.eval x| * Real.exp (-(x ^ 2 / 2))) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = Real.exp (r ^ 2) * (|P.eval x| * Real.exp (-(1 / 4 * x ^ 2))) := by rw [← h2]; ring

theorem integrable_exp_mul_hermiteGauss (r : ℝ) (n : ℕ) :
    Integrable fun x : ℝ => Real.exp (r * x) * hermiteGauss n x := by
  have h := integrable_exp_mul_poly_gauss r (Polynomial.map (Int.castRingHom ℝ) (hermite n))
  refine h.congr (Eventually.of_forall fun x => ?_)
  beta_reduce
  unfold hermiteGauss
  rw [eval_map, aeval_def, algebraMap_int_eq]

/-- The Gaussian exponential moment `∫ e^{rx} e^{−x²/2} dx = √(2π) e^{r²/2}`. -/
theorem integral_exp_mul_gauss (r : ℝ) :
    ∫ x : ℝ, Real.exp (r * x) * Real.exp (-(x ^ 2 / 2)) = Real.sqrt (2 * Real.pi) * Real.exp (r ^ 2 / 2) := by
  have e : ∀ x : ℝ, Real.exp (r * x) * Real.exp (-(x ^ 2 / 2)) =
      Real.exp (r ^ 2 / 2) * Real.exp (-(1 / 2) * (x - r) ^ 2) := by
    intro x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [e]
  have hshift := integral_sub_right_eq_self (μ := volume) (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) r
  rw [integral_const_mul, hshift, integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi by ring]
  ring

/-- **Exponential moments of the Hermite–Gaussians.**  `∫ e^{rx} He_n(x) e^{−x²/2} dx =
√(2π) rⁿ e^{r²/2}`. -/
theorem integral_exp_mul_hermiteGauss (r : ℝ) (n : ℕ) :
    ∫ x : ℝ, Real.exp (r * x) * hermiteGauss n x =
      Real.sqrt (2 * Real.pi) * r ^ n * Real.exp (r ^ 2 / 2) := by
  induction n with
  | zero =>
    have h0 : ∀ x : ℝ, hermiteGauss 0 x = Real.exp (-(x ^ 2 / 2)) := by
      intro x
      simp [hermiteGauss, hermite_zero]
    simp_rw [h0]
    rw [integral_exp_mul_gauss]
    ring
  | succ n ih =>
    have hu : ∀ x ∈ tsupport (hermiteGauss n),
        HasDerivAt (fun y => Real.exp (r * y)) (r * Real.exp (r * x)) x := by
      intro x _
      have := ((hasDerivAt_id x).const_mul r).exp
      simpa [mul_comm] using this
    have hv : ∀ x ∈ tsupport (fun y => Real.exp (r * y)),
        HasDerivAt (hermiteGauss n) (-hermiteGauss (n + 1) x) x :=
      fun x _ => hasDerivAt_hermiteGauss n x
    have h1 : Integrable ((fun y => Real.exp (r * y)) * fun x => -hermiteGauss (n + 1) x) := by
      have := (integrable_exp_mul_hermiteGauss r (n + 1)).neg
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp [Pi.mul_apply]
    have h2 : Integrable ((fun x => r * Real.exp (r * x)) * hermiteGauss n) := by
      have := (integrable_exp_mul_hermiteGauss r n).const_mul r
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]
      ring
    have h3 : Integrable ((fun y => Real.exp (r * y)) * hermiteGauss n) :=
      integrable_exp_mul_hermiteGauss r n
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable hu hv h1 h2 h3
    have e1 : ∫ x : ℝ, Real.exp (r * x) * hermiteGauss (n + 1) x =
        -∫ x : ℝ, Real.exp (r * x) * -hermiteGauss (n + 1) x := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    rw [e1, hibp, neg_neg]
    have e2 : ∫ x : ℝ, r * Real.exp (r * x) * hermiteGauss n x =
        r * ∫ x : ℝ, Real.exp (r * x) * hermiteGauss n x := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [e2, ih]
    ring

end

end GaloisForLFunctions.HTGeometry
