import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The derivatives of a Gaussian are polynomials times the Gaussian

Writing `g_t(x) = e^{-x²/(4t)}`, one has `g_t' = -(x/(2t)) g_t`, so every derivative of `g_t` is a
polynomial times `g_t`, with the polynomial obeying the recursion

`q_{k+1} = q_k' - (X/(2t)) q_k`,   `q_0 = 1`.

The recursion raises the degree by at most one and the inverse power of `t` by at most one, so for
`0 < t ≤ 1` every coefficient of `q_k` is bounded by an absolute constant times `t^{-k}`, and hence

`|q_k(ξ)| ≤ (k+1) C_k t^{-k} (1 + |ξ|^k)`.

This is the polynomial factor that appears in every fixed-degree Gaussian jet.
-/

open Polynomial

namespace RHTower

noncomputable section

/-! ## The jet polynomials -/

/-- The polynomial factor in the `k`-th derivative of `e^{-x²/(4t)}`. -/
noncomputable def gaussJetPoly (t : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | (k + 1) => (gaussJetPoly t k).derivative
      - Polynomial.C (1 / (2 * t)) * Polynomial.X * gaussJetPoly t k

@[simp]
theorem gaussJetPoly_zero (t : ℝ) : gaussJetPoly t 0 = 1 := rfl

theorem gaussJetPoly_succ (t : ℝ) (k : ℕ) :
    gaussJetPoly t (k + 1) = (gaussJetPoly t k).derivative
      - Polynomial.C (1 / (2 * t)) * Polynomial.X * gaussJetPoly t k := rfl

/-- **Every derivative of the Gaussian is its jet polynomial times the Gaussian.** -/
theorem hasDerivAt_gaussJet {t : ℝ} (ht : t ≠ 0) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (gaussJetPoly t k).eval y * Real.exp (-(y ^ 2 / (4 * t))))
      ((gaussJetPoly t (k + 1)).eval x * Real.exp (-(x ^ 2 / (4 * t)))) x := by
  have hpoly : HasDerivAt (fun y : ℝ => (gaussJetPoly t k).eval y)
      ((gaussJetPoly t k).derivative.eval x) x := (gaussJetPoly t k).hasDerivAt x
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hsq : HasDerivAt (fun y : ℝ => -(y ^ 2 / (4 * t))) (-(2 * x / (4 * t))) x :=
    (h1.div_const (4 * t)).neg
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / (4 * t))))
      (Real.exp (-(x ^ 2 / (4 * t))) * -(2 * x / (4 * t))) x := hsq.exp
  have hprod := hpoly.mul hexp
  refine hprod.congr_deriv ?_
  rw [gaussJetPoly_succ]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  field_simp
  ring

/-! ## Degree and coefficient bounds -/

theorem gaussJetPoly_natDegree_le (t : ℝ) : ∀ k : ℕ, (gaussJetPoly t k).natDegree ≤ k
  | 0 => by simp
  | (k + 1) => by
    rw [gaussJetPoly_succ]
    refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
    refine max_le ?_ ?_
    · refine le_trans (Polynomial.natDegree_derivative_le _) ?_
      have := gaussJetPoly_natDegree_le t k
      omega
    · refine le_trans Polynomial.natDegree_mul_le ?_
      have h1 : (Polynomial.C (1 / (2 * t)) * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := by
        refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
        simp
      have h2 := gaussJetPoly_natDegree_le t k
      omega

theorem gaussJetPoly_coeff_eq_zero {t : ℝ} {k j : ℕ} (h : k < j) :
    (gaussJetPoly t k).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (gaussJetPoly_natDegree_le t k) h)

/-- The absolute constant in the coefficient bound. -/
noncomputable def gaussJetConst : ℕ → ℝ
  | 0 => 1
  | (k + 1) => (k : ℝ) * gaussJetConst k + gaussJetConst k / 2

theorem gaussJetConst_pos : ∀ k : ℕ, 0 < gaussJetConst k
  | 0 => by norm_num [gaussJetConst]
  | (k + 1) => by
    have h := gaussJetConst_pos k
    rw [gaussJetConst]
    positivity

/-- **The coefficient bound.** -/
theorem gaussJetPoly_coeff_bound {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∀ (k j : ℕ), |(gaussJetPoly t k).coeff j| ≤ gaussJetConst k * (t ^ k)⁻¹
  | 0, j => by
    rw [gaussJetPoly_zero, gaussJetConst, pow_zero, inv_one, mul_one]
    rcases eq_or_ne j 0 with hj | hj
    · simp [hj]
    · simp [Polynomial.coeff_one, hj]
  | (k + 1), j => by
    have hind := gaussJetPoly_coeff_bound ht0 ht1 k
    have hCk : 0 < gaussJetConst k := gaussJetConst_pos k
    have htpow : (0 : ℝ) < t ^ k := by positivity
    have htpow1 : (0 : ℝ) < t ^ (k + 1) := by positivity
    have hple : t ^ (k + 1) ≤ t ^ k := by
      rw [pow_succ]
      nlinarith [htpow]
    have hmono : (t ^ k)⁻¹ ≤ (t ^ (k + 1))⁻¹ := by
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le htpow1 hple
    have hfirst : |(gaussJetPoly t k).derivative.coeff j|
        ≤ (k : ℝ) * gaussJetConst k * (t ^ k)⁻¹ := by
      rw [Polynomial.coeff_derivative, abs_mul]
      by_cases hjk : k < j + 1
      · rw [gaussJetPoly_coeff_eq_zero hjk, abs_zero, zero_mul]
        positivity
      · have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) := by
          have h : j + 1 ≤ k := by omega
          exact_mod_cast h
        have habs : |((j : ℝ) + 1)| = (j : ℝ) + 1 := abs_of_nonneg (by positivity)
        have hcast : |((j : ℕ) : ℝ) + 1| = (j : ℝ) + 1 := habs
        have hstep := hind (j + 1)
        have hnn : (0 : ℝ) ≤ |(gaussJetPoly t k).coeff (j + 1)| := abs_nonneg _
        calc |(gaussJetPoly t k).coeff (j + 1)| * |((j : ℕ) : ℝ) + 1|
            = |(gaussJetPoly t k).coeff (j + 1)| * ((j : ℝ) + 1) := by rw [hcast]
          _ ≤ (gaussJetConst k * (t ^ k)⁻¹) * (k : ℝ) :=
              mul_le_mul hstep hjk' (by positivity) (by positivity)
          _ = (k : ℝ) * gaussJetConst k * (t ^ k)⁻¹ := by ring
    have hshift : |(Polynomial.C (1 / (2 * t)) * Polynomial.X * gaussJetPoly t k).coeff j|
        ≤ gaussJetConst k / 2 * (t ^ (k + 1))⁻¹ := by
      have hcoeff : (Polynomial.C (1 / (2 * t)) * Polynomial.X * gaussJetPoly t k).coeff j
          = (1 / (2 * t)) * ((Polynomial.X * gaussJetPoly t k).coeff j) := by
        rw [mul_assoc, Polynomial.coeff_C_mul]
      have hXbound : |(Polynomial.X * gaussJetPoly t k).coeff j|
          ≤ gaussJetConst k * (t ^ k)⁻¹ := by
        cases j with
        | zero =>
          rw [Polynomial.mul_coeff_zero]
          simp
          positivity
        | succ i =>
          rw [Polynomial.coeff_X_mul]
          exact hind i
      rw [hcoeff, abs_mul]
      have habsc : |(1 : ℝ) / (2 * t)| = 1 / (2 * t) := abs_of_pos (by positivity)
      rw [habsc]
      have hval : (1 / (2 * t)) * (gaussJetConst k * (t ^ k)⁻¹)
          = gaussJetConst k / 2 * (t ^ (k + 1))⁻¹ := by
        rw [pow_succ]
        field_simp
      calc 1 / (2 * t) * |(Polynomial.X * gaussJetPoly t k).coeff j|
          ≤ 1 / (2 * t) * (gaussJetConst k * (t ^ k)⁻¹) :=
            mul_le_mul_of_nonneg_left hXbound (by positivity)
        _ = gaussJetConst k / 2 * (t ^ (k + 1))⁻¹ := hval
    rw [gaussJetPoly_succ, Polynomial.coeff_sub, gaussJetConst]
    refine le_trans (abs_sub _ _) ?_
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hfirst' : (k : ℝ) * gaussJetConst k * (t ^ k)⁻¹
        ≤ (k : ℝ) * gaussJetConst k * (t ^ (k + 1))⁻¹ :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    have := le_trans hfirst hfirst'
    linarith [hshift, this]

/-- **The value bound.**  On `0 < t ≤ 1` the `k`-th jet polynomial is bounded by an absolute
constant times `t^{-k}(1 + |ξ|^k)`. -/
theorem abs_gaussJetPoly_eval_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (k : ℕ) (x : ℝ) :
    |(gaussJetPoly t k).eval x| ≤ ((k : ℝ) + 1) * gaussJetConst k * (t ^ k)⁻¹ * (1 + |x| ^ k) := by
  have hdeg : (gaussJetPoly t k).natDegree < k + 1 :=
    lt_of_le_of_lt (gaussJetPoly_natDegree_le t k) (Nat.lt_succ_self k)
  have heval : (gaussJetPoly t k).eval x
      = ∑ i ∈ Finset.range (k + 1), (gaussJetPoly t k).coeff i * x ^ i :=
    Polynomial.eval_eq_sum_range' hdeg x
  have hterm : ∀ i ∈ Finset.range (k + 1),
      |(gaussJetPoly t k).coeff i * x ^ i| ≤ gaussJetConst k * (t ^ k)⁻¹ * (1 + |x| ^ k) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hik : i ≤ k := by omega
    have hxi : |x| ^ i ≤ 1 + |x| ^ k := by
      by_cases hx : |x| ≤ 1
      · have : |x| ^ i ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
        have hk : (0 : ℝ) ≤ |x| ^ k := by positivity
        linarith
      · have hx1 : (1 : ℝ) ≤ |x| := le_of_lt (not_le.1 hx)
        have : |x| ^ i ≤ |x| ^ k := pow_le_pow_right₀ hx1 hik
        have hpos : (0 : ℝ) ≤ 1 := zero_le_one
        linarith
    have hc := gaussJetPoly_coeff_bound ht0 ht1 k i
    have hnn : (0 : ℝ) ≤ gaussJetConst k * (t ^ k)⁻¹ := by
      have := gaussJetConst_pos k
      positivity
    rw [abs_mul, abs_pow]
    exact mul_le_mul hc hxi (by positivity) hnn
  calc |(gaussJetPoly t k).eval x|
      = |∑ i ∈ Finset.range (k + 1), (gaussJetPoly t k).coeff i * x ^ i| := by rw [heval]
    _ ≤ ∑ i ∈ Finset.range (k + 1), |(gaussJetPoly t k).coeff i * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range (k + 1), gaussJetConst k * (t ^ k)⁻¹ * (1 + |x| ^ k) :=
        Finset.sum_le_sum hterm
    _ = ((k : ℝ) + 1) * gaussJetConst k * (t ^ k)⁻¹ * (1 + |x| ^ k) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ## The iterated derivatives of the Gaussian -/

/-- The Gaussian kernel `e^{-x²/(4t)}`. -/
def gaussKernel (t x : ℝ) : ℝ := Real.exp (-(x ^ 2 / (4 * t)))

theorem gaussKernel_pos (t x : ℝ) : 0 < gaussKernel t x := Real.exp_pos _

/-- **Every iterated derivative of the Gaussian is its jet polynomial times the Gaussian.** -/
theorem iteratedDeriv_gaussKernel {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    iteratedDeriv n (gaussKernel t) = fun x => (gaussJetPoly t n).eval x * gaussKernel t x := by
  induction n with
  | zero =>
    funext x
    rw [iteratedDeriv_zero, gaussJetPoly_zero]
    simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (hasDerivAt_gaussJet ht n x).deriv

/-! ## The uniform bound on a finite combination of even derivatives -/

theorem abs_pow_le_one_add_pow {k m : ℕ} (hkm : k ≤ m) (x : ℝ) : |x| ^ k ≤ 1 + |x| ^ m := by
  by_cases hx : |x| ≤ 1
  · have h1 : |x| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
    have h2 : (0 : ℝ) ≤ |x| ^ m := by positivity
    linarith
  · have hx1 : (1 : ℝ) ≤ |x| := le_of_lt (not_le.1 hx)
    have h1 : |x| ^ k ≤ |x| ^ m := pow_le_pow_right₀ hx1 hkm
    linarith

/-- The jet bound at a common degree and a common inverse power of `t`. -/
theorem abs_gaussJetPoly_eval_le' {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {k m : ℕ} (hkm : k ≤ m)
    (x : ℝ) :
    |(gaussJetPoly t k).eval x|
      ≤ 2 * (((k : ℝ) + 1) * gaussJetConst k) * (t ^ m)⁻¹ * (1 + |x| ^ m) := by
  have hbase := abs_gaussJetPoly_eval_le ht0 ht1 k x
  have hCk : 0 < gaussJetConst k := gaussJetConst_pos k
  have htk : (0 : ℝ) < t ^ k := by positivity
  have htm : (0 : ℝ) < t ^ m := by positivity
  have hple : t ^ m ≤ t ^ k := pow_le_pow_of_le_one ht0.le ht1 hkm
  have hmono : (t ^ k)⁻¹ ≤ (t ^ m)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le htm hple
  have hpow : 1 + |x| ^ k ≤ 2 * (1 + |x| ^ m) := by
    have := abs_pow_le_one_add_pow hkm x
    have h2 : (0 : ℝ) ≤ |x| ^ m := by positivity
    linarith
  have hA : (0 : ℝ) ≤ ((k : ℝ) + 1) * gaussJetConst k := by positivity
  calc |(gaussJetPoly t k).eval x|
      ≤ ((k : ℝ) + 1) * gaussJetConst k * (t ^ k)⁻¹ * (1 + |x| ^ k) := hbase
    _ ≤ ((k : ℝ) + 1) * gaussJetConst k * (t ^ m)⁻¹ * (2 * (1 + |x| ^ m)) := by
        have h1 : ((k : ℝ) + 1) * gaussJetConst k * (t ^ k)⁻¹
            ≤ ((k : ℝ) + 1) * gaussJetConst k * (t ^ m)⁻¹ :=
          mul_le_mul_of_nonneg_left hmono hA
        exact mul_le_mul h1 hpow (by positivity) (by positivity)
    _ = 2 * (((k : ℝ) + 1) * gaussJetConst k) * (t ^ m)⁻¹ * (1 + |x| ^ m) := by ring

/-- The absolute constant attached to a finite combination of even jets. -/
noncomputable def evenJetConst (m : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), |c k| * (2 * (2 * (k : ℝ) + 1) * gaussJetConst (2 * k))

theorem evenJetConst_nonneg (m : ℕ) (c : ℕ → ℝ) : 0 ≤ evenJetConst m c := by
  refine Finset.sum_nonneg fun k _ => ?_
  have := gaussJetConst_pos (2 * k)
  positivity

/-- A finite combination of even jet polynomials obeys the single power bound
`C (1+|x|^{2m}) t^{-2m}`. -/
theorem abs_evenJetCombination_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (m : ℕ) (c : ℕ → ℝ)
    (x : ℝ) :
    |∑ k ∈ Finset.range (m + 1), c k * (gaussJetPoly t (2 * k)).eval x|
      ≤ evenJetConst m c * (t ^ (2 * m))⁻¹ * (1 + |x| ^ (2 * m)) := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [evenJetConst, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hkm : 2 * k ≤ 2 * m := by omega
  have hstep := abs_gaussJetPoly_eval_le' ht0 ht1 hkm x
  have hcast : (((2 * k : ℕ) : ℝ) + 1) = 2 * (k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hstep
  rw [abs_mul]
  calc |c k| * |(gaussJetPoly t (2 * k)).eval x|
      ≤ |c k| * (2 * ((2 * (k : ℝ) + 1) * gaussJetConst (2 * k)) * (t ^ (2 * m))⁻¹
          * (1 + |x| ^ (2 * m))) :=
        mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
    _ = |c k| * (2 * (2 * (k : ℝ) + 1) * gaussJetConst (2 * k)) * (t ^ (2 * m))⁻¹
          * (1 + |x| ^ (2 * m)) := by ring

theorem gaussJetScale_rpow {t : ℝ} (ht : 0 < t) (m : ℕ) :
    (t ^ (2 * m))⁻¹ * (Real.sqrt t)⁻¹ = t ^ (-(2 * (m : ℝ)) - 1 / 2) := by
  have hsplit : t ^ (-(2 * (m : ℝ)) - 1 / 2)
      = t ^ (-(2 * (m : ℝ))) * t ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add ht]
    ring_nf
  have hfirst : t ^ (-(2 * (m : ℝ))) = (t ^ (2 * m))⁻¹ := by
    rw [Real.rpow_neg ht.le]
    congr 1
    rw [← Real.rpow_natCast t (2 * m)]
    congr 1
    push_cast
    ring
  have hsecond : t ^ (-(1 / 2) : ℝ) = (Real.sqrt t)⁻¹ := by
    rw [Real.rpow_neg ht.le, Real.sqrt_eq_rpow]
  rw [hsplit, hfirst, hsecond]

/-- **(24.129) The even-derivative Gaussian bound.**  For `0 < t ≤ 1`, any finite combination of
even derivatives of the normalized Gaussian `√(π/t) e^{-ξ²/(4t)}` is dominated by
`C t^{-2m-1/2}(1+|ξ|^{2m}) e^{-ξ²/(4t)}` with a constant depending only on the coefficients. -/
theorem abs_evenDerivGaussian_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (m : ℕ) (c : ℕ → ℝ)
    (x : ℝ) :
    |Real.sqrt (Real.pi / t) * ∑ k ∈ Finset.range (m + 1),
        c k * iteratedDeriv (2 * k) (gaussKernel t) x|
      ≤ Real.sqrt Real.pi * evenJetConst m c * t ^ (-(2 * (m : ℝ)) - 1 / 2)
          * (1 + |x| ^ (2 * m)) * gaussKernel t x := by
  have hsum : ∑ k ∈ Finset.range (m + 1), c k * iteratedDeriv (2 * k) (gaussKernel t) x
      = (∑ k ∈ Finset.range (m + 1), c k * (gaussJetPoly t (2 * k)).eval x) * gaussKernel t x := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDeriv_gaussKernel (ne_of_gt ht0) (2 * k)]
    ring
  have hsqrt : Real.sqrt (Real.pi / t) = Real.sqrt Real.pi * (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_div Real.pi_pos.le, div_eq_mul_inv]
  have hG : 0 < gaussKernel t x := gaussKernel_pos t x
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hspi : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  rw [hsum, hsqrt, ← gaussJetScale_rpow ht0 m, abs_mul, abs_mul, abs_mul, abs_of_pos hG,
    abs_of_nonneg hspi, abs_of_nonneg (inv_nonneg.2 hst.le)]
  have hbound := abs_evenJetCombination_le ht0 ht1 m c x
  have hpre : 0 ≤ Real.sqrt Real.pi * (Real.sqrt t)⁻¹ := by positivity
  calc Real.sqrt Real.pi * (Real.sqrt t)⁻¹
        * (|∑ k ∈ Finset.range (m + 1), c k * (gaussJetPoly t (2 * k)).eval x| * gaussKernel t x)
      ≤ Real.sqrt Real.pi * (Real.sqrt t)⁻¹
          * (evenJetConst m c * (t ^ (2 * m))⁻¹ * (1 + |x| ^ (2 * m)) * gaussKernel t x) := by
        refine mul_le_mul_of_nonneg_left ?_ hpre
        exact mul_le_mul_of_nonneg_right hbound hG.le
    _ = Real.sqrt Real.pi * evenJetConst m c * ((t ^ (2 * m))⁻¹ * (Real.sqrt t)⁻¹)
          * (1 + |x| ^ (2 * m)) * gaussKernel t x := by ring

end

end RHTower
