import Mathlib

/-!
# Iterated integration by parts against the kernel `1/(1 − xy)`

For `0 ≤ y < 1` put `g_m(x) = m! yᵐ/(1 − xy)^{m+1}`, so that `g_m' = g_{m+1}`.  If a polynomial `f`
has all derivatives of order `< n` vanishing at `0` and `1`, then `n` integrations by parts give

`∫₀¹ f⁽ⁿ⁾(x)/(1 − xy) dx = (−1)ⁿ n! yⁿ ∫₀¹ f(x)/(1 − xy)^{n+1} dx`.

For `f = xⁿ(1 − x)ⁿ` the left side is `n!` times the integral of the shifted Legendre polynomial
`Pₙ = f⁽ⁿ⁾/n!` (Rodrigues' formula), which gives Beukers' identity

`∫₀¹ Pₙ(x)/(1 − xy) dx = (−1)ⁿ yⁿ ∫₀¹ (x(1 − x))ⁿ/(1 − xy)^{n+1} dx`.
-/

open Polynomial MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry.BeukersZetaTwo

/-- The `m`-th derivative `m! yᵐ/(1 − xy)^{m+1}` of `x ↦ 1/(1 − xy)`. -/
noncomputable def kernelDeriv (y : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  (m.factorial : ℝ) * y ^ m / (1 - x * y) ^ (m + 1)

theorem one_sub_mul_pos {x y : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 < 1 - x * y := by nlinarith

theorem hasDerivAt_kernelDeriv {y x : ℝ} (hxy : 1 - x * y ≠ 0) (m : ℕ) :
    HasDerivAt (kernelDeriv y m) (kernelDeriv y (m + 1) x) x := by
  have h1 : HasDerivAt (fun t : ℝ => 1 - t * y) (-y) x := by
    simpa using ((hasDerivAt_id x).mul_const y).const_sub 1
  have hp : (1 - x * y) ^ (m + 1) ≠ 0 := pow_ne_zero _ hxy
  have h := ((h1.pow (m + 1)).inv hp).const_mul ((m.factorial : ℝ) * y ^ m)
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp [kernelDeriv, div_eq_mul_inv]
  · simp only [kernelDeriv, Pi.pow_apply, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem continuousOn_kernelDeriv {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (m : ℕ) :
    ContinuousOn (kernelDeriv y m) (uIcc 0 1) := by
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  have := one_sub_mul_pos hx.1 hx.2 hy0 hy1
  exact (hasDerivAt_kernelDeriv this.ne' m).continuousAt.continuousWithinAt

/-- **Iterated integration by parts.** -/
theorem integral_iterate_derivative_mul_kernel {f : ℝ[X]} {n : ℕ}
    (hf0 : ∀ j < n, (derivative^[j] f).eval 0 = 0) (hf1 : ∀ j < n, (derivative^[j] f).eval 1 = 0)
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∫ x in (0 : ℝ)..1, (derivative^[n] f).eval x * kernelDeriv y 0 x =
      (-1) ^ n * ∫ x in (0 : ℝ)..1, f.eval x * kernelDeriv y n x := by
  have hpos : ∀ x ∈ uIcc (0 : ℝ) 1, 1 - x * y ≠ 0 := fun x hx => by
    rw [uIcc_of_le zero_le_one] at hx
    exact (one_sub_mul_pos hx.1 hx.2 hy0 hy1).ne'
  have hpolyInt : ∀ k : ℕ, IntervalIntegrable (fun x => (derivative^[k] f).eval x)
      MeasureTheory.volume 0 1 :=
    fun k => (Polynomial.continuous _).intervalIntegrable 0 1
  have hstep : ∀ m < n, ∫ x in (0 : ℝ)..1, (derivative^[n - m] f).eval x * kernelDeriv y m x =
      -∫ x in (0 : ℝ)..1, (derivative^[n - (m + 1)] f).eval x * kernelDeriv y (m + 1) x := by
    intro m hm
    set k := n - (m + 1) with hk
    have hnm : n - m = k + 1 := by omega
    rw [hnm]
    have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (kernelDeriv y m) (kernelDeriv y (m + 1) x) x :=
      fun x hx => hasDerivAt_kernelDeriv (hpos x hx) m
    have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x => (derivative^[k] f).eval x)
        ((derivative^[k + 1] f).eval x) x := fun x _ => by
      rw [Function.iterate_succ_apply']
      exact Polynomial.hasDerivAt _ x
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((continuousOn_kernelDeriv hy0 hy1 (m + 1)).intervalIntegrable) (hpolyInt (k + 1))
    have hk0 := hf0 k (by omega)
    have hk1 := hf1 k (by omega)
    have e1 : ∫ x in (0 : ℝ)..1, (derivative^[k + 1] f).eval x * kernelDeriv y m x =
        ∫ x in (0 : ℝ)..1, kernelDeriv y m x * (derivative^[k + 1] f).eval x := by
      congr 1; funext x; ring
    have e2 : ∫ x in (0 : ℝ)..1, (derivative^[k] f).eval x * kernelDeriv y (m + 1) x =
        ∫ x in (0 : ℝ)..1, kernelDeriv y (m + 1) x * (derivative^[k] f).eval x := by
      congr 1; funext x; ring
    rw [e1, e2, hibp, hk0, hk1]
    ring
  have hall : ∀ m ≤ n, ∫ x in (0 : ℝ)..1, (derivative^[n] f).eval x * kernelDeriv y 0 x =
      (-1) ^ m * ∫ x in (0 : ℝ)..1, (derivative^[n - m] f).eval x * kernelDeriv y m x := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [ih (by omega), hstep m (by omega), pow_succ]
      ring
  simpa using hall n le_rfl

/-- The Rodrigues polynomial `xⁿ(1 − x)ⁿ`. -/
noncomputable def rodriguesPoly (n : ℕ) : ℝ[X] := X ^ n * (1 - X) ^ n

theorem rodriguesPoly_eval (n : ℕ) (x : ℝ) : (rodriguesPoly n).eval x = (x * (1 - x)) ^ n := by
  simp [rodriguesPoly, mul_pow]

theorem iterate_derivative_rodriguesPoly_eval_zero {n j : ℕ} (hj : j < n) :
    (derivative^[j] (rodriguesPoly n)).eval 0 = 0 := by
  have hdvd : (X : ℝ[X]) ^ n ∣ rodriguesPoly n := ⟨(1 - X) ^ n, rfl⟩
  obtain ⟨q, hq⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd j hdvd
  rw [hq, eval_mul, eval_pow, eval_X, zero_pow (by omega), zero_mul]

theorem iterate_derivative_rodriguesPoly_eval_one {n j : ℕ} (hj : j < n) :
    (derivative^[j] (rodriguesPoly n)).eval 1 = 0 := by
  have hdvd : (X - C 1 : ℝ[X]) ^ n ∣ rodriguesPoly n := by
    refine ⟨(-1) ^ n * X ^ n, ?_⟩
    have e : (1 - X : ℝ[X]) = (-1) * (X - C 1) := by rw [map_one]; ring
    rw [rodriguesPoly, e, mul_pow]
    ring
  obtain ⟨q, hq⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd j hdvd
  rw [hq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow (by omega), zero_mul]

/-- The shifted Legendre polynomial over `ℝ`. -/
noncomputable def legendreR (n : ℕ) : ℝ[X] := (shiftedLegendre n).map (Int.castRingHom ℝ)

theorem factorial_mul_legendreR (n : ℕ) :
    (n.factorial : ℝ[X]) * legendreR n = derivative^[n] (rodriguesPoly n) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) (factorial_mul_shiftedLegendre_eq n)
  rw [Polynomial.map_mul, ← Polynomial.iterate_derivative_map] at h
  simpa [legendreR, rodriguesPoly, Polynomial.map_pow, Polynomial.map_sub] using h

/-- **Beukers' identity.**  For `0 ≤ y < 1`,
`∫₀¹ Pₙ(x)/(1 − xy) dx = (−1)ⁿ yⁿ ∫₀¹ (x(1 − x))ⁿ/(1 − xy)^{n+1} dx`. -/
theorem integral_legendre_div_one_sub_mul (n : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∫ x in (0 : ℝ)..1, (legendreR n).eval x / (1 - x * y) =
      (-1) ^ n * y ^ n * ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n / (1 - x * y) ^ (n + 1) := by
  have h := integral_iterate_derivative_mul_kernel (f := rodriguesPoly n) (n := n)
    (fun j hj => iterate_derivative_rodriguesPoly_eval_zero hj)
    (fun j hj => iterate_derivative_rodriguesPoly_eval_one hj) hy0 hy1
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hl : ∀ x : ℝ, (derivative^[n] (rodriguesPoly n)).eval x * kernelDeriv y 0 x =
      (n.factorial : ℝ) * ((legendreR n).eval x / (1 - x * y)) := fun x => by
    rw [← factorial_mul_legendreR, eval_mul, kernelDeriv]
    simp only [eval_natCast, Nat.factorial_zero, Nat.cast_one, pow_zero, zero_add, pow_one]
    ring
  have hr : ∀ x : ℝ, (rodriguesPoly n).eval x * kernelDeriv y n x =
      (n.factorial : ℝ) * (y ^ n * ((x * (1 - x)) ^ n / (1 - x * y) ^ (n + 1))) := fun x => by
    rw [rodriguesPoly_eval, kernelDeriv]
    ring
  simp_rw [hl, hr, intervalIntegral.integral_const_mul] at h
  have h' : (n.factorial : ℝ) * ∫ x in (0 : ℝ)..1, (legendreR n).eval x / (1 - x * y) =
      (n.factorial : ℝ) * ((-1) ^ n * y ^ n *
        ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ n / (1 - x * y) ^ (n + 1)) := by
    rw [h]; ring
  exact mul_left_cancel₀ hfac h'

end GaloisForLFunctions.HTGeometry.BeukersZetaTwo
