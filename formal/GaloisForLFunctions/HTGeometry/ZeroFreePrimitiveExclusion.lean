import GaloisForLFunctions.HTGeometry.GoldbergFiniteOrder

/-!
# Zero-free primitives of first-order solutions are exponentials of polynomials

If `W` is entire and nowhere zero and its derivative satisfies a first-order algebraic differential
relation, then `W' ` has finite order by Gol'dberg's theorem, hence so does `W` — a primitive grows
at most like the radius times the derivative — and Hadamard's zero-free factorization makes `W` the
exponential of a polynomial.  Such a `W` satisfies the first-order relation `W' = P' · W`, so it is
itself of differential order one.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter

/-- **A primitive inherits a finite-order envelope.**  The mean value inequality on the disc of
radius `‖z‖` costs one power of the radius. -/
theorem finiteOrderEnvelope_of_deriv {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (h : FiniteOrderEnvelope (deriv W)) : FiniteOrderEnvelope W := by
  obtain ⟨C, d, hC, hgrow⟩ := h
  refine ⟨‖W 0‖ + 1 + C, d + 1, by positivity, fun z => ?_⟩
  set X : ℝ := C * (1 + ‖z‖) ^ d with hX
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hX0 : 0 ≤ X := by positivity
  have hexp1 : (1 : ℝ) ≤ Real.exp X := Real.one_le_exp hX0
  have hball : ∀ x ∈ Metric.closedBall (0 : ℂ) ‖z‖, ‖deriv W x‖ ≤ Real.exp X := by
    intro x hx
    have hxz : ‖x‖ ≤ ‖z‖ := by simpa using hx
    refine le_trans (hgrow x) (Real.exp_le_exp.mpr ?_)
    refine mul_le_mul_of_nonneg_left ?_ hC
    exact pow_le_pow_left₀ (by positivity) (by linarith) d
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := W) (fun x _ => hW x) hball (convex_closedBall (0 : ℂ) ‖z‖)
    (by simp : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ‖z‖)
    (by simp : z ∈ Metric.closedBall (0 : ℂ) ‖z‖)
  rw [sub_zero] at hmv
  have hnorm : ‖W z‖ - ‖W 0‖ ≤ ‖W z - W 0‖ := norm_sub_norm_le _ _
  have h1 : ‖W z‖ ≤ ‖W 0‖ + Real.exp X * ‖z‖ := by linarith
  have h2 : ‖W 0‖ + Real.exp X * ‖z‖ ≤ (‖W 0‖ + ‖z‖) * Real.exp X := by
    nlinarith [hexp1, norm_nonneg (W 0), hzn]
  have h3 : ‖W 0‖ + ‖z‖ ≤ Real.exp (‖W 0‖ + ‖z‖) := by
    have := Real.add_one_le_exp (‖W 0‖ + ‖z‖)
    linarith
  have h4 : (‖W 0‖ + ‖z‖) * Real.exp X ≤ Real.exp (‖W 0‖ + ‖z‖ + X) := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_right h3 (le_of_lt (Real.exp_pos X))
  have hpow1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ (d + 1) := one_le_pow₀ (by linarith)
  have hpowz : ‖z‖ ≤ (1 + ‖z‖) ^ (d + 1) := by
    have h5 : (1 : ℝ) + ‖z‖ ≤ (1 + ‖z‖) ^ (d + 1) := by
      calc (1 : ℝ) + ‖z‖ = (1 + ‖z‖) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (1 + ‖z‖) ^ (d + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  have hpowd : (1 + ‖z‖) ^ d ≤ (1 + ‖z‖) ^ (d + 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have h5 : ‖W 0‖ + ‖z‖ + X ≤ (‖W 0‖ + 1 + C) * (1 + ‖z‖) ^ (d + 1) := by
    rw [hX]
    nlinarith [hpow1, hpowz, hpowd, hC, norm_nonneg (W 0)]
  calc ‖W z‖ ≤ ‖W 0‖ + Real.exp X * ‖z‖ := h1
    _ ≤ (‖W 0‖ + ‖z‖) * Real.exp X := h2
    _ ≤ Real.exp (‖W 0‖ + ‖z‖ + X) := h4
    _ ≤ Real.exp ((‖W 0‖ + 1 + C) * (1 + ‖z‖) ^ (d + 1)) := Real.exp_le_exp.mpr h5

/-- **The zero-free primitive boundary case.**  A nowhere-vanishing entire function whose derivative
satisfies a first-order algebraic differential relation is the exponential of a polynomial, and
therefore satisfies the first-order relation `W' = P'·W` itself. -/
theorem exists_polynomial_exp_of_zeroFree_primitive {W : ℂ → ℂ} (hW : Differentiable ℂ W)
    (hne : ∀ z, W z ≠ 0) {n₀ : ℕ} (hn₀ : taylorCoeff (deriv W) n₀ ≠ 0)
    {S : Finset (ℕ × ℕ)} {A : ℕ × ℕ → Polynomial ℂ} {d m : ℕ}
    (hdeg : ∀ p ∈ S, p.1 + p.2 ≤ d)
    (hrel : ∀ w : ℂ, ∑ p ∈ S, (A p).eval w * (deriv W w) ^ p.1
      * (deriv (deriv W) w) ^ p.2 = 0)
    (hm : 1 ≤ m) (hmd : m ≤ d) (hmem : (d - m, m) ∈ S)
    (htopdeg : ∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ m) (hAne : A (d - m, m) ≠ 0) :
    ∃ P : Polynomial ℂ, (∀ z, W z = Complex.exp (P.eval z)) ∧
      ∀ z, deriv W z = (Polynomial.derivative P).eval z * W z := by
  have hWan : AnalyticOnNhd ℂ W Set.univ := hW.differentiableOn.analyticOnNhd isOpen_univ
  have hWd : Differentiable ℂ (deriv W) := fun z => ((hWan.deriv) z (Set.mem_univ z)).differentiableAt
  have henvd : FiniteOrderEnvelope (deriv W) :=
    finiteOrderEnvelope_of_algebraic_relation hWd hn₀ hdeg hrel hm hmd hmem htopdeg hAne
  obtain ⟨C, dd, hC, hgrow⟩ := finiteOrderEnvelope_of_deriv hW henvd
  obtain ⟨P, hP⟩ := exists_polynomial_exp_of_ne_zero_of_growth hW hne hC hgrow
  refine ⟨P, hP, fun z => ?_⟩
  have hfun : W = fun w => Complex.exp (P.eval w) := funext hP
  have hderiv : HasDerivAt (fun w => Complex.exp (P.eval w))
      (Complex.exp (P.eval z) * (Polynomial.derivative P).eval z) z := by
    have hp : HasDerivAt (fun w => P.eval w) ((Polynomial.derivative P).eval z) z :=
      P.hasDerivAt z
    exact hp.cexp
  rw [hfun, hderiv.deriv]
  simp only []
  ring

end GaloisForLFunctions.HTGeometry
