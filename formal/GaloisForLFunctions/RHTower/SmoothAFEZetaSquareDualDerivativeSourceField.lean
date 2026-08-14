import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeDivisorSquareAffineMeanSquare

noncomputable section

open Complex Set MeasureTheory Filter Topology

namespace RHTower

/-- Literal source derivative field, retaining divisor multiplicity and critical phase. -/
def smoothAFEZetaSquareDualDerivativeSourceField
    (T r t : ℝ) : ℂ :=
  ∑' n : ℕ, smoothAFEZetaSquareDualDerivativeCoefficient T r t n

private theorem smoothAFEZetaSquareDualDerivativeLSeries_term_succ
    (T r center y : ℝ) (n : ℕ) :
    LSeries.term
        (smoothAFEZetaSquareDualDerivativeNatCoefficient T r center)
        ((y : ℝ) * I) (n + 1) =
      smoothAFEZetaSquareDualDerivativeCoefficient T r (center - y) n := by
  have hn : (n + 1 : ℕ) ≠ 0 := by omega
  have hnC : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn,
    smoothAFEZetaSquareDualDerivativeNatCoefficient_succ]
  unfold smoothAFEZetaSquareDualDerivativeCoefficient
  simp only [Nat.cast_add, Nat.cast_one]
  have hphase :
      (n + 1 : ℂ) ^ (linePt center - 1) /
          (n + 1 : ℂ) ^ ((y : ℝ) * I) =
        (n + 1 : ℂ) ^ (linePt (center - y) - 1) := by
    rw [← Complex.cpow_sub _ _ hnC]
    congr 1
    simp only [linePt]
    push_cast
    ring
  calc
    (((n + 1).divisors.card : ℂ) *
          (n + 1 : ℂ) ^ (linePt center - 1) *
            deriv (fun u : ℝ =>
              smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r) /
        (n + 1 : ℂ) ^ ((y : ℝ) * I) =
      ((n + 1).divisors.card : ℂ) *
        ((n + 1 : ℂ) ^ (linePt center - 1) /
          (n + 1 : ℂ) ^ ((y : ℝ) * I)) *
            deriv (fun u : ℝ =>
              smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r := by
        ring
    _ = ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt (center - y) - 1) *
          deriv (fun u : ℝ =>
            smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r := by
      rw [hphase]

/-- The affine L-series is exactly the literal source derivative field at reflected local phase. -/
theorem smoothAFEZetaSquareDualDerivativeLSeries_eq_sourceField
    {T r center : ℝ} (hr : 4 ≤ r) (hT : 0 < T) (y : ℝ) :
    LSeries
        (smoothAFEZetaSquareDualDerivativeNatCoefficient T r center)
        ((y : ℝ) * I) =
      smoothAFEZetaSquareDualDerivativeSourceField T r (center - y) := by
  let a : ℕ → ℂ :=
    smoothAFEZetaSquareDualDerivativeNatCoefficient T r center
  let s : ℂ := (y : ℝ) * I
  have habs : Summable (fun k : ℕ => ‖a k‖) :=
    (summable_smoothAFEZetaSquareDualDerivativeNatCoefficient_affine_masses
      (center := center) hr hT).1
  have hterm : Summable (fun k : ℕ => LSeries.term a s k) := by
    rw [← summable_norm_iff]
    refine habs.congr (fun k => ?_)
    rw [LSeries.norm_term_eq]
    by_cases hk : k = 0
    · simp [hk, a]
    · simp [hk, s]
  have hsplit := hterm.sum_add_tsum_nat_add 1
  calc
    LSeries
        (smoothAFEZetaSquareDualDerivativeNatCoefficient T r center)
        ((y : ℝ) * I) = ∑' k : ℕ, LSeries.term a s k := by rfl
    _ = ∑' n : ℕ, LSeries.term a s (n + 1) := by
      rw [← hsplit]
      simp [a, s]
    _ = ∑' n : ℕ,
        smoothAFEZetaSquareDualDerivativeCoefficient T r (center - y) n := by
      apply tsum_congr
      intro n
      exact smoothAFEZetaSquareDualDerivativeLSeries_term_succ T r center y n
    _ = smoothAFEZetaSquareDualDerivativeSourceField T r (center - y) := rfl

/-- The affine mean-square estimate lands on the literal source field without losing phase. -/
theorem exists_integral_normSq_smoothAFEZetaSquareDualDerivativeSourceField_reflected_le_dyadic_logCube :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
      ∀ {N : ℕ} {r center H : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) → 1 ≤ H →
        (∫ y in Set.Icc (-H) H,
          ‖smoothAFEZetaSquareDualDerivativeSourceField
            (N : ℝ) r (center - y)‖ ^ 2) ≤
          5 * Real.pi * Real.exp 1 *
              (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
            (5 * Real.pi / 2) *
              (A * (N : ℝ) ^ (-(399 / 200 : ℝ))) * H := by
  obtain ⟨A, K, hA, hK, hmv⟩ :=
    exists_integral_normSq_smoothAFEZetaSquareDualDerivativeLSeries_le_dyadic_logCube
  refine ⟨A, K, hA, hK, ?_⟩
  intro N r center H hN hr hH
  have hN0 : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hr4 : (4 : ℝ) ≤ r := by
    have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
    exact hN4real.trans hr.1
  have hbound := hmv (center := center) hN hr hH
  have heq :
      (fun y : ℝ =>
        ‖LSeries
          (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
          ((y : ℝ) * I)‖ ^ 2) =
      (fun y : ℝ =>
        ‖smoothAFEZetaSquareDualDerivativeSourceField
          (N : ℝ) r (center - y)‖ ^ 2) := by
    funext y
    rw [smoothAFEZetaSquareDualDerivativeLSeries_eq_sourceField hr4 hN0]
  rwa [heq] at hbound

/-- Physical-cell form: the source derivative field has the same affine mean-square bound on
`[center-H, center+H]`. -/
theorem exists_integral_normSq_smoothAFEZetaSquareDualDerivativeSourceField_le_dyadic_logCube :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
      ∀ {N : ℕ} {r center H : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) → 1 ≤ H →
        (∫ t in Set.Icc (center - H) (center + H),
          ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ 2) ≤
          5 * Real.pi * Real.exp 1 *
              (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
            (5 * Real.pi / 2) *
              (A * (N : ℝ) ^ (-(399 / 200 : ℝ))) * H := by
  obtain ⟨A, K, hA, hK, hmv⟩ :=
    exists_integral_normSq_smoothAFEZetaSquareDualDerivativeSourceField_reflected_le_dyadic_logCube
  refine ⟨A, K, hA, hK, ?_⟩
  intro N r center H hN hr hH
  have hleft : center - H ≤ center + H := by linarith
  have hreflect :
      (∫ y in Set.Icc (-H) H,
          ‖smoothAFEZetaSquareDualDerivativeSourceField
            (N : ℝ) r (center - y)‖ ^ 2) =
        ∫ t in Set.Icc (center - H) (center + H),
          ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
    rw [intervalIntegral.integral_comp_sub_left
      (fun t : ℝ =>
        ‖smoothAFEZetaSquareDualDerivativeSourceField (N : ℝ) r t‖ ^ 2)
      center]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hleft]
    congr 1
    all_goals ring
  rw [← hreflect]
  exact hmv hN hr hH

end RHTower
