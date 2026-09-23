import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareDualDerivativeAffineMeanSquare
import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareDualDerivativeMass

noncomputable section

open Complex Set MeasureTheory

namespace RHTower

/-- Critical amplitude cancellation: the affine `n`-weighted mass is exactly
the phase-free divisor-square derivative mass. -/
theorem natSucc_mul_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_eq
    (T r center : ℝ) (n : ℕ) :
    (n + 1 : ℝ) *
        ‖smoothAFEZetaSquareDualDerivativeCoefficient T r center n‖ ^ 2 =
      (((n + 1).divisors.card : ℝ) ^ 2) *
        ‖deriv (fun u : ℝ =>
          smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r‖ ^ 2 := by
  have hx : 0 < (n + 1 : ℝ) := by positivity
  rw [norm_smoothAFEZetaSquareDualDerivativeCoefficient]
  rw [mul_pow, mul_pow,
    ← Real.rpow_natCast ((n + 1 : ℝ) ^ (-(1 / 2 : ℝ))) 2,
    ← Real.rpow_mul hx.le]
  have hpow : (n + 1 : ℝ) *
      (n + 1 : ℝ) ^ (-(1 / 2 : ℝ) * (2 : ℝ)) = 1 := by
    rw [show (-(1 / 2 : ℝ) * (2 : ℝ)) = -1 by ring,
      Real.rpow_neg_one]
    exact mul_inv_cancel₀ hx.ne'
  calc
    (n + 1 : ℝ) *
        (((((n + 1).divisors.card : ℝ) ^ 2) *
          (n + 1 : ℝ) ^ (-(1 / 2 : ℝ) * (2 : ℝ))) *
            ‖deriv (fun u : ℝ =>
              smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r‖ ^ 2) =
      (((n + 1).divisors.card : ℝ) ^ 2) *
        ‖deriv (fun u : ℝ =>
          smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r‖ ^ 2 *
          ((n + 1 : ℝ) *
            (n + 1 : ℝ) ^ (-(1 / 2 : ℝ) * (2 : ℝ))) := by
      ring
    _ = (((n + 1).divisors.card : ℝ) ^ 2) *
        ‖deriv (fun u : ℝ =>
          smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * T)) r‖ ^ 2 := by
      rw [hpow, mul_one]

/-- The exact weighted mass inherits the corpus' Abel-summed divisor-square
tail, improving the subpower estimate to `log^(3 : ℕ) N / N`. -/
theorem exists_tsum_weighted_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_logCube :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N : ℕ} {r center : ℝ},
      4 ≤ N → r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) →
      (∑' n : ℕ,
        (n + 1 : ℝ) *
          ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r center n‖ ^ 2) ≤
        K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by
  obtain ⟨K, hK, hmass⟩ :=
    RHTower.Sieve.exists_tsum_divisorSquare_norm_deriv_dualWeight_sq_le_dyadic
  refine ⟨K, hK, ?_⟩
  intro N r center hN hr
  calc
    (∑' n : ℕ,
      (n + 1 : ℝ) *
        ‖smoothAFEZetaSquareDualDerivativeCoefficient (N : ℝ) r center n‖ ^ 2) =
      ∑' n : ℕ,
        (((n + 1).divisors.card : ℝ) ^ 2) *
          ‖deriv (fun u : ℝ =>
            smoothAFEZetaSquareDualWeight u ((n + 1 : ℝ) * (N : ℝ))) r‖ ^ 2 := by
      apply tsum_congr
      intro n
      exact natSucc_mul_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_eq
        (N : ℝ) r center n
    _ ≤ K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ) := by
      simpa using hmass hN hr

/-- **Frankenstein affine landing.** The plain mass comes from the
negative/positive contour split, while the weighted mass comes from the
Abel-summed divisor-square route. -/
theorem exists_integral_normSq_smoothAFEZetaSquareDualDerivativeLSeries_le_dyadic_logCube :
    ∃ A K : ℝ, 0 ≤ A ∧ 0 ≤ K ∧
      ∀ {N : ℕ} {r center H : ℝ}, 4 ≤ N →
        r ∈ Set.Icc (N : ℝ) (2 * N : ℝ) → 1 ≤ H →
        (∫ y in Set.Icc (-H) H,
          ‖LSeries
            (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
            ((y : ℝ) * I)‖ ^ 2) ≤
          5 * Real.pi * Real.exp 1 *
              (K * (1 + Real.log (N : ℝ)) ^ 3 / (N : ℝ)) +
            (5 * Real.pi / 2) *
              (A * (N : ℝ) ^ (-(399 / 200 : ℝ))) * H := by
  obtain ⟨A, B, hA, hB, hmass⟩ :=
    exists_tsum_smoothAFEZetaSquareDualDerivativeCoefficient_masses_le_dyadic
  obtain ⟨K, hK, hweightedMass⟩ :=
    exists_tsum_weighted_norm_smoothAFEZetaSquareDualDerivativeCoefficient_sq_le_logCube
  refine ⟨A, K, hA, hK, ?_⟩
  intro N r center H hN hr hH
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hr4 : (4 : ℝ) ≤ r := by
    have hN4real : (4 : ℝ) ≤ N := by exact_mod_cast hN
    exact hN4real.trans hr.1
  obtain ⟨habs, hplain, hweighted⟩ :=
    summable_smoothAFEZetaSquareDualDerivativeNatCoefficient_affine_masses
      (center := center) hr4 hN0
  have hmv :=
    RHTower.Sieve.integral_Icc_normSq_LSeries_le_general_affine_infinite
      (a := smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
      (smoothAFEZetaSquareDualDerivativeNatCoefficient_zero _ _ _) 0
      (by simpa using habs) (by simpa using hplain) (by simpa using hweighted) hH
  have hmv' :
      (∫ y in Set.Icc (-H) H,
        ‖LSeries
          (smoothAFEZetaSquareDualDerivativeNatCoefficient (N : ℝ) r center)
          ((y : ℝ) * I)‖ ^ 2) ≤
        5 * Real.pi * Real.exp 1 *
            (∑' k : ℕ, (k : ℝ) *
              ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                (N : ℝ) r center k‖ ^ 2) +
          (5 * Real.pi / 2) *
            (∑' k : ℕ,
              ‖smoothAFEZetaSquareDualDerivativeNatCoefficient
                (N : ℝ) r center k‖ ^ 2) * H := by
    simpa using hmv
  obtain ⟨hplainMass, hsubpowerWeightedMass⟩ := hmass (t := center) hN hr
  have hlogWeightedMass := hweightedMass (center := center) hN hr
  rw [tsum_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_eq
    (center := center) hr4 hN0] at hmv'
  rw [tsum_weighted_norm_smoothAFEZetaSquareDualDerivativeNatCoefficient_sq_eq
    (center := center) hr4 hN0] at hmv'
  exact hmv'.trans (by
    gcongr)

end RHTower
