import GaloisForLFunctions.RHTower.PerfectSquareQuadraticTaylorAndTrapezoidalCentralDiffRHBridge

/-!
# Midpoint-Slope Pure Half-Square Quadratic Taylor Sandwiches, Pure-Monomial `m * h^4` Three-Square Weights, and Quartic-Cancelling Central-Difference Tauberian Bridges

This module is the thirtieth self-contained step in the unconditional RH synthesis tower. Building
directly on `PerfectSquareQuadraticTaylorAndTrapezoidalCentralDiffRHBridge`, we establish four major
structural advances:

1. **Pure Half-Square Pointwise Quadratic Taylor Sandwiches Around `chebyshevMidpointClassicalPotential N`
   and Symmetric Trapezoidal Step Sandwiches (Section 1):**
   In `QuadraticTaylorSecondSqrtRieszAndSquareGridCesaroRHBridge`, expanding `Φ₂(M) - Φ₂(N)` around
   the left-endpoint slope `Φ₁(N)` gave asymmetric triangular Taylor weights `(M - N)(M - N + 1)/2`
   (forward) and `(N - P)(N - P - 1)/2` (backward). Because `Φ₂(N + 1) - Φ₂(N) = Φ₁(N) + ψ(N) =
   Φ₁(N + 1)`, the symmetric central slope of `Φ₂` at `N` is the midpoint potential
   `chebyshevMidpointClassicalPotential N = (Φ₁(N) + Φ₁(N + 1)) / 2 = Φ₁(N) + (1 / 2) * ψ(N)`.
   We prove that expanding `Φ₂` around `chebyshevMidpointClassicalPotential N` eliminates the
   `± (K - N) / 2` asymmetry identically, yielding the pure half-square weight `(K - N)^2 / 2` on
   both sides:
   - `chebyshevSecondConvexPotential_succ_sub_midpointClassicalPotential_sandwich`:
     `((M - N) + 1 / 2) * ψ(N) ≤ (Φ₂(M + 1) - Φ₂(M)) - Φ₁^{\mathrm{mid}}(N) ≤ ((M - N) + 1 / 2) * ψ(M)`
   - `chebyshevSecondConvexPotential_forward_midpointSlope_quadratic_taylor_sandwich`:
     `((M - N)^2 / 2) * ψ(N) ≤ Φ₂(M) - Φ₂(N) - (M - N) * Φ₁^{\mathrm{mid}}(N) ≤ ((M - N)^2 / 2) * ψ(M)`
   - `chebyshevSecondConvexPotential_backward_midpointSlope_quadratic_taylor_sandwich`:
     `((N - P)^2 / 2) * ψ(P) ≤ (N - P) * Φ₁^{\mathrm{mid}}(N) - (Φ₂(N) - Φ₂(P)) ≤ ((N - P)^2 / 2) * ψ(N)`
   - `chebyshevSecondConvexPotential_trapezoidal_forward_midpointSlope_quadratic_taylor_sandwich` and
     `chebyshevSecondConvexPotential_trapezoidal_backward_midpointSlope_quadratic_taylor_sandwich`:
     averaging at `K` and `K + 1` gives the completely symmetric endpoint-average quadratic Taylor
     weight `((K - N)^2 + (K + 1 - N)^2) / 4`.

2. **The Symmetric Midpoint-Slope Second-Order Trapezoidal Taylor Weights `W_{\mathrm{mid}, ±}`,
   Exact `+(1 / 4) * (√M - √N)` Shift Laws, and Forward/Backward Sandwiches (Section 2):**
   We define `secularMidpointSlopeSecondOrderForwardWeight N M` (`W_{\mathrm{mid}, +}(N, M)`) and
   `secularMidpointSlopeSecondOrderBackwardWeight L N` (`W_{\mathrm{mid}, -}(L, N)`), prove that they
   differ from the left-endpoint weights `W_±` by the exact radical shift `+(1 / 4) * (√M - √N)` and
   `+(1 / 4) * (√N - √L)` (`(k^2 + (k + 1)^2) / 4 = k(k + 1) / 2 + 1 / 4`), prove their symmetric
   step recurrences with weight `(√(K + 1) - √K) * (((K - N)^2 + (K + 1 - N)^2) / 4)`, their
   non-negativity, and the two-sided forward and backward quadratic Taylor sandwiches
   `chebyshevTrapezoidalSecondSqrtRieszPotential_forward_midpointSlope_quadratic_taylor_sandwich`
   and `chebyshevTrapezoidalSecondSqrtRieszPotential_backward_midpointSlope_quadratic_taylor_sandwich`.

3. **Pure-Monomial `m * h^4` Weight Difference, 4-Term Euler–Maclaurin Polynomials
   `E_{W_{\mathrm{mid}, ±}}(m, h)`, and Centered Three-Square `(C₁^{\mathrm{mid}}(m^2), ψ(m^2) - m^2)`
   Sandwiches (Section 3):**
   On the square grid `((m - h)^2, m^2, (m + h)^2)`, replacing `Φ₁(m^2)` by `Φ₁^{\mathrm{mid}}(m^2)`
   cancels both `± (1 / 2) * h^2 * m` and `+(1 / 6) * h^3` in the Euler–Maclaurin weight polynomials:
   `E_{W_{\mathrm{mid}, ±}}(m, h) = (2 / 3) * h^3 * m^2 ± (1 / 2) * h^4 * m + (1 / 10) * h^5 + (1 / 8) * h`.
   Consequently, their difference is the pure monomial `m * h^4`
   (`eulerMaclaurinTrapezoidalSqrtRiesz_sub_sq_sub_half_mul_increment_square_second_diff_eq`), their
   sum is the 3-term even polynomial `(4 / 3) * h^3 * m^2 + (1 / 5) * h^5 + (1 / 4) * h`, and the
   centered three-square inequality for `chebyshevTrapezoidalSecondSqrtRieszAction` couples
   `chebyshevMidpointClassicalCesaroSum (m^2)` with `ψ(m^2) - m^2` (weighted by `≈ m * h^4`) and
   the three-term secular polynomial `m * h^2 * ((2 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 1 / 8)`.

4. **Quartic-Cancelling (`m^4`-Free and `h^3 * m^2`-Free) Central-Difference Secular Identities and
   Second-Order Central-Difference Sandwiches for `2 * h * chebyshevSecondCesaroSum (m^2)` (Section 4):**
   We prove `eulerMaclaurinTrapezoidalSecondSqrtRiesz_central_diff_quartic_cancelling_secular_eq`:
   subtracting `2 * h * S₂(m^2)`, `((E_{F_√}((m + h)^2) - E_{F_√}((m - h)^2)) - (2 * m^2 - 1) * h) * S₁(m^2)`,
   AND `(E_{W_{\mathrm{trap}, +}}(m, h) + E_{W_{\mathrm{trap}, -}}(m, h)) * m^2` from
   `E_2^{\mathrm{trap}}((m + h)^2) - E_2^{\mathrm{trap}}((m - h)^2)` cancels BOTH `(4 / 3) * h^3 * m^4`
   AND `(1 / 3) * h^3 * m^2` identically, leaving the quadratic-in-`m` polynomial
   `((4 / 5) * h^5 - (1 / 24) * h) * m^2 + (1 / 21) * h^7 - (1 / 24) * h^3`. We derive the resulting
   second-order central-difference inequalities for `2 * h * chebyshevSecondCesaroSum (m^2)` in both
   the `(C₁(m^2), W_{\mathrm{trap}, ±})` and `(C₁^{\mathrm{mid}}(m^2), W_{\mathrm{mid}, ±})` gauges.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open Complex Real Filter Topology Finset

/-! ## Section 1: Pure Half-Square Pointwise Quadratic Taylor Sandwiches Around `chebyshevMidpointClassicalPotential` and Symmetric Trapezoidal Step Sandwiches -/

/-- **Single-Step Midpoint-Slope Sandwich for `chebyshevSecondConvexPotential`:**
For any `2 ≤ N ≤ M`, subtracting the midpoint slope
`chebyshevMidpointClassicalPotential N = Φ₁(N) + (1 / 2) * ψ(N)` from the unit step
`Φ₂(M + 1) - Φ₂(M) = Φ₁(M) + ψ(M)` produces the exact half-integer weight `M - N + 1 / 2`:
`(M - N + 1 / 2) * ψ(N) ≤
  (chebyshevSecondConvexPotential (M + 1) - chebyshevSecondConvexPotential M) -
    chebyshevMidpointClassicalPotential N ≤
  (M - N + 1 / 2) * ψ(M)`. -/
theorem chebyshevSecondConvexPotential_succ_sub_midpointClassicalPotential_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((M : ℝ) - (N : ℝ) + 1 / 2) * Chebyshev.psi (N : ℝ) ≤
      (chebyshevSecondConvexPotential (M + 1) - chebyshevSecondConvexPotential M) -
        chebyshevMidpointClassicalPotential N ∧
    (chebyshevSecondConvexPotential (M + 1) - chebyshevSecondConvexPotential M) -
        chebyshevMidpointClassicalPotential N ≤
      ((M : ℝ) - (N : ℝ) + 1 / 2) * Chebyshev.psi (M : ℝ) := by
  have hM2 : 2 ≤ M := le_trans hN hNM
  have hstep2 := chebyshevSecondConvexPotential_succ_sub_of_two_le hM2
  have hstep1 := chebyshevClassicalConvexPotential_succ_sub_of_two_le hM2
  unfold chebyshevMidpointClassicalPotential
  by_cases hEq : N = M
  · subst hEq
    constructor <;> linarith [hstep2, hstep1]
  · have hN1_le_M : N + 1 ≤ M := by omega
    have hN1_two : 2 ≤ N + 1 := by omega
    have hPhi1_step := chebyshevClassicalConvexPotential_succ_sub_of_two_le hN
    have hPhi1_bounds := chebyshevClassicalConvexPotential_sub_bounds hN1_two hN1_le_M
    have hc1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    have hpsi_mono1 : Chebyshev.psi (N : ℝ) ≤ Chebyshev.psi ((N + 1 : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast (show N ≤ N + 1 by omega))
    have hpsi_mono2 : Chebyshev.psi (N : ℝ) ≤ Chebyshev.psi (M : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast hNM)
    have hspan_nonneg : 0 ≤ (M : ℝ) - ((N + 1 : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact_mod_cast hN1_le_M
    have hlow_mul :=
      le_trans (mul_le_mul_of_nonneg_left hpsi_mono1 hspan_nonneg) hPhi1_bounds.1
    rw [hc1] at hlow_mul hPhi1_bounds
    constructor
    · linarith [hstep2, hstep1, hPhi1_step, hlow_mul, hpsi_mono2]
    · linarith [hstep2, hstep1, hPhi1_step, hPhi1_bounds.2, hpsi_mono2]

/-- **Pure Half-Square Forward Pointwise Quadratic Taylor Sandwich Around `chebyshevMidpointClassicalPotential`:**
For any `2 ≤ N ≤ M`, expanding `chebyshevSecondConvexPotential M` around `N` using the midpoint slope
`chebyshevMidpointClassicalPotential N = Φ₁(N) + (1 / 2) * ψ(N)` replaces the triangular weight
`(M - N) * (M - N + 1) / 2` by the exact half-square `(M - N)^2 / 2`:
`(((M - N)^2) / 2) * ψ(N) ≤
  chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N -
    (M - N) * chebyshevMidpointClassicalPotential N ≤
  (((M - N)^2) / 2) * ψ(M)`. -/
theorem chebyshevSecondConvexPotential_forward_midpointSlope_quadratic_taylor_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (((M : ℝ) - (N : ℝ)) ^ 2 / 2) * Chebyshev.psi (N : ℝ) ≤
      chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N -
        ((M : ℝ) - (N : ℝ)) * chebyshevMidpointClassicalPotential N ∧
    chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N -
        ((M : ℝ) - (N : ℝ)) * chebyshevMidpointClassicalPotential N ≤
      (((M : ℝ) - (N : ℝ)) ^ 2 / 2) * Chebyshev.psi (M : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hstep :=
      chebyshevSecondConvexPotential_succ_sub_midpointClassicalPotential_sandwich
        hN (Nat.le_add_right N d)
    have hassoc : N + d + 1 = N + (d + 1) := by omega
    rw [hassoc] at hstep
    have hc_d : ((N + d : ℕ) : ℝ) - (N : ℝ) = (d : ℝ) := by push_cast; ring
    have hc_d1 : ((N + (d + 1) : ℕ) : ℝ) - (N : ℝ) = (d : ℝ) + 1 := by push_cast; ring
    rw [hc_d] at ih' hstep
    rw [hc_d1]
    have hpsi_mono :
        Chebyshev.psi ((N + d : ℕ) : ℝ) ≤ Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hsq_nonneg : 0 ≤ (d : ℝ) ^ 2 / 2 := by positivity
    have hd_nonneg : 0 ≤ (d : ℝ) + 1 / 2 := by positivity
    have ih_up := le_trans ih'.2 (mul_le_mul_of_nonneg_left hpsi_mono hsq_nonneg)
    have hstep_up := le_trans hstep.2 (mul_le_mul_of_nonneg_left hpsi_mono hd_nonneg)
    have halg_N :
        (((d : ℝ) + 1) ^ 2 / 2) * Chebyshev.psi (N : ℝ) =
          ((d : ℝ) ^ 2 / 2) * Chebyshev.psi (N : ℝ) +
            ((d : ℝ) + 1 / 2) * Chebyshev.psi (N : ℝ) := by ring
    have halg_M :
        (((d : ℝ) + 1) ^ 2 / 2) * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) =
          ((d : ℝ) ^ 2 / 2) * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) +
            ((d : ℝ) + 1 / 2) * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) := by ring
    constructor
    · linarith [ih'.1, hstep.1, halg_N]
    · linarith [ih_up, hstep_up, halg_M]

/-- **Pure Half-Square Backward Pointwise Quadratic Taylor Sandwich Around `chebyshevMidpointClassicalPotential`:**
For any `2 ≤ P ≤ N`, expanding `chebyshevSecondConvexPotential P` around `N` using the midpoint slope
`chebyshevMidpointClassicalPotential N = Φ₁(N) + (1 / 2) * ψ(N)` replaces the triangular weight
`(N - P) * (N - P - 1) / 2` by the exact half-square `(N - P)^2 / 2`:
`(((N - P)^2) / 2) * ψ(P) ≤
  (N - P) * chebyshevMidpointClassicalPotential N -
    (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential P) ≤
  (((N - P)^2) / 2) * ψ(N)`. -/
theorem chebyshevSecondConvexPotential_backward_midpointSlope_quadratic_taylor_sandwich
    {P N : ℕ} (hP : 2 ≤ P) (hPN : P ≤ N) :
    (((N : ℝ) - (P : ℝ)) ^ 2 / 2) * Chebyshev.psi (P : ℝ) ≤
      ((N : ℝ) - (P : ℝ)) * chebyshevMidpointClassicalPotential N -
        (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential P) ∧
    ((N : ℝ) - (P : ℝ)) * chebyshevMidpointClassicalPotential N -
        (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential P) ≤
      (((N : ℝ) - (P : ℝ)) ^ 2 / 2) * Chebyshev.psi (N : ℝ) := by
  have hbwd := chebyshevSecondConvexPotential_backward_quadratic_taylor_sandwich hP hPN
  have hpsi_mono : Chebyshev.psi (P : ℝ) ≤ Chebyshev.psi (N : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast hPN)
  have hspan_nonneg : 0 ≤ ((N : ℝ) - (P : ℝ)) / 2 := by
    have : (P : ℝ) ≤ (N : ℝ) := by exact_mod_cast hPN
    linarith
  have hmid_low := mul_le_mul_of_nonneg_left hpsi_mono hspan_nonneg
  unfold chebyshevMidpointClassicalPotential
  have halg_P :
      (((N : ℝ) - (P : ℝ)) ^ 2 / 2) * Chebyshev.psi (P : ℝ) =
        ((N : ℝ) - (P : ℝ)) * ((N : ℝ) - (P : ℝ) - 1) / 2 * Chebyshev.psi (P : ℝ) +
          (((N : ℝ) - (P : ℝ)) / 2) * Chebyshev.psi (P : ℝ) := by ring
  have halg_N :
      (((N : ℝ) - (P : ℝ)) ^ 2 / 2) * Chebyshev.psi (N : ℝ) =
        ((N : ℝ) - (P : ℝ)) * ((N : ℝ) - (P : ℝ) - 1) / 2 * Chebyshev.psi (N : ℝ) +
          (((N : ℝ) - (P : ℝ)) / 2) * Chebyshev.psi (N : ℝ) := by ring
  constructor
  · linarith [hbwd.1, hmid_low, halg_P]
  · linarith [hbwd.2, halg_N]

/-- **Symmetric Trapezoidal Forward Step Quadratic Taylor Sandwich Around `chebyshevMidpointClassicalPotential`:**
For any `2 ≤ N ≤ M`, averaging the pure half-square quadratic Taylor remainders at `M` and `M + 1`
gives the symmetric endpoint-average quadratic Taylor weight `((M - N)^2 + (M + 1 - N)^2) / 4`:
`((((M - N)^2 + (M + 1 - N)^2) / 4) * ψ(N) ≤
  (chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2 -
    chebyshevSecondConvexPotential N -
    (M + 1 / 2 - N) * chebyshevMidpointClassicalPotential N ≤
  ((((M - N)^2 + (M + 1 - N)^2) / 4) * ψ(M + 1)`. -/
theorem chebyshevSecondConvexPotential_trapezoidal_forward_midpointSlope_quadratic_taylor_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    ((((M : ℝ) - (N : ℝ)) ^ 2 + (((M + 1 : ℕ) : ℝ) - (N : ℝ)) ^ 2) / 4) *
        Chebyshev.psi (N : ℝ) ≤
      (chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2 -
        chebyshevSecondConvexPotential N -
        ((M : ℝ) + 1 / 2 - (N : ℝ)) * chebyshevMidpointClassicalPotential N ∧
    (chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2 -
        chebyshevSecondConvexPotential N -
        ((M : ℝ) + 1 / 2 - (N : ℝ)) * chebyshevMidpointClassicalPotential N ≤
      ((((M : ℝ) - (N : ℝ)) ^ 2 + (((M + 1 : ℕ) : ℝ) - (N : ℝ)) ^ 2) / 4) *
        Chebyshev.psi ((M + 1 : ℕ) : ℝ) := by
  have hM :=
    chebyshevSecondConvexPotential_forward_midpointSlope_quadratic_taylor_sandwich hN hNM
  have hM1 :=
    chebyshevSecondConvexPotential_forward_midpointSlope_quadratic_taylor_sandwich
      hN (show N ≤ M + 1 by omega)
  have hc1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  have hpsi_mono : Chebyshev.psi (M : ℝ) ≤ Chebyshev.psi ((M + 1 : ℕ) : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast (show M ≤ M + 1 by omega))
  have hw0_nonneg : 0 ≤ ((M : ℝ) - (N : ℝ)) ^ 2 / 2 := by positivity
  have hM_up := le_trans hM.2 (mul_le_mul_of_nonneg_left hpsi_mono hw0_nonneg)
  have halg_lhs :
      (chebyshevSecondConvexPotential M + chebyshevSecondConvexPotential (M + 1)) / 2 -
          chebyshevSecondConvexPotential N -
          ((M : ℝ) + 1 / 2 - (N : ℝ)) * chebyshevMidpointClassicalPotential N =
        ((chebyshevSecondConvexPotential M - chebyshevSecondConvexPotential N -
            ((M : ℝ) - (N : ℝ)) * chebyshevMidpointClassicalPotential N) +
          (chebyshevSecondConvexPotential (M + 1) - chebyshevSecondConvexPotential N -
            (((M + 1 : ℕ) : ℝ) - (N : ℝ)) * chebyshevMidpointClassicalPotential N)) / 2 := by
    rw [hc1]; ring
  rw [halg_lhs]
  constructor
  · linarith [hM.1, hM1.1]
  · linarith [hM_up, hM1.2]

/-- **Symmetric Trapezoidal Backward Step Quadratic Taylor Sandwich Around `chebyshevMidpointClassicalPotential`:**
For any `2 ≤ L ≤ P` with `P + 1 ≤ N`, averaging the pure half-square backward quadratic Taylor
remainders at `P` and `P + 1` gives the identical symmetric endpoint-average quadratic Taylor weight
`((N - P)^2 + (N - (P + 1))^2) / 4`:
`((((N - P)^2 + (N - (P + 1))^2) / 4) * ψ(L) ≤
  (N - 1 / 2 - P) * chebyshevMidpointClassicalPotential N -
    (chebyshevSecondConvexPotential N -
      (chebyshevSecondConvexPotential P + chebyshevSecondConvexPotential (P + 1)) / 2) ≤
  ((((N - P)^2 + (N - (P + 1))^2) / 4) * ψ(N)`. -/
theorem chebyshevSecondConvexPotential_trapezoidal_backward_midpointSlope_quadratic_taylor_sandwich
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P + 1 ≤ N) :
    ((((N : ℝ) - (P : ℝ)) ^ 2 + ((N : ℝ) - ((P + 1 : ℕ) : ℝ)) ^ 2) / 4) *
        Chebyshev.psi (L : ℝ) ≤
      ((N : ℝ) - 1 / 2 - (P : ℝ)) * chebyshevMidpointClassicalPotential N -
        (chebyshevSecondConvexPotential N -
          (chebyshevSecondConvexPotential P + chebyshevSecondConvexPotential (P + 1)) / 2) ∧
    ((N : ℝ) - 1 / 2 - (P : ℝ)) * chebyshevMidpointClassicalPotential N -
        (chebyshevSecondConvexPotential N -
          (chebyshevSecondConvexPotential P + chebyshevSecondConvexPotential (P + 1)) / 2) ≤
      ((((N : ℝ) - (P : ℝ)) ^ 2 + ((N : ℝ) - ((P + 1 : ℕ) : ℝ)) ^ 2) / 4) *
        Chebyshev.psi (N : ℝ) := by
  have hP2 : 2 ≤ P := le_trans hL hLP
  have hP :=
    chebyshevSecondConvexPotential_backward_midpointSlope_quadratic_taylor_sandwich
      hP2 (by omega : P ≤ N)
  have hP1 :=
    chebyshevSecondConvexPotential_backward_midpointSlope_quadratic_taylor_sandwich
      (show 2 ≤ P + 1 by omega) hPN
  have hc1 : ((P + 1 : ℕ) : ℝ) = (P : ℝ) + 1 := by push_cast; ring
  have hpsi_mono0 : Chebyshev.psi (L : ℝ) ≤ Chebyshev.psi (P : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast hLP)
  have hpsi_mono1 : Chebyshev.psi (L : ℝ) ≤ Chebyshev.psi ((P + 1 : ℕ) : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast (show L ≤ P + 1 by omega))
  have hw0_nonneg : 0 ≤ ((N : ℝ) - (P : ℝ)) ^ 2 / 2 := by positivity
  have hw1_nonneg : 0 ≤ ((N : ℝ) - ((P + 1 : ℕ) : ℝ)) ^ 2 / 2 := by positivity
  have hP_low := le_trans (mul_le_mul_of_nonneg_left hpsi_mono0 hw0_nonneg) hP.1
  have hP1_low := le_trans (mul_le_mul_of_nonneg_left hpsi_mono1 hw1_nonneg) hP1.1
  have halg_rhs :
      ((N : ℝ) - 1 / 2 - (P : ℝ)) * chebyshevMidpointClassicalPotential N -
          (chebyshevSecondConvexPotential N -
            (chebyshevSecondConvexPotential P + chebyshevSecondConvexPotential (P + 1)) / 2) =
        ((((N : ℝ) - (P : ℝ)) * chebyshevMidpointClassicalPotential N -
            (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential P)) +
          (((N : ℝ) - ((P + 1 : ℕ) : ℝ)) * chebyshevMidpointClassicalPotential N -
            (chebyshevSecondConvexPotential N - chebyshevSecondConvexPotential (P + 1)))) / 2 := by
    rw [hc1]; ring
  rw [halg_rhs]
  constructor
  · linarith [hP_low, hP1_low]
  · linarith [hP.2, hP1.2]

/-! ## Section 2: The Symmetric Midpoint-Slope Second-Order Trapezoidal Taylor Weights `W_{\mathrm{mid}, ±}`, Exact `+(1 / 4) * (√M - √N)` Shift Laws, and Forward/Backward Sandwiches -/

/-- **The Symmetric Midpoint-Slope Second-Order Forward Taylor Weight (`W_{\mathrm{mid}, +}(N, M)`) for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
`secularMidpointSlopeSecondOrderForwardWeight N M =
  secularTrapezoidalSecondOrderForwardWeight N M -
    (1 / 2) * ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
      (N - 1 / 2) * (√M - √N))`. -/
def secularMidpointSlopeSecondOrderForwardWeight (N M : ℕ) : ℝ :=
  secularTrapezoidalSecondOrderForwardWeight N M -
    (1 / 2 : ℝ) *
      ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
        ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)))

/-- **The Symmetric Midpoint-Slope Second-Order Backward Taylor Weight (`W_{\mathrm{mid}, -}^{\mathrm{aux}}(L, P, N)`) for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
`secularMidpointSlopeSecondOrderBackwardWeightAux L P N =
  secularTrapezoidalSecondOrderBackwardWeightAux L P N +
    (1 / 2) * ((N - 1 / 2) * (√P - √L) -
      (secularSqrtIncrementAction P - secularSqrtIncrementAction L))`. -/
def secularMidpointSlopeSecondOrderBackwardWeightAux (L P N : ℕ) : ℝ :=
  secularTrapezoidalSecondOrderBackwardWeightAux L P N +
    (1 / 2 : ℝ) *
      (((N : ℝ) - 1 / 2) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
        (secularSqrtIncrementAction P - secularSqrtIncrementAction L))

/-- **The Symmetric Midpoint-Slope Second-Order Backward Taylor Weight (`W_{\mathrm{mid}, -}(L, N)`) on `[L, N]`:**
`secularMidpointSlopeSecondOrderBackwardWeight L N =
  secularMidpointSlopeSecondOrderBackwardWeightAux L N N`. -/
def secularMidpointSlopeSecondOrderBackwardWeight (L N : ℕ) : ℝ :=
  secularMidpointSlopeSecondOrderBackwardWeightAux L N N

@[simp]
theorem secularMidpointSlopeSecondOrderForwardWeight_self (N : ℕ) :
    secularMidpointSlopeSecondOrderForwardWeight N N = 0 := by
  unfold secularMidpointSlopeSecondOrderForwardWeight
  simp

@[simp]
theorem secularMidpointSlopeSecondOrderBackwardWeightAux_self (L N : ℕ) :
    secularMidpointSlopeSecondOrderBackwardWeightAux L L N = 0 := by
  unfold secularMidpointSlopeSecondOrderBackwardWeightAux
  simp

@[simp]
theorem secularMidpointSlopeSecondOrderBackwardWeight_self (N : ℕ) :
    secularMidpointSlopeSecondOrderBackwardWeight N N = 0 := by
  unfold secularMidpointSlopeSecondOrderBackwardWeight
  simp

/-- **Exact `+(1 / 4) * (√M - √N)` Radical Shift Law Relating `secularMidpointSlopeSecondOrderForwardWeight` and `secularSecondOrderForwardWeight`:**
Because `(k^2 + (k + 1)^2) / 4 = k(k + 1) / 2 + 1 / 4` identically for all `k`, the midpoint-slope
trapezoidal forward weight differs from the left-endpoint forward weight by `+(1 / 4) * (√M - √N)`:
`secularMidpointSlopeSecondOrderForwardWeight N M =
  secularSecondOrderForwardWeight N M + (1 / 4) * (√M - √N)`. -/
theorem secularMidpointSlopeSecondOrderForwardWeight_eq_add_quarter_sqrt_sub (N M : ℕ) :
    secularMidpointSlopeSecondOrderForwardWeight N M =
      secularSecondOrderForwardWeight N M +
        (1 / 4 : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) := by
  unfold secularMidpointSlopeSecondOrderForwardWeight secularTrapezoidalSecondOrderForwardWeight
  ring

/-- **Exact `+(1 / 4) * (√P - √L)` Radical Shift Law Relating `secularMidpointSlopeSecondOrderBackwardWeightAux` and `secularSecondOrderBackwardWeightAux`:**
For any `L, P, N : ℕ`,
`secularMidpointSlopeSecondOrderBackwardWeightAux L P N =
  secularSecondOrderBackwardWeightAux L P N + (1 / 4) * (√P - √L)`. -/
theorem secularMidpointSlopeSecondOrderBackwardWeightAux_eq_add_quarter_sqrt_sub (L P N : ℕ) :
    secularMidpointSlopeSecondOrderBackwardWeightAux L P N =
      secularSecondOrderBackwardWeightAux L P N +
        (1 / 4 : ℝ) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) := by
  unfold secularMidpointSlopeSecondOrderBackwardWeightAux
    secularTrapezoidalSecondOrderBackwardWeightAux
  ring

/-- **Closed-Form Expression for `secularMidpointSlopeSecondOrderForwardWeight` in Terms of `secularTrapezoidalSqrtRieszAction` and `secularSqrtIncrementAction`:**
For any `N, M : ℕ`, both the outer and inner shift constants equal `N - 1 / 2`:
`secularMidpointSlopeSecondOrderForwardWeight N M =
  (secularTrapezoidalSqrtRieszAction M - secularTrapezoidalSqrtRieszAction N) -
  secularClassicalCesaroSum N * (√M - √N) -
  (N - 1 / 2) * ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
    (N - 1 / 2) * (√M - √N))`. -/
theorem secularMidpointSlopeSecondOrderForwardWeight_eq (N M : ℕ) :
    secularMidpointSlopeSecondOrderForwardWeight N M =
      (secularTrapezoidalSqrtRieszAction M - secularTrapezoidalSqrtRieszAction N) -
        secularClassicalCesaroSum N *
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) -
        ((N : ℝ) - 1 / 2) *
          ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
            ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) := by
  unfold secularMidpointSlopeSecondOrderForwardWeight secularTrapezoidalSecondOrderForwardWeight
    secularSecondOrderForwardWeight secularTrapezoidalSqrtRieszAction
  ring

/-- **Closed-Form Expression for `secularMidpointSlopeSecondOrderBackwardWeight` in Terms of `secularTrapezoidalSqrtRieszAction` and `secularSqrtIncrementAction`:**
For any `L, N : ℕ`, both the outer and inner shift constants equal `N - 1 / 2`:
`secularMidpointSlopeSecondOrderBackwardWeight L N =
  (secularTrapezoidalSqrtRieszAction N - secularTrapezoidalSqrtRieszAction L) -
  secularClassicalCesaroSum N * (√N - √L) +
  (N - 1 / 2) * ((N - 1 / 2) * (√N - √L) -
    (secularSqrtIncrementAction N - secularSqrtIncrementAction L))`. -/
theorem secularMidpointSlopeSecondOrderBackwardWeight_eq (L N : ℕ) :
    secularMidpointSlopeSecondOrderBackwardWeight L N =
      (secularTrapezoidalSqrtRieszAction N - secularTrapezoidalSqrtRieszAction L) -
        secularClassicalCesaroSum N *
          (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) +
        ((N : ℝ) - 1 / 2) *
          (((N : ℝ) - 1 / 2) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
            (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) := by
  unfold secularMidpointSlopeSecondOrderBackwardWeight
    secularMidpointSlopeSecondOrderBackwardWeightAux
    secularTrapezoidalSecondOrderBackwardWeightAux
    secularSecondOrderBackwardWeightAux secularTrapezoidalSqrtRieszAction
  ring

/-- **Symmetric Step Recurrence for `secularMidpointSlopeSecondOrderForwardWeight`:**
For any `2 ≤ N ≤ M`,
`secularMidpointSlopeSecondOrderForwardWeight N (M + 1) -
  secularMidpointSlopeSecondOrderForwardWeight N M =
    (√(M + 1) - √M) * (((M - N)^2 + (M + 1 - N)^2) / 4)`. -/
theorem secularMidpointSlopeSecondOrderForwardWeight_succ_sub
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    secularMidpointSlopeSecondOrderForwardWeight N (M + 1) -
        secularMidpointSlopeSecondOrderForwardWeight N M =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        ((((M : ℝ) - (N : ℝ)) ^ 2 + (((M + 1 : ℕ) : ℝ) - (N : ℝ)) ^ 2) / 4) := by
  have hM2 : 2 ≤ M := le_trans hN hNM
  have hW := secularTrapezoidalSecondOrderForwardWeight_succ_sub hN hNM
  have hI := secularSqrtIncrementAction_succ_sub_of_two_le (M - 2)
  have hi3 : M - 2 + 3 = M + 1 := by omega
  have hi2 : M - 2 + 2 = M := by omega
  have hc3 : ((M - 2 : ℕ) : ℝ) + 3 = ((M + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hM2]; push_cast; ring
  have hc2 : ((M - 2 : ℕ) : ℝ) + 2 = (M : ℝ) := by
    rw [Nat.cast_sub hM2]; push_cast; ring
  rw [hi3, hi2, hc3, hc2] at hI
  have hc1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  unfold secularMidpointSlopeSecondOrderForwardWeight
  rw [hc1] at hW hI ⊢
  linear_combination hW - (1 / 2 : ℝ) * hI

/-- **Symmetric Step Recurrence for `secularMidpointSlopeSecondOrderBackwardWeightAux`:**
For any `2 ≤ L ≤ P ≤ N`,
`secularMidpointSlopeSecondOrderBackwardWeightAux L (P + 1) N -
  secularMidpointSlopeSecondOrderBackwardWeightAux L P N =
    (√(P + 1) - √P) * (((N - P)^2 + (N - (P + 1))^2) / 4)`. -/
theorem secularMidpointSlopeSecondOrderBackwardWeightAux_succ_sub
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    secularMidpointSlopeSecondOrderBackwardWeightAux L (P + 1) N -
        secularMidpointSlopeSecondOrderBackwardWeightAux L P N =
      (Real.sqrt ((P + 1 : ℕ) : ℝ) - Real.sqrt (P : ℝ)) *
        ((((N : ℝ) - (P : ℝ)) ^ 2 + ((N : ℝ) - ((P + 1 : ℕ) : ℝ)) ^ 2) / 4) := by
  have hP2 : 2 ≤ P := le_trans hL hLP
  have hW := secularTrapezoidalSecondOrderBackwardWeightAux_succ_sub hL hLP hPN
  have hI := secularSqrtIncrementAction_succ_sub_of_two_le (P - 2)
  have hi3 : P - 2 + 3 = P + 1 := by omega
  have hi2 : P - 2 + 2 = P := by omega
  have hc3 : ((P - 2 : ℕ) : ℝ) + 3 = ((P + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hP2]; push_cast; ring
  have hc2 : ((P - 2 : ℕ) : ℝ) + 2 = (P : ℝ) := by
    rw [Nat.cast_sub hP2]; push_cast; ring
  rw [hi3, hi2, hc3, hc2] at hI
  have hc1 : ((P + 1 : ℕ) : ℝ) = (P : ℝ) + 1 := by push_cast; ring
  unfold secularMidpointSlopeSecondOrderBackwardWeightAux
  rw [hc1] at hW hI ⊢
  linear_combination hW - (1 / 2 : ℝ) * hI

/-- **Non-Negativity of `secularMidpointSlopeSecondOrderForwardWeight N M`:**
For any `2 ≤ N ≤ M`, `0 ≤ secularMidpointSlopeSecondOrderForwardWeight N M`. -/
theorem secularMidpointSlopeSecondOrderForwardWeight_nonneg
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    0 ≤ secularMidpointSlopeSecondOrderForwardWeight N M := by
  rw [secularMidpointSlopeSecondOrderForwardWeight_eq_add_quarter_sqrt_sub]
  have h1 := secularSecondOrderForwardWeight_nonneg hN hNM
  have h2 : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hNM)
  linarith

/-- **Non-Negativity of `secularMidpointSlopeSecondOrderBackwardWeightAux L P N`:**
For any `2 ≤ L ≤ P ≤ N`, `0 ≤ secularMidpointSlopeSecondOrderBackwardWeightAux L P N`. -/
theorem secularMidpointSlopeSecondOrderBackwardWeightAux_nonneg
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    0 ≤ secularMidpointSlopeSecondOrderBackwardWeightAux L P N := by
  rw [secularMidpointSlopeSecondOrderBackwardWeightAux_eq_add_quarter_sqrt_sub]
  have h1 := secularSecondOrderBackwardWeightAux_nonneg hL hLP hPN
  have h2 : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ) := by
    rw [sub_nonneg]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hLP)
  linarith

/-- **Non-Negativity of `secularMidpointSlopeSecondOrderBackwardWeight L N`:**
For any `2 ≤ L ≤ N`, `0 ≤ secularMidpointSlopeSecondOrderBackwardWeight L N`. -/
theorem secularMidpointSlopeSecondOrderBackwardWeight_nonneg
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    0 ≤ secularMidpointSlopeSecondOrderBackwardWeight L N :=
  secularMidpointSlopeSecondOrderBackwardWeightAux_nonneg hL hLN le_rfl

/-- **Exact Forward Midpoint-Slope Second-Order Quadratic Taylor Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `2 ≤ N ≤ M`,
`secularMidpointSlopeSecondOrderForwardWeight N M * ψ(N) ≤
  (chebyshevTrapezoidalSecondSqrtRieszPotential M - chebyshevTrapezoidalSecondSqrtRieszPotential N -
    (√M - √N) * chebyshevSecondConvexPotential N) -
  ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) - (N - 1 / 2) * (√M - √N)) *
    chebyshevMidpointClassicalPotential N ≤
  secularMidpointSlopeSecondOrderForwardWeight N M * ψ(M)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_forward_midpointSlope_quadratic_taylor_sandwich
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    secularMidpointSlopeSecondOrderForwardWeight N M * Chebyshev.psi (N : ℝ) ≤
      (chebyshevTrapezoidalSecondSqrtRieszPotential M -
          chebyshevTrapezoidalSecondSqrtRieszPotential N -
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N) -
        ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
            ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
          chebyshevMidpointClassicalPotential N ∧
    (chebyshevTrapezoidalSecondSqrtRieszPotential M -
          chebyshevTrapezoidalSecondSqrtRieszPotential N -
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSecondConvexPotential N) -
        ((secularSqrtIncrementAction M - secularSqrtIncrementAction N) -
            ((N : ℝ) - 1 / 2) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
          chebyshevMidpointClassicalPotential N ≤
      secularMidpointSlopeSecondOrderForwardWeight N M * Chebyshev.psi (M : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNM
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have ih' := ih (Nat.le_add_right N d)
    have hP_step :=
      chebyshevTrapezoidalSecondSqrtRieszPotential_succ_sub (show 2 ≤ N + d by omega)
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (N + d - 2)
    have hi3 : N + d - 2 + 3 = N + (d + 1) := by omega
    have hi2 : N + d - 2 + 2 = N + d := by omega
    have hc3 : ((N + d - 2 : ℕ) : ℝ) + 3 = ((N + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((N + d - 2 : ℕ) : ℝ) + 2 = ((N + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hI_step
    have hassoc : N + d + 1 = N + (d + 1) := by omega
    have hW_step :=
      secularMidpointSlopeSecondOrderForwardWeight_succ_sub hN (Nat.le_add_right N d)
    have hPhi2 :=
      chebyshevSecondConvexPotential_trapezoidal_forward_midpointSlope_quadratic_taylor_sandwich
        hN (Nat.le_add_right N d)
    rw [hassoc] at hP_step hW_step hPhi2
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((N + (d + 1) : ℕ) : ℝ) - Real.sqrt ((N + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hstep_low := mul_le_mul_of_nonneg_left hPhi2.1 hsqrt_nonneg
    have hstep_up := mul_le_mul_of_nonneg_left hPhi2.2 hsqrt_nonneg
    have hpsi_mono :
        Chebyshev.psi ((N + d : ℕ) : ℝ) ≤ Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ) :=
      Chebyshev.psi_mono (by exact_mod_cast (show N + d ≤ N + (d + 1) by omega))
    have hW_nonneg :=
      secularMidpointSlopeSecondOrderForwardWeight_nonneg hN (Nat.le_add_right N d)
    have ih_up_upgraded := le_trans ih'.2 (mul_le_mul_of_nonneg_left hpsi_mono hW_nonneg)
    constructor
    · linarith [ih'.1, hstep_low, hP_step,
        congrArg (fun x => x * chebyshevMidpointClassicalPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi (N : ℝ)) hW_step]
    · linarith [ih_up_upgraded, hstep_up, hP_step,
        congrArg (fun x => x * chebyshevMidpointClassicalPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi ((N + (d + 1) : ℕ) : ℝ)) hW_step]

/-- Auxiliary backward midpoint-slope second-order quadratic Taylor sandwich for
`chebyshevTrapezoidalSecondSqrtRieszPotential` on `2 ≤ L ≤ P ≤ N`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_backward_midpointSlope_quadratic_taylor_sandwich_aux
    {L P N : ℕ} (hL : 2 ≤ L) (hLP : L ≤ P) (hPN : P ≤ N) :
    secularMidpointSlopeSecondOrderBackwardWeightAux L P N * Chebyshev.psi (L : ℝ) ≤
      (((N : ℝ) - 1 / 2) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        chebyshevMidpointClassicalPotential N -
      ((Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential P -
          chebyshevTrapezoidalSecondSqrtRieszPotential L)) ∧
    (((N : ℝ) - 1 / 2) * (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction P - secularSqrtIncrementAction L)) *
        chebyshevMidpointClassicalPotential N -
      ((Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential P -
          chebyshevTrapezoidalSecondSqrtRieszPotential L)) ≤
      secularMidpointSlopeSecondOrderBackwardWeightAux L P N * Chebyshev.psi (N : ℝ) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLP
  induction d with
  | zero =>
    simp
  | succ d ih =>
    have hLd_le_N : L + d ≤ N := by omega
    have ih' := ih (Nat.le_add_right L d) hLd_le_N
    have hP_step :=
      chebyshevTrapezoidalSecondSqrtRieszPotential_succ_sub (show 2 ≤ L + d by omega)
    have hI_step := secularSqrtIncrementAction_succ_sub_of_two_le (L + d - 2)
    have hi3 : L + d - 2 + 3 = L + (d + 1) := by omega
    have hi2 : L + d - 2 + 2 = L + d := by omega
    have hc3 : ((L + d - 2 : ℕ) : ℝ) + 3 = ((L + (d + 1) : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((L + d - 2 : ℕ) : ℝ) + 2 = ((L + d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [hi3, hi2, hc3, hc2] at hI_step
    have hassoc : L + d + 1 = L + (d + 1) := by omega
    have hW_step :=
      secularMidpointSlopeSecondOrderBackwardWeightAux_succ_sub hL (Nat.le_add_right L d) hLd_le_N
    have hPhi2 :=
      chebyshevSecondConvexPotential_trapezoidal_backward_midpointSlope_quadratic_taylor_sandwich
        hL (Nat.le_add_right L d) (show L + d + 1 ≤ N by omega)
    rw [hassoc] at hP_step hW_step hPhi2
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((L + (d + 1) : ℕ) : ℝ) - Real.sqrt ((L + d : ℕ) : ℝ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show L + d ≤ L + (d + 1) by omega))
    have hstep_low := mul_le_mul_of_nonneg_left hPhi2.1 hsqrt_nonneg
    have hstep_up := mul_le_mul_of_nonneg_left hPhi2.2 hsqrt_nonneg
    constructor
    · linarith [ih'.1, hstep_low, hP_step,
        congrArg (fun x => x * chebyshevMidpointClassicalPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi (L : ℝ)) hW_step]
    · linarith [ih'.2, hstep_up, hP_step,
        congrArg (fun x => x * chebyshevMidpointClassicalPotential N) hI_step,
        congrArg (fun x => x * Chebyshev.psi (N : ℝ)) hW_step]

/-- **Exact Backward Midpoint-Slope Second-Order Quadratic Taylor Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `2 ≤ L ≤ N`,
`secularMidpointSlopeSecondOrderBackwardWeight L N * ψ(L) ≤
  ((N - 1 / 2) * (√N - √L) - (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
    chebyshevMidpointClassicalPotential N -
  ((√N - √L) * chebyshevSecondConvexPotential N -
    (chebyshevTrapezoidalSecondSqrtRieszPotential N - chebyshevTrapezoidalSecondSqrtRieszPotential L)) ≤
  secularMidpointSlopeSecondOrderBackwardWeight L N * ψ(N)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_backward_midpointSlope_quadratic_taylor_sandwich
    {L N : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) :
    secularMidpointSlopeSecondOrderBackwardWeight L N * Chebyshev.psi (L : ℝ) ≤
      (((N : ℝ) - 1 / 2) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        chebyshevMidpointClassicalPotential N -
      ((Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential N -
          chebyshevTrapezoidalSecondSqrtRieszPotential L)) ∧
    (((N : ℝ) - 1 / 2) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) -
          (secularSqrtIncrementAction N - secularSqrtIncrementAction L)) *
        chebyshevMidpointClassicalPotential N -
      ((Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSecondConvexPotential N -
        (chebyshevTrapezoidalSecondSqrtRieszPotential N -
          chebyshevTrapezoidalSecondSqrtRieszPotential L)) ≤
      secularMidpointSlopeSecondOrderBackwardWeight L N * Chebyshev.psi (N : ℝ) :=
  chebyshevTrapezoidalSecondSqrtRieszPotential_backward_midpointSlope_quadratic_taylor_sandwich_aux
    hL hLN le_rfl

/-! ## Section 3: Pure-Monomial `m * h^4` Weight Difference, 4-Term Euler–Maclaurin Polynomials `E_{W_{\mathrm{mid}, ±}}(m, h)`, and Centered Three-Square `(C₁^{\mathrm{mid}}(m^2), ψ(m^2) - m^2)` Sandwiches -/

/-- **Exact Three-Square Weight Difference Identity for `secularMidpointSlopeSecondOrderWeight`:**
For any `h ≤ m`, subtracting `secularMidpointSlopeSecondOrderBackwardWeight ((m - h)^2) (m^2)` from
`secularMidpointSlopeSecondOrderForwardWeight (m^2) ((m + h)^2)` cancels the `± (1 / 4) * h` shifts
and yields:
`secularMidpointSlopeSecondOrderForwardWeight (m^2) ((m + h)^2) -
  secularMidpointSlopeSecondOrderBackwardWeight ((m - h)^2) (m^2) =
    (secularTrapezoidalSqrtRieszAction ((m + h)^2) - 2 * secularTrapezoidalSqrtRieszAction (m^2) +
      secularTrapezoidalSqrtRieszAction ((m - h)^2)) -
    (m^2 - 1 / 2) * (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) +
      secularSqrtIncrementAction ((m - h)^2))`. -/
theorem secularMidpointSlopeSecondOrderWeight_three_square_sub_eq
    {m h : ℕ} (hmh : h ≤ m) :
    secularMidpointSlopeSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) -
        secularMidpointSlopeSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) =
      (secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
          2 * secularTrapezoidalSqrtRieszAction (m ^ 2) +
          secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2)) := by
  have h1 := secularTrapezoidalSecondOrderWeight_three_square_sub_eq hmh
  unfold secularTrapezoidalSecondOrderBackwardWeight at h1
  unfold secularMidpointSlopeSecondOrderForwardWeight
    secularMidpointSlopeSecondOrderBackwardWeight
    secularMidpointSlopeSecondOrderBackwardWeightAux
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  linear_combination h1

/-- **Pure-Monomial `m * h^4` Weight Cancellation for `eulerMaclaurinTrapezoidalSqrtRieszSecular`:**
For any `h ≤ m`, subtracting `(m^2 - 1 / 2) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)` from
`Δ²_{sq, h} eulerMaclaurinTrapezoidalSqrtRieszSecular(m)` cancels BOTH `2 * m^3 * h^2` AND
`-m * h^2` identically, leaving the pure monomial `m * h^4`. -/
theorem eulerMaclaurinTrapezoidalSqrtRiesz_sub_sq_sub_half_mul_increment_square_second_diff_eq
    {m h : ℕ} (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
      (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) =
      (m : ℝ) * (h : ℝ) ^ 4 := by
  rw [eulerMaclaurinTrapezoidalSqrtRieszSecular_square_second_diff_eq hmh,
    eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq hmh]
  push_cast
  ring

/-- **Four-Term Square-Grid Evaluation of the Euler–Maclaurin Counterpart of `secularMidpointSlopeSecondOrderForwardWeight`:**
For any `2 ≤ m` and `h : ℕ`, both `+(1 / 2) * h^2 * m` and `+(1 / 6) * h^3` cancel identically:
`(eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h)^2) - eulerMaclaurinTrapezoidalSqrtRieszSecular (m^2)) -
  secularClassicalCesaroSum (m^2) * h -
  (m^2 - 1 / 2) * ((eulerMaclaurinSqrtIncrementSecular ((m + h)^2) - eulerMaclaurinSqrtIncrementSecular (m^2)) -
    (m^2 - 1 / 2) * h) =
  (2 / 3) * h^3 * m^2 + (1 / 2) * h^4 * m + (1 / 10) * h^5 + (1 / 8) * h`. -/
theorem eulerMaclaurinMidpointSlopeSecondOrderForwardWeight_sq_eq
    {m : ℕ} (hm : 2 ≤ m) (h : ℕ) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2)) -
      secularClassicalCesaroSum (m ^ 2) * (h : ℝ) -
      (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular (m ^ 2)) -
          (((m ^ 2 : ℕ) : ℝ) - 1 / 2) * (h : ℝ)) =
      (2 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 +
        (1 / 2 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) +
        (1 / 10 : ℝ) * (h : ℝ) ^ 5 +
        (1 / 8 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq (m + h),
    eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq m,
    eulerMaclaurinSqrtIncrementSecular_sq_eq (m + h),
    eulerMaclaurinSqrtIncrementSecular_sq_eq m,
    secularClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- **Four-Term Square-Grid Evaluation of the Euler–Maclaurin Counterpart of `secularMidpointSlopeSecondOrderBackwardWeight`:**
For any `2 ≤ m` and `h ≤ m`, the backward polynomial is the exact `m ↦ -m` parity reflection of the
4-term forward polynomial:
`(eulerMaclaurinTrapezoidalSqrtRieszSecular (m^2) - eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h)^2)) -
  secularClassicalCesaroSum (m^2) * h +
  (m^2 - 1 / 2) * ((m^2 - 1 / 2) * h -
    (eulerMaclaurinSqrtIncrementSecular (m^2) - eulerMaclaurinSqrtIncrementSecular ((m - h)^2))) =
  (2 / 3) * h^3 * m^2 - (1 / 2) * h^4 * m + (1 / 10) * h^5 + (1 / 8) * h`. -/
theorem eulerMaclaurinMidpointSlopeSecondOrderBackwardWeight_sq_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) -
        eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
      secularClassicalCesaroSum (m ^ 2) * (h : ℝ) +
      (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
        ((((m ^ 2 : ℕ) : ℝ) - 1 / 2) * (h : ℝ) -
          (eulerMaclaurinSqrtIncrementSecular (m ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) =
      (2 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 -
        (1 / 2 : ℝ) * (h : ℝ) ^ 4 * (m : ℝ) +
        (1 / 10 : ℝ) * (h : ℝ) ^ 5 +
        (1 / 8 : ℝ) * (h : ℝ) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq m,
    eulerMaclaurinTrapezoidalSqrtRieszSecular_sq_eq (m - h),
    eulerMaclaurinSqrtIncrementSecular_sq_eq m,
    eulerMaclaurinSqrtIncrementSecular_sq_eq (m - h),
    secularClassicalCesaroSum_eq hm2]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  rw [hc_sub]
  push_cast
  ring

/-- **Exact Three-Square Weight Sum Identity for `secularMidpointSlopeSecondOrderWeight`:**
For any `h ≤ m`,
`secularMidpointSlopeSecondOrderForwardWeight (m^2) ((m + h)^2) +
  secularMidpointSlopeSecondOrderBackwardWeight ((m - h)^2) (m^2) =
    (secularTrapezoidalSqrtRieszAction ((m + h)^2) - secularTrapezoidalSqrtRieszAction ((m - h)^2)) -
    2 * h * secularClassicalCesaroSum (m^2) -
    (m^2 - 1 / 2) * ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
      (2 * m^2 - 1) * h)`. -/
theorem secularMidpointSlopeSecondOrderWeight_three_square_add_eq
    {m h : ℕ} (hmh : h ≤ m) :
    secularMidpointSlopeSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) +
        secularMidpointSlopeSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) =
      (secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
          secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
        2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
        (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) := by
  have h1 := secularTrapezoidalSecondOrderWeight_three_square_add_eq hmh
  unfold secularTrapezoidalSecondOrderBackwardWeight at h1
  unfold secularMidpointSlopeSecondOrderForwardWeight
    secularMidpointSlopeSecondOrderBackwardWeight
    secularMidpointSlopeSecondOrderBackwardWeightAux
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq (m - h)]
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub hmh
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  rw [hc_sub, hc_add]
  linear_combination h1

/-- **Three-Term Purely Even-in-`m` Central-Difference Weight Sum Identity for `eulerMaclaurinMidpointSlopeSecondOrderWeight`:**
For any `2 ≤ m` and `h ≤ m`, adding the forward and backward Euler–Maclaurin midpoint-slope weight
polynomials cancels `± (1 / 2) * h^4 * m` identically and has no `h^3` constant term:
`(eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h)^2) - eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h)^2)) -
  2 * h * secularClassicalCesaroSum (m^2) -
  (m^2 - 1 / 2) * ((eulerMaclaurinSqrtIncrementSecular ((m + h)^2) - eulerMaclaurinSqrtIncrementSecular ((m - h)^2)) -
    (2 * m^2 - 1) * h) =
  (4 / 3) * h^3 * m^2 + (1 / 5) * h^5 + (1 / 4) * h`. -/
theorem eulerMaclaurinMidpointSlopeSecondOrderWeight_three_square_add_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
        eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
      2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
      (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) =
      (4 / 3 : ℝ) * (h : ℝ) ^ 3 * (m : ℝ) ^ 2 +
        (1 / 5 : ℝ) * (h : ℝ) ^ 5 +
        (1 / 4 : ℝ) * (h : ℝ) := by
  have h1 := eulerMaclaurinMidpointSlopeSecondOrderForwardWeight_sq_eq hm h
  have h2 := eulerMaclaurinMidpointSlopeSecondOrderBackwardWeight_sq_eq hm hmh
  linarith

/-- **Centered Three-Square `(Φ₁^{\mathrm{mid}}(m^2), ψ(m^2))` Lower Bound for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `h + 2 ≤ m`, subtracting the backward midpoint-slope quadratic Taylor upper bound from the
forward midpoint-slope quadratic Taylor lower bound across `((m - h)^2, m^2, (m + h)^2)` yields:
`((secularTrapezoidalSqrtRieszAction ((m + h)^2) - 2 * secularTrapezoidalSqrtRieszAction (m^2) +
    secularTrapezoidalSqrtRieszAction ((m - h)^2)) -
  (m^2 - 1 / 2) * (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) +
    secularSqrtIncrementAction ((m - h)^2))) * ψ(m^2) ≤
  (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h)^2) -
    2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m^2) +
    chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h)^2)) -
  (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) +
    secularSqrtIncrementAction ((m - h)^2)) * chebyshevMidpointClassicalPotential (m^2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_centered_midpointPhi1_psi_ge
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    ((secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
          2 * secularTrapezoidalSqrtRieszAction (m ^ 2) +
          secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2))) *
      Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) ≤
      (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2)) -
        (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2)) *
          chebyshevMidpointClassicalPotential (m ^ 2) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd :=
    (chebyshevTrapezoidalSecondSqrtRieszPotential_forward_midpointSlope_quadratic_taylor_sandwich
      hm2 hle2).1
  have hbwd :=
    (chebyshevTrapezoidalSecondSqrtRieszPotential_backward_midpointSlope_quadratic_taylor_sandwich
      hm_sub2 hle1).2
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd
  rw [hspan_bwd] at hbwd
  have hW := secularMidpointSlopeSecondOrderWeight_three_square_sub_eq (show h ≤ m by omega)
  linarith [congrArg (fun x => x * Chebyshev.psi ((m ^ 2 : ℕ) : ℝ)) hW]

/-- **Complementary Centered Three-Square `(Φ₁^{\mathrm{mid}}(m^2), ψ)` Upper Bound for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `h + 2 ≤ m`, subtracting the backward midpoint-slope quadratic Taylor lower bound from the
forward midpoint-slope quadratic Taylor upper bound across `((m - h)^2, m^2, (m + h)^2)` yields:
`(chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h)^2) -
  2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m^2) +
  chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h)^2)) -
  (secularSqrtIncrementAction ((m + h)^2) - 2 * secularSqrtIncrementAction (m^2) +
    secularSqrtIncrementAction ((m - h)^2)) * chebyshevMidpointClassicalPotential (m^2) ≤
  secularMidpointSlopeSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ((m + h)^2) -
    secularMidpointSlopeSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ((m - h)^2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_centered_midpointPhi1_psi_le
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
        2 * chebyshevTrapezoidalSecondSqrtRieszPotential (m ^ 2) +
        chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2)) -
      (secularSqrtIncrementAction ((m + h) ^ 2) -
          2 * secularSqrtIncrementAction (m ^ 2) +
          secularSqrtIncrementAction ((m - h) ^ 2)) *
        chebyshevMidpointClassicalPotential (m ^ 2) ≤
      secularMidpointSlopeSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
          Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) -
        secularMidpointSlopeSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
          Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd :=
    (chebyshevTrapezoidalSecondSqrtRieszPotential_forward_midpointSlope_quadratic_taylor_sandwich
      hm2 hle2).2
  have hbwd :=
    (chebyshevTrapezoidalSecondSqrtRieszPotential_backward_midpointSlope_quadratic_taylor_sandwich
      hm_sub2 hle1).1
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd
  rw [hspan_bwd] at hbwd
  linarith

/-- **Quintic-and-Cubic Cancelling Square-Grid Second-Difference Identity for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular` Subtracting `S₁^{\mathrm{mid}}(m^2) * Δ²_{sq, h} E_{F_√}(m)`:**
For any `2 ≤ m` and `h ≤ m`, subtracting `secularMidpointClassicalCesaroSum (m^2) * Δ²_{sq, h} eulerMaclaurinSqrtIncrementSecular(m)`
from `Δ²_{sq, h} eulerMaclaurinTrapezoidalSecondSqrtRieszSecular(m)` cancels `m^5 * h^2` AND the
`m^3 * h^2` term (reducing `-17 / 8` to `-1 / 8`), leaving
`m * h^2 * ((5 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 1 / 8)`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRiesz_sub_secularMidpointC1_center_mul_increment_square_second_diff_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
      secularMidpointClassicalCesaroSum (m ^ 2) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((5 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 +
          (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 1 / 8) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [eulerMaclaurinTrapezoidalSecondSqrtRieszSecular_square_second_diff_eq hmh,
    eulerMaclaurinSqrtIncrementSecular_square_second_diff_eq hmh,
    secularMidpointClassicalCesaroSum_eq hm2]
  push_cast
  ring

/-- **Exact Three-Term Centered Midpoint-Slope Secular Cancellation Identity for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`, subtracting both `secularMidpointClassicalCesaroSum (m^2) * Δ²_{sq, h} E_{F_√}(m)`
and `(Δ²_{sq, h} E_{R_√^{(1, trap)}}(m) - (m^2 - 1 / 2) * Δ²_{sq, h} E_{F_√}(m)) * m^2` from
`Δ²_{sq, h} eulerMaclaurinTrapezoidalSecondSqrtRieszSecular(m)` yields
`m * h^2 * ((2 / 3) * m^2 * h^2 + (1 / 3) * h^4 - 1 / 8)`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRiesz_centered_midpointSlope_three_square_secular_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
        2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) +
        eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
      secularMidpointClassicalCesaroSum (m ^ 2) *
        (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
      ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) +
          eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
          (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) *
        ((m ^ 2 : ℕ) : ℝ) =
      (m : ℝ) * (h : ℝ) ^ 2 *
        ((2 / 3 : ℝ) * (m : ℝ) ^ 2 * (h : ℝ) ^ 2 + (1 / 3 : ℝ) * (h : ℝ) ^ 4 - 1 / 8) := by
  have h1 :=
    eulerMaclaurinTrapezoidalSecondSqrtRiesz_sub_secularMidpointC1_center_mul_increment_square_second_diff_eq
      hm hmh
  have h2 :=
    eulerMaclaurinTrapezoidalSqrtRiesz_sub_sq_sub_half_mul_increment_square_second_diff_eq hmh
  have hc_m2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have halg :
      (eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) +
          eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
        secularMidpointClassicalCesaroSum (m ^ 2) *
          (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
        ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) +
            eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
          (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
            (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
               2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
               eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) *
          ((m ^ 2 : ℕ) : ℝ) =
      ((eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
          2 * eulerMaclaurinTrapezoidalSecondSqrtRieszSecular (m ^ 2) +
          eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
        secularMidpointClassicalCesaroSum (m ^ 2) *
          (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) -
        ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
            2 * eulerMaclaurinTrapezoidalSqrtRieszSecular (m ^ 2) +
            eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
          (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
            (eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
              2 * eulerMaclaurinSqrtIncrementSecular (m ^ 2) +
              eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2))) *
          ((m ^ 2 : ℕ) : ℝ) := by
    ring
  rw [halg, h1, h2, hc_m2]
  ring

/-- **Centered Three-Square Coupled `(C₁^{\mathrm{mid}}(m^2), ψ(m^2) - m^2)` Inequality with Pure-Monomial `m * h^4` Weight:**
For any `h + 2 ≤ m`, subtracting `secularMidpointClassicalCesaroSum (m^2)` from
`chebyshevMidpointClassicalPotential (m^2)` and `m^2` from `ψ(m^2)` gives:
`Δ²_{sq, h} secularSqrtIncrementAction(m) * chebyshevMidpointClassicalCesaroSum (m^2) +
  (Δ²_{sq, h} secularTrapezoidalSqrtRieszAction(m) - (m^2 - 1 / 2) * Δ²_{sq, h} secularSqrtIncrementAction(m)) *
    (ψ(m^2) - m^2) ≤
  Δ²_{sq, h} chebyshevTrapezoidalSecondSqrtRieszAction(m) +
  (Δ²_{sq, h} secularTrapezoidalSecondSqrtRieszAction(m) -
    secularMidpointClassicalCesaroSum (m^2) * Δ²_{sq, h} secularSqrtIncrementAction(m) -
    (Δ²_{sq, h} secularTrapezoidalSqrtRieszAction(m) -
      (m^2 - 1 / 2) * Δ²_{sq, h} secularSqrtIncrementAction(m)) * m^2)`. -/
theorem centered_three_square_midpointClassicalCesaroSum_add_psi_sub_sq_le_trapezoidalSecondSqrtRieszAction
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (secularSqrtIncrementAction ((m + h) ^ 2) -
        2 * secularSqrtIncrementAction (m ^ 2) +
        secularSqrtIncrementAction ((m - h) ^ 2)) *
      chebyshevMidpointClassicalCesaroSum (m ^ 2) +
      ((secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
          2 * secularTrapezoidalSqrtRieszAction (m ^ 2) +
          secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
        (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
          (secularSqrtIncrementAction ((m + h) ^ 2) -
            2 * secularSqrtIncrementAction (m ^ 2) +
            secularSqrtIncrementAction ((m - h) ^ 2))) *
        (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ)) ≤
      (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
          2 * chebyshevTrapezoidalSecondSqrtRieszAction (m ^ 2) +
          chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) +
        ((secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
            2 * secularTrapezoidalSecondSqrtRieszAction (m ^ 2) +
            secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
          secularMidpointClassicalCesaroSum (m ^ 2) *
            (secularSqrtIncrementAction ((m + h) ^ 2) -
              2 * secularSqrtIncrementAction (m ^ 2) +
              secularSqrtIncrementAction ((m - h) ^ 2)) -
          ((secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
              2 * secularTrapezoidalSqrtRieszAction (m ^ 2) +
              secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
            (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
              (secularSqrtIncrementAction ((m + h) ^ 2) -
                2 * secularSqrtIncrementAction (m ^ 2) +
                secularSqrtIncrementAction ((m - h) ^ 2))) *
            ((m ^ 2 : ℕ) : ℝ)) := by
  have hpot :=
    chebyshevTrapezoidalSecondSqrtRieszPotential_square_second_diff_centered_midpointPhi1_psi_ge hmh
  rw [chebyshevMidpointClassicalCesaroSum_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2)]
  linarith

/-! ## Section 4: Quartic-Cancelling (`m^4`-Free and `h^3 * m^2`-Free) Central-Difference Secular Identities and Second-Order Central-Difference Sandwiches for `2 * h * chebyshevSecondCesaroSum (m^2)` -/

/-- **Quartic-Cancelling (`m^4`-Free and `h^3 * m^2`-Free) Central-Difference Secular Identity for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`, subtracting `2 * h * S₂(m^2)`,
`((E_{F_√}((m + h)^2) - E_{F_√}((m - h)^2)) - (2 * m^2 - 1) * h) * S₁(m^2)`, AND
`(E_{W_{\mathrm{trap}, +}}(m, h) + E_{W_{\mathrm{trap}, -}}(m, h)) * m^2` from
`E_2^{\mathrm{trap}}((m + h)^2) - E_2^{\mathrm{trap}}((m - h)^2)` cancels BOTH `(4 / 3) * h^3 * m^4`
AND `(1 / 3) * h^3 * m^2` identically, leaving the quadratic-in-`m` polynomial:
`((4 / 5) * h^5 - (1 / 24) * h) * m^2 + (1 / 21) * h^7 - (1 / 24) * h^3`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRiesz_central_diff_quartic_cancelling_secular_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    ((eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
          eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
        2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
      ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
        (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
        secularClassicalCesaroSum (m ^ 2) -
      ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
          eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
        2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
        (((m ^ 2 : ℕ) : ℝ) - 1) *
          ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
              eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
            (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ))) *
        ((m ^ 2 : ℕ) : ℝ) =
      ((4 / 5 : ℝ) * (h : ℝ) ^ 5 - (1 / 24 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21 : ℝ) * (h : ℝ) ^ 7 - (1 / 24 : ℝ) * (h : ℝ) ^ 3 := by
  have h1 := eulerMaclaurinTrapezoidalSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_eq hm hmh
  have h2 := eulerMaclaurinTrapezoidalSecondOrderWeight_three_square_add_eq hm hmh
  have hc_m2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have halg :
      ((eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
            eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          secularClassicalCesaroSum (m ^ 2) -
        ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
            eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
          (((m ^ 2 : ℕ) : ℝ) - 1) *
            ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
                eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
              (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ))) *
          ((m ^ 2 : ℕ) : ℝ) =
      (((eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
            eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          secularClassicalCesaroSum (m ^ 2)) -
        ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
            eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
          (((m ^ 2 : ℕ) : ℝ) - 1) *
            ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
                eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
              (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ))) *
          ((m ^ 2 : ℕ) : ℝ) := by
    ring
  rw [halg, h1, h2, hc_m2]
  ring

/-- **Two-Sided Second-Order Central-Difference Sandwich for `2 * h * chebyshevSecondCesaroSum (m^2)` Coupled to `chebyshevClassicalCesaroSum (m^2)` and `ψ`:**
For any `h + 2 ≤ m`, converting `chebyshevTrapezoidalSecondSqrtRieszPotential_central_diff_quadratic_taylor_sandwich`
into centered Cesàro and Riesz observables gives:
`secularTrapezoidalSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ(m^2) +
  secularTrapezoidalSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ((m - h)^2) ≤
  ((chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
      chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2)) -
    2 * h * chebyshevSecondCesaroSum (m^2)) -
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    (2 * m^2 - 1) * h) * chebyshevClassicalCesaroSum (m^2) +
  (((secularTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
      secularTrapezoidalSecondSqrtRieszAction ((m - h)^2)) -
    2 * h * secularSecondCesaroSum (m^2)) -
    ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
      (2 * m^2 - 1) * h) * secularClassicalCesaroSum (m^2)) ≤
  secularTrapezoidalSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ((m + h)^2) +
  secularTrapezoidalSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ(m^2)`. -/
theorem two_mul_chebyshevSecondCesaroSum_sq_central_diff_second_order_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    secularTrapezoidalSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
        Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) +
      secularTrapezoidalSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
        Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) ≤
      ((chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
            chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
          2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2)) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevClassicalCesaroSum (m ^ 2) +
        (((secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
              secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
            2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
            secularClassicalCesaroSum (m ^ 2)) ∧
    ((chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
            chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
          2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2)) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevClassicalCesaroSum (m ^ 2) +
        (((secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
              secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
            2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
            secularClassicalCesaroSum (m ^ 2)) ≤
      secularTrapezoidalSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
          Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) +
        secularTrapezoidalSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
          Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) := by
  have hpot := chebyshevTrapezoidalSecondSqrtRieszPotential_central_diff_quadratic_taylor_sandwich hmh
  rw [chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevClassicalCesaroSum_eq_convexPotential_sub_secular (m ^ 2)]
  constructor
  · linarith [hpot.1]
  · linarith [hpot.2]

/-- **Quartic-Cancelling Central-Difference Upper Bound for `2 * h * chebyshevSecondCesaroSum (m^2)` Subtracting `(W_{\mathrm{trap}, +} + W_{\mathrm{trap}, -}) * m^2`:**
For any `h + 2 ≤ m`, subtracting `(W_{\mathrm{trap}, +}(m^2, (m + h)^2) + W_{\mathrm{trap}, -}((m - h)^2, m^2)) * m^2`
from the secular central difference centers `ψ(m^2)` and `ψ((m - h)^2)` around `m^2`:
`2 * h * chebyshevSecondCesaroSum (m^2) +
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    (2 * m^2 - 1) * h) * chebyshevClassicalCesaroSum (m^2) +
  secularTrapezoidalSecondOrderForwardWeight (m^2) ((m + h)^2) * (ψ(m^2) - m^2) +
  secularTrapezoidalSecondOrderBackwardWeight ((m - h)^2) (m^2) * (ψ((m - h)^2) - m^2) ≤
  (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
    chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2)) +
  (((secularTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
      secularTrapezoidalSecondSqrtRieszAction ((m - h)^2)) -
    2 * h * secularSecondCesaroSum (m^2)) -
    ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
      (2 * m^2 - 1) * h) * secularClassicalCesaroSum (m^2) -
    ((secularTrapezoidalSqrtRieszAction ((m + h)^2) -
        secularTrapezoidalSqrtRieszAction ((m - h)^2)) -
      2 * h * secularClassicalCesaroSum (m^2) -
      (m^2 - 1) * ((secularSqrtIncrementAction ((m + h)^2) -
          secularSqrtIncrementAction ((m - h)^2)) -
        (2 * m^2 - 1) * h)) * m^2)`. -/
theorem two_mul_chebyshevSecondCesaroSum_sq_central_diff_quartic_cancelling_le
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) +
      ((secularSqrtIncrementAction ((m + h) ^ 2) -
          secularSqrtIncrementAction ((m - h) ^ 2)) -
        (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
        chebyshevClassicalCesaroSum (m ^ 2) +
      secularTrapezoidalSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
        (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ)) +
      secularTrapezoidalSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
        (Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ)) ≤
      (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) +
        (((secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
              secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
            2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
            secularClassicalCesaroSum (m ^ 2) -
          ((secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
              secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
            2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
            (((m ^ 2 : ℕ) : ℝ) - 1) *
              ((secularSqrtIncrementAction ((m + h) ^ 2) -
                  secularSqrtIncrementAction ((m - h) ^ 2)) -
                (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ))) *
            ((m ^ 2 : ℕ) : ℝ)) := by
  have h1 := (two_mul_chebyshevSecondCesaroSum_sq_central_diff_second_order_sandwich hmh).1
  have hW := secularTrapezoidalSecondOrderWeight_three_square_add_eq (show h ≤ m by omega)
  linarith [congrArg (fun x => x * ((m ^ 2 : ℕ) : ℝ)) hW]

/-- **Complementary Quartic-Cancelling Central-Difference Lower Bound for `2 * h * chebyshevSecondCesaroSum (m^2)`:**
For any `h + 2 ≤ m`,
`(chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
  chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2)) +
  (((secularTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
      secularTrapezoidalSecondSqrtRieszAction ((m - h)^2)) -
    2 * h * secularSecondCesaroSum (m^2)) -
    ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
      (2 * m^2 - 1) * h) * secularClassicalCesaroSum (m^2) -
    ((secularTrapezoidalSqrtRieszAction ((m + h)^2) -
        secularTrapezoidalSqrtRieszAction ((m - h)^2)) -
      2 * h * secularClassicalCesaroSum (m^2) -
      (m^2 - 1) * ((secularSqrtIncrementAction ((m + h)^2) -
          secularSqrtIncrementAction ((m - h)^2)) -
        (2 * m^2 - 1) * h)) * m^2) ≤
  2 * h * chebyshevSecondCesaroSum (m^2) +
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    (2 * m^2 - 1) * h) * chebyshevClassicalCesaroSum (m^2) +
  secularTrapezoidalSecondOrderForwardWeight (m^2) ((m + h)^2) * (ψ((m + h)^2) - m^2) +
  secularTrapezoidalSecondOrderBackwardWeight ((m - h)^2) (m^2) * (ψ(m^2) - m^2)`. -/
theorem two_mul_chebyshevSecondCesaroSum_sq_central_diff_quartic_cancelling_ge
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
        chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) +
      (((secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
            secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          secularClassicalCesaroSum (m ^ 2) -
        ((secularTrapezoidalSqrtRieszAction ((m + h) ^ 2) -
            secularTrapezoidalSqrtRieszAction ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
          (((m ^ 2 : ℕ) : ℝ) - 1) *
            ((secularSqrtIncrementAction ((m + h) ^ 2) -
                secularSqrtIncrementAction ((m - h) ^ 2)) -
              (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ))) *
          ((m ^ 2 : ℕ) : ℝ)) ≤
      2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2) +
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevClassicalCesaroSum (m ^ 2) +
        secularTrapezoidalSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
          (Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ)) +
        secularTrapezoidalSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
          (Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) - ((m ^ 2 : ℕ) : ℝ)) := by
  have h2 := (two_mul_chebyshevSecondCesaroSum_sq_central_diff_second_order_sandwich hmh).2
  have hW := secularTrapezoidalSecondOrderWeight_three_square_add_eq (show h ≤ m by omega)
  linarith [congrArg (fun x => x * ((m ^ 2 : ℕ) : ℝ)) hW]

/-- **Second-Order Midpoint-Slope Central-Difference Quadratic Taylor Sandwich for `chebyshevTrapezoidalSecondSqrtRieszPotential`:**
For any `h + 2 ≤ m`, subtracting the backward midpoint-slope quadratic Taylor sandwich on `[(m - h)^2, m^2]`
from the forward midpoint-slope quadratic Taylor sandwich on `[m^2, (m + h)^2]` isolates `2 * h * Φ₂(m^2)`
and `((S_{F_√}((m + h)^2) - S_{F_√}((m - h)^2)) - (2 * m^2 - 1) * h) * Φ₁^{\mathrm{mid}}(m^2)`:
`secularMidpointSlopeSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ(m^2) +
  secularMidpointSlopeSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ((m - h)^2) ≤
  (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h)^2) -
    chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h)^2) -
    2 * h * chebyshevSecondConvexPotential (m^2)) -
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    (2 * m^2 - 1) * h) * chebyshevMidpointClassicalPotential (m^2) ≤
  secularMidpointSlopeSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ((m + h)^2) +
  secularMidpointSlopeSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ(m^2)`. -/
theorem chebyshevTrapezoidalSecondSqrtRieszPotential_central_diff_midpointSlope_quadratic_taylor_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    secularMidpointSlopeSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
        Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) +
      secularMidpointSlopeSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
        Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) ≤
      (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2) -
          2 * (h : ℝ) * chebyshevSecondConvexPotential (m ^ 2)) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevMidpointClassicalPotential (m ^ 2) ∧
    (chebyshevTrapezoidalSecondSqrtRieszPotential ((m + h) ^ 2) -
          chebyshevTrapezoidalSecondSqrtRieszPotential ((m - h) ^ 2) -
          2 * (h : ℝ) * chebyshevSecondConvexPotential (m ^ 2)) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevMidpointClassicalPotential (m ^ 2) ≤
      secularMidpointSlopeSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
          Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) +
        secularMidpointSlopeSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
          Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) := by
  have hm_sub2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle1 : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle2 : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd :=
    chebyshevTrapezoidalSecondSqrtRieszPotential_forward_midpointSlope_quadratic_taylor_sandwich
      hm2 hle2
  have hbwd :=
    chebyshevTrapezoidalSecondSqrtRieszPotential_backward_midpointSlope_quadratic_taylor_sandwich
      hm_sub2 hle1
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m + h)] at hfwd
  rw [sqrt_nat_sq_eq (m - h), sqrt_nat_sq_eq m] at hbwd
  have hc_sub : ((m - h : ℕ) : ℝ) = (m : ℝ) - (h : ℝ) := Nat.cast_sub (by omega)
  have hc_add : ((m + h : ℕ) : ℝ) = (m : ℝ) + (h : ℝ) := by push_cast; ring
  have hspan_fwd : ((m + h : ℕ) : ℝ) - (m : ℝ) = (h : ℝ) := by rw [hc_add]; ring
  have hspan_bwd : (m : ℝ) - ((m - h : ℕ) : ℝ) = (h : ℝ) := by rw [hc_sub]; ring
  rw [hspan_fwd] at hfwd
  rw [hspan_bwd] at hbwd
  constructor
  · linarith [hfwd.1, hbwd.1]
  · linarith [hfwd.2, hbwd.2]

/-- **Quartic-Cancelling (`m^4`-Free and `h^3 * m^2`-Free) Midpoint-Slope Central-Difference Secular Identity for `eulerMaclaurinTrapezoidalSecondSqrtRieszSecular`:**
For any `2 ≤ m` and `h ≤ m`, subtracting `2 * h * S₂(m^2)`,
`((E_{F_√}((m + h)^2) - E_{F_√}((m - h)^2)) - (2 * m^2 - 1) * h) * S₁^{\mathrm{mid}}(m^2)`, AND
`(E_{W_{\mathrm{mid}, +}}(m, h) + E_{W_{\mathrm{mid}, -}}(m, h)) * m^2` from
`E_2^{\mathrm{trap}}((m + h)^2) - E_2^{\mathrm{trap}}((m - h)^2)` cancels BOTH `(4 / 3) * h^3 * m^4`
AND `(1 / 3) * h^3 * m^2` identically, leaving the exact same quadratic-in-`m` polynomial as
`eulerMaclaurinTrapezoidalSecondSqrtRiesz_central_diff_quartic_cancelling_secular_eq`:
`((4 / 5) * h^5 - (1 / 24) * h) * m^2 + (1 / 21) * h^7 - (1 / 24) * h^3`. -/
theorem eulerMaclaurinTrapezoidalSecondSqrtRiesz_central_diff_midpointSlope_quartic_cancelling_secular_eq
    {m h : ℕ} (hm : 2 ≤ m) (hmh : h ≤ m) :
    ((eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
          eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
        2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
      ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
          eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
        (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
        secularMidpointClassicalCesaroSum (m ^ 2) -
      ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
          eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
        2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
        (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
          ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
              eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
            (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ))) *
        ((m ^ 2 : ℕ) : ℝ) =
      ((4 / 5 : ℝ) * (h : ℝ) ^ 5 - (1 / 24 : ℝ) * (h : ℝ)) * (m : ℝ) ^ 2 +
        (1 / 21 : ℝ) * (h : ℝ) ^ 7 - (1 / 24 : ℝ) * (h : ℝ) ^ 3 := by
  have h1 := eulerMaclaurinTrapezoidalSecondSqrtRiesz_central_diff_sub_secularC2_and_secularC1_eq hm hmh
  have h2 := eulerMaclaurinMidpointSlopeSecondOrderWeight_three_square_add_eq hm hmh
  have h3 := eulerMaclaurinSqrtIncrementSecular_central_diff_sub_two_sq_sub_one_mul_eq hmh
  have hc_m2 : ((m ^ 2 : ℕ) : ℝ) = (m : ℝ) ^ 2 := by push_cast; ring
  have hdiff_S1 :
      secularMidpointClassicalCesaroSum (m ^ 2) =
        secularClassicalCesaroSum (m ^ 2) + (1 / 2 : ℝ) * (m : ℝ) ^ 2 := by
    unfold secularMidpointClassicalCesaroSum
    rw [hc_m2]
  rw [hdiff_S1]
  have halg :
      ((eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
            eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          (secularClassicalCesaroSum (m ^ 2) + (1 / 2 : ℝ) * (m : ℝ) ^ 2) -
        ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
            eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
          (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
            ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
                eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
              (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ))) *
          ((m ^ 2 : ℕ) : ℝ) =
      (((eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m + h) ^ 2) -
            eulerMaclaurinTrapezoidalSecondSqrtRieszSecular ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          secularClassicalCesaroSum (m ^ 2)) -
        ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
            eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          ((1 / 2 : ℝ) * (m : ℝ) ^ 2) -
        ((eulerMaclaurinTrapezoidalSqrtRieszSecular ((m + h) ^ 2) -
            eulerMaclaurinTrapezoidalSqrtRieszSecular ((m - h) ^ 2)) -
          2 * (h : ℝ) * secularClassicalCesaroSum (m ^ 2) -
          (((m ^ 2 : ℕ) : ℝ) - 1 / 2) *
            ((eulerMaclaurinSqrtIncrementSecular ((m + h) ^ 2) -
                eulerMaclaurinSqrtIncrementSecular ((m - h) ^ 2)) -
              (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ))) *
          ((m ^ 2 : ℕ) : ℝ) := by
    ring
  rw [halg, h1, h2, h3, hc_m2]
  ring

/-- **Two-Sided Midpoint-Slope Second-Order Central-Difference Sandwich for `2 * h * chebyshevSecondCesaroSum (m^2)`:**
For any `h + 2 ≤ m`,
`secularMidpointSlopeSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ(m^2) +
  secularMidpointSlopeSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ((m - h)^2) ≤
  ((chebyshevTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
      chebyshevTrapezoidalSecondSqrtRieszAction ((m - h)^2)) -
    2 * h * chebyshevSecondCesaroSum (m^2)) -
  ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
    (2 * m^2 - 1) * h) * chebyshevMidpointClassicalCesaroSum (m^2) +
  (((secularTrapezoidalSecondSqrtRieszAction ((m + h)^2) -
      secularTrapezoidalSecondSqrtRieszAction ((m - h)^2)) -
    2 * h * secularSecondCesaroSum (m^2)) -
    ((secularSqrtIncrementAction ((m + h)^2) - secularSqrtIncrementAction ((m - h)^2)) -
      (2 * m^2 - 1) * h) * secularMidpointClassicalCesaroSum (m^2)) ≤
  secularMidpointSlopeSecondOrderForwardWeight (m^2) ((m + h)^2) * ψ((m + h)^2) +
  secularMidpointSlopeSecondOrderBackwardWeight ((m - h)^2) (m^2) * ψ(m^2)`. -/
theorem two_mul_chebyshevSecondCesaroSum_sq_central_diff_midpointSlope_second_order_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    secularMidpointSlopeSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
        Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) +
      secularMidpointSlopeSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
        Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ) ≤
      ((chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
            chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
          2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2)) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevMidpointClassicalCesaroSum (m ^ 2) +
        (((secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
              secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
            2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
            secularMidpointClassicalCesaroSum (m ^ 2)) ∧
    ((chebyshevTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
            chebyshevTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
          2 * (h : ℝ) * chebyshevSecondCesaroSum (m ^ 2)) -
        ((secularSqrtIncrementAction ((m + h) ^ 2) -
            secularSqrtIncrementAction ((m - h) ^ 2)) -
          (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
          chebyshevMidpointClassicalCesaroSum (m ^ 2) +
        (((secularTrapezoidalSecondSqrtRieszAction ((m + h) ^ 2) -
              secularTrapezoidalSecondSqrtRieszAction ((m - h) ^ 2)) -
            2 * (h : ℝ) * secularSecondCesaroSum (m ^ 2)) -
          ((secularSqrtIncrementAction ((m + h) ^ 2) -
              secularSqrtIncrementAction ((m - h) ^ 2)) -
            (2 * ((m ^ 2 : ℕ) : ℝ) - 1) * (h : ℝ)) *
            secularMidpointClassicalCesaroSum (m ^ 2)) ≤
      secularMidpointSlopeSecondOrderForwardWeight (m ^ 2) ((m + h) ^ 2) *
          Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) +
        secularMidpointSlopeSecondOrderBackwardWeight ((m - h) ^ 2) (m ^ 2) *
          Chebyshev.psi ((m ^ 2 : ℕ) : ℝ) := by
  have hpot :=
    chebyshevTrapezoidalSecondSqrtRieszPotential_central_diff_midpointSlope_quadratic_taylor_sandwich
      hmh
  rw [chebyshevMidpointClassicalCesaroSum_eq_potential_sub_secular (m ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m + h) ^ 2),
    chebyshevTrapezoidalSecondSqrtRieszAction_eq_potential_sub_secular ((m - h) ^ 2),
    chebyshevSecondCesaroSum_eq_convexPotential_sub_secular (m ^ 2)]
  constructor
  · linarith [hpot.1]
  · linarith [hpot.2]

end

end GaloisForLFunctions.RHTower
