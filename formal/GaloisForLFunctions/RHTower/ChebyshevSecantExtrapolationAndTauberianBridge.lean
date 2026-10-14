import GaloisForLFunctions.RHTower.ChebyshevSqrtConvexityAndThreeQuarterMesh

/-!
# Extended Secant Lower Extrapolation, Two-Sided Three-Point Convex Trap, and Tauberian Pointwise Bridge

In `ChebyshevSqrtConvexityAndThreeQuarterMesh.lean`, we established the decomposition
`chebyshevSqrtIncrementAction M = chebyshevSqrtConvexPotential M - secularSqrtIncrementAction M`,
proved that `chebyshevSqrtConvexPotential M` is convex as a function of `√M`, and used the
Jensen Secant Upper Bound on `[N, M]` to break the `√n` mesh barrier to `O(n^{3/4})` gaps for
one-sided upper RH equivalences.

In this module, we complete the dual lower-extrapolation and local Tauberian theory:

1. **Section 1 (Extended Secant Lower Extrapolation, the Two-Sided Three-Point Convex Trap, and
   Two-Sided `O(n^{3/4})`-Gap Mesh RH Criteria):**
   - Rearranging the Jensen Secant Upper Bound on `[L, N, P]` (`2 ≤ L ≤ N ≤ P`) yields the
     **Right Secant Lower Extrapolation** (`chebyshevSqrtIncrementAction_right_secant_extrapolation_ge`):
     `(√N - √L) * F P ≥ (√N - √L) * F N + (√P - √N) * (F N - F L) - (√P - √N) * (√N - √L) * (P - L)`.
   - Using the division-free square-root step comparison
     `(√P - √N) * (N - L) ≤ (P - N) * (√N - √L) ≤ (M - N) * (√N - √L)` for `0 ≤ L ≤ N ≤ P ≤ M`,
     any locally regular triple `2 ≤ L < N ≤ P ≤ M` with `M - N ≤ κ * (N - L)` traps
     `chebyshevSqrtIncrementAction P` **from below** by its values at `L` and `N` up to
     `-(M - L)^2 / (2 * √L)`.
   - Combining this with the Jensen Secant Upper Bound on `[N, M]` gives the **Two-Sided
     Three-Point Convex Trap** (`abs_chebyshevSqrtIncrementAction_le_of_three_point_trap`) and
     two-sided `O(n^{3/4})`-gap mesh RH equivalences.

2. **Section 2 (Local `3 * (M - N)` Window-Increment Bridge to `chebyshevNormalizedCesaroSum`):**
   - We refine the global `3 * M` comparison between `chebyshevSqrtIncrementAction M` and
     `(1 / 2) * chebyshevNormalizedCesaroSum M` to the **local window-increment bound**
     (`abs_chebyshevSqrtIncrementAction_sub_sub_half_normalizedCesaroSum_sub_le`):
     `|(chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) - (1 / 2) * (chebyshevNormalizedCesaroSum M - chebyshevNormalizedCesaroSum N)| ≤ 3 * (M - N)`
     for all `2 ≤ N ≤ M`, and deduce the induced window secant sandwich for
     `chebyshevNormalizedCesaroSum`.

3. **Section 3 (Rationalized Tauberian Pointwise `ψ(N) - N` Extraction and Symmetric Window
   Transfer):**
   - Using `1 / (√M - √N) = (√M + √N) / (M - N)`, we rationalize the forward and backward
     Tauberian bounds for `ψ(N) - N` and prove the **Symmetric Window Tauberian Transfer**
     (`abs_psi_sub_le_of_symmetric_window_chebyshevSqrtIncrementAction`): if
     `|chebyshevSqrtIncrementAction K| ≤ B` at the three points `K ∈ {N - H, N, N + H}`
     (`1 ≤ H ≤ N`, `2 ≤ N - H`), then
     `|ψ(N) - N| ≤ 6 * √N * B / H + H`.
-/

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open Filter Topology
open scoped BigOperators Chebyshev ArithmeticFunction

noncomputable section

/-! ## Section 1: Extended Secant Lower Extrapolation, the Two-Sided Three-Point Convex Trap,
and Two-Sided `O(n^{3/4})`-Gap Mesh RH Criteria -/

/-- **Right Secant Lower Extrapolation for `chebyshevSqrtConvexPotential`:**
For any `2 ≤ L ≤ N ≤ P`, extrapolating the secant line of `chebyshevSqrtConvexPotential` from
`[L, N]` to `P` bounds `chebyshevSqrtConvexPotential P` from below with zero error:
`(√P - √L) * Φ N - (√P - √N) * Φ L ≤ (√N - √L) * Φ P`. -/
theorem chebyshevSqrtConvexPotential_right_secant_extrapolation_ge
    {L N P : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) (hNP : N ≤ P) :
    (Real.sqrt (P : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSqrtConvexPotential N -
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtConvexPotential L ≤
      (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSqrtConvexPotential P := by
  have hjensen := chebyshevSqrtConvexPotential_jensen_secant_le hL hLN hNP
  linarith

/-- **Left Secant Lower Extrapolation for `chebyshevSqrtConvexPotential`:**
For any `2 ≤ P ≤ M ≤ R`, extrapolating the secant line of `chebyshevSqrtConvexPotential` from
`[M, R]` to `P` bounds `chebyshevSqrtConvexPotential P` from below with zero error:
`(√R - √P) * Φ M - (√M - √P) * Φ R ≤ (√R - √M) * Φ P`. -/
theorem chebyshevSqrtConvexPotential_left_secant_extrapolation_ge
    {P M R : ℕ} (hP : 2 ≤ P) (hPM : P ≤ M) (hMR : M ≤ R) :
    (Real.sqrt (R : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSqrtConvexPotential M -
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSqrtConvexPotential R ≤
      (Real.sqrt (R : ℝ) - Real.sqrt (M : ℝ)) * chebyshevSqrtConvexPotential P := by
  have hjensen := chebyshevSqrtConvexPotential_jensen_secant_le hP hPM hMR
  linarith

/-- **Right Secant Lower Extrapolation for `chebyshevSqrtIncrementAction`:**
For any `2 ≤ L ≤ N ≤ P`,
`(√N - √L) * F N + (√P - √N) * (F N - F L) - (√P - √N) * (√N - √L) * (P - L) ≤ (√N - √L) * F P`. -/
theorem chebyshevSqrtIncrementAction_right_secant_extrapolation_ge
    {L N P : ℕ} (hL : 2 ≤ L) (hLN : L ≤ N) (hNP : N ≤ P) :
    (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSqrtIncrementAction N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction L) -
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * ((P : ℝ) - L) ≤
      (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSqrtIncrementAction P := by
  have hjensen := chebyshevSqrtIncrementAction_jensen_secant_le hL hLN hNP
  linarith

/-- **Left Secant Lower Extrapolation for `chebyshevSqrtIncrementAction`:**
For any `2 ≤ P ≤ M ≤ R`,
`(√R - √M) * F M + (√M - √P) * (F M - F R) - (√R - √M) * (√M - √P) * (R - P) ≤ (√R - √M) * F P`. -/
theorem chebyshevSqrtIncrementAction_left_secant_extrapolation_ge
    {P M R : ℕ} (hP : 2 ≤ P) (hPM : P ≤ M) (hMR : M ≤ R) :
    (Real.sqrt (R : ℝ) - Real.sqrt (M : ℝ)) * chebyshevSqrtIncrementAction M +
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction R) -
        (Real.sqrt (R : ℝ) - Real.sqrt (M : ℝ)) *
          (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * ((R : ℝ) - P) ≤
      (Real.sqrt (R : ℝ) - Real.sqrt (M : ℝ)) * chebyshevSqrtIncrementAction P := by
  have hjensen := chebyshevSqrtIncrementAction_jensen_secant_le hP hPM hMR
  linarith

/-- **Division-Free Square-Root Increment Ratio Inequality:**
For any `L ≤ N ≤ P ≤ M` in `ℕ`, concavity of `√·` across the shared point `N` yields
`(√P - √N) * (N - L) ≤ (P - N) * (√N - √L) ≤ (M - N) * (√N - √L)`. -/
theorem sqrt_sub_mul_sub_le_sub_mul_sqrt_sub
    {L N P M : ℕ} (hLN : L ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * ((N : ℝ) - L) ≤
        ((P : ℝ) - N) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) ∧
      ((P : ℝ) - N) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) ≤
        ((M : ℝ) - N) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) := by
  have hsLN : 0 ≤ Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hLN)
  have hsNP : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
  have hsqL : Real.sqrt (L : ℝ) * Real.sqrt (L : ℝ) = (L : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hsqP : Real.sqrt (P : ℝ) * Real.sqrt (P : ℝ) = (P : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hNL_eq :
      (N : ℝ) - L =
        (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * (Real.sqrt (N : ℝ) + Real.sqrt (L : ℝ)) := by
    calc
      (N : ℝ) - L = Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) -
          Real.sqrt (L : ℝ) * Real.sqrt (L : ℝ) := by rw [hsqN, hsqL]
      _ = (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) *
          (Real.sqrt (N : ℝ) + Real.sqrt (L : ℝ)) := by ring
  have hPN_eq :
      (P : ℝ) - N =
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (P : ℝ) + Real.sqrt (N : ℝ)) := by
    calc
      (P : ℝ) - N = Real.sqrt (P : ℝ) * Real.sqrt (P : ℝ) -
          Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := by rw [hsqP, hsqN]
      _ = (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (Real.sqrt (P : ℝ) + Real.sqrt (N : ℝ)) := by ring
  constructor
  · rw [hNL_eq, hPN_eq]
    have hsum_le : Real.sqrt (N : ℝ) + Real.sqrt (L : ℝ) ≤
        Real.sqrt (P : ℝ) + Real.sqrt (N : ℝ) := by linarith
    calc
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          ((Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * (Real.sqrt (N : ℝ) + Real.sqrt (L : ℝ))) =
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) *
          (Real.sqrt (N : ℝ) + Real.sqrt (L : ℝ)) := by ring
      _ ≤ (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) *
          (Real.sqrt (P : ℝ) + Real.sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_le (mul_nonneg hsNP hsLN)
      _ = (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (Real.sqrt (P : ℝ) + Real.sqrt (N : ℝ)) *
          (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) := by ring
  · exact mul_le_mul_of_nonneg_right (sub_le_sub_right (by exact_mod_cast hPM) (N : ℝ)) hsLN

/-- **Prime-Free Secant Extrapolation Lower Bound for `chebyshevSqrtIncrementAction`:**
For any `2 ≤ L < N ≤ P ≤ M` with `(M : ℝ) - N ≤ κ * ((N : ℝ) - L)` (`κ ≥ 0`),
`chebyshevSqrtIncrementAction P ≥ -((1 + 2 * κ) * max |chebyshevSqrtIncrementAction L| |chebyshevSqrtIncrementAction N| + (M - L)^2 / (2 * √N))`. -/
theorem chebyshevSqrtIncrementAction_ge_neg_max_sub_sq_div_sqrt
    {L N P M : ℕ} {κ : ℝ} (hL : 2 ≤ L) (hLN : L < N) (hNP : N ≤ P) (hPM : P ≤ M)
    (_hκ : 0 ≤ κ) (hreg : (M : ℝ) - N ≤ κ * ((N : ℝ) - L)) :
    -((1 + 2 * κ) * max |chebyshevSqrtIncrementAction L| |chebyshevSqrtIncrementAction N| +
        ((M : ℝ) - L) ^ 2 / (2 * Real.sqrt (N : ℝ))) ≤
      chebyshevSqrtIncrementAction P := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hNL_pos : 0 < (N : ℝ) - L := sub_pos.mpr (by exact_mod_cast hLN)
  have hsLN : 0 < Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hLN)
  have hsNP : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
  have hratio : Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) ≤
      κ * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) := by
    have hstep := (sqrt_sub_mul_sub_le_sub_mul_sqrt_sub hLN.le hNP hPM).1.trans
      (sqrt_sub_mul_sub_le_sub_mul_sqrt_sub hLN.le hNP hPM).2
    have hstep2 :
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * ((N : ℝ) - L) ≤
          κ * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * ((N : ℝ) - L) := by
      calc
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * ((N : ℝ) - L) ≤
          ((M : ℝ) - N) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) := hstep
        _ ≤ (κ * ((N : ℝ) - L)) * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) :=
          mul_le_mul_of_nonneg_right hreg hsLN.le
        _ = κ * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * ((N : ℝ) - L) := by ring
    exact le_of_mul_le_mul_right hstep2 hNL_pos
  set μ := max |chebyshevSqrtIncrementAction L| |chebyshevSqrtIncrementAction N|
  have hμ0 : 0 ≤ μ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hFN_ge : -μ ≤ chebyshevSqrtIncrementAction N :=
    (neg_le_neg (le_max_right _ _)).trans (neg_abs_le _)
  have hFL_le : chebyshevSqrtIncrementAction L ≤ μ :=
    (le_abs_self _).trans (le_max_left _ _)
  have hdiff_ge : -2 * μ ≤ chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction L := by
    linarith
  have hterm1 :
      -(Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * μ ≤
        (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSqrtIncrementAction N := by
    nlinarith
  have hterm2 :
      -(Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * (2 * κ * μ) ≤
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction L) := by
    calc
      -(Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * (2 * κ * μ) =
        -(κ * (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ))) * (2 * μ) := by ring
      _ ≤ -(Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (2 * μ) := by nlinarith
      _ = (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (-2 * μ) := by ring
      _ ≤ (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction L) :=
        mul_le_mul_of_nonneg_left hdiff_ge hsNP
  have hsqrt_PN_le :
      Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) ≤
        ((M : ℝ) - L) / (2 * Real.sqrt (N : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    have hsqP : Real.sqrt (P : ℝ) * Real.sqrt (P : ℝ) = (P : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
      Real.mul_self_sqrt hN0.le
    calc
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * (2 * Real.sqrt (N : ℝ)) ≤
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (Real.sqrt (P : ℝ) + Real.sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hsNP
      _ = Real.sqrt (P : ℝ) * Real.sqrt (P : ℝ) -
          Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := by ring
      _ = (P : ℝ) - N := by rw [hsqP, hsqN]
      _ ≤ (M : ℝ) - L := by
        have : (P : ℝ) ≤ M := by exact_mod_cast hPM
        have : (L : ℝ) ≤ N := by exact_mod_cast hLN.le
        linarith
  have hcurv_le :
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * ((P : ℝ) - L) ≤
        (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) *
          (((M : ℝ) - L) ^ 2 / (2 * Real.sqrt (N : ℝ))) := by
    have hPL_le : (P : ℝ) - L ≤ (M : ℝ) - L := by
      have : (P : ℝ) ≤ M := by exact_mod_cast hPM
      linarith
    have hPL0 : 0 ≤ (P : ℝ) - L := sub_nonneg.mpr (by exact_mod_cast (hLN.le.trans hNP))
    have hML0 : 0 ≤ (M : ℝ) - L := sub_nonneg.mpr (by exact_mod_cast ((hLN.le.trans hNP).trans hPM))
    calc
      (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * ((P : ℝ) - L) ≤
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) *
          (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * ((M : ℝ) - L) :=
        mul_le_mul_of_nonneg_left hPL_le (mul_nonneg hsNP hsLN.le)
      _ = (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) *
          ((Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) - L)) := by ring
      _ ≤ (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) *
          ((((M : ℝ) - L) / (2 * Real.sqrt (N : ℝ))) * ((M : ℝ) - L)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrt_PN_le hML0) hsLN.le
      _ = (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) *
          (((M : ℝ) - L) ^ 2 / (2 * Real.sqrt (N : ℝ))) := by ring
  have hextrap := chebyshevSqrtIncrementAction_right_secant_extrapolation_ge hL hLN.le hNP
  have htotal :
      (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) *
          (-((1 + 2 * κ) * μ + ((M : ℝ) - L) ^ 2 / (2 * Real.sqrt (N : ℝ)))) ≤
        (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) * chebyshevSqrtIncrementAction P := by
    linarith
  exact le_of_mul_le_mul_left htotal hsLN

/-- **Two-Sided Three-Point Convex Trap for `chebyshevSqrtIncrementAction`:**
For any `2 ≤ L < N ≤ P ≤ M` with `(M : ℝ) - N ≤ κ * ((N : ℝ) - L)` (`κ ≥ 0`),
`|chebyshevSqrtIncrementAction P| ≤ (1 + 2 * κ) * max |F L| (max |F N| |F M|) + (M - L)^2 / (2 * √N)`. -/
theorem abs_chebyshevSqrtIncrementAction_le_of_three_point_trap
    {L N P M : ℕ} {κ : ℝ} (hL : 2 ≤ L) (hLN : L < N) (hNP : N ≤ P) (hPM : P ≤ M)
    (hκ : 0 ≤ κ) (hreg : (M : ℝ) - N ≤ κ * ((N : ℝ) - L)) :
    |chebyshevSqrtIncrementAction P| ≤
      (1 + 2 * κ) *
          max |chebyshevSqrtIncrementAction L|
            (max |chebyshevSqrtIncrementAction N| |chebyshevSqrtIncrementAction M|) +
        ((M : ℝ) - L) ^ 2 / (2 * Real.sqrt (N : ℝ)) := by
  have hN2 : 2 ≤ N := hL.trans hLN.le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  set μ₃ := max |chebyshevSqrtIncrementAction L|
    (max |chebyshevSqrtIncrementAction N| |chebyshevSqrtIncrementAction M|)
  have hμ₃_nonneg : 0 ≤ μ₃ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hup := chebyshevSqrtIncrementAction_le_max_add_sq_div_sqrt hN2 hNP hPM
  have hlow := chebyshevSqrtIncrementAction_ge_neg_max_sub_sq_div_sqrt hL hLN hNP hPM hκ hreg
  have hmax2_le :
      max (chebyshevSqrtIncrementAction N) (chebyshevSqrtIncrementAction M) ≤
        (1 + 2 * κ) * μ₃ := by
    have h1 : max (chebyshevSqrtIncrementAction N) (chebyshevSqrtIncrementAction M) ≤
        max |chebyshevSqrtIncrementAction N| |chebyshevSqrtIncrementAction M| :=
      max_le_max (le_abs_self _) (le_abs_self _)
    have h2 : max |chebyshevSqrtIncrementAction N| |chebyshevSqrtIncrementAction M| ≤ μ₃ :=
      le_max_right _ _
    have h3 : μ₃ ≤ (1 + 2 * κ) * μ₃ := by nlinarith
    exact (h1.trans h2).trans h3
  have hmaxLN_le :
      max |chebyshevSqrtIncrementAction L| |chebyshevSqrtIncrementAction N| ≤ μ₃ :=
    max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
  have hsq_le :
      ((M : ℝ) - N) ^ 2 / (2 * Real.sqrt (N : ℝ)) ≤
        ((M : ℝ) - L) ^ 2 / (2 * Real.sqrt (N : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hMN0 : 0 ≤ (M : ℝ) - N := sub_nonneg.mpr (by exact_mod_cast (hNP.trans hPM))
    have hML : (M : ℝ) - N ≤ (M : ℝ) - L := by
      have : (L : ℝ) ≤ N := by exact_mod_cast hLN.le
      linarith
    exact pow_le_pow_left₀ hMN0 hML 2
  rw [abs_le]
  constructor
  · have hmul :
        (1 + 2 * κ) * max |chebyshevSqrtIncrementAction L| |chebyshevSqrtIncrementAction N| ≤
          (1 + 2 * κ) * μ₃ :=
      mul_le_mul_of_nonneg_left hmaxLN_le (by positivity)
    linarith
  · linarith

/-- **Two-Sided `O(n^{3/4})`-Gap Mesh Transfer for `|chebyshevSqrtIncrementAction|`:**
If a sampling set `A ⊆ ℕ` traps every `P ≥ N₁` in a three-point configuration `L, N, M ∈ A` with
`3 ≤ L < N ≤ P ≤ M ≤ 2 * N`, `(M : ℝ) - N ≤ κ * ((N : ℝ) - L)`, and `(M - L)^2 ≤ K * N * √N`,
then `|chebyshevSqrtIncrementAction n| ≤ C * n` on `A` implies
`|chebyshevSqrtIncrementAction P| ≤ C' * P` for all `P ≥ 3`. -/
theorem abs_chebyshevSqrtIncrementAction_le_of_three_quarter_mesh_samples
    {A : Set ℕ} {C κ K : ℝ} {N₁ : ℕ}
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hK : 0 ≤ K)
    (hA : ∀ n ∈ A, 3 ≤ n → |chebyshevSqrtIncrementAction n| ≤ C * (n : ℝ))
    (hdense : ∀ P : ℕ, N₁ ≤ P → ∃ L ∈ A, ∃ N ∈ A, ∃ M ∈ A,
      3 ≤ L ∧ L < N ∧ N ≤ P ∧ P ≤ M ∧ M ≤ 2 * N ∧
      (M : ℝ) - N ≤ κ * ((N : ℝ) - L) ∧
      ((M : ℝ) - L) ^ 2 ≤ K * (N : ℝ) * Real.sqrt (N : ℝ)) :
    ∃ C' : ℝ, ∀ P : ℕ, 3 ≤ P → |chebyshevSqrtIncrementAction P| ≤ C' * (P : ℝ) := by
  classical
  set B : ℝ := (Finset.range (N₁ + 3)).sup' ⟨0, by simp⟩
    fun P => |chebyshevSqrtIncrementAction P|
  refine ⟨max B ((1 + 2 * κ) * (2 * C) + K / 2), fun P hP3 => ?_⟩
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
  rcases lt_or_ge P N₁ with hlt | hge
  · have hleB : |chebyshevSqrtIncrementAction P| ≤ B :=
      Finset.le_sup' (fun P => |chebyshevSqrtIncrementAction P|)
        (Finset.mem_range.mpr (by omega))
    have hB_le : B ≤ max B ((1 + 2 * κ) * (2 * C) + K / 2) := le_max_left _ _
    have hmax_nonneg : 0 ≤ max B ((1 + 2 * κ) * (2 * C) + K / 2) :=
      le_trans (by positivity) (le_max_right B ((1 + 2 * κ) * (2 * C) + K / 2))
    calc
      |chebyshevSqrtIncrementAction P| ≤ max B ((1 + 2 * κ) * (2 * C) + K / 2) := hleB.trans hB_le
      _ = max B ((1 + 2 * κ) * (2 * C) + K / 2) * 1 := by ring
      _ ≤ max B ((1 + 2 * κ) * (2 * C) + K / 2) * (P : ℝ) :=
        mul_le_mul_of_nonneg_left hP1 hmax_nonneg
  · obtain ⟨L, hLA, N, hNA, M, hMA, hL3, hLN, hNP, hPM, hM2N, hreg, hgap⟩ := hdense P hge
    have hL2 : 2 ≤ L := by omega
    have hN3 : 3 ≤ N := by omega
    have hM3 : 3 ≤ M := by omega
    have htrap := abs_chebyshevSqrtIncrementAction_le_of_three_point_trap
      hL2 hLN hNP hPM hκ hreg
    have hCL : |chebyshevSqrtIncrementAction L| ≤ 2 * C * (P : ℝ) := by
      have h1 := hA L hLA hL3
      have hLP : (L : ℝ) ≤ P := by exact_mod_cast (hLN.le.trans hNP)
      calc
        |chebyshevSqrtIncrementAction L| ≤ C * (L : ℝ) := h1
        _ ≤ 2 * C * (P : ℝ) := by nlinarith
    have hCN : |chebyshevSqrtIncrementAction N| ≤ 2 * C * (P : ℝ) := by
      have h1 := hA N hNA hN3
      have hNP' : (N : ℝ) ≤ P := by exact_mod_cast hNP
      calc
        |chebyshevSqrtIncrementAction N| ≤ C * (N : ℝ) := h1
        _ ≤ 2 * C * (P : ℝ) := by nlinarith
    have hCM : |chebyshevSqrtIncrementAction M| ≤ 2 * C * (P : ℝ) := by
      have h1 := hA M hMA hM3
      have hM2P : (M : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast (show M ≤ 2 * P by omega)
      calc
        |chebyshevSqrtIncrementAction M| ≤ C * (M : ℝ) := h1
        _ ≤ 2 * C * (P : ℝ) := by nlinarith
    have hmax3 :
        max |chebyshevSqrtIncrementAction L|
            (max |chebyshevSqrtIncrementAction N| |chebyshevSqrtIncrementAction M|) ≤
          2 * C * (P : ℝ) := max_le hCL (max_le hCN hCM)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
    have hcurv_le :
        ((M : ℝ) - L) ^ 2 / (2 * Real.sqrt (N : ℝ)) ≤ (K / 2) * (P : ℝ) := by
      have hdiv :
          ((M : ℝ) - L) ^ 2 / (2 * Real.sqrt (N : ℝ)) ≤ (K / 2) * (N : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        calc
          ((M : ℝ) - L) ^ 2 ≤ K * (N : ℝ) * Real.sqrt (N : ℝ) := hgap
          _ = (K / 2) * (N : ℝ) * (2 * Real.sqrt (N : ℝ)) := by ring
      have hNP_cast : (N : ℝ) ≤ P := by exact_mod_cast hNP
      exact hdiv.trans (mul_le_mul_of_nonneg_left hNP_cast (by positivity))
    have hmul_max3 :
        (1 + 2 * κ) *
            max |chebyshevSqrtIncrementAction L|
              (max |chebyshevSqrtIncrementAction N| |chebyshevSqrtIncrementAction M|) ≤
          (1 + 2 * κ) * (2 * C) * (P : ℝ) := by
      calc
        (1 + 2 * κ) *
            max |chebyshevSqrtIncrementAction L|
              (max |chebyshevSqrtIncrementAction N| |chebyshevSqrtIncrementAction M|) ≤
          (1 + 2 * κ) * (2 * C * (P : ℝ)) :=
          mul_le_mul_of_nonneg_left hmax3 (by positivity)
        _ = (1 + 2 * κ) * (2 * C) * (P : ℝ) := by ring
    have hP_bound :
        |chebyshevSqrtIncrementAction P| ≤ ((1 + 2 * κ) * (2 * C) + K / 2) * (P : ℝ) := by
      linarith
    exact hP_bound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
/-! ## Section 2: Local `3 * (M - N)` Window-Increment Bridge to `chebyshevNormalizedCesaroSum` -/

/-- **Local `3 * (M - N)` Window-Increment Comparison Between `chebyshevSqrtIncrementAction` and
`(1 / 2) * chebyshevNormalizedCesaroSum`:**
For all `2 ≤ N ≤ M`,
`|(chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) - (1 / 2) * (chebyshevNormalizedCesaroSum M - chebyshevNormalizedCesaroSum N)| ≤ 3 * (M - N)`. -/
theorem abs_chebyshevSqrtIncrementAction_sub_sub_half_normalizedCesaroSum_sub_le
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    |(chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) -
        (1 / 2 : ℝ) * (chebyshevNormalizedCesaroSum M - chebyshevNormalizedCesaroSum N)| ≤
      3 * ((M : ℝ) - N) := by
  have hIco1 :
      chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N =
        ∑ k ∈ Finset.Ico (N - 2) (M - 2),
          (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) *
            (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) := by
    unfold chebyshevSqrtIncrementAction
    exact (Finset.sum_Ico_eq_sub _ (show N - 2 ≤ M - 2 by omega)).symm
  have hIco2 :
      chebyshevNormalizedCesaroSum M - chebyshevNormalizedCesaroSum N =
        ∑ k ∈ Finset.Ico (N - 2) (M - 2),
          (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) / Real.sqrt (k + 2 : ℕ) := by
    unfold chebyshevNormalizedCesaroSum
    exact (Finset.sum_Ico_eq_sub _ (show N - 2 ≤ M - 2 by omega)).symm
  rw [hIco1, hIco2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.Ico (N - 2) (M - 2),
      |(Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) *
          (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) -
        (1 / 2 : ℝ) * ((Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) / Real.sqrt (k + 2 : ℕ))| ≤ 3 := by
    intro k _
    have hdiff :
        (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) *
            (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) -
          (1 / 2 : ℝ) * ((Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) / Real.sqrt (k + 2 : ℕ)) =
        -(1 / (2 * Real.sqrt (k + 2 : ℕ)) - (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ))) *
          (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) := by ring
    rw [hdiff, abs_mul, abs_neg]
    have hinc := inv_two_mul_sqrt_sub_sqrt_succ_sub_sqrt_bounds (d := k + 2) (by omega)
    rw [show k + 2 + 1 = k + 3 by omega] at hinc
    rw [abs_of_nonneg hinc.1]
    have hψ_le : |Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)| ≤ 6 * (k + 2 : ℕ) := by
      have h1 := psi_nat_le_six_mul (k + 2)
      have h2 := psi_nat_nonneg (k + 2)
      rw [abs_le]
      constructor <;> linarith
    calc
      (1 / (2 * Real.sqrt (k + 2 : ℕ)) - (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ))) *
          |Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)| ≤
        (1 / (2 * (k + 2 : ℕ))) * (6 * (k + 2 : ℕ)) :=
        mul_le_mul hinc.2 hψ_le (abs_nonneg _) (by positivity)
      _ = 3 := by field_simp; ring
  have hcard : ((M - 2 - (N - 2) : ℕ) : ℝ) = (M : ℝ) - N := by
    rw [show M - 2 - (N - 2) = M - N by omega, Nat.cast_sub hNM]
  calc
    |∑ k ∈ Finset.Ico (N - 2) (M - 2),
        ((Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) *
            (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) -
          (1 / 2 : ℝ) * ((Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) / Real.sqrt (k + 2 : ℕ)))| ≤
      ∑ k ∈ Finset.Ico (N - 2) (M - 2), (3 : ℝ) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = 3 * ((M - 2 - (N - 2) : ℕ) : ℝ) := by simp [mul_comm]
    _ = 3 * ((M : ℝ) - N) := by rw [hcard]

/-- **Window Secant Sandwich for `chebyshevNormalizedCesaroSum`:**
For all `2 ≤ N ≤ M`,
`(√M - √N) * (ψ(N) - M) - 3 * (M - N) ≤ (1 / 2) * (chebyshevNormalizedCesaroSum M - chebyshevNormalizedCesaroSum N) ≤ (√M - √N) * (ψ(M) - N) + 3 * (M - N)`. -/
theorem chebyshevNormalizedCesaroSum_sub_bounds {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (Chebyshev.psi (N : ℝ) - (M : ℝ)) -
        3 * ((M : ℝ) - N) ≤
      (1 / 2 : ℝ) * (chebyshevNormalizedCesaroSum M - chebyshevNormalizedCesaroSum N) ∧
    (1 / 2 : ℝ) * (chebyshevNormalizedCesaroSum M - chebyshevNormalizedCesaroSum N) ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (Chebyshev.psi (M : ℝ) - (N : ℝ)) +
        3 * ((M : ℝ) - N) := by
  have h1 := chebyshevSqrtIncrementAction_sub_bounds hN hNM
  have h2 := abs_sub_le_iff.mp
    (abs_chebyshevSqrtIncrementAction_sub_sub_half_normalizedCesaroSum_sub_le hN hNM)
  constructor <;> linarith

/-! ## Section 3: Rationalized Tauberian Pointwise `ψ(N) - N` Extraction and
Symmetric Window Transfer -/

/-- Exact rationalization identity `1 / (√M - √N) = (√M + √N) / (M - N)` for `N < M`. -/
theorem inv_sqrt_sub_sqrt_eq {N M : ℕ} (hNM : N < M) :
    1 / (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) =
      (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) / ((M : ℝ) - N) := by
  have hMN : 0 < (M : ℝ) - N := sub_pos.mpr (by exact_mod_cast hNM)
  have hsNM : 0 < Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hNM)
  have hsqM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  rw [div_eq_div_iff hsNM.ne' hMN.ne']
  calc
    1 * ((M : ℝ) - N) =
      Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := by
      rw [one_mul, hsqM, hsqN]
    _ = (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) * (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) := by
      ring

/-- **Rationalized Forward Tauberian Upper Bound for `ψ(N) - N`:**
For any `2 ≤ N < M`,
`ψ(N) - N ≤ ((√M + √N) / (M - N)) * (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) + (M - N)`. -/
theorem psi_sub_le_rationalized_forward_chebyshevSqrtIncrementAction
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N < M) :
    Chebyshev.psi (N : ℝ) - (N : ℝ) ≤
      ((Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) / ((M : ℝ) - N)) *
          (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) +
        ((M : ℝ) - N) := by
  have h := psi_sub_le_forward_secant_chebyshevSqrtIncrementAction hN hNM
  have hrew :
      (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) /
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) =
        ((Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) / ((M : ℝ) - N)) *
          (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) := by
    calc
      (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) /
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) =
        (1 / (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
          (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) := by ring
      _ = ((Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) / ((M : ℝ) - N)) *
          (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) := by
        rw [inv_sqrt_sub_sqrt_eq hNM]
  linarith

/-- **Rationalized Backward Tauberian Lower Bound for `ψ(M) - M`:**
For any `2 ≤ N < M`,
`((√M + √N) / (M - N)) * (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) - (M - N) ≤ ψ(M) - M`. -/
theorem psi_sub_ge_rationalized_backward_chebyshevSqrtIncrementAction
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N < M) :
    ((Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) / ((M : ℝ) - N)) *
        (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) -
      ((M : ℝ) - N) ≤
      Chebyshev.psi (M : ℝ) - (M : ℝ) := by
  have h := psi_sub_ge_backward_secant_chebyshevSqrtIncrementAction hN hNM
  have hrew :
      (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) /
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) =
        ((Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) / ((M : ℝ) - N)) *
          (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) := by
    calc
      (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) /
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) =
        (1 / (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) *
          (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) := by ring
      _ = ((Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) / ((M : ℝ) - N)) *
          (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) := by
        rw [inv_sqrt_sub_sqrt_eq hNM]
  linarith

/-- **Symmetric Window Tauberian Transfer (`|chebyshevSqrtIncrementAction| ≤ B` $\implies$
`|ψ(N) - N| ≤ 6 * √N * B / H + H`):**
For any `N, H : ℕ` with `1 ≤ H`, `H ≤ N`, and `2 ≤ N - H`, if
`|chebyshevSqrtIncrementAction (N - H)| ≤ B`, `|chebyshevSqrtIncrementAction N| ≤ B`, and
`|chebyshevSqrtIncrementAction (N + H)| ≤ B`, then
`|ψ(N) - N| ≤ 6 * √N * B / H + H`. -/
theorem abs_psi_sub_le_of_symmetric_window_chebyshevSqrtIncrementAction
    {N H : ℕ} {B : ℝ} (hH1 : 1 ≤ H) (hHN : H ≤ N) (hNH2 : 2 ≤ N - H)
    (hB_left : |chebyshevSqrtIncrementAction (N - H)| ≤ B)
    (hB_mid : |chebyshevSqrtIncrementAction N| ≤ B)
    (hB_right : |chebyshevSqrtIncrementAction (N + H)| ≤ B) :
    |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤
      6 * Real.sqrt (N : ℝ) * B / (H : ℝ) + (H : ℝ) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hB_mid
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH1
  have hN2 : 2 ≤ N := by omega
  have hN0 : (0 : ℝ) ≤ N := by positivity
  rw [abs_le]
  constructor
  · -- Lower bound from `[N - H, N]`
    have hlt : N - H < N := by omega
    have hback := psi_sub_ge_rationalized_backward_chebyshevSqrtIncrementAction hNH2 hlt
    have hsub_eq : (N : ℝ) - ((N - H : ℕ) : ℝ) = (H : ℝ) := by
      rw [Nat.cast_sub hHN]; ring
    rw [hsub_eq] at hback
    have hdiff_ge :
        -2 * B ≤ chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction (N - H) := by
      have h1 := (abs_le.mp hB_mid).1
      have h2 := (abs_le.mp hB_left).2
      linarith
    have hsqrt_le :
        Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ) ≤ 3 * Real.sqrt (N : ℝ) := by
      have hs1 : Real.sqrt ((N - H : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le N H)
      have hs0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg N
      linarith
    have hquot_ge :
        -(6 * Real.sqrt (N : ℝ) * B / (H : ℝ)) ≤
          ((Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ)) *
            (chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction (N - H)) := by
      have hnonneg :
          0 ≤ (Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ) := by positivity
      calc
        -(6 * Real.sqrt (N : ℝ) * B / (H : ℝ)) =
          -((3 * Real.sqrt (N : ℝ)) / (H : ℝ)) * (2 * B) := by ring
        _ ≤ -((Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ)) * (2 * B) := by
          have hdiv_le :
              (Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ) ≤
                (3 * Real.sqrt (N : ℝ)) / (H : ℝ) :=
            div_le_div_of_nonneg_right hsqrt_le hH0.le
          nlinarith
        _ = ((Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ)) * (-2 * B) := by ring
        _ ≤ ((Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ)) *
            (chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction (N - H)) :=
          mul_le_mul_of_nonneg_left hdiff_ge hnonneg
    linarith
  · -- Upper bound from `[N, N + H]`
    have hlt : N < N + H := by omega
    have hforw := psi_sub_le_rationalized_forward_chebyshevSqrtIncrementAction hN2 hlt
    have hsub_eq : ((N + H : ℕ) : ℝ) - (N : ℝ) = (H : ℝ) := by push_cast; ring
    rw [hsub_eq] at hforw
    have hdiff_le :
        chebyshevSqrtIncrementAction (N + H) - chebyshevSqrtIncrementAction N ≤ 2 * B := by
      have h1 := (abs_le.mp hB_right).2
      have h2 := (abs_le.mp hB_mid).1
      linarith
    have hsqrt_le :
        Real.sqrt ((N + H : ℕ) : ℝ) + Real.sqrt (N : ℝ) ≤ 3 * Real.sqrt (N : ℝ) := by
      have hs1 : Real.sqrt ((N + H : ℕ) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
        apply Real.sqrt_le_iff.mpr
        refine ⟨by positivity, ?_⟩
        have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN0
        have hle : ((N + H : ℕ) : ℝ) ≤ 4 * (N : ℝ) := by
          have : N + H ≤ 4 * N := by omega
          exact_mod_cast this
        calc
          ((N + H : ℕ) : ℝ) ≤ 4 * (N : ℝ) := hle
          _ = 4 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by rw [hsq]
          _ = (2 * Real.sqrt (N : ℝ)) ^ 2 := by ring
      linarith
    have hquot_le :
        ((Real.sqrt ((N + H : ℕ) : ℝ) + Real.sqrt (N : ℝ)) / (H : ℝ)) *
            (chebyshevSqrtIncrementAction (N + H) - chebyshevSqrtIncrementAction N) ≤
          6 * Real.sqrt (N : ℝ) * B / (H : ℝ) := by
      have hnonneg :
          0 ≤ (Real.sqrt ((N + H : ℕ) : ℝ) + Real.sqrt (N : ℝ)) / (H : ℝ) := by positivity
      calc
        ((Real.sqrt ((N + H : ℕ) : ℝ) + Real.sqrt (N : ℝ)) / (H : ℝ)) *
            (chebyshevSqrtIncrementAction (N + H) - chebyshevSqrtIncrementAction N) ≤
          ((Real.sqrt ((N + H : ℕ) : ℝ) + Real.sqrt (N : ℝ)) / (H : ℝ)) * (2 * B) :=
          mul_le_mul_of_nonneg_left hdiff_le hnonneg
        _ ≤ ((3 * Real.sqrt (N : ℝ)) / (H : ℝ)) * (2 * B) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsqrt_le hH0.le) (by positivity)
        _ = 6 * Real.sqrt (N : ℝ) * B / (H : ℝ) := by ring
    linarith

/-- **Local Increment Bound for `chebyshevSqrtIncrementAction` from `chebyshevNormalizedCesaroSum`:**
For `2 ≤ N ≤ M`, if `|chebyshevNormalizedCesaroSum N| ≤ B` and
`|chebyshevNormalizedCesaroSum M| ≤ B`, then
`|chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N| ≤ B + 3 * (M - N)`. -/
theorem abs_chebyshevSqrtIncrementAction_sub_le_of_normalizedCesaroSum_bounds
    {N M : ℕ} {B : ℝ} (hN : 2 ≤ N) (hNM : N ≤ M)
    (hBN : |chebyshevNormalizedCesaroSum N| ≤ B)
    (hBM : |chebyshevNormalizedCesaroSum M| ≤ B) :
    |chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N| ≤
      B + 3 * ((M : ℝ) - N) := by
  have hbridge :=
    abs_chebyshevSqrtIncrementAction_sub_sub_half_normalizedCesaroSum_sub_le hN hNM
  have h1 := abs_le.mp hbridge
  have h2 := abs_le.mp hBN
  have h3 := abs_le.mp hBM
  rw [abs_le]
  constructor <;> linarith

/-- **Symmetric Window Tauberian Transfer from `chebyshevNormalizedCesaroSum` (`|S_N| ≤ B`
$\implies$ `|ψ(N) - N| ≤ 3 * √N * B / H + 9 * √N + H`):**
For any `N, H : ℕ` with `1 ≤ H`, `H ≤ N`, and `2 ≤ N - H`, if
`|chebyshevNormalizedCesaroSum (N - H)| ≤ B`, `|chebyshevNormalizedCesaroSum N| ≤ B`, and
`|chebyshevNormalizedCesaroSum (N + H)| ≤ B`, then
`|ψ(N) - N| ≤ 3 * √N * B / H + 9 * √N + H`, using the local window bridge of error `3 H` rather
than the global `3 M` prefix error. -/
theorem abs_psi_sub_le_of_symmetric_window_chebyshevNormalizedCesaroSum
    {N H : ℕ} {B : ℝ} (hH1 : 1 ≤ H) (hHN : H ≤ N) (hNH2 : 2 ≤ N - H)
    (hB_left : |chebyshevNormalizedCesaroSum (N - H)| ≤ B)
    (hB_mid : |chebyshevNormalizedCesaroSum N| ≤ B)
    (hB_right : |chebyshevNormalizedCesaroSum (N + H)| ≤ B) :
    |Chebyshev.psi (N : ℝ) - (N : ℝ)| ≤
      3 * Real.sqrt (N : ℝ) * B / (H : ℝ) + 9 * Real.sqrt (N : ℝ) + (H : ℝ) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hB_mid
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH1
  have hN2 : 2 ≤ N := by omega
  have hN0 : (0 : ℝ) ≤ N := by positivity
  rw [abs_le]
  constructor
  · -- Lower bound from `[N - H, N]`
    have hlt : N - H < N := by omega
    have hback := psi_sub_ge_rationalized_backward_chebyshevSqrtIncrementAction hNH2 hlt
    have hsub_eq : (N : ℝ) - ((N - H : ℕ) : ℝ) = (H : ℝ) := by
      rw [Nat.cast_sub hHN]; ring
    rw [hsub_eq] at hback
    have hinc :=
      abs_chebyshevSqrtIncrementAction_sub_le_of_normalizedCesaroSum_bounds
        hNH2 (Nat.sub_le N H) hB_left hB_mid
    rw [hsub_eq] at hinc
    have hdiff_ge :
        -(B + 3 * (H : ℝ)) ≤
          chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction (N - H) :=
      (abs_le.mp hinc).1
    have hsqrt_le :
        Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ) ≤ 3 * Real.sqrt (N : ℝ) := by
      have hs1 : Real.sqrt ((N - H : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le N H)
      have hs0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg N
      linarith
    have hquot_ge :
        -(3 * Real.sqrt (N : ℝ) * B / (H : ℝ) + 9 * Real.sqrt (N : ℝ)) ≤
          ((Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ)) *
            (chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction (N - H)) := by
      have hnonneg :
          0 ≤ (Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ) := by positivity
      calc
        -(3 * Real.sqrt (N : ℝ) * B / (H : ℝ) + 9 * Real.sqrt (N : ℝ)) =
          -((3 * Real.sqrt (N : ℝ)) / (H : ℝ)) * (B + 3 * (H : ℝ)) := by
          field_simp [hH0.ne']
          ring
        _ ≤ -((Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ)) *
            (B + 3 * (H : ℝ)) := by
          have hdiv_le :
              (Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ) ≤
                (3 * Real.sqrt (N : ℝ)) / (H : ℝ) :=
            div_le_div_of_nonneg_right hsqrt_le hH0.le
          nlinarith
        _ = ((Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ)) *
            (-(B + 3 * (H : ℝ))) := by ring
        _ ≤ ((Real.sqrt (N : ℝ) + Real.sqrt ((N - H : ℕ) : ℝ)) / (H : ℝ)) *
            (chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction (N - H)) :=
          mul_le_mul_of_nonneg_left hdiff_ge hnonneg
    linarith
  · -- Upper bound from `[N, N + H]`
    have hlt : N < N + H := by omega
    have hforw := psi_sub_le_rationalized_forward_chebyshevSqrtIncrementAction hN2 hlt
    have hsub_eq : ((N + H : ℕ) : ℝ) - (N : ℝ) = (H : ℝ) := by push_cast; ring
    rw [hsub_eq] at hforw
    have hinc :=
      abs_chebyshevSqrtIncrementAction_sub_le_of_normalizedCesaroSum_bounds
        hN2 (Nat.le_add_right N H) hB_mid hB_right
    rw [hsub_eq] at hinc
    have hdiff_le :
        chebyshevSqrtIncrementAction (N + H) - chebyshevSqrtIncrementAction N ≤
          B + 3 * (H : ℝ) :=
      (abs_le.mp hinc).2
    have hsqrt_le :
        Real.sqrt ((N + H : ℕ) : ℝ) + Real.sqrt (N : ℝ) ≤ 3 * Real.sqrt (N : ℝ) := by
      have hs1 : Real.sqrt ((N + H : ℕ) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
        apply Real.sqrt_le_iff.mpr
        refine ⟨by positivity, ?_⟩
        have hsq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN0
        have hle : ((N + H : ℕ) : ℝ) ≤ 4 * (N : ℝ) := by
          have : N + H ≤ 4 * N := by omega
          exact_mod_cast this
        calc
          ((N + H : ℕ) : ℝ) ≤ 4 * (N : ℝ) := hle
          _ = 4 * (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) := by rw [hsq]
          _ = (2 * Real.sqrt (N : ℝ)) ^ 2 := by ring
      linarith
    have hquot_le :
        ((Real.sqrt ((N + H : ℕ) : ℝ) + Real.sqrt (N : ℝ)) / (H : ℝ)) *
            (chebyshevSqrtIncrementAction (N + H) - chebyshevSqrtIncrementAction N) ≤
          3 * Real.sqrt (N : ℝ) * B / (H : ℝ) + 9 * Real.sqrt (N : ℝ) := by
      have hnonneg :
          0 ≤ (Real.sqrt ((N + H : ℕ) : ℝ) + Real.sqrt (N : ℝ)) / (H : ℝ) := by positivity
      calc
        ((Real.sqrt ((N + H : ℕ) : ℝ) + Real.sqrt (N : ℝ)) / (H : ℝ)) *
            (chebyshevSqrtIncrementAction (N + H) - chebyshevSqrtIncrementAction N) ≤
          ((Real.sqrt ((N + H : ℕ) : ℝ) + Real.sqrt (N : ℝ)) / (H : ℝ)) *
            (B + 3 * (H : ℝ)) :=
          mul_le_mul_of_nonneg_left hdiff_le hnonneg
        _ ≤ ((3 * Real.sqrt (N : ℝ)) / (H : ℝ)) * (B + 3 * (H : ℝ)) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsqrt_le hH0.le) (by positivity)
        _ = 3 * Real.sqrt (N : ℝ) * B / (H : ℝ) + 9 * Real.sqrt (N : ℝ) := by
          field_simp [hH0.ne']
          ring
    linarith

end

end GaloisForLFunctions.RHTower

