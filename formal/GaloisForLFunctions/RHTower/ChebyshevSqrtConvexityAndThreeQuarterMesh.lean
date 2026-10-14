import GaloisForLFunctions.RHTower.NormalizedChebyshevCesaroAndSqrtRieszBridge

/-!
# Convex Square-Root Chebyshev Potential, Tauberian Secant Extraction, and `O(n^{3/4})`-Gap Mesh RH Criteria

In `NormalizedChebyshevCesaroAndSqrtRieszBridge.lean`, we proved that the terminal Mertens
deviation `∓(8 / 3) * M * √M * (mertensSum M - log M + γ)` cancels identically between
`-(8 / 3) * M * integerLag M` and `2 * mertensDeviationSqrtAction M`, reducing
`mobiusDivisorSquareRootAbelMoment M` within `O(M)` unconditionally to both:
* `chebyshevSqrtIncrementAction M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * (ψ(k + 2) - (k + 2))`,
* `(1 / 2) * chebyshevNormalizedCesaroSum M = (1 / 2) * ∑_{k < M - 2} (ψ(k + 2) - (k + 2)) / √(k + 2)`.

In this module, we exploit the decisive structural consequence of eliminating `mertensSum`: the
only arithmetic function remaining in `chebyshevSqrtIncrementAction M` is Chebyshev's `ψ(d)`,
which is **monotone non-decreasing** (`Chebyshev.psi_mono`), weighted against the positive
square-root increment `√(d + 1) - √d > 0`:

1. **Section 1 (The Convex Square-Root Chebyshev Potential `chebyshevSqrtConvexPotential` and
   Exact Secular `(1 / 3) * M * √M` Decomposition):**
   We split `chebyshevSqrtIncrementAction M = chebyshevSqrtConvexPotential M - secularSqrtIncrementAction M`,
   where
   `chebyshevSqrtConvexPotential M := ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * ψ(k + 2)`
   and
   `secularSqrtIncrementAction M := ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * (k + 2)`.
   Telescoping `(k + 3) * √(k + 3) - (k + 2) * √(k + 2)` yields the exact algebraic identity
   `secularSqrtIncrementAction M = M * √M - (1 / 2) * shiftedTwoSqrtPrefix (M - 2) - √M - √2`,
   and hence `|secularSqrtIncrementAction M - (1 / 3) * M * √M| ≤ 4 * √M`.
   Consequently, `mobiusDivisorSquareRootAbelMoment M` equals
   `chebyshevSqrtConvexPotential M - (1 / 3) * M * √M` within `O(M)` unconditionally.

2. **Section 2 (Exact Secant-Slope Monotonicity in `√M`, Three-Point Convexity, and Tauberian
   Pointwise `ψ(N) - N` Extraction):**
   Because `ψ` is monotone and `∑_{N ≤ d < M} (√(d + 1) - √d) = √M - √N`, we obtain the exact
   constant-free secant-slope sandwich (`chebyshevSqrtConvexPotential_sub_bounds`):
   `(√M - √N) * ψ(N) ≤ chebyshevSqrtConvexPotential M - chebyshevSqrtConvexPotential N ≤ (√M - √N) * ψ(M)`
   for all `2 ≤ N ≤ M`. This proves that `chebyshevSqrtConvexPotential M` is **exactly convex as
   a function of `√M`**, yields the three-point second-difference lower bound
   `(F M - F N) / (√M - √N) - (F N - F L) / (√N - √L) ≥ -(M - L)` for
   `F = chebyshevSqrtIncrementAction`, and extracts unconditional Tauberian upper and lower bounds
   for `ψ(N) - N` from forward and backward secant slopes of `chebyshevSqrtIncrementAction`.

3. **Section 3 (Jensen Secant Upper Interpolation and Breaking the `√n` Mesh Barrier to
   `O(n^{3/4})` Gaps for One-Sided RH Criteria):**
   Eliminating `ψ(P)` between the backward secant upper bound on `[N, P]` and the forward secant
   lower bound on `[P, M]` proves the **Jensen Secant Upper Bound** for
   `chebyshevSqrtIncrementAction P` on any interval `2 ≤ N ≤ P ≤ M`:
   `chebyshevSqrtIncrementAction P ≤ max (chebyshevSqrtIncrementAction N) (chebyshevSqrtIncrementAction M) + (M - N)^2 / (2 * √N)`
   with **no prime sum, no Mertens sum, no logarithm, and no Brun–Titchmarsh input**.
   Relative to the `O(N)` target scale, `(M - N)^2 / √N ≤ K * N` permits mesh gaps up to
   `M - N ≤ √K * N^{3/4}` — jumping from exponent `1/2` (`√n`) to exponent `3/4` (`n^{3/4}`,
   including explicit quartic meshes `s(k) = (k + 7)^4`) for the one-sided upper RH equivalences
   of `chebyshevSqrtIncrementAction`, `chebyshevNormalizedCesaroSum`, and
   `mobiusDivisorSquareRootAbelMoment`.
-/

namespace GaloisForLFunctions.RHTower

open _root_.RHTower
open Filter Topology
open scoped BigOperators Chebyshev ArithmeticFunction

noncomputable section

/-! ## Section 1: The Convex Square-Root Chebyshev Potential `chebyshevSqrtConvexPotential` and
Exact Secular `(1 / 3) * M * √M` Decomposition -/

/-- **Convex Square-Root Chebyshev Potential:**
`chebyshevSqrtConvexPotential M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * ψ(k + 2)`.
Because `ψ` is non-negative and monotone non-decreasing, `chebyshevSqrtConvexPotential M` is
non-negative, monotone non-decreasing in `M`, and convex as a function of `√M`. -/
def chebyshevSqrtConvexPotential (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) * Chebyshev.psi (k + 2 : ℕ)

/-- **Secular Square-Root-Increment Action:**
`secularSqrtIncrementAction M = ∑_{k < M - 2} (√(k + 3) - √(k + 2)) * (k + 2)`. -/
def secularSqrtIncrementAction (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M - 2),
    (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) * (k + 2 : ℕ)

/-- Exact decomposition `chebyshevSqrtIncrementAction M = chebyshevSqrtConvexPotential M - secularSqrtIncrementAction M`. -/
theorem chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular (M : ℕ) :
    chebyshevSqrtIncrementAction M =
      chebyshevSqrtConvexPotential M - secularSqrtIncrementAction M := by
  unfold chebyshevSqrtIncrementAction chebyshevSqrtConvexPotential secularSqrtIncrementAction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Non-negativity of `chebyshevSqrtConvexPotential M`. -/
theorem chebyshevSqrtConvexPotential_nonneg (M : ℕ) :
    0 ≤ chebyshevSqrtConvexPotential M := by
  unfold chebyshevSqrtConvexPotential
  refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (psi_nat_nonneg (k + 2))
  rw [sub_nonneg]
  exact Real.sqrt_le_sqrt (by exact_mod_cast (show k + 2 ≤ k + 3 by omega))

/-- Exact step identity for `shiftedTwoSqrtPrefix`:
for all `M ≥ 2`,
`∑_{k < M - 2} √(k + 3) = (1 / 2) * shiftedTwoSqrtPrefix (M - 2) + √M - √2`. -/
theorem sum_range_sqrt_add_three_eq {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.range (M - 2), Real.sqrt (k + 3 : ℕ)) =
      (1 / 2 : ℝ) * shiftedTwoSqrtPrefix (M - 2) + Real.sqrt (M : ℝ) - Real.sqrt 2 := by
  have htel := Finset.sum_range_sub (fun k => Real.sqrt (k + 2 : ℕ)) (M - 2)
  rw [show (M - 2 + 2 : ℕ) = M by omega, show (0 + 2 : ℕ) = 2 by rfl] at htel
  push_cast at htel
  have hsplit :
      (∑ k ∈ Finset.range (M - 2),
          (Real.sqrt ((k : ℝ) + 1 + 2) - Real.sqrt ((k : ℝ) + 2))) =
        (∑ k ∈ Finset.range (M - 2), Real.sqrt (k + 3 : ℕ)) -
          (1 / 2 : ℝ) * shiftedTwoSqrtPrefix (M - 2) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      rw [show (k + 3 : ℕ) = k + 1 + 2 by omega]
      push_cast
      rfl
    · unfold shiftedTwoSqrtPrefix
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
  linarith

/-- **Exact Closed Identity for `secularSqrtIncrementAction M`:**
For all `M ≥ 2`,
`secularSqrtIncrementAction M = M * √M - (1 / 2) * shiftedTwoSqrtPrefix (M - 2) - √M - √2`. -/
theorem secularSqrtIncrementAction_eq_sub_half_shiftedTwoSqrtPrefix {M : ℕ} (hM : 2 ≤ M) :
    secularSqrtIncrementAction M =
      (M : ℝ) * Real.sqrt (M : ℝ) - (1 / 2 : ℝ) * shiftedTwoSqrtPrefix (M - 2) -
        Real.sqrt (M : ℝ) - Real.sqrt 2 := by
  have htel := Finset.sum_range_sub
    (fun k => ((k + 2 : ℕ) : ℝ) * Real.sqrt (k + 2 : ℕ)) (M - 2)
  rw [show (M - 2 + 2 : ℕ) = M by omega, show (0 + 2 : ℕ) = 2 by rfl] at htel
  have hcongr :
      (∑ k ∈ Finset.range (M - 2),
          (((k + 1 + 2 : ℕ) : ℝ) * Real.sqrt (k + 1 + 2 : ℕ) -
            ((k + 2 : ℕ) : ℝ) * Real.sqrt (k + 2 : ℕ))) =
        secularSqrtIncrementAction M + ∑ k ∈ Finset.range (M - 2), Real.sqrt (k + 3 : ℕ) := by
    unfold secularSqrtIncrementAction
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [show k + 1 + 2 = k + 3 by omega]
    push_cast
    ring
  rw [hcongr, sum_range_sqrt_add_three_eq hM] at htel
  push_cast at htel
  linarith

/-- **Sharp `4 * √M` Approximation of `secularSqrtIncrementAction M` by `(1 / 3) * M * √M`:**
For all `M ≥ 2`,
`|secularSqrtIncrementAction M - (1 / 3) * M * √M| ≤ 4 * √M`. -/
theorem abs_secularSqrtIncrementAction_sub_one_third_mul_sqrt_le {M : ℕ} (hM : 2 ≤ M) :
    |secularSqrtIncrementAction M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ)| ≤
      4 * Real.sqrt (M : ℝ) := by
  have hW := abs_shiftedTwoSqrtPrefix_sub_four_thirds_le (M - 2)
  rw [show M - 2 + 2 = M by omega] at hW
  have hW' := abs_le.mp hW
  have hsqrt2 : Real.sqrt 2 ≤ Real.sqrt (M : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hM)
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  rw [secularSqrtIncrementAction_eq_sub_half_shiftedTwoSqrtPrefix hM, abs_le]
  constructor <;> linarith

/-- **Sharp `4 * √M` Comparison Between `chebyshevSqrtIncrementAction M` and
`chebyshevSqrtConvexPotential M - (1 / 3) * M * √M`:**
For all `M ≥ 2`,
`|chebyshevSqrtIncrementAction M - (chebyshevSqrtConvexPotential M - (1 / 3) * M * √M)| ≤ 4 * √M`. -/
theorem abs_chebyshevSqrtIncrementAction_sub_convexPotential_sub_one_third_le
    {M : ℕ} (hM : 2 ≤ M) :
    |chebyshevSqrtIncrementAction M -
        (chebyshevSqrtConvexPotential M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ))| ≤
      4 * Real.sqrt (M : ℝ) := by
  have hident :
      chebyshevSqrtIncrementAction M -
          (chebyshevSqrtConvexPotential M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ)) =
        -(secularSqrtIncrementAction M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ)) := by
    rw [chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular]
    ring
  rw [hident, abs_neg]
  exact abs_secularSqrtIncrementAction_sub_one_third_mul_sqrt_le hM

/-- **Direct Unconditional `O(M)` Bridge Between `mobiusDivisorSquareRootAbelMoment M` and
`chebyshevSqrtConvexPotential M - (1 / 3) * M * √M`:**
There exists `B ≥ 0` such that for all `M ≥ 3`,
`|mobiusDivisorSquareRootAbelMoment M - (chebyshevSqrtConvexPotential M - (1 / 3) * M * √M)| ≤ B * M`. -/
theorem exists_abs_mobiusDivisorSquareRootAbel_sub_convexPotential_sub_one_third_linear :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      |mobiusDivisorSquareRootAbelMoment M -
        (chebyshevSqrtConvexPotential M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ))| ≤
        B * (M : ℝ) := by
  obtain ⟨B₀, hB₀, h0⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear
  refine ⟨B₀ + 7, by positivity, fun M hM => ?_⟩
  have hM2 : 2 ≤ M := by omega
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hsqrtM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
    have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
    nlinarith
  have h1 := h0 M hM
  have h2 := abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M
  have h3 := (abs_chebyshevSqrtIncrementAction_sub_convexPotential_sub_one_third_le hM2).trans
    (mul_le_mul_of_nonneg_left hsqrtM (by norm_num))
  calc
    |mobiusDivisorSquareRootAbelMoment M -
        (chebyshevSqrtConvexPotential M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ))| =
      |(mobiusDivisorSquareRootAbelMoment M - (1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M) +
        ((1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M - chebyshevSqrtIncrementAction M) +
        (chebyshevSqrtIncrementAction M -
          (chebyshevSqrtConvexPotential M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ)))| := by
      ring_nf
    _ ≤ |mobiusDivisorSquareRootAbelMoment M - (1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M| +
        |(1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M - chebyshevSqrtIncrementAction M| +
        |chebyshevSqrtIncrementAction M -
          (chebyshevSqrtConvexPotential M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ))| :=
      abs_add_three _ _ _
    _ = |mobiusDivisorSquareRootAbelMoment M - (1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M| +
        |chebyshevSqrtIncrementAction M - (1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M| +
        |chebyshevSqrtIncrementAction M -
          (chebyshevSqrtConvexPotential M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ))| := by
      rw [abs_sub_comm ((1 / 2 : ℝ) * chebyshevNormalizedCesaroSum M)]
    _ ≤ B₀ * (M : ℝ) + 3 * (M : ℝ) + 4 * (M : ℝ) := add_le_add (add_le_add h1 h2) h3
    _ = (B₀ + 7) * (M : ℝ) := by ring

/-- **One-Sided Upper RH Equivalence for `chebyshevSqrtConvexPotential M - (1 / 3) * M * √M`.** -/
theorem riemannHypothesis_iff_chebyshevSqrtConvexPotential_sub_cubic_boundedAbove :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        chebyshevSqrtConvexPotential M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) ≤
          C * (M : ℝ) := by
  rw [riemannHypothesis_iff_chebyshevNormalizedCesaroSum_boundedAbove]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(1 / 2 : ℝ) * C + 7, fun M hM => ?_⟩
    have hM2 : 2 ≤ M := by omega
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hsqrtM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
      have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
      nlinarith
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M)).1
    have h3 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_convexPotential_sub_one_third_le hM2)).2
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨2 * (C + 7), fun M hM => ?_⟩
    have hM2 : 2 ≤ M := by omega
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hsqrtM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
      have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
      nlinarith
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M)).2
    have h3 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_convexPotential_sub_one_third_le hM2)).1
    linarith

/-- **One-Sided Lower RH Equivalence for `chebyshevSqrtConvexPotential M - (1 / 3) * M * √M`.** -/
theorem riemannHypothesis_iff_chebyshevSqrtConvexPotential_sub_cubic_boundedBelow :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        -C * (M : ℝ) ≤
          chebyshevSqrtConvexPotential M - (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) := by
  rw [riemannHypothesis_iff_chebyshevNormalizedCesaroSum_boundedBelow]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(1 / 2 : ℝ) * C + 7, fun M hM => ?_⟩
    have hM2 : 2 ≤ M := by omega
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hsqrtM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
      have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
      nlinarith
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M)).2
    have h3 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_convexPotential_sub_one_third_le hM2)).1
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨2 * (C + 7), fun M hM => ?_⟩
    have hM2 : 2 ≤ M := by omega
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hsqrtM : Real.sqrt (M : ℝ) ≤ (M : ℝ) := by
      have hsq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hs1 : (1 : ℝ) ≤ Real.sqrt (M : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hM1
      nlinarith
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M)).1
    have h3 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_convexPotential_sub_one_third_le hM2)).2
    linarith

/-- **One-Sided Upper RH Equivalence for `chebyshevSqrtIncrementAction M`.** -/
theorem riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedAbove :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        chebyshevSqrtIncrementAction M ≤ C * (M : ℝ) := by
  rw [riemannHypothesis_iff_chebyshevNormalizedCesaroSum_boundedAbove]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(1 / 2 : ℝ) * C + 3, fun M hM => ?_⟩
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M)).1
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨2 * (C + 3), fun M hM => ?_⟩
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M)).2
    linarith

/-- **One-Sided Lower RH Equivalence for `chebyshevSqrtIncrementAction M`.** -/
theorem riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedBelow :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ M : ℕ, 3 ≤ M →
        -C * (M : ℝ) ≤ chebyshevSqrtIncrementAction M := by
  rw [riemannHypothesis_iff_chebyshevNormalizedCesaroSum_boundedBelow]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(1 / 2 : ℝ) * C + 3, fun M hM => ?_⟩
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M)).2
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨2 * (C + 3), fun M hM => ?_⟩
    have h1 := hC M hM
    have h2 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le M)).1
    linarith

/-! ## Section 2: Exact Secant-Slope Monotonicity in `√M`, Three-Point Convexity, and
Tauberian Pointwise `ψ(N) - N` Extraction -/

/-- Exact telescoping of the square-root increments over `Finset.Ico (N - 2) (M - 2)` for `2 ≤ N ≤ M`. -/
theorem sum_Ico_sqrt_succ_sub_sqrt_eq {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (∑ k ∈ Finset.Ico (N - 2) (M - 2),
        (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ))) =
      Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
  have h := Finset.sum_Ico_sub (fun k => Real.sqrt (k + 2 : ℕ)) (show N - 2 ≤ M - 2 by omega)
  rw [show M - 2 + 2 = M by omega, show N - 2 + 2 = N by omega] at h
  have hcongr :
      (∑ k ∈ Finset.Ico (N - 2) (M - 2),
          (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ))) =
        ∑ k ∈ Finset.Ico (N - 2) (M - 2),
          (Real.sqrt (k + 1 + 2 : ℕ) - Real.sqrt (k + 2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show k + 3 = k + 1 + 2 by omega]
  rw [hcongr]
  exact h

/-- **Exact Secant-Slope Sandwich for `chebyshevSqrtConvexPotential`:**
For all `2 ≤ N ≤ M`,
`(√M - √N) * ψ(N) ≤ chebyshevSqrtConvexPotential M - chebyshevSqrtConvexPotential N ≤ (√M - √N) * ψ(M)`.
With zero error, zero logarithms, and zero Mertens terms, the difference quotient of
`chebyshevSqrtConvexPotential` with respect to `√M` is sandwiched between `ψ(N)` and `ψ(M)`. -/
theorem chebyshevSqrtConvexPotential_sub_bounds {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * Chebyshev.psi (N : ℝ) ≤
        chebyshevSqrtConvexPotential M - chebyshevSqrtConvexPotential N ∧
      chebyshevSqrtConvexPotential M - chebyshevSqrtConvexPotential N ≤
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * Chebyshev.psi (M : ℝ) := by
  have hIco :
      chebyshevSqrtConvexPotential M - chebyshevSqrtConvexPotential N =
        ∑ k ∈ Finset.Ico (N - 2) (M - 2),
          (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) * Chebyshev.psi (k + 2 : ℕ) := by
    unfold chebyshevSqrtConvexPotential
    exact (Finset.sum_Ico_eq_sub _ (show N - 2 ≤ M - 2 by omega)).symm
  rw [hIco, ← sum_Ico_sqrt_succ_sub_sqrt_eq hN hNM, Finset.sum_mul, Finset.sum_mul]
  constructor
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_Ico.mp hk
    have hdiff : 0 ≤ Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show k + 2 ≤ k + 3 by omega))
    exact mul_le_mul_of_nonneg_left
      (Chebyshev.psi_mono (by exact_mod_cast (show N ≤ k + 2 by omega))) hdiff
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_Ico.mp hk
    have hdiff : 0 ≤ Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show k + 2 ≤ k + 3 by omega))
    exact mul_le_mul_of_nonneg_left
      (Chebyshev.psi_mono (by exact_mod_cast (show k + 2 ≤ M by omega))) hdiff

/-- **Exact Three-Point `√M`-Convexity of `chebyshevSqrtConvexPotential`:**
For all `2 ≤ L < N < M`,
`(chebyshevSqrtConvexPotential N - chebyshevSqrtConvexPotential L) / (√N - √L) ≤ ψ(N)` and
`ψ(N) ≤ (chebyshevSqrtConvexPotential M - chebyshevSqrtConvexPotential N) / (√M - √N)`. -/
theorem chebyshevSqrtConvexPotential_secant_slope_mono
    {L N M : ℕ} (hL : 2 ≤ L) (hLN : L < N) (hNM : N < M) :
    (chebyshevSqrtConvexPotential N - chebyshevSqrtConvexPotential L) /
        (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) ≤ Chebyshev.psi (N : ℝ) ∧
      Chebyshev.psi (N : ℝ) ≤
        (chebyshevSqrtConvexPotential M - chebyshevSqrtConvexPotential N) /
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) := by
  have hsLN : 0 < Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hLN)
  have hsNM : 0 < Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hNM)
  have h1 := (chebyshevSqrtConvexPotential_sub_bounds hL hLN.le).2
  have h2 := (chebyshevSqrtConvexPotential_sub_bounds (hL.trans hLN.le) hNM.le).1
  constructor
  · rw [div_le_iff₀ hsLN, mul_comm]
    exact h1
  · rw [le_div_iff₀ hsNM, mul_comm]
    exact h2

/-- **Square-Sample Convexity Identity:**
Evaluated at consecutive squares `K^2` and `(K + 1)^2` (`K ≥ 2`), the denominator
`√((K + 1)^2) - √(K^2) = 1`, so the first difference of `chebyshevSqrtConvexPotential (K^2)` is
sandwiched directly between `ψ(K^2)` and `ψ((K + 1)^2)`:
`ψ(K^2) ≤ chebyshevSqrtConvexPotential ((K + 1)^2) - chebyshevSqrtConvexPotential (K^2) ≤ ψ((K + 1)^2)`. -/
theorem chebyshevSqrtConvexPotential_sq_succ_sub_bounds {K : ℕ} (hK : 2 ≤ K) :
    Chebyshev.psi ((K ^ 2 : ℕ) : ℝ) ≤
        chebyshevSqrtConvexPotential ((K + 1) ^ 2) - chebyshevSqrtConvexPotential (K ^ 2) ∧
      chebyshevSqrtConvexPotential ((K + 1) ^ 2) - chebyshevSqrtConvexPotential (K ^ 2) ≤
        Chebyshev.psi (((K + 1) ^ 2 : ℕ) : ℝ) := by
  have hK2 : 2 ≤ K ^ 2 := by nlinarith
  have hle : K ^ 2 ≤ (K + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ K) 2
  have hbounds := chebyshevSqrtConvexPotential_sub_bounds hK2 hle
  have hdiff : Real.sqrt (((K + 1) ^ 2 : ℕ) : ℝ) - Real.sqrt ((K ^ 2 : ℕ) : ℝ) = 1 := by
    have h1 : Real.sqrt (((K + 1) ^ 2 : ℕ) : ℝ) = (K : ℝ) + 1 := by
      push_cast
      exact Real.sqrt_sq (by positivity)
    have h2 : Real.sqrt ((K ^ 2 : ℕ) : ℝ) = (K : ℝ) := by
      push_cast
      exact Real.sqrt_sq (by positivity)
    linarith
  rw [hdiff, one_mul, one_mul] at hbounds
  exact hbounds

/-- **Exact Secant-Slope Sandwich for `secularSqrtIncrementAction`:**
For all `2 ≤ N ≤ M`,
`(√M - √N) * N ≤ secularSqrtIncrementAction M - secularSqrtIncrementAction N ≤ (√M - √N) * M`. -/
theorem secularSqrtIncrementAction_sub_bounds {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (N : ℝ) ≤
        secularSqrtIncrementAction M - secularSqrtIncrementAction N ∧
      secularSqrtIncrementAction M - secularSqrtIncrementAction N ≤
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (M : ℝ) := by
  have hIco :
      secularSqrtIncrementAction M - secularSqrtIncrementAction N =
        ∑ k ∈ Finset.Ico (N - 2) (M - 2),
          (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) * (k + 2 : ℕ) := by
    unfold secularSqrtIncrementAction
    exact (Finset.sum_Ico_eq_sub _ (show N - 2 ≤ M - 2 by omega)).symm
  rw [hIco, ← sum_Ico_sqrt_succ_sub_sqrt_eq hN hNM, Finset.sum_mul, Finset.sum_mul]
  constructor
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_Ico.mp hk
    have hdiff : 0 ≤ Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show k + 2 ≤ k + 3 by omega))
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show N ≤ k + 2 by omega)) hdiff
  · refine Finset.sum_le_sum fun k hk => ?_
    have hk' := Finset.mem_Ico.mp hk
    have hdiff : 0 ≤ Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ) := by
      rw [sub_nonneg]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (show k + 2 ≤ k + 3 by omega))
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show k + 2 ≤ M by omega)) hdiff

/-- **Exact Constant-Free Secant Sandwich for `chebyshevSqrtIncrementAction`:**
For all `2 ≤ N ≤ M`,
`(√M - √N) * (ψ(N) - M) ≤ chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N ≤ (√M - √N) * (ψ(M) - N)`. -/
theorem chebyshevSqrtIncrementAction_sub_bounds {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (Chebyshev.psi (N : ℝ) - (M : ℝ)) ≤
        chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N ∧
      chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N ≤
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (Chebyshev.psi (M : ℝ) - (N : ℝ)) := by
  have hψ := chebyshevSqrtConvexPotential_sub_bounds hN hNM
  have hsec := secularSqrtIncrementAction_sub_bounds hN hNM
  rw [chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular M,
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular N]
  constructor <;> linarith

/-- **Three-Point Approximate Convexity (Second-Difference Lower Bound) of
`chebyshevSqrtIncrementAction` in `√M`:**
For all `2 ≤ L < N < M`, the interior value `ψ(N)` cancels identically between the forward
difference quotient on `[N, M]` and the backward difference quotient on `[L, N]`, yielding
`(chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) / (√M - √N) - (chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction L) / (√N - √L) ≥ -(M - L)`. -/
theorem chebyshevSqrtIncrementAction_secant_slope_sub_ge
    {L N M : ℕ} (hL : 2 ≤ L) (hLN : L < N) (hNM : N < M) :
    -((M : ℝ) - L) ≤
      (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) /
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) -
        (chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction L) /
          (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) := by
  have hsLN : 0 < Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hLN)
  have hsNM : 0 < Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hNM)
  have h1 : (chebyshevSqrtIncrementAction N - chebyshevSqrtIncrementAction L) /
      (Real.sqrt (N : ℝ) - Real.sqrt (L : ℝ)) ≤ Chebyshev.psi (N : ℝ) - (L : ℝ) := by
    rw [div_le_iff₀ hsLN, mul_comm]
    exact (chebyshevSqrtIncrementAction_sub_bounds hL hLN.le).2
  have h2 : Chebyshev.psi (N : ℝ) - (M : ℝ) ≤
      (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) /
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) := by
    rw [le_div_iff₀ hsNM, mul_comm]
    exact (chebyshevSqrtIncrementAction_sub_bounds (hL.trans hLN.le) hNM.le).1
  linarith

/-- **Tauberian Pointwise Upper Extraction for `ψ(N) - N`:**
For any `2 ≤ N < M`, `ψ(N) - N` is bounded above by the forward secant slope of
`chebyshevSqrtIncrementAction` on `[N, M]` plus the window length `M - N`:
`ψ(N) - N ≤ (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) / (√M - √N) + (M - N)`. -/
theorem psi_sub_le_forward_secant_chebyshevSqrtIncrementAction
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N < M) :
    Chebyshev.psi (N : ℝ) - (N : ℝ) ≤
      (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) /
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) +
        ((M : ℝ) - N) := by
  have hsNM : 0 < Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hNM)
  have h := (chebyshevSqrtIncrementAction_sub_bounds hN hNM.le).1
  have hdiv : Chebyshev.psi (N : ℝ) - (M : ℝ) ≤
      (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) /
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) := by
    rw [le_div_iff₀ hsNM, mul_comm]
    exact h
  linarith

/-- **Tauberian Pointwise Lower Extraction for `ψ(M) - M`:**
For any `2 ≤ N < M`, `ψ(M) - M` is bounded below by the backward secant slope of
`chebyshevSqrtIncrementAction` on `[N, M]` minus the window length `M - N`:
`(chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) / (√M - √N) - (M - N) ≤ ψ(M) - M`. -/
theorem psi_sub_ge_backward_secant_chebyshevSqrtIncrementAction
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N < M) :
    (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) /
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) -
      ((M : ℝ) - N) ≤
      Chebyshev.psi (M : ℝ) - (M : ℝ) := by
  have hsNM : 0 < Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_pos]
    exact Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hNM)
  have h := (chebyshevSqrtIncrementAction_sub_bounds hN hNM.le).2
  have hdiv :
      (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) /
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) ≤ Chebyshev.psi (M : ℝ) - (N : ℝ) := by
    rw [div_le_iff₀ hsNM, mul_comm]
    exact h
  linarith

/-! ## Section 3: Jensen Secant Upper Interpolation and Breaking the `√n` Mesh Barrier
to `O(n^{3/4})` Gaps for One-Sided RH Criteria -/

/-- **Exact Jensen Secant Upper Bound for `chebyshevSqrtConvexPotential` on `[N, M]`:**
For any `2 ≤ N ≤ P ≤ M`, eliminating `ψ(P)` between `[N, P]` and `[P, M]` proves that
`chebyshevSqrtConvexPotential P` lies below the secant line connecting `(√N, Φ N)` and `(√M, Φ M)`
with **zero error**:
`(√M - √N) * chebyshevSqrtConvexPotential P ≤ (√M - √P) * chebyshevSqrtConvexPotential N + (√P - √N) * chebyshevSqrtConvexPotential M`. -/
theorem chebyshevSqrtConvexPotential_jensen_secant_le
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtConvexPotential P ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSqrtConvexPotential N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtConvexPotential M := by
  have hsNP : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
  have hsPM : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hPM)
  have hleft := (chebyshevSqrtConvexPotential_sub_bounds hN hNP).2
  have hright := (chebyshevSqrtConvexPotential_sub_bounds (hN.trans hNP) hPM).1
  have h1 := mul_le_mul_of_nonneg_left hleft hsPM
  have h2 := mul_le_mul_of_nonneg_left hright hsNP
  nlinarith

/-- **Exact Jensen Secant Upper Bound for `chebyshevSqrtIncrementAction` on `[N, M]`:**
For any `2 ≤ N ≤ P ≤ M`, eliminating `ψ(P)` between `[N, P]` and `[P, M]` bounds
`(√M - √N) * chebyshevSqrtIncrementAction P` by its secant combination plus the pure secular
curvature `(√M - √P) * (√P - √N) * (M - N)`:
`(√M - √N) * F P ≤ (√M - √P) * F N + (√P - √N) * F M + (√M - √P) * (√P - √N) * (M - N)`. -/
theorem chebyshevSqrtIncrementAction_jensen_secant_le
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtIncrementAction P ≤
      (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSqrtIncrementAction N +
        (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtIncrementAction M +
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
          (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) - N) := by
  have hsNP : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
  have hsPM : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ) := by
    rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hPM)
  have hleft := (chebyshevSqrtIncrementAction_sub_bounds hN hNP).2
  have hright := (chebyshevSqrtIncrementAction_sub_bounds (hN.trans hNP) hPM).1
  have h1 := mul_le_mul_of_nonneg_left hleft hsPM
  have h2 := mul_le_mul_of_nonneg_left hright hsNP
  nlinarith

/-- **Prime-Free Endpoint-Max Upper Bound for `chebyshevSqrtIncrementAction` on `[N, M]`:**
For all `2 ≤ N ≤ P ≤ M`,
`chebyshevSqrtIncrementAction P ≤ max (chebyshevSqrtIncrementAction N) (chebyshevSqrtIncrementAction M) + (M - N)^2 / (2 * √N)`.
Unlike `integerLag` chord interpolation, there is **no prime sum, no Mertens sum, and no
logarithmic factor** in the interpolation error — only the deterministic secular curvature
`(M - N)^2 / (2 * √N)`. -/
theorem chebyshevSqrtIncrementAction_le_max_add_sq_div_sqrt
    {N P M : ℕ} (hN : 2 ≤ N) (hNP : N ≤ P) (hPM : P ≤ M) :
    chebyshevSqrtIncrementAction P ≤
      max (chebyshevSqrtIncrementAction N) (chebyshevSqrtIncrementAction M) +
        ((M : ℝ) - N) ^ 2 / (2 * Real.sqrt (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
  have hNM : N ≤ M := hNP.trans hPM
  rcases eq_or_lt_of_le hNM with hNM_eq | hNM_lt
  · have hP : P = N := by omega
    rw [← hNM_eq, hP]
    simp
  · have hsNM : 0 < Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
      rw [sub_pos]
      exact Real.sqrt_lt_sqrt hN0.le (by exact_mod_cast hNM_lt)
    have hsNP : 0 ≤ Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) := by
      rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hNP)
    have hsPM : 0 ≤ Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ) := by
      rw [sub_nonneg]; exact Real.sqrt_le_sqrt (by exact_mod_cast hPM)
    have hjensen := chebyshevSqrtIncrementAction_jensen_secant_le hN hNP hPM
    set μ := max (chebyshevSqrtIncrementAction N) (chebyshevSqrtIncrementAction M)
    have hμN : chebyshevSqrtIncrementAction N ≤ μ := le_max_left _ _
    have hμM : chebyshevSqrtIncrementAction M ≤ μ := le_max_right _ _
    have hsec_max :
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSqrtIncrementAction N +
          (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtIncrementAction M ≤
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * μ := by
      calc
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * chebyshevSqrtIncrementAction N +
            (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtIncrementAction M ≤
          (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * μ +
            (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * μ :=
          add_le_add (mul_le_mul_of_nonneg_left hμN hsPM) (mul_le_mul_of_nonneg_left hμM hsNP)
        _ = (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * μ := by ring
    have hprod_le :
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) * (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) ≤
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
            (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) := by
      have h1 : Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ) ≤ Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
        linarith
      have h2 : Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ) ≤ Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) := by
        linarith
      exact mul_le_mul h1 h2 hsNP hsNM.le
    have hsqrt_diff_le :
        Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ) ≤
          ((M : ℝ) - N) / (2 * Real.sqrt (N : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      have hsqM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt hN0.le
      calc
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * (2 * Real.sqrt (N : ℝ)) ≤
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
            (Real.sqrt (M : ℝ) + Real.sqrt (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hsNM.le
        _ = Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) -
            Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := by ring
        _ = (M : ℝ) - N := by rw [hsqM, hsqN]
    have hcurv_le :
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
            (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) - N) ≤
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
            (((M : ℝ) - N) ^ 2 / (2 * Real.sqrt (N : ℝ))) := by
      have hMN0 : 0 ≤ (M : ℝ) - N := sub_nonneg.mpr (by exact_mod_cast hNM)
      calc
        (Real.sqrt (M : ℝ) - Real.sqrt (P : ℝ)) *
            (Real.sqrt (P : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) - N) ≤
          ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
            (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ))) * ((M : ℝ) - N) :=
          mul_le_mul_of_nonneg_right hprod_le hMN0
        _ = (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
            ((Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * ((M : ℝ) - N)) := by ring
        _ ≤ (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
            ((((M : ℝ) - N) / (2 * Real.sqrt (N : ℝ))) * ((M : ℝ) - N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrt_diff_le hMN0) hsNM.le
        _ = (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
            (((M : ℝ) - N) ^ 2 / (2 * Real.sqrt (N : ℝ))) := by ring
    have htotal :
        (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) * chebyshevSqrtIncrementAction P ≤
          (Real.sqrt (M : ℝ) - Real.sqrt (N : ℝ)) *
            (μ + ((M : ℝ) - N) ^ 2 / (2 * Real.sqrt (N : ℝ))) := by
      linarith
    exact le_of_mul_le_mul_left htotal hsNM

/-- **Upper Bounds Transfer Along `O(n^{3/4})`-Gap Meshes (`(M - N)^2 ≤ K * N * √N`):**
If a sampling set `A ⊆ ℕ` brackets every `P ≥ N₁` by `N, M ∈ A` with
`3 ≤ N ≤ P ≤ M ≤ 2 * N` and `(M - N)^2 ≤ K * N * √N` (so `M - N ≤ √K * N^{3/4}`), and
`chebyshevSqrtIncrementAction n ≤ C * n` on `A`, then `chebyshevSqrtIncrementAction P ≤ C' * P`
for all `P ≥ 3`. -/
theorem chebyshevSqrtIncrementAction_le_of_three_quarter_mesh_samples
    {A : Set ℕ} {C K : ℝ} {N₁ : ℕ}
    (hK : 0 ≤ K)
    (hA : ∀ n ∈ A, 3 ≤ n → chebyshevSqrtIncrementAction n ≤ C * (n : ℝ))
    (hdense : ∀ P : ℕ, N₁ ≤ P → ∃ N ∈ A, ∃ M ∈ A,
      3 ≤ N ∧ N ≤ P ∧ P ≤ M ∧ M ≤ 2 * N ∧
      ((M : ℝ) - N) ^ 2 ≤ K * (N : ℝ) * Real.sqrt (N : ℝ)) :
    ∃ C' : ℝ, ∀ P : ℕ, 3 ≤ P → chebyshevSqrtIncrementAction P ≤ C' * (P : ℝ) := by
  classical
  set B : ℝ := (Finset.range (N₁ + 3)).sup' ⟨0, by simp⟩
    fun P => chebyshevSqrtIncrementAction P
  refine ⟨max B (2 * |C| + K / 2), fun P hP3 => ?_⟩
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast (show 1 ≤ P by omega)
  rcases lt_or_ge P N₁ with hlt | hge
  · have hleB : chebyshevSqrtIncrementAction P ≤ B :=
      Finset.le_sup' (fun P => chebyshevSqrtIncrementAction P)
        (Finset.mem_range.mpr (by omega))
    have hB_le : B ≤ max B (2 * |C| + K / 2) := le_max_left _ _
    have hmax_nonneg : 0 ≤ max B (2 * |C| + K / 2) :=
      le_trans (by positivity) (le_max_right B (2 * |C| + K / 2))
    calc
      chebyshevSqrtIncrementAction P ≤ max B (2 * |C| + K / 2) := hleB.trans hB_le
      _ = max B (2 * |C| + K / 2) * 1 := by ring
      _ ≤ max B (2 * |C| + K / 2) * (P : ℝ) :=
        mul_le_mul_of_nonneg_left hP1 hmax_nonneg
  · obtain ⟨N, hNA, M, hMA, hN3, hNP, hPM, hM2N, hgap⟩ := hdense P hge
    have hN2 : 2 ≤ N := by omega
    have hM3 : 3 ≤ M := hN3.trans (hNP.trans hPM)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
    have hjensen := chebyshevSqrtIncrementAction_le_max_add_sq_div_sqrt hN2 hNP hPM
    have hCN : chebyshevSqrtIncrementAction N ≤ 2 * |C| * (P : ℝ) := by
      have h1 := hA N hNA hN3
      have h2 : C ≤ |C| := le_abs_self C
      have hNP_cast : (N : ℝ) ≤ P := by exact_mod_cast hNP
      calc
        chebyshevSqrtIncrementAction N ≤ C * (N : ℝ) := h1
        _ ≤ |C| * (N : ℝ) := mul_le_mul_of_nonneg_right h2 hN0.le
        _ ≤ 2 * |C| * (P : ℝ) := by nlinarith [abs_nonneg C]
    have hCM : chebyshevSqrtIncrementAction M ≤ 2 * |C| * (P : ℝ) := by
      have h1 := hA M hMA hM3
      have h2 : C ≤ |C| := le_abs_self C
      have hM0 : (0 : ℝ) ≤ M := by positivity
      have hM2P : (M : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast (show M ≤ 2 * P by omega)
      calc
        chebyshevSqrtIncrementAction M ≤ C * (M : ℝ) := h1
        _ ≤ |C| * (M : ℝ) := mul_le_mul_of_nonneg_right h2 hM0
        _ ≤ 2 * |C| * (P : ℝ) := by nlinarith [abs_nonneg C]
    have hmax_le :
        max (chebyshevSqrtIncrementAction N) (chebyshevSqrtIncrementAction M) ≤
          2 * |C| * (P : ℝ) := max_le hCN hCM
    have hcurv_le :
        ((M : ℝ) - N) ^ 2 / (2 * Real.sqrt (N : ℝ)) ≤ (K / 2) * (P : ℝ) := by
      have hdiv :
          ((M : ℝ) - N) ^ 2 / (2 * Real.sqrt (N : ℝ)) ≤ (K / 2) * (N : ℝ) := by
        rw [div_le_iff₀ (by positivity)]
        calc
          ((M : ℝ) - N) ^ 2 ≤ K * (N : ℝ) * Real.sqrt (N : ℝ) := hgap
          _ = (K / 2) * (N : ℝ) * (2 * Real.sqrt (N : ℝ)) := by ring
      have hNP_cast : (N : ℝ) ≤ P := by exact_mod_cast hNP
      exact hdiv.trans (mul_le_mul_of_nonneg_left hNP_cast (by positivity))
    have hP_bound : chebyshevSqrtIncrementAction P ≤ (2 * |C| + K / 2) * (P : ℝ) := by
      linarith
    exact hP_bound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

/-- **One-Sided `O(n^{3/4})`-Gap Mesh RH Equivalence for `chebyshevSqrtIncrementAction`:**
For any sampling set `A ⊆ ℕ` that brackets every `P ≥ N₁` by `N, M ∈ A` with
`3 ≤ N ≤ P ≤ M ≤ 2 * N` and `(M - N)^2 ≤ K * N * √N` (gaps up to `O(N^{3/4})`), the Riemann
Hypothesis holds if and only if `chebyshevSqrtIncrementAction n ≤ C * n` on `A`. -/
theorem riemannHypothesis_iff_three_quarter_mesh_chebyshevSqrtIncrementAction_boundedAbove
    {A : Set ℕ} {K : ℝ} {N₁ : ℕ} (hK : 0 ≤ K)
    (hdense : ∀ P : ℕ, N₁ ≤ P → ∃ N ∈ A, ∃ M ∈ A,
      3 ≤ N ∧ N ≤ P ∧ P ≤ M ∧ M ≤ 2 * N ∧
      ((M : ℝ) - N) ^ 2 ≤ K * (N : ℝ) * Real.sqrt (N : ℝ)) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ n ∈ A, 3 ≤ n → chebyshevSqrtIncrementAction n ≤ C * (n : ℝ) := by
  rw [riemannHypothesis_iff_chebyshevSqrtIncrementAction_boundedAbove]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun n _ hn => hC n hn⟩
  · rintro ⟨C, hC⟩
    exact chebyshevSqrtIncrementAction_le_of_three_quarter_mesh_samples hK hC hdense

/-- **One-Sided `O(n^{3/4})`-Gap Mesh RH Equivalence for `chebyshevNormalizedCesaroSum`:**
For any sampling set `A ⊆ ℕ` that brackets every `P ≥ N₁` by `N, M ∈ A` with
`3 ≤ N ≤ P ≤ M ≤ 2 * N` and `(M - N)^2 ≤ K * N * √N` (gaps up to `O(N^{3/4})`), the Riemann
Hypothesis holds if and only if `chebyshevNormalizedCesaroSum n ≤ C * n` on `A`. -/
theorem riemannHypothesis_iff_three_quarter_mesh_chebyshevNormalizedCesaroSum_boundedAbove
    {A : Set ℕ} {K : ℝ} {N₁ : ℕ} (hK : 0 ≤ K)
    (hdense : ∀ P : ℕ, N₁ ≤ P → ∃ N ∈ A, ∃ M ∈ A,
      3 ≤ N ∧ N ≤ P ∧ P ≤ M ∧ M ≤ 2 * N ∧
      ((M : ℝ) - N) ^ 2 ≤ K * (N : ℝ) * Real.sqrt (N : ℝ)) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ n ∈ A, 3 ≤ n → chebyshevNormalizedCesaroSum n ≤ C * (n : ℝ) := by
  rw [riemannHypothesis_iff_three_quarter_mesh_chebyshevSqrtIncrementAction_boundedAbove hK hdense]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨2 * (C + 3), fun n hnA hn3 => ?_⟩
    have h1 := hC n hnA hn3
    have h2 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le n)).2
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨(1 / 2 : ℝ) * C + 3, fun n hnA hn3 => ?_⟩
    have h1 := hC n hnA hn3
    have h2 := (abs_sub_le_iff.mp
      (abs_chebyshevSqrtIncrementAction_sub_half_normalizedCesaroSum_le n)).1
    linarith

/-- **One-Sided `O(n^{3/4})`-Gap Mesh RH Equivalence for `mobiusDivisorSquareRootAbelMoment`:**
For any sampling set `A ⊆ ℕ` that brackets every `P ≥ N₁` by `N, M ∈ A` with
`3 ≤ N ≤ P ≤ M ≤ 2 * N` and `(M - N)^2 ≤ K * N * √N` (gaps up to `O(N^{3/4})`), the Riemann
Hypothesis holds if and only if `mobiusDivisorSquareRootAbelMoment n ≤ C * n` on `A`. -/
theorem riemannHypothesis_iff_three_quarter_mesh_mobiusDivisorSquareRootAbel_boundedAbove
    {A : Set ℕ} {K : ℝ} {N₁ : ℕ} (hK : 0 ≤ K)
    (hdense : ∀ P : ℕ, N₁ ≤ P → ∃ N ∈ A, ∃ M ∈ A,
      3 ≤ N ∧ N ≤ P ∧ P ≤ M ∧ M ≤ 2 * N ∧
      ((M : ℝ) - N) ^ 2 ≤ K * (N : ℝ) * Real.sqrt (N : ℝ)) :
    RiemannHypothesis ↔
      ∃ C : ℝ, ∀ n ∈ A, 3 ≤ n → mobiusDivisorSquareRootAbelMoment n ≤ C * (n : ℝ) := by
  obtain ⟨B, _hB0, hB⟩ :=
    exists_abs_mobiusDivisorSquareRootAbel_sub_half_chebyshevNormalizedCesaroSum_linear
  rw [riemannHypothesis_iff_three_quarter_mesh_chebyshevNormalizedCesaroSum_boundedAbove hK hdense]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨(1 / 2 : ℝ) * C + B, fun n hnA hn3 => ?_⟩
    have h1 := hC n hnA hn3
    have h2 := (abs_sub_le_iff.mp (hB n hn3)).1
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨2 * (C + B), fun n hnA hn3 => ?_⟩
    have h1 := hC n hnA hn3
    have h2 := (abs_sub_le_iff.mp (hB n hn3)).2
    linarith

/-- **Explicit Quartic Mesh Verification (`s(k) = (k + 7)^4`):**
The quartic sequence `s(k) = (k + 7)^4` satisfies `s(k + 1) ≤ 2 * s(k)` and the `O(n^{3/4})`-gap
law `((s(k + 1) : ℝ) - s(k))^2 ≤ 49 * s(k) * √(s(k))` for all `k : ℕ`. -/
theorem quartic_mesh_step_bounds (k : ℕ) :
    (k + 7 + 1) ^ 4 ≤ 2 * (k + 7) ^ 4 ∧
      ((((k + 7 + 1) ^ 4 : ℕ) : ℝ) - ((k + 7) ^ 4 : ℕ)) ^ 2 ≤
        49 * (((k + 7) ^ 4 : ℕ) : ℝ) * Real.sqrt (((k + 7) ^ 4 : ℕ) : ℝ) := by
  constructor
  · rw [← Nat.cast_le (α := ℝ)]
    push_cast
    have hpos : (0 : ℝ) ≤
        (k : ℝ) ^ 4 + 24 * (k : ℝ) ^ 3 + 204 * (k : ℝ) ^ 2 + 696 * (k : ℝ) + 706 := by
      positivity
    linarith
  · have hsqrt : Real.sqrt (((k + 7) ^ 4 : ℕ) : ℝ) = (((k : ℝ) + 7) ^ 2) := by
      have hsq : (((k + 7) ^ 4 : ℕ) : ℝ) = (((k : ℝ) + 7) ^ 2) ^ 2 := by push_cast; ring
      rw [hsq]
      exact Real.sqrt_sq (by positivity)
    rw [hsqrt]
    push_cast
    have hpos : (0 : ℝ) ≤
        2891776 + (k : ℝ) * 2649618 + (k : ℝ) ^ 2 * 1002659 + (k : ℝ) ^ 3 * 200900 +
          (k : ℝ) ^ 4 * 22507 + (k : ℝ) ^ 5 * 1338 + (k : ℝ) ^ 6 * 33 := by
      positivity
    have hident :
        49 * ((k : ℝ) + 7) ^ 4 * ((k : ℝ) + 7) ^ 2 -
            (((k : ℝ) + 7 + 1) ^ 4 - ((k : ℝ) + 7) ^ 4) ^ 2 =
          2891776 + (k : ℝ) * 2649618 + (k : ℝ) ^ 2 * 1002659 + (k : ℝ) ^ 3 * 200900 +
            (k : ℝ) ^ 4 * 22507 + (k : ℝ) ^ 5 * 1338 + (k : ℝ) ^ 6 * 33 := by
      ring
    linarith

end

end GaloisForLFunctions.RHTower
