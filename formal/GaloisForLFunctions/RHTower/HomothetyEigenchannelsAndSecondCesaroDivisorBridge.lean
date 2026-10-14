import GaloisForLFunctions.RHTower.MobiusDivisorCesaroAndSquareGridSqrtRieszBridge

/-!
# Telescoping Cell-Integral Homothety Eigenchannels, the Exact Outgoing-Charge / Convex-Potential Weld, and Second-Cesàro / Square-Root Riesz Möbius–Divisor Bridges

This module advances the unconditional RHTower hierarchy beyond
`MobiusDivisorCesaroAndSquareGridSqrtRieszBridge.lean` (Module 31) by establishing a general
**Telescoping Cell-Integral Homothety Principle** for Möbius–divisor dilation channels, discovering
the exact cancellation between the secular part of `coherentSelbergSquareRootAbelMoment` and
`coherentSquareRootPolarLatticeDefect`, and constructing the **pure degree-2 Midpoint Second-Cesàro**
and **pure degree-`3/2` Cell-Integral Square-Root Riesz** dilation eigenchannels:

## Mathematical Overview

1. **Section 1 (Master Weighted Dilation Fubini & Block-Telescoping Homothety Principles, and the
   Exact Outgoing-Charge / Convex-Potential Weld):**
   - For any weight `w : ℕ → ℝ`, `primeFreeDivisorDefect (k / d)` vanishes for `k < d` because
     `primeFreeDivisorDefect 0 = 0`. We prove the general prefix-range reduction
     `sum_Icc_mul_primeFreeDivisorDefect_eq_range`, the general weighted Fubini law
     `sum_Icc_psiDefect_weighted_eq_sum_dilation`, the residue-block factorization
     `sum_range_mul_primeFreeDivisorDefect_block_eq`, and the shifted telescoping lemma
     `sum_range_sub_shift`.
   - We prove the exact identity `sum_Icc_sqrt_sub_eq_secularSqrtIncrementAction_add`:
     for all `M ≥ 2`,
     `∑ k ∈ Icc 1 (M - 1), (√M - √k) = secularSqrtIncrementAction M + (√2 - 1)`.
   - Consequently, `coherentSquareRootPolarLatticeDefect M = secularSqrtIncrementAction M + (√2 - 1) - M * √M / 3`
     (`coherentSquareRootPolarLatticeDefect_eq_secularSqrtIncrementAction`). When added to
     `coherentSelbergSquareRootAbelMoment M = chebyshevSqrtConvexPotential M - secularSqrtIncrementAction M - (√2 - 1)`,
     both `secularSqrtIncrementAction M` and `√2 - 1` **cancel identically to zero**, yielding the
     exact zero-error weld (`coherentCompletedOutgoing_mul_eq_chebyshevSqrtConvexPotential_sub`):
     `M * unitRieszCoherentCompletedOutgoingCharge M = chebyshevSqrtConvexPotential M - M * √M / 3`.
     This proves that `M * unitRieszCoherentCompletedOutgoingCharge M + M * √M / 3 = Φ_√(M)` is
     unconditionally monotone increasing in `M` and unconditionally convex on the square grid `M = m^2`!

2. **Section 2 (Second-Cesàro and Midpoint Second-Cesàro Möbius–Divisor Dilation Channels and Exact
   Degree-2 Integer Homothety):**
   - We define `divisorUnsignedSecondCesaroDilationChannel M d` (weight `M - k`) and
     `divisorUnsignedMidpointSecondCesaroDilationChannel M d` (cell-integral weight
     `∫_k^{k+1} (M - t) dt = M - k - 1 / 2`), together with their signed `μ(d)` counterparts.
   - Because `M - k - 1 / 2 = G(M, k + 1) - G(M, k)` with `G(M, k) = M * k - k^2 / 2` homogeneous of
     degree `2`, `divisorUnsignedMidpointSecondCesaroDilationChannel` is an **exact degree-2
     integer-dilation eigenchannel** with zero lower-order error
     (`divisorUnsignedMidpointSecondCesaroDilationChannel_mul`):
     `divisorUnsignedMidpointSecondCesaroDilationChannel (r * M) (r * d) = r^2 * divisorUnsignedMidpointSecondCesaroDilationChannel M d`.
   - From `D₂(M, d) = D₂^{\mathrm{mid}}(M, d) + (1 / 2) * D₁(M, d)`, we deduce the exact shifted
     homothety law for the unshifted Second-Cesàro channel
     (`divisorUnsignedSecondCesaroDilationChannel_mul`):
     `D₂(r * M, r * d) = r^2 * D₂(M, d) - (r * (r - 1) / 2) * D₁(M, d)`.

3. **Section 3 (Exact Cofinal Sum Bridges for `chebyshevSecondCesaroSum` (`C₂(M)`), Midpoint
   Second-Cesàro Sum, and Square-Grid Central Differences):**
   - For all `M ≥ 2`, we prove the exact cofinal decomposition of `chebyshevSecondCesaroSum M`
     (`chebyshevSecondCesaroSum_eq_sum_mobiusDivisorSecondCesaroDilationChannel_sub`):
     `chebyshevSecondCesaroSum M = (∑ d ∈ Icc 1 (M - 1), mobiusDivisorSecondCesaroDilationChannel M d) - γ * M * (M - 1) + (M - 1)`,
     and its pure-square midpoint counterpart
     (`chebyshevSecondCesaroSum_sub_half_cesaro_eq_sum_mobiusDivisorMidpointSecondCesaroDilationChannel_sub`):
     `C₂(M) - (1 / 2) * C₁(M) = (∑ d ∈ Icc 1 (M - 1), mobiusDivisorMidpointSecondCesaroDilationChannel M d) - γ * (M - 1)^2 + (M - 3 / 2)`.

4. **Section 4 (Left, Right, Trapezoidal, and Cell-Integral Square-Root Riesz Dilation Channels,
   Pure Degree-`3/2` Integer Homothety, and Exact Cubic Euler–Maclaurin Completion):**
   - We define `divisorUnsignedSqrtRieszDilationChannel` (weight `√M - √(k + 1)`),
     `divisorUnsignedRightSqrtRieszDilationChannel` (weight `√M - √k`),
     `divisorUnsignedTrapezoidalSqrtRieszDilationChannel` (trapezoidal weight
     `((√M - √(k + 1)) + (√M - √k)) / 2`), and `divisorUnsignedCellSqrtRieszDilationChannel`
     (cell-integral weight `sqrtRieszCellIntegralWeight M k = ∫_k^{k+1} (√M - √t) dt = √M - (2 / 3) * ((k + 1)√(k + 1) - k√k)`).
   - We prove the step recurrence and conjugate inversion recovering `divisorUnsignedCesaroDilationChannel M d`
     from `divisorUnsignedSqrtRieszDilationChannel (M + 1) d - divisorUnsignedSqrtRieszDilationChannel M d`,
     the **pure degree-`3/2` integer homothety law** (`divisorUnsignedCellSqrtRieszDilationChannel_mul`):
     `divisorUnsignedCellSqrtRieszDilationChannel (r * M) (r * d) = r * √r * divisorUnsignedCellSqrtRieszDilationChannel M d`,
     and the exact cubic Euler–Maclaurin identity (`sqrtRieszCellIntegralWeight_eq_trapezoidal_sub_cube`):
     `sqrtRieszCellIntegralWeight M k = ((√M - √(k + 1)) + (√M - √k)) / 2 - (1 / 6) * (√(k + 1) - √k)^3`.

5. **Section 5 (Exact Cofinal Sum Bridges for `chebyshevRightSqrtRieszAction`,
   `chebyshevSqrtRieszAction`, `chebyshevTrapezoidalSqrtRieszAction`, and
   `mobiusDivisorCellSqrtRieszDilationChannel`):**
   - We prove the exact cofinal identities expressing `chebyshevRightSqrtRieszAction M`,
     `chebyshevSqrtRieszAction M`, `chebyshevTrapezoidalSqrtRieszAction M`, and
     `∑ d ∈ Icc 1 (M - 1), mobiusDivisorCellSqrtRieszDilationChannel M d` in terms of their
     signed Möbius–divisor dilation channels.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev ArithmeticFunction
open Real Finset _root_.RHTower

noncomputable section

/-! ## Section 1: Master Weighted Dilation Fubini & Block-Telescoping Homothety Principles, and the
Exact Outgoing-Charge / Convex-Potential Weld -/

/-- **General Prefix-Range Reduction for Weighted Floor-Dilation Sums:**
Because `primeFreeDivisorDefect 0 = 0` and `k / d = 0` for all `k < d`, the sum of
`w k * primeFreeDivisorDefect (k / d)` over `k ∈ Icc d (M - 1)` equals the full prefix sum over
`k ∈ range M` for every `M, d : ℕ` and every weight `w : ℕ → ℝ`. -/
theorem sum_Icc_mul_primeFreeDivisorDefect_eq_range (M d : ℕ) (w : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc d (M - 1), w k * primeFreeDivisorDefect (k / d)) =
      ∑ k ∈ Finset.range M, w k * primeFreeDivisorDefect (k / d) := by
  have hD0 : primeFreeDivisorDefect 0 = 0 := by simp [primeFreeDivisorDefect]
  by_cases hd : d = 0
  · simp [hd, hD0]
  by_cases hM : M = 0
  · simp [hM, Finset.Icc_eq_empty_of_lt (by omega : 0 < d)]
  by_cases hdM : d ≤ M
  · rw [← Finset.Ico_add_one_right_eq_Icc, show M - 1 + 1 = M by omega,
      Finset.sum_Ico_eq_sub _ hdM]
    have hz : (∑ k ∈ Finset.range d, w k * primeFreeDivisorDefect (k / d)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Nat.div_eq_of_lt (Finset.mem_range.mp hk), hD0, mul_zero]
    rw [hz, sub_zero]
  · rw [Finset.Icc_eq_empty_of_lt (by omega : M - 1 < d), Finset.sum_empty]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    rw [Nat.div_eq_of_lt (by have := Finset.mem_range.mp hk; omega : k < d), hD0, mul_zero]

/-- **General Weighted Dilation-Channel Fubini Law:**
For every `M : ℕ` and every weight `w : ℕ → ℝ`, transposing the triangular summation domain
`1 ≤ d ≤ k ≤ M - 1` yields:
`∑ k ∈ Icc 1 (M - 1), w k * psiDefect k = ∑ d ∈ Icc 1 (M - 1), μ(d) * (∑ k ∈ Icc d (M - 1), w k * primeFreeDivisorDefect (k / d))`. -/
theorem sum_Icc_psiDefect_weighted_eq_sum_dilation (M : ℕ) (w : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 (M - 1), w k * psiDefect k) =
      ∑ d ∈ Finset.Icc 1 (M - 1),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (∑ k ∈ Finset.Icc d (M - 1), w k * primeFreeDivisorDefect (k / d)) := by
  let K := Finset.Icc 1 (M - 1)
  have hpoint : ∀ k ∈ K,
      w k * psiDefect k =
        ∑ d ∈ K,
          if d ≤ k then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (w k * primeFreeDivisorDefect (k / d))
          else 0 := by
    intro k hk
    have hk' : k ∈ Finset.Icc 1 (M - 1) := by simpa only [K] using hk
    rw [psiDefect_eq_mobius_primeFreeDivisorDefect (Finset.mem_Icc.mp hk').1, Finset.mul_sum]
    have hset : Finset.Icc 1 k = K.filter (fun d => d ≤ k) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_filter, K]
      constructor
      · intro hd
        exact ⟨⟨hd.1, hd.2.trans (Finset.mem_Icc.mp hk').2⟩, hd.2⟩
      · intro hd
        exact ⟨hd.1.1, hd.2⟩
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> ring
  rw [show Finset.Icc 1 (M - 1) = K by rfl]
  calc
    (∑ k ∈ K, w k * psiDefect k) =
        ∑ k ∈ K, ∑ d ∈ K,
          if d ≤ k then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (w k * primeFreeDivisorDefect (k / d))
          else 0 := Finset.sum_congr rfl hpoint
    _ = ∑ d ∈ K, ∑ k ∈ K,
          if d ≤ k then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (w k * primeFreeDivisorDefect (k / d))
          else 0 := by rw [Finset.sum_comm]
    _ = ∑ d ∈ K,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            (∑ k ∈ Finset.Icc d (M - 1), w k * primeFreeDivisorDefect (k / d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' : d ∈ Finset.Icc 1 (M - 1) := by simpa only [K] using hd
      have hset : K.filter (fun k => d ≤ k) = Finset.Icc d (M - 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, K]
        constructor
        · intro hk
          exact ⟨hk.2, hk.1.2⟩
        · intro hk
          exact ⟨⟨(Finset.mem_Icc.mp hd').1.trans hk.1, hk.2⟩, hk.1⟩
      rw [← hset, Finset.mul_sum, Finset.sum_filter]

private theorem sum_range_mul_blocks' (r M : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (r * M), f k) =
      ∑ q ∈ Finset.range M, ∑ i ∈ Finset.range r, f (r * q + i) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- **General Residue-Block Factorization for Weighted Floor-Dilation Sums:**
For any `r > 0`, `M, d : ℕ`, and weight `w : ℕ → ℝ`, grouping `k ∈ range (r * M)` into blocks
`k = r * q + i` (`q ∈ range M`, `i ∈ range r`) factors `primeFreeDivisorDefect ((r * q + i) / (r * d)) = primeFreeDivisorDefect (q / d)`
outside the inner residue-class sum:
`∑ k ∈ range (r * M), w k * primeFreeDivisorDefect (k / (r * d)) = ∑ q ∈ range M, (∑ i ∈ range r, w (r * q + i)) * primeFreeDivisorDefect (q / d)`. -/
theorem sum_range_mul_primeFreeDivisorDefect_block_eq
    {r M d : ℕ} (hr : 0 < r) (w : ℕ → ℝ) :
    (∑ k ∈ Finset.range (r * M), w k * primeFreeDivisorDefect (k / (r * d))) =
      ∑ q ∈ Finset.range M,
        (∑ i ∈ Finset.range r, w (r * q + i)) * primeFreeDivisorDefect (q / d) := by
  rw [sum_range_mul_blocks']
  apply Finset.sum_congr rfl
  intro q _
  have hdiv (i : ℕ) (hi : i ∈ Finset.range r) : (r * q + i) / (r * d) = q / d := by
    rw [← Nat.div_div_eq_div_mul, Nat.mul_add_div hr,
      Nat.div_eq_of_lt (Finset.mem_range.mp hi), Nat.add_zero]
  calc
    (∑ i ∈ Finset.range r, w (r * q + i) * primeFreeDivisorDefect ((r * q + i) / (r * d))) =
        ∑ i ∈ Finset.range r, w (r * q + i) * primeFreeDivisorDefect (q / d) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hdiv i hi]
    _ = (∑ i ∈ Finset.range r, w (r * q + i)) * primeFreeDivisorDefect (q / d) := by
      rw [← Finset.sum_mul]

/-- Shifted telescoping sum over `i ∈ range r`:
`∑ i ∈ range r, (G (a + i + 1) - G (a + i)) = G (a + r) - G a`. -/
theorem sum_range_sub_shift (G : ℕ → ℝ) (a r : ℕ) :
    (∑ i ∈ Finset.range r, (G (a + i + 1) - G (a + i))) = G (a + r) - G a := by
  simpa only [Nat.add_assoc, Nat.add_zero] using
    Finset.sum_range_sub (fun i : ℕ => G (a + i)) r

/-- **Exact Identity Between the Square-Root Lattice Gap Sum and `secularSqrtIncrementAction`:**
For every integer `M ≥ 2`,
`∑ k ∈ Icc 1 (M - 1), (√M - √k) = secularSqrtIncrementAction M + (√2 - 1)`. -/
theorem sum_Icc_sqrt_sub_eq_secularSqrtIncrementAction_add
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.Icc 1 (M - 1), (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ))) =
      secularSqrtIncrementAction M + (Real.sqrt 2 - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    have h1 : 2 + 0 - 1 = 1 := by omega
    have h2 : 2 + 0 = 2 := by omega
    rw [h1, h2, Finset.Icc_self, Finset.sum_singleton]
    simp [secularSqrtIncrementAction]
  | succ n ih =>
    have hih := ih (by omega)
    have hsplit : Finset.Icc 1 (2 + (n + 1) - 1) =
        insert (2 + n) (Finset.Icc 1 (2 + n - 1)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : 2 + n ∉ Finset.Icc 1 (2 + n - 1) := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert hnotmem]
    have hsum_shift :
        (∑ k ∈ Finset.Icc 1 (2 + n - 1),
          (Real.sqrt ((2 + (n + 1) : ℕ) : ℝ) - Real.sqrt (k : ℝ))) =
        (∑ k ∈ Finset.Icc 1 (2 + n - 1),
          (Real.sqrt ((2 + n : ℕ) : ℝ) - Real.sqrt (k : ℝ))) +
        (((2 + n : ℕ) : ℝ) - 1) *
          (Real.sqrt ((2 + (n + 1) : ℕ) : ℝ) - Real.sqrt ((2 + n : ℕ) : ℝ)) := by
      have hrewrite :
          (∑ k ∈ Finset.Icc 1 (2 + n - 1),
            (Real.sqrt ((2 + (n + 1) : ℕ) : ℝ) - Real.sqrt (k : ℝ))) =
          ∑ k ∈ Finset.Icc 1 (2 + n - 1),
            ((Real.sqrt ((2 + n : ℕ) : ℝ) - Real.sqrt (k : ℝ)) +
              (Real.sqrt ((2 + (n + 1) : ℕ) : ℝ) - Real.sqrt ((2 + n : ℕ) : ℝ))) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [hrewrite, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
        show 2 + n - 1 + 1 - 1 = 2 + n - 1 by omega, nsmul_eq_mul,
        Nat.cast_sub (by omega : 1 ≤ 2 + n), Nat.cast_one]
    have hsec_step := secularSqrtIncrementAction_succ_sub_of_two_le n
    have hi3 : 2 + (n + 1) = n + 3 := by omega
    have hi2 : 2 + n = n + 2 := by omega
    have hc3 : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hc2 : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [hsum_shift, hih, hi3, hi2, hc3, hc2]
    linarith

/-- **Exact Secular Representation of `coherentSquareRootPolarLatticeDefect`:**
For every integer `M ≥ 2`,
`coherentSquareRootPolarLatticeDefect M = secularSqrtIncrementAction M + (√2 - 1) - M * √M / 3`. -/
theorem coherentSquareRootPolarLatticeDefect_eq_secularSqrtIncrementAction
    {M : ℕ} (hM : 2 ≤ M) :
    coherentSquareRootPolarLatticeDefect M =
      secularSqrtIncrementAction M + (Real.sqrt 2 - 1) -
        (M : ℝ) * Real.sqrt (M : ℝ) / 3 := by
  unfold coherentSquareRootPolarLatticeDefect
  rw [sum_Icc_sqrt_sub_eq_secularSqrtIncrementAction_add hM]

/-- **Exact Euler–Maclaurin Decomposition of `coherentSquareRootPolarLatticeDefect`:**
For every integer `M ≥ 2`,
`coherentSquareRootPolarLatticeDefect M = -(1 / 2) * √M + (√2 - 1) + (secularSqrtIncrementAction M - eulerMaclaurinSqrtIncrementSecular M)`.
This refines the coarse bracket `-√M ≤ D_M ≤ -(1 / 3) * √M` of
`CCMFUSuzukiSelbergOutgoingAbelWeld.lean` to an explicit `-(1 / 2) * √M + O(1)` asymptotics with
`1 / (24 * √M)` remainder. -/
theorem coherentSquareRootPolarLatticeDefect_eq_neg_half_sqrt_add_discrepancy
    {M : ℕ} (hM : 2 ≤ M) :
    coherentSquareRootPolarLatticeDefect M =
      -(1 / 2 : ℝ) * Real.sqrt (M : ℝ) + (Real.sqrt 2 - 1) +
        (secularSqrtIncrementAction M - eulerMaclaurinSqrtIncrementSecular M) := by
  rw [coherentSquareRootPolarLatticeDefect_eq_secularSqrtIncrementAction hM]
  unfold eulerMaclaurinSqrtIncrementSecular
  ring

/-- **Exact Zero-Error Cancellation Between `coherentSelbergSquareRootAbelMoment` and
`coherentSquareRootPolarLatticeDefect`:**
For every integer `M ≥ 2`, adding `coherentSelbergSquareRootAbelMoment M` and
`coherentSquareRootPolarLatticeDefect M` cancels both `secularSqrtIncrementAction M` and `√2 - 1`
identically to zero:
`coherentSelbergSquareRootAbelMoment M + coherentSquareRootPolarLatticeDefect M = chebyshevSqrtConvexPotential M - M * √M / 3`. -/
theorem coherentSelbergSquareRootAbelMoment_add_latticeDefect_eq_chebyshevSqrtConvexPotential_sub
    {M : ℕ} (hM : 2 ≤ M) :
    coherentSelbergSquareRootAbelMoment M + coherentSquareRootPolarLatticeDefect M =
      chebyshevSqrtConvexPotential M - (M : ℝ) * Real.sqrt (M : ℝ) / 3 := by
  rw [coherentSelbergSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_sub hM,
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular M,
    coherentSquareRootPolarLatticeDefect_eq_secularSqrtIncrementAction hM]
  ring

/-- **Exact Outgoing-Charge / Convex-Potential Weld:**
For every integer `M ≥ 2`, the unnormalized completed outgoing charge
`M * unitRieszCoherentCompletedOutgoingCharge M` equals the monotone, square-root-convex prime
potential `chebyshevSqrtConvexPotential M` (`Φ_√(M)`) minus the pure continuum monomial
`M * √M / 3`:
`M * unitRieszCoherentCompletedOutgoingCharge M = chebyshevSqrtConvexPotential M - M * √M / 3`. -/
theorem coherentCompletedOutgoing_mul_eq_chebyshevSqrtConvexPotential_sub
    {M : ℕ} (hM : 2 ≤ M) :
    (M : ℝ) * unitRieszCoherentCompletedOutgoingCharge M =
      chebyshevSqrtConvexPotential M - (M : ℝ) * Real.sqrt (M : ℝ) / 3 := by
  rw [coherentCompletedOutgoing_mul_eq_abel_add_latticeDefect hM,
    coherentSelbergSquareRootAbelMoment_add_latticeDefect_eq_chebyshevSqrtConvexPotential_sub hM]

/-- **Exact Three-Square Second-Difference Identity for `unitRieszCoherentCompletedOutgoingCharge`:**
On the square grid `M = s^2` (`s ≥ 2`), `s^2 * √(s^2) / 3 = s^3 / 3` has exact symmetric second
difference `2 * m * h^2`. Consequently, for all `h + 2 ≤ m`, the three-square second difference of
`M * unitRieszCoherentCompletedOutgoingCharge M` equals `Δ²_{sq, h} Φ_√(m) - 2 * m * h^2` with
**zero Euler–Maclaurin remainder**:
`Δ²_{sq, h} (M * unitRieszCoherentCompletedOutgoingCharge M) (m) = Δ²_{sq, h} chebyshevSqrtConvexPotential (m) - 2 * m * h^2`. -/
theorem coherentCompletedOutgoing_mul_square_second_diff_eq
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    (((m - h) ^ 2 : ℕ) : ℝ) * unitRieszCoherentCompletedOutgoingCharge ((m - h) ^ 2) +
        (((m + h) ^ 2 : ℕ) : ℝ) * unitRieszCoherentCompletedOutgoingCharge ((m + h) ^ 2) -
        2 * ((m ^ 2 : ℕ) : ℝ) * unitRieszCoherentCompletedOutgoingCharge (m ^ 2) =
      (chebyshevSqrtConvexPotential ((m - h) ^ 2) +
        chebyshevSqrtConvexPotential ((m + h) ^ 2) -
        2 * chebyshevSqrtConvexPotential (m ^ 2)) -
        2 * (m : ℝ) * (h : ℝ) ^ 2 := by
  have hmh_le : h ≤ m := by omega
  have hmh2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hadd2 : 2 ≤ (m + h) ^ 2 := by
    have : 2 ≤ m + h := by omega
    nlinarith
  have h1 := coherentCompletedOutgoing_mul_eq_chebyshevSqrtConvexPotential_sub hmh2
  have h2 := coherentCompletedOutgoing_mul_eq_chebyshevSqrtConvexPotential_sub hadd2
  have h3 := coherentCompletedOutgoing_mul_eq_chebyshevSqrtConvexPotential_sub hm2
  rw [sqrt_nat_sq_eq (m - h)] at h1
  rw [sqrt_nat_sq_eq (m + h)] at h2
  rw [sqrt_nat_sq_eq m] at h3
  have hc1 : (((m - h) ^ 2 : ℕ) : ℝ) * ((m - h : ℕ) : ℝ) / 3 =
      ((m : ℝ) - (h : ℝ)) ^ 3 / 3 := by
    push_cast [Nat.cast_sub hmh_le]
    ring
  have hc2 : (((m + h) ^ 2 : ℕ) : ℝ) * ((m + h : ℕ) : ℝ) / 3 =
      ((m : ℝ) + (h : ℝ)) ^ 3 / 3 := by
    push_cast
    ring
  have hc3 : ((m ^ 2 : ℕ) : ℝ) * (m : ℝ) / 3 = (m : ℝ) ^ 3 / 3 := by
    push_cast
    ring
  rw [hc1] at h1
  rw [hc2] at h2
  rw [hc3] at h3
  linarith [show ((m : ℝ) - (h : ℝ)) ^ 3 / 3 + ((m : ℝ) + (h : ℝ)) ^ 3 / 3 -
      2 * ((m : ℝ) ^ 3 / 3) = 2 * (m : ℝ) * (h : ℝ) ^ 2 by ring]

/-- **Zero-Remainder Three-Square Second-Difference Sandwich for
`unitRieszCoherentCompletedOutgoingCharge`:**
For all `m, h : ℕ` with `h + 2 ≤ m`:
`-2 * m * h^2 ≤ Δ²_{sq, h} (M * unitRieszCoherentCompletedOutgoingCharge M) (m) ≤ h * (ψ((m + h)^2) - ψ((m - h)^2)) - 2 * m * h^2`. -/
theorem coherentCompletedOutgoing_mul_square_second_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    -2 * (m : ℝ) * (h : ℝ) ^ 2 ≤
        (((m - h) ^ 2 : ℕ) : ℝ) * unitRieszCoherentCompletedOutgoingCharge ((m - h) ^ 2) +
          (((m + h) ^ 2 : ℕ) : ℝ) * unitRieszCoherentCompletedOutgoingCharge ((m + h) ^ 2) -
          2 * ((m ^ 2 : ℕ) : ℝ) * unitRieszCoherentCompletedOutgoingCharge (m ^ 2) ∧
      (((m - h) ^ 2 : ℕ) : ℝ) * unitRieszCoherentCompletedOutgoingCharge ((m - h) ^ 2) +
          (((m + h) ^ 2 : ℕ) : ℝ) * unitRieszCoherentCompletedOutgoingCharge ((m + h) ^ 2) -
          2 * ((m ^ 2 : ℕ) : ℝ) * unitRieszCoherentCompletedOutgoingCharge (m ^ 2) ≤
        (h : ℝ) * (Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) -
          Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ)) -
          2 * (m : ℝ) * (h : ℝ) ^ 2 := by
  rw [coherentCompletedOutgoing_mul_square_second_diff_eq hmh]
  have hphi := chebyshevSqrtConvexPotential_square_second_diff_sandwich hmh
  constructor <;> linarith [hphi.1, hphi.2]

/-! ## Section 2: Second-Cesàro and Midpoint Second-Cesàro Möbius–Divisor Dilation Channels and
Exact Degree-2 Integer Homothety -/

/-- **Unsigned Second-Cesàro Floor-Dilation Channel:**
`divisorUnsignedSecondCesaroDilationChannel M d = ∑ k ∈ Icc d (M - 1), (M - k) * primeFreeDivisorDefect (k / d)`. -/
def divisorUnsignedSecondCesaroDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1), ((M : ℝ) - (k : ℝ)) * primeFreeDivisorDefect (k / d)

/-- **Signed Second-Cesàro Möbius–Divisor Dilation Channel:**
`mobiusDivisorSecondCesaroDilationChannel M d = μ(d) * divisorUnsignedSecondCesaroDilationChannel M d`. -/
def mobiusDivisorSecondCesaroDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) * divisorUnsignedSecondCesaroDilationChannel M d

/-- **Unsigned Midpoint Second-Cesàro Floor-Dilation Eigenchannel:**
`divisorUnsignedMidpointSecondCesaroDilationChannel M d = ∑ k ∈ Icc d (M - 1), (M - k - 1 / 2) * primeFreeDivisorDefect (k / d)`.
Here `M - k - 1 / 2 = ∫_k^{k+1} (M - t) dt` is the exact cell integral of the degree-1 linear kernel
`M - t`, making this channel an exact degree-2 homothety eigenchannel. -/
def divisorUnsignedMidpointSecondCesaroDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1), ((M : ℝ) - (k : ℝ) - (1 / 2 : ℝ)) * primeFreeDivisorDefect (k / d)

/-- **Signed Midpoint Second-Cesàro Möbius–Divisor Dilation Eigenchannel:**
`mobiusDivisorMidpointSecondCesaroDilationChannel M d = μ(d) * divisorUnsignedMidpointSecondCesaroDilationChannel M d`. -/
def mobiusDivisorMidpointSecondCesaroDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    divisorUnsignedMidpointSecondCesaroDilationChannel M d

/-- Exact linear decomposition of `divisorUnsignedMidpointSecondCesaroDilationChannel`:
`D₂^{\mathrm{mid}}(M, d) = D₂(M, d) - (1 / 2) * D₁(M, d)`. -/
theorem divisorUnsignedMidpointSecondCesaroDilationChannel_eq_sub_half (M d : ℕ) :
    divisorUnsignedMidpointSecondCesaroDilationChannel M d =
      divisorUnsignedSecondCesaroDilationChannel M d -
        (1 / 2 : ℝ) * divisorUnsignedCesaroDilationChannel M d := by
  unfold divisorUnsignedMidpointSecondCesaroDilationChannel
    divisorUnsignedSecondCesaroDilationChannel divisorUnsignedCesaroDilationChannel
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact linear decomposition of `mobiusDivisorMidpointSecondCesaroDilationChannel`. -/
theorem mobiusDivisorMidpointSecondCesaroDilationChannel_eq_sub_half (M d : ℕ) :
    mobiusDivisorMidpointSecondCesaroDilationChannel M d =
      mobiusDivisorSecondCesaroDilationChannel M d -
        (1 / 2 : ℝ) * mobiusDivisorCesaroDilationChannel M d := by
  unfold mobiusDivisorMidpointSecondCesaroDilationChannel
    mobiusDivisorSecondCesaroDilationChannel mobiusDivisorCesaroDilationChannel
  rw [divisorUnsignedMidpointSecondCesaroDilationChannel_eq_sub_half]
  ring

/-- **One-Step Recurrence in `M` for `divisorUnsignedSecondCesaroDilationChannel`:**
For all `M, d : ℕ`,
`divisorUnsignedSecondCesaroDilationChannel (M + 1) d - divisorUnsignedSecondCesaroDilationChannel M d = divisorUnsignedCesaroDilationChannel (M + 1) d`. -/
theorem divisorUnsignedSecondCesaroDilationChannel_succ_sub (M d : ℕ) :
    divisorUnsignedSecondCesaroDilationChannel (M + 1) d -
        divisorUnsignedSecondCesaroDilationChannel M d =
      divisorUnsignedCesaroDilationChannel (M + 1) d := by
  unfold divisorUnsignedSecondCesaroDilationChannel
  rw [sum_Icc_mul_primeFreeDivisorDefect_eq_range (M + 1) d,
    sum_Icc_mul_primeFreeDivisorDefect_eq_range M d,
    divisorUnsignedCesaroDilationChannel_eq_range (M + 1) d,
    Finset.sum_range_succ, Finset.sum_range_succ (f := fun k => primeFreeDivisorDefect (k / d))]
  have hsum :
      (∑ k ∈ Finset.range M, (((M + 1 : ℕ) : ℝ) - (k : ℝ)) * primeFreeDivisorDefect (k / d)) -
        (∑ k ∈ Finset.range M, ((M : ℝ) - (k : ℝ)) * primeFreeDivisorDefect (k / d)) =
      ∑ k ∈ Finset.range M, primeFreeDivisorDefect (k / d) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  have hlast : (((M + 1 : ℕ) : ℝ) - (M : ℝ)) * primeFreeDivisorDefect (M / d) =
      primeFreeDivisorDefect (M / d) := by
    push_cast
    ring
  linarith

/-- **One-Step Recurrence in `M` for `mobiusDivisorSecondCesaroDilationChannel`:**
For all `M, d : ℕ`,
`mobiusDivisorSecondCesaroDilationChannel (M + 1) d - mobiusDivisorSecondCesaroDilationChannel M d = mobiusDivisorCesaroDilationChannel (M + 1) d`. -/
theorem mobiusDivisorSecondCesaroDilationChannel_succ_sub (M d : ℕ) :
    mobiusDivisorSecondCesaroDilationChannel (M + 1) d -
        mobiusDivisorSecondCesaroDilationChannel M d =
      mobiusDivisorCesaroDilationChannel (M + 1) d := by
  unfold mobiusDivisorSecondCesaroDilationChannel mobiusDivisorCesaroDilationChannel
  rw [← mul_sub, divisorUnsignedSecondCesaroDilationChannel_succ_sub]

/-- **One-Step Recurrence in `M` for `divisorUnsignedMidpointSecondCesaroDilationChannel`:**
For all `M, d : ℕ`, the forward first difference of the midpoint Second-Cesàro channel is the
consecutive average of the First-Cesàro channel at `M` and `M + 1`:
`D₂^{\mathrm{mid}}(M + 1, d) - D₂^{\mathrm{mid}}(M, d) = (D₁(M, d) + D₁(M + 1, d)) / 2`. -/
theorem divisorUnsignedMidpointSecondCesaroDilationChannel_succ_sub (M d : ℕ) :
    divisorUnsignedMidpointSecondCesaroDilationChannel (M + 1) d -
        divisorUnsignedMidpointSecondCesaroDilationChannel M d =
      (divisorUnsignedCesaroDilationChannel M d +
        divisorUnsignedCesaroDilationChannel (M + 1) d) / 2 := by
  rw [divisorUnsignedMidpointSecondCesaroDilationChannel_eq_sub_half (M + 1) d,
    divisorUnsignedMidpointSecondCesaroDilationChannel_eq_sub_half M d]
  have hstep := divisorUnsignedSecondCesaroDilationChannel_succ_sub M d
  linarith

/-- **Exact Degree-2 Integer Homothety of `divisorUnsignedMidpointSecondCesaroDilationChannel`:**
For all `r, M, d : ℕ` (including zero indices and terminal clipped blocks),
`divisorUnsignedMidpointSecondCesaroDilationChannel (r * M) (r * d) = r^2 * divisorUnsignedMidpointSecondCesaroDilationChannel M d`,
with **zero lower-order error**. -/
theorem divisorUnsignedMidpointSecondCesaroDilationChannel_mul (r M d : ℕ) :
    divisorUnsignedMidpointSecondCesaroDilationChannel (r * M) (r * d) =
      (r : ℝ) ^ 2 * divisorUnsignedMidpointSecondCesaroDilationChannel M d := by
  unfold divisorUnsignedMidpointSecondCesaroDilationChannel
  rw [sum_Icc_mul_primeFreeDivisorDefect_eq_range (r * M) (r * d),
    sum_Icc_mul_primeFreeDivisorDefect_eq_range M d]
  by_cases hr : r = 0
  · simp [hr]
  have hrpos : 0 < r := by omega
  rw [sum_range_mul_primeFreeDivisorDefect_block_eq hrpos]
  have htel (q : ℕ) :
      (∑ i ∈ Finset.range r, (((r * M : ℕ) : ℝ) - ((r * q + i : ℕ) : ℝ) - (1 / 2 : ℝ))) =
        (r : ℝ) ^ 2 * ((M : ℝ) - (q : ℝ) - (1 / 2 : ℝ)) := by
    let G : ℕ → ℝ := fun k => ((r * M : ℕ) : ℝ) * (k : ℝ) - (1 / 2 : ℝ) * (k : ℝ) ^ 2
    have hstep (i : ℕ) :
        (((r * M : ℕ) : ℝ) - ((r * q + i : ℕ) : ℝ) - (1 / 2 : ℝ)) =
          G (r * q + i + 1) - G (r * q + i) := by
      dsimp [G]
      push_cast
      ring
    simp_rw [hstep]
    rw [sum_range_sub_shift G (r * q) r]
    dsimp [G]
    push_cast
    ring
  simp_rw [htel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- **Exact Signed Degree-2 Homothety of `mobiusDivisorMidpointSecondCesaroDilationChannel` on
Coprime Supports:**
When `r.Coprime d`,
`mobiusDivisorMidpointSecondCesaroDilationChannel (r * M) (r * d) = r^2 * μ(r) * mobiusDivisorMidpointSecondCesaroDilationChannel M d`. -/
theorem mobiusDivisorMidpointSecondCesaroDilationChannel_mul_coprime
    {r M d : ℕ} (hc : r.Coprime d) :
    mobiusDivisorMidpointSecondCesaroDilationChannel (r * M) (r * d) =
      (r : ℝ) ^ 2 * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        mobiusDivisorMidpointSecondCesaroDilationChannel M d := by
  unfold mobiusDivisorMidpointSecondCesaroDilationChannel
  rw [divisorUnsignedMidpointSecondCesaroDilationChannel_mul,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc]
  push_cast
  ring

/-- **Exact Signed Degree-2 Homothety of `mobiusDivisorMidpointSecondCesaroDilationChannel` with
Shared-Prime Masking:** -/
theorem mobiusDivisorMidpointSecondCesaroDilationChannel_mul_masked (r M d : ℕ) :
    mobiusDivisorMidpointSecondCesaroDilationChannel (r * M) (r * d) =
      if r.Coprime d then
        (r : ℝ) ^ 2 * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
          mobiusDivisorMidpointSecondCesaroDilationChannel M d
      else 0 := by
  by_cases hc : r.Coprime d
  · rw [if_pos hc]
    exact mobiusDivisorMidpointSecondCesaroDilationChannel_mul_coprime hc
  · have hm : ArithmeticFunction.moebius (r * d) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (fun hsf => hc (Nat.coprime_of_squarefree_mul hsf))
    unfold mobiusDivisorMidpointSecondCesaroDilationChannel
    rw [if_neg hc, hm, Int.cast_zero, zero_mul]

/-- **Exact Shifted Degree-2 Integer Homothety of `divisorUnsignedSecondCesaroDilationChannel`:**
For all `r, M, d : ℕ`, the unshifted Second-Cesàro channel transforms under integer dilation by `r`
with an exact `-(r * (r - 1) / 2)` lower-order First-Cesàro shift:
`divisorUnsignedSecondCesaroDilationChannel (r * M) (r * d) = r^2 * divisorUnsignedSecondCesaroDilationChannel M d - (r * (r - 1) / 2) * divisorUnsignedCesaroDilationChannel M d`. -/
theorem divisorUnsignedSecondCesaroDilationChannel_mul (r M d : ℕ) :
    divisorUnsignedSecondCesaroDilationChannel (r * M) (r * d) =
      (r : ℝ) ^ 2 * divisorUnsignedSecondCesaroDilationChannel M d -
        ((r : ℝ) * ((r : ℝ) - 1) / 2) * divisorUnsignedCesaroDilationChannel M d := by
  have h1 := divisorUnsignedMidpointSecondCesaroDilationChannel_eq_sub_half (r * M) (r * d)
  have h2 := divisorUnsignedMidpointSecondCesaroDilationChannel_eq_sub_half M d
  have hmid := divisorUnsignedMidpointSecondCesaroDilationChannel_mul r M d
  have hces := divisorUnsignedCesaroDilationChannel_mul r M d
  rw [hmid, hces, h2] at h1
  linarith [show (r : ℝ) ^ 2 *
        (divisorUnsignedSecondCesaroDilationChannel M d -
          (1 / 2 : ℝ) * divisorUnsignedCesaroDilationChannel M d) +
      (1 / 2 : ℝ) * ((r : ℝ) * divisorUnsignedCesaroDilationChannel M d) =
    (r : ℝ) ^ 2 * divisorUnsignedSecondCesaroDilationChannel M d -
      ((r : ℝ) * ((r : ℝ) - 1) / 2) * divisorUnsignedCesaroDilationChannel M d by ring]

/-! ## Section 3: Exact Cofinal Sum Bridges for `chebyshevSecondCesaroSum` (`C₂(M)`), Midpoint
Second-Cesàro Sum, and Square-Grid Central Differences -/

/-- Exact relation between the linearly weighted prefix sum of `psiRemainder` on `Icc 1 (M - 1)`
and `chebyshevSecondCesaroSum M`: for all `M ≥ 2`,
`∑ k ∈ Icc 1 (M - 1), (M - k) * psiRemainder k = chebyshevSecondCesaroSum M - (M - 1)`. -/
theorem sum_Icc_sub_mul_psiRemainder_eq_chebyshevSecondCesaroSum_sub
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.Icc 1 (M - 1), ((M : ℝ) - (k : ℝ)) * psiRemainder k) =
      chebyshevSecondCesaroSum M - ((M : ℝ) - 1) := by
  rw [chebyshevSecondCesaroSum_eq_linear_weighted_psi_sub M]
  have hsplit : Finset.Icc 1 (M - 1) = insert 1 (Finset.Ico 2 M) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnotmem : (1 : ℕ) ∉ Finset.Ico 2 M := by
    simp only [Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_insert hnotmem, psiRemainder_one, Finset.sum_Ico_eq_sum_range]
  have hsum :
      (∑ x ∈ Finset.range (M - 2), ((M : ℝ) - ((2 + x : ℕ) : ℝ)) * psiRemainder (2 + x)) =
      ∑ k ∈ Finset.range (M - 2),
        ((M : ℝ) - ((k : ℝ) + 2)) * (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show (2 + k : ℕ) = k + 2 by omega, psiRemainder_add_two k]
    push_cast
    ring
  rw [hsum]
  push_cast
  ring

/-- Exact closed form for the linear triangular sum `∑ k ∈ Icc 1 (M - 1), (M - k)`:
for all `M ≥ 1`, `∑ k ∈ Icc 1 (M - 1), (M - k) = M * (M - 1) / 2`. -/
theorem sum_Icc_sub_eq {M : ℕ} (hM : 1 ≤ M) :
    (∑ k ∈ Finset.Icc 1 (M - 1), ((M : ℝ) - (k : ℝ))) =
      (M : ℝ) * ((M : ℝ) - 1) / 2 := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show M - 1 + 1 - 1 = M - 1 by omega]
  let G : ℕ → ℝ := fun k => ((M : ℝ) + (1 / 2 : ℝ)) * (k : ℝ) - (1 / 2 : ℝ) * (k : ℝ) ^ 2
  have hG :
      (∑ x ∈ Finset.range (M - 1), ((M : ℝ) - ((1 + x : ℕ) : ℝ))) =
      ∑ x ∈ Finset.range (M - 1), (G (1 + x + 1) - G (1 + x)) := by
    apply Finset.sum_congr rfl
    intro x _
    dsimp [G]
    push_cast
    ring
  rw [hG, sum_range_sub_shift G 1 (M - 1), show 1 + (M - 1) = M by omega]
  dsimp [G]
  norm_num
  ring

/-- Exact relation between the linearly weighted prefix sum of `psiDefect` on `Icc 1 (M - 1)`
and `chebyshevSecondCesaroSum M`: for all `M ≥ 2`,
`∑ k ∈ Icc 1 (M - 1), (M - k) * psiDefect k = chebyshevSecondCesaroSum M + γ * M * (M - 1) - (M - 1)`. -/
theorem sum_Icc_sub_mul_psiDefect_eq_chebyshevSecondCesaroSum_add
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.Icc 1 (M - 1), ((M : ℝ) - (k : ℝ)) * psiDefect k) =
      chebyshevSecondCesaroSum M +
        Real.eulerMascheroniConstant * (M : ℝ) * ((M : ℝ) - 1) - ((M : ℝ) - 1) := by
  have hrewrite :
      (∑ k ∈ Finset.Icc 1 (M - 1), ((M : ℝ) - (k : ℝ)) * psiDefect k) =
      ∑ k ∈ Finset.Icc 1 (M - 1),
        (((M : ℝ) - (k : ℝ)) * psiRemainder k +
          2 * Real.eulerMascheroniConstant * ((M : ℝ) - (k : ℝ))) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [psiDefect_eq_psiRemainder_add k]
    ring
  rw [hrewrite, Finset.sum_add_distrib,
    sum_Icc_sub_mul_psiRemainder_eq_chebyshevSecondCesaroSum_sub hM,
    ← Finset.mul_sum, sum_Icc_sub_eq (by omega : 1 ≤ M)]
  ring

/-- **Exact Second-Cesàro Möbius–Divisor Dilation Decomposition of `chebyshevSecondCesaroSum`:**
For every integer `M ≥ 2`,
`chebyshevSecondCesaroSum M = (∑ d ∈ Icc 1 (M - 1), mobiusDivisorSecondCesaroDilationChannel M d) - γ * M * (M - 1) + (M - 1)`. -/
theorem chebyshevSecondCesaroSum_eq_sum_mobiusDivisorSecondCesaroDilationChannel_sub
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSecondCesaroSum M =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorSecondCesaroDilationChannel M d) -
        Real.eulerMascheroniConstant * (M : ℝ) * ((M : ℝ) - 1) + ((M : ℝ) - 1) := by
  have h1 := sum_Icc_sub_mul_psiDefect_eq_chebyshevSecondCesaroSum_add hM
  have h2 := sum_Icc_psiDefect_weighted_eq_sum_dilation M (fun k => (M : ℝ) - (k : ℝ))
  unfold mobiusDivisorSecondCesaroDilationChannel divisorUnsignedSecondCesaroDilationChannel
  linarith

/-- **Exact Midpoint Second-Cesàro Möbius–Divisor Dilation Decomposition:**
For every integer `M ≥ 2`, the cofinal sum of the degree-2 homothety eigenchannels
`mobiusDivisorMidpointSecondCesaroDilationChannel M d` equals `C₂(M) - (1 / 2) * C₁(M)` plus a
**pure-square** Euler–Mascheroni secular term `γ * (M - 1)^2`:
`chebyshevSecondCesaroSum M - (1 / 2) * chebyshevClassicalCesaroSum M = (∑ d ∈ Icc 1 (M - 1), mobiusDivisorMidpointSecondCesaroDilationChannel M d) - γ * (M - 1)^2 + (M - 3 / 2)`. -/
theorem chebyshevSecondCesaroSum_sub_half_cesaro_eq_sum_mobiusDivisorMidpointSecondCesaroDilationChannel_sub
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSecondCesaroSum M - (1 / 2 : ℝ) * chebyshevClassicalCesaroSum M =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorMidpointSecondCesaroDilationChannel M d) -
        Real.eulerMascheroniConstant * ((M : ℝ) - 1) ^ 2 + ((M : ℝ) - (3 / 2 : ℝ)) := by
  have hC2 := chebyshevSecondCesaroSum_eq_sum_mobiusDivisorSecondCesaroDilationChannel_sub hM
  have hC1 := chebyshevClassicalCesaroSum_eq_sum_mobiusDivisorCesaroDilationChannel_sub hM
  have hsum :
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorMidpointSecondCesaroDilationChannel M d) =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorSecondCesaroDilationChannel M d) -
        (1 / 2 : ℝ) * (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCesaroDilationChannel M d) := by
    simp_rw [mobiusDivisorMidpointSecondCesaroDilationChannel_eq_sub_half]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith [show Real.eulerMascheroniConstant * ((M : ℝ) - 1) ^ 2 =
    Real.eulerMascheroniConstant * (M : ℝ) * ((M : ℝ) - 1) -
      Real.eulerMascheroniConstant * ((M : ℝ) - 1) by ring]

/-- For `M ≥ 3`, `chebyshevSecondCesaroSum M - (1 / 2) * chebyshevClassicalCesaroSum M` is the
exact consecutive average `(chebyshevSecondCesaroSum (M - 1) + chebyshevSecondCesaroSum M) / 2`. -/
theorem chebyshevSecondCesaroSum_sub_half_cesaro_eq_avg
    {M : ℕ} (hM : 3 ≤ M) :
    chebyshevSecondCesaroSum M - (1 / 2 : ℝ) * chebyshevClassicalCesaroSum M =
      (chebyshevSecondCesaroSum (M - 1) + chebyshevSecondCesaroSum M) / 2 := by
  have hstep := chebyshevSecondCesaroSum_succ_sub (by omega : 2 ≤ M - 1)
  rw [show M - 1 + 1 = M by omega] at hstep
  linarith

/-- **Exact Square-Grid Central-Difference Identity for `mobiusDivisorSecondCesaroDilationChannel`:**
For all `m, h : ℕ` with `2 ≤ m - h`,
`(∑ d ∈ Icc 1 ((m + h)^2 - 1), D₂((m + h)^2, d)) - (∑ d ∈ Icc 1 ((m - h)^2 - 1), D₂((m - h)^2, d)) = (C₂((m + h)^2) - C₂((m - h)^2)) + 4 * γ * m * h * (2 * m^2 + 2 * h^2 - 1) - 4 * m * h`. -/
theorem sum_mobiusDivisorSecondCesaroDilationChannel_central_diff_sq_eq
    {m h : ℕ} (hmh : 2 ≤ m - h) :
    (∑ d ∈ Finset.Icc 1 ((m + h) ^ 2 - 1),
        mobiusDivisorSecondCesaroDilationChannel ((m + h) ^ 2) d) -
      (∑ d ∈ Finset.Icc 1 ((m - h) ^ 2 - 1),
        mobiusDivisorSecondCesaroDilationChannel ((m - h) ^ 2) d) =
      (chebyshevSecondCesaroSum ((m + h) ^ 2) - chebyshevSecondCesaroSum ((m - h) ^ 2)) +
        4 * Real.eulerMascheroniConstant * (m : ℝ) * (h : ℝ) *
          (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1) -
        4 * (m : ℝ) * (h : ℝ) := by
  have hmh_le : h ≤ m := by omega
  have hmh2 : 2 ≤ (m - h) ^ 2 := by nlinarith
  have hadd2 : 2 ≤ (m + h) ^ 2 := by
    have : 2 ≤ m + h := by omega
    nlinarith
  have h1 := chebyshevSecondCesaroSum_eq_sum_mobiusDivisorSecondCesaroDilationChannel_sub hadd2
  have h2 := chebyshevSecondCesaroSum_eq_sum_mobiusDivisorSecondCesaroDilationChannel_sub hmh2
  have hc1 : (((m + h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) + (h : ℝ)) ^ 2 := by push_cast; ring
  have hc2 : (((m - h) ^ 2 : ℕ) : ℝ) = ((m : ℝ) - (h : ℝ)) ^ 2 := by
    push_cast [Nat.cast_sub hmh_le]; ring
  rw [hc1] at h1
  rw [hc2] at h2
  linarith [show Real.eulerMascheroniConstant * ((m : ℝ) + (h : ℝ)) ^ 2 *
        (((m : ℝ) + (h : ℝ)) ^ 2 - 1) -
      Real.eulerMascheroniConstant * ((m : ℝ) - (h : ℝ)) ^ 2 *
        (((m : ℝ) - (h : ℝ)) ^ 2 - 1) =
    4 * Real.eulerMascheroniConstant * (m : ℝ) * (h : ℝ) *
      (2 * (m : ℝ) ^ 2 + 2 * (h : ℝ) ^ 2 - 1) by ring]

/-! ## Section 4: Left, Right, Trapezoidal, and Cell-Integral Square-Root Riesz Dilation Channels,
Pure Degree-`3/2` Integer Homothety, and Exact Cubic Euler–Maclaurin Completion -/

/-- **Unsigned Right-Endpoint Square-Root Riesz Dilation Channel:**
`divisorUnsignedRightSqrtRieszDilationChannel M d = ∑ k ∈ Icc d (M - 1), (√M - √k) * primeFreeDivisorDefect (k / d)`.
This corresponds to the weight `√M - √k` of `chebyshevRightSqrtRieszAction M = R_√(M) + F_√(M)`. -/
def divisorUnsignedRightSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1),
    (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) * primeFreeDivisorDefect (k / d)

/-- **Signed Right-Endpoint Square-Root Riesz Möbius–Divisor Dilation Channel:** -/
def mobiusDivisorRightSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) * divisorUnsignedRightSqrtRieszDilationChannel M d

/-- **Unsigned Left-Endpoint Square-Root Riesz Dilation Channel:**
`divisorUnsignedSqrtRieszDilationChannel M d = ∑ k ∈ Icc d (M - 1), (√M - √(k + 1)) * primeFreeDivisorDefect (k / d)`.
This corresponds to the weight `√M - √(k + 1)` of `chebyshevSqrtRieszAction M = R_√(M)`. -/
def divisorUnsignedSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1),
    (Real.sqrt (M : ℝ) - Real.sqrt ((k + 1 : ℕ) : ℝ)) * primeFreeDivisorDefect (k / d)

/-- **Signed Left-Endpoint Square-Root Riesz Möbius–Divisor Dilation Channel:** -/
def mobiusDivisorSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) * divisorUnsignedSqrtRieszDilationChannel M d

/-- **Unsigned Trapezoidal Square-Root Riesz Dilation Channel:**
`divisorUnsignedTrapezoidalSqrtRieszDilationChannel M d = ∑ k ∈ Icc d (M - 1), (((√M - √(k + 1)) + (√M - √k)) / 2) * primeFreeDivisorDefect (k / d)`.
This corresponds to the trapezoidal weight of `chebyshevTrapezoidalSqrtRieszAction M`. -/
def divisorUnsignedTrapezoidalSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1),
    ((Real.sqrt (M : ℝ) - Real.sqrt ((k + 1 : ℕ) : ℝ)) +
      (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ))) / 2 *
      primeFreeDivisorDefect (k / d)

/-- **Signed Trapezoidal Square-Root Riesz Möbius–Divisor Dilation Channel:** -/
def mobiusDivisorTrapezoidalSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    divisorUnsignedTrapezoidalSqrtRieszDilationChannel M d

/-- **The Exact Cell-Integral Square-Root Riesz Weight:**
`sqrtRieszCellIntegralWeight M k = ∫_k^{k+1} (√M - √t) dt = √M - (2 / 3) * ((k + 1) * √(k + 1) - k * √k)`. -/
def sqrtRieszCellIntegralWeight (M k : ℕ) : ℝ :=
  Real.sqrt (M : ℝ) -
    (2 / 3 : ℝ) *
      (((k + 1 : ℕ) : ℝ) * Real.sqrt ((k + 1 : ℕ) : ℝ) - (k : ℝ) * Real.sqrt (k : ℝ))

/-- **Unsigned Cell-Integral Square-Root Riesz Dilation Eigenchannel:**
`divisorUnsignedCellSqrtRieszDilationChannel M d = ∑ k ∈ Icc d (M - 1), sqrtRieszCellIntegralWeight M k * primeFreeDivisorDefect (k / d)`. -/
def divisorUnsignedCellSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1), sqrtRieszCellIntegralWeight M k * primeFreeDivisorDefect (k / d)

/-- **Signed Cell-Integral Square-Root Riesz Möbius–Divisor Dilation Eigenchannel:** -/
def mobiusDivisorCellSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) * divisorUnsignedCellSqrtRieszDilationChannel M d

/-- **Unsigned Cubic Square-Root Defect Dilation Channel:**
`divisorUnsignedCubicSqrtDefectDilationChannel M d = ∑ k ∈ Icc d (M - 1), (√(k + 1) - √k)^3 * primeFreeDivisorDefect (k / d)`. -/
def divisorUnsignedCubicSqrtDefectDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1),
    (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) ^ 3 * primeFreeDivisorDefect (k / d)

/-- **Signed Cubic Square-Root Defect Möbius–Divisor Dilation Channel:** -/
def mobiusDivisorCubicSqrtDefectDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) * divisorUnsignedCubicSqrtDefectDilationChannel M d

/-- Exact endpoint shift relation between `divisorUnsignedRightSqrtRieszDilationChannel`,
`divisorUnsignedSqrtRieszDilationChannel`, and `divisorUnsignedDilationChannel`:
`R_{\mathrm{R}}(M, d) = R_{\mathrm{L}}(M, d) + divisorUnsignedDilationChannel M d`. -/
theorem divisorUnsignedRightSqrtRieszDilationChannel_eq_add (M d : ℕ) :
    divisorUnsignedRightSqrtRieszDilationChannel M d =
      divisorUnsignedSqrtRieszDilationChannel M d + divisorUnsignedDilationChannel M d := by
  unfold divisorUnsignedRightSqrtRieszDilationChannel
    divisorUnsignedSqrtRieszDilationChannel divisorUnsignedDilationChannel
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact endpoint shift relation for the signed Right and Left Riesz dilation channels. -/
theorem mobiusDivisorRightSqrtRieszDilationChannel_eq_add (M d : ℕ) :
    mobiusDivisorRightSqrtRieszDilationChannel M d =
      mobiusDivisorSqrtRieszDilationChannel M d + mobiusDivisorDilationChannel M d := by
  unfold mobiusDivisorRightSqrtRieszDilationChannel mobiusDivisorSqrtRieszDilationChannel
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    divisorUnsignedRightSqrtRieszDilationChannel_eq_add]
  ring

/-- Exact decomposition of `divisorUnsignedTrapezoidalSqrtRieszDilationChannel`:
`R_{\mathrm{trap}}(M, d) = R_{\mathrm{L}}(M, d) + (1 / 2) * divisorUnsignedDilationChannel M d`. -/
theorem divisorUnsignedTrapezoidalSqrtRieszDilationChannel_eq_add_half (M d : ℕ) :
    divisorUnsignedTrapezoidalSqrtRieszDilationChannel M d =
      divisorUnsignedSqrtRieszDilationChannel M d +
        (1 / 2 : ℝ) * divisorUnsignedDilationChannel M d := by
  unfold divisorUnsignedTrapezoidalSqrtRieszDilationChannel
    divisorUnsignedSqrtRieszDilationChannel divisorUnsignedDilationChannel
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact decomposition of `mobiusDivisorTrapezoidalSqrtRieszDilationChannel`. -/
theorem mobiusDivisorTrapezoidalSqrtRieszDilationChannel_eq_add_half (M d : ℕ) :
    mobiusDivisorTrapezoidalSqrtRieszDilationChannel M d =
      mobiusDivisorSqrtRieszDilationChannel M d +
        (1 / 2 : ℝ) * mobiusDivisorDilationChannel M d := by
  unfold mobiusDivisorTrapezoidalSqrtRieszDilationChannel mobiusDivisorSqrtRieszDilationChannel
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    divisorUnsignedTrapezoidalSqrtRieszDilationChannel_eq_add_half]
  ring

/-- **One-Step Recurrence in `M` for `divisorUnsignedSqrtRieszDilationChannel`:**
For all `M, d : ℕ`,
`divisorUnsignedSqrtRieszDilationChannel (M + 1) d - divisorUnsignedSqrtRieszDilationChannel M d = (√(M + 1) - √M) * divisorUnsignedCesaroDilationChannel M d`. -/
theorem divisorUnsignedSqrtRieszDilationChannel_succ_sub (M d : ℕ) :
    divisorUnsignedSqrtRieszDilationChannel (M + 1) d -
        divisorUnsignedSqrtRieszDilationChannel M d =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) *
        divisorUnsignedCesaroDilationChannel M d := by
  unfold divisorUnsignedSqrtRieszDilationChannel
  rw [sum_Icc_mul_primeFreeDivisorDefect_eq_range (M + 1) d,
    sum_Icc_mul_primeFreeDivisorDefect_eq_range M d,
    divisorUnsignedCesaroDilationChannel_eq_range M d,
    Finset.sum_range_succ, sub_self, zero_mul, add_zero,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **Channel-Wise Conjugate Inversion Formula:**
For all `M, d : ℕ`, `divisorUnsignedCesaroDilationChannel M d` is recovered with zero error from a
single forward step of `divisorUnsignedSqrtRieszDilationChannel`:
`divisorUnsignedCesaroDilationChannel M d = (√(M + 1) + √M) * (divisorUnsignedSqrtRieszDilationChannel (M + 1) d - divisorUnsignedSqrtRieszDilationChannel M d)`. -/
theorem divisorUnsignedCesaroDilationChannel_eq_sqrt_add_mul_sqrtRieszDilationChannel_diff
    (M d : ℕ) :
    divisorUnsignedCesaroDilationChannel M d =
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt (M : ℝ)) *
        (divisorUnsignedSqrtRieszDilationChannel (M + 1) d -
          divisorUnsignedSqrtRieszDilationChannel M d) := by
  rw [divisorUnsignedSqrtRieszDilationChannel_succ_sub, ← mul_assoc]
  have hconj :
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt (M : ℝ)) *
        (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ)) = 1 := by
    have hsq1 : Real.sqrt ((M + 1 : ℕ) : ℝ) * Real.sqrt ((M + 1 : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hsq0 : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    calc
      (Real.sqrt ((M + 1 : ℕ) : ℝ) + Real.sqrt (M : ℝ)) *
          (Real.sqrt ((M + 1 : ℕ) : ℝ) - Real.sqrt (M : ℝ))
        = Real.sqrt ((M + 1 : ℕ) : ℝ) * Real.sqrt ((M + 1 : ℕ) : ℝ) -
            Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) := by ring
      _ = ((M + 1 : ℕ) : ℝ) - (M : ℝ) := by rw [hsq1, hsq0]
      _ = 1 := by push_cast; ring
  rw [hconj, one_mul]

/-- **Exact Degree-`3/2` Integer Homothety of `divisorUnsignedCellSqrtRieszDilationChannel`:**
For all `r, M, d : ℕ` (including zero indices and terminal clipped blocks),
`divisorUnsignedCellSqrtRieszDilationChannel (r * M) (r * d) = r * √r * divisorUnsignedCellSqrtRieszDilationChannel M d`,
with **zero lower-order error**. -/
theorem divisorUnsignedCellSqrtRieszDilationChannel_mul (r M d : ℕ) :
    divisorUnsignedCellSqrtRieszDilationChannel (r * M) (r * d) =
      (r : ℝ) * Real.sqrt (r : ℝ) * divisorUnsignedCellSqrtRieszDilationChannel M d := by
  unfold divisorUnsignedCellSqrtRieszDilationChannel
  rw [sum_Icc_mul_primeFreeDivisorDefect_eq_range (r * M) (r * d),
    sum_Icc_mul_primeFreeDivisorDefect_eq_range M d]
  by_cases hr : r = 0
  · simp [hr]
  have hrpos : 0 < r := by omega
  rw [sum_range_mul_primeFreeDivisorDefect_block_eq hrpos]
  have htel (q : ℕ) :
      (∑ i ∈ Finset.range r, sqrtRieszCellIntegralWeight (r * M) (r * q + i)) =
        (r : ℝ) * Real.sqrt (r : ℝ) * sqrtRieszCellIntegralWeight M q := by
    let G : ℕ → ℝ := fun k =>
      Real.sqrt ((r * M : ℕ) : ℝ) * (k : ℝ) -
        (2 / 3 : ℝ) * (k : ℝ) * Real.sqrt (k : ℝ)
    have hstep (i : ℕ) :
        sqrtRieszCellIntegralWeight (r * M) (r * q + i) =
          G (r * q + i + 1) - G (r * q + i) := by
      unfold sqrtRieszCellIntegralWeight
      dsimp [G]
      push_cast
      ring
    simp_rw [hstep]
    rw [sum_range_sub_shift G (r * q) r]
    dsimp [G]
    unfold sqrtRieszCellIntegralWeight
    rw [show r * q + r = r * (q + 1) by ring]
    push_cast
    simp only [Real.sqrt_mul (Nat.cast_nonneg (α := ℝ) r)]
    ring
  simp_rw [htel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- **Exact Signed Degree-`3/2` Homothety of `mobiusDivisorCellSqrtRieszDilationChannel` on
Coprime Supports:**
When `r.Coprime d`,
`mobiusDivisorCellSqrtRieszDilationChannel (r * M) (r * d) = r * √r * μ(r) * mobiusDivisorCellSqrtRieszDilationChannel M d`. -/
theorem mobiusDivisorCellSqrtRieszDilationChannel_mul_coprime
    {r M d : ℕ} (hc : r.Coprime d) :
    mobiusDivisorCellSqrtRieszDilationChannel (r * M) (r * d) =
      (r : ℝ) * Real.sqrt (r : ℝ) * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        mobiusDivisorCellSqrtRieszDilationChannel M d := by
  unfold mobiusDivisorCellSqrtRieszDilationChannel
  rw [divisorUnsignedCellSqrtRieszDilationChannel_mul,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc]
  push_cast
  ring

/-- **Exact Signed Degree-`3/2` Homothety of `mobiusDivisorCellSqrtRieszDilationChannel` with
Shared-Prime Masking:** -/
theorem mobiusDivisorCellSqrtRieszDilationChannel_mul_masked (r M d : ℕ) :
    mobiusDivisorCellSqrtRieszDilationChannel (r * M) (r * d) =
      if r.Coprime d then
        (r : ℝ) * Real.sqrt (r : ℝ) * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
          mobiusDivisorCellSqrtRieszDilationChannel M d
      else 0 := by
  by_cases hc : r.Coprime d
  · rw [if_pos hc]
    exact mobiusDivisorCellSqrtRieszDilationChannel_mul_coprime hc
  · have hm : ArithmeticFunction.moebius (r * d) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (fun hsf => hc (Nat.coprime_of_squarefree_mul hsf))
    unfold mobiusDivisorCellSqrtRieszDilationChannel
    rw [if_neg hc, hm, Int.cast_zero, zero_mul]

/-- **Exact Cubic Euler–Maclaurin Identity for `sqrtRieszCellIntegralWeight`:**
For all `M, k : ℕ`, the cell-integral Riesz weight differs from the trapezoidal Riesz weight by
`-(1 / 6) * (√(k + 1) - √k)^3`:
`sqrtRieszCellIntegralWeight M k = ((√M - √(k + 1)) + (√M - √k)) / 2 - (1 / 6) * (√(k + 1) - √k)^3`. -/
theorem sqrtRieszCellIntegralWeight_eq_trapezoidal_sub_cube (M k : ℕ) :
    sqrtRieszCellIntegralWeight M k =
      ((Real.sqrt (M : ℝ) - Real.sqrt ((k + 1 : ℕ) : ℝ)) +
        (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ))) / 2 -
        (1 / 6 : ℝ) * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) ^ 3 := by
  unfold sqrtRieszCellIntegralWeight
  set a : ℝ := Real.sqrt (k : ℝ)
  set b : ℝ := Real.sqrt ((k + 1 : ℕ) : ℝ)
  have ha2 : a ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = ((k + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hdiff : b ^ 2 - a ^ 2 = 1 := by
    rw [hb2, ha2]
    push_cast
    ring
  have ha3 : ((k : ℝ) * a) = a ^ 3 := by
    calc
      (k : ℝ) * a = a ^ 2 * a := by rw [ha2]
      _ = a ^ 3 := by ring
  have hb3 : (((k + 1 : ℕ) : ℝ) * b) = b ^ 3 := by
    calc
      ((k + 1 : ℕ) : ℝ) * b = b ^ 2 * b := by rw [hb2]
      _ = b ^ 3 := by ring
  have hid := add_mul_sq_sub_eq_four_thirds_cubic_sub_sub_cubic_defect a b
  rw [hdiff, mul_one] at hid
  rw [hb3, ha3]
  linarith

/-- **Exact Cubic Euler–Maclaurin Completion of `divisorUnsignedTrapezoidalSqrtRieszDilationChannel`:**
For all `M, d : ℕ`,
`divisorUnsignedCellSqrtRieszDilationChannel M d = divisorUnsignedTrapezoidalSqrtRieszDilationChannel M d - (1 / 6) * divisorUnsignedCubicSqrtDefectDilationChannel M d`. -/
theorem divisorUnsignedCellSqrtRieszDilationChannel_eq_trapezoidal_sub_cubic (M d : ℕ) :
    divisorUnsignedCellSqrtRieszDilationChannel M d =
      divisorUnsignedTrapezoidalSqrtRieszDilationChannel M d -
        (1 / 6 : ℝ) * divisorUnsignedCubicSqrtDefectDilationChannel M d := by
  unfold divisorUnsignedCellSqrtRieszDilationChannel
    divisorUnsignedTrapezoidalSqrtRieszDilationChannel
    divisorUnsignedCubicSqrtDefectDilationChannel
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [sqrtRieszCellIntegralWeight_eq_trapezoidal_sub_cube]
  ring

/-- **Exact Cubic Euler–Maclaurin Completion of `mobiusDivisorTrapezoidalSqrtRieszDilationChannel`:** -/
theorem mobiusDivisorCellSqrtRieszDilationChannel_eq_trapezoidal_sub_cubic (M d : ℕ) :
    mobiusDivisorCellSqrtRieszDilationChannel M d =
      mobiusDivisorTrapezoidalSqrtRieszDilationChannel M d -
        (1 / 6 : ℝ) * mobiusDivisorCubicSqrtDefectDilationChannel M d := by
  unfold mobiusDivisorCellSqrtRieszDilationChannel
    mobiusDivisorTrapezoidalSqrtRieszDilationChannel
    mobiusDivisorCubicSqrtDefectDilationChannel
  rw [divisorUnsignedCellSqrtRieszDilationChannel_eq_trapezoidal_sub_cubic]
  ring

/-! ## Section 5: Exact Cofinal Sum Bridges for `chebyshevRightSqrtRieszAction`,
`chebyshevSqrtRieszAction`, `chebyshevTrapezoidalSqrtRieszAction`, and
`mobiusDivisorCellSqrtRieszDilationChannel` -/

/-- Exact relation between the `(√M - √k)`-weighted prefix sum of `psiRemainder` on `Icc 1 (M - 1)`
and `chebyshevRightSqrtRieszAction M`: for all `M ≥ 2`,
`∑ k ∈ Icc 1 (M - 1), (√M - √k) * psiRemainder k = chebyshevRightSqrtRieszAction M - (√M - 1)`. -/
theorem sum_Icc_sqrt_sub_mul_psiRemainder_eq_chebyshevRightSqrtRieszAction_sub
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.Icc 1 (M - 1), (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) * psiRemainder k) =
      chebyshevRightSqrtRieszAction M - (Real.sqrt (M : ℝ) - 1) := by
  unfold chebyshevRightSqrtRieszAction
  rw [chebyshevSqrtRieszAction_add_sqrtIncrementAction_eq M]
  have hsplit : Finset.Icc 1 (M - 1) = insert 1 (Finset.Ico 2 M) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnotmem : (1 : ℕ) ∉ Finset.Ico 2 M := by
    simp only [Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_insert hnotmem, psiRemainder_one, Finset.sum_Ico_eq_sum_range]
  have hsum :
      (∑ x ∈ Finset.range (M - 2),
        (Real.sqrt (M : ℝ) - Real.sqrt ((2 + x : ℕ) : ℝ)) * psiRemainder (2 + x)) =
      ∑ k ∈ Finset.range (M - 2),
        (Real.sqrt (M : ℝ) - Real.sqrt ((k : ℝ) + 2)) *
          (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show (2 + k : ℕ) = k + 2 by omega, psiRemainder_add_two k]
    push_cast
    ring
  rw [hsum]
  norm_num
  ring

/-- **Exact Right-Endpoint Riesz Möbius–Divisor Dilation Decomposition of
`chebyshevRightSqrtRieszAction`:**
For every integer `M ≥ 2`,
`chebyshevRightSqrtRieszAction M = (∑ d ∈ Icc 1 (M - 1), mobiusDivisorRightSqrtRieszDilationChannel M d) - 2 * γ * (secularSqrtIncrementAction M + (√2 - 1)) + (√M - 1)`. -/
theorem chebyshevRightSqrtRieszAction_eq_sum_mobiusDivisorRightSqrtRieszDilationChannel_sub
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevRightSqrtRieszAction M =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorRightSqrtRieszDilationChannel M d) -
        2 * Real.eulerMascheroniConstant * (secularSqrtIncrementAction M + (Real.sqrt 2 - 1)) +
        (Real.sqrt (M : ℝ) - 1) := by
  have h2 := sum_Icc_psiDefect_weighted_eq_sum_dilation M
    (fun k => Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ))
  have hrewrite :
      (∑ k ∈ Finset.Icc 1 (M - 1),
        (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) * psiDefect k) =
      (∑ k ∈ Finset.Icc 1 (M - 1),
        (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) * psiRemainder k) +
      2 * Real.eulerMascheroniConstant *
        (∑ k ∈ Finset.Icc 1 (M - 1), (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [psiDefect_eq_psiRemainder_add k]
    ring
  rw [hrewrite, sum_Icc_sqrt_sub_mul_psiRemainder_eq_chebyshevRightSqrtRieszAction_sub hM,
    sum_Icc_sqrt_sub_eq_secularSqrtIncrementAction_add hM] at h2
  unfold mobiusDivisorRightSqrtRieszDilationChannel divisorUnsignedRightSqrtRieszDilationChannel
  linarith

/-- **Exact Left-Endpoint Riesz Möbius–Divisor Dilation Decomposition of
`chebyshevSqrtRieszAction`:**
For every integer `M ≥ 2`,
`chebyshevSqrtRieszAction M = (∑ d ∈ Icc 1 (M - 1), mobiusDivisorSqrtRieszDilationChannel M d) - 2 * γ * (secularSqrtIncrementAction M - (√M - √2)) + (√M - √2)`. -/
theorem chebyshevSqrtRieszAction_eq_sum_mobiusDivisorSqrtRieszDilationChannel_sub
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSqrtRieszAction M =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorSqrtRieszDilationChannel M d) -
        2 * Real.eulerMascheroniConstant *
          (secularSqrtIncrementAction M - (Real.sqrt (M : ℝ) - Real.sqrt 2)) +
        (Real.sqrt (M : ℝ) - Real.sqrt 2) := by
  have hR := chebyshevRightSqrtRieszAction_eq_sum_mobiusDivisorRightSqrtRieszDilationChannel_sub hM
  have hF := sum_mobiusDivisorDilationChannel_eq_chebyshevSqrtIncrementAction_add hM
  have hsplit :
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorRightSqrtRieszDilationChannel M d) =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorSqrtRieszDilationChannel M d) +
        (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorDilationChannel M d) := by
    simp_rw [mobiusDivisorRightSqrtRieszDilationChannel_eq_add]
    rw [Finset.sum_add_distrib]
  unfold chebyshevRightSqrtRieszAction at hR
  linarith

/-- **Exact Trapezoidal Riesz Möbius–Divisor Dilation Decomposition of
`chebyshevTrapezoidalSqrtRieszAction`:**
For every integer `M ≥ 2`,
`chebyshevTrapezoidalSqrtRieszAction M = (∑ d ∈ Icc 1 (M - 1), mobiusDivisorTrapezoidalSqrtRieszDilationChannel M d) - 2 * γ * (secularSqrtIncrementAction M - (1 / 2) * √M + √2 - 1 / 2) + (√M - (√2 + 1) / 2)`. -/
theorem chebyshevTrapezoidalSqrtRieszAction_eq_sum_mobiusDivisorTrapezoidalSqrtRieszDilationChannel_sub
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevTrapezoidalSqrtRieszAction M =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorTrapezoidalSqrtRieszDilationChannel M d) -
        2 * Real.eulerMascheroniConstant *
          (secularSqrtIncrementAction M - (1 / 2 : ℝ) * Real.sqrt (M : ℝ) +
            Real.sqrt 2 - (1 / 2 : ℝ)) +
        (Real.sqrt (M : ℝ) - (Real.sqrt 2 + 1) / 2) := by
  have hL := chebyshevSqrtRieszAction_eq_sum_mobiusDivisorSqrtRieszDilationChannel_sub hM
  have hF := sum_mobiusDivisorDilationChannel_eq_chebyshevSqrtIncrementAction_add hM
  have htrap :
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorTrapezoidalSqrtRieszDilationChannel M d) =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorSqrtRieszDilationChannel M d) +
        (1 / 2 : ℝ) * (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorDilationChannel M d) := by
    simp_rw [mobiusDivisorTrapezoidalSqrtRieszDilationChannel_eq_add_half]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold chebyshevTrapezoidalSqrtRieszAction
  linarith

/-- **Exact Closed-Form Telescoping Sum of `sqrtRieszCellIntegralWeight`:**
For every integer `M ≥ 1`,
`∑ k ∈ Icc 1 (M - 1), sqrtRieszCellIntegralWeight M k = (1 / 3) * M * √M - √M + 2 / 3`. -/
theorem sum_Icc_sqrtRieszCellIntegralWeight_eq {M : ℕ} (hM : 1 ≤ M) :
    (∑ k ∈ Finset.Icc 1 (M - 1), sqrtRieszCellIntegralWeight M k) =
      (1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) - Real.sqrt (M : ℝ) + (2 / 3 : ℝ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show M - 1 + 1 - 1 = M - 1 by omega]
  let G : ℕ → ℝ := fun k =>
    Real.sqrt (M : ℝ) * (k : ℝ) -
      (2 / 3 : ℝ) * (k : ℝ) * Real.sqrt (k : ℝ)
  have hG :
      (∑ x ∈ Finset.range (M - 1), sqrtRieszCellIntegralWeight M (1 + x)) =
      ∑ x ∈ Finset.range (M - 1), (G (1 + x + 1) - G (1 + x)) := by
    apply Finset.sum_congr rfl
    intro x _
    unfold sqrtRieszCellIntegralWeight
    dsimp [G]
    push_cast
    ring
  rw [hG, sum_range_sub_shift G 1 (M - 1), show 1 + (M - 1) = M by omega]
  dsimp [G]
  norm_num
  ring

/-- **Exact Cofinal Sum Identity for `mobiusDivisorCellSqrtRieszDilationChannel`:**
For every integer `M ≥ 1`,
`∑ d ∈ Icc 1 (M - 1), mobiusDivisorCellSqrtRieszDilationChannel M d = (∑ k ∈ Icc 1 (M - 1), sqrtRieszCellIntegralWeight M k * psiRemainder k) + 2 * γ * ((1 / 3) * M * √M - √M + 2 / 3)`. -/
theorem sum_mobiusDivisorCellSqrtRieszDilationChannel_eq_psiRemainder_add_gamma
    {M : ℕ} (hM : 1 ≤ M) :
    (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCellSqrtRieszDilationChannel M d) =
      (∑ k ∈ Finset.Icc 1 (M - 1), sqrtRieszCellIntegralWeight M k * psiRemainder k) +
        2 * Real.eulerMascheroniConstant *
          ((1 / 3 : ℝ) * (M : ℝ) * Real.sqrt (M : ℝ) - Real.sqrt (M : ℝ) + (2 / 3 : ℝ)) := by
  have h1 := (sum_Icc_psiDefect_weighted_eq_sum_dilation M (sqrtRieszCellIntegralWeight M)).symm
  unfold mobiusDivisorCellSqrtRieszDilationChannel divisorUnsignedCellSqrtRieszDilationChannel
  rw [h1]
  have hrewrite :
      (∑ k ∈ Finset.Icc 1 (M - 1), sqrtRieszCellIntegralWeight M k * psiDefect k) =
      (∑ k ∈ Finset.Icc 1 (M - 1), sqrtRieszCellIntegralWeight M k * psiRemainder k) +
        2 * Real.eulerMascheroniConstant *
          (∑ k ∈ Finset.Icc 1 (M - 1), sqrtRieszCellIntegralWeight M k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [psiDefect_eq_psiRemainder_add k]
    ring
  rw [hrewrite, sum_Icc_sqrtRieszCellIntegralWeight_eq hM]

/-- **Exact Cofinal Bridge Between `mobiusDivisorCellSqrtRieszDilationChannel` and
`chebyshevTrapezoidalSqrtRieszAction`:**
For every integer `M ≥ 2`, the cofinal sum of the degree-`3/2` homothety eigenchannels
`mobiusDivisorCellSqrtRieszDilationChannel M d` equals `chebyshevTrapezoidalSqrtRieszAction M`
minus `(1 / 6)` of the cubic defect sum plus the exact Euler–Maclaurin secular shift. -/
theorem sum_mobiusDivisorCellSqrtRieszDilationChannel_eq_trapezoidalSqrtRieszAction_sub_cubic
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCellSqrtRieszDilationChannel M d) =
      chebyshevTrapezoidalSqrtRieszAction M -
        (1 / 6 : ℝ) *
          (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCubicSqrtDefectDilationChannel M d) +
        2 * Real.eulerMascheroniConstant *
          (secularSqrtIncrementAction M - (1 / 2 : ℝ) * Real.sqrt (M : ℝ) +
            Real.sqrt 2 - (1 / 2 : ℝ)) -
        (Real.sqrt (M : ℝ) - (Real.sqrt 2 + 1) / 2) := by
  have htrap :=
    chebyshevTrapezoidalSqrtRieszAction_eq_sum_mobiusDivisorTrapezoidalSqrtRieszDilationChannel_sub hM
  have hcell :
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCellSqrtRieszDilationChannel M d) =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorTrapezoidalSqrtRieszDilationChannel M d) -
        (1 / 6 : ℝ) *
          (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCubicSqrtDefectDilationChannel M d) := by
    simp_rw [mobiusDivisorCellSqrtRieszDilationChannel_eq_trapezoidal_sub_cubic]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

/-! ## Section 6: Quadratic Square-Root Riesz Dilation Channels (`(√M - √t)^2`), Exact Degree-1
and Degree-2 Homothety Eigenchannels, and Cofinal Bridges to `chebyshevSecondSqrtTrapezoidalAction` -/

/-- **Exact Pointwise Polarization Identity for `(√M - √k)^2`:**
For all `M, k : ℕ`,
`(√M - √k)^2 = 2 * √M * (√M - √k) - (M - k)`. -/
theorem sqrt_sub_sq_eq_two_mul_sqrt_sub_sub_linear (M k : ℕ) :
    (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) ^ 2 =
      2 * Real.sqrt (M : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) -
        ((M : ℝ) - (k : ℝ)) := by
  have hM : Real.sqrt (M : ℝ) ^ 2 = (M : ℝ) := Real.sq_sqrt (by positivity)
  have hk : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
  linarith [show (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) ^ 2 =
    2 * Real.sqrt (M : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) -
      (Real.sqrt (M : ℝ) ^ 2 - Real.sqrt (k : ℝ) ^ 2) by ring]

/-- **Exact Cell-Difference Identity for `(√M - √k)^2 - (√M - √(k + 1))^2`:**
For all `M, k : ℕ`,
`(√M - √k)^2 - (√M - √(k + 1))^2 = 2 * √M * (√(k + 1) - √k) - 1`. -/
theorem sqrt_sub_sq_cell_diff_eq (M k : ℕ) :
    (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) ^ 2 -
        (Real.sqrt (M : ℝ) - Real.sqrt ((k + 1 : ℕ) : ℝ)) ^ 2 =
      2 * Real.sqrt (M : ℝ) * (Real.sqrt ((k + 1 : ℕ) : ℝ) - Real.sqrt (k : ℝ)) - 1 := by
  rw [sqrt_sub_sq_eq_two_mul_sqrt_sub_sub_linear M k,
    sqrt_sub_sq_eq_two_mul_sqrt_sub_sub_linear M (k + 1)]
  push_cast
  ring

/-- **Unsigned Quadratic-Gap Abel Dilation Eigenchannel:**
`divisorUnsignedQuadraticSqrtAbelDilationChannel M d = ∑ k ∈ Icc d (M - 1), ((√M - √k)^2 - (√M - √(k + 1))^2) * primeFreeDivisorDefect (k / d)`.
This is the Möbius–divisor dilation channel associated with
`chebyshevSecondSqrtTrapezoidalAction M = 2 * √M * F_√(M) - C₁(M)` from Module 15. -/
def divisorUnsignedQuadraticSqrtAbelDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1),
    ((Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) ^ 2 -
      (Real.sqrt (M : ℝ) - Real.sqrt ((k + 1 : ℕ) : ℝ)) ^ 2) *
      primeFreeDivisorDefect (k / d)

/-- **Signed Quadratic-Gap Abel Möbius–Divisor Dilation Eigenchannel:** -/
def mobiusDivisorQuadraticSqrtAbelDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    divisorUnsignedQuadraticSqrtAbelDilationChannel M d

/-- Exact decomposition of `divisorUnsignedQuadraticSqrtAbelDilationChannel`:
`divisorUnsignedQuadraticSqrtAbelDilationChannel M d = 2 * √M * divisorUnsignedDilationChannel M d - divisorUnsignedCesaroDilationChannel M d`. -/
theorem divisorUnsignedQuadraticSqrtAbelDilationChannel_eq_sub (M d : ℕ) :
    divisorUnsignedQuadraticSqrtAbelDilationChannel M d =
      2 * Real.sqrt (M : ℝ) * divisorUnsignedDilationChannel M d -
        divisorUnsignedCesaroDilationChannel M d := by
  unfold divisorUnsignedQuadraticSqrtAbelDilationChannel
    divisorUnsignedDilationChannel divisorUnsignedCesaroDilationChannel
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [sqrt_sub_sq_cell_diff_eq]
  ring

/-- Exact decomposition of `mobiusDivisorQuadraticSqrtAbelDilationChannel`. -/
theorem mobiusDivisorQuadraticSqrtAbelDilationChannel_eq_sub (M d : ℕ) :
    mobiusDivisorQuadraticSqrtAbelDilationChannel M d =
      2 * Real.sqrt (M : ℝ) * mobiusDivisorDilationChannel M d -
        mobiusDivisorCesaroDilationChannel M d := by
  unfold mobiusDivisorQuadraticSqrtAbelDilationChannel mobiusDivisorCesaroDilationChannel
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    divisorUnsignedQuadraticSqrtAbelDilationChannel_eq_sub]
  ring

/-- **Exact Degree-1 Integer Homothety of `divisorUnsignedQuadraticSqrtAbelDilationChannel`:**
Because `2 * √(r * M) * divisorUnsignedDilationChannel (r * M) (r * d) = 2 * (√r * √M) * (√r * divisorUnsignedDilationChannel M d) = r * (2 * √M * divisorUnsignedDilationChannel M d)`,
both terms scale by `r`, making `divisorUnsignedQuadraticSqrtAbelDilationChannel` an exact degree-1
integer homothety eigenchannel:
`divisorUnsignedQuadraticSqrtAbelDilationChannel (r * M) (r * d) = r * divisorUnsignedQuadraticSqrtAbelDilationChannel M d`. -/
theorem divisorUnsignedQuadraticSqrtAbelDilationChannel_mul (r M d : ℕ) :
    divisorUnsignedQuadraticSqrtAbelDilationChannel (r * M) (r * d) =
      (r : ℝ) * divisorUnsignedQuadraticSqrtAbelDilationChannel M d := by
  rw [divisorUnsignedQuadraticSqrtAbelDilationChannel_eq_sub,
    divisorUnsignedQuadraticSqrtAbelDilationChannel_eq_sub,
    divisorUnsignedDilationChannel_mul, divisorUnsignedCesaroDilationChannel_mul]
  push_cast
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ r)]
  have hsq : Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ) = (r : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  linear_combination 2 * Real.sqrt (M : ℝ) * divisorUnsignedDilationChannel M d * hsq

/-- **Exact Cofinal Sum Bridge for `chebyshevSecondSqrtTrapezoidalAction`:**
For every integer `M ≥ 2`, the cofinal sum of `mobiusDivisorQuadraticSqrtAbelDilationChannel M d`
equals `chebyshevSecondSqrtTrapezoidalAction M = 2 * √M * F_√(M) - C₁(M)` plus a **pure-square**
Euler–Mascheroni secular term `2 * γ * (√M - 1)^2`:
`chebyshevSecondSqrtTrapezoidalAction M = (∑ d ∈ Icc 1 (M - 1), mobiusDivisorQuadraticSqrtAbelDilationChannel M d) - 2 * γ * (√M - 1)^2 + (2 * √M * (√2 - 1) - 1)`. -/
theorem chebyshevSecondSqrtTrapezoidalAction_eq_sum_mobiusDivisorQuadraticSqrtAbelDilationChannel_sub
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevSecondSqrtTrapezoidalAction M =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorQuadraticSqrtAbelDilationChannel M d) -
        2 * Real.eulerMascheroniConstant * (Real.sqrt (M : ℝ) - 1) ^ 2 +
        (2 * Real.sqrt (M : ℝ) * (Real.sqrt 2 - 1) - 1) := by
  have hvolt := chebyshevClassicalCesaroSum_add_secondSqrtTrapezoidalAction_eq M
  have hF := sum_mobiusDivisorDilationChannel_eq_chebyshevSqrtIncrementAction_add hM
  have hC1 := chebyshevClassicalCesaroSum_eq_sum_mobiusDivisorCesaroDilationChannel_sub hM
  have hsum :
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorQuadraticSqrtAbelDilationChannel M d) =
      2 * Real.sqrt (M : ℝ) * (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorDilationChannel M d) -
        (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCesaroDilationChannel M d) := by
    simp_rw [mobiusDivisorQuadraticSqrtAbelDilationChannel_eq_sub]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hsq : Real.sqrt (M : ℝ) ^ 2 = (M : ℝ) := Real.sq_sqrt (by positivity)
  rw [← hsq] at hC1
  rw [hF] at hsum
  linear_combination hvolt - hC1 - hsum

/-- **Unsigned Trapezoidal Quadratic Square-Root Riesz Dilation Channel:**
`divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel M d = ∑ k ∈ Icc d (M - 1), (((√M - √(k + 1))^2 + (√M - √k)^2) / 2) * primeFreeDivisorDefect (k / d)`. -/
def divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1),
    ((Real.sqrt (M : ℝ) - Real.sqrt ((k + 1 : ℕ) : ℝ)) ^ 2 +
      (Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) ^ 2) / 2 *
      primeFreeDivisorDefect (k / d)

/-- **Signed Trapezoidal Quadratic Square-Root Riesz Möbius–Divisor Dilation Channel:** -/
def mobiusDivisorTrapezoidalQuadraticSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel M d

/-- **The Exact Cell-Integral Quadratic Square-Root Riesz Weight:**
`quadraticSqrtRieszCellIntegralWeight M k = ∫_k^{k+1} (√M - √t)^2 dt = 2 * √M * sqrtRieszCellIntegralWeight M k - (M - k - 1 / 2)`. -/
def quadraticSqrtRieszCellIntegralWeight (M k : ℕ) : ℝ :=
  2 * Real.sqrt (M : ℝ) * sqrtRieszCellIntegralWeight M k -
    ((M : ℝ) - (k : ℝ) - (1 / 2 : ℝ))

/-- **Unsigned Cell-Integral Quadratic Square-Root Riesz Dilation Eigenchannel:**
`divisorUnsignedCellQuadraticSqrtRieszDilationChannel M d = ∑ k ∈ Icc d (M - 1), quadraticSqrtRieszCellIntegralWeight M k * primeFreeDivisorDefect (k / d)`. -/
def divisorUnsignedCellQuadraticSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1),
    quadraticSqrtRieszCellIntegralWeight M k * primeFreeDivisorDefect (k / d)

/-- **Signed Cell-Integral Quadratic Square-Root Riesz Möbius–Divisor Dilation Eigenchannel:** -/
def mobiusDivisorCellQuadraticSqrtRieszDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    divisorUnsignedCellQuadraticSqrtRieszDilationChannel M d

/-- Exact polarization identity for `divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel`:
`divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel M d = 2 * √M * divisorUnsignedTrapezoidalSqrtRieszDilationChannel M d - divisorUnsignedMidpointSecondCesaroDilationChannel M d`. -/
theorem divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel_eq_sub (M d : ℕ) :
    divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel M d =
      2 * Real.sqrt (M : ℝ) * divisorUnsignedTrapezoidalSqrtRieszDilationChannel M d -
        divisorUnsignedMidpointSecondCesaroDilationChannel M d := by
  unfold divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel
    divisorUnsignedTrapezoidalSqrtRieszDilationChannel
    divisorUnsignedMidpointSecondCesaroDilationChannel
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [sqrt_sub_sq_eq_two_mul_sqrt_sub_sub_linear M (k + 1),
    sqrt_sub_sq_eq_two_mul_sqrt_sub_sub_linear M k]
  push_cast
  ring

/-- Exact polarization identity for `divisorUnsignedCellQuadraticSqrtRieszDilationChannel`:
`divisorUnsignedCellQuadraticSqrtRieszDilationChannel M d = 2 * √M * divisorUnsignedCellSqrtRieszDilationChannel M d - divisorUnsignedMidpointSecondCesaroDilationChannel M d`. -/
theorem divisorUnsignedCellQuadraticSqrtRieszDilationChannel_eq_sub (M d : ℕ) :
    divisorUnsignedCellQuadraticSqrtRieszDilationChannel M d =
      2 * Real.sqrt (M : ℝ) * divisorUnsignedCellSqrtRieszDilationChannel M d -
        divisorUnsignedMidpointSecondCesaroDilationChannel M d := by
  unfold divisorUnsignedCellQuadraticSqrtRieszDilationChannel
    quadraticSqrtRieszCellIntegralWeight
    divisorUnsignedCellSqrtRieszDilationChannel
    divisorUnsignedMidpointSecondCesaroDilationChannel
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **Exact Degree-2 Integer Homothety of `divisorUnsignedCellQuadraticSqrtRieszDilationChannel`:**
For all `r, M, d : ℕ`,
`divisorUnsignedCellQuadraticSqrtRieszDilationChannel (r * M) (r * d) = r^2 * divisorUnsignedCellQuadraticSqrtRieszDilationChannel M d`,
with **zero lower-order error**. -/
theorem divisorUnsignedCellQuadraticSqrtRieszDilationChannel_mul (r M d : ℕ) :
    divisorUnsignedCellQuadraticSqrtRieszDilationChannel (r * M) (r * d) =
      (r : ℝ) ^ 2 * divisorUnsignedCellQuadraticSqrtRieszDilationChannel M d := by
  rw [divisorUnsignedCellQuadraticSqrtRieszDilationChannel_eq_sub,
    divisorUnsignedCellQuadraticSqrtRieszDilationChannel_eq_sub,
    divisorUnsignedCellSqrtRieszDilationChannel_mul,
    divisorUnsignedMidpointSecondCesaroDilationChannel_mul]
  push_cast
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ r)]
  have hsq : Real.sqrt (r : ℝ) * Real.sqrt (r : ℝ) = (r : ℝ) :=
    Real.mul_self_sqrt (by positivity)
  linear_combination
    2 * (r : ℝ) * Real.sqrt (M : ℝ) * divisorUnsignedCellSqrtRieszDilationChannel M d * hsq

/-- **Exact Cubic Euler–Maclaurin Completion of
`divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel`:**
Because the linear part `M - t` is integrated with zero error by the trapezoidal rule, the
midpoint Second-Cesàro parts cancel identically:
`divisorUnsignedCellQuadraticSqrtRieszDilationChannel M d = divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel M d - (1 / 3) * √M * divisorUnsignedCubicSqrtDefectDilationChannel M d`. -/
theorem divisorUnsignedCellQuadraticSqrtRieszDilationChannel_eq_trapezoidal_sub_cubic (M d : ℕ) :
    divisorUnsignedCellQuadraticSqrtRieszDilationChannel M d =
      divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel M d -
        (1 / 3 : ℝ) * Real.sqrt (M : ℝ) *
          divisorUnsignedCubicSqrtDefectDilationChannel M d := by
  rw [divisorUnsignedCellQuadraticSqrtRieszDilationChannel_eq_sub,
    divisorUnsignedTrapezoidalQuadraticSqrtRieszDilationChannel_eq_sub,
    divisorUnsignedCellSqrtRieszDilationChannel_eq_trapezoidal_sub_cubic]
  ring

end

end GaloisForLFunctions.RHTower
