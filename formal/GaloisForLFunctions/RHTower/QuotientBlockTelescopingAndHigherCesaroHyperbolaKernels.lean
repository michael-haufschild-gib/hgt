import GaloisForLFunctions.RHTower.HomothetyEigenchannelsAndSecondCesaroDivisorBridge

/-!
# Universal Quotient-Block Telescoping, Collapsed Parabolic & Riesz Möbius Kernels, and Zero-Loss Higher-Cesàro Hyperbola Bounds

This module advances the unconditional RHTower hierarchy beyond
`HomothetyEigenchannelsAndSecondCesaroDivisorBridge.lean` (Module 32) by establishing a
**Universal Quotient-Block Telescoping Theorem** for all Möbius–divisor dilation channels whose cell
weights are forward differences `G(k + 1) - G(k)`, deriving the closed-form complete-block and
terminal-band evaluations for the **Midpoint Second-Cesàro**, **Unshifted Second-Cesàro**,
**Cell-Integral Square-Root Riesz**, and **Quadratic-Gap Abel** channels, and proving
**zero-centered-hyperbola-loss upper bounds** for the unit and dilated higher-Cesàro and Riesz
channels:

## Mathematical Overview

1. **Section 1 (Universal Quotient-Block Telescoping and Hyperbola-Transposed Collapsed Möbius
   Kernels):**
   - For every `d ≥ 1` and every quotient index `1 ≤ q ≤ (M - 1) / d`, the quotient fiber
     `S = (Icc d (M - 1)).filter (fun k => k / d = q)` is the half-open integer interval
     `Ico (q * d) (q * d + divisorDilationTriangularLength M d q) = Ico (q * d) (min M ((q + 1) * d))`
     (`filter_Icc_div_eq_Ico_triangularLength` and `filter_Icc_div_eq_Ico_min`).
   - Consequently, for **any** primitive `G : ℕ → ℝ`, the sum of
     `(G (k + 1) - G k) * primeFreeDivisorDefect (k / d)` over `k ∈ Icc d (M - 1)` telescopes on
     every quotient block in closed form
     (`sum_Icc_sub_primitive_mul_primeFreeDivisorDefect_eq_quotientBlocks`):
     `∑ k ∈ Icc d (M - 1), (G (k + 1) - G k) * primeFreeDivisorDefect (k / d) = ∑ q ∈ Icc 1 ((M - 1) / d), (G (q * d + divisorDilationTriangularLength M d q) - G (q * d)) * primeFreeDivisorDefect q`.
   - Transposing the hyperbola `1 ≤ d * q ≤ M - 1` yields the universal collapsed Möbius-kernel
     identity (`sum_mobius_sub_primitive_dilation_eq_divisorDefect_kernel`).

2. **Section 2 (Midpoint and Unshifted Second-Cesàro Quotient-Block Weights, Parabolic Terminal
   Evaluations, and Collapsed Parabolic Möbius Kernels):**
   - We define `midpointSecondCesaroBlockWeight M d q` and `secondCesaroBlockWeight M d q`, together
     with the collapsed Möbius kernels `mobiusClippedMidpointSecondCesaroKernel M q` and
     `mobiusClippedSecondCesaroKernel M q`.
   - On complete blocks `(q + 1) * d ≤ M`, `midpointSecondCesaroBlockWeight M d q = d * (M - q * d - d / 2)`,
     while on the terminal band `q * d ≤ M ≤ (q + 1) * d`, `midpointSecondCesaroBlockWeight M d q`
     collapses to the **pure half-square** `((M : ℝ) - (q : ℝ) * (d : ℝ))^2 / 2 ≥ 0`
     (`midpointSecondCesaroBlockWeight_eq_terminal`), and `secondCesaroBlockWeight M d q` collapses
     to the triangular number `(M - q * d) * (M - q * d + 1) / 2` (`secondCesaroBlockWeight_eq_terminal`).
   - We prove the exact step recurrence in `M`:
     `mobiusClippedSecondCesaroKernel (M + 1) q - mobiusClippedSecondCesaroKernel M q = mobiusClippedCesaroKernel (M + 1) q`
     (`mobiusClippedSecondCesaroKernel_succ_sub`), showing that the Second-Cesàro collapsed Möbius
     kernel is the exact prefix sum of `mobiusClippedCesaroKernel j q` over `j ∈ Icc 1 M`
     (`mobiusClippedSecondCesaroKernel_eq_sum_cesaroKernel`).

3. **Section 3 (Cell-Integral Square-Root Riesz and Quadratic-Gap Abel Quotient-Block
   Factorizations, Cubic-Square Terminal Factorization, and Collapsed Riesz Möbius Kernels):**
   - We define `cellSqrtRieszBlockWeight M d q`, `mobiusClippedCellSqrtRieszKernel M q`,
     `quadraticSqrtAbelBlockWeight M d q`, and `mobiusClippedQuadraticSqrtAbelKernel M q`.
   - We prove their quotient-block factorizations, collapsed Möbius-kernel identities, complete-block
     evaluations, and terminal-band factorizations: on `q * d ≤ M ≤ (q + 1) * d`,
     `cellSqrtRieszBlockWeight M d q = (1 / 3) * (√M - √(q * d))^2 * (√M + 2 * √(q * d)) ≥ 0`
     (`cellSqrtRieszBlockWeight_eq_terminal_factored`), vanishing to second order at `q * d = M`,
     while `quadraticSqrtAbelBlockWeight M d q = (√M - √(q * d))^2 ≥ 0`
     (`quadraticSqrtAbelBlockWeight_eq_terminal`).

4. **Section 4 (Channel-Wise Cesàro Prefix-Sum Representations and Zero-Centered-Hyperbola-Loss
   Upper Bounds for Second-Cesàro, Midpoint Second-Cesàro, and Left Square-Root Riesz Channels):**
   - We prove `divisorUnsignedSecondCesaroDilationChannel_eq_sum_cesaro`
     (`D₂(M, d) = ∑ j ∈ Icc 1 M, D₁(j, d)`),
     `divisorUnsignedMidpointSecondCesaroDilationChannel_eq_avg`
     (`D₂^{\mathrm{mid}}(M, d) = (D₂(M - 1, d) + D₂(M, d)) / 2` for `M ≥ 1`), and
     `divisorUnsignedSqrtRieszDilationChannel_eq_sum_cesaro`
     (`R_{\mathrm{L}}(M, d) = ∑ j ∈ range M, (√(j + 1) - √j) * D₁(j, d)`).
   - Because every weight on `D₁(j, 1)` is non-negative and `∑_{k=1}^{j-1} centeredDivisorHyperbola k ≤ 0`
     unconditionally (`sum_centeredDivisorHyperbola_bounds`), the centered divisor hyperbola
     contributes **non-positively** to `D₂(M, 1)`, `D₂^{\mathrm{mid}}(M, 1)`, and `R_{\mathrm{L}}(M, 1)`,
     yielding unconditional zero-loss upper bounds (`divisorUnsignedSecondCesaroDilationChannel_one_le`,
     `divisorUnsignedMidpointSecondCesaroDilationChannel_one_le`,
     `divisorUnsignedMidpointSecondCesaroDilationChannel_mul_one_le`, and
     `divisorUnsignedSqrtRieszDilationChannel_one_le`).
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev ArithmeticFunction
open Real Finset _root_.RHTower

noncomputable section

/-! ## Section 1: Universal Quotient-Block Telescoping and Hyperbola-Transposed Collapsed Möbius
Kernels -/

/-- For every `M, d, q : ℕ` with `q * d ≤ M`, adding the clipped block length
`divisorDilationTriangularLength M d q = min (M - q * d) d` to the left endpoint `q * d` yields the
exact right endpoint `min M ((q + 1) * d)`. -/
theorem add_divisorDilationTriangularLength_eq_min
    {M d q : ℕ} (hqd : q * d ≤ M) :
    q * d + divisorDilationTriangularLength M d q = min M ((q + 1) * d) := by
  unfold divisorDilationTriangularLength
  have hprod : (q + 1) * d = q * d + d := by ring
  by_cases hM : M ≤ (q + 1) * d
  · rw [min_eq_left (by omega), min_eq_left hM]
    omega
  · rw [min_eq_right (by omega), min_eq_right (by omega), hprod]

/-- **Exact Integer Homothety of `divisorDilationTriangularLength`:**
For all `r, M, d, q : ℕ`, scaling `(M, d)` by `r` scales the clipped block length
`divisorDilationTriangularLength M d q = min (M - q * d) d` by `r`. -/
theorem divisorDilationTriangularLength_mul (r M d q : ℕ) :
    divisorDilationTriangularLength (r * M) (r * d) q =
      r * divisorDilationTriangularLength M d q := by
  unfold divisorDilationTriangularLength
  have hsub : r * M - q * (r * d) = r * (M - q * d) := by
    rw [show q * (r * d) = r * (q * d) by ring, ← Nat.mul_sub_left_distrib]
  rw [hsub]
  by_cases h : M - q * d ≤ d
  · rw [min_eq_left h, min_eq_left (Nat.mul_le_mul_left r h)]
  · have hle : d ≤ M - q * d := by omega
    rw [min_eq_right (Nat.mul_le_mul_left r hle), min_eq_right hle]

/-- **Half-Open Interval Representation of a Quotient Fiber:**
For `1 ≤ d`, `1 ≤ q`, and `q ≤ (M - 1) / d`, the quotient fiber
`(Icc d (M - 1)).filter (fun k => k / d = q)` equals the half-open interval
`Ico (q * d) (q * d + divisorDilationTriangularLength M d q)`. -/
theorem filter_Icc_div_eq_Ico_triangularLength
    {M d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) (hqM : q ≤ (M - 1) / d) :
    (Finset.Icc d (M - 1)).filter (fun k => k / d = q) =
      Finset.Ico (q * d) (q * d + divisorDilationTriangularLength M d q) := by
  have hlowerM : q * d ≤ M - 1 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hqM
  have hqd1 : 1 ≤ q * d := Nat.mul_pos (by omega) (by omega)
  have hqdM : q * d ≤ M := by omega
  have hM1 : 1 ≤ M := by omega
  have hX1 : 1 ≤ (q + 1) * d := Nat.mul_pos (by omega) (by omega)
  rw [filter_Icc_div_eq_block hd hq, ← Finset.Ico_add_one_right_eq_Icc,
    add_divisorDilationTriangularLength_eq_min hqdM]
  congr 1
  by_cases hMX : M ≤ (q + 1) * d
  · rw [min_eq_left (by omega), Nat.sub_add_cancel hM1, min_eq_left hMX]
  · rw [min_eq_right (by omega), Nat.sub_add_cancel hX1, min_eq_right (by omega)]

/-- **Clipped Half-Open Interval Representation of a Quotient Fiber:**
For `1 ≤ d`, `1 ≤ q`, and `q ≤ (M - 1) / d`,
`(Icc d (M - 1)).filter (fun k => k / d = q) = Ico (q * d) (min M ((q + 1) * d))`. -/
theorem filter_Icc_div_eq_Ico_min
    {M d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) (hqM : q ≤ (M - 1) / d) :
    (Finset.Icc d (M - 1)).filter (fun k => k / d = q) =
      Finset.Ico (q * d) (min M ((q + 1) * d)) := by
  have hlowerM : q * d ≤ M - 1 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hqM
  rw [filter_Icc_div_eq_Ico_triangularLength hd hq hqM,
    add_divisorDilationTriangularLength_eq_min (by omega)]

/-- **Universal Single-Block Telescoping Law:**
For any primitive `G : ℕ → ℝ` and any quotient fiber `1 ≤ d`, `1 ≤ q ≤ (M - 1) / d`, the sum of
`(G (k + 1) - G k) * primeFreeDivisorDefect (k / d)` over the fiber `k / d = q` telescopes in
closed form to `(G (q * d + divisorDilationTriangularLength M d q) - G (q * d)) * primeFreeDivisorDefect q`. -/
theorem sum_quotientBlock_sub_primitive
    (G : ℕ → ℝ) {M d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) (hqM : q ≤ (M - 1) / d) :
    (∑ k ∈ (Finset.Icc d (M - 1)).filter (fun k => k / d = q),
      (G (k + 1) - G k) * primeFreeDivisorDefect (k / d)) =
      (G (q * d + divisorDilationTriangularLength M d q) - G (q * d)) *
        primeFreeDivisorDefect q := by
  let S := (Finset.Icc d (M - 1)).filter (fun k => k / d = q)
  calc
    (∑ k ∈ S, (G (k + 1) - G k) * primeFreeDivisorDefect (k / d)) =
        ∑ k ∈ S, (G (k + 1) - G k) * primeFreeDivisorDefect q := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    _ = (∑ k ∈ S, (G (k + 1) - G k)) * primeFreeDivisorDefect q := by
      rw [← Finset.sum_mul]
    _ = (G (q * d + divisorDilationTriangularLength M d q) - G (q * d)) *
          primeFreeDivisorDefect q := by
      congr 1
      rw [show S = Finset.Ico (q * d) (q * d + divisorDilationTriangularLength M d q) by
        exact filter_Icc_div_eq_Ico_triangularLength hd hq hqM]
      rw [Finset.sum_Ico_eq_sum_range,
        Nat.add_sub_cancel_left, sum_range_sub_shift G (q * d)]

/-- **Universal Quotient-Block Factorization for Telescoping Dilation Channels:**
For any primitive `G : ℕ → ℝ` and any `d ≥ 1`, grouping `k ∈ Icc d (M - 1)` by its floor quotient
`q = k / d ∈ Icc 1 ((M - 1) / d)` telescopes each block into
`G (q * d + divisorDilationTriangularLength M d q) - G (q * d)`. -/
theorem sum_Icc_sub_primitive_mul_primeFreeDivisorDefect_eq_quotientBlocks
    (G : ℕ → ℝ) {M d : ℕ} (hd : 1 ≤ d) :
    (∑ k ∈ Finset.Icc d (M - 1), (G (k + 1) - G k) * primeFreeDivisorDefect (k / d)) =
      ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
        (G (q * d + divisorDilationTriangularLength M d q) - G (q * d)) *
          primeFreeDivisorDefect q := by
  let K := Finset.Icc d (M - 1)
  let Q := Finset.Icc 1 ((M - 1) / d)
  calc
    (∑ k ∈ K, (G (k + 1) - G k) * primeFreeDivisorDefect (k / d)) =
        ∑ k ∈ K, ∑ q ∈ Q,
          if k / d = q then (G (k + 1) - G k) * primeFreeDivisorDefect (k / d) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ∈ Finset.Icc d (M - 1) := by simpa only [K] using hk
      have hqmem : k / d ∈ Q := by
        simp only [Q, Finset.mem_Icc]
        exact ⟨(Nat.le_div_iff_mul_le (by omega : 0 < d)).2
          (by simpa using (Finset.mem_Icc.mp hk').1),
          Nat.div_le_div_right (Finset.mem_Icc.mp hk').2⟩
      have hflip :
          (∑ q ∈ Q, if k / d = q then (G (k + 1) - G k) * primeFreeDivisorDefect (k / d) else 0) =
            ∑ q ∈ Q, if q = k / d then (G (k + 1) - G k) * primeFreeDivisorDefect (k / d) else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases heq : q = k / d
        · subst q; rfl
        · rw [if_neg heq, if_neg (Ne.symm heq)]
      rw [hflip, Finset.sum_ite_eq' Q (k / d), if_pos hqmem]
    _ = ∑ q ∈ Q, ∑ k ∈ K,
          if k / d = q then (G (k + 1) - G k) * primeFreeDivisorDefect (k / d) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Q,
          ∑ k ∈ K.filter (fun k => k / d = q),
            (G (k + 1) - G k) * primeFreeDivisorDefect (k / d) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_filter]
    _ = ∑ q ∈ Q,
          (G (q * d + divisorDilationTriangularLength M d q) - G (q * d)) *
            primeFreeDivisorDefect q := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq' := Finset.mem_Icc.mp (by simpa only [Q] using hq)
      exact sum_quotientBlock_sub_primitive G hd hq'.1 hq'.2

/-- **Universal Hyperbola-Transposed Collapsed Möbius-Kernel Identity:**
For any primitive `G : ℕ → ℝ` and any `M : ℕ`, transposing the hyperbola `1 ≤ d * q ≤ M - 1`
collapses the cofinal sum of the `μ(d)`-signed dilation channels into the inner product of
`primeFreeDivisorDefect q` with the collapsed Möbius kernel
`∑ d ∈ Icc 1 ((M - 1) / q), μ(d) * (G (q * d + divisorDilationTriangularLength M d q) - G (q * d))`. -/
theorem sum_mobius_sub_primitive_dilation_eq_divisorDefect_kernel
    (G : ℕ → ℝ) (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 (M - 1),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (∑ k ∈ Finset.Icc d (M - 1), (G (k + 1) - G k) * primeFreeDivisorDefect (k / d))) =
      ∑ q ∈ Finset.Icc 1 (M - 1),
        primeFreeDivisorDefect q *
          (∑ d ∈ Finset.Icc 1 ((M - 1) / q),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              (G (q * d + divisorDilationTriangularLength M d q) - G (q * d))) := by
  have hchannels :
      (∑ d ∈ Finset.Icc 1 (M - 1),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (∑ k ∈ Finset.Icc d (M - 1), (G (k + 1) - G k) * primeFreeDivisorDefect (k / d))) =
      ∑ d ∈ Finset.Icc 1 (M - 1),
        ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            (G (q * d + divisorDilationTriangularLength M d q) - G (q * d)) *
              primeFreeDivisorDefect q := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [sum_Icc_sub_primitive_mul_primeFreeDivisorDefect_eq_quotientBlocks G
      (Finset.mem_Icc.mp hd).1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hchannels,
    sum_hyperbola_swap_real (M - 1)
      (fun d q =>
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (G (q * d + divisorDilationTriangularLength M d q) - G (q * d)) *
            primeFreeDivisorDefect q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-! ## Section 2: Midpoint and Unshifted Second-Cesàro Quotient-Block Weights, Parabolic Terminal
Evaluations, and Collapsed Parabolic Möbius Kernels -/

/-- **Quotient-Block Weight for `divisorUnsignedMidpointSecondCesaroDilationChannel`:**
`midpointSecondCesaroBlockWeight M d q = L * (M - q * d - L / 2)` where
`L = divisorDilationTriangularLength M d q = min (M - q * d) d`. -/
def midpointSecondCesaroBlockWeight (M d q : ℕ) : ℝ :=
  (divisorDilationTriangularLength M d q : ℝ) *
    ((M : ℝ) - (q : ℝ) * (d : ℝ) - (divisorDilationTriangularLength M d q : ℝ) / 2)

/-- **Quotient-Block Weight for `divisorUnsignedSecondCesaroDilationChannel`:**
`secondCesaroBlockWeight M d q = L * (M - q * d - (L - 1) / 2)` where
`L = divisorDilationTriangularLength M d q = min (M - q * d) d`. -/
def secondCesaroBlockWeight (M d q : ℕ) : ℝ :=
  (divisorDilationTriangularLength M d q : ℝ) *
    ((M : ℝ) - (q : ℝ) * (d : ℝ) - ((divisorDilationTriangularLength M d q : ℝ) - 1) / 2)

/-- Exact linear-shift relation between `midpointSecondCesaroBlockWeight`,
`secondCesaroBlockWeight`, and `divisorDilationTriangularLength`:
`midpointSecondCesaroBlockWeight M d q = secondCesaroBlockWeight M d q - (1 / 2) * divisorDilationTriangularLength M d q`. -/
theorem midpointSecondCesaroBlockWeight_eq_sub_half (M d q : ℕ) :
    midpointSecondCesaroBlockWeight M d q =
      secondCesaroBlockWeight M d q -
        (1 / 2 : ℝ) * (divisorDilationTriangularLength M d q : ℝ) := by
  unfold midpointSecondCesaroBlockWeight secondCesaroBlockWeight
  ring

/-- **Block-by-Block Degree-2 Integer Homothety of `midpointSecondCesaroBlockWeight`:**
For all `r, M, d, q : ℕ`,
`midpointSecondCesaroBlockWeight (r * M) (r * d) q = r^2 * midpointSecondCesaroBlockWeight M d q`. -/
theorem midpointSecondCesaroBlockWeight_mul (r M d q : ℕ) :
    midpointSecondCesaroBlockWeight (r * M) (r * d) q =
      (r : ℝ) ^ 2 * midpointSecondCesaroBlockWeight M d q := by
  unfold midpointSecondCesaroBlockWeight
  rw [divisorDilationTriangularLength_mul]
  push_cast
  ring

/-- **Complete-Block Evaluation of `midpointSecondCesaroBlockWeight`:**
On any complete block `(q + 1) * d ≤ M`,
`midpointSecondCesaroBlockWeight M d q = d * (M - q * d - d / 2)`. -/
theorem midpointSecondCesaroBlockWeight_eq_full
    {M d q : ℕ} (hfull : (q + 1) * d ≤ M) :
    midpointSecondCesaroBlockWeight M d q =
      (d : ℝ) * ((M : ℝ) - (q : ℝ) * (d : ℝ) - (d : ℝ) / 2) := by
  unfold midpointSecondCesaroBlockWeight
  rw [divisorDilationTriangularLength_eq_full hfull]

/-- **Pure Half-Square Terminal-Band Evaluation of `midpointSecondCesaroBlockWeight`:**
On the terminal band `q * d ≤ M ≤ (q + 1) * d`, `divisorDilationTriangularLength M d q = M - q * d`,
and `midpointSecondCesaroBlockWeight M d q` collapses to the **pure half-square**
`((M : ℝ) - (q : ℝ) * (d : ℝ))^2 / 2 ≥ 0`. -/
theorem midpointSecondCesaroBlockWeight_eq_terminal
    {M d q : ℕ} (hqd : q * d ≤ M) (hterminal : M ≤ (q + 1) * d) :
    midpointSecondCesaroBlockWeight M d q =
      ((M : ℝ) - (q : ℝ) * (d : ℝ)) ^ 2 / 2 := by
  unfold midpointSecondCesaroBlockWeight
  rw [divisorDilationTriangularLength_eq_terminal hterminal, Nat.cast_sub hqd, Nat.cast_mul]
  ring

/-- **Complete-Block Evaluation of `secondCesaroBlockWeight`:**
On any complete block `(q + 1) * d ≤ M`,
`secondCesaroBlockWeight M d q = d * (M - q * d - (d - 1) / 2)`. -/
theorem secondCesaroBlockWeight_eq_full
    {M d q : ℕ} (hfull : (q + 1) * d ≤ M) :
    secondCesaroBlockWeight M d q =
      (d : ℝ) * ((M : ℝ) - (q : ℝ) * (d : ℝ) - ((d : ℝ) - 1) / 2) := by
  unfold secondCesaroBlockWeight
  rw [divisorDilationTriangularLength_eq_full hfull]

/-- **Triangular-Number Terminal-Band Evaluation of `secondCesaroBlockWeight`:**
On the terminal band `q * d ≤ M ≤ (q + 1) * d`, `secondCesaroBlockWeight M d q` collapses to the
exact triangular number `(M - q * d) * (M - q * d + 1) / 2`. -/
theorem secondCesaroBlockWeight_eq_terminal
    {M d q : ℕ} (hqd : q * d ≤ M) (hterminal : M ≤ (q + 1) * d) :
    secondCesaroBlockWeight M d q =
      ((M : ℝ) - (q : ℝ) * (d : ℝ)) * ((M : ℝ) - (q : ℝ) * (d : ℝ) + 1) / 2 := by
  unfold secondCesaroBlockWeight
  rw [divisorDilationTriangularLength_eq_terminal hterminal, Nat.cast_sub hqd, Nat.cast_mul]
  ring

/-- **Quotient-Block Factorization of `divisorUnsignedMidpointSecondCesaroDilationChannel`:**
For every `d ≥ 1`,
`divisorUnsignedMidpointSecondCesaroDilationChannel M d = ∑ q ∈ Icc 1 ((M - 1) / d), midpointSecondCesaroBlockWeight M d q * primeFreeDivisorDefect q`. -/
theorem divisorUnsignedMidpointSecondCesaroDilationChannel_eq_quotientBlocks
    {M d : ℕ} (hd : 1 ≤ d) :
    divisorUnsignedMidpointSecondCesaroDilationChannel M d =
      ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
        midpointSecondCesaroBlockWeight M d q * primeFreeDivisorDefect q := by
  unfold divisorUnsignedMidpointSecondCesaroDilationChannel
  let G : ℕ → ℝ := fun k => (M : ℝ) * (k : ℝ) - (1 / 2 : ℝ) * (k : ℝ) ^ 2
  have hstep :
      (∑ k ∈ Finset.Icc d (M - 1),
        ((M : ℝ) - (k : ℝ) - (1 / 2 : ℝ)) * primeFreeDivisorDefect (k / d)) =
      ∑ k ∈ Finset.Icc d (M - 1), (G (k + 1) - G k) * primeFreeDivisorDefect (k / d) := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp [G]
    push_cast
    ring
  rw [hstep, sum_Icc_sub_primitive_mul_primeFreeDivisorDefect_eq_quotientBlocks G hd]
  apply Finset.sum_congr rfl
  intro q _
  unfold midpointSecondCesaroBlockWeight
  dsimp [G]
  push_cast
  ring

/-- **Quotient-Block Factorization of `divisorUnsignedSecondCesaroDilationChannel`:**
For every `d ≥ 1`,
`divisorUnsignedSecondCesaroDilationChannel M d = ∑ q ∈ Icc 1 ((M - 1) / d), secondCesaroBlockWeight M d q * primeFreeDivisorDefect q`. -/
theorem divisorUnsignedSecondCesaroDilationChannel_eq_quotientBlocks
    {M d : ℕ} (hd : 1 ≤ d) :
    divisorUnsignedSecondCesaroDilationChannel M d =
      ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
        secondCesaroBlockWeight M d q * primeFreeDivisorDefect q := by
  rw [show divisorUnsignedSecondCesaroDilationChannel M d =
      divisorUnsignedMidpointSecondCesaroDilationChannel M d +
        (1 / 2 : ℝ) * divisorUnsignedCesaroDilationChannel M d by
    linarith [divisorUnsignedMidpointSecondCesaroDilationChannel_eq_sub_half M d]]
  rw [divisorUnsignedMidpointSecondCesaroDilationChannel_eq_quotientBlocks hd,
    divisorUnsignedCesaroDilationChannel_eq_quotientBlocks hd,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [midpointSecondCesaroBlockWeight_eq_sub_half]
  ring

/-- **Collapsed Parabolic Möbius Kernel for Midpoint Second-Cesàro Summation:**
`mobiusClippedMidpointSecondCesaroKernel M q = ∑ d ∈ Icc 1 ((M - 1) / q), μ(d) * midpointSecondCesaroBlockWeight M d q`. -/
def mobiusClippedMidpointSecondCesaroKernel (M q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ((M - 1) / q),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * midpointSecondCesaroBlockWeight M d q

/-- **Collapsed Parabolic Möbius Kernel for Unshifted Second-Cesàro Summation:**
`mobiusClippedSecondCesaroKernel M q = ∑ d ∈ Icc 1 ((M - 1) / q), μ(d) * secondCesaroBlockWeight M d q`. -/
def mobiusClippedSecondCesaroKernel (M q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ((M - 1) / q),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * secondCesaroBlockWeight M d q

/-- Exact linear-shift relation between `mobiusClippedMidpointSecondCesaroKernel`,
`mobiusClippedSecondCesaroKernel`, and `mobiusClippedCesaroKernel`:
`mobiusClippedMidpointSecondCesaroKernel M q = mobiusClippedSecondCesaroKernel M q - (1 / 2) * mobiusClippedCesaroKernel M q`. -/
theorem mobiusClippedMidpointSecondCesaroKernel_eq_sub_half (M q : ℕ) :
    mobiusClippedMidpointSecondCesaroKernel M q =
      mobiusClippedSecondCesaroKernel M q - (1 / 2 : ℝ) * mobiusClippedCesaroKernel M q := by
  unfold mobiusClippedMidpointSecondCesaroKernel
    mobiusClippedSecondCesaroKernel mobiusClippedCesaroKernel
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  rw [midpointSecondCesaroBlockWeight_eq_sub_half]
  ring

/-- **Collapsed Midpoint Second-Cesàro Möbius-Kernel Producer Identity:**
For every `M : ℕ`,
`∑ d ∈ Icc 1 (M - 1), mobiusDivisorMidpointSecondCesaroDilationChannel M d = ∑ q ∈ Icc 1 (M - 1), primeFreeDivisorDefect q * mobiusClippedMidpointSecondCesaroKernel M q`. -/
theorem sum_mobiusDivisorMidpointSecondCesaroDilationChannel_eq_divisorDefect_kernel (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorMidpointSecondCesaroDilationChannel M d) =
      ∑ q ∈ Finset.Icc 1 (M - 1),
        primeFreeDivisorDefect q * mobiusClippedMidpointSecondCesaroKernel M q := by
  have hchannels :
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorMidpointSecondCesaroDilationChannel M d) =
      ∑ d ∈ Finset.Icc 1 (M - 1),
        ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            midpointSecondCesaroBlockWeight M d q *
              primeFreeDivisorDefect q := by
    apply Finset.sum_congr rfl
    intro d hd
    unfold mobiusDivisorMidpointSecondCesaroDilationChannel
    rw [divisorUnsignedMidpointSecondCesaroDilationChannel_eq_quotientBlocks
      (Finset.mem_Icc.mp hd).1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hchannels,
    sum_hyperbola_swap_real (M - 1)
      (fun d q =>
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          midpointSecondCesaroBlockWeight M d q *
            primeFreeDivisorDefect q)]
  apply Finset.sum_congr rfl
  intro q _
  unfold mobiusClippedMidpointSecondCesaroKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- **Collapsed Unshifted Second-Cesàro Möbius-Kernel Producer Identity:**
For every `M : ℕ`,
`∑ d ∈ Icc 1 (M - 1), mobiusDivisorSecondCesaroDilationChannel M d = ∑ q ∈ Icc 1 (M - 1), primeFreeDivisorDefect q * mobiusClippedSecondCesaroKernel M q`. -/
theorem sum_mobiusDivisorSecondCesaroDilationChannel_eq_divisorDefect_kernel (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorSecondCesaroDilationChannel M d) =
      ∑ q ∈ Finset.Icc 1 (M - 1),
        primeFreeDivisorDefect q * mobiusClippedSecondCesaroKernel M q := by
  have hchannels :
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorSecondCesaroDilationChannel M d) =
      ∑ d ∈ Finset.Icc 1 (M - 1),
        ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            secondCesaroBlockWeight M d q *
              primeFreeDivisorDefect q := by
    apply Finset.sum_congr rfl
    intro d hd
    unfold mobiusDivisorSecondCesaroDilationChannel
    rw [divisorUnsignedSecondCesaroDilationChannel_eq_quotientBlocks
      (Finset.mem_Icc.mp hd).1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hchannels,
    sum_hyperbola_swap_real (M - 1)
      (fun d q =>
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          secondCesaroBlockWeight M d q *
            primeFreeDivisorDefect q)]
  apply Finset.sum_congr rfl
  intro q _
  unfold mobiusClippedSecondCesaroKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Whenever `M ≤ q * d`, `divisorDilationTriangularLength M d q = 0` and
`secondCesaroBlockWeight M d q = 0`. -/
theorem secondCesaroBlockWeight_eq_zero_of_le
    {M d q : ℕ} (hle : M ≤ q * d) :
    secondCesaroBlockWeight M d q = 0 := by
  unfold secondCesaroBlockWeight divisorDilationTriangularLength
  have h0 : M - q * d = 0 := by omega
  simp [h0]

/-- **One-Step Recurrence in `M` for `secondCesaroBlockWeight`:**
For all `M, d, q : ℕ` with `q * d ≤ M`, the forward difference of `secondCesaroBlockWeight` in `M`
equals the First-Cesàro block length `divisorDilationTriangularLength (M + 1) d q`. -/
theorem secondCesaroBlockWeight_succ_sub
    {M d q : ℕ} (hqd : q * d ≤ M) :
    secondCesaroBlockWeight (M + 1) d q - secondCesaroBlockWeight M d q =
      (divisorDilationTriangularLength (M + 1) d q : ℝ) := by
  have hprod : (q + 1) * d = q * d + d := by ring
  by_cases hfull : (q + 1) * d ≤ M
  · have hfull' : (q + 1) * d ≤ M + 1 := by omega
    rw [secondCesaroBlockWeight_eq_full hfull', secondCesaroBlockWeight_eq_full hfull,
      divisorDilationTriangularLength_eq_full hfull']
    push_cast
    ring
  · have hterm : M ≤ (q + 1) * d := by omega
    have hterm' : M + 1 ≤ (q + 1) * d := by omega
    have hqd' : q * d ≤ M + 1 := by omega
    rw [secondCesaroBlockWeight_eq_terminal hqd' hterm',
      secondCesaroBlockWeight_eq_terminal hqd hterm,
      divisorDilationTriangularLength_eq_terminal hterm',
      Nat.cast_sub hqd']
    push_cast
    ring

/-- **One-Step Recurrence in `M` for `mobiusClippedSecondCesaroKernel`:**
For all `M, q : ℕ` with `1 ≤ q`,
`mobiusClippedSecondCesaroKernel (M + 1) q - mobiusClippedSecondCesaroKernel M q = mobiusClippedCesaroKernel (M + 1) q`. -/
theorem mobiusClippedSecondCesaroKernel_succ_sub
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusClippedSecondCesaroKernel (M + 1) q - mobiusClippedSecondCesaroKernel M q =
      mobiusClippedCesaroKernel (M + 1) q := by
  unfold mobiusClippedSecondCesaroKernel mobiusClippedCesaroKernel
  rw [Nat.add_sub_cancel]
  have hsub : Finset.Icc 1 ((M - 1) / q) ⊆ Finset.Icc 1 (M / q) := by
    intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    exact ⟨hd.1, hd.2.trans (Nat.div_le_div_right (by omega))⟩
  have hpad :
      (∑ d ∈ Finset.Icc 1 ((M - 1) / q),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * secondCesaroBlockWeight M d q) =
      ∑ d ∈ Finset.Icc 1 (M / q),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * secondCesaroBlockWeight M d q := by
    apply Finset.sum_subset hsub
    intro d hdM hdnot
    simp only [Finset.mem_Icc] at hdM hdnot
    have hgt : (M - 1) / q < d := by omega
    have hlt : M - 1 < q * d := by
      simpa [Nat.mul_comm] using Nat.lt_mul_of_div_lt hgt (by omega : 0 < q)
    rw [secondCesaroBlockWeight_eq_zero_of_le (by omega : M ≤ q * d), mul_zero]
  rw [hpad, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdI := Finset.mem_Icc.mp hd
  have hqd : q * d ≤ M := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < q)).mp hdI.2
  rw [← mul_sub, secondCesaroBlockWeight_succ_sub hqd]

/-- **Exact Cesàro-Kernel Prefix-Sum Representation of `mobiusClippedSecondCesaroKernel`:**
For every `M, q : ℕ` with `1 ≤ q`, the Second-Cesàro collapsed Möbius kernel is the exact prefix sum
of the First-Cesàro tent kernel `mobiusClippedCesaroKernel j q` over `j ∈ Icc 1 M`:
`mobiusClippedSecondCesaroKernel M q = ∑ j ∈ Icc 1 M, mobiusClippedCesaroKernel j q`. -/
theorem mobiusClippedSecondCesaroKernel_eq_sum_cesaroKernel
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusClippedSecondCesaroKernel M q =
      ∑ j ∈ Finset.Icc 1 M, mobiusClippedCesaroKernel j q := by
  induction M with
  | zero =>
    unfold mobiusClippedSecondCesaroKernel
    simp
  | succ M ih =>
    have hsplit : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : M + 1 ∉ Finset.Icc 1 M := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert hnotmem, ← ih]
    linarith [mobiusClippedSecondCesaroKernel_succ_sub (M := M) hq]

/-! ## Section 3: Cell-Integral Square-Root Riesz and Quadratic-Gap Abel Quotient-Block
Factorizations, Cubic-Square Terminal Factorization, and Collapsed Riesz Möbius Kernels -/

/-- **Quotient-Block Weight for `divisorUnsignedCellSqrtRieszDilationChannel`:**
`cellSqrtRieszBlockWeight M d q = √M * L - (2 / 3) * ((q * d + L) * √(q * d + L) - (q * d) * √(q * d))`
where `L = divisorDilationTriangularLength M d q`. -/
def cellSqrtRieszBlockWeight (M d q : ℕ) : ℝ :=
  Real.sqrt (M : ℝ) * (divisorDilationTriangularLength M d q : ℝ) -
    (2 / 3 : ℝ) *
      (((q * d + divisorDilationTriangularLength M d q : ℕ) : ℝ) *
        Real.sqrt ((q * d + divisorDilationTriangularLength M d q : ℕ) : ℝ) -
        ((q * d : ℕ) : ℝ) * Real.sqrt ((q * d : ℕ) : ℝ))

/-- **Quotient-Block Factorization of `divisorUnsignedCellSqrtRieszDilationChannel`:**
For every `d ≥ 1`,
`divisorUnsignedCellSqrtRieszDilationChannel M d = ∑ q ∈ Icc 1 ((M - 1) / d), cellSqrtRieszBlockWeight M d q * primeFreeDivisorDefect q`. -/
theorem divisorUnsignedCellSqrtRieszDilationChannel_eq_quotientBlocks
    {M d : ℕ} (hd : 1 ≤ d) :
    divisorUnsignedCellSqrtRieszDilationChannel M d =
      ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
        cellSqrtRieszBlockWeight M d q * primeFreeDivisorDefect q := by
  unfold divisorUnsignedCellSqrtRieszDilationChannel
  let G : ℕ → ℝ := fun k =>
    Real.sqrt (M : ℝ) * (k : ℝ) - (2 / 3 : ℝ) * (k : ℝ) * Real.sqrt (k : ℝ)
  have hstep :
      (∑ k ∈ Finset.Icc d (M - 1),
        sqrtRieszCellIntegralWeight M k * primeFreeDivisorDefect (k / d)) =
      ∑ k ∈ Finset.Icc d (M - 1), (G (k + 1) - G k) * primeFreeDivisorDefect (k / d) := by
    apply Finset.sum_congr rfl
    intro k _
    unfold sqrtRieszCellIntegralWeight
    dsimp [G]
    push_cast
    ring
  rw [hstep, sum_Icc_sub_primitive_mul_primeFreeDivisorDefect_eq_quotientBlocks G hd]
  apply Finset.sum_congr rfl
  intro q _
  unfold cellSqrtRieszBlockWeight
  dsimp [G]
  push_cast
  ring

/-- **Complete-Block Evaluation of `cellSqrtRieszBlockWeight`:**
On any complete block `(q + 1) * d ≤ M`,
`cellSqrtRieszBlockWeight M d q = d * √M - (2 / 3) * d * √d * ((q + 1) * √(q + 1) - q * √q)`. -/
theorem cellSqrtRieszBlockWeight_eq_full
    {M d q : ℕ} (hfull : (q + 1) * d ≤ M) :
    cellSqrtRieszBlockWeight M d q =
      (d : ℝ) * Real.sqrt (M : ℝ) -
        (2 / 3 : ℝ) * (d : ℝ) * Real.sqrt (d : ℝ) *
          (((q + 1 : ℕ) : ℝ) * Real.sqrt ((q + 1 : ℕ) : ℝ) -
            (q : ℝ) * Real.sqrt (q : ℝ)) := by
  unfold cellSqrtRieszBlockWeight
  rw [divisorDilationTriangularLength_eq_full hfull,
    show q * d + d = (q + 1) * d by ring]
  push_cast
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (q : ℝ))]
  ring

/-- **Non-Negative Cubic-Square Terminal-Band Factorization of `cellSqrtRieszBlockWeight`:**
On the terminal band `q * d ≤ M ≤ (q + 1) * d`, `cellSqrtRieszBlockWeight M d q` factors into the
manifestly non-negative cubic form
`(1 / 3) * (√M - √(q * d))^2 * (√M + 2 * √(q * d)) ≥ 0`, vanishing to second order at `q * d = M`. -/
theorem cellSqrtRieszBlockWeight_eq_terminal_factored
    {M d q : ℕ} (hqd : q * d ≤ M) (hterminal : M ≤ (q + 1) * d) :
    cellSqrtRieszBlockWeight M d q =
      (1 / 3 : ℝ) * (Real.sqrt (M : ℝ) - Real.sqrt ((q * d : ℕ) : ℝ)) ^ 2 *
        (Real.sqrt (M : ℝ) + 2 * Real.sqrt ((q * d : ℕ) : ℝ)) := by
  unfold cellSqrtRieszBlockWeight
  have hadd : q * d + divisorDilationTriangularLength M d q = M := by
    rw [divisorDilationTriangularLength_eq_terminal hterminal]
    omega
  rw [hadd, divisorDilationTriangularLength_eq_terminal hterminal, Nat.cast_sub hqd]
  set u : ℝ := Real.sqrt (M : ℝ)
  set v : ℝ := Real.sqrt ((q * d : ℕ) : ℝ)
  have hu2 : u ^ 2 = (M : ℝ) := Real.sq_sqrt (by positivity)
  have hv2 : v ^ 2 = ((q * d : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  rw [← hu2, ← hv2]
  ring

/-- On the terminal band `q * d ≤ M ≤ (q + 1) * d`, `0 ≤ cellSqrtRieszBlockWeight M d q`. -/
theorem cellSqrtRieszBlockWeight_terminal_nonneg
    {M d q : ℕ} (hqd : q * d ≤ M) (hterminal : M ≤ (q + 1) * d) :
    0 ≤ cellSqrtRieszBlockWeight M d q := by
  rw [cellSqrtRieszBlockWeight_eq_terminal_factored hqd hterminal]
  positivity

/-- **Collapsed Cell-Integral Square-Root Riesz Möbius Kernel:**
`mobiusClippedCellSqrtRieszKernel M q = ∑ d ∈ Icc 1 ((M - 1) / q), μ(d) * cellSqrtRieszBlockWeight M d q`. -/
def mobiusClippedCellSqrtRieszKernel (M q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ((M - 1) / q),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * cellSqrtRieszBlockWeight M d q

/-- **Collapsed Cell-Integral Square-Root Riesz Möbius-Kernel Producer Identity:**
For every `M : ℕ`,
`∑ d ∈ Icc 1 (M - 1), mobiusDivisorCellSqrtRieszDilationChannel M d = ∑ q ∈ Icc 1 (M - 1), primeFreeDivisorDefect q * mobiusClippedCellSqrtRieszKernel M q`. -/
theorem sum_mobiusDivisorCellSqrtRieszDilationChannel_eq_divisorDefect_kernel (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCellSqrtRieszDilationChannel M d) =
      ∑ q ∈ Finset.Icc 1 (M - 1),
        primeFreeDivisorDefect q * mobiusClippedCellSqrtRieszKernel M q := by
  have hchannels :
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCellSqrtRieszDilationChannel M d) =
      ∑ d ∈ Finset.Icc 1 (M - 1),
        ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
            cellSqrtRieszBlockWeight M d q *
              primeFreeDivisorDefect q := by
    apply Finset.sum_congr rfl
    intro d hd
    unfold mobiusDivisorCellSqrtRieszDilationChannel
    rw [divisorUnsignedCellSqrtRieszDilationChannel_eq_quotientBlocks
      (Finset.mem_Icc.mp hd).1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hchannels,
    sum_hyperbola_swap_real (M - 1)
      (fun d q =>
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          cellSqrtRieszBlockWeight M d q *
            primeFreeDivisorDefect q)]
  apply Finset.sum_congr rfl
  intro q _
  unfold mobiusClippedCellSqrtRieszKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- **Quotient-Block Weight for `divisorUnsignedQuadraticSqrtAbelDilationChannel`:**
`quadraticSqrtAbelBlockWeight M d q = (√M - √(q * d))^2 - (√M - √(q * d + L))^2` where
`L = divisorDilationTriangularLength M d q`. -/
def quadraticSqrtAbelBlockWeight (M d q : ℕ) : ℝ :=
  (Real.sqrt (M : ℝ) - Real.sqrt ((q * d : ℕ) : ℝ)) ^ 2 -
    (Real.sqrt (M : ℝ) - Real.sqrt ((q * d + divisorDilationTriangularLength M d q : ℕ) : ℝ)) ^ 2

/-- **Quotient-Block Factorization of `divisorUnsignedQuadraticSqrtAbelDilationChannel`:**
For every `d ≥ 1`,
`divisorUnsignedQuadraticSqrtAbelDilationChannel M d = ∑ q ∈ Icc 1 ((M - 1) / d), quadraticSqrtAbelBlockWeight M d q * primeFreeDivisorDefect q`. -/
theorem divisorUnsignedQuadraticSqrtAbelDilationChannel_eq_quotientBlocks
    {M d : ℕ} (hd : 1 ≤ d) :
    divisorUnsignedQuadraticSqrtAbelDilationChannel M d =
      ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
        quadraticSqrtAbelBlockWeight M d q * primeFreeDivisorDefect q := by
  unfold divisorUnsignedQuadraticSqrtAbelDilationChannel
  let G : ℕ → ℝ := fun k => -(Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) ^ 2
  have hstep :
      (∑ k ∈ Finset.Icc d (M - 1),
        ((Real.sqrt (M : ℝ) - Real.sqrt (k : ℝ)) ^ 2 -
          (Real.sqrt (M : ℝ) - Real.sqrt ((k + 1 : ℕ) : ℝ)) ^ 2) *
          primeFreeDivisorDefect (k / d)) =
      ∑ k ∈ Finset.Icc d (M - 1), (G (k + 1) - G k) * primeFreeDivisorDefect (k / d) := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp [G]
    ring
  rw [hstep, sum_Icc_sub_primitive_mul_primeFreeDivisorDefect_eq_quotientBlocks G hd]
  apply Finset.sum_congr rfl
  intro q _
  unfold quadraticSqrtAbelBlockWeight
  dsimp [G]
  ring

/-- **Pure-Square Terminal-Band Evaluation of `quadraticSqrtAbelBlockWeight`:**
On the terminal band `q * d ≤ M ≤ (q + 1) * d`, `q * d + divisorDilationTriangularLength M d q = M`,
so the right-endpoint term `(√M - √M)^2` vanishes and `quadraticSqrtAbelBlockWeight M d q`
collapses to the **pure square** `(√M - √(q * d))^2 ≥ 0`. -/
theorem quadraticSqrtAbelBlockWeight_eq_terminal
    {M d q : ℕ} (hqd : q * d ≤ M) (hterminal : M ≤ (q + 1) * d) :
    quadraticSqrtAbelBlockWeight M d q =
      (Real.sqrt (M : ℝ) - Real.sqrt ((q * d : ℕ) : ℝ)) ^ 2 := by
  unfold quadraticSqrtAbelBlockWeight
  have hadd : q * d + divisorDilationTriangularLength M d q = M := by
    rw [divisorDilationTriangularLength_eq_terminal hterminal]
    omega
  rw [hadd]
  ring

/-! ## Section 4: Channel-Wise Cesàro Prefix-Sum Representations and Zero-Centered-Hyperbola-Loss
Upper Bounds for Second-Cesàro, Midpoint Second-Cesàro, and Left Square-Root Riesz Channels -/

/-- **Channel-Wise Cesàro Prefix-Sum Representation of
`divisorUnsignedSecondCesaroDilationChannel`:**
For all `M, d : ℕ`, the unshifted Second-Cesàro channel is the exact prefix sum of the First-Cesàro
channel `divisorUnsignedCesaroDilationChannel j d` over `j ∈ Icc 1 M`:
`divisorUnsignedSecondCesaroDilationChannel M d = ∑ j ∈ Icc 1 M, divisorUnsignedCesaroDilationChannel j d`. -/
theorem divisorUnsignedSecondCesaroDilationChannel_eq_sum_cesaro (M d : ℕ) :
    divisorUnsignedSecondCesaroDilationChannel M d =
      ∑ j ∈ Finset.Icc 1 M, divisorUnsignedCesaroDilationChannel j d := by
  induction M with
  | zero =>
    unfold divisorUnsignedSecondCesaroDilationChannel
    rw [sum_Icc_mul_primeFreeDivisorDefect_eq_range]
    simp
  | succ M ih =>
    have hsplit : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : M + 1 ∉ Finset.Icc 1 M := by
      simp only [Finset.mem_Icc]
      omega
    rw [hsplit, Finset.sum_insert hnotmem, ← ih]
    linarith [divisorUnsignedSecondCesaroDilationChannel_succ_sub M d]

/-- **Consecutive-Average Representation of `divisorUnsignedMidpointSecondCesaroDilationChannel`:**
For all `M ≥ 1` and `d : ℕ`, the degree-2 homothety eigenchannel
`divisorUnsignedMidpointSecondCesaroDilationChannel M d` is the exact consecutive average of the
unshifted Second-Cesàro channel at `M - 1` and `M`:
`divisorUnsignedMidpointSecondCesaroDilationChannel M d = (divisorUnsignedSecondCesaroDilationChannel (M - 1) d + divisorUnsignedSecondCesaroDilationChannel M d) / 2`. -/
theorem divisorUnsignedMidpointSecondCesaroDilationChannel_eq_avg
    {M : ℕ} (hM : 1 ≤ M) (d : ℕ) :
    divisorUnsignedMidpointSecondCesaroDilationChannel M d =
      (divisorUnsignedSecondCesaroDilationChannel (M - 1) d +
        divisorUnsignedSecondCesaroDilationChannel M d) / 2 := by
  rw [divisorUnsignedMidpointSecondCesaroDilationChannel_eq_sub_half M d]
  have hstep := divisorUnsignedSecondCesaroDilationChannel_succ_sub (M - 1) d
  rw [Nat.sub_add_cancel hM] at hstep
  linarith

/-- **Channel-Wise Cesàro Prefix-Sum Representation of
`divisorUnsignedSqrtRieszDilationChannel`:**
For all `M, d : ℕ`, the Left-Endpoint Square-Root Riesz channel is the exact `(√(j + 1) - √j)`-weighted
prefix sum of the First-Cesàro channel `divisorUnsignedCesaroDilationChannel j d` over `j ∈ range M`. -/
theorem divisorUnsignedSqrtRieszDilationChannel_eq_sum_cesaro (M d : ℕ) :
    divisorUnsignedSqrtRieszDilationChannel M d =
      ∑ j ∈ Finset.range M,
        (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) *
          divisorUnsignedCesaroDilationChannel j d := by
  induction M with
  | zero =>
    unfold divisorUnsignedSqrtRieszDilationChannel
    rw [sum_Icc_mul_primeFreeDivisorDefect_eq_range]
    simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ← ih]
    linarith [divisorUnsignedSqrtRieszDilationChannel_succ_sub M d]

/-- **Exact Shifted Prefix-Sum Identity for `secularSqrtIncrementAction`:**
For every `M ≥ 2`,
`∑ j ∈ range M, (√(j + 1) - √j) * ((j - 1 : ℕ) : ℝ) = secularSqrtIncrementAction M - (√M - √2)`. -/
theorem sum_range_sqrt_diff_mul_pred_eq_secularSqrtIncrementAction_sub
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ j ∈ Finset.range M,
      (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) * ((j - 1 : ℕ) : ℝ)) =
      secularSqrtIncrementAction M - (Real.sqrt (M : ℝ) - Real.sqrt 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hM
  induction n with
  | zero =>
    simp [secularSqrtIncrementAction, Finset.sum_range_succ]
  | succ n ih =>
    have hih := ih (by omega)
    have hsec := secularSqrtIncrementAction_succ_sub_of_two_le n
    rw [show 2 + (n + 1) = (2 + n) + 1 by omega, Finset.sum_range_succ, hih]
    have hn3 : 2 + n + 1 = n + 3 := by omega
    have hn1 : 2 + n - 1 = n + 1 := by omega
    have hn2 : 2 + n = n + 2 := by omega
    rw [hn3, hn1, hn2]
    have hc3 : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
    have hc2 : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    have hc1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hc3, hc2, hc1]
    linear_combination -hsec

/-- **Prefix-Sum Dominance by `secularSqrtIncrementAction`:**
For every `M : ℕ`,
`∑ j ∈ range M, (√(j + 1) - √j) * ((j - 1 : ℕ) : ℝ) ≤ secularSqrtIncrementAction M`. -/
theorem sum_range_sqrt_diff_mul_pred_le_secularSqrtIncrementAction (M : ℕ) :
    (∑ j ∈ Finset.range M,
      (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) * ((j - 1 : ℕ) : ℝ)) ≤
      secularSqrtIncrementAction M := by
  by_cases hM : M < 2
  · interval_cases M <;> simp [secularSqrtIncrementAction]
  · have hM2 : 2 ≤ M := by omega
    rw [sum_range_sqrt_diff_mul_pred_eq_secularSqrtIncrementAction_sub hM2]
    have hsqrt : Real.sqrt 2 ≤ Real.sqrt (M : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hM2)
    linarith

/-- **Unconditional Zero-Centered-Hyperbola-Loss Upper Bound for the Unit Second-Cesàro Channel:**
Because `divisorUnsignedSecondCesaroDilationChannel M 1 = ∑ j ∈ Icc 1 M, divisorUnsignedCesaroDilationChannel j 1`
and `divisorUnsignedCesaroDilationChannel j 1 ≤ divisorHyperbolaSmoothMean * (j - 1) + 33 * √(j - 1)`
with zero centered-hyperbola loss for every `j`, summing over `j ∈ Icc 1 M` yields for all `M : ℕ`:
`divisorUnsignedSecondCesaroDilationChannel M 1 ≤ divisorHyperbolaSmoothMean * (M * (M - 1) / 2) + 33 * (M - 1) * √(M - 1)`. -/
theorem divisorUnsignedSecondCesaroDilationChannel_one_le (M : ℕ) :
    divisorUnsignedSecondCesaroDilationChannel M 1 ≤
      divisorHyperbolaSmoothMean * ((M : ℝ) * ((M - 1 : ℕ) : ℝ) / 2) +
        33 * ((M - 1 : ℕ) : ℝ) * Real.sqrt (M - 1 : ℕ) := by
  induction M with
  | zero =>
    unfold divisorUnsignedSecondCesaroDilationChannel
    rw [sum_Icc_mul_primeFreeDivisorDefect_eq_range]
    simp
  | succ M ih =>
    have hstep := divisorUnsignedSecondCesaroDilationChannel_succ_sub M 1
    have hces := divisorUnsignedCesaroDilationChannel_one_le_smoothMean_add_sqrt (M + 1)
    rw [Nat.add_sub_cancel] at hces ⊢
    by_cases hM0 : M = 0
    · subst M
      have h1 : divisorUnsignedSecondCesaroDilationChannel 1 1 = 0 := by
        unfold divisorUnsignedSecondCesaroDilationChannel
        simp
      simp [h1]
    · have hM1 : 1 ≤ M := by omega
      have hsqrt : Real.sqrt (M - 1 : ℕ) ≤ Real.sqrt (M : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast (by omega : M - 1 ≤ M))
      have hmul :
          33 * ((M - 1 : ℕ) : ℝ) * Real.sqrt (M - 1 : ℕ) + 33 * Real.sqrt (M : ℝ) ≤
            33 * (M : ℝ) * Real.sqrt (M : ℝ) := by
        have h1 :
            33 * ((M - 1 : ℕ) : ℝ) * Real.sqrt (M - 1 : ℕ) ≤
              33 * ((M - 1 : ℕ) : ℝ) * Real.sqrt (M : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
        have hcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel hM1
        have h2 :
            33 * ((M - 1 : ℕ) : ℝ) * Real.sqrt (M : ℝ) + 33 * Real.sqrt (M : ℝ) =
              33 * (M : ℝ) * Real.sqrt (M : ℝ) := by
          linear_combination 33 * Real.sqrt (M : ℝ) * hcast
        linarith
      have hquad :
          divisorHyperbolaSmoothMean * ((M : ℝ) * ((M - 1 : ℕ) : ℝ) / 2) +
            divisorHyperbolaSmoothMean * (M : ℝ) =
            divisorHyperbolaSmoothMean * (((M + 1 : ℕ) : ℝ) * (M : ℝ) / 2) := by
        rw [Nat.cast_sub hM1, Nat.cast_one, Nat.cast_add, Nat.cast_one]
        ring
      linarith

/-- **Unconditional Zero-Centered-Hyperbola-Loss Upper Bound for the Unit Midpoint Second-Cesàro
Eigenchannel:**
Averaging `divisorUnsignedSecondCesaroDilationChannel_one_le` at `M - 1` and `M` via
`divisorUnsignedMidpointSecondCesaroDilationChannel_eq_avg` yields for all `M ≥ 1`:
`divisorUnsignedMidpointSecondCesaroDilationChannel M 1 ≤ divisorHyperbolaSmoothMean * ((M - 1)^2 / 2) + 33 * (M - 1) * √(M - 1)`. -/
theorem divisorUnsignedMidpointSecondCesaroDilationChannel_one_le
    {M : ℕ} (hM : 1 ≤ M) :
    divisorUnsignedMidpointSecondCesaroDilationChannel M 1 ≤
      divisorHyperbolaSmoothMean * (((M - 1 : ℕ) : ℝ) ^ 2 / 2) +
        33 * ((M - 1 : ℕ) : ℝ) * Real.sqrt (M - 1 : ℕ) := by
  rw [divisorUnsignedMidpointSecondCesaroDilationChannel_eq_avg hM 1]
  have h1 := divisorUnsignedSecondCesaroDilationChannel_one_le (M - 1)
  have h2 := divisorUnsignedSecondCesaroDilationChannel_one_le M
  by_cases hM1 : M = 1
  · subst M
    have hz0 : divisorUnsignedSecondCesaroDilationChannel 0 1 = 0 := by
      unfold divisorUnsignedSecondCesaroDilationChannel
      rw [sum_Icc_mul_primeFreeDivisorDefect_eq_range]
      simp
    have hz1 : divisorUnsignedSecondCesaroDilationChannel 1 1 = 0 := by
      unfold divisorUnsignedSecondCesaroDilationChannel
      simp
    simp [hz0, hz1]
  · have hM2 : 2 ≤ M := by omega
    have hle1 : M - 1 - 1 ≤ M - 1 := by omega
    have hsqrt : Real.sqrt (M - 1 - 1 : ℕ) ≤ Real.sqrt (M - 1 : ℕ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hle1)
    have hcast_le : ((M - 1 - 1 : ℕ) : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hle1
    have hterm :
        33 * ((M - 1 - 1 : ℕ) : ℝ) * Real.sqrt (M - 1 - 1 : ℕ) ≤
          33 * ((M - 1 : ℕ) : ℝ) * Real.sqrt (M - 1 : ℕ) := by
      have ha :
          33 * ((M - 1 - 1 : ℕ) : ℝ) * Real.sqrt (M - 1 - 1 : ℕ) ≤
            33 * ((M - 1 : ℕ) : ℝ) * Real.sqrt (M - 1 - 1 : ℕ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcast_le (by positivity))
          (Real.sqrt_nonneg _)
      have hb :
          33 * ((M - 1 : ℕ) : ℝ) * Real.sqrt (M - 1 - 1 : ℕ) ≤
            33 * ((M - 1 : ℕ) : ℝ) * Real.sqrt (M - 1 : ℕ) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      exact ha.trans hb
    have hquad :
        (divisorHyperbolaSmoothMean * (((M - 1 : ℕ) : ℝ) * ((M - 1 - 1 : ℕ) : ℝ) / 2) +
          divisorHyperbolaSmoothMean * ((M : ℝ) * ((M - 1 : ℕ) : ℝ) / 2)) / 2 =
          divisorHyperbolaSmoothMean * (((M - 1 : ℕ) : ℝ) ^ 2 / 2) := by
      have hc1 : ((M - 1 - 1 : ℕ) : ℝ) = (M : ℝ) - 2 := by
        rw [show M - 1 - 1 = M - 2 by omega, Nat.cast_sub hM2]
        norm_num
      have hc2 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
        rw [Nat.cast_sub hM, Nat.cast_one]
      rw [hc1, hc2]
      ring
    linarith

/-- **Unconditional Dilated Degree-2 Upper Bound for
`divisorUnsignedMidpointSecondCesaroDilationChannel (r * Q) r`:**
Combining the exact degree-2 homothety law `divisorUnsignedMidpointSecondCesaroDilationChannel_mul`
with `divisorUnsignedMidpointSecondCesaroDilationChannel_one_le` yields for all `r : ℕ` and `Q ≥ 1`:
`divisorUnsignedMidpointSecondCesaroDilationChannel (r * Q) r ≤ r^2 * (divisorHyperbolaSmoothMean * ((Q - 1)^2 / 2) + 33 * (Q - 1) * √(Q - 1))`. -/
theorem divisorUnsignedMidpointSecondCesaroDilationChannel_mul_one_le
    (r : ℕ) {Q : ℕ} (hQ : 1 ≤ Q) :
    divisorUnsignedMidpointSecondCesaroDilationChannel (r * Q) r ≤
      (r : ℝ) ^ 2 *
        (divisorHyperbolaSmoothMean * (((Q - 1 : ℕ) : ℝ) ^ 2 / 2) +
           33 * ((Q - 1 : ℕ) : ℝ) * Real.sqrt (Q - 1 : ℕ)) := by
  have h := divisorUnsignedMidpointSecondCesaroDilationChannel_mul r Q 1
  rw [Nat.mul_one] at h
  rw [h]
  exact mul_le_mul_of_nonneg_left
    (divisorUnsignedMidpointSecondCesaroDilationChannel_one_le hQ) (by positivity)

/-- **Unconditional Zero-Centered-Hyperbola-Loss Upper Bound for the Unit Left-Endpoint Square-Root
Riesz Channel:**
Using `divisorUnsignedSqrtRieszDilationChannel_eq_sum_cesaro`,
`divisorUnsignedCesaroDilationChannel_one_le_smoothMean_add_sqrt`, and
`sum_range_sqrt_diff_mul_pred_eq_secularSqrtIncrementAction_sub`, for every `M ≥ 2`:
`divisorUnsignedSqrtRieszDilationChannel M 1 ≤ divisorHyperbolaSmoothMean * (secularSqrtIncrementAction M - (√M - √2)) + 33 * √(M - 1) * √M`. -/
theorem divisorUnsignedSqrtRieszDilationChannel_one_le
    {M : ℕ} (hM : 2 ≤ M) :
    divisorUnsignedSqrtRieszDilationChannel M 1 ≤
      divisorHyperbolaSmoothMean *
        (secularSqrtIncrementAction M - (Real.sqrt (M : ℝ) - Real.sqrt 2)) +
        33 * Real.sqrt (M - 1 : ℕ) * Real.sqrt (M : ℝ) := by
  rw [divisorUnsignedSqrtRieszDilationChannel_eq_sum_cesaro,
    ← sum_range_sqrt_diff_mul_pred_eq_secularSqrtIncrementAction_sub hM]
  have htel :
      (∑ j ∈ Finset.range M, (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ))) =
        Real.sqrt (M : ℝ) := by
    have h := Finset.sum_range_sub (fun j : ℕ => Real.sqrt (j : ℝ)) M
    simpa using h
  calc
    (∑ j ∈ Finset.range M,
        (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) *
          divisorUnsignedCesaroDilationChannel j 1) ≤
      ∑ j ∈ Finset.range M,
        (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) *
          (divisorHyperbolaSmoothMean * ((j - 1 : ℕ) : ℝ) +
            33 * Real.sqrt (M - 1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjM : j < M := Finset.mem_range.mp hj
      have hdiff_nonneg : 0 ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ) := by
        have : Real.sqrt (j : ℝ) ≤ Real.sqrt ((j + 1 : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast (by omega : j ≤ j + 1))
        linarith
      apply mul_le_mul_of_nonneg_left _ hdiff_nonneg
      have hces := divisorUnsignedCesaroDilationChannel_one_le_smoothMean_add_sqrt j
      have hsqrt : Real.sqrt (j - 1 : ℕ) ≤ Real.sqrt (M - 1 : ℕ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast (by omega : j - 1 ≤ M - 1))
      linarith
    _ = divisorHyperbolaSmoothMean *
          (∑ j ∈ Finset.range M,
            (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) * ((j - 1 : ℕ) : ℝ)) +
        33 * Real.sqrt (M - 1 : ℕ) *
          (∑ j ∈ Finset.range M, (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = divisorHyperbolaSmoothMean *
          (∑ j ∈ Finset.range M,
            (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt (j : ℝ)) * ((j - 1 : ℕ) : ℝ)) +
        33 * Real.sqrt (M - 1 : ℕ) * Real.sqrt (M : ℝ) := by
      rw [htel]

end

end GaloisForLFunctions.RHTower
