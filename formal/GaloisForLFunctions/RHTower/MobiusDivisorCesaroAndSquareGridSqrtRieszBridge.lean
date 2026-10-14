import GaloisForLFunctions.RHTower.MidpointSlopeQuadraticTaylorAndQuarticCancellingCentralDiffBridge
import GaloisForLFunctions.RHTower.DivisorSmoothSquareBlockMean
import GaloisForLFunctions.RHTower.DivisorHyperbolaPositivePrefix

/-!
# Zero-Error Möbius–Divisor Bridges for `chebyshevSqrtIncrementAction` and `chebyshevClassicalCesaroSum`, Linear Dilation Homothety, and Square-Grid Tauberian Sandwiches

This module advances the unconditional RHTower hierarchy beyond
`MidpointSlopeQuadraticTaylorAndQuarticCancellingCentralDiffBridge.lean` (Module 30) by
establishing **exact, zero-error algebraic identities** connecting the Chebyshev Riesz/Cesàro
actions (`chebyshevSqrtIncrementAction M` and `chebyshevClassicalCesaroSum M`) developed in
Modules 11–30 with the prime-free Möbius–divisor and centered-hyperbola producer hierarchy
(`coherentSelbergSquareRootAbelMoment`, `mobiusDivisorSquareRootAbelMoment`,
`mobiusDivisorDilationChannel`, `primeFreeDivisorDefect`, `divisorHyperbolaSmoothRemainder`, and
`centeredDivisorHyperbola`):

## Mathematical Overview

1. **Section 1 (Exact Zero-Error Identities Connecting `chebyshevSqrtIncrementAction`,
   `coherentSelbergSquareRootAbelMoment`, and `mobiusDivisorSquareRootAbelMoment`, and Square-Grid
   Second-Difference Cancellation of `γ`):**
   - In Module 11 (`NormalizedChebyshevCesaroAndSqrtRieszBridge.lean`), we compared
     `mobiusDivisorSquareRootAbelMoment M` and `chebyshevSqrtIncrementAction M` (`F_√(M)`) up to
     an `O(M)` error via double summation by parts of the observer-jet Mertens lag.
   - Here we prove the **exact, zero-error algebraic identities** valid for every integer `M ≥ 2`:
     `coherentSelbergSquareRootAbelMoment M = chebyshevSqrtIncrementAction M - (√2 - 1)`
     (`coherentSelbergSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_sub`) and
     `mobiusDivisorSquareRootAbelMoment M = chebyshevSqrtIncrementAction M + 2 * γ * (√M - 1) - (√2 - 1)`
     (`mobiusDivisorSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_add`).
   - On the square grid `M = s^2` (`s ≥ 2`), `√(s^2) = s` is **linear** in `s`. Consequently, in
     any symmetric three-square second difference on `[(m - h)^2, m^2, (m + h)^2]` (`2 ≤ m - h`),
     both the Euler–Mascheroni boundary term `2 * γ * (s - 1)` and the initial constant `-(√2 - 1)`
     **cancel identically to zero** (`mobiusDivisorSquareRootAbelMoment_square_second_diff_eq`):
     `Δ²_{sq, h} mobiusDivisorSquareRootAbelMoment (m) = Δ²_{sq, h} chebyshevSqrtIncrementAction (m)`.
     Combining this with `chebyshevSqrtConvexPotential_square_second_diff_psi_sandwich` and
     `secularSqrtIncrementAction_square_second_diff_sandwich` yields an unconditional `γ`-free
     three-square second-difference lower bound (`mobiusDivisorSquareRootAbelMoment_square_second_diff_ge`).

2. **Section 2 (The First-Cesàro Möbius–Divisor Dilation Channels, Exact Decomposition of
   `chebyshevClassicalCesaroSum`, and Linear Integer Homothety):**
   - Summing `psiDefect k = ∑_{d = 1}^k μ(d) * primeFreeDivisorDefect (k / d)` over
     `k ∈ [1, M - 1]` and transposing the triangular summation domain `1 ≤ d ≤ k ≤ M - 1` defines
     the **unsigned and signed first-Cesàro Möbius–divisor dilation channels**:
     `divisorUnsignedCesaroDilationChannel M d := ∑ k ∈ Icc d (M - 1), primeFreeDivisorDefect (k / d)`
     and
     `mobiusDivisorCesaroDilationChannel M d := μ(d) * divisorUnsignedCesaroDilationChannel M d`.
   - For all `M ≥ 2`, we prove the **exact first-Cesàro Möbius–divisor identity**
     (`chebyshevClassicalCesaroSum_eq_sum_mobiusDivisorCesaroDilationChannel_sub`):
     `chebyshevClassicalCesaroSum M = (∑ d ∈ Icc 1 (M - 1), mobiusDivisorCesaroDilationChannel M d) - 2 * γ * (M - 1) + 1`.
   - Furthermore, because the Cesàro weight is constant (`1`) on every residue class `r * q + i`
     (`0 ≤ i < r`), `divisorUnsignedCesaroDilationChannel` satisfies the **exact degree-1 integer
     homothety law** (`divisorUnsignedCesaroDilationChannel_mul`):
     `divisorUnsignedCesaroDilationChannel (r * M) (r * d) = r * divisorUnsignedCesaroDilationChannel M d`
     for all `r, M, d : ℕ`, with exact coprime multiplicative masking for the signed channel
     (`mobiusDivisorCesaroDilationChannel_mul_coprime` and `mobiusDivisorCesaroDilationChannel_mul_masked`).

3. **Section 3 (Quotient-Block Factorization, the Collapsed Integer-Tent Kernel
   `mobiusClippedCesaroKernel`, and Zero-Loss Upper Bounds on the Unit and Dilated Cesàro Channels):**
   - Grouping `k ∈ Icc d (M - 1)` by its floor quotient `q = k / d ∈ Icc 1 ((M - 1) / d)` proves
     that each quotient block has exact integer weight `divisorDilationTriangularLength M d q = min (M - q * d) d`
     (`divisorUnsignedCesaroDilationChannel_eq_quotientBlocks`), and transposing the hyperbola
     `d * q ≤ M - 1` collapses the Cesàro sum against the integer-tent kernel
     `mobiusClippedCesaroKernel M q = ∑_{d ≤ (M - 1) / q} μ(d) * min (M - q * d) d`
     (`sum_mobiusDivisorCesaroDilationChannel_eq_divisorDefect_kernel`).
   - For the unit channel `d = 1`, combining `divisorHyperbolaSmooth_add_centered`,
     `sum_centeredDivisorHyperbola_eq_primitives`, `sum_divisorHyperbolaSmooth_mean_error`, and the
     unconditional non-positivity `∑_{k=1}^{M-1} centeredDivisorHyperbola k ≤ 0`
     (`sum_centeredDivisorHyperbola_bounds`) yields an unconditional one-sided upper bound with
     **zero centered-hyperbola loss** (`divisorUnsignedCesaroDilationChannel_one_le_smoothMean_add_sqrt`):
     `divisorUnsignedCesaroDilationChannel M 1 ≤ divisorHyperbolaSmoothMean * (M - 1) + 33 * √(M - 1)`,
     and by exact homothety its `r`-dilated counterpart for `divisorUnsignedCesaroDilationChannel (r * Q) r`.

4. **Section 4 (Direct Square-Grid Tauberian Step Sandwiches for `mobiusDivisorSquareRootAbelMoment`
   and `mobiusDivisorCesaroDilationChannel`):**
   - Coupling the zero-error bridge identities from Sections 1–2 with our square-grid Euler–Maclaurin
     and convex-potential sandwiches from Modules 12, 20, and 22 produces explicit forward and
     backward square-grid step inequalities directly relating `ψ(m^2) - m^2` to increments of
     `mobiusDivisorSquareRootAbelMoment` (`[m^2, (m + h)^2]` and `[(m - h)^2, m^2]`, the latter with
     zero Euler–Maclaurin remainder!) and to consecutive-square differences of the first-Cesàro
     Möbius–divisor dilation sum.
-/

namespace GaloisForLFunctions.RHTower

open scoped BigOperators Chebyshev ArithmeticFunction
open Real Finset _root_.RHTower

noncomputable section

/-! ## Section 1: Exact Zero-Error Identities Connecting `chebyshevSqrtIncrementAction`,
`coherentSelbergSquareRootAbelMoment`, and `mobiusDivisorSquareRootAbelMoment`, and Square-Grid
Second-Difference Cancellation of `γ` -/

/-- At `k = 1`, `chebyshevPsi 1 = 0` and `psiRemainder 1 = -1`. -/
theorem psiRemainder_one : psiRemainder 1 = -1 := by
  unfold psiRemainder chebyshevPsi
  simp [ArithmeticFunction.vonMangoldt_apply_one]

/-- For every `k : ℕ`, `psiRemainder (k + 2) = Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)`. -/
theorem psiRemainder_add_two (k : ℕ) :
    psiRemainder (k + 2) = Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2) := by
  rw [psiRemainder, chebyshevPsi_eq_psi]
  push_cast
  ring

/-- **Exact Zero-Error Bridge Between `coherentSelbergSquareRootAbelMoment` and
`chebyshevSqrtIncrementAction`:**
For every integer `M ≥ 2`,
`coherentSelbergSquareRootAbelMoment M = chebyshevSqrtIncrementAction M - (√2 - 1)`
identically, with zero approximation error. -/
theorem coherentSelbergSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_sub
    {M : ℕ} (hM : 2 ≤ M) :
    coherentSelbergSquareRootAbelMoment M =
      chebyshevSqrtIncrementAction M - (Real.sqrt 2 - 1) := by
  unfold coherentSelbergSquareRootAbelMoment chebyshevSqrtIncrementAction
  have hsplit : Finset.Icc 1 (M - 1) = insert 1 (Finset.Ico 2 M) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnotmem : (1 : ℕ) ∉ Finset.Ico 2 M := by
    simp only [Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_insert hnotmem, psiRemainder_one]
  have h1 : (Real.sqrt ((1 : ℕ) + 1 : ℕ) - Real.sqrt (1 : ℕ)) * (-1 : ℝ) =
      -(Real.sqrt 2 - 1) := by
    norm_num
  rw [h1, Finset.sum_Ico_eq_sum_range]
  have hsum :
      (∑ x ∈ Finset.range (M - 2),
        (Real.sqrt (2 + x + 1 : ℕ) - Real.sqrt (2 + x : ℕ)) * psiRemainder (2 + x)) =
      ∑ k ∈ Finset.range (M - 2),
        (Real.sqrt (k + 3 : ℕ) - Real.sqrt (k + 2 : ℕ)) *
          (Chebyshev.psi (k + 2 : ℕ) - (k + 2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show (2 + k + 1 : ℕ) = k + 3 by omega, show (2 + k : ℕ) = k + 2 by omega,
      psiRemainder_add_two k]
    push_cast
    ring
  rw [hsum]
  ring

/-- **Exact Zero-Error Bridge Between `mobiusDivisorSquareRootAbelMoment` and
`chebyshevSqrtIncrementAction`:**
For every integer `M ≥ 2`,
`mobiusDivisorSquareRootAbelMoment M = chebyshevSqrtIncrementAction M + 2 * γ * (√M - 1) - (√2 - 1)`
identically, improving the `O(M)` comparison of Module 11 to an exact algebraic identity. -/
theorem mobiusDivisorSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_add
    {M : ℕ} (hM : 2 ≤ M) :
    mobiusDivisorSquareRootAbelMoment M =
      chebyshevSqrtIncrementAction M +
        2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1) - (Real.sqrt 2 - 1) := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary (by omega : 1 ≤ M),
    coherentSelbergSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_sub hM]
  ring

/-- **Exact Dilation-Channel Sum Identity for `chebyshevSqrtIncrementAction`:**
For every integer `M ≥ 2`, the cofinal sum of the signed Möbius–divisor dilation channels
`mobiusDivisorDilationChannel M d` equals
`chebyshevSqrtIncrementAction M + 2 * γ * (√M - 1) - (√2 - 1)`. -/
theorem sum_mobiusDivisorDilationChannel_eq_chebyshevSqrtIncrementAction_add
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorDilationChannel M d) =
      chebyshevSqrtIncrementAction M +
        2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1) - (Real.sqrt 2 - 1) := by
  rw [← mobiusDivisorSquareRootAbelMoment_eq_sum_dilationChannels,
    mobiusDivisorSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_add hM]

/-- **Exact Window Difference Identity for `mobiusDivisorSquareRootAbelMoment`:**
On any integer window `2 ≤ N ≤ M`, the constant `-(√2 - 1)` and `-2 * γ` cancel identically:
`mobiusDivisorSquareRootAbelMoment M - mobiusDivisorSquareRootAbelMoment N = (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) + 2 * γ * (√M - √N)`. -/
theorem mobiusDivisorSquareRootAbelMoment_sub_eq
    {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    mobiusDivisorSquareRootAbelMoment M - mobiusDivisorSquareRootAbelMoment N =
      (chebyshevSqrtIncrementAction M - chebyshevSqrtIncrementAction N) +
        2 * Real.eulerMascheroniConstant * (Real.sqrt M - Real.sqrt N) := by
  have hM : 2 ≤ M := le_trans hN hNM
  rw [mobiusDivisorSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_add hM,
    mobiusDivisorSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_add hN]
  ring

/-- **Exact Square-Grid Evaluation of `mobiusDivisorSquareRootAbelMoment`:**
At every perfect square `M = m^2` (`m ≥ 2`), `√(m^2) = m` rationalizes the Euler–Mascheroni
boundary term to an affine linear function of `m`:
`mobiusDivisorSquareRootAbelMoment (m^2) = chebyshevSqrtIncrementAction (m^2) + 2 * γ * (m - 1) - (√2 - 1)`. -/
theorem mobiusDivisorSquareRootAbelMoment_sq_eq
    {m : ℕ} (hm : 2 ≤ m) :
    mobiusDivisorSquareRootAbelMoment (m ^ 2) =
      chebyshevSqrtIncrementAction (m ^ 2) +
        2 * Real.eulerMascheroniConstant * ((m : ℝ) - 1) - (Real.sqrt 2 - 1) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  rw [mobiusDivisorSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_add hm2,
    sqrt_nat_sq_eq m]

/-- **Exact `γ`-Free Three-Square Second-Difference Identity for `mobiusDivisorSquareRootAbelMoment`:**
Because `2 * γ * (s - 1) - (√2 - 1)` is affine linear in `s`, on any symmetric three-square stencil
`((m - h)^2, m^2, (m + h)^2)` with `2 ≤ m - h`, both `γ` and `√2 - 1` cancel identically:
`Δ²_{sq, h} mobiusDivisorSquareRootAbelMoment (m) = Δ²_{sq, h} chebyshevSqrtIncrementAction (m)`. -/
theorem mobiusDivisorSquareRootAbelMoment_square_second_diff_eq
    {m h : ℕ} (hmh : 2 ≤ m - h) :
    mobiusDivisorSquareRootAbelMoment ((m - h) ^ 2) +
        mobiusDivisorSquareRootAbelMoment ((m + h) ^ 2) -
        2 * mobiusDivisorSquareRootAbelMoment (m ^ 2) =
      chebyshevSqrtIncrementAction ((m - h) ^ 2) +
        chebyshevSqrtIncrementAction ((m + h) ^ 2) -
        2 * chebyshevSqrtIncrementAction (m ^ 2) := by
  have hm : 2 ≤ m := by omega
  have hmh_le : h ≤ m := by omega
  have hadd : 2 ≤ m + h := by omega
  rw [mobiusDivisorSquareRootAbelMoment_sq_eq hmh,
    mobiusDivisorSquareRootAbelMoment_sq_eq hadd,
    mobiusDivisorSquareRootAbelMoment_sq_eq hm,
    Nat.cast_sub hmh_le, Nat.cast_add]
  ring

/-- **Two-Sided Three-Square Second-Difference Sandwich for `chebyshevSqrtConvexPotential`:**
For all `m, h : ℕ` with `h + 2 ≤ m`:
1. `0 ≤ chebyshevSqrtConvexPotential ((m - h)^2) + chebyshevSqrtConvexPotential ((m + h)^2) - 2 * chebyshevSqrtConvexPotential (m^2)`,
2. `chebyshevSqrtConvexPotential ((m - h)^2) + chebyshevSqrtConvexPotential ((m + h)^2) - 2 * chebyshevSqrtConvexPotential (m^2) ≤ h * (ψ((m + h)^2) - ψ((m - h)^2))`. -/
theorem chebyshevSqrtConvexPotential_square_second_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    0 ≤ chebyshevSqrtConvexPotential ((m - h) ^ 2) +
          chebyshevSqrtConvexPotential ((m + h) ^ 2) -
          2 * chebyshevSqrtConvexPotential (m ^ 2) ∧
      chebyshevSqrtConvexPotential ((m - h) ^ 2) +
          chebyshevSqrtConvexPotential ((m + h) ^ 2) -
          2 * chebyshevSqrtConvexPotential (m ^ 2) ≤
        (h : ℝ) * (Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) -
          Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ)) := by
  have hmh_le : h ≤ m := by omega
  have hmh2 : 2 ≤ (m - h) ^ 2 := by
    have : 2 ≤ m - h := by omega
    nlinarith
  have hm2 : 2 ≤ m ^ 2 := by
    have : 2 ≤ m := by omega
    nlinarith
  have hle_left : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (Nat.sub_le m h) 2
  have hle_right : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  have hfwd := chebyshevSqrtConvexPotential_sub_bounds hm2 hle_right
  have hbwd := chebyshevSqrtConvexPotential_sub_bounds hmh2 hle_left
  rw [sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq m, Nat.cast_add] at hfwd
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m - h), Nat.cast_sub hmh_le] at hbwd
  constructor <;> linarith [hfwd.1, hfwd.2, hbwd.1, hbwd.2]

/-- **Unconditional `γ`-Free Three-Square Second-Difference Lower Bound for
`mobiusDivisorSquareRootAbelMoment`:**
Combining `mobiusDivisorSquareRootAbelMoment_square_second_diff_eq`,
`chebyshevSqrtConvexPotential_square_second_diff_sandwich` (`0 ≤ Δ²_{sq, h} Φ_√(m)`), and
`secularSqrtIncrementAction_square_second_diff_sandwich`
(`Δ²_{sq, h} S_{F_√}(m) ≤ 2 * m * h^2 + (1 / 24) * (1 / m - 1 / (m + h)) ≤ 2 * m * h^2 + (1 / 24) / m`)
yields the explicit lower bound on `[(m - h)^2, m^2, (m + h)^2]` for all `h + 2 ≤ m`:
`-(2 * m * h^2 + (1 / 24) / m) ≤ Δ²_{sq, h} mobiusDivisorSquareRootAbelMoment (m)`. -/
theorem mobiusDivisorSquareRootAbelMoment_square_second_diff_ge
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    -(2 * (m : ℝ) * (h : ℝ) ^ 2 + (1 / 24 : ℝ) / (m : ℝ)) ≤
      mobiusDivisorSquareRootAbelMoment ((m - h) ^ 2) +
        mobiusDivisorSquareRootAbelMoment ((m + h) ^ 2) -
        2 * mobiusDivisorSquareRootAbelMoment (m ^ 2) := by
  have hmh2 : 2 ≤ m - h := by omega
  rw [mobiusDivisorSquareRootAbelMoment_square_second_diff_eq hmh2,
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular (m ^ 2)]
  have hphi := (chebyshevSqrtConvexPotential_square_second_diff_sandwich hmh).1
  have hsec := (secularSqrtIncrementAction_square_second_diff_sandwich hmh).2
  have hrem_nonneg : 0 ≤ (1 / 24 : ℝ) * (1 / ((m : ℝ) + (h : ℝ))) := by positivity
  linarith [show (1 / 24 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) =
    (1 / 24 : ℝ) / (m : ℝ) - (1 / 24 : ℝ) * (1 / ((m : ℝ) + (h : ℝ))) by ring]

/-- **Two-Sided `γ`-Free Three-Square Second-Difference Sandwich for
`mobiusDivisorSquareRootAbelMoment`:**
For all `h + 2 ≤ m`,
`-(2 * m * h^2 + (1 / 24) / m) ≤ Δ²_{sq, h} mobiusDivisorSquareRootAbelMoment (m) ≤ h * (ψ((m + h)^2) - ψ((m - h)^2)) - 2 * m * h^2 + (1 / 24) / (m - h)`. -/
theorem mobiusDivisorSquareRootAbelMoment_square_second_diff_sandwich
    {m h : ℕ} (hmh : h + 2 ≤ m) :
    -(2 * (m : ℝ) * (h : ℝ) ^ 2 + (1 / 24 : ℝ) / (m : ℝ)) ≤
        mobiusDivisorSquareRootAbelMoment ((m - h) ^ 2) +
          mobiusDivisorSquareRootAbelMoment ((m + h) ^ 2) -
          2 * mobiusDivisorSquareRootAbelMoment (m ^ 2) ∧
      mobiusDivisorSquareRootAbelMoment ((m - h) ^ 2) +
          mobiusDivisorSquareRootAbelMoment ((m + h) ^ 2) -
          2 * mobiusDivisorSquareRootAbelMoment (m ^ 2) ≤
        (h : ℝ) * (Chebyshev.psi (((m + h) ^ 2 : ℕ) : ℝ) -
          Chebyshev.psi (((m - h) ^ 2 : ℕ) : ℝ)) -
          2 * (m : ℝ) * (h : ℝ) ^ 2 + (1 / 24 : ℝ) / ((m : ℝ) - (h : ℝ)) := by
  refine ⟨mobiusDivisorSquareRootAbelMoment_square_second_diff_ge hmh, ?_⟩
  have hmh2 : 2 ≤ m - h := by omega
  rw [mobiusDivisorSquareRootAbelMoment_square_second_diff_eq hmh2,
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular (m ^ 2)]
  have hphi := (chebyshevSqrtConvexPotential_square_second_diff_sandwich hmh).2
  have hsec := (secularSqrtIncrementAction_square_second_diff_sandwich hmh).1
  have hrem_nonneg : 0 ≤ (1 / 24 : ℝ) * (1 / (m : ℝ)) := by positivity
  linarith [show (1 / 24 : ℝ) * (1 / ((m : ℝ) - (h : ℝ)) - 1 / (m : ℝ)) =
    (1 / 24 : ℝ) / ((m : ℝ) - (h : ℝ)) - (1 / 24 : ℝ) * (1 / (m : ℝ)) by ring]

/-! ## Section 2: The First-Cesàro Möbius–Divisor Dilation Channels, Exact Decomposition of
`chebyshevClassicalCesaroSum`, and Linear Integer Homothety -/

/-- Exact relation between the prefix sum of `psiRemainder` on `Icc 1 (M - 1)` and
`chebyshevClassicalCesaroSum M`: for all `M ≥ 2`,
`∑ k ∈ Icc 1 (M - 1), psiRemainder k = chebyshevClassicalCesaroSum M - 1`. -/
theorem sum_Icc_psiRemainder_eq_chebyshevClassicalCesaroSum_sub_one
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.Icc 1 (M - 1), psiRemainder k) =
      chebyshevClassicalCesaroSum M - 1 := by
  unfold chebyshevClassicalCesaroSum
  have hsplit : Finset.Icc 1 (M - 1) = insert 1 (Finset.Ico 2 M) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnotmem : (1 : ℕ) ∉ Finset.Ico 2 M := by
    simp only [Finset.mem_Ico]
    omega
  rw [hsplit, Finset.sum_insert hnotmem, psiRemainder_one, Finset.sum_Ico_eq_sum_range]
  have hsum :
      (∑ x ∈ Finset.range (M - 2), psiRemainder (2 + x)) =
      ∑ k ∈ Finset.range (M - 2), (Chebyshev.psi ((k : ℝ) + 2) - ((k : ℝ) + 2)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [show (2 + k : ℕ) = k + 2 by omega, psiRemainder_add_two k]
  rw [hsum]
  ring

/-- Exact relation between the prefix sum of `psiDefect` on `Icc 1 (M - 1)` and
`chebyshevClassicalCesaroSum M`: for all `M ≥ 2`,
`∑ k ∈ Icc 1 (M - 1), psiDefect k = chebyshevClassicalCesaroSum M + 2 * γ * (M - 1) - 1`. -/
theorem sum_Icc_psiDefect_eq_chebyshevClassicalCesaroSum_add
    {M : ℕ} (hM : 2 ≤ M) :
    (∑ k ∈ Finset.Icc 1 (M - 1), psiDefect k) =
      chebyshevClassicalCesaroSum M +
        2 * Real.eulerMascheroniConstant * ((M : ℝ) - 1) - 1 := by
  have hrewrite :
      (∑ k ∈ Finset.Icc 1 (M - 1), psiDefect k) =
      ∑ k ∈ Finset.Icc 1 (M - 1),
        (psiRemainder k + 2 * Real.eulerMascheroniConstant) := by
    apply Finset.sum_congr rfl
    intro k _
    exact psiDefect_eq_psiRemainder_add k
  rw [hrewrite, Finset.sum_add_distrib,
    sum_Icc_psiRemainder_eq_chebyshevClassicalCesaroSum_sub_one hM,
    Finset.sum_const, Nat.card_Icc, show M - 1 + 1 - 1 = M - 1 by omega, nsmul_eq_mul,
    Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
  ring

/-- **Unsigned First-Cesàro Floor-Dilation Channel:**
`divisorUnsignedCesaroDilationChannel M d = ∑ k ∈ Icc d (M - 1), primeFreeDivisorDefect (k / d)`.
This is the unweighted (degree-1) Cesàro counterpart of `divisorUnsignedDilationChannel M d`. -/
def divisorUnsignedCesaroDilationChannel (M d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc d (M - 1), primeFreeDivisorDefect (k / d)

/-- **Signed First-Cesàro Möbius–Divisor Dilation Channel:**
`mobiusDivisorCesaroDilationChannel M d = μ(d) * divisorUnsignedCesaroDilationChannel M d`. -/
def mobiusDivisorCesaroDilationChannel (M d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) * divisorUnsignedCesaroDilationChannel M d

/-- **Exact First-Cesàro Dilation-Channel Fubini Law:**
For every `M : ℕ`,
`∑ k ∈ Icc 1 (M - 1), psiDefect k = ∑ d ∈ Icc 1 (M - 1), mobiusDivisorCesaroDilationChannel M d`. -/
theorem sum_Icc_psiDefect_eq_sum_mobiusDivisorCesaroDilationChannel (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 (M - 1), psiDefect k) =
      ∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCesaroDilationChannel M d := by
  let K := Finset.Icc 1 (M - 1)
  have hpoint : ∀ k ∈ K,
      psiDefect k =
        ∑ d ∈ K,
          if d ≤ k then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (k / d)
          else 0 := by
    intro k hk
    have hk' : k ∈ Finset.Icc 1 (M - 1) := by simpa only [K] using hk
    rw [psiDefect_eq_mobius_primeFreeDivisorDefect (Finset.mem_Icc.mp hk').1]
    have hset : Finset.Icc 1 k = K.filter (fun d => d ≤ k) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_filter, K]
      constructor
      · intro hd
        exact ⟨⟨hd.1, hd.2.trans (Finset.mem_Icc.mp hk').2⟩, hd.2⟩
      · intro hd
        exact ⟨hd.1.1, hd.2⟩
    rw [hset, Finset.sum_filter]
  rw [show Finset.Icc 1 (M - 1) = K by rfl]
  calc
    (∑ k ∈ K, psiDefect k) =
        ∑ k ∈ K, ∑ d ∈ K,
          if d ≤ k then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (k / d)
          else 0 := Finset.sum_congr rfl hpoint
    _ = ∑ d ∈ K, ∑ k ∈ K,
          if d ≤ k then
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * primeFreeDivisorDefect (k / d)
          else 0 := by rw [Finset.sum_comm]
    _ = ∑ d ∈ K, mobiusDivisorCesaroDilationChannel M d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' : d ∈ Finset.Icc 1 (M - 1) := by simpa only [K] using hd
      unfold mobiusDivisorCesaroDilationChannel divisorUnsignedCesaroDilationChannel
      have hset : K.filter (fun k => d ≤ k) = Finset.Icc d (M - 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, K]
        constructor
        · intro hk
          exact ⟨hk.2, hk.1.2⟩
        · intro hk
          exact ⟨⟨(Finset.mem_Icc.mp hd').1.trans hk.1, hk.2⟩, hk.1⟩
      rw [← hset, Finset.mul_sum, Finset.sum_filter]

/-- **Exact First-Cesàro Möbius–Divisor Dilation Decomposition of `chebyshevClassicalCesaroSum`:**
For every integer `M ≥ 2`,
`chebyshevClassicalCesaroSum M = (∑ d ∈ Icc 1 (M - 1), mobiusDivisorCesaroDilationChannel M d) - 2 * γ * (M - 1) + 1`. -/
theorem chebyshevClassicalCesaroSum_eq_sum_mobiusDivisorCesaroDilationChannel_sub
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevClassicalCesaroSum M =
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCesaroDilationChannel M d) -
        2 * Real.eulerMascheroniConstant * ((M : ℝ) - 1) + 1 := by
  have h1 := sum_Icc_psiDefect_eq_chebyshevClassicalCesaroSum_add hM
  have h2 := sum_Icc_psiDefect_eq_sum_mobiusDivisorCesaroDilationChannel M
  linarith

/-- Because `primeFreeDivisorDefect 0 = 0`, `divisorUnsignedCesaroDilationChannel M d` equals the
full prefix sum over `k ∈ range M` for all `M, d : ℕ`. -/
theorem divisorUnsignedCesaroDilationChannel_eq_range (M d : ℕ) :
    divisorUnsignedCesaroDilationChannel M d =
      ∑ k ∈ Finset.range M, primeFreeDivisorDefect (k / d) := by
  have hD0 : primeFreeDivisorDefect 0 = 0 := by simp [primeFreeDivisorDefect]
  by_cases hd : d = 0
  · simp [divisorUnsignedCesaroDilationChannel, hd, hD0]
  by_cases hM : M = 0
  · simp [divisorUnsignedCesaroDilationChannel, hM,
      Finset.Icc_eq_empty_of_lt (by omega : 0 < d)]
  by_cases hdM : d ≤ M
  · unfold divisorUnsignedCesaroDilationChannel
    rw [← Finset.Ico_add_one_right_eq_Icc, show M - 1 + 1 = M by omega,
      Finset.sum_Ico_eq_sub _ hdM]
    have hz : (∑ k ∈ Finset.range d, primeFreeDivisorDefect (k / d)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Nat.div_eq_of_lt (Finset.mem_range.mp hk), hD0]
    rw [hz, sub_zero]
  · unfold divisorUnsignedCesaroDilationChannel
    rw [Finset.Icc_eq_empty_of_lt (by omega : M - 1 < d), Finset.sum_empty]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    rw [Nat.div_eq_of_lt (by have := Finset.mem_range.mp hk; omega : k < d), hD0]

private theorem sum_range_mul_blocks (r M : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (r * M), f k) =
      ∑ q ∈ Finset.range M, ∑ i ∈ Finset.range r, f (r * q + i) := by
  induction M with
  | zero => simp
  | succ M ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- **Exact Degree-1 Integer Homothety of `divisorUnsignedCesaroDilationChannel`:**
For all `r, M, d : ℕ` (including zero indices and terminal clipped blocks),
`divisorUnsignedCesaroDilationChannel (r * M) (r * d) = r * divisorUnsignedCesaroDilationChannel M d`. -/
theorem divisorUnsignedCesaroDilationChannel_mul (r M d : ℕ) :
    divisorUnsignedCesaroDilationChannel (r * M) (r * d) =
      (r : ℝ) * divisorUnsignedCesaroDilationChannel M d := by
  rw [divisorUnsignedCesaroDilationChannel_eq_range,
    divisorUnsignedCesaroDilationChannel_eq_range]
  by_cases hr : r = 0
  · simp [hr]
  have hrpos : 0 < r := by omega
  rw [sum_range_mul_blocks]
  have hblock (q : ℕ) :
      (∑ i ∈ Finset.range r, primeFreeDivisorDefect ((r * q + i) / (r * d))) =
        (r : ℝ) * primeFreeDivisorDefect (q / d) := by
    have hdiv (i : ℕ) (hi : i ∈ Finset.range r) : (r * q + i) / (r * d) = q / d := by
      rw [← Nat.div_div_eq_div_mul, Nat.mul_add_div hrpos,
        Nat.div_eq_of_lt (Finset.mem_range.mp hi), Nat.add_zero]
    calc
      (∑ i ∈ Finset.range r, primeFreeDivisorDefect ((r * q + i) / (r * d))) =
          ∑ _i ∈ Finset.range r, primeFreeDivisorDefect (q / d) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hdiv i hi]
      _ = (r : ℝ) * primeFreeDivisorDefect (q / d) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp_rw [hblock, ← Finset.mul_sum]

/-- **Exact Signed First-Cesàro Homothety on Coprime Supports:**
When `r.Coprime d`,
`mobiusDivisorCesaroDilationChannel (r * M) (r * d) = r * μ(r) * mobiusDivisorCesaroDilationChannel M d`. -/
theorem mobiusDivisorCesaroDilationChannel_mul_coprime {r M d : ℕ}
    (hc : r.Coprime d) :
    mobiusDivisorCesaroDilationChannel (r * M) (r * d) =
      (r : ℝ) * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        mobiusDivisorCesaroDilationChannel M d := by
  unfold mobiusDivisorCesaroDilationChannel
  rw [divisorUnsignedCesaroDilationChannel_mul,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc]
  push_cast
  ring

/-- **Exact Signed First-Cesàro Homothety with Shared-Prime Masking:**
For all `r, M, d : ℕ`, shared prime factors between `r` and `d` annihilate the dilated channel. -/
theorem mobiusDivisorCesaroDilationChannel_mul_masked (r M d : ℕ) :
    mobiusDivisorCesaroDilationChannel (r * M) (r * d) =
      (r : ℝ) * ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        (if r.Coprime d then mobiusDivisorCesaroDilationChannel M d else 0) := by
  by_cases hc : r.Coprime d
  · rw [if_pos hc]
    exact mobiusDivisorCesaroDilationChannel_mul_coprime hc
  · have hm : ArithmeticFunction.moebius (r * d) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree
        (fun hsf => hc (Nat.coprime_of_squarefree_mul hsf))
    unfold mobiusDivisorCesaroDilationChannel
    rw [if_neg hc, mul_zero, hm, Int.cast_zero, zero_mul]

/-! ## Section 3: Quotient-Block Factorization of `divisorUnsignedCesaroDilationChannel`,
the Collapsed Integer-Tent Kernel `mobiusClippedCesaroKernel`, and Zero-Loss Upper Bounds on the
Unit and Dilated Cesàro Channels -/

/-- **Exact Clipped-Block First-Cesàro Law:**
On one quotient fiber `k / d = q` (`1 ≤ q ≤ (M - 1) / d`), `primeFreeDivisorDefect (k / d)` is
constant and the fiber cardinality is `divisorDilationTriangularLength M d q = min (M - q * d) d`. -/
theorem sum_divisorCesaroDilationQuotientBlock
    {M d q : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q)
    (hqM : q ≤ (M - 1) / d) :
    (∑ k ∈ (Finset.Icc d (M - 1)).filter (fun k => k / d = q),
      primeFreeDivisorDefect (k / d)) =
      (divisorDilationTriangularLength M d q : ℝ) * primeFreeDivisorDefect q := by
  let S := (Finset.Icc d (M - 1)).filter (fun k => k / d = q)
  have hlowerM : q * d ≤ M - 1 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hqM
  have hqdpos : 0 < q * d := Nat.mul_pos (by omega) (by omega)
  have hM : 1 ≤ M := by omega
  have hX : 1 ≤ (q + 1) * d := Nat.mul_pos (by omega) (by omega)
  have hcard : S.card = divisorDilationTriangularLength M d q := by
    rw [show S = Finset.Icc (q * d) (min (M - 1) ((q + 1) * d - 1)) by
      exact filter_Icc_div_eq_block hd hq]
    rw [Nat.card_Icc, divisorDilationTriangularLength]
    have hprod : (q + 1) * d = q * d + d := by ring
    by_cases hMX : M ≤ (q + 1) * d
    · rw [min_eq_left (by omega), Nat.sub_add_cancel hM, min_eq_left (by omega)]
    · rw [min_eq_right (by omega), Nat.sub_add_cancel hX, hprod, min_eq_right (by omega)]
      omega
  calc
    (∑ k ∈ S, primeFreeDivisorDefect (k / d)) =
        ∑ _k ∈ S, primeFreeDivisorDefect q := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [(Finset.mem_filter.mp hk).2]
    _ = (divisorDilationTriangularLength M d q : ℝ) * primeFreeDivisorDefect q := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]

/-- **Quotient-Block Factorization of `divisorUnsignedCesaroDilationChannel`:**
For every `d ≥ 1`,
`divisorUnsignedCesaroDilationChannel M d = ∑ q ∈ Icc 1 ((M - 1) / d), divisorDilationTriangularLength M d q * primeFreeDivisorDefect q`. -/
theorem divisorUnsignedCesaroDilationChannel_eq_quotientBlocks
    {M d : ℕ} (hd : 1 ≤ d) :
    divisorUnsignedCesaroDilationChannel M d =
      ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
        (divisorDilationTriangularLength M d q : ℝ) * primeFreeDivisorDefect q := by
  unfold divisorUnsignedCesaroDilationChannel
  let K := Finset.Icc d (M - 1)
  let Q := Finset.Icc 1 ((M - 1) / d)
  calc
    (∑ k ∈ K, primeFreeDivisorDefect (k / d)) =
        ∑ k ∈ K, ∑ q ∈ Q,
          if k / d = q then primeFreeDivisorDefect (k / d) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ∈ Finset.Icc d (M - 1) := by simpa only [K] using hk
      have hqmem : k / d ∈ Q := by
        simp only [Q, Finset.mem_Icc]
        exact ⟨(Nat.le_div_iff_mul_le (by omega : 0 < d)).2
          (by simpa using (Finset.mem_Icc.mp hk').1),
          Nat.div_le_div_right (Finset.mem_Icc.mp hk').2⟩
      have hflip :
          (∑ q ∈ Q, if k / d = q then primeFreeDivisorDefect (k / d) else 0) =
            ∑ q ∈ Q, if q = k / d then primeFreeDivisorDefect (k / d) else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        by_cases heq : q = k / d
        · subst q; rfl
        · rw [if_neg heq, if_neg (Ne.symm heq)]
      rw [hflip, Finset.sum_ite_eq' Q (k / d), if_pos hqmem]
    _ = ∑ q ∈ Q, ∑ k ∈ K,
          if k / d = q then primeFreeDivisorDefect (k / d) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Q, ∑ k ∈ K.filter (fun k => k / d = q), primeFreeDivisorDefect (k / d) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_filter]
    _ = ∑ q ∈ Q, (divisorDilationTriangularLength M d q : ℝ) * primeFreeDivisorDefect q := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq' := Finset.mem_Icc.mp (by simpa only [Q] using hq)
      exact sum_divisorCesaroDilationQuotientBlock hd hq'.1 hq'.2

/-- **Quotient-Block Factorization of `mobiusDivisorCesaroDilationChannel`:**
For every `d ≥ 1`,
`mobiusDivisorCesaroDilationChannel M d = μ(d) * ∑ q ∈ Icc 1 ((M - 1) / d), divisorDilationTriangularLength M d q * primeFreeDivisorDefect q`. -/
theorem mobiusDivisorCesaroDilationChannel_eq_quotientBlocks
    {M d : ℕ} (hd : 1 ≤ d) :
    mobiusDivisorCesaroDilationChannel M d =
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
          (divisorDilationTriangularLength M d q : ℝ) * primeFreeDivisorDefect q := by
  unfold mobiusDivisorCesaroDilationChannel
  rw [divisorUnsignedCesaroDilationChannel_eq_quotientBlocks hd]

/-- **Collapsed Integer-Tent Möbius Kernel for First-Cesàro Summation:**
`mobiusClippedCesaroKernel M q = ∑ d ∈ Icc 1 ((M - 1) / q), μ(d) * min (M - q * d) d`. -/
def mobiusClippedCesaroKernel (M q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 ((M - 1) / q),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (divisorDilationTriangularLength M d q : ℝ)

/-- **Collapsed First-Cesàro Möbius-Kernel Producer Identity:**
Transposing `1 ≤ d * q ≤ M - 1` expresses the sum of `mobiusDivisorCesaroDilationChannel M d` as
the inner product of `primeFreeDivisorDefect q` with the integer-tent kernel
`mobiusClippedCesaroKernel M q`. -/
theorem sum_mobiusDivisorCesaroDilationChannel_eq_divisorDefect_kernel (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCesaroDilationChannel M d) =
      ∑ q ∈ Finset.Icc 1 (M - 1),
        primeFreeDivisorDefect q * mobiusClippedCesaroKernel M q := by
  have hchannels :
      (∑ d ∈ Finset.Icc 1 (M - 1), mobiusDivisorCesaroDilationChannel M d) =
        ∑ d ∈ Finset.Icc 1 (M - 1),
          ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              (divisorDilationTriangularLength M d q : ℝ) *
                primeFreeDivisorDefect q := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [mobiusDivisorCesaroDilationChannel_eq_quotientBlocks (Finset.mem_Icc.mp hd).1,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hchannels,
    sum_hyperbola_swap_real (M - 1)
      (fun d q =>
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (divisorDilationTriangularLength M d q : ℝ) *
            primeFreeDivisorDefect q)]
  apply Finset.sum_congr rfl
  intro q _
  unfold mobiusClippedCesaroKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- **Exact Decomposition of the Unit First-Cesàro Channel `divisorUnsignedCesaroDilationChannel M 1`
into Smooth Remainder Prefix and Non-Positive Centered Modular Primitives:**
For every `M : ℕ`,
`divisorUnsignedCesaroDilationChannel M 1 = (∑ k ∈ Icc 1 (M - 1), divisorHyperbolaSmoothRemainder k) + 2 * (∑ d ∈ Icc 1 (Nat.sqrt (M - 1)), centeredModularPrimitive d M)`. -/
theorem divisorUnsignedCesaroDilationChannel_one_eq_smooth_add_centered (M : ℕ) :
    divisorUnsignedCesaroDilationChannel M 1 =
      (∑ k ∈ Finset.Icc 1 (M - 1), divisorHyperbolaSmoothRemainder k) +
        2 * (∑ d ∈ Finset.Icc 1 (Nat.sqrt (M - 1)),
          HTGeometry.centeredModularPrimitive d M) := by
  unfold divisorUnsignedCesaroDilationChannel
  have hsplit :
      (∑ k ∈ Finset.Icc 1 (M - 1), primeFreeDivisorDefect (k / 1)) =
        (∑ k ∈ Finset.Icc 1 (M - 1), divisorHyperbolaSmoothRemainder k) +
          2 * (∑ k ∈ Finset.Icc 1 (M - 1), centeredDivisorHyperbola k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.div_one]
    simpa only [primeFreeDivisorDefect] using (divisorHyperbolaSmooth_add_centered k).symm
  rw [hsplit]
  by_cases hM : M = 0
  · subst M
    simp
  · have hM1 : M - 1 + 1 = M := by omega
    rw [sum_centeredDivisorHyperbola_eq_primitives (M - 1), hM1]

/-- **Unconditional Zero-Loss One-Sided Upper Bound for the Unit First-Cesàro Channel:**
Because `∑_{k = 1}^{M - 1} centeredDivisorHyperbola k ≤ 0` unconditionally
(`sum_centeredDivisorHyperbola_bounds`), the centered hyperbola contributes **non-positively** to
`divisorUnsignedCesaroDilationChannel M 1`, yielding for all `M : ℕ`:
`divisorUnsignedCesaroDilationChannel M 1 ≤ divisorHyperbolaSmoothMean * (M - 1) + 33 * √(M - 1)`. -/
theorem divisorUnsignedCesaroDilationChannel_one_le_smoothMean_add_sqrt (M : ℕ) :
    divisorUnsignedCesaroDilationChannel M 1 ≤
      divisorHyperbolaSmoothMean * ((M - 1 : ℕ) : ℝ) + 33 * Real.sqrt (M - 1 : ℕ) := by
  unfold divisorUnsignedCesaroDilationChannel
  have hsplit :
      (∑ k ∈ Finset.Icc 1 (M - 1), primeFreeDivisorDefect (k / 1)) =
        (∑ k ∈ Finset.Icc 1 (M - 1), divisorHyperbolaSmoothRemainder k) +
          2 * (∑ k ∈ Finset.Icc 1 (M - 1), centeredDivisorHyperbola k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.div_one]
    simpa only [primeFreeDivisorDefect] using (divisorHyperbolaSmooth_add_centered k).symm
  have hsmooth := (abs_le.mp (sum_divisorHyperbolaSmooth_mean_error (M - 1))).2
  have hcent := (sum_centeredDivisorHyperbola_bounds (M - 1)).2
  linarith

/-- **Unconditional Dilated One-Sided Upper Bound for `divisorUnsignedCesaroDilationChannel (r * Q) r`:**
Combining `divisorUnsignedCesaroDilationChannel_mul` with
`divisorUnsignedCesaroDilationChannel_one_le_smoothMean_add_sqrt` yields for all `r, Q : ℕ`:
`divisorUnsignedCesaroDilationChannel (r * Q) r ≤ r * (divisorHyperbolaSmoothMean * (Q - 1) + 33 * √(Q - 1))`. -/
theorem divisorUnsignedCesaroDilationChannel_mul_one_le (r Q : ℕ) :
    divisorUnsignedCesaroDilationChannel (r * Q) r ≤
      (r : ℝ) * (divisorHyperbolaSmoothMean * ((Q - 1 : ℕ) : ℝ) +
        33 * Real.sqrt (Q - 1 : ℕ)) := by
  have h := divisorUnsignedCesaroDilationChannel_mul r Q 1
  rw [Nat.mul_one] at h
  rw [h]
  exact mul_le_mul_of_nonneg_left
    (divisorUnsignedCesaroDilationChannel_one_le_smoothMean_add_sqrt Q) (Nat.cast_nonneg r)

/-! ## Section 4: Direct Square-Grid Tauberian Step Sandwiches for
`mobiusDivisorSquareRootAbelMoment` and `mobiusDivisorCesaroDilationChannel` -/

/-- **Forward Square-Grid Step Lower Bound for `mobiusDivisorSquareRootAbelMoment` in Terms of
`ψ(m^2) - m^2`:**
For all `m ≥ 2` and `h ≥ 1`, on `[m^2, (m + h)^2]`:
`h * (ψ(m^2) - m^2 + 2 * γ - m * h - (1 / 3) * h^2 + 1 / 2) - (1 / 24) / m ≤ mobiusDivisorSquareRootAbelMoment ((m + h)^2) - mobiusDivisorSquareRootAbelMoment (m^2)`. -/
theorem mobiusDivisorSquareRootAbelMoment_forward_square_step_ge
    {m h : ℕ} (hm : 2 ≤ m) (_hh : 1 ≤ h) :
    (h : ℝ) * (Chebyshev.psi ((m : ℝ) ^ 2) - (m : ℝ) ^ 2 +
        2 * Real.eulerMascheroniConstant - (m : ℝ) * (h : ℝ) -
        (1 / 3 : ℝ) * (h : ℝ) ^ 2 + 1 / 2) - (1 / 24 : ℝ) / (m : ℝ) ≤
      mobiusDivisorSquareRootAbelMoment ((m + h) ^ 2) -
        mobiusDivisorSquareRootAbelMoment (m ^ 2) := by
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hle : m ^ 2 ≤ (m + h) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right m h) 2
  rw [mobiusDivisorSquareRootAbelMoment_sub_eq hm2 hle,
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular ((m + h) ^ 2),
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular (m ^ 2),
    sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq m, Nat.cast_add]
  have hphi := (chebyshevSqrtConvexPotential_sub_bounds hm2 hle).1
  rw [sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq m, Nat.cast_add, Nat.cast_pow] at hphi
  have hsec := (secularSqrtIncrementAction_sub_eulerMaclaurin_sandwich hm2 hle).2
  rw [eulerMaclaurinSqrtIncrementSecular_sq_eq (m + h),
    eulerMaclaurinSqrtIncrementSecular_sq_eq m,
    sqrt_nat_sq_eq (m + h), sqrt_nat_sq_eq m, Nat.cast_add] at hsec
  have hrem_nonneg : 0 ≤ (1 / 24 : ℝ) * (1 / ((m : ℝ) + (h : ℝ))) := by positivity
  linarith [show (1 / 3 : ℝ) * ((m : ℝ) + (h : ℝ)) ^ 3 - (1 / 2 : ℝ) * ((m : ℝ) + (h : ℝ)) -
        ((1 / 3 : ℝ) * (m : ℝ) ^ 3 - (1 / 2 : ℝ) * (m : ℝ)) =
      (h : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (h : ℝ) + (1 / 3 : ℝ) * (h : ℝ) ^ 2 - 1 / 2) by ring,
    show (1 / 24 : ℝ) * (1 / (m : ℝ) - 1 / ((m : ℝ) + (h : ℝ))) =
      (1 / 24 : ℝ) / (m : ℝ) - (1 / 24 : ℝ) * (1 / ((m : ℝ) + (h : ℝ))) by ring]

/-- **Zero-Remainder Backward Square-Grid Step Upper Bound for `mobiusDivisorSquareRootAbelMoment`
in Terms of `ψ(m^2) - m^2`:**
Because `secularSqrtIncrementAction (m^2) - secularSqrtIncrementAction ((m - h)^2) ≥ eulerMaclaurinSqrtIncrementSecular (m^2) - eulerMaclaurinSqrtIncrementSecular ((m - h)^2)`
with **zero Euler–Maclaurin remainder**, for all `2 ≤ m - h` and `1 ≤ h`:
`mobiusDivisorSquareRootAbelMoment (m^2) - mobiusDivisorSquareRootAbelMoment ((m - h)^2) ≤ h * (ψ(m^2) - m^2 + 2 * γ + m * h - (1 / 3) * h^2 + 1 / 2)`. -/
theorem mobiusDivisorSquareRootAbelMoment_backward_square_step_le
    {m h : ℕ} (hmh : 2 ≤ m - h) (_hh : 1 ≤ h) :
    mobiusDivisorSquareRootAbelMoment (m ^ 2) -
        mobiusDivisorSquareRootAbelMoment ((m - h) ^ 2) ≤
      (h : ℝ) * (Chebyshev.psi ((m : ℝ) ^ 2) - (m : ℝ) ^ 2 +
        2 * Real.eulerMascheroniConstant + (m : ℝ) * (h : ℝ) -
        (1 / 3 : ℝ) * (h : ℝ) ^ 2 + 1 / 2) := by
  have hmh_le : h ≤ m := by omega
  have hmh2 : 2 ≤ (m - h) ^ 2 := by nlinarith
  have hle : (m - h) ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (by omega) 2
  rw [mobiusDivisorSquareRootAbelMoment_sub_eq hmh2 hle,
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular (m ^ 2),
    chebyshevSqrtIncrementAction_eq_convexPotential_sub_secular ((m - h) ^ 2),
    sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m - h), Nat.cast_sub hmh_le]
  have hphi := (chebyshevSqrtConvexPotential_sub_bounds hmh2 hle).2
  rw [sqrt_nat_sq_eq m, sqrt_nat_sq_eq (m - h), Nat.cast_sub hmh_le, Nat.cast_pow] at hphi
  have hsec := (secularSqrtIncrementAction_sub_eulerMaclaurin_sandwich hmh2 hle).1
  rw [eulerMaclaurinSqrtIncrementSecular_sq_eq m,
    eulerMaclaurinSqrtIncrementSecular_sq_eq (m - h), Nat.cast_sub hmh_le] at hsec
  linarith [show (1 / 3 : ℝ) * (m : ℝ) ^ 3 - (1 / 2 : ℝ) * (m : ℝ) -
        ((1 / 3 : ℝ) * ((m : ℝ) - (h : ℝ)) ^ 3 - (1 / 2 : ℝ) * ((m : ℝ) - (h : ℝ))) =
      (h : ℝ) * ((m : ℝ) ^ 2 - (m : ℝ) * (h : ℝ) + (1 / 3 : ℝ) * (h : ℝ) ^ 2 - 1 / 2) by ring]

/-- **Three-Square Second-Difference Identity for the First-Cesàro Möbius–Divisor Dilation Sum:**
For all `m, h : ℕ` with `2 ≤ m - h`,
`Δ²_{sq, h} (∑_d mobiusDivisorCesaroDilationChannel (·) d) (m) = Δ²_{sq, h} chebyshevClassicalCesaroSum (m) + 4 * γ * h^2`. -/
theorem sum_mobiusDivisorCesaroDilationChannel_square_second_diff_eq
    {m h : ℕ} (hmh : 2 ≤ m - h) :
    (∑ d ∈ Finset.Icc 1 ((m - h) ^ 2 - 1),
        mobiusDivisorCesaroDilationChannel ((m - h) ^ 2) d) +
      (∑ d ∈ Finset.Icc 1 ((m + h) ^ 2 - 1),
        mobiusDivisorCesaroDilationChannel ((m + h) ^ 2) d) -
      2 * (∑ d ∈ Finset.Icc 1 (m ^ 2 - 1),
        mobiusDivisorCesaroDilationChannel (m ^ 2) d) =
      chebyshevClassicalCesaroSum ((m - h) ^ 2) +
        chebyshevClassicalCesaroSum ((m + h) ^ 2) -
        2 * chebyshevClassicalCesaroSum (m ^ 2) +
        4 * Real.eulerMascheroniConstant * (h : ℝ) ^ 2 := by
  have hm : 2 ≤ m := by omega
  have hmh_le : h ≤ m := by omega
  have hmh2 : 2 ≤ (m - h) ^ 2 := by nlinarith
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hadd2 : 2 ≤ (m + h) ^ 2 := by nlinarith
  have h1 := chebyshevClassicalCesaroSum_eq_sum_mobiusDivisorCesaroDilationChannel_sub hmh2
  have h2 := chebyshevClassicalCesaroSum_eq_sum_mobiusDivisorCesaroDilationChannel_sub hadd2
  have h3 := chebyshevClassicalCesaroSum_eq_sum_mobiusDivisorCesaroDilationChannel_sub hm2
  rw [Nat.cast_pow, Nat.cast_sub hmh_le] at h1
  rw [Nat.cast_pow, Nat.cast_add] at h2
  rw [Nat.cast_pow] at h3
  linarith

/-- **Consecutive-Square Tauberian Step Sandwich for the First-Cesàro Möbius–Divisor Dilation Sum:**
For all `m ≥ 3`, the forward difference of `∑_d mobiusDivisorCesaroDilationChannel (m^2) d` across
consecutive squares `[m^2, (m + 1)^2]` and `[(m - 1)^2, m^2]` sandwiches `ψ(m^2) - m^2`:
1. `(2 * m + 1) * (ψ(m^2) - m^2 + 2 * γ) - m * (2 * m + 1) ≤ (∑_d mobiusDivisorCesaroDilationChannel ((m + 1)^2) d) - (∑_d mobiusDivisorCesaroDilationChannel (m^2) d)`,
2. `(∑_d mobiusDivisorCesaroDilationChannel (m^2) d) - (∑_d mobiusDivisorCesaroDilationChannel ((m - 1)^2) d) ≤ (2 * m - 1) * (ψ(m^2) - m^2 + 2 * γ) + m * (2 * m - 1)`. -/
theorem sum_mobiusDivisorCesaroDilationChannel_consecutive_square_sandwich
    {m : ℕ} (hm : 3 ≤ m) :
    ((2 * (m : ℝ) + 1) * (Chebyshev.psi ((m : ℝ) ^ 2) - (m : ℝ) ^ 2 +
        2 * Real.eulerMascheroniConstant) - (m : ℝ) * (2 * (m : ℝ) + 1) ≤
      (∑ d ∈ Finset.Icc 1 ((m + 1) ^ 2 - 1),
          mobiusDivisorCesaroDilationChannel ((m + 1) ^ 2) d) -
        (∑ d ∈ Finset.Icc 1 (m ^ 2 - 1),
          mobiusDivisorCesaroDilationChannel (m ^ 2) d)) ∧
    ((∑ d ∈ Finset.Icc 1 (m ^ 2 - 1),
          mobiusDivisorCesaroDilationChannel (m ^ 2) d) -
        (∑ d ∈ Finset.Icc 1 ((m - 1) ^ 2 - 1),
          mobiusDivisorCesaroDilationChannel ((m - 1) ^ 2) d) ≤
      (2 * (m : ℝ) - 1) * (Chebyshev.psi ((m : ℝ) ^ 2) - (m : ℝ) ^ 2 +
        2 * Real.eulerMascheroniConstant) + (m : ℝ) * (2 * (m : ℝ) - 1)) := by
  have hm2_le : 2 ≤ m := by omega
  have hm1_le : 1 ≤ m := by omega
  have hm2 : 2 ≤ m ^ 2 := by nlinarith
  have hsucc2 : 2 ≤ (m + 1) ^ 2 := by nlinarith
  have hpred2 : 2 ≤ (m - 1) ^ 2 := by
    have : 2 ≤ m - 1 := by omega
    nlinarith
  have h1 := chebyshevClassicalCesaroSum_eq_sum_mobiusDivisorCesaroDilationChannel_sub hm2
  have h2 := chebyshevClassicalCesaroSum_eq_sum_mobiusDivisorCesaroDilationChannel_sub hsucc2
  have h3 := chebyshevClassicalCesaroSum_eq_sum_mobiusDivisorCesaroDilationChannel_sub hpred2
  rw [Nat.cast_pow] at h1
  rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h2
  rw [Nat.cast_pow, Nat.cast_sub hm1_le, Nat.cast_one] at h3
  have hfwd := chebyshevPsi_sq_sub_sq_le_succ_sq_sub_classicalCesaroSum hm2_le
  have hbwd := chebyshevPsi_sq_sub_sq_ge_sq_sub_pred_sq_classicalCesaroSum hm
  rw [Nat.cast_pow] at hfwd hbwd
  constructor <;> linarith

/-- **Exact Bridge Between `chebyshevRightSqrtRieszAction`, `chebyshevSqrtRieszAction`, and
`mobiusDivisorSquareRootAbelMoment`:**
For all `M ≥ 2`, the endpoint shift `chebyshevRightSqrtRieszAction M - chebyshevSqrtRieszAction M`
equals `mobiusDivisorSquareRootAbelMoment M - 2 * γ * (√M - 1) + (√2 - 1)` identically. -/
theorem chebyshevRightSqrtRieszAction_sub_chebyshevSqrtRieszAction_eq_mobiusDivisor
    {M : ℕ} (hM : 2 ≤ M) :
    chebyshevRightSqrtRieszAction M - chebyshevSqrtRieszAction M =
      mobiusDivisorSquareRootAbelMoment M -
        2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1) + (Real.sqrt 2 - 1) := by
  unfold chebyshevRightSqrtRieszAction
  rw [mobiusDivisorSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_add hM]
  ring

/-- **Exact Bridge Between `chebyshevTrapezoidalSqrtRieszAction`, `chebyshevSqrtRieszAction`, and
`mobiusDivisorSquareRootAbelMoment`:**
For all `M ≥ 2`,
`2 * (chebyshevTrapezoidalSqrtRieszAction M - chebyshevSqrtRieszAction M) = mobiusDivisorSquareRootAbelMoment M - 2 * γ * (√M - 1) + (√2 - 1)`. -/
theorem two_mul_chebyshevTrapezoidalSqrtRieszAction_sub_eq_mobiusDivisor
    {M : ℕ} (hM : 2 ≤ M) :
    2 * (chebyshevTrapezoidalSqrtRieszAction M - chebyshevSqrtRieszAction M) =
      mobiusDivisorSquareRootAbelMoment M -
        2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1) + (Real.sqrt 2 - 1) := by
  unfold chebyshevTrapezoidalSqrtRieszAction
  rw [mobiusDivisorSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_add hM]
  ring

/-- **Exact Bridge Between `chebyshevTrapezoidalSecondSqrtRieszAction`,
`chebyshevMidpointSecondSqrtRieszAction`, and `mobiusDivisorSquareRootAbelMoment`:**
For all `M ≥ 2`,
`2 * (chebyshevTrapezoidalSecondSqrtRieszAction M - chebyshevMidpointSecondSqrtRieszAction M) = mobiusDivisorSquareRootAbelMoment M - 2 * γ * (√M - 1) + (√2 - 1)`. -/
theorem two_mul_chebyshevTrapezoidalSecondSqrtRieszAction_sub_midpoint_eq_mobiusDivisor
    {M : ℕ} (hM : 2 ≤ M) :
    2 * (chebyshevTrapezoidalSecondSqrtRieszAction M -
        chebyshevMidpointSecondSqrtRieszAction M) =
      mobiusDivisorSquareRootAbelMoment M -
        2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1) + (Real.sqrt 2 - 1) := by
  rw [chebyshevTrapezoidalSecondSqrtRieszAction_eq_midpoint_add_half_increment M,
    mobiusDivisorSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_add hM]
  ring

/-! ## Section 5: Exact Piecewise-Linear Tent Decomposition of `mobiusClippedCesaroKernel` in
Terms of `moebiusPrefixSum` and `weightedMobiusLinearSum` -/

/-- On any complete quotient block `(q + 1) * d ≤ M`, the integer block length
`divisorDilationTriangularLength M d q = min (M - q * d) d` equals `d`. -/
theorem divisorDilationTriangularLength_eq_full
    {M d q : ℕ} (hfull : (q + 1) * d ≤ M) :
    divisorDilationTriangularLength M d q = d := by
  unfold divisorDilationTriangularLength
  have hprod : (q + 1) * d = q * d + d := by ring
  exact min_eq_right (by omega)

/-- On the terminal quotient band `M ≤ (q + 1) * d`, the integer block length
`divisorDilationTriangularLength M d q = min (M - q * d) d` equals `M - q * d`. -/
theorem divisorDilationTriangularLength_eq_terminal
    {M d q : ℕ} (hterminal : M ≤ (q + 1) * d) :
    divisorDilationTriangularLength M d q = M - q * d := by
  unfold divisorDilationTriangularLength
  have hprod : (q + 1) * d = q * d + d := by ring
  exact min_eq_left (by omega)

/-- **Mertens Prefix Sum:**
`moebiusPrefixSum N = ∑ d ∈ Icc 1 N, μ(d)`. -/
def moebiusPrefixSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- **Linear-Weighted Mertens Prefix Sum:**
`weightedMobiusLinearSum N = ∑ d ∈ Icc 1 N, μ(d) * d`. -/
def weightedMobiusLinearSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ)

/-- **Terminal-Band First-Cesàro Möbius Kernel:**
`mobiusTerminalClippedCesaroKernel M q = ∑ d ∈ Ioc (M / (q + 1)) ((M - 1) / q), μ(d) * (M - q * d)`. -/
def mobiusTerminalClippedCesaroKernel (M q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc (M / (q + 1)) ((M - 1) / q),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((M : ℝ) - (q : ℝ) * (d : ℝ))

private theorem div_succ_le_pred_div {M q : ℕ} (hq : 1 ≤ q) :
    M / (q + 1) ≤ (M - 1) / q := by
  let A := M / (q + 1)
  by_cases hA0 : A = 0
  · simp [A, hA0]
  · have hApos : 0 < A := Nat.pos_of_ne_zero hA0
    have hprod : (q + 1) * A ≤ M := by
      dsimp [A]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self M (q + 1)
    have hqA : q * A ≤ M - 1 := by
      have hlt : q * A < (q + 1) * A := by nlinarith
      omega
    exact (Nat.le_div_iff_mul_le (by omega : 0 < q)).2
      (by simpa [Nat.mul_comm] using hqA)

private theorem Icc_union_Ioc_eq_Icc {A B : ℕ} (hAB : A ≤ B) :
    Finset.Icc 1 A ∪ Finset.Ioc A B = Finset.Icc 1 B := by
  ext d
  simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro (hd | hd)
    · exact ⟨hd.1, hd.2.trans hAB⟩
    · exact ⟨Nat.one_le_iff_ne_zero.mpr ((Nat.zero_le A).trans_lt hd.1).ne', hd.2⟩
  · intro hdB
    by_cases hdA : d ≤ A
    · exact Or.inl ⟨hdB.1, hdA⟩
    · exact Or.inr ⟨lt_of_not_ge hdA, hdB.2⟩

private theorem disjoint_Icc_Ioc (A B : ℕ) :
    Disjoint (Finset.Icc 1 A) (Finset.Ioc A B) := by
  rw [Finset.disjoint_left]
  intro d hdA hdB
  simp only [Finset.mem_Icc] at hdA
  simp only [Finset.mem_Ioc] at hdB
  omega

/-- **Exact Complete/Terminal Split of `mobiusClippedCesaroKernel`:**
For every `q ≥ 1`, `mobiusClippedCesaroKernel M q` splits into the complete-block linear Mertens
sum `weightedMobiusLinearSum (M / (q + 1))` plus `mobiusTerminalClippedCesaroKernel M q`. -/
theorem mobiusClippedCesaroKernel_eq_full_add_terminal
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusClippedCesaroKernel M q =
      weightedMobiusLinearSum (M / (q + 1)) +
        mobiusTerminalClippedCesaroKernel M q := by
  let A := M / (q + 1)
  let B := (M - 1) / q
  have hAB : A ≤ B := div_succ_le_pred_div hq
  unfold mobiusClippedCesaroKernel weightedMobiusLinearSum mobiusTerminalClippedCesaroKernel
  change (∑ d ∈ Finset.Icc 1 B,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (divisorDilationTriangularLength M d q : ℝ)) = _
  rw [← Icc_union_Ioc_eq_Icc hAB, Finset.sum_union (disjoint_Icc_Ioc A B)]
  congr 1
  · apply Finset.sum_congr rfl
    intro d hdmem
    have hdI := Finset.mem_Icc.mp hdmem
    have hfull : (q + 1) * d ≤ M := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < q + 1)).mp hdI.2
    rw [divisorDilationTriangularLength_eq_full hfull]
  · apply Finset.sum_congr rfl
    intro d hdmem
    have hdI := Finset.mem_Ioc.mp hdmem
    have hqd : q * d ≤ M - 1 := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < q)).mp hdI.2
    have hqdM : q * d ≤ M := by omega
    have hterminal : M < (q + 1) * d := by
      have := Nat.lt_mul_of_div_lt hdI.1 (by omega : 0 < q + 1)
      simpa [Nat.mul_comm] using this
    rw [divisorDilationTriangularLength_eq_terminal hterminal.le,
      Nat.cast_sub hqdM, Nat.cast_mul]

/-- **Exact Prefix-Difference Decomposition of `mobiusTerminalClippedCesaroKernel`:**
Because `M - q * d` is affine linear in `d`, the terminal-band sum decomposes purely into
differences of `moebiusPrefixSum` and `weightedMobiusLinearSum` at `B = (M - 1) / q` and
`A = M / (q + 1)`. -/
theorem mobiusTerminalClippedCesaroKernel_eq_prefix_sub
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusTerminalClippedCesaroKernel M q =
      (M : ℝ) * (moebiusPrefixSum ((M - 1) / q) - moebiusPrefixSum (M / (q + 1))) -
        (q : ℝ) * (weightedMobiusLinearSum ((M - 1) / q) -
          weightedMobiusLinearSum (M / (q + 1))) := by
  let A := M / (q + 1)
  let B := (M - 1) / q
  have hAB : A ≤ B := div_succ_le_pred_div hq
  have hm_diff :
      moebiusPrefixSum B - moebiusPrefixSum A =
        ∑ d ∈ Finset.Ioc A B, ((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
    unfold moebiusPrefixSum
    rw [← Icc_union_Ioc_eq_Icc hAB, Finset.sum_union (disjoint_Icc_Ioc A B)]
    ring
  have hw_diff :
      weightedMobiusLinearSum B - weightedMobiusLinearSum A =
        ∑ d ∈ Finset.Ioc A B, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) := by
    unfold weightedMobiusLinearSum
    rw [← Icc_union_Ioc_eq_Icc hAB, Finset.sum_union (disjoint_Icc_Ioc A B)]
    ring
  change mobiusTerminalClippedCesaroKernel M q =
    (M : ℝ) * (moebiusPrefixSum B - moebiusPrefixSum A) -
      (q : ℝ) * (weightedMobiusLinearSum B - weightedMobiusLinearSum A)
  rw [hm_diff, hw_diff, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold mobiusTerminalClippedCesaroKernel
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- **Closed-Form Prefix-Sum Identity for `mobiusClippedCesaroKernel`:**
For every `q ≥ 1`, `mobiusClippedCesaroKernel M q` is an exact linear combination of
`weightedMobiusLinearSum` and `moebiusPrefixSum` evaluated at `M / (q + 1)` and `(M - 1) / q`:
`mobiusClippedCesaroKernel M q = (q + 1) * weightedMobiusLinearSum (M / (q + 1)) - q * weightedMobiusLinearSum ((M - 1) / q) + M * (moebiusPrefixSum ((M - 1) / q) - moebiusPrefixSum (M / (q + 1)))`. -/
theorem mobiusClippedCesaroKernel_eq_linear_and_moebiusPrefix
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusClippedCesaroKernel M q =
      ((q : ℝ) + 1) * weightedMobiusLinearSum (M / (q + 1)) -
        (q : ℝ) * weightedMobiusLinearSum ((M - 1) / q) +
        (M : ℝ) * (moebiusPrefixSum ((M - 1) / q) - moebiusPrefixSum (M / (q + 1))) := by
  rw [mobiusClippedCesaroKernel_eq_full_add_terminal hq,
    mobiusTerminalClippedCesaroKernel_eq_prefix_sub hq]
  ring

/-- **Exact Abel Identity Relating `weightedMobiusLinearSum` and `moebiusPrefixSum`:**
For every `N : ℕ`,
`weightedMobiusLinearSum N = (N + 1) * moebiusPrefixSum N - ∑ d ∈ Icc 1 N, moebiusPrefixSum d`. -/
theorem weightedMobiusLinearSum_eq_moebiusPrefixSum_abel (N : ℕ) :
    weightedMobiusLinearSum N =
      ((N : ℝ) + 1) * moebiusPrefixSum N -
        ∑ d ∈ Finset.Icc 1 N, moebiusPrefixSum d := by
  unfold weightedMobiusLinearSum
  have habel := HTGeometry.sum_mul_eq_partial_mul_diff_ring
    (fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
    (fun d : ℕ => (d : ℝ)) N
  rw [habel]
  change (∑ k ∈ Finset.Icc 1 N,
      moebiusPrefixSum k * ((k : ℝ) - ((k + 1 : ℕ) : ℝ))) +
    moebiusPrefixSum N * ((N + 1 : ℕ) : ℝ) = _
  have hsum :
      (∑ k ∈ Finset.Icc 1 N,
        moebiusPrefixSum k * ((k : ℝ) - ((k + 1 : ℕ) : ℝ))) =
      -(∑ d ∈ Finset.Icc 1 N, moebiusPrefixSum d) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  rw [hsum]
  push_cast
  ring

/-- **Zero-Extended Piecewise-Linear Integer Tent for First-Cesàro Dilation:**
`mobiusCesaroTentWeight M q d = min (M - q * d) d` on `1 ≤ d` and `q * d ≤ M - 1`, and `0` outside. -/
def mobiusCesaroTentWeight (M q d : ℕ) : ℝ :=
  if 1 ≤ d ∧ q * d ≤ M - 1 then
    (divisorDilationTriangularLength M d q : ℝ)
  else 0

/-- The first-Cesàro integer tent vanishes at `d = (M - 1) / q + 1`. -/
theorem mobiusCesaroTentWeight_boundary_zero
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusCesaroTentWeight M q (((M - 1) / q) + 1) = 0 := by
  rw [mobiusCesaroTentWeight, if_neg]
  intro h
  have hlt : M - 1 < (((M - 1) / q) + 1) * q := by
    rw [← Nat.div_lt_iff_lt_mul (by omega : 0 < q)]
    omega
  have : q * (((M - 1) / q) + 1) ≤ M - 1 := h.2
  rw [Nat.mul_comm] at this
  omega

/-- **Boundary-Free Mertens-Gradient Law for `mobiusClippedCesaroKernel`:**
For every `q ≥ 1`,
`mobiusClippedCesaroKernel M q = ∑ d ∈ Icc 1 ((M - 1) / q), moebiusPrefixSum d * (mobiusCesaroTentWeight M q d - mobiusCesaroTentWeight M q (d + 1))`. -/
theorem mobiusClippedCesaroKernel_eq_mertensGradient
    {M q : ℕ} (hq : 1 ≤ q) :
    mobiusClippedCesaroKernel M q =
      ∑ d ∈ Finset.Icc 1 ((M - 1) / q),
        moebiusPrefixSum d *
          (mobiusCesaroTentWeight M q d - mobiusCesaroTentWeight M q (d + 1)) := by
  have htent :
      mobiusClippedCesaroKernel M q =
        ∑ d ∈ Finset.Icc 1 ((M - 1) / q),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * mobiusCesaroTentWeight M q d := by
    unfold mobiusClippedCesaroKernel
    apply Finset.sum_congr rfl
    intro d hd
    have hdI := Finset.mem_Icc.mp hd
    have hqd : q * d ≤ M - 1 := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < q)).mp hdI.2
    rw [mobiusCesaroTentWeight, if_pos ⟨hdI.1, hqd⟩]
  rw [htent]
  have habel := HTGeometry.sum_mul_eq_partial_mul_diff_ring
    (fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
    (mobiusCesaroTentWeight M q) ((M - 1) / q)
  rw [habel, mobiusCesaroTentWeight_boundary_zero hq, mul_zero, add_zero]
  rfl

/-- On the complete-block region `(q + 1) * (d + 1) ≤ M`, the backward gradient of
`mobiusCesaroTentWeight` is **identically `-1`**. -/
theorem mobiusCesaroTentWeight_sub_succ_eq_neg_one_of_full
    {M q d : ℕ} (hd : 1 ≤ d)
    (hfull : (q + 1) * (d + 1) ≤ M) :
    mobiusCesaroTentWeight M q d - mobiusCesaroTentWeight M q (d + 1) = -1 := by
  have hqdsucc : q * (d + 1) ≤ M - 1 := by
    have hlt : q * (d + 1) < (q + 1) * (d + 1) :=
      Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
    omega
  have hqd : q * d ≤ M - 1 :=
    (Nat.mul_le_mul_left q (by omega : d ≤ d + 1)).trans hqdsucc
  have hfullD : (q + 1) * d ≤ M :=
    (Nat.mul_le_mul_left (q + 1) (by omega : d ≤ d + 1)).trans hfull
  rw [mobiusCesaroTentWeight, if_pos ⟨hd, hqd⟩,
    mobiusCesaroTentWeight, if_pos ⟨by omega, hqdsucc⟩,
    divisorDilationTriangularLength_eq_full hfullD,
    divisorDilationTriangularLength_eq_full hfull]
  push_cast
  ring

/-- Inside the terminal band `M ≤ (q + 1) * d` and `q * (d + 1) ≤ M - 1`, the backward gradient of
`mobiusCesaroTentWeight` is **identically `+q`**. -/
theorem mobiusCesaroTentWeight_sub_succ_eq_of_terminal
    {M q d : ℕ} (hd : 1 ≤ d)
    (hqdsucc : q * (d + 1) ≤ M - 1)
    (hterminal : M ≤ (q + 1) * d) :
    mobiusCesaroTentWeight M q d - mobiusCesaroTentWeight M q (d + 1) = (q : ℝ) := by
  have hqd : q * d ≤ M - 1 :=
    (Nat.mul_le_mul_left q (by omega : d ≤ d + 1)).trans hqdsucc
  have hterminalSucc : M ≤ (q + 1) * (d + 1) :=
    hterminal.trans (Nat.mul_le_mul_left (q + 1) (by omega))
  rw [mobiusCesaroTentWeight, if_pos ⟨hd, hqd⟩,
    mobiusCesaroTentWeight, if_pos ⟨by omega, hqdsucc⟩,
    divisorDilationTriangularLength_eq_terminal hterminal,
    divisorDilationTriangularLength_eq_terminal hterminalSucc,
    Nat.cast_sub (by omega : q * d ≤ M),
    Nat.cast_sub (by omega : q * (d + 1) ≤ M)]
  push_cast
  ring

end

end GaloisForLFunctions.RHTower
