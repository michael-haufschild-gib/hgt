import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.RHTower.DivisorSmoothSquareMaximum
import GaloisForLFunctions.RHTower.HomothetyEigenchannelsAndSecondCesaroDivisorBridge
import GaloisForLFunctions.RHTower.SuzukiCompletedOutgoingDilationBalance
import GaloisForLFunctions.RHTower.SuzukiEulerianOutgoingChargeRigidity

/-!
# Quasi-RH Abscissa Laws II: High-Dilation Tails, Small-Quotient Hyperbola Duality, and Monotone Convex Prime Potentials

This module connects five further sectors of the `RHTower` corpus to support unconditional proofs
of the quasi-RH strips `1/6 ≤ Re(ρ) ≤ 5/6` (`zetaZeroAbscissa ≤ 5/6`) and
`1/4 ≤ Re(ρ) ≤ 3/4` (`zetaZeroAbscissa ≤ 3/4`):

1. **Two-Sided Functional-Equation Strip Equivalences (`Section 1`):**
   Using `xi_one_sub` and `ZetaXiZeroCorrespondence`, `zetaZeroAbscissa ≤ 1/2 + α` (`0 ≤ α`) is
   globally equivalent to the symmetric two-sided strip `1/2 - α ≤ ρ.re ∧ ρ.re ≤ 1/2 + α` for
   all zeros of `xi` and for all nontrivial zeros of `riemannZeta`, yielding exact characterizations
   of `1/6 ≤ Re(ρ) ≤ 5/6` (`zetaZeroAbscissa ≤ 5/6`) and `1/4 ≤ Re(ρ) ≤ 3/4` (`zetaZeroAbscissa ≤ 3/4`).

2. **Unconditional `(3/5) √M` Dilation-Head Bound and High-Dilation Tail Strip Laws (`Section 2`):**
   From `DivisorSmoothSquareMaximum.divisorUnsignedDilationChannel_le_three_fifths_sqrt`, every
   signed dilation channel satisfies `|mobiusDivisorDilationChannel M d| ≤ (3/5) √M`
   unconditionally. Consequently, the dilation head `mobiusDivisorDilationHead M ⌊M^φ⌋₊ / M` is
   unconditionally bounded by `(3/5) M^(φ - 1/2)`:
   - up to `D = ⌊M^(5/6)⌋₊`, the dilation head is unconditionally `≤ (3/5) M^(1/3)` (already inside
     the `5/6` strip budget);
   - up to `D = ⌊M^(3/4)⌋₊`, the dilation head is unconditionally `≤ (3/5) M^(1/4)` (already inside
     the `3/4` strip budget);
   - up to `D = ⌊M^(1/2)⌋₊`, the dilation head is unconditionally `≤ 3/5` (already inside the RH
     budget).
   Thus any one-sided upper or lower bound of exponent `c ≥ φ - 1/2` on the complementary
   **high-dilation tail** `mobiusDivisorDilationTail M ⌊M^φ⌋₊ / M` unconditionally forces
   `zetaZeroAbscissa ≤ 1/2 + c`, and at `φ = 1/2` yields exact `sInf` exponent laws.

3. **Exact Dirichlet Hyperbola Duality on the High-Dilation Tail (`Section 3`):**
   Transposing the truncated hyperbola `d ≥ D + 1`, `d * q ≤ M - 1` proves that
   `mobiusDivisorDilationTail M D` is supported exclusively on the **small-quotient window**
   `1 ≤ q ≤ (M - 1) / (D + 1)`:
   `mobiusDivisorDilationTail M D = ∑ q ∈ Icc 1 ((M - 1) / (D + 1)), primeFreeDivisorDefect q * mobiusHighDilationClippedAbelKernel M D q`.
   For the `5/6` strip (`D = ⌊M^(5/6)⌋₊`), this compresses the active quotient range to `q ≤ M^(1/6)`;
   for the `3/4` strip (`D = ⌊M^(3/4)⌋₊`), it compresses the active quotient range to `q ≤ M^(1/4)`.

4. **Outgoing Charge, Monotone Convex Potential (`chebyshevSqrtConvexPotential`),
   `chebyshevSqrtIncrementAction`, and SP-E Quarter-Dilation Balance Abscissa Laws (`Section 4`):**
   Connecting `HomothetyEigenchannelsAndSecondCesaroDivisorBridge`,
   `MobiusDivisorCesaroAndSquareGridSqrtRieszBridge`, `SuzukiCompletedOutgoingDilationBalance`, and
   `SuzukiEulerianOutgoingChargeRigidity` to `zetaZeroAbscissa` establishes one-sided strip laws,
   exact `sInf` exponent laws, and `5/6` & `3/4` strip criteria for `chebyshevSqrtIncrementAction`,
   `unitRieszCoherentCompletedOutgoingCharge`, the monotone square-root-convex prime potential
   defect `(chebyshevSqrtConvexPotential M - M √M / 3) / M`, the cumulative SP-E quarter-dilation
   balance, and `suzukiEulerianCompletedOutgoingDiscrepancy`.
-/

open Complex Real Set Filter Topology Finset
open scoped BigOperators ArithmeticFunction
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Section 1: Two-Sided Functional-Equation Strip Equivalences for `zetaZeroAbscissa`
(`1/6 ≤ Re(ρ) ≤ 5/6` and `1/4 ≤ Re(ρ) ≤ 3/4`) -/

/-- By the functional equation `xi (1 - s) = xi s`, every zero of `xi` lies in the symmetric strip
`1 - zetaZeroAbscissa ≤ ρ.re ∧ ρ.re ≤ zetaZeroAbscissa`. -/
theorem xi_zero_re_mem_zetaZeroAbscissa_strip {ρ : ℂ} (hρ : xi ρ = 0) :
    1 - zetaZeroAbscissa ≤ ρ.re ∧ ρ.re ≤ zetaZeroAbscissa := by
  refine ⟨?_, xi_zero_re_le_zetaZeroAbscissa hρ⟩
  have h1 : xi (1 - ρ) = 0 := by rw [xi_one_sub, hρ]
  have hle := xi_zero_re_le_zetaZeroAbscissa h1
  rw [Complex.sub_re, Complex.one_re] at hle
  linarith

/-- Every nontrivial zero of `riemannZeta` lies in the symmetric strip
`1 - zetaZeroAbscissa ≤ ρ.re ∧ ρ.re ≤ zetaZeroAbscissa`. -/
theorem nontrivial_zeta_zero_re_mem_zetaZeroAbscissa_strip {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (hnt : ∀ n : ℕ, ρ ≠ -(2 * ((n : ℂ) + 1))) :
    1 - zetaZeroAbscissa ≤ ρ.re ∧ ρ.re ≤ zetaZeroAbscissa :=
  xi_zero_re_mem_zetaZeroAbscissa_strip
    (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr ⟨hz, hnt⟩)

/-- For any `0 ≤ α`, `zetaZeroAbscissa ≤ 1/2 + α` is equivalent to every zero of `xi` lying in the
symmetric strip `1/2 - α ≤ ρ.re ∧ ρ.re ≤ 1/2 + α`. -/
theorem zetaZeroAbscissa_le_iff_forall_xi_zero_re_mem_strip {α : ℝ} (hα : 0 ≤ α) :
    zetaZeroAbscissa ≤ 1 / 2 + α ↔
      ∀ ρ : ℂ, xi ρ = 0 → 1 / 2 - α ≤ ρ.re ∧ ρ.re ≤ 1 / 2 + α := by
  rw [← xiZeroHalfPlaneBound_iff_zetaZeroAbscissa_le hα]
  constructor
  · intro hXi ρ hρ
    have hupper : ρ.re ≤ 1 / 2 + α := hXi ρ hρ
    have h1 : xi (1 - ρ) = 0 := by rw [xi_one_sub, hρ]
    have hlower := hXi (1 - ρ) h1
    rw [Complex.sub_re, Complex.one_re] at hlower
    exact ⟨by linarith, hupper⟩
  · intro h ρ hρ
    exact (h ρ hρ).2

/-- For any `0 ≤ α`, `zetaZeroAbscissa ≤ 1/2 + α` is equivalent to every nontrivial zero of
`riemannZeta` lying in the symmetric strip `1/2 - α ≤ ρ.re ∧ ρ.re ≤ 1/2 + α`. -/
theorem zetaZeroAbscissa_le_iff_forall_nontrivial_zeta_zero_re_mem_strip {α : ℝ} (hα : 0 ≤ α) :
    zetaZeroAbscissa ≤ 1 / 2 + α ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → (∀ n : ℕ, ρ ≠ -(2 * ((n : ℂ) + 1))) →
        1 / 2 - α ≤ ρ.re ∧ ρ.re ≤ 1 / 2 + α := by
  rw [zetaZeroAbscissa_le_iff_forall_xi_zero_re_mem_strip hα]
  constructor
  · intro h ρ hz hnt
    exact h ρ (xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mpr ⟨hz, hnt⟩)
  · intro h ρ hρ
    obtain ⟨hz, hnt⟩ := xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial.mp hρ
    exact h ρ hz hnt

/-- Exact equivalence for the `5/6` quasi-RH target strip `1/6 ≤ Re(ρ) ≤ 5/6` on `xi` zeros. -/
theorem zetaZeroAbscissa_le_five_sixths_iff_xi_zero_mem_strip :
    zetaZeroAbscissa ≤ 5 / 6 ↔
      ∀ ρ : ℂ, xi ρ = 0 → 1 / 6 ≤ ρ.re ∧ ρ.re ≤ 5 / 6 := by
  have h := zetaZeroAbscissa_le_iff_forall_xi_zero_re_mem_strip (α := (1 / 3 : ℝ)) (by norm_num)
  norm_num at h
  exact h

/-- Exact equivalence for the `5/6` quasi-RH target strip `1/6 ≤ Re(ρ) ≤ 5/6` on nontrivial
`riemannZeta` zeros. -/
theorem zetaZeroAbscissa_le_five_sixths_iff_nontrivial_zeta_zero_mem_strip :
    zetaZeroAbscissa ≤ 5 / 6 ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → (∀ n : ℕ, ρ ≠ -(2 * ((n : ℂ) + 1))) →
        1 / 6 ≤ ρ.re ∧ ρ.re ≤ 5 / 6 := by
  have h := zetaZeroAbscissa_le_iff_forall_nontrivial_zeta_zero_re_mem_strip
    (α := (1 / 3 : ℝ)) (by norm_num)
  norm_num at h
  exact h

/-- Exact equivalence for the `3/4` quasi-RH target strip `1/4 ≤ Re(ρ) ≤ 3/4` on `xi` zeros. -/
theorem zetaZeroAbscissa_le_three_quarters_iff_xi_zero_mem_strip :
    zetaZeroAbscissa ≤ 3 / 4 ↔
      ∀ ρ : ℂ, xi ρ = 0 → 1 / 4 ≤ ρ.re ∧ ρ.re ≤ 3 / 4 := by
  have h := zetaZeroAbscissa_le_iff_forall_xi_zero_re_mem_strip (α := (1 / 4 : ℝ)) (by norm_num)
  norm_num at h
  exact h

/-- Exact equivalence for the `3/4` quasi-RH target strip `1/4 ≤ Re(ρ) ≤ 3/4` on nontrivial
`riemannZeta` zeros. -/
theorem zetaZeroAbscissa_le_three_quarters_iff_nontrivial_zeta_zero_mem_strip :
    zetaZeroAbscissa ≤ 3 / 4 ↔
      ∀ ρ : ℂ, riemannZeta ρ = 0 → (∀ n : ℕ, ρ ≠ -(2 * ((n : ℂ) + 1))) →
        1 / 4 ≤ ρ.re ∧ ρ.re ≤ 3 / 4 := by
  have h := zetaZeroAbscissa_le_iff_forall_nontrivial_zeta_zero_re_mem_strip
    (α := (1 / 4 : ℝ)) (by norm_num)
  norm_num at h
  exact h

/-! ## Section 2: Unconditional `(3/5) √M` Dilation-Head Bound and High-Dilation Tail Strip Laws -/

/-- Every signed Möbius–divisor dilation channel has amplitude at most `(3/5) √M`. -/
theorem abs_mobiusDivisorDilationChannel_le_three_fifths_sqrt (M d : ℕ) :
    |mobiusDivisorDilationChannel M d| ≤ (3 / 5 : ℝ) * Real.sqrt M := by
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned, abs_mul,
    abs_of_nonneg (divisorUnsignedDilationChannel_nonneg M d)]
  have hm : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  calc
    |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * divisorUnsignedDilationChannel M d
        ≤ 1 * divisorUnsignedDilationChannel M d :=
      mul_le_mul_of_nonneg_right hm (divisorUnsignedDilationChannel_nonneg M d)
    _ ≤ (3 / 5 : ℝ) * Real.sqrt M := by
      simpa using divisorUnsignedDilationChannel_le_three_fifths_sqrt M d

/-- Above the physical support `d > M - 1`, the dilation channel vanishes identically. -/
theorem mobiusDivisorDilationChannel_eq_zero_of_lt {M d : ℕ} (hd : M - 1 < d) :
    mobiusDivisorDilationChannel M d = 0 := by
  unfold mobiusDivisorDilationChannel
  rw [Finset.Icc_eq_empty_of_lt hd, Finset.sum_empty, mul_zero]

/-- Prefix sum of signed Möbius–divisor dilation channels up to dilation cutoff `D`. -/
def mobiusDivisorDilationHead (M D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, mobiusDivisorDilationChannel M d

/-- High-dilation tail of signed Möbius–divisor dilation channels strictly above cutoff `D`. -/
def mobiusDivisorDilationTail (M D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (D + 1) (M - 1), mobiusDivisorDilationChannel M d

/-- Exact decomposition of `mobiusDivisorSquareRootAbelMoment M` into `mobiusDivisorDilationHead M D`
and `mobiusDivisorDilationTail M D` at any cutoff `D : ℕ`. -/
theorem mobiusDivisorSquareRootAbelMoment_eq_dilationHead_add_dilationTail (M D : ℕ) :
    mobiusDivisorSquareRootAbelMoment M =
      mobiusDivisorDilationHead M D + mobiusDivisorDilationTail M D := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_sum_dilationChannels]
  unfold mobiusDivisorDilationHead mobiusDivisorDilationTail
  rcases le_or_gt D (M - 1) with hDM | hMD
  · have hsplit : Finset.Icc 1 (M - 1) = Finset.Icc 1 D ∪ Finset.Icc (D + 1) (M - 1) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.Icc 1 D) (Finset.Icc (D + 1) (M - 1)) := by
      rw [Finset.disjoint_left]
      intro d hd1 hd2
      simp only [Finset.mem_Icc] at hd1 hd2
      omega
    rw [hsplit, Finset.sum_union hdisj]
  · rw [Finset.Icc_eq_empty_of_lt (by omega : M - 1 < D + 1), Finset.sum_empty, add_zero]
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hMD.le) ?_
    intro d hd hnot
    simp only [Finset.mem_Icc] at hd hnot
    exact mobiusDivisorDilationChannel_eq_zero_of_lt (by omega)

/-- Unconditional uniform bound on the dilation head up to any cutoff `D : ℕ`:
`|mobiusDivisorDilationHead M D| ≤ (3/5) D √M`. -/
theorem abs_mobiusDivisorDilationHead_le (M D : ℕ) :
    |mobiusDivisorDilationHead M D| ≤ (3 / 5 : ℝ) * (D : ℝ) * Real.sqrt M := by
  unfold mobiusDivisorDilationHead
  calc
    |∑ d ∈ Finset.Icc 1 D, mobiusDivisorDilationChannel M d|
        ≤ ∑ d ∈ Finset.Icc 1 D, |mobiusDivisorDilationChannel M d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 D, (3 / 5 : ℝ) * Real.sqrt M :=
      Finset.sum_le_sum fun d _ => abs_mobiusDivisorDilationChannel_le_three_fifths_sqrt M d
    _ = (3 / 5 : ℝ) * (D : ℝ) * Real.sqrt M := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

/-- Unconditional aperture-normalized bound on the dilation head at cutoff `D = ⌊M^φ⌋₊`:
`|mobiusDivisorDilationHead M ⌊M^φ⌋₊ / M| ≤ (3/5) * M^(φ - 1/2)`. -/
theorem abs_mobiusDivisorDilationHead_natFloor_rpow_div_le
    {M : ℕ} (hM : 1 ≤ M) (φ : ℝ) :
    |mobiusDivisorDilationHead M ⌊(M : ℝ) ^ φ⌋₊ / M| ≤
      (3 / 5 : ℝ) * (M : ℝ) ^ (φ - 1 / 2) := by
  have hM0 : (0 : ℝ) < M := by positivity
  have hfloor : ((⌊(M : ℝ) ^ φ⌋₊ : ℕ) : ℝ) ≤ (M : ℝ) ^ φ :=
    Nat.floor_le (Real.rpow_nonneg hM0.le φ)
  rw [abs_div, abs_of_pos hM0, div_le_iff₀ hM0]
  calc
    |mobiusDivisorDilationHead M ⌊(M : ℝ) ^ φ⌋₊|
        ≤ (3 / 5 : ℝ) * ((⌊(M : ℝ) ^ φ⌋₊ : ℕ) : ℝ) * Real.sqrt M :=
      abs_mobiusDivisorDilationHead_le M _
    _ ≤ (3 / 5 : ℝ) * (M : ℝ) ^ φ * Real.sqrt M := by
      gcongr
    _ = (3 / 5 : ℝ) * (M : ℝ) ^ (φ - 1 / 2) * M := by
      rw [Real.sqrt_eq_rpow, mul_assoc, mul_assoc]
      congr 1
      rw [← Real.rpow_add hM0, ← Real.rpow_add_one hM0.ne']
      congr 1
      ring

/-- Up to `D = ⌊M^(5/6)⌋₊`, the dilation head is unconditionally `O(M^(1/3))` (within the `5/6`
quasi-RH strip budget). -/
theorem abs_mobiusDivisorDilationHead_five_sixths_div_le {M : ℕ} (hM : 1 ≤ M) :
    |mobiusDivisorDilationHead M ⌊(M : ℝ) ^ (5 / 6 : ℝ)⌋₊ / M| ≤
      (3 / 5 : ℝ) * (M : ℝ) ^ (1 / 3 : ℝ) := by
  have h := abs_mobiusDivisorDilationHead_natFloor_rpow_div_le hM (5 / 6 : ℝ)
  have hexp : (5 / 6 : ℝ) - 1 / 2 = 1 / 3 := by ring
  rwa [hexp] at h

/-- Up to `D = ⌊M^(3/4)⌋₊`, the dilation head is unconditionally `O(M^(1/4))` (within the `3/4`
quasi-RH strip budget). -/
theorem abs_mobiusDivisorDilationHead_three_quarters_div_le {M : ℕ} (hM : 1 ≤ M) :
    |mobiusDivisorDilationHead M ⌊(M : ℝ) ^ (3 / 4 : ℝ)⌋₊ / M| ≤
      (3 / 5 : ℝ) * (M : ℝ) ^ (1 / 4 : ℝ) := by
  have h := abs_mobiusDivisorDilationHead_natFloor_rpow_div_le hM (3 / 4 : ℝ)
  have hexp : (3 / 4 : ℝ) - 1 / 2 = 1 / 4 := by ring
  rwa [hexp] at h

/-- Up to `D = ⌊M^(1/2)⌋₊`, the dilation head is unconditionally bounded by `3/5` (within the RH
budget). -/
theorem abs_mobiusDivisorDilationHead_half_div_le {M : ℕ} (hM : 1 ≤ M) :
    |mobiusDivisorDilationHead M ⌊(M : ℝ) ^ (1 / 2 : ℝ)⌋₊ / M| ≤ 3 / 5 := by
  have h := abs_mobiusDivisorDilationHead_natFloor_rpow_div_le hM (1 / 2 : ℝ)
  have hexp : (1 / 2 : ℝ) - 1 / 2 = 0 := by ring
  rw [hexp, Real.rpow_zero, mul_one] at h
  exact h

/-- **General High-Dilation Tail One-Sided Upper Strip Law:**
For any cutoff exponent `φ ≥ 1/2` and any `c ≥ φ - 1/2`, a one-sided upper bound of exponent `c`
on `mobiusDivisorDilationTail M ⌊M^φ⌋₊ / M` unconditionally forces `zetaZeroAbscissa ≤ 1/2 + c`. -/
theorem zetaZeroAbscissa_le_of_mobiusDivisorDilationTail_le_rpow
    {φ C c : ℝ} (hφ : 1 / 2 ≤ φ) (hφc : φ - 1 / 2 ≤ c) (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorDilationTail M ⌊(M : ℝ) ^ φ⌋₊ / M ≤ C + C * (M : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + c := by
  have hc0 : 0 ≤ c := by linarith
  have h := zetaZeroAbscissa_le_of_mobiusDivisorSquareRootAbel_le_rpow
    (C := C + 3 / 5) (c := c) (by positivity) fun M hM2 => by
      have hM1 : 1 ≤ M := by omega
      have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
      have hhead := (le_abs_self _).trans
        (abs_mobiusDivisorDilationHead_natFloor_rpow_div_le hM1 φ)
      have hpow : (M : ℝ) ^ (φ - 1 / 2) ≤ (M : ℝ) ^ c :=
        Real.rpow_le_rpow_of_exponent_le hMone hφc
      have htail := hM M hM2
      rw [mobiusDivisorSquareRootAbelMoment_eq_dilationHead_add_dilationTail M ⌊(M : ℝ) ^ φ⌋₊,
        add_div]
      nlinarith
  rwa [max_eq_right hc0] at h

/-- **General High-Dilation Tail One-Sided Lower Strip Law:**
For any cutoff exponent `φ ≥ 1/2` and any `c ≥ φ - 1/2`, a one-sided lower bound of exponent `c`
on `mobiusDivisorDilationTail M ⌊M^φ⌋₊ / M` unconditionally forces `zetaZeroAbscissa ≤ 1/2 + c`. -/
theorem zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorDilationTail
    {φ C c : ℝ} (hφ : 1 / 2 ≤ φ) (hφc : φ - 1 / 2 ≤ c) (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M →
      -(C + C * (M : ℝ) ^ c) ≤ mobiusDivisorDilationTail M ⌊(M : ℝ) ^ φ⌋₊ / M) :
    zetaZeroAbscissa ≤ 1 / 2 + c := by
  have hc0 : 0 ≤ c := by linarith
  have h := zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel
    (C := C + 3 / 5) (c := c) (by positivity) fun M hM2 => by
      have hM1 : 1 ≤ M := by omega
      have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
      have hhead := (abs_le.mp
        (abs_mobiusDivisorDilationHead_natFloor_rpow_div_le hM1 φ)).1
      have hpow : (M : ℝ) ^ (φ - 1 / 2) ≤ (M : ℝ) ^ c :=
        Real.rpow_le_rpow_of_exponent_le hMone hφc
      have htail := hM M hM2
      rw [mobiusDivisorSquareRootAbelMoment_eq_dilationHead_add_dilationTail M ⌊(M : ℝ) ^ φ⌋₊,
        add_div]
      nlinarith
  rwa [max_eq_right hc0] at h

/-- **High-Dilation Tail Criterion for `1/6 ≤ Re(ρ) ≤ 5/6` (One-Sided Upper):**
Bounding `mobiusDivisorDilationTail M ⌊M^(5/6)⌋₊ / M` from above by `C + C * M^(1/3)`
unconditionally forces every zero of `xi` into `1/6 ≤ Re(ρ) ≤ 5/6`. -/
theorem xi_zero_mem_five_sixths_strip_of_mobiusDivisorDilationTail_le
    {C : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorDilationTail M ⌊(M : ℝ) ^ (5 / 6 : ℝ)⌋₊ / M ≤
        C + C * (M : ℝ) ^ (1 / 3 : ℝ)) :
    ∀ ρ : ℂ, xi ρ = 0 → 1 / 6 ≤ ρ.re ∧ ρ.re ≤ 5 / 6 := by
  rw [← zetaZeroAbscissa_le_five_sixths_iff_xi_zero_mem_strip]
  have h := zetaZeroAbscissa_le_of_mobiusDivisorDilationTail_le_rpow
    (φ := 5 / 6) (c := 1 / 3) (by norm_num) (by norm_num) hC0 hM
  linarith

/-- **High-Dilation Tail Criterion for `1/6 ≤ Re(ρ) ≤ 5/6` (One-Sided Lower):**
Bounding `mobiusDivisorDilationTail M ⌊M^(5/6)⌋₊ / M` from below by `-(C + C * M^(1/3))`
unconditionally forces every zero of `xi` into `1/6 ≤ Re(ρ) ≤ 5/6`. -/
theorem xi_zero_mem_five_sixths_strip_of_neg_le_mobiusDivisorDilationTail
    {C : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M →
      -(C + C * (M : ℝ) ^ (1 / 3 : ℝ)) ≤
        mobiusDivisorDilationTail M ⌊(M : ℝ) ^ (5 / 6 : ℝ)⌋₊ / M) :
    ∀ ρ : ℂ, xi ρ = 0 → 1 / 6 ≤ ρ.re ∧ ρ.re ≤ 5 / 6 := by
  rw [← zetaZeroAbscissa_le_five_sixths_iff_xi_zero_mem_strip]
  have h := zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorDilationTail
    (φ := 5 / 6) (c := 1 / 3) (by norm_num) (by norm_num) hC0 hM
  linarith

/-- **High-Dilation Tail Criterion for `1/4 ≤ Re(ρ) ≤ 3/4` (One-Sided Upper):**
Bounding `mobiusDivisorDilationTail M ⌊M^(3/4)⌋₊ / M` from above by `C + C * M^(1/4)`
unconditionally forces every zero of `xi` into `1/4 ≤ Re(ρ) ≤ 3/4`. -/
theorem xi_zero_mem_three_quarters_strip_of_mobiusDivisorDilationTail_le
    {C : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorDilationTail M ⌊(M : ℝ) ^ (3 / 4 : ℝ)⌋₊ / M ≤
        C + C * (M : ℝ) ^ (1 / 4 : ℝ)) :
    ∀ ρ : ℂ, xi ρ = 0 → 1 / 4 ≤ ρ.re ∧ ρ.re ≤ 3 / 4 := by
  rw [← zetaZeroAbscissa_le_three_quarters_iff_xi_zero_mem_strip]
  have h := zetaZeroAbscissa_le_of_mobiusDivisorDilationTail_le_rpow
    (φ := 3 / 4) (c := 1 / 4) (by norm_num) (by norm_num) hC0 hM
  linarith

/-- **High-Dilation Tail Criterion for `1/4 ≤ Re(ρ) ≤ 3/4` (One-Sided Lower):**
Bounding `mobiusDivisorDilationTail M ⌊M^(3/4)⌋₊ / M` from below by `-(C + C * M^(1/4))`
unconditionally forces every zero of `xi` into `1/4 ≤ Re(ρ) ≤ 3/4`. -/
theorem xi_zero_mem_three_quarters_strip_of_neg_le_mobiusDivisorDilationTail
    {C : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M →
      -(C + C * (M : ℝ) ^ (1 / 4 : ℝ)) ≤
        mobiusDivisorDilationTail M ⌊(M : ℝ) ^ (3 / 4 : ℝ)⌋₊ / M) :
    ∀ ρ : ℂ, xi ρ = 0 → 1 / 4 ≤ ρ.re ∧ ρ.re ≤ 3 / 4 := by
  rw [← zetaZeroAbscissa_le_three_quarters_iff_xi_zero_mem_strip]
  have h := zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorDilationTail
    (φ := 3 / 4) (c := 1 / 4) (by norm_num) (by norm_num) hC0 hM
  linarith

/-- Unconditional subpower bound on the square-root high-dilation tail
`mobiusDivisorDilationTail M ⌊M^(1/2)⌋₊ / M` at `zetaZeroAbscissa`. -/
theorem exists_mobiusDivisorDilationTail_half_subpower_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |mobiusDivisorDilationTail M ⌊(M : ℝ) ^ (1 / 2 : ℝ)⌋₊ / M| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
  refine ⟨C + 3 / 5, by positivity, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := by omega
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hpow1 : 1 ≤ (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) :=
    Real.one_le_rpow hMone (by linarith [half_le_zetaZeroAbscissa])
  have hhead := abs_mobiusDivisorDilationHead_half_div_le hM1
  have htot := hC M hM
  have heq : mobiusDivisorDilationTail M ⌊(M : ℝ) ^ (1 / 2 : ℝ)⌋₊ / M =
      mobiusDivisorSquareRootAbelMoment M / M -
        mobiusDivisorDilationHead M ⌊(M : ℝ) ^ (1 / 2 : ℝ)⌋₊ / M := by
    rw [mobiusDivisorSquareRootAbelMoment_eq_dilationHead_add_dilationTail M
      ⌊(M : ℝ) ^ (1 / 2 : ℝ)⌋₊]
    ring
  rw [heq]
  refine (abs_sub _ _).trans ?_
  nlinarith

/-- **Exact One-Sided Upper Exponent Law for the Square-Root High-Dilation Tail:**
`zetaZeroAbscissa` is `1/2` plus the infimum of upper growth exponents `c ≥ 0` of
`mobiusDivisorDilationTail M ⌊M^(1/2)⌋₊ / M`. -/
theorem zetaZeroAbscissa_eq_half_add_sInf_mobiusDivisorDilationTail_half_upper_exponents :
    zetaZeroAbscissa = 1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      mobiusDivisorDilationTail M ⌊(M : ℝ) ^ (1 / 2 : ℝ)⌋₊ / M ≤ C * (M : ℝ) ^ c} := by
  set S := {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
    mobiusDivisorDilationTail M ⌊(M : ℝ) ^ (1 / 2 : ℝ)⌋₊ / M ≤ C * (M : ℝ) ^ c}
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa - 1 / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorDilationTail_half_subpower_zetaZeroAbscissa ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0,
      fun M hM => (le_abs_self _).trans (hC M hM)⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨0, fun c hc => hc.1⟩
  refine le_antisymm ?_ ?_
  · have hle : zetaZeroAbscissa - 1 / 2 ≤ sInf S := by
      refine le_csInf hne fun c hc => ?_
      obtain ⟨hc0, C, hC0, hC⟩ := hc
      have h := zetaZeroAbscissa_le_of_mobiusDivisorDilationTail_le_rpow
        (φ := 1 / 2) le_rfl (by linarith) hC0
        (fun M hM => (hC M hM).trans (le_add_of_nonneg_left hC0))
      linarith
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hle := csInf_le hbdd (hmem ε hε)
    linarith

/-- **Exact One-Sided Lower Exponent Law for the Square-Root High-Dilation Tail:**
`zetaZeroAbscissa` is `1/2` plus the infimum of lower growth exponents `c ≥ 0` of
`mobiusDivisorDilationTail M ⌊M^(1/2)⌋₊ / M`. -/
theorem zetaZeroAbscissa_eq_half_add_sInf_mobiusDivisorDilationTail_half_lower_exponents :
    zetaZeroAbscissa = 1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      -(C * (M : ℝ) ^ c) ≤ mobiusDivisorDilationTail M ⌊(M : ℝ) ^ (1 / 2 : ℝ)⌋₊ / M} := by
  set S := {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
    -(C * (M : ℝ) ^ c) ≤ mobiusDivisorDilationTail M ⌊(M : ℝ) ^ (1 / 2 : ℝ)⌋₊ / M}
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa - 1 / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorDilationTail_half_subpower_zetaZeroAbscissa ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0,
      fun M hM => (abs_le.mp (hC M hM)).1⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨0, fun c hc => hc.1⟩
  refine le_antisymm ?_ ?_
  · have hle : zetaZeroAbscissa - 1 / 2 ≤ sInf S := by
      refine le_csInf hne fun c hc => ?_
      obtain ⟨hc0, C, hC0, hC⟩ := hc
      have h := zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorDilationTail
        (φ := 1 / 2) le_rfl (by linarith) hC0
        (fun M hM => (neg_le_neg (le_add_of_nonneg_left hC0)).trans (hC M hM))
      linarith
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hle := csInf_le hbdd (hmem ε hε)
    linarith

/-! ## Section 3: Exact Dirichlet Hyperbola Duality on the High-Dilation Tail
(`mobiusDivisorDilationTail` ↔ Small-Quotient Sum `q ≤ (M - 1) / (D + 1)`) -/

/-- Truncated hyperbola Fubini law on `d ≥ D + 1`, `q ≥ 1`, `d * q ≤ N`: transposing the summation
order restricts `q` to the small-quotient window `1 ≤ q ≤ N / (D + 1)`. -/
theorem sum_hyperbola_dilationTail_swap_real (N D : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ Finset.Icc (D + 1) N, ∑ q ∈ Finset.Icc 1 (N / d), F d q) =
      ∑ q ∈ Finset.Icc 1 (N / (D + 1)), ∑ d ∈ Finset.Icc (D + 1) (N / q), F d q :=
  sum_hyperbola_tail_swap_real N (D + 1) (fun q d => F d q) (Nat.succ_pos D)

/-- High-dilation Möbius aggregation of clipped square-root block weights on quotient cell `q`
for `d ∈ Icc (D + 1) ((M - 1) / q)`. -/
def mobiusHighDilationClippedAbelKernel (M D q : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (D + 1) ((M - 1) / q),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ) * divisorDilationClippedAbelWeight M d q

/-- **Exact Small-Quotient Hyperbola Duality for `mobiusDivisorDilationTail`:**
For every aperture `M` and dilation cutoff `D`, the high-dilation tail `mobiusDivisorDilationTail M D`
equals the pairing of `primeFreeDivisorDefect q` with `mobiusHighDilationClippedAbelKernel M D q`
over the complementary small-quotient window `1 ≤ q ≤ (M - 1) / (D + 1)`. -/
theorem mobiusDivisorDilationTail_eq_smallQuotient_highDilationKernel (M D : ℕ) :
    mobiusDivisorDilationTail M D =
      ∑ q ∈ Finset.Icc 1 ((M - 1) / (D + 1)),
        primeFreeDivisorDefect q * mobiusHighDilationClippedAbelKernel M D q := by
  unfold mobiusDivisorDilationTail
  have hchannels :
      (∑ d ∈ Finset.Icc (D + 1) (M - 1), mobiusDivisorDilationChannel M d) =
        ∑ d ∈ Finset.Icc (D + 1) (M - 1),
          ∑ q ∈ Finset.Icc 1 ((M - 1) / d),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              divisorDilationClippedAbelWeight M d q * primeFreeDivisorDefect q := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 1 ≤ d := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    rw [mobiusDivisorDilationChannel_eq_quotientBlocks hd1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hchannels,
    sum_hyperbola_dilationTail_swap_real (M - 1) D
      (fun d q =>
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          divisorDilationClippedAbelWeight M d q * primeFreeDivisorDefect q)]
  apply Finset.sum_congr rfl
  intro q _
  unfold mobiusHighDilationClippedAbelKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- On the late-dilation octave `(M - 1) / 2 ≤ D`, only the first quotient block `q = 1` survives,
so `mobiusDivisorDilationTail M D` collapses to `primeFreeDivisorDefect 1` times the terminal
square-root Mertens sum. -/
theorem mobiusDivisorDilationTail_eq_first_block_of_half_le
    {M D : ℕ} (hD : (M - 1) / 2 ≤ D) :
    mobiusDivisorDilationTail M D =
      primeFreeDivisorDefect 1 *
        ∑ d ∈ Finset.Icc (D + 1) (M - 1),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (Real.sqrt M - Real.sqrt d) := by
  unfold mobiusDivisorDilationTail
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hdD, hdM⟩ := Finset.mem_Icc.mp hd
  have hd1 : 1 ≤ d := by omega
  have hdltM : d < M := by omega
  have hMd : M ≤ 2 * d := by omega
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
    divisorUnsignedDilationChannel_eq_first_block hd1 hdltM hMd]
  ring

/-- **Small-Quotient High-Dilation Kernel Strip Law:**
For any `φ ≥ 1/2` and `c ≥ φ - 1/2`, a one-sided upper bound of exponent `c` on the small-quotient
sum `q ≤ (M - 1) / (⌊M^φ⌋₊ + 1)` paired with `mobiusHighDilationClippedAbelKernel M ⌊M^φ⌋₊ q`
unconditionally forces `zetaZeroAbscissa ≤ 1/2 + c`. -/
theorem zetaZeroAbscissa_le_of_smallQuotient_highDilationKernel_le_rpow
    {φ C c : ℝ} (hφ : 1 / 2 ≤ φ) (hφc : φ - 1 / 2 ≤ c) (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M →
      (∑ q ∈ Finset.Icc 1 ((M - 1) / (⌊(M : ℝ) ^ φ⌋₊ + 1)),
        primeFreeDivisorDefect q *
          mobiusHighDilationClippedAbelKernel M ⌊(M : ℝ) ^ φ⌋₊ q) / M ≤
        C + C * (M : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + c := by
  refine zetaZeroAbscissa_le_of_mobiusDivisorDilationTail_le_rpow hφ hφc hC0 fun M hM2 => ?_
  rw [mobiusDivisorDilationTail_eq_smallQuotient_highDilationKernel]
  exact hM M hM2

/-- When `(q + 1) * D ≤ M` (`1 ≤ q`), every dilation block `1 ≤ d ≤ D` on quotient `q` is complete,
so `mobiusHighDilationClippedAbelKernel M D q` splits into the high-dilation complete-block Mertens
increment plus `mobiusTerminalClippedAbelKernel M q`. -/
theorem mobiusHighDilationClippedAbelKernel_eq_full_add_terminal
    {M D q : ℕ} (hq : 1 ≤ q) (hfull : (q + 1) * D ≤ M) :
    mobiusHighDilationClippedAbelKernel M D q =
      (Real.sqrt (q + 1 : ℕ) - Real.sqrt q) *
          (weightedMobiusSquareRootSum (M / (q + 1)) - weightedMobiusSquareRootSum D) +
        mobiusTerminalClippedAbelKernel M q := by
  have hDM : D ≤ (M - 1) / q := by
    by_cases hD0 : D = 0
    · simp [hD0]
    · have hqD : q * D ≤ M - 1 := by
        have hlt : q * D < (q + 1) * D := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
        omega
      exact (Nat.le_div_iff_mul_le (by omega : 0 < q)).2 (by simpa [Nat.mul_comm] using hqD)
  have hsplit : Finset.Icc 1 ((M - 1) / q) =
      Finset.Icc 1 D ∪ Finset.Icc (D + 1) ((M - 1) / q) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 D) (Finset.Icc (D + 1) ((M - 1) / q)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    simp only [Finset.mem_Icc] at hd1 hd2
    omega
  have htot := mobiusClippedAbelKernel_eq_full_add_terminal (M := M) hq
  unfold mobiusClippedAbelKernel at htot
  rw [hsplit, Finset.sum_union hdisj] at htot
  have hhead :
      (∑ d ∈ Finset.Icc 1 D,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * divisorDilationClippedAbelWeight M d q) =
      (Real.sqrt (q + 1 : ℕ) - Real.sqrt q) * weightedMobiusSquareRootSum D := by
    unfold weightedMobiusSquareRootSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hfd : (q + 1) * d ≤ M := (Nat.mul_le_mul_left (q + 1) hdD).trans hfull
    rw [divisorDilationClippedAbelWeight_eq_full hd1 hq hfd]
    ring
  rw [hhead] at htot
  change _ + mobiusHighDilationClippedAbelKernel M D q = _ at htot
  linarith

/-- **Complete Hyperbolic Rectangle Factorization:**
On any rectangle `1 ≤ q ≤ Q`, `1 ≤ d ≤ D` inside the complete-block region `(Q + 1) * D ≤ M`, the
2D Möbius–divisor kernel sum factors identically into `divisorUnsignedDilationChannel (Q + 1) 1`
times `weightedMobiusSquareRootSum D`. -/
theorem sum_complete_hyperbola_rectangle_eq_unitChannel_mul
    {M Q D : ℕ} (hfull : (Q + 1) * D ≤ M) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Icc 1 D,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        divisorDilationClippedAbelWeight M d q * primeFreeDivisorDefect q) =
      divisorUnsignedDilationChannel (Q + 1) 1 * weightedMobiusSquareRootSum D := by
  have hinner : ∀ q ∈ Finset.Icc 1 Q,
      (∑ d ∈ Finset.Icc 1 D,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          divisorDilationClippedAbelWeight M d q * primeFreeDivisorDefect q) =
      ((Real.sqrt (q + 1 : ℕ) - Real.sqrt q) * primeFreeDivisorDefect q) *
        weightedMobiusSquareRootSum D := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    unfold weightedMobiusSquareRootSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
    have hfd : (q + 1) * d ≤ M := by
      calc (q + 1) * d ≤ (Q + 1) * d := Nat.mul_le_mul_right d (by omega)
        _ ≤ (Q + 1) * D := Nat.mul_le_mul_left (Q + 1) hdD
        _ ≤ M := hfull
    rw [divisorDilationClippedAbelWeight_eq_full hd1 hq1 hfd]
    ring
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  congr 1
  unfold divisorUnsignedDilationChannel
  rw [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro q _
  rw [Nat.div_one]

/-- **Unconditional `(3/5) √(Q + 1)` Ceiling on Complete Hyperbolic Rectangles:**
Combining `sum_complete_hyperbola_rectangle_eq_unitChannel_mul` with
`divisorUnsignedDilationChannel_one_le_three_fifths_sqrt` bounds the `q`-sum on any complete
rectangle `(Q + 1) * D ≤ M` by `(3/5) √(Q + 1) * |weightedMobiusSquareRootSum D|`. -/
theorem abs_sum_complete_hyperbola_rectangle_le_three_fifths_sqrt_mul
    {M Q D : ℕ} (hfull : (Q + 1) * D ≤ M) :
    |∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Icc 1 D,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        divisorDilationClippedAbelWeight M d q * primeFreeDivisorDefect q| ≤
      (3 / 5 : ℝ) * Real.sqrt (Q + 1 : ℕ) * |weightedMobiusSquareRootSum D| := by
  rw [sum_complete_hyperbola_rectangle_eq_unitChannel_mul hfull, abs_mul,
    abs_of_nonneg (divisorUnsignedDilationChannel_nonneg (Q + 1) 1)]
  exact mul_le_mul_of_nonneg_right
    (divisorUnsignedDilationChannel_one_le_three_fifths_sqrt (Q + 1)) (abs_nonneg _)

/-! ## Section 4: Outgoing Charge, Monotone Convex Potential (`chebyshevSqrtConvexPotential`),
`chebyshevSqrtIncrementAction`, and SP-E Quarter-Dilation Balance Abscissa Laws -/

/-- Uniform `O(1)` bound on the normalized difference between `mobiusDivisorSquareRootAbelMoment`
and `chebyshevSqrtIncrementAction`. -/
theorem abs_mobiusDivisorSquareRootAbel_div_sub_chebyshevSqrtIncrementAction_div_le
    {M : ℕ} (hM : 2 ≤ M) :
    |mobiusDivisorSquareRootAbelMoment M / M - chebyshevSqrtIncrementAction M / M| ≤
      2 * |Real.eulerMascheroniConstant| + 1 := by
  have hM1 : 1 ≤ M := by omega
  have hMR : (0 : ℝ) < M := by positivity
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt M := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt M := Real.sqrt_le_sqrt hMone
  have hsqrtLe : Real.sqrt M ≤ (M : ℝ) := by
    nlinarith [Real.sq_sqrt hMR.le, Real.sqrt_nonneg (M : ℝ)]
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 2 := by
    constructor
    · calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
    · calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        _ = 2 := by norm_num
  have heq : mobiusDivisorSquareRootAbelMoment M / M - chebyshevSqrtIncrementAction M / M =
      (2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M -
        (Real.sqrt 2 - 1) / M := by
    rw [mobiusDivisorSquareRootAbelMoment_eq_chebyshevSqrtIncrementAction_add hM]
    ring
  have hgamma : |(2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M| ≤
      2 * |Real.eulerMascheroniConstant| := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos hMR, abs_of_nonneg (sub_nonneg.mpr hsqrtOne)]
    exact (div_le_iff₀ hMR).2 (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hconst : |(Real.sqrt 2 - 1) / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hMR, abs_of_nonneg (by linarith [hsqrt2.1])]
    exact (div_le_iff₀ hMR).2 (by linarith [hsqrt2.2])
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add hgamma hconst)

/-- Uniform `O(1)` bound on the difference between `mobiusDivisorSquareRootAbelMoment M / M`
and `unitRieszCoherentCompletedOutgoingCharge M`. -/
theorem abs_mobiusDivisorSquareRootAbel_div_sub_completedOutgoingCharge_le
    {M : ℕ} (hM : 2 ≤ M) :
    |mobiusDivisorSquareRootAbelMoment M / M - unitRieszCoherentCompletedOutgoingCharge M| ≤
      2 * |Real.eulerMascheroniConstant| + 1 := by
  have hM1 : 1 ≤ M := by omega
  have hMR : (0 : ℝ) < M := by positivity
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt M := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt M := Real.sqrt_le_sqrt hMone
  have hsqrtLe : Real.sqrt M ≤ (M : ℝ) := by
    nlinarith [Real.sq_sqrt hMR.le, Real.sqrt_nonneg (M : ℝ)]
  have heq : mobiusDivisorSquareRootAbelMoment M / M - unitRieszCoherentCompletedOutgoingCharge M =
      (2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M -
        coherentSquareRootPolarLatticeDefect M / M := by
    rw [mobiusDivisorSquareRootAbelMoment_eq_coherent_add_gammaBoundary hM1,
      coherentCompletedOutgoing_eq_abel_add_latticeDefect_div hM]
    ring
  have hgamma : |(2 * Real.eulerMascheroniConstant * (Real.sqrt M - 1)) / M| ≤
      2 * |Real.eulerMascheroniConstant| := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos hMR, abs_of_nonneg (sub_nonneg.mpr hsqrtOne)]
    exact (div_le_iff₀ hMR).2 (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hdef : |coherentSquareRootPolarLatticeDefect M / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hMR, div_le_iff₀ hMR]
    exact (abs_coherentSquareRootPolarLatticeDefect_le hM1).trans (by linarith)
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add hgamma hdef)

/-- Normalized identity expressing `unitRieszCoherentCompletedOutgoingCharge M` as the normalized
excess of the monotone square-root-convex potential `chebyshevSqrtConvexPotential M` over `M √M / 3`. -/
theorem unitRieszCoherentCompletedOutgoingCharge_eq_chebyshevSqrtConvexPotential_sub_div
    {M : ℕ} (hM : 2 ≤ M) :
    unitRieszCoherentCompletedOutgoingCharge M =
      (chebyshevSqrtConvexPotential M - (M : ℝ) * Real.sqrt M / 3) / M := by
  have hMR : (M : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hMR).2
  simpa only [mul_comm] using coherentCompletedOutgoing_mul_eq_chebyshevSqrtConvexPotential_sub hM

/-- Unconditional subpower bound on `chebyshevSqrtIncrementAction M / M` at `zetaZeroAbscissa`. -/
theorem exists_chebyshevSqrtIncrementAction_subpower_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |chebyshevSqrtIncrementAction M / M| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
  refine ⟨C + (2 * |Real.eulerMascheroniConstant| + 1), by positivity, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := by omega
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hpow1 : 1 ≤ (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) :=
    Real.one_le_rpow hMone (by linarith [half_le_zetaZeroAbscissa])
  have hdiff := abs_mobiusDivisorSquareRootAbel_div_sub_chebyshevSqrtIncrementAction_div_le hM
  have htot := hC M hM
  have heq : chebyshevSqrtIncrementAction M / M =
      mobiusDivisorSquareRootAbelMoment M / M -
        (mobiusDivisorSquareRootAbelMoment M / M - chebyshevSqrtIncrementAction M / M) := by ring
  rw [heq]
  refine (abs_sub _ _).trans ?_
  nlinarith [abs_nonneg Real.eulerMascheroniConstant]

/-- Unconditional subpower bound on `unitRieszCoherentCompletedOutgoingCharge M` at `zetaZeroAbscissa`. -/
theorem exists_unitRieszCoherentCompletedOutgoingCharge_subpower_zetaZeroAbscissa
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      |unitRieszCoherentCompletedOutgoingCharge M| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
  refine ⟨C + (2 * |Real.eulerMascheroniConstant| + 1), by positivity, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := by omega
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hpow1 : 1 ≤ (M : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) :=
    Real.one_le_rpow hMone (by linarith [half_le_zetaZeroAbscissa])
  have hdiff := abs_mobiusDivisorSquareRootAbel_div_sub_completedOutgoingCharge_le hM
  have htot := hC M hM
  have heq : unitRieszCoherentCompletedOutgoingCharge M =
      mobiusDivisorSquareRootAbelMoment M / M -
        (mobiusDivisorSquareRootAbelMoment M / M -
          unitRieszCoherentCompletedOutgoingCharge M) := by ring
  rw [heq]
  refine (abs_sub _ _).trans ?_
  nlinarith [abs_nonneg Real.eulerMascheroniConstant]

/-- **One-Sided Upper Strip Law for `chebyshevSqrtIncrementAction`:** -/
theorem zetaZeroAbscissa_le_of_chebyshevSqrtIncrementAction_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M → chebyshevSqrtIncrementAction M / M ≤ C + C * (M : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_mobiusDivisorSquareRootAbel_le_rpow
    (C := C + (2 * |Real.eulerMascheroniConstant| + 1)) (by positivity) fun M hM2 => ?_
  have hdiff := (le_abs_self _).trans
    (abs_mobiusDivisorSquareRootAbel_div_sub_chebyshevSqrtIncrementAction_div_le hM2)
  have hact := hM M hM2
  have hpos : 0 ≤ (M : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg M) c
  nlinarith [abs_nonneg Real.eulerMascheroniConstant]

/-- **One-Sided Lower Strip Law for `chebyshevSqrtIncrementAction`:** -/
theorem zetaZeroAbscissa_le_of_neg_rpow_le_chebyshevSqrtIncrementAction
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M → -(C + C * (M : ℝ) ^ c) ≤ chebyshevSqrtIncrementAction M / M) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel
    (C := C + (2 * |Real.eulerMascheroniConstant| + 1)) (by positivity) fun M hM2 => ?_
  have hdiff := (abs_le.mp
    (abs_mobiusDivisorSquareRootAbel_div_sub_chebyshevSqrtIncrementAction_div_le hM2)).1
  have hact := hM M hM2
  have hpos : 0 ≤ (M : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg M) c
  nlinarith [abs_nonneg Real.eulerMascheroniConstant]

/-- **One-Sided Upper Strip Law for `unitRieszCoherentCompletedOutgoingCharge`:** -/
theorem zetaZeroAbscissa_le_of_unitRieszCoherentCompletedOutgoingCharge_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M → unitRieszCoherentCompletedOutgoingCharge M ≤ C + C * (M : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_mobiusDivisorSquareRootAbel_le_rpow
    (C := C + (2 * |Real.eulerMascheroniConstant| + 1)) (by positivity) fun M hM2 => ?_
  have hdiff := (le_abs_self _).trans
    (abs_mobiusDivisorSquareRootAbel_div_sub_completedOutgoingCharge_le hM2)
  have hact := hM M hM2
  have hpos : 0 ≤ (M : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg M) c
  nlinarith [abs_nonneg Real.eulerMascheroniConstant]

/-- **One-Sided Lower Strip Law for `unitRieszCoherentCompletedOutgoingCharge`:** -/
theorem zetaZeroAbscissa_le_of_neg_rpow_le_unitRieszCoherentCompletedOutgoingCharge
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M → -(C + C * (M : ℝ) ^ c) ≤ unitRieszCoherentCompletedOutgoingCharge M) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_neg_rpow_le_mobiusDivisorSquareRootAbel
    (C := C + (2 * |Real.eulerMascheroniConstant| + 1)) (by positivity) fun M hM2 => ?_
  have hdiff := (abs_le.mp
    (abs_mobiusDivisorSquareRootAbel_div_sub_completedOutgoingCharge_le hM2)).1
  have hact := hM M hM2
  have hpos : 0 ≤ (M : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg M) c
  nlinarith [abs_nonneg Real.eulerMascheroniConstant]

/-- **One-Sided Upper Strip Law for the Monotone Convex Potential `chebyshevSqrtConvexPotential`:**
If `(chebyshevSqrtConvexPotential M - M √M / 3) / M ≤ C + C * M^c` for all `M ≥ 2`, then
`zetaZeroAbscissa ≤ 1/2 + max 0 c`. -/
theorem zetaZeroAbscissa_le_of_chebyshevSqrtConvexPotential_sub_cubic_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M →
      (chebyshevSqrtConvexPotential M - (M : ℝ) * Real.sqrt M / 3) / M ≤ C + C * (M : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_unitRieszCoherentCompletedOutgoingCharge_le_rpow hC0 fun M hM2 => ?_
  rw [unitRieszCoherentCompletedOutgoingCharge_eq_chebyshevSqrtConvexPotential_sub_div hM2]
  exact hM M hM2

/-- **One-Sided Lower Strip Law for the Monotone Convex Potential `chebyshevSqrtConvexPotential`:**
If `-(C + C * M^c) ≤ (chebyshevSqrtConvexPotential M - M √M / 3) / M` for all `M ≥ 2`, then
`zetaZeroAbscissa ≤ 1/2 + max 0 c`. -/
theorem zetaZeroAbscissa_le_of_neg_rpow_le_chebyshevSqrtConvexPotential_sub_cubic
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M →
      -(C + C * (M : ℝ) ^ c) ≤ (chebyshevSqrtConvexPotential M - (M : ℝ) * Real.sqrt M / 3) / M) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_neg_rpow_le_unitRieszCoherentCompletedOutgoingCharge hC0
    fun M hM2 => ?_
  rw [unitRieszCoherentCompletedOutgoingCharge_eq_chebyshevSqrtConvexPotential_sub_div hM2]
  exact hM M hM2

/-- **Exact One-Sided Upper Exponent Law for `unitRieszCoherentCompletedOutgoingCharge`:** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_completedOutgoingCharge_upper_exponents :
    zetaZeroAbscissa = 1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      unitRieszCoherentCompletedOutgoingCharge M ≤ C * (M : ℝ) ^ c} := by
  set S := {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
    unitRieszCoherentCompletedOutgoingCharge M ≤ C * (M : ℝ) ^ c}
  have hmem : ∀ ε : ℝ, 0 < ε → zetaZeroAbscissa - 1 / 2 + ε ∈ S := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ :=
      exists_unitRieszCoherentCompletedOutgoingCharge_subpower_zetaZeroAbscissa ε hε
    exact ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0,
      fun M hM => (le_abs_self _).trans (hC M hM)⟩
  have hne : S.Nonempty := ⟨_, hmem 1 one_pos⟩
  have hbdd : BddBelow S := ⟨0, fun c hc => hc.1⟩
  refine le_antisymm ?_ ?_
  · have hle : zetaZeroAbscissa - 1 / 2 ≤ sInf S := by
      refine le_csInf hne fun c hc => ?_
      obtain ⟨hc0, C, hC0, hC⟩ := hc
      have h := zetaZeroAbscissa_le_of_unitRieszCoherentCompletedOutgoingCharge_le_rpow hC0
        (fun M hM => (hC M hM).trans (le_add_of_nonneg_left hC0))
      rw [max_eq_right hc0] at h
      linarith
    linarith
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hle := csInf_le hbdd (hmem ε hε)
    linarith

/-- **Exact One-Sided Upper Exponent Law for the Monotone Convex Potential Excess:** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_chebyshevSqrtConvexPotential_upper_exponents :
    zetaZeroAbscissa = 1 / 2 + sInf {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 2 ≤ M →
      (chebyshevSqrtConvexPotential M - (M : ℝ) * Real.sqrt M / 3) / M ≤ C * (M : ℝ) ^ c} := by
  rw [zetaZeroAbscissa_eq_half_add_sInf_completedOutgoingCharge_upper_exponents]
  congr 2
  ext c
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => exists_congr fun C => and_congr_right fun _ =>
    forall_congr' fun M => imp_congr_right fun hM => ?_
  rw [unitRieszCoherentCompletedOutgoingCharge_eq_chebyshevSqrtConvexPotential_sub_div hM]

/-- **One-Sided Upper Strip Law for the Cumulative SP-E Quarter-Dilation Balance:** -/
theorem zetaZeroAbscissa_le_of_sum_quarterDilationBalance_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ M : ℕ, 2 ≤ M →
      (∑ j ∈ Finset.Ico 2 M,
        (unitRieszCoherentOutgoingQuarterDilationGain j -
          unitRieszCoherentOutgoingQuarterDilationDebt j -
          (Real.sqrt (j + 1 : ℕ) - Real.sqrt j) / 3)) ≤ C + C * (M : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_unitRieszCoherentCompletedOutgoingCharge_le_rpow
    (C := C + |unitRieszCoherentCompletedOutgoingCharge 2|) (by positivity) fun M hM2 => ?_
  have hsum := sum_quarterDilationBalance_eq_completedOutgoingCharge_sub hM2
  have hbound := hM M hM2
  have hbase := le_abs_self (unitRieszCoherentCompletedOutgoingCharge 2)
  have hpos : 0 ≤ (M : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg M) c
  nlinarith [abs_nonneg (unitRieszCoherentCompletedOutgoingCharge 2)]

/-- **One-Sided Lower Strip Law for `suzukiEulerianCompletedOutgoingDiscrepancy`:** -/
theorem zetaZeroAbscissa_le_of_neg_rpow_le_suzukiEulerianCompletedOutgoingDiscrepancy
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hN : ∀ N : ℕ, 2 ≤ N →
      -(C + C * ((N + 1 : ℕ) : ℝ) ^ c) ≤ suzukiEulerianCompletedOutgoingDiscrepancy N) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  let B0 := C + 5 + |suzukiEulerianCoherentBoundaryAnchor| +
    |unitRieszCoherentCompletedOutgoingCharge 2|
  refine zetaZeroAbscissa_le_of_unitRieszCoherentCompletedOutgoingCharge_le_rpow
    (C := B0) (by dsimp [B0]; positivity) fun M hM2 => ?_
  have hpos : 0 ≤ (M : ℝ) ^ c := Real.rpow_nonneg (Nat.cast_nonneg M) c
  rcases lt_or_ge M 3 with hlt | hM3
  · have hM_eq : M = 2 := by omega
    subst M
    have hbase : unitRieszCoherentCompletedOutgoingCharge 2 ≤ B0 := by
      dsimp [B0]
      linarith [le_abs_self (unitRieszCoherentCompletedOutgoingCharge 2),
        abs_nonneg suzukiEulerianCoherentBoundaryAnchor]
    have hB0_nonneg : 0 ≤ B0 := by dsimp [B0]; positivity
    exact hbase.trans (le_add_of_nonneg_right (mul_nonneg hB0_nonneg hpos))
  · have hN2 : 2 ≤ M - 1 := by omega
    have hadd : M - 1 + 1 = M := Nat.sub_add_cancel (by omega : 1 ≤ M)
    have hdisc := suzukiEulerianCompletedOutgoingDiscrepancy_eq_neg_charge_add_residual hN2
    rw [hadd] at hdisc
    have hres := (le_abs_self _).trans (abs_suzukiEulerianCompletedOutgoingResidual_le (M - 1))
    have hb := hN (M - 1) hN2
    rw [hadd] at hb
    dsimp [B0]
    nlinarith [abs_nonneg suzukiEulerianCoherentBoundaryAnchor,
      abs_nonneg (unitRieszCoherentCompletedOutgoingCharge 2)]

end

end RHTower
