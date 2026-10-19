import GaloisForLFunctions.RHTower.QuasiRHDilationTailHyperbolaAndOutgoingPotentialAbscissaLaw
import GaloisForLFunctions.RHTower.SquareSampleObserverJetOneSidedStrip
import GaloisForLFunctions.RHTower.WeilLagPowerGapExceptionalSampling

/-!
# Quasi-RH Abscissa Laws III: Power-Mesh Sampling, Exact Integer-Power Dilation Cutoffs, Square-Sample Sums, and Observer-Jet / Exceptional Lag Laws

This module connects four further sectors of the `RHTower` corpus to support unconditional proofs
of the quasi-RH strips `1/6 ≤ Re(ρ) ≤ 5/6` (`zetaZeroAbscissa ≤ 5/6`) and
`1/4 ≤ Re(ρ) ≤ 3/4` (`zetaZeroAbscissa ≤ 3/4`):

1. **Power-Gap Sampling & Arbitrary `m`-th Power Mesh (`M = j^m`, `m ≥ 1`) Abscissa Laws (`Section 1`):**
   Combining the two-step von Koch bootstrap on power-gap sets
   (`MobiusDivisorOneSidedPowerGapBootstrap`, `MobiusDivisorLowerStripPowerGapBootstrap`) with
   `exists_pow_le_sub_le_rpow` and `exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa`
   proves that for **any** integer power `m ≥ 1`, `zetaZeroAbscissa` equals `1/2` plus the exact
   infimum of one-sided upper (or lower) growth exponents `c ≥ 0` of
   `mobiusDivisorSquareRootAbelMoment (j^m) / (j^m)` tested solely on the sparse `m`-th power mesh
   `M = j^m`, as well as adaptive backward power-window criteria.

2. **Exact Integer-Power Dilation Cutoffs (`M = j^m`, `D = j^(m - 1)`) and `(j - 1)`-Quotient
   Hyperbola Reduction (`Section 2`):**
   For every `m ≥ 2` and `j ≥ 1`, `(j^m - 1) / (j^(m - 1) + 1) = j - 1` holds as an exact identity
   in `ℕ` (`pow_sub_one_div_pow_pred_add_one`). Combined with hyperbola duality
   (`mobiusDivisorDilationTail_eq_smallQuotient_highDilationKernel`), the high-dilation tail
   `mobiusDivisorDilationTail (j^m) (j^(m - 1))` sums over **strictly fewer than `j` quotients**
   (`1 ≤ q ≤ j - 1`) with zero floor/ceiling rounding error. On even power meshes `M = j^(2*r)` with
   `D = j^(2*r - 1)`, the normalized dilation head is unconditionally bounded by `(3/5) * j^(r - 1)`:
   - for `r = 3` (`M = j^6`, `D = j^5`), the head is `≤ (3/5) * j^2 = (3/5) * (j^6)^(1/3)`, reducing
     `zetaZeroAbscissa ≤ 5/6` (`1/6 ≤ Re(ρ) ≤ 5/6`) to a one-sided `O(j^8)` bound on the
     `(j - 1)`-quotient sum `mobiusDivisorDilationTail (j^6) (j^5)`;
   - for `r = 2` (`M = j^4`, `D = j^3`), the head is `≤ (3/5) * j = (3/5) * (j^4)^(1/4)`, reducing
     `zetaZeroAbscissa ≤ 3/4` (`1/4 ≤ Re(ρ) ≤ 3/4`) to a one-sided `O(j^5)` bound on the
     `(j - 1)`-quotient sum `mobiusDivisorDilationTail (j^4) (j^3)`;
   - for `r = 1` (`M = j^2`, `D = j`), the head is `≤ 3/5`.

3. **Unweighted Square-Sample Chebyshev Sum & Observer-Jet / `lagBracketSlope` Tail Action
   Abscissa Laws (`Section 3`):**
   Connecting `SquareSampleObserverJetOneSidedStrip` with `zetaZeroAbscissa` yields the
   unconditional forward bound, one-sided strip laws, and exact `sInf` exponent laws for the
   unweighted square-sample Chebyshev sum `(∑_{1 ≤ s < N} psiRemainder (s^2)) / N^2`, together with
   one-sided strip laws for `completedSourceObserverJetPositiveHistoryAction`,
   `completedSourceObserverJetNegativeHistoryAction`, `lagBracketSlopePositiveTailAction`, and
   `lagBracketSlopeNegativeTailAction`.

4. **Exceptional Power-Gap `integerLag` Abscissa Laws (`Section 4`):**
   Connecting `WeilLagPowerGapExceptionalSampling` with `zetaZeroAbscissa` establishes that
   one-sided `O(k^c)` bounds on `integerLag k` sampled in power-gap windows outside an exponentially
   thin log-scale exceptional set `S` (`∫_S e^(κ u) du < ∞`, `κ > 0`) unconditionally force
   `zetaZeroAbscissa ≤ 1/2 + max 0 c`.
-/

open Complex Real Set Filter Topology MeasureTheory Finset
open scoped BigOperators ArithmeticFunction
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Section 1: Power-Gap Sampling & Arbitrary `m`-th Power Mesh Abscissa Laws -/

/-- One-sided upper power-gap strip law for `zetaZeroAbscissa`:
if `mobiusDivisorSquareRootAbelMoment k / k ≤ M + M * k^c` on a power-gap sample set `A`,
then `zetaZeroAbscissa ≤ 1 / 2 + max 0 c`. -/
theorem zetaZeroAbscissa_le_half_add_max_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    {A : Set ℕ} {M c K δ : ℝ} {N₀ : ℕ}
    (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hA_bound : ∀ k ∈ A, 2 ≤ k →
      mobiusDivisorSquareRootAbelMoment k / (k : ℝ) ≤ M + M * (k : ℝ) ^ c)
    (hA_gaps : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound (le_max_left 0 c) (fun ρ hρ => ?_)
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    hM0 hδ hK hA_bound hA_gaps q
  linarith [(abs_le.mp h).2]

/-- One-sided lower power-gap strip law for `zetaZeroAbscissa`:
if `-(M + M * k^c) ≤ mobiusDivisorSquareRootAbelMoment k / k` on a power-gap sample set `A`,
then `zetaZeroAbscissa ≤ 1 / 2 + max 0 c`. -/
theorem zetaZeroAbscissa_le_half_add_max_of_powerGaps_neg_rpow_le_mobiusDivisorSquareRootAbel
    {A : Set ℕ} {M c K δ : ℝ} {N₀ : ℕ}
    (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hA_bound : ∀ k ∈ A, 2 ≤ k →
      -(M + M * (k : ℝ) ^ c) ≤ mobiusDivisorSquareRootAbelMoment k / (k : ℝ))
    (hA_gaps : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound (le_max_left 0 c) (fun ρ hρ => ?_)
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_powerGaps_neg_rpow_le_mobiusDivisorSquareRootAbel
    hM0 hδ hK hA_bound hA_gaps q
  linarith [(abs_le.mp h).2]

/-- **Arbitrary `m`-th power mesh upper strip law for `zetaZeroAbscissa` (`m ≥ 1`).**
A one-sided upper bound `mobiusDivisorSquareRootAbelMoment (j^m) / (j^m) ≤ M + M * (j^m)^c`
evaluated solely along `m`-th powers `j^m` unconditionally forces
`zetaZeroAbscissa ≤ 1 / 2 + max 0 c`. -/
theorem zetaZeroAbscissa_le_half_add_max_of_mobiusDivisorSquareRootAbel_pow_le_rpow
    {m : ℕ} {M c : ℝ} (hm : 1 ≤ m) (hM0 : 0 ≤ M)
    (hpow : ∀ j : ℕ, 2 ≤ j ^ m →
      mobiusDivisorSquareRootAbelMoment (j ^ m) / ((j ^ m : ℕ) : ℝ) ≤
        M + M * ((j ^ m : ℕ) : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  let A : Set ℕ := Set.range (fun j : ℕ => j ^ m)
  have hδ : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  have hK : (0 : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ (m - 1) := by positivity
  have hA_gaps : ∀ n : ℕ, 1 ≤ n →
      ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤
        ((m : ℝ) * (2 : ℝ) ^ (m - 1)) * (n : ℝ) ^ (1 - 1 / (m : ℝ)) := by
    intro n hn
    obtain ⟨j, hjle, hjgap⟩ := exists_pow_le_sub_le_rpow hm hn
    exact ⟨j ^ m, ⟨j, rfl⟩, hjle, hjgap⟩
  refine zetaZeroAbscissa_le_half_add_max_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    hM0 hδ hK ?_ hA_gaps
  rintro k ⟨j, rfl⟩ hk2
  exact hpow j hk2

/-- **Arbitrary `m`-th power mesh lower strip law for `zetaZeroAbscissa` (`m ≥ 1`).**
A one-sided lower bound `-(M + M * (j^m)^c) ≤ mobiusDivisorSquareRootAbelMoment (j^m) / (j^m)`
evaluated solely along `m`-th powers `j^m` unconditionally forces
`zetaZeroAbscissa ≤ 1 / 2 + max 0 c`. -/
theorem zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_mobiusDivisorSquareRootAbel_pow
    {m : ℕ} {M c : ℝ} (hm : 1 ≤ m) (hM0 : 0 ≤ M)
    (hpow : ∀ j : ℕ, 2 ≤ j ^ m →
      -(M + M * ((j ^ m : ℕ) : ℝ) ^ c) ≤
        mobiusDivisorSquareRootAbelMoment (j ^ m) / ((j ^ m : ℕ) : ℝ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  let A : Set ℕ := Set.range (fun j : ℕ => j ^ m)
  have hδ : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  have hK : (0 : ℝ) ≤ (m : ℝ) * (2 : ℝ) ^ (m - 1) := by positivity
  have hA_gaps : ∀ n : ℕ, 1 ≤ n →
      ∃ k ∈ A, k ≤ n ∧ (n : ℝ) - k ≤
        ((m : ℝ) * (2 : ℝ) ^ (m - 1)) * (n : ℝ) ^ (1 - 1 / (m : ℝ)) := by
    intro n hn
    obtain ⟨j, hjle, hjgap⟩ := exists_pow_le_sub_le_rpow hm hn
    exact ⟨j ^ m, ⟨j, rfl⟩, hjle, hjgap⟩
  refine zetaZeroAbscissa_le_half_add_max_of_powerGaps_neg_rpow_le_mobiusDivisorSquareRootAbel
    hM0 hδ hK ?_ hA_gaps
  rintro k ⟨j, rfl⟩ hk2
  exact hpow j hk2

/-- The set of nonnegative one-sided upper growth exponents `c ≥ 0` for
`mobiusDivisorSquareRootAbelMoment (j^m) / (j^m)` along the `m`-th power mesh. -/
def mobiusDivisorSquareRootAbelPowUpperExponentSet (m : ℕ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, 2 ≤ j ^ m →
    mobiusDivisorSquareRootAbelMoment (j ^ m) / ((j ^ m : ℕ) : ℝ) ≤
      C * ((j ^ m : ℕ) : ℝ) ^ c}

/-- The set of nonnegative one-sided lower growth exponents `c ≥ 0` for
`mobiusDivisorSquareRootAbelMoment (j^m) / (j^m)` along the `m`-th power mesh. -/
def mobiusDivisorSquareRootAbelPowLowerExponentSet (m : ℕ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, 2 ≤ j ^ m →
    -(C * ((j ^ m : ℕ) : ℝ) ^ c) ≤
      mobiusDivisorSquareRootAbelMoment (j ^ m) / ((j ^ m : ℕ) : ℝ)}

/-- **Exact `sInf` abscissa formula on every `m`-th power mesh (`m ≥ 1`, upper bound).** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_mobiusDivisorSquareRootAbel_pow_upper
    {m : ℕ} (hm : 1 ≤ m) :
    zetaZeroAbscissa = 1 / 2 + sInf (mobiusDivisorSquareRootAbelPowUpperExponentSet m) := by
  have hbdd : BddBelow (mobiusDivisorSquareRootAbelPowUpperExponentSet m) :=
    ⟨0, fun _ hc => hc.1⟩
  have hmem : ∀ ε : ℝ, 0 < ε →
      zetaZeroAbscissa - 1 / 2 + ε ∈ mobiusDivisorSquareRootAbelPowUpperExponentSet m := by
    intro ε hε
    have hhalf := half_le_zetaZeroAbscissa
    obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
    refine ⟨by linarith, C, hC0, fun j hj => ?_⟩
    exact (le_abs_self _).trans (hC (j ^ m) hj)
  have h1 : zetaZeroAbscissa - 1 / 2 ≤
      sInf (mobiusDivisorSquareRootAbelPowUpperExponentSet m) := by
    refine le_csInf ⟨zetaZeroAbscissa - 1 / 2 + 1, hmem 1 zero_lt_one⟩ ?_
    rintro c ⟨hc0, C, hC0, hC⟩
    have hpow : ∀ j : ℕ, 2 ≤ j ^ m →
        mobiusDivisorSquareRootAbelMoment (j ^ m) / ((j ^ m : ℕ) : ℝ) ≤
          C + C * ((j ^ m : ℕ) : ℝ) ^ c :=
      fun j hj => (hC j hj).trans (le_add_of_nonneg_left hC0)
    have hle :=
      zetaZeroAbscissa_le_half_add_max_of_mobiusDivisorSquareRootAbel_pow_le_rpow hm hC0 hpow
    rw [max_eq_right hc0] at hle
    linarith
  have h2 : sInf (mobiusDivisorSquareRootAbelPowUpperExponentSet m) ≤
      zetaZeroAbscissa - 1 / 2 := by
    by_contra hlt
    push Not at hlt
    set δ : ℝ := (sInf (mobiusDivisorSquareRootAbelPowUpperExponentSet m) -
      (zetaZeroAbscissa - 1 / 2)) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hcs := csInf_le hbdd (hmem δ hδ)
    dsimp [δ] at hcs
    linarith
  linarith

/-- **Exact `sInf` abscissa formula on every `m`-th power mesh (`m ≥ 1`, lower bound).** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_mobiusDivisorSquareRootAbel_pow_lower
    {m : ℕ} (hm : 1 ≤ m) :
    zetaZeroAbscissa = 1 / 2 + sInf (mobiusDivisorSquareRootAbelPowLowerExponentSet m) := by
  have hbdd : BddBelow (mobiusDivisorSquareRootAbelPowLowerExponentSet m) :=
    ⟨0, fun _ hc => hc.1⟩
  have hmem : ∀ ε : ℝ, 0 < ε →
      zetaZeroAbscissa - 1 / 2 + ε ∈ mobiusDivisorSquareRootAbelPowLowerExponentSet m := by
    intro ε hε
    have hhalf := half_le_zetaZeroAbscissa
    obtain ⟨C, hC0, hC⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
    refine ⟨by linarith, C, hC0, fun j hj => ?_⟩
    exact (neg_le_neg (hC (j ^ m) hj)).trans (neg_abs_le _)
  have h1 : zetaZeroAbscissa - 1 / 2 ≤
      sInf (mobiusDivisorSquareRootAbelPowLowerExponentSet m) := by
    refine le_csInf ⟨zetaZeroAbscissa - 1 / 2 + 1, hmem 1 zero_lt_one⟩ ?_
    rintro c ⟨hc0, C, hC0, hC⟩
    have hpow : ∀ j : ℕ, 2 ≤ j ^ m →
        -(C + C * ((j ^ m : ℕ) : ℝ) ^ c) ≤
          mobiusDivisorSquareRootAbelMoment (j ^ m) / ((j ^ m : ℕ) : ℝ) :=
      fun j hj => (neg_le_neg (le_add_of_nonneg_left hC0)).trans (hC j hj)
    have hle :=
      zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_mobiusDivisorSquareRootAbel_pow hm hC0 hpow
    rw [max_eq_right hc0] at hle
    linarith
  have h2 : sInf (mobiusDivisorSquareRootAbelPowLowerExponentSet m) ≤
      zetaZeroAbscissa - 1 / 2 := by
    by_contra hlt
    push Not at hlt
    set δ : ℝ := (sInf (mobiusDivisorSquareRootAbelPowLowerExponentSet m) -
      (zetaZeroAbscissa - 1 / 2)) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hcs := csInf_le hbdd (hmem δ hδ)
    dsimp [δ] at hcs
    linarith
  linarith

/-- Adaptive power-window upper strip law for `zetaZeroAbscissa`:
if every backward power-gap window `[n - K n^(1 - δ), n]` (`n ≥ N₀`) contains a sample `k ≥ 2`
satisfying `mobiusDivisorSquareRootAbelMoment k / k ≤ M + M * k^c`, then
`zetaZeroAbscissa ≤ 1 / 2 + max 0 c`. -/
theorem zetaZeroAbscissa_le_half_add_max_of_powerWindow_mobiusDivisorSquareRootAbel_le_rpow
    {M c K δ : ℝ} {N₀ : ℕ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hwin : ∀ n : ℕ, N₀ ≤ n → ∃ k : ℕ, 2 ≤ k ∧ k ≤ n ∧
      (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ) ∧
      mobiusDivisorSquareRootAbelMoment k / (k : ℝ) ≤ M + M * (k : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  let A : Set ℕ := {k : ℕ | 2 ≤ k ∧
    mobiusDivisorSquareRootAbelMoment k / (k : ℝ) ≤ M + M * (k : ℝ) ^ c}
  refine zetaZeroAbscissa_le_half_add_max_of_powerGaps_mobiusDivisorSquareRootAbel_le_rpow
    (A := A) (N₀ := N₀) hM0 hδ hK (fun k hk _ => hk.2) (fun n hn => ?_)
  obtain ⟨k, hk2, hkn, hgap, hkbound⟩ := hwin n hn
  exact ⟨k, ⟨hk2, hkbound⟩, hkn, hgap⟩

/-- Adaptive power-window lower strip law for `zetaZeroAbscissa`:
if every backward power-gap window `[n - K n^(1 - δ), n]` (`n ≥ N₀`) contains a sample `k ≥ 2`
satisfying `-(M + M * k^c) ≤ mobiusDivisorSquareRootAbelMoment k / k`, then
`zetaZeroAbscissa ≤ 1 / 2 + max 0 c`. -/
theorem zetaZeroAbscissa_le_half_add_max_of_powerWindow_neg_rpow_le_mobiusDivisorSquareRootAbel
    {M c K δ : ℝ} {N₀ : ℕ} (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K)
    (hwin : ∀ n : ℕ, N₀ ≤ n → ∃ k : ℕ, 2 ≤ k ∧ k ≤ n ∧
      (n : ℝ) - k ≤ K * (n : ℝ) ^ (1 - δ) ∧
      -(M + M * (k : ℝ) ^ c) ≤ mobiusDivisorSquareRootAbelMoment k / (k : ℝ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  let A : Set ℕ := {k : ℕ | 2 ≤ k ∧
    -(M + M * (k : ℝ) ^ c) ≤ mobiusDivisorSquareRootAbelMoment k / (k : ℝ)}
  refine zetaZeroAbscissa_le_half_add_max_of_powerGaps_neg_rpow_le_mobiusDivisorSquareRootAbel
    (A := A) (N₀ := N₀) hM0 hδ hK (fun k hk _ => hk.2) (fun n hn => ?_)
  obtain ⟨k, hk2, hkn, hgap, hkbound⟩ := hwin n hn
  exact ⟨k, ⟨hk2, hkbound⟩, hkn, hgap⟩

/-! ## Section 2: Exact Integer-Power Dilation-Cutoff & Hyperbola Quotient-Window Reduction -/

/-- **Exact hyperbola quotient-cutoff identity on `m`-th powers (`m ≥ 2`, `j ≥ 1`).**
For any `m ≥ 2` and `j ≥ 1`, dividing `j^m - 1` by the exact integer-power dilation threshold
`j^(m - 1) + 1` yields `j - 1` with zero floor/ceiling rounding error. -/
theorem pow_sub_one_div_pow_pred_add_one {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) :
    (j ^ m - 1) / (j ^ (m - 1) + 1) = j - 1 := by
  have hpow : j * j ^ (m - 1) = j ^ m := by
    conv_rhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ m), pow_succ']
  have hj_le : j ≤ j ^ (m - 1) := by
    simpa using Nat.pow_le_pow_right hj (by omega : 1 ≤ m - 1)
  have hj1_pos : 1 ≤ j ^ m := Nat.one_le_pow m j hj
  have hpowZ : (j : ℤ) * (j ^ (m - 1) : ℕ) = (j ^ m : ℕ) := by exact_mod_cast hpow
  have hj_leZ : (j : ℤ) ≤ (j ^ (m - 1) : ℕ) := by exact_mod_cast hj_le
  have hjZ : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj
  apply Nat.div_eq_of_lt_le
  · have hle_int : (((j - 1) * (j ^ (m - 1) + 1) : ℕ) : ℤ) ≤ ((j ^ m - 1 : ℕ) : ℤ) := by
      push_cast [hj, hj1_pos]
      linarith
    exact_mod_cast hle_int
  · have hlt_int : ((j ^ m - 1 : ℕ) : ℤ) < (((j - 1 + 1) * (j ^ (m - 1) + 1) : ℕ) : ℤ) := by
      rw [Nat.sub_add_cancel hj]
      push_cast [hj1_pos]
      linarith
    exact_mod_cast hlt_int

/-- **Exact `(j - 1)`-quotient hyperbola representation of `mobiusDivisorDilationTail (j^m) (j^(m - 1))`.**
On the `m`-th power mesh `M = j^m` with exact dilation cutoff `D = j^(m - 1)` (`m ≥ 2`, `j ≥ 1`),
the high-dilation tail sums solely over the `j - 1` quotients `1 ≤ q ≤ j - 1`. -/
theorem mobiusDivisorDilationTail_pow_eq_Icc_pred_smallQuotient
    {m j : ℕ} (hm : 2 ≤ m) (hj : 1 ≤ j) :
    mobiusDivisorDilationTail (j ^ m) (j ^ (m - 1)) =
      ∑ q ∈ Finset.Icc 1 (j - 1),
        primeFreeDivisorDefect q *
          mobiusHighDilationClippedAbelKernel (j ^ m) (j ^ (m - 1)) q := by
  rw [mobiusDivisorDilationTail_eq_smallQuotient_highDilationKernel (j ^ m) (j ^ (m - 1)),
    pow_sub_one_div_pow_pred_add_one hm hj]

/-- **Unconditional dilation-head bound on even power meshes `M = j^(2*r)` (`D = j^(2*r - 1)`).**
For every `r ≥ 1` and `j ≥ 1`,
`|mobiusDivisorDilationHead (j^(2*r)) (j^(2*r - 1)) / (j^(2*r))| ≤ (3 / 5) * j^(r - 1)`. -/
theorem abs_mobiusDivisorDilationHead_even_pow_div_le
    {r j : ℕ} (hr : 1 ≤ r) (hj : 1 ≤ j) :
    |mobiusDivisorDilationHead (j ^ (2 * r)) (j ^ (2 * r - 1)) / ((j ^ (2 * r) : ℕ) : ℝ)| ≤
      (3 / 5 : ℝ) * (j : ℝ) ^ (r - 1) := by
  have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hM_pos : (0 : ℝ) < ((j ^ (2 * r) : ℕ) : ℝ) := by positivity
  have hsqrt : Real.sqrt ((j ^ (2 * r) : ℕ) : ℝ) = (j : ℝ) ^ r := by
    have hsq : ((j ^ (2 * r) : ℕ) : ℝ) = ((j : ℝ) ^ r) ^ 2 := by
      push_cast
      rw [← pow_mul, mul_comm 2 r]
    rw [hsq, Real.sqrt_sq (by positivity)]
  have hhead := abs_mobiusDivisorDilationHead_le (j ^ (2 * r)) (j ^ (2 * r - 1))
  rw [hsqrt] at hhead
  rw [abs_div, abs_of_pos hM_pos, div_le_iff₀ hM_pos]
  have hexp : ((j ^ (2 * r - 1) : ℕ) : ℝ) * (j : ℝ) ^ r =
      (j : ℝ) ^ (r - 1) * ((j ^ (2 * r) : ℕ) : ℝ) := by
    push_cast
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  linarith

/-- Specialization of `abs_mobiusDivisorDilationHead_even_pow_div_le` to `r = 3` (`M = j^6`, `D = j^5`):
the `5/6` dilation head is unconditionally bounded by `(3 / 5) * j^2 = (3 / 5) * (j^6)^(1/3)`. -/
theorem abs_mobiusDivisorDilationHead_pow_six_div_le {j : ℕ} (hj : 1 ≤ j) :
    |mobiusDivisorDilationHead (j ^ 6) (j ^ 5) / ((j ^ 6 : ℕ) : ℝ)| ≤
      (3 / 5 : ℝ) * (j : ℝ) ^ 2 := by
  simpa using abs_mobiusDivisorDilationHead_even_pow_div_le (r := 3) (by omega) hj

/-- Specialization of `abs_mobiusDivisorDilationHead_even_pow_div_le` to `r = 2` (`M = j^4`, `D = j^3`):
the `3/4` dilation head is unconditionally bounded by `(3 / 5) * j = (3 / 5) * (j^4)^(1/4)`. -/
theorem abs_mobiusDivisorDilationHead_pow_four_div_le {j : ℕ} (hj : 1 ≤ j) :
    |mobiusDivisorDilationHead (j ^ 4) (j ^ 3) / ((j ^ 4 : ℕ) : ℝ)| ≤
      (3 / 5 : ℝ) * (j : ℝ) := by
  simpa using abs_mobiusDivisorDilationHead_even_pow_div_le (r := 2) (by omega) hj

/-- Specialization of `abs_mobiusDivisorDilationHead_even_pow_div_le` to `r = 1` (`M = j^2`, `D = j`):
the `1/2` dilation head on the square mesh is unconditionally bounded by `3 / 5`. -/
theorem abs_mobiusDivisorDilationHead_pow_two_div_le {j : ℕ} (hj : 1 ≤ j) :
    |mobiusDivisorDilationHead (j ^ 2) j / ((j ^ 2 : ℕ) : ℝ)| ≤ (3 / 5 : ℝ) := by
  simpa using abs_mobiusDivisorDilationHead_even_pow_div_le (r := 1) (by omega) hj

/-- **General even-power (`M = j^(2*r)`, `D = j^(2*r - 1)`) one-sided upper dilation-tail strip law.**
For `r ≥ 1` and `((r - 1 : ℕ) : ℝ) / (2 * r : ℕ) ≤ c`, a one-sided upper bound on
`mobiusDivisorDilationTail (j^(2*r)) (j^(2*r - 1)) / (j^(2*r))` along `j ≥ 2` unconditionally
forces `zetaZeroAbscissa ≤ 1 / 2 + c`. -/
theorem zetaZeroAbscissa_le_half_add_of_dilationTail_even_pow_le_rpow
    {r : ℕ} {C c : ℝ} (hr : 1 ≤ r) (hC0 : 0 ≤ C)
    (hc : ((r - 1 : ℕ) : ℝ) / ((2 * r : ℕ) : ℝ) ≤ c)
    (htail : ∀ j : ℕ, 2 ≤ j →
      mobiusDivisorDilationTail (j ^ (2 * r)) (j ^ (2 * r - 1)) / ((j ^ (2 * r) : ℕ) : ℝ) ≤
        C + C * ((j ^ (2 * r) : ℕ) : ℝ) ^ c) :
    zetaZeroAbscissa ≤ 1 / 2 + c := by
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  have hm : 1 ≤ 2 * r := by omega
  have hle := zetaZeroAbscissa_le_half_add_max_of_mobiusDivisorSquareRootAbel_pow_le_rpow
    (m := 2 * r) (M := C + 3 / 5) (c := c) hm (by positivity) (fun j hj => ?_)
  · rwa [max_eq_right hc0] at hle
  · have hj2 : 2 ≤ j := by
      by_contra hlt
      have hj1 : j ≤ 1 := by omega
      have hpow1 : j ^ (2 * r) ≤ 1 := by
        calc j ^ (2 * r) ≤ 1 ^ (2 * r) := Nat.pow_le_pow_left hj1 (2 * r)
          _ = 1 := one_pow _
      omega
    have hj1 : 1 ≤ j := by omega
    have hdecomp := mobiusDivisorSquareRootAbelMoment_eq_dilationHead_add_dilationTail
      (j ^ (2 * r)) (j ^ (2 * r - 1))
    have hhead := (abs_le.mp (abs_mobiusDivisorDilationHead_even_pow_div_le hr hj1)).2
    have hht := htail j hj2
    have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
    have hrpow_id : (j : ℝ) ^ (r - 1) =
        ((j ^ (2 * r) : ℕ) : ℝ) ^ (((r - 1 : ℕ) : ℝ) / ((2 * r : ℕ) : ℝ)) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast (j : ℝ) (2 * r), ← Real.rpow_mul hj_pos.le,
        mul_div_cancel₀ _ (by positivity : ((2 * r : ℕ) : ℝ) ≠ 0), Real.rpow_natCast]
    have hM1 : (1 : ℝ) ≤ ((j ^ (2 * r) : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j ^ (2 * r))
    have hpow_le : (j : ℝ) ^ (r - 1) ≤ ((j ^ (2 * r) : ℕ) : ℝ) ^ c := by
      rw [hrpow_id]
      exact Real.rpow_le_rpow_of_exponent_le hM1 hc
    rw [hdecomp, add_div]
    nlinarith

/-- **General even-power (`M = j^(2*r)`, `D = j^(2*r - 1)`) one-sided lower dilation-tail strip law.** -/
theorem zetaZeroAbscissa_le_half_add_of_neg_rpow_le_dilationTail_even_pow
    {r : ℕ} {C c : ℝ} (hr : 1 ≤ r) (hC0 : 0 ≤ C)
    (hc : ((r - 1 : ℕ) : ℝ) / ((2 * r : ℕ) : ℝ) ≤ c)
    (htail : ∀ j : ℕ, 2 ≤ j →
      -(C + C * ((j ^ (2 * r) : ℕ) : ℝ) ^ c) ≤
        mobiusDivisorDilationTail (j ^ (2 * r)) (j ^ (2 * r - 1)) / ((j ^ (2 * r) : ℕ) : ℝ)) :
    zetaZeroAbscissa ≤ 1 / 2 + c := by
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  have hm : 1 ≤ 2 * r := by omega
  have hle := zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_mobiusDivisorSquareRootAbel_pow
    (m := 2 * r) (M := C + 3 / 5) (c := c) hm (by positivity) (fun j hj => ?_)
  · rwa [max_eq_right hc0] at hle
  · have hj2 : 2 ≤ j := by
      by_contra hlt
      have hj1 : j ≤ 1 := by omega
      have hpow1 : j ^ (2 * r) ≤ 1 := by
        calc j ^ (2 * r) ≤ 1 ^ (2 * r) := Nat.pow_le_pow_left hj1 (2 * r)
          _ = 1 := one_pow _
      omega
    have hj1 : 1 ≤ j := by omega
    have hdecomp := mobiusDivisorSquareRootAbelMoment_eq_dilationHead_add_dilationTail
      (j ^ (2 * r)) (j ^ (2 * r - 1))
    have hhead := (abs_le.mp (abs_mobiusDivisorDilationHead_even_pow_div_le hr hj1)).1
    have hht := htail j hj2
    have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
    have hrpow_id : (j : ℝ) ^ (r - 1) =
        ((j ^ (2 * r) : ℕ) : ℝ) ^ (((r - 1 : ℕ) : ℝ) / ((2 * r : ℕ) : ℝ)) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast (j : ℝ) (2 * r), ← Real.rpow_mul hj_pos.le,
        mul_div_cancel₀ _ (by positivity : ((2 * r : ℕ) : ℝ) ≠ 0), Real.rpow_natCast]
    have hM1 : (1 : ℝ) ≤ ((j ^ (2 * r) : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j ^ (2 * r))
    have hpow_le : (j : ℝ) ^ (r - 1) ≤ ((j ^ (2 * r) : ℕ) : ℝ) ^ c := by
      rw [hrpow_id]
      exact Real.rpow_le_rpow_of_exponent_le hM1 hc
    rw [hdecomp, add_div]
    nlinarith

/-- **Exact 6th-power (`M = j^6`, `D = j^5`) one-sided upper tail criterion for `1/6 ≤ Re(ρ) ≤ 5/6`.**
Because `mobiusDivisorDilationTail (j^6) (j^5)` sums over only `j - 1` quotients `1 ≤ q ≤ j - 1`,
an upper bound `mobiusDivisorDilationTail (j^6) (j^5) ≤ C * j^8` along `j ≥ 2` unconditionally
forces `zetaZeroAbscissa ≤ 5 / 6`. -/
theorem zetaZeroAbscissa_le_five_sixths_of_dilationTail_pow_six_le
    {C : ℝ} (hC0 : 0 ≤ C)
    (htail : ∀ j : ℕ, 2 ≤ j →
      mobiusDivisorDilationTail (j ^ 6) (j ^ 5) ≤ C * (j : ℝ) ^ 8) :
    zetaZeroAbscissa ≤ 5 / 6 := by
  have h := zetaZeroAbscissa_le_half_add_of_dilationTail_even_pow_le_rpow
    (r := 3) (C := C) (c := 1 / 3) (by omega) hC0 (by norm_num) (fun j hj => ?_)
  · linarith
  · have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
    have hM_pos : (0 : ℝ) < ((j ^ 6 : ℕ) : ℝ) := by positivity
    have hrpow : ((j ^ 6 : ℕ) : ℝ) ^ (1 / 3 : ℝ) = (j : ℝ) ^ 2 := by
      push_cast
      rw [← Real.rpow_natCast (j : ℝ) 6, ← Real.rpow_mul hj_pos.le]
      norm_num
    have hdiv : mobiusDivisorDilationTail (j ^ 6) (j ^ 5) / ((j ^ 6 : ℕ) : ℝ) ≤
        C * (j : ℝ) ^ 2 := by
      rw [div_le_iff₀ hM_pos]
      calc mobiusDivisorDilationTail (j ^ 6) (j ^ 5)
        _ ≤ C * (j : ℝ) ^ 8 := htail j hj
        _ = C * (j : ℝ) ^ 2 * ((j ^ 6 : ℕ) : ℝ) := by push_cast; ring
    change mobiusDivisorDilationTail (j ^ 6) (j ^ 5) / ((j ^ 6 : ℕ) : ℝ) ≤
      C + C * ((j ^ 6 : ℕ) : ℝ) ^ (1 / 3 : ℝ)
    rw [hrpow]
    linarith

/-- **Exact 6th-power (`M = j^6`, `D = j^5`) one-sided lower tail criterion for `1/6 ≤ Re(ρ) ≤ 5/6`.** -/
theorem zetaZeroAbscissa_le_five_sixths_of_neg_le_dilationTail_pow_six
    {C : ℝ} (hC0 : 0 ≤ C)
    (htail : ∀ j : ℕ, 2 ≤ j →
      -(C * (j : ℝ) ^ 8) ≤ mobiusDivisorDilationTail (j ^ 6) (j ^ 5)) :
    zetaZeroAbscissa ≤ 5 / 6 := by
  have h := zetaZeroAbscissa_le_half_add_of_neg_rpow_le_dilationTail_even_pow
    (r := 3) (C := C) (c := 1 / 3) (by omega) hC0 (by norm_num) (fun j hj => ?_)
  · linarith
  · have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
    have hM_pos : (0 : ℝ) < ((j ^ 6 : ℕ) : ℝ) := by positivity
    have hrpow : ((j ^ 6 : ℕ) : ℝ) ^ (1 / 3 : ℝ) = (j : ℝ) ^ 2 := by
      push_cast
      rw [← Real.rpow_natCast (j : ℝ) 6, ← Real.rpow_mul hj_pos.le]
      norm_num
    have hdiv : -(C * (j : ℝ) ^ 2) ≤
        mobiusDivisorDilationTail (j ^ 6) (j ^ 5) / ((j ^ 6 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hM_pos]
      calc -(C * (j : ℝ) ^ 2) * ((j ^ 6 : ℕ) : ℝ)
        _ = -(C * (j : ℝ) ^ 8) := by push_cast; ring
        _ ≤ mobiusDivisorDilationTail (j ^ 6) (j ^ 5) := htail j hj
    change -(C + C * ((j ^ 6 : ℕ) : ℝ) ^ (1 / 3 : ℝ)) ≤
      mobiusDivisorDilationTail (j ^ 6) (j ^ 5) / ((j ^ 6 : ℕ) : ℝ)
    rw [hrpow]
    linarith

/-- **Exact 4th-power (`M = j^4`, `D = j^3`) one-sided upper tail criterion for `1/4 ≤ Re(ρ) ≤ 3/4`.**
Because `mobiusDivisorDilationTail (j^4) (j^3)` sums over only `j - 1` quotients `1 ≤ q ≤ j - 1`,
an upper bound `mobiusDivisorDilationTail (j^4) (j^3) ≤ C * j^5` along `j ≥ 2` unconditionally
forces `zetaZeroAbscissa ≤ 3 / 4`. -/
theorem zetaZeroAbscissa_le_three_quarters_of_dilationTail_pow_four_le
    {C : ℝ} (hC0 : 0 ≤ C)
    (htail : ∀ j : ℕ, 2 ≤ j →
      mobiusDivisorDilationTail (j ^ 4) (j ^ 3) ≤ C * (j : ℝ) ^ 5) :
    zetaZeroAbscissa ≤ 3 / 4 := by
  have h := zetaZeroAbscissa_le_half_add_of_dilationTail_even_pow_le_rpow
    (r := 2) (C := C) (c := 1 / 4) (by omega) hC0 (by norm_num) (fun j hj => ?_)
  · linarith
  · have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
    have hM_pos : (0 : ℝ) < ((j ^ 4 : ℕ) : ℝ) := by positivity
    have hrpow : ((j ^ 4 : ℕ) : ℝ) ^ (1 / 4 : ℝ) = (j : ℝ) := by
      push_cast
      rw [← Real.rpow_natCast (j : ℝ) 4, ← Real.rpow_mul hj_pos.le]
      norm_num
    have hdiv : mobiusDivisorDilationTail (j ^ 4) (j ^ 3) / ((j ^ 4 : ℕ) : ℝ) ≤
        C * (j : ℝ) := by
      rw [div_le_iff₀ hM_pos]
      calc mobiusDivisorDilationTail (j ^ 4) (j ^ 3)
        _ ≤ C * (j : ℝ) ^ 5 := htail j hj
        _ = C * (j : ℝ) * ((j ^ 4 : ℕ) : ℝ) := by push_cast; ring
    change mobiusDivisorDilationTail (j ^ 4) (j ^ 3) / ((j ^ 4 : ℕ) : ℝ) ≤
      C + C * ((j ^ 4 : ℕ) : ℝ) ^ (1 / 4 : ℝ)
    rw [hrpow]
    linarith

/-- **Exact 4th-power (`M = j^4`, `D = j^3`) one-sided lower tail criterion for `1/4 ≤ Re(ρ) ≤ 3/4`.** -/
theorem zetaZeroAbscissa_le_three_quarters_of_neg_le_dilationTail_pow_four
    {C : ℝ} (hC0 : 0 ≤ C)
    (htail : ∀ j : ℕ, 2 ≤ j →
      -(C * (j : ℝ) ^ 5) ≤ mobiusDivisorDilationTail (j ^ 4) (j ^ 3)) :
    zetaZeroAbscissa ≤ 3 / 4 := by
  have h := zetaZeroAbscissa_le_half_add_of_neg_rpow_le_dilationTail_even_pow
    (r := 2) (C := C) (c := 1 / 4) (by omega) hC0 (by norm_num) (fun j hj => ?_)
  · linarith
  · have hj_pos : (0 : ℝ) < (j : ℝ) := by positivity
    have hM_pos : (0 : ℝ) < ((j ^ 4 : ℕ) : ℝ) := by positivity
    have hrpow : ((j ^ 4 : ℕ) : ℝ) ^ (1 / 4 : ℝ) = (j : ℝ) := by
      push_cast
      rw [← Real.rpow_natCast (j : ℝ) 4, ← Real.rpow_mul hj_pos.le]
      norm_num
    have hdiv : -(C * (j : ℝ)) ≤
        mobiusDivisorDilationTail (j ^ 4) (j ^ 3) / ((j ^ 4 : ℕ) : ℝ) := by
      rw [le_div_iff₀ hM_pos]
      calc -(C * (j : ℝ)) * ((j ^ 4 : ℕ) : ℝ)
        _ = -(C * (j : ℝ) ^ 5) := by push_cast; ring
        _ ≤ mobiusDivisorDilationTail (j ^ 4) (j ^ 3) := htail j hj
    change -(C + C * ((j ^ 4 : ℕ) : ℝ) ^ (1 / 4 : ℝ)) ≤
      mobiusDivisorDilationTail (j ^ 4) (j ^ 3) / ((j ^ 4 : ℕ) : ℝ)
    rw [hrpow]
    linarith

/-! ## Section 3: Unweighted Square-Sample Chebyshev Sum & Observer-Jet / `lagBracketSlope` Abscissa Laws -/

/-- **Unconditional forward abscissa bound for the unweighted square-sample Chebyshev sum.**
For every `ε > 0`, there exists `C ≥ 0` such that for all `N ≥ 2`,
`|∑_{1 ≤ s < N} psiRemainder (s^2)| / N^2 ≤ C * (N^2)^(zetaZeroAbscissa - 1/2 + ε)`. -/
theorem exists_psiRemainder_squareSum_zetaZeroAbscissa_rpow_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      |∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)| / ((N : ℝ) ^ 2) ≤
        C * ((N ^ 2 : ℕ) : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  obtain ⟨C₀, hC₀, hAbel⟩ := exists_mobiusDivisorSquareRootAbelMoment_subpower_zetaZeroAbscissa ε hε
  let K : ℝ := 9 + |2 * Real.eulerMascheroniConstant|
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C₀ + K, by positivity, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hsq2 : 2 ≤ N ^ 2 := by nlinarith
  have hNsq_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hdiff := abs_mobiusDivisorSquareRootAbel_sub_psiRemainder_squareSum_le hN1
  have hab : |∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)| ≤
      |mobiusDivisorSquareRootAbelMoment (N ^ 2)| + K * (N : ℝ) ^ 2 := by
    have h1 := abs_sub_comm (mobiusDivisorSquareRootAbelMoment (N ^ 2))
      (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2))
    have h2 := abs_sub_abs_le_abs_sub (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2))
      (mobiusDivisorSquareRootAbelMoment (N ^ 2))
    dsimp [K]
    linarith
  have hdiv_le : |∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)| / ((N : ℝ) ^ 2) ≤
      |mobiusDivisorSquareRootAbelMoment (N ^ 2) / ((N ^ 2 : ℕ) : ℝ)| + K := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((N ^ 2 : ℕ) : ℝ)),
      Nat.cast_pow, div_le_iff₀ hNsq_pos, add_mul, div_mul_cancel₀ _ hNsq_pos.ne']
    exact hab
  have h1le : (1 : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
    apply Real.one_le_rpow
    · exact_mod_cast (by omega : 1 ≤ N ^ 2)
    · linarith [half_le_zetaZeroAbscissa]
  have hA := hAbel (N ^ 2) hsq2
  calc |∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)| / ((N : ℝ) ^ 2)
    _ ≤ C₀ * ((N ^ 2 : ℕ) : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) + K * 1 := by linarith
    _ ≤ C₀ * ((N ^ 2 : ℕ) : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) +
        K * ((N ^ 2 : ℕ) : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left h1le hK0)
    _ = (C₀ + K) * ((N ^ 2 : ℕ) : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by ring

/-- One-sided upper strip law for `zetaZeroAbscissa` via the unweighted square-sample sum. -/
theorem zetaZeroAbscissa_le_half_add_max_of_psiRemainder_squareSum_le_rpow
    {M c : ℝ} {N₀ : ℕ} (hM : 0 ≤ M)
    (hup : ∀ N : ℕ, N₀ ≤ N →
      (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) ≤
        M * (N : ℝ) ^ 2 + M * (N : ℝ) ^ (2 + 2 * c)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound (le_max_left 0 c) (fun ρ hρ => ?_)
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_psiRemainder_squareSum_le_rpow hM hup q
  linarith [(abs_le.mp h).2]

/-- One-sided lower strip law for `zetaZeroAbscissa` via the unweighted square-sample sum. -/
theorem zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_psiRemainder_squareSum
    {M c : ℝ} {N₀ : ℕ} (hM : 0 ≤ M)
    (hlow : ∀ N : ℕ, N₀ ≤ N →
      -(M * (N : ℝ) ^ 2 + M * (N : ℝ) ^ (2 + 2 * c)) ≤
        ∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound (le_max_left 0 c) (fun ρ hρ => ?_)
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_neg_rpow_le_psiRemainder_squareSum hM hlow q
  linarith [(abs_le.mp h).2]

/-- The set of nonnegative one-sided upper growth exponents `c ≥ 0` for the unweighted
square-sample Chebyshev sum `(∑_{1 ≤ s < N} psiRemainder (s^2)) / N^2`. -/
def psiRemainderSquareSumUpperExponentSet : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) / ((N : ℝ) ^ 2) ≤
      C * ((N ^ 2 : ℕ) : ℝ) ^ c}

/-- The set of nonnegative one-sided lower growth exponents `c ≥ 0` for the unweighted
square-sample Chebyshev sum `(∑_{1 ≤ s < N} psiRemainder (s^2)) / N^2`. -/
def psiRemainderSquareSumLowerExponentSet : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
    -(C * ((N ^ 2 : ℕ) : ℝ) ^ c) ≤
      (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) / ((N : ℝ) ^ 2)}

/-- **Exact `sInf` abscissa formula for the unweighted square-sample Chebyshev sum (upper bound).** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_psiRemainder_squareSum_upper :
    zetaZeroAbscissa = 1 / 2 + sInf psiRemainderSquareSumUpperExponentSet := by
  have hbdd : BddBelow psiRemainderSquareSumUpperExponentSet := ⟨0, fun _ hc => hc.1⟩
  have hmem : ∀ ε : ℝ, 0 < ε →
      zetaZeroAbscissa - 1 / 2 + ε ∈ psiRemainderSquareSumUpperExponentSet := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := exists_psiRemainder_squareSum_zetaZeroAbscissa_rpow_bound hε
    refine ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0, fun N hN => ?_⟩
    have hNsq_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    exact (div_le_div_of_nonneg_right (le_abs_self _) hNsq_pos.le).trans (hC N hN)
  have h1 : zetaZeroAbscissa - 1 / 2 ≤ sInf psiRemainderSquareSumUpperExponentSet := by
    refine le_csInf ⟨zetaZeroAbscissa - 1 / 2 + 1, hmem 1 zero_lt_one⟩ ?_
    rintro c ⟨hc0, C, hC0, hC⟩
    have hup : ∀ N : ℕ, 2 ≤ N →
        (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) ≤
          C * (N : ℝ) ^ 2 + C * (N : ℝ) ^ (2 + 2 * c) := by
      intro N hN
      have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
      have hNsq_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      have hdiv := (div_le_iff₀ hNsq_pos).mp (hC N hN)
      have hrpow : ((N ^ 2 : ℕ) : ℝ) ^ c * (N : ℝ) ^ 2 = (N : ℝ) ^ (2 + 2 * c) := by
        push_cast
        rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_mul hN_pos.le,
          ← Real.rpow_add hN_pos]
        ring_nf
      rw [mul_assoc, hrpow] at hdiv
      have h0 : 0 ≤ C * (N : ℝ) ^ 2 := by positivity
      linarith
    have hle := zetaZeroAbscissa_le_half_add_max_of_psiRemainder_squareSum_le_rpow hC0 hup
    rw [max_eq_right hc0] at hle
    linarith
  have h2 : sInf psiRemainderSquareSumUpperExponentSet ≤ zetaZeroAbscissa - 1 / 2 := by
    by_contra hlt
    push Not at hlt
    set δ : ℝ := (sInf psiRemainderSquareSumUpperExponentSet - (zetaZeroAbscissa - 1 / 2)) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hcs := csInf_le hbdd (hmem δ hδ)
    dsimp [δ] at hcs
    linarith
  linarith

/-- **Exact `sInf` abscissa formula for the unweighted square-sample Chebyshev sum (lower bound).** -/
theorem zetaZeroAbscissa_eq_half_add_sInf_psiRemainder_squareSum_lower :
    zetaZeroAbscissa = 1 / 2 + sInf psiRemainderSquareSumLowerExponentSet := by
  have hbdd : BddBelow psiRemainderSquareSumLowerExponentSet := ⟨0, fun _ hc => hc.1⟩
  have hmem : ∀ ε : ℝ, 0 < ε →
      zetaZeroAbscissa - 1 / 2 + ε ∈ psiRemainderSquareSumLowerExponentSet := by
    intro ε hε
    obtain ⟨C, hC0, hC⟩ := exists_psiRemainder_squareSum_zetaZeroAbscissa_rpow_bound hε
    refine ⟨by linarith [half_le_zetaZeroAbscissa], C, hC0, fun N hN => ?_⟩
    have hNsq_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have hneg : -(|∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)| / ((N : ℝ) ^ 2)) ≤
        (∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2)) / ((N : ℝ) ^ 2) := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (neg_abs_le _) hNsq_pos.le
    exact (neg_le_neg (hC N hN)).trans hneg
  have h1 : zetaZeroAbscissa - 1 / 2 ≤ sInf psiRemainderSquareSumLowerExponentSet := by
    refine le_csInf ⟨zetaZeroAbscissa - 1 / 2 + 1, hmem 1 zero_lt_one⟩ ?_
    rintro c ⟨hc0, C, hC0, hC⟩
    have hlow : ∀ N : ℕ, 2 ≤ N →
        -(C * (N : ℝ) ^ 2 + C * (N : ℝ) ^ (2 + 2 * c)) ≤
          ∑ s ∈ Finset.Ico 1 N, psiRemainder (s ^ 2) := by
      intro N hN
      have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
      have hNsq_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      have hdiv := (le_div_iff₀ hNsq_pos).mp (hC N hN)
      have hrpow : ((N ^ 2 : ℕ) : ℝ) ^ c * (N : ℝ) ^ 2 = (N : ℝ) ^ (2 + 2 * c) := by
        push_cast
        rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_mul hN_pos.le,
          ← Real.rpow_add hN_pos]
        ring_nf
      rw [neg_mul, mul_assoc, hrpow] at hdiv
      have h0 : 0 ≤ C * (N : ℝ) ^ 2 := by positivity
      linarith
    have hle := zetaZeroAbscissa_le_half_add_max_of_neg_rpow_le_psiRemainder_squareSum hC0 hlow
    rw [max_eq_right hc0] at hle
    linarith
  have h2 : sInf psiRemainderSquareSumLowerExponentSet ≤ zetaZeroAbscissa - 1 / 2 := by
    by_contra hlt
    push Not at hlt
    set δ : ℝ := (sInf psiRemainderSquareSumLowerExponentSet - (zetaZeroAbscissa - 1 / 2)) / 2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hcs := csInf_le hbdd (hmem δ hδ)
    dsimp [δ] at hcs
    linarith
  linarith

/-- One-sided strip law for `zetaZeroAbscissa` via `completedSourceObserverJetPositiveHistoryAction`. -/
theorem zetaZeroAbscissa_le_half_add_max_of_completedSourceObserverJetPositiveHistory_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hpos : ∀ M : ℕ, 3 ≤ M →
      completedSourceObserverJetPositiveHistoryAction M ≤
        C * (M : ℝ) + C * (M : ℝ) ^ (1 + c)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound (le_max_left 0 c) (fun ρ hρ => ?_)
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_completedSourceObserverJetPositiveHistory_le_rpow hC0 hpos q
  linarith [(abs_le.mp h).2]

/-- One-sided strip law for `zetaZeroAbscissa` via `completedSourceObserverJetNegativeHistoryAction`. -/
theorem zetaZeroAbscissa_le_half_add_max_of_completedSourceObserverJetNegativeHistory_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hneg : ∀ M : ℕ, 3 ≤ M →
      completedSourceObserverJetNegativeHistoryAction M ≤
        C * (M : ℝ) + C * (M : ℝ) ^ (1 + c)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound (le_max_left 0 c) (fun ρ hρ => ?_)
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_completedSourceObserverJetNegativeHistory_le_rpow hC0 hneg q
  linarith [(abs_le.mp h).2]

/-- One-sided strip law for `zetaZeroAbscissa` via the prime-free `lagBracketSlopePositiveTailAction`. -/
theorem zetaZeroAbscissa_le_half_add_max_of_lagBracketSlopePositiveTailAction_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hpos : ∀ M : ℕ, 3 ≤ M →
      lagBracketSlopePositiveTailAction M ≤
        C * (M : ℝ) + C * (M : ℝ) ^ (1 + c)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound (le_max_left 0 c) (fun ρ hρ => ?_)
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_lagBracketSlopePositiveTailAction_le_rpow hC0 hpos q
  linarith [(abs_le.mp h).2]

/-- One-sided strip law for `zetaZeroAbscissa` via the prime-free `lagBracketSlopeNegativeTailAction`. -/
theorem zetaZeroAbscissa_le_half_add_max_of_lagBracketSlopeNegativeTailAction_le_rpow
    {C c : ℝ} (hC0 : 0 ≤ C)
    (hneg : ∀ M : ℕ, 3 ≤ M →
      lagBracketSlopeNegativeTailAction M ≤
        C * (M : ℝ) + C * (M : ℝ) ^ (1 + c)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound (le_max_left 0 c) (fun ρ hρ => ?_)
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_lagBracketSlopeNegativeTailAction_le_rpow hC0 hneg q
  linarith [(abs_le.mp h).2]

/-! ## Section 4: Exceptional Power-Gap `integerLag` Abscissa Laws (`WeilLagPowerGapExceptionalSampling`) -/

/-- **Power-gap upper `integerLag` sampling with exponential exceptions forces `zetaZeroAbscissa ≤ 1/2 + max 0 c`.**
Even if `integerLag k ≤ M + M * k^c` is only sampled in backward power-gap windows
`[⌊e^u⌋ - K ⌊e^u⌋^(1 - δ), ⌊e^u⌋]` outside a measurable log-scale exceptional set `S` with
`∫_S e^(κ u) du < ∞` (`κ > 0`), `zetaZeroAbscissa ≤ 1 / 2 + max 0 c` holds unconditionally. -/
theorem zetaZeroAbscissa_le_half_add_max_of_powerGaps_integerLag_le_rpow_except
    {A : Set ℕ} {M c K δ κ : ℝ} {S : Set ℝ}
    (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hA : ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M + M * (k : ℝ) ^ c)
    (hgap : ∀ᶠ u : ℝ in atTop, u ∉ S →
      ∃ k ∈ A, k ≤ ⌊Real.exp u⌋₊ ∧
        (⌊Real.exp u⌋₊ : ℝ) - k ≤ K * (⌊Real.exp u⌋₊ : ℝ) ^ (1 - δ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound (le_max_left 0 c) (fun ρ hρ => ?_)
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_powerGaps_integerLag_le_rpow_except
    hM0 hδ hK hκ hS hSint hA hgap q
  linarith [(abs_le.mp h).2]

/-- **Power-gap lower `integerLag` sampling with exponential exceptions forces `zetaZeroAbscissa ≤ 1/2 + max 0 c`.** -/
theorem zetaZeroAbscissa_le_half_add_max_of_powerGaps_neg_rpow_le_integerLag_except
    {A : Set ℕ} {M c K δ κ : ℝ} {S : Set ℝ}
    (hM0 : 0 ≤ M) (hδ : 0 < δ) (hK : 0 ≤ K) (hκ : 0 < κ) (hS : MeasurableSet S)
    (hSint : IntegrableOn (fun u => Real.exp (κ * u)) S)
    (hA : ∀ k ∈ A, 2 ≤ k → -(M + M * (k : ℝ) ^ c) ≤ integerLag k)
    (hgap : ∀ᶠ u : ℝ in atTop, u ∉ S →
      ∃ k ∈ A, k ≤ ⌊Real.exp u⌋₊ ∧
        (⌊Real.exp u⌋₊ : ℝ) - k ≤ K * (⌊Real.exp u⌋₊ : ℝ) ^ (1 - δ)) :
    zetaZeroAbscissa ≤ 1 / 2 + max 0 c := by
  refine zetaZeroAbscissa_le_of_xiZeroHalfPlaneBound (le_max_left 0 c) (fun ρ hρ => ?_)
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have h := abs_re_sub_half_le_of_powerGaps_neg_rpow_le_integerLag_except
    hM0 hδ hK hκ hS hSint hA hgap q
  linarith [(abs_le.mp h).2]

end

end RHTower
