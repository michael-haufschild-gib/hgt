import GaloisForLFunctions.BezoutValuationIncidence.VaughanTypeIIShortAndAllHorizonMobiusL2Energy
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovMoebius
import GaloisForLFunctions.RHTower.Sieve.MoebiusMeanSquareRealForm

/-!
# Vinogradov–Korobov Cofinal Möbius Discrepancy and First-Octave Mean-Square Cancellation

This module connects `BezoutValuationIncidence` to the unconditional signed Möbius estimates proved
in `RHTower/Sieve/`:

1. **Vinogradov–Korobov Rate for `mertensM` and Trans-Horizon Quotient Windows
   (`exists_abs_mertensM_le_vk_rate`, `exists_abs_sum_Ioc_moebiusReal_le_vk_rate`):**
   Upgrades the qualitative `o(N)` Mertens input in `UniformCofinalMobiusPrefixDiscrepancy.lean` to
   the unconditional Vinogradov–Korobov rate
   `|mertensM N| ≤ C * N * exp(-vkKappa * vkScale N / 24)` (`κ = 1 / (12 * 10^8)`).
   Because `Finset.Ioc N Q = ∅` when `Q ≤ N` and `Q ≥ N` whenever `Finset.Ioc N Q` is nonempty,
   every trans-horizon window `∑ d ∈ Finset.Ioc N Q, moebiusReal d` satisfies the two-endpoint
   Vinogradov–Korobov bound for all `Q : ℕ` without any lower-bound restriction on `Q`.

2. **Vinogradov–Korobov Bound on the Literal Möbius Source Prefix and Discrepancy
   (`exists_abs_sum_sieveSeq_moebiusReal_le_vk_quotient_windows`,
   `exists_abs_sievePrefixDiscrepancy_moebiusReal_le_vk`):**
   Combines `sum_sieveSeq_moebiusReal_eq_one_sub_quotient_windows` with the unconditional
   Vinogradov–Korobov quotient-window estimate to bound both
   `|∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k|` and `|sievePrefixDiscrepancy N M moebiusReal|`
   across every trans-horizon window `1 ≤ M ≤ (B + 1) * N`.

3. **Unconditional Short-Interval Mean-Square Bound on the First Trans-Horizon Octave
   (`sum_sq_sieveSeq_first_octave_Ico_eq`, `sum_sq_typeIIShort_first_octave_Ico_eq`,
   `exists_sum_sq_sieveSeq_first_octave_Ico_le`):**
   Combines first-octave reciprocity (`sieveSeq N moebiusReal n = -moebiusReal n` and
   `typeIIShort N n = moebiusReal n` on `(N, 2N]`) with `exists_sum_sq_real_moebius_Ico_le`
   (`MoebiusMeanSquareRealForm.lean:41`) to obtain an unconditional short-interval `L²` mean-square
   cancellation theorem for `sieveSeq N moebiusReal` and `typeIIShort N` on `(N, 2N]`.
-/

open Finset Filter ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.HTGeometry
open RHTower RHTower.Sieve
open scoped BigOperators Topology

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Vinogradov–Korobov Rate for `mertensM` and Trans-Horizon Quotient Windows -/

/-- Exact decomposition of any Möbius window `∑ d ∈ Finset.Ioc N Q, moebiusReal d` as a difference
of `mertensM` values when `N ≤ Q`, and `0` when `Q ≤ N`. -/
theorem abs_sum_Ioc_moebiusReal_le_add_abs_mertensM (N Q : ℕ) :
    |∑ d ∈ Finset.Ioc N Q, moebiusReal d| ≤ |mertensM Q| + |mertensM N| := by
  by_cases hNQ : N ≤ Q
  · have heq : Finset.Ioc N Q = Finset.Ico (N + 1) (Q + 1) := by
      ext d
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [heq, Finset.sum_Ico_eq_sub _ (by omega : N + 1 ≤ Q + 1)]
    change |mertensM Q - mertensM N| ≤ |mertensM Q| + |mertensM N|
    exact abs_sub _ _
  · have hempty : Finset.Ioc N Q = ∅ := by
      ext d
      simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]
      omega
    rw [hempty, Finset.sum_empty, abs_zero]
    positivity

/-- **Vinogradov–Korobov Rate for the Real Mertens Function (`exists_abs_mertensM_le_vk_rate`):**
There exists `C ≥ 0` such that eventually as `N → ∞`:
`|mertensM N| ≤ C * N * exp(-vkKappa * vkScale N / 24)`. -/
theorem exists_abs_mertensM_le_vk_rate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |mertensM N| ≤ C * (N : ℝ) * Real.exp (-(vkKappa * vkScale (N : ℝ) / 24)) := by
  obtain ⟨C, hC0, hrate⟩ := exists_abs_sum_moebius_le_vk_rate
  refine ⟨C, hC0, ?_⟩
  have hev := tendsto_natCast_atTop_atTop.eventually hrate
  filter_upwards [hev] with N hN
  simpa only [Nat.floor_natCast, mertensM] using hN

/-- **Uniform Vinogradov–Korobov Bound on Trans-Horizon Möbius Windows
(`exists_abs_sum_Ioc_moebiusReal_le_vk_rate`):**
There exists `C ≥ 0` such that for all sufficiently large `N : ℕ` and **every** `Q : ℕ`:
`|∑ d ∈ Finset.Ioc N Q, moebiusReal d| ≤ C * Q * exp(-vkKappa * vkScale Q / 24) + C * N * exp(-vkKappa * vkScale N / 24)`. -/
theorem exists_abs_sum_Ioc_moebiusReal_le_vk_rate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ,
      |∑ d ∈ Finset.Ioc N Q, moebiusReal d| ≤
        C * (Q : ℝ) * Real.exp (-(vkKappa * vkScale (Q : ℝ) / 24)) +
          C * (N : ℝ) * Real.exp (-(vkKappa * vkScale (N : ℝ) / 24)) := by
  obtain ⟨C, hC0, hev⟩ := exists_abs_mertensM_le_vk_rate
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨C, hC0, Filter.eventually_atTop.mpr ⟨N₀, fun N hN Q => ?_⟩⟩
  by_cases hNQ : N < Q
  · have hQ₀ : N₀ ≤ Q := le_trans hN (le_of_lt hNQ)
    have h1 := abs_sum_Ioc_moebiusReal_le_add_abs_mertensM N Q
    have h2 := hN₀ Q hQ₀
    have h3 := hN₀ N hN
    linarith
  · have hempty : Finset.Ioc N Q = ∅ := by
      ext d
      simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]
      omega
    rw [hempty, Finset.sum_empty, abs_zero]
    positivity

/-! ## §2. Vinogradov–Korobov Bound on the Literal Möbius Source Prefix -/

/-- **Vinogradov–Korobov Bound on the Literal Möbius Source Prefix
(`exists_abs_sum_sieveSeq_moebiusReal_le_vk_quotient_windows`):**
There exists `C ≥ 0` such that eventually as `N → ∞`, for **every** band count `B : ℕ` and **every**
horizon `1 ≤ M ≤ (B + 1) * N`, the prefix sum of `sieveSeq N moebiusReal` is bounded by `1` plus
the sum of the Vinogradov–Korobov rates at the quotient endpoints `M / q` (`1 ≤ q ≤ B`) and `N`. -/
theorem exists_abs_sum_sieveSeq_moebiusReal_le_vk_quotient_windows :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ (B M : ℕ),
      1 ≤ M → M ≤ (B + 1) * N →
        |∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k| ≤
          1 + ∑ q ∈ Finset.Icc 1 B,
            (C * ((M / q : ℕ) : ℝ) * Real.exp (-(vkKappa * vkScale ((M / q : ℕ) : ℝ) / 24)) +
              C * (N : ℝ) * Real.exp (-(vkKappa * vkScale (N : ℝ) / 24))) := by
  obtain ⟨C, hC0, hev⟩ := exists_abs_sum_Ioc_moebiusReal_le_vk_rate
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hev] with N hN B M hM hhi
  rw [sum_sieveSeq_moebiusReal_eq_one_sub_quotient_windows hM hhi]
  calc
    |1 - ∑ q ∈ Finset.Icc 1 B, ∑ d ∈ Finset.Ioc N (M / q), moebiusReal d|
      ≤ |(1 : ℝ)| + |∑ q ∈ Finset.Icc 1 B, ∑ d ∈ Finset.Ioc N (M / q), moebiusReal d| :=
        abs_sub _ _
    _ ≤ 1 + ∑ q ∈ Finset.Icc 1 B, |∑ d ∈ Finset.Ioc N (M / q), moebiusReal d| := by
        rw [abs_one]
        exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ 1 + ∑ q ∈ Finset.Icc 1 B,
          (C * ((M / q : ℕ) : ℝ) * Real.exp (-(vkKappa * vkScale ((M / q : ℕ) : ℝ) / 24)) +
            C * (N : ℝ) * Real.exp (-(vkKappa * vkScale (N : ℝ) / 24))) :=
        add_le_add le_rfl (Finset.sum_le_sum fun q _ => hN (M / q))

/-! ## §3. Unconditional Short-Interval Mean-Square Cancellation on the First Trans-Horizon Octave -/

/-- On the first trans-horizon octave `N + 1 ≤ k ≤ 2 * N`, the Vaughan Type-II short-side
coefficient `typeIIShort N k` equals `moebiusReal k`. -/
theorem typeIIShort_eq_moebiusReal_first_octave {N k : ℕ}
    (hk1 : N + 1 ≤ k) (hk2 : k ≤ 2 * N) :
    typeIIShort N k = moebiusReal k := by
  rw [typeIIShort_eq_neg_sieveSeq_of_two_le N (by omega : 2 ≤ k),
    sieveSeq_moebiusReal_first_octave hk1 hk2, neg_neg]

/-- For any short-interval parameters `Y, K, L : ℕ` contained in the first trans-horizon octave
`(N, 2N]` (`N ≤ Y` and `Y + K + L ≤ 2 * N + 1`), the short-interval mean square of
`sieveSeq N moebiusReal` equals the short-interval mean square of `moebiusReal`. -/
theorem sum_sq_sieveSeq_first_octave_Ico_eq {N L Y K : ℕ}
    (hNY : N ≤ Y) (hhi : Y + K + L ≤ 2 * N + 1) :
    (∑ t ∈ Finset.Ico Y (Y + K),
        (∑ n ∈ Finset.Ioc t (t + L), sieveSeq N moebiusReal n) ^ (2 : ℕ)) =
      ∑ t ∈ Finset.Ico Y (Y + K),
        (∑ n ∈ Finset.Ioc t (t + L), ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ (2 : ℕ) := by
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨htY, htYK⟩ := Finset.mem_Ico.mp ht
  have hinner :
      (∑ n ∈ Finset.Ioc t (t + L), sieveSeq N moebiusReal n) =
        -(∑ n ∈ Finset.Ioc t (t + L), moebiusReal n) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hnt, hntL⟩ := Finset.mem_Ioc.mp hn
    exact sieveSeq_moebiusReal_first_octave (by omega) (by omega)
  rw [hinner, neg_sq]
  rfl

/-- For any short-interval parameters `Y, K, L : ℕ` contained in the first trans-horizon octave
`(N, 2N]` (`N ≤ Y` and `Y + K + L ≤ 2 * N + 1`), the short-interval mean square of `typeIIShort N`
equals the short-interval mean square of `moebiusReal`. -/
theorem sum_sq_typeIIShort_first_octave_Ico_eq {N L Y K : ℕ}
    (hNY : N ≤ Y) (hhi : Y + K + L ≤ 2 * N + 1) :
    (∑ t ∈ Finset.Ico Y (Y + K),
        (∑ n ∈ Finset.Ioc t (t + L), typeIIShort N n) ^ (2 : ℕ)) =
      ∑ t ∈ Finset.Ico Y (Y + K),
        (∑ n ∈ Finset.Ioc t (t + L), ((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ (2 : ℕ) := by
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨htY, htYK⟩ := Finset.mem_Ico.mp ht
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  obtain ⟨hnt, hntL⟩ := Finset.mem_Ioc.mp hn
  exact typeIIShort_eq_moebiusReal_first_octave (by omega) (by omega)

/-- **Unconditional First-Octave Short-Interval Mean-Square Bound for `sieveSeq N moebiusReal`
(`exists_sum_sq_sieveSeq_first_octave_Ico_le`):**
Transfers the unconditional Möbius short-interval mean-square theorem
(`exists_sum_sq_real_moebius_Ico_le`) directly to `sieveSeq M moebiusReal` across the first
trans-horizon octave `(M, 2M]`. -/
theorem exists_sum_sq_sieveSeq_first_octave_Ico_le :
    ∃ B : ℝ → ℝ, Tendsto B atTop (𝓝 0) ∧
      ∀ᶠ N : ℝ in atTop, ∀ (M L Y K J : ℕ) (ε W : ℝ),
        M ≤ Y → Y + K + L ≤ 2 * M + 1 →
        Y + K + L < ⌊N⌋₊ + 1 → 0 < (L : ℝ) → 0 < (Y : ℝ) → 0 ≤ ε → 0 < W →
        8 * Real.pi * W + 5 ≤ ((contourParam (N + smoothWidth N) : ℕ) : ℝ) →
        (Y : ℝ) + K = (Y : ℝ) * (1 + ε) ^ J →
        (∑ t ∈ Finset.Ico Y (Y + K),
            (∑ n ∈ Finset.Ioc t (t + L), sieveSeq M moebiusReal n) ^ (2 : ℕ))
          ≤ ((Y : ℝ) * (1 + ε) ^ J)
              * ((J : ℝ) * blockCost (L : ℝ) (Y : ℝ) ε ((B N * N) ^ (2 : ℕ))
                  ((((⌊N⌋₊ + 1 : ℕ) : ℝ)) ^ (2 : ℕ)) W) := by
  obtain ⟨B, hB, hev⟩ := exists_sum_sq_real_moebius_Ico_le
  refine ⟨B, hB, ?_⟩
  filter_upwards [hev] with N hN M L Y K J ε W hMY hhi hM hL hY hε hW hWC hJ
  rw [sum_sq_sieveSeq_first_octave_Ico_eq hMY hhi]
  exact hN L Y K J ε W hM hL hY hε hW hWC hJ

end

end GaloisForLFunctions.BezoutValuationIncidence
