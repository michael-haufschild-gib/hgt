import GaloisForLFunctions.BezoutValuationIncidence.PrimeTailCalibrationAndMobiusDefect
import GaloisForLFunctions.BezoutValuationIncidence.DilatedCellScalingAndSecondOctaveFermiJumpBridge

/-!
# Renormalized Combined Prefix Defect, Common-Return Annihilation, and First-Octave Möbius Cancellation

While `PrimeTailCalibrationAndMobiusDefect` shows that the unrenormalized combined defect
`moebiusCombinedPrefixDefect N M = signedLcmFractDefect N M moebiusReal + bezoutSawtoothRemainderForm M N moebiusReal`
equals `M * sieveSuccessorReserve N moebiusReal - 1` on `1 ≤ M ≤ N` and therefore grows at least like
`N / (2 log N)` at `M = N`, any cofinal BVI analysis must retain the exact cancellation between the
combined defect and the diagonal main term `M * sieveSuccessorReserve N c`.

This module establishes the universal calculus of the **renormalized combined prefix defect**
`sieveRenormalizedPrefixDefect N M c = sieveCombinedPrefixDefect N M c - M * sieveSuccessorReserve N c`
for arbitrary sieve weights `c : ℕ → ℝ` and evaluates it explicitly for the literal Möbius source
`c = moebiusReal` across both the sub-horizon bulk `[1, N]` and the **first trans-horizon octave**
`[N + 1, 2N - 1]`:

* `sieveRenormalizedPrefixDefect_eq_succ_sub_sq`,
  `two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary`, &
  `sieveRenormalizedPrefixDefect_succ_sub_eq`:
  For every `N, M : ℕ` and every weight `c : ℕ → ℝ`, the renormalized defect equals
  `∑_{k=1}^M s_{N,c}(k) s_{N,c}(k + 1) - ∑_{k=1}^M s_{N,c}(k)²`, satisfies the exact Dirichlet
  polarization law
  `2 * sieveRenormalizedPrefixDefect N M c = -∑_{k=1}^M (s_{N,c}(k+1) - s_{N,c}(k))² + s_{N,c}(M+1)² - s_{N,c}(1)²`,
  and has forward step difference `s_{N,c}(M + 1) * (s_{N,c}(M + 2) - s_{N,c}(M + 1))`.
* `signedLcmFractDefect_eq_zero_of_common_return`,
  `bezoutSawtoothRemainderForm_eq_zero_of_common_return`, &
  `sieveCombinedPrefixDefect_factorial_mul_eq_zero`:
  At every common divisibility return time `M` (`∀ d ∈ [1, N], d ∣ M`, in particular `M = q * N!`),
  both `signedLcmFractDefect N M c` and `bezoutSawtoothRemainderForm M N c` vanish identically.
* `moebiusCombinedPrefixDefect_first_octave_eq`,
  `moebiusCombinedPrefixDefect_first_octave_bounds`,
  `moebiusCombinedPrefixDefect_le_sub_horizon_linear_of_le_two_mul_sub_one`, &
  `moebiusRenormalizedDefect_antitone_first_octave`:
  Across the first trans-horizon octave `N ≤ M ≤ 2N - 1` (`N ≥ 2`),
  `moebiusCombinedPrefixDefect N M = M * sieveSuccessorReserve N moebiusReal - 1 + ∑_{k=N+1}^M (μ(k) μ(k+1) - μ(k)²)`.
  Because `-2 μ(k)² ≤ μ(k) μ(k+1) - μ(k)² ≤ 0` pointwise for every `k : ℕ`, the trans-horizon
  renormalized Möbius defect is antitone in `M` and non-positive, so the sub-horizon linear law
  `M * sieveSuccessorReserve N moebiusReal - 1` is an exact global upper bound throughout the entire
  two-octave horizon `1 ≤ M ≤ 2N - 1`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Universal Combined and Renormalized Prefix Defect Calculus -/

/-- The combined signed LCM and Bézout sawtooth defect for an arbitrary weight `c`:
`sieveCombinedPrefixDefect N M c = signedLcmFractDefect N M c + bezoutSawtoothRemainderForm M N c`. -/
def sieveCombinedPrefixDefect (N M : ℕ) (c : ℕ → ℝ) : ℝ :=
  signedLcmFractDefect N M c + bezoutSawtoothRemainderForm M N c

/-- The renormalized combined prefix defect retaining cancellation with the pole-free diagonal
main term `M * sieveSuccessorReserve N c`:
`sieveRenormalizedPrefixDefect N M c = sieveCombinedPrefixDefect N M c - M * sieveSuccessorReserve N c`. -/
def sieveRenormalizedPrefixDefect (N M : ℕ) (c : ℕ → ℝ) : ℝ :=
  sieveCombinedPrefixDefect N M c - (M : ℝ) * sieveSuccessorReserve N c

/-- For the literal Möbius weight `c = moebiusReal`, `sieveCombinedPrefixDefect` coincides with
`moebiusCombinedPrefixDefect`. -/
theorem sieveCombinedPrefixDefect_moebiusReal_eq (N M : ℕ) :
    sieveCombinedPrefixDefect N M moebiusReal = moebiusCombinedPrefixDefect N M :=
  rfl

/-- **Universal Source-Space Identity for `sieveRenormalizedPrefixDefect`
(`sieveRenormalizedPrefixDefect_eq_succ_sub_sq`):**
For every sieve cutoff `N : ℕ`, prefix `M : ℕ`, and weight `c : ℕ → ℝ`:
`sieveRenormalizedPrefixDefect N M c = ∑_{k=1}^M s_{N,c}(k) s_{N,c}(k + 1) - ∑_{k=1}^M s_{N,c}(k)²`. -/
theorem sieveRenormalizedPrefixDefect_eq_succ_sub_sq (N M : ℕ) (c : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect N M c =
      (∑ k ∈ Finset.Icc 1 M, sieveSeq N c k * sieveSeq N c (k + 1)) -
        ∑ k ∈ Finset.Icc 1 M, sieveSeq N c k ^ (2 : ℕ) := by
  have hsame := sum_sieveSeq_sq_eq_selberg_sub_signedLcmFractDefect N M c
  have hsucc := sum_sieveSeq_mul_succ_eq_main_add_sawtooth M N c
  unfold sieveRenormalizedPrefixDefect sieveCombinedPrefixDefect sieveSuccessorReserve
  linarith only [hsame, hsucc]

/-- Factored forward-difference form of `sieveRenormalizedPrefixDefect`:
`sieveRenormalizedPrefixDefect N M c = ∑_{k=1}^M s_{N,c}(k) * (s_{N,c}(k + 1) - s_{N,c}(k))`. -/
theorem sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff (N M : ℕ) (c : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect N M c =
      ∑ k ∈ Finset.Icc 1 M, sieveSeq N c k * (sieveSeq N c (k + 1) - sieveSeq N c k) := by
  rw [sieveRenormalizedPrefixDefect_eq_succ_sub_sq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- **Exact Dirichlet Polarization Law for `sieveRenormalizedPrefixDefect`
(`two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary`):**
For every `N : ℕ`, `M ≥ 1`, and weight `c : ℕ → ℝ`:
`2 * sieveRenormalizedPrefixDefect N M c = -∑_{k=1}^M (s_{N,c}(k + 1) - s_{N,c}(k))² + s_{N,c}(M + 1)² - s_{N,c}(1)²`. -/
theorem two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary
    (N : ℕ) {M : ℕ} (hM : 1 ≤ M) (c : ℕ → ℝ) :
    2 * sieveRenormalizedPrefixDefect N M c =
      -(∑ k ∈ Finset.Icc 1 M, (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) +
        sieveSeq N c (M + 1) ^ (2 : ℕ) - sieveSeq N c 1 ^ (2 : ℕ) := by
  have hren := sieveRenormalizedPrefixDefect_eq_succ_sub_sq N M c
  have hpol := sum_addDiff_sieveSeq_sq_eq N hM c
  linarith only [hren, hpol]

/-- **Forward Step Law for `sieveRenormalizedPrefixDefect` (`sieveRenormalizedPrefixDefect_succ_sub_eq`):**
Stepping the prefix horizon from `M` to `M + 1` changes `sieveRenormalizedPrefixDefect` by
`s_{N,c}(M + 1) * (s_{N,c}(M + 2) - s_{N,c}(M + 1))`. -/
theorem sieveRenormalizedPrefixDefect_succ_sub_eq (N M : ℕ) (c : ℕ → ℝ) :
    sieveRenormalizedPrefixDefect N (M + 1) c - sieveRenormalizedPrefixDefect N M c =
      sieveSeq N c (M + 1) * (sieveSeq N c (M + 2) - sieveSeq N c (M + 1)) := by
  rw [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff,
    sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff,
    Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
  ring

/-! ## §2. Exact Common-Return Annihilation of Both LCM and Bézout Defects -/

/-- Whenever a positive integer `d` divides `M`, `fractDivSeq d M = 0`. -/
theorem fractDivSeq_eq_zero_of_dvd {d M : ℕ} (_ : 0 < d) (hdvd : d ∣ M) :
    fractDivSeq d M = 0 := by
  unfold fractDivSeq
  rw [Int.fract_div_natCast_eq_div_natCast_mod, Nat.mod_eq_zero_of_dvd hdvd]
  simp

/-- At any common divisibility return time `M` (`∀ d ∈ [1, N], d ∣ M`), the Same-Node signed LCM
fractional-part defect `signedLcmFractDefect N M c` vanishes identically. -/
theorem signedLcmFractDefect_eq_zero_of_common_return {N M : ℕ} (c : ℕ → ℝ)
    (hM : ∀ d ∈ Finset.Icc 1 N, d ∣ M) :
    signedLcmFractDefect N M c = 0 := by
  unfold signedLcmFractDefect
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have hd1 : 0 < p.1 := (Finset.mem_Icc.mp hp1).1
  have hd2 : 0 < p.2 := (Finset.mem_Icc.mp hp2).1
  have hlcm_pos : 0 < Nat.lcm p.1 p.2 := Nat.lcm_pos hd1 hd2
  have hlcm_dvd : Nat.lcm p.1 p.2 ∣ M := Nat.lcm_dvd (hM p.1 hp1) (hM p.2 hp2)
  rw [fractDivSeq_eq_zero_of_dvd hlcm_pos hlcm_dvd, mul_zero]

/-- Whenever `d₁ * d₂ ∣ M` (`d₁, d₂ ≥ 1`), the Bézout sawtooth defect `bezoutSawtoothDefect M d₁ d₂`
vanishes identically. -/
theorem bezoutSawtoothDefect_eq_zero_of_mul_dvd {M d₁ d₂ : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hdvd : d₁ * d₂ ∣ M) :
    bezoutSawtoothDefect M d₁ d₂ = 0 := by
  by_cases hcop : Nat.Coprime d₁ d₂
  · unfold bezoutSawtoothDefect
    rw [if_pos hcop]
    obtain ⟨heq, _⟩ := bezoutIncidenceCount_eq_div_add_rem M hcop hd₁ hd₂
    have hmod : M % (d₁ * d₂) = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have hzero : bezoutIncidenceCount 0 d₁ d₂ = 0 := by
      unfold bezoutIncidenceCount bezoutIncidenceSet
      simp
    rw [hmod, hzero, add_zero] at heq
    have hprod_ne : ((d₁ : ℝ) * (d₂ : ℝ)) ≠ 0 := by positivity
    obtain ⟨q, rfl⟩ := hdvd
    have hdiv_nat : d₁ * d₂ * q / (d₁ * d₂) = q :=
      Nat.mul_div_cancel_left q (by positivity)
    rw [heq, hdiv_nat]
    push_cast
    field_simp [hprod_ne]
    ring
  · exact bezoutSawtoothDefect_eq_zero_of_not_coprime M hcop

/-- At any common divisibility return time `M` (`∀ d ∈ [1, N], d ∣ M`), the Bézout sawtooth
remainder quadratic form `bezoutSawtoothRemainderForm M N c` vanishes identically. -/
theorem bezoutSawtoothRemainderForm_eq_zero_of_common_return {N M : ℕ} (c : ℕ → ℝ)
    (hM : ∀ d ∈ Finset.Icc 1 N, d ∣ M) :
    bezoutSawtoothRemainderForm M N c = 0 := by
  unfold bezoutSawtoothRemainderForm
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  by_cases hcop : Nat.Coprime p.1 p.2
  · have hd1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
    have hd2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
    have hdvd : p.1 * p.2 ∣ M := hcop.mul_dvd_of_dvd_of_dvd (hM p.1 hp1) (hM p.2 hp2)
    rw [bezoutSawtoothDefect_eq_zero_of_mul_dvd hd1 hd2 hdvd, mul_zero]
  · rw [bezoutSawtoothDefect_eq_zero_of_not_coprime M hcop, mul_zero]

/-- **Complete Common-Return Annihilation of `sieveCombinedPrefixDefect`
(`sieveCombinedPrefixDefect_eq_zero_of_common_return`):**
At every common divisibility return time `M` (`∀ d ∈ [1, N], d ∣ M`), the combined defect vanishes
identically and the renormalized defect equals `-M * sieveSuccessorReserve N c`. -/
theorem sieveCombinedPrefixDefect_eq_zero_of_common_return {N M : ℕ} (c : ℕ → ℝ)
    (hM : ∀ d ∈ Finset.Icc 1 N, d ∣ M) :
    sieveCombinedPrefixDefect N M c = 0 ∧
      sieveRenormalizedPrefixDefect N M c = -(M : ℝ) * sieveSuccessorReserve N c := by
  have h1 := signedLcmFractDefect_eq_zero_of_common_return c hM
  have h2 := bezoutSawtoothRemainderForm_eq_zero_of_common_return c hM
  unfold sieveRenormalizedPrefixDefect sieveCombinedPrefixDefect
  rw [h1, h2]
  exact ⟨by ring, by ring⟩

/-- At every factorial multiple `M = q * N!`, both `sieveCombinedPrefixDefect` and its constituent
LCM and Bézout defects vanish identically. -/
theorem sieveCombinedPrefixDefect_factorial_mul_eq_zero (N q : ℕ) (c : ℕ → ℝ) :
    signedLcmFractDefect N (q * N.factorial) c = 0 ∧
      bezoutSawtoothRemainderForm (q * N.factorial) N c = 0 ∧
      sieveCombinedPrefixDefect N (q * N.factorial) c = 0 := by
  have hret : ∀ d ∈ Finset.Icc 1 N, d ∣ q * N.factorial := fun d hd =>
    dvd_mul_of_dvd_right (Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2) q
  exact ⟨signedLcmFractDefect_eq_zero_of_common_return c hret,
    bezoutSawtoothRemainderForm_eq_zero_of_common_return c hret,
    (sieveCombinedPrefixDefect_eq_zero_of_common_return c hret).1⟩

/-! ## §3. First Trans-Horizon Octave Formula & Universal Envelope for `moebiusCombinedPrefixDefect` -/

/-- Across the first trans-horizon octave `N ≤ M ≤ 2N` (`N ≥ 1`), the prefix mean square of
`sieveSeq N moebiusReal` equals `1 + ∑_{k=N+1}^M μ(k)²`. -/
theorem sum_sieveSeq_moebiusReal_sq_first_octave_prefix {N M : ℕ}
    (hN : 1 ≤ N) (hM_low : N ≤ M) (hM_high : M ≤ 2 * N) :
    (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k ^ (2 : ℕ)) =
      1 + ∑ k ∈ Finset.Icc (N + 1) M, moebiusReal k ^ (2 : ℕ) := by
  have hsplit : Finset.Icc 1 M = Finset.Icc 1 N ∪ Finset.Icc (N + 1) M := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) M) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  have hbulk : (∑ k ∈ Finset.Icc 1 N, sieveSeq N moebiusReal k ^ (2 : ℕ)) = 1 := by
    have hpt : ∀ k ∈ Finset.Icc 1 N,
        sieveSeq N moebiusReal k ^ (2 : ℕ) = sieveSeq N moebiusReal k := by
      intro k hk
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
      rw [sieveSeq_moebiusReal_eq_ite_of_le hk1 hkN]
      split_ifs <;> norm_num
    rw [Finset.sum_congr rfl hpt, sum_sieveSeq_moebiusReal_eq_one_of_le hN le_rfl]
  have htail : (∑ k ∈ Finset.Icc (N + 1) M, sieveSeq N moebiusReal k ^ (2 : ℕ)) =
      ∑ k ∈ Finset.Icc (N + 1) M, moebiusReal k ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    exact sieveSeq_moebiusReal_sq_first_octave hk1 (hkM.trans hM_high)
  rw [hsplit, Finset.sum_union hdisj, hbulk, htail]

/-- Across the first trans-horizon octave `N ≤ M ≤ 2N - 1` (`N ≥ 2`), the prefix Bézout correlation
of `sieveSeq N moebiusReal` equals `∑_{k=N+1}^M μ(k) μ(k + 1)`. -/
theorem sum_sieveSeq_moebiusReal_mul_succ_first_octave_prefix {N M : ℕ}
    (hN : 2 ≤ N) (hM_low : N ≤ M) (hM_high : M + 1 ≤ 2 * N) :
    (∑ k ∈ Finset.Icc 1 M, sieveSeq N moebiusReal k * sieveSeq N moebiusReal (k + 1)) =
      ∑ k ∈ Finset.Icc (N + 1) M, moebiusReal k * moebiusReal (k + 1) := by
  by_cases hMN : M = N
  · subst hMN
    have hemp : Finset.Icc (M + 1) M = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hemp, Finset.sum_empty]
    refine Finset.sum_eq_zero fun k hk => ?_
    obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
    exact sieveSeq_moebiusReal_mul_succ_eq_zero_of_le hN hk1 hkM
  · have hlt : N + 1 ≤ M + 1 := by omega
    have h := (sum_sieveSeq_moebiusReal_mul_succ_eq_sum_first_octave_jumps hN hlt hM_high).2
    simpa only [Nat.add_sub_cancel] using h

/-- **Exact First-Octave Trans-Horizon Formula for `moebiusCombinedPrefixDefect`
(`moebiusCombinedPrefixDefect_first_octave_eq`):**
For every `N ≥ 2` and `N ≤ M ≤ 2N - 1`:
`moebiusCombinedPrefixDefect N M = M * sieveSuccessorReserve N moebiusReal - 1 + ∑_{k=N+1}^M (μ(k) μ(k + 1) - μ(k)²)`. -/
theorem moebiusCombinedPrefixDefect_first_octave_eq {N M : ℕ}
    (hN : 2 ≤ N) (hM_low : N ≤ M) (hM_high : M + 1 ≤ 2 * N) :
    moebiusCombinedPrefixDefect N M =
      (M : ℝ) * sieveSuccessorReserve N moebiusReal - 1 +
        ∑ k ∈ Finset.Icc (N + 1) M,
          (moebiusReal k * moebiusReal (k + 1) - moebiusReal k ^ (2 : ℕ)) := by
  have hren := sieveRenormalizedPrefixDefect_eq_succ_sub_sq N M moebiusReal
  unfold sieveRenormalizedPrefixDefect at hren
  rw [sieveCombinedPrefixDefect_moebiusReal_eq,
    sum_sieveSeq_moebiusReal_sq_first_octave_prefix (by omega) hM_low (by omega),
    sum_sieveSeq_moebiusReal_mul_succ_first_octave_prefix hN hM_low hM_high] at hren
  rw [Finset.sum_sub_distrib]
  linarith only [hren]

/-- **Pointwise Non-Positivity and Lower Bound of the Möbius Successor Increment
(`moebiusReal_mul_succ_sub_sq_bounds`):**
For every integer `k : ℕ`:
`-2 * μ(k)² ≤ μ(k) μ(k + 1) - μ(k)² ≤ 0`. -/
theorem moebiusReal_mul_succ_sub_sq_bounds (k : ℕ) :
    -2 * moebiusReal k ^ (2 : ℕ) ≤
        moebiusReal k * moebiusReal (k + 1) - moebiusReal k ^ (2 : ℕ) ∧
      moebiusReal k * moebiusReal (k + 1) - moebiusReal k ^ (2 : ℕ) ≤ 0 := by
  have hk_cases : moebiusReal k = -1 ∨ moebiusReal k = 0 ∨ moebiusReal k = 1 := by
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or k with h | h | h <;> simp [h]
  have hsucc_cases : moebiusReal (k + 1) = -1 ∨ moebiusReal (k + 1) = 0 ∨ moebiusReal (k + 1) = 1 := by
    unfold moebiusReal
    rcases ArithmeticFunction.moebius_eq_or (k + 1) with h | h | h <;> simp [h]
  rcases hk_cases with hk | hk | hk <;> rcases hsucc_cases with hs | hs | hs <;>
    { rw [hk, hs]; constructor <;> norm_num }

/-- **Two-Sided Squarefree-Count Envelope for the First-Octave Renormalized Möbius Defect
(`moebiusCombinedPrefixDefect_first_octave_bounds`):**
For every `N ≥ 2` and `N ≤ M ≤ 2N - 1`:
`-2 * ∑_{k=N+1}^M μ(k)² ≤ moebiusCombinedPrefixDefect N M - (M * sieveSuccessorReserve N moebiusReal - 1) ≤ 0`. -/
theorem moebiusCombinedPrefixDefect_first_octave_bounds {N M : ℕ}
    (hN : 2 ≤ N) (hM_low : N ≤ M) (hM_high : M + 1 ≤ 2 * N) :
    -2 * (∑ k ∈ Finset.Icc (N + 1) M, moebiusReal k ^ (2 : ℕ)) ≤
        moebiusCombinedPrefixDefect N M -
          ((M : ℝ) * sieveSuccessorReserve N moebiusReal - 1) ∧
      moebiusCombinedPrefixDefect N M -
        ((M : ℝ) * sieveSuccessorReserve N moebiusReal - 1) ≤ 0 := by
  have heq := moebiusCombinedPrefixDefect_first_octave_eq hN hM_low hM_high
  have hlo : (∑ k ∈ Finset.Icc (N + 1) M, -2 * moebiusReal k ^ (2 : ℕ)) ≤
      ∑ k ∈ Finset.Icc (N + 1) M,
        (moebiusReal k * moebiusReal (k + 1) - moebiusReal k ^ (2 : ℕ)) :=
    Finset.sum_le_sum fun k _ => (moebiusReal_mul_succ_sub_sq_bounds k).1
  have hhi : (∑ k ∈ Finset.Icc (N + 1) M,
      (moebiusReal k * moebiusReal (k + 1) - moebiusReal k ^ (2 : ℕ))) ≤ 0 :=
    Finset.sum_nonpos fun k _ => (moebiusReal_mul_succ_sub_sq_bounds k).2
  rw [← Finset.mul_sum] at hlo
  constructor <;> linarith only [heq, hlo, hhi]

/-- **Global Two-Octave Upper Bound for `moebiusCombinedPrefixDefect`
(`moebiusCombinedPrefixDefect_le_sub_horizon_linear_of_le_two_mul_sub_one`):**
Throughout the entire two-octave range `1 ≤ M ≤ 2N - 1` (`N ≥ 2`), `moebiusCombinedPrefixDefect N M`
never exceeds its sub-horizon linear law `M * sieveSuccessorReserve N moebiusReal - 1`. -/
theorem moebiusCombinedPrefixDefect_le_sub_horizon_linear_of_le_two_mul_sub_one {N M : ℕ}
    (hN : 2 ≤ N) (hM1 : 1 ≤ M) (hM2 : M + 1 ≤ 2 * N) :
    moebiusCombinedPrefixDefect N M ≤
      (M : ℝ) * sieveSuccessorReserve N moebiusReal - 1 := by
  by_cases hMN : M ≤ N
  · exact (moebiusCombinedPrefixDefect_eq hN hM1 hMN).le
  · have hM_low : N ≤ M := by omega
    have hhi := (moebiusCombinedPrefixDefect_first_octave_bounds hN hM_low hM2).2
    linarith only [hhi]

/-- **Antitonicity of the Renormalized Möbius Defect Across the First Trans-Horizon Octave
(`moebiusRenormalizedDefect_antitone_first_octave`):**
For every `N ≥ 2` and `N ≤ M₁ ≤ M₂ ≤ 2N - 1`,
`moebiusCombinedPrefixDefect N M₂ - M₂ * sieveSuccessorReserve N moebiusReal ≤ moebiusCombinedPrefixDefect N M₁ - M₁ * sieveSuccessorReserve N moebiusReal`. -/
theorem moebiusRenormalizedDefect_antitone_first_octave {N M₁ M₂ : ℕ}
    (hN : 2 ≤ N) (h1 : N ≤ M₁) (h12 : M₁ ≤ M₂) (h2 : M₂ + 1 ≤ 2 * N) :
    moebiusCombinedPrefixDefect N M₂ - (M₂ : ℝ) * sieveSuccessorReserve N moebiusReal ≤
      moebiusCombinedPrefixDefect N M₁ - (M₁ : ℝ) * sieveSuccessorReserve N moebiusReal := by
  have heq1 := moebiusCombinedPrefixDefect_first_octave_eq hN h1 (by omega)
  have heq2 := moebiusCombinedPrefixDefect_first_octave_eq hN (h1.trans h12) h2
  have hsub : Finset.Icc (N + 1) M₁ ⊆ Finset.Icc (N + 1) M₂ :=
    Finset.Icc_subset_Icc_right h12
  have hsplit := Finset.sum_sdiff hsub (f := fun k =>
    moebiusReal k * moebiusReal (k + 1) - moebiusReal k ^ (2 : ℕ))
  have hsdiff_nonpos : (∑ k ∈ Finset.Icc (N + 1) M₂ \ Finset.Icc (N + 1) M₁,
      (moebiusReal k * moebiusReal (k + 1) - moebiusReal k ^ (2 : ℕ))) ≤ 0 :=
    Finset.sum_nonpos fun k _ => (moebiusReal_mul_succ_sub_sq_bounds k).2
  linarith only [heq1, heq2, hsplit, hsdiff_nonpos]

end
end GaloisForLFunctions.BezoutValuationIncidence
