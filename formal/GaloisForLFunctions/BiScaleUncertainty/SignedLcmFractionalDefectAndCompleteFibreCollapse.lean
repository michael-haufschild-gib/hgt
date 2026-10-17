import GaloisForLFunctions.BiScaleUncertainty.SelbergSieveTailQuadraticFormAndTruncatedDivisorGram
import GaloisForLFunctions.BiScaleUncertainty.CoprimeResidueAntiCorrelationAndSawtoothPhase
import GaloisForLFunctions.RHTower.EulerDeletionTruncatedDivisorPairCorrelation

/-!
# Exact Signed LCM Fractional-Part Defect, Additive-Multiplicative Successor Reciprocity, and Complete-Fibre Collapse (`SignedLcmFractionalDefectAndCompleteFibreCollapse`)

In `SelbergSieveTailQuadraticFormAndTruncatedDivisorGram`, the mean square of the sieved divisor sum
`s_{N,c}(k) = ∑_{d ∣ k, d ≤ N} c(d)` was bounded via the triangle inequality (`|c(d₁)| |c(d₂)|`),
incurring an `ℓ¹`-norm squared error `(∑_{d=1}^N |c(d)|)²`. Throwing away the signs of the
fractional-part remainder is the classic sieve/parity barrier (Wall 1 / Wall 10).

This module replaces the triangle-inequality bound with the **exact signed LCM fractional-part
defect calculus** and proves four unconditional structural laws:

1. **Lossless Signed Selberg Decomposition (`sievedDivisorPrefixMeanSquare_eq_selberg_sub_signedLcmFractDefect`):**
   Defining the signed LCM fractional-part defect
   `signedLcmFractDefect N M c = ∑_{d₁, d₂ ∈ [1, N]} c(d₁) c(d₂) {M / lcm(d₁, d₂)}`,
   the prefix mean square for **every** `N M : ℕ` and arbitrary signed weights `c : ℕ → ℝ` satisfies
   `∑_{k=1}^M s_{N,c}(k)² = M · Q_Sel(N, c) - signedLcmFractDefect N M c`
   with **zero** triangle-inequality loss, where
   `Q_Sel(N, c) = ∑_{e=1}^N φ(e) (∑_{d ≤ N, e ∣ d} c(d)/d)²`.

2. **Additive-Multiplicative Successor Reciprocity Law (`signedLcmFractDefect_succ_sub_eq`):**
   Under the additive step `M ↦ M + 1` (which distinguishes `ℤ` from Beurling generalized integers),
   the Coprime Predecessor Residue Law `{(M + 1)/L} - {M/L} = 1/L - 1_{L ∣ (M+1)}` combined with
   `lcm(d₁, d₂) ∣ (M + 1) ↔ d₁ ∣ (M + 1) ∧ d₂ ∣ (M + 1)` turns the divisibility indicator sum into
   the exact square `s_{N,c}(M + 1)² ≥ 0`, yielding the exact recurrence
   `signedLcmFractDefect N (M + 1) c - signedLcmFractDefect N M c = Q_Sel(N, c) - s_{N,c}(M + 1)²`.
   In particular, at any common multiple `M` of `[1, N]`, `signedLcmFractDefect N M c = 0` and
   `∑_{k=1}^M s_{N,c}(k)² = M · Q_Sel(N, c)` identically.

3. **Exact LCM Fibre Decomposition & Möbius Inversion (`signedLcmFractDefect_eq_sum_lcmFibres`,
   `sievedLcmFibre_moebius_inversion`):**
   Grouping pairs `(d₁, d₂) ∈ [1, N]²` by their literal least common multiple `L = lcm(d₁, d₂) ∈ [1, N²]`
   writes `signedLcmFractDefect N M c = ∑_{L ∈ lcm([1,N]²)} F_{N,c}(L) {M / L}`, where the finite
   LCM fibre `F_{N,c}(L) = ∑_{d₁, d₂ ≤ N, lcm(d₁, d₂) = L} c(d₁) c(d₂)` satisfies
   `∑_{q ∣ L} F_{N,c}(q) = s_{N,c}(L)²` and `F_{N,c}(L) = ∑_{d ∣ L} μ(L/d) s_{N,c}(d)²`.

4. **Complete-Fibre Möbius Collapse (`sievedLcmFibre_moebius_eq_moebius_of_le`,
   `sievedLcmFibre_moebius_sub_moebius_eq_gt_divisors`):**
   For the Möbius weight `c(d) = μ(d)`, every divisor `d` in `1 < d ≤ N` has `s_{N,μ}(d) = 0`.
   Consequently, on every modulus `1 ≤ L ≤ N`, the `3^{ω(L)}` signed pair terms in `F_{N,μ}(L)`
   cancel down to a **single Möbius sign** `F_{N,μ}(L) = μ(L)`, and for `L > N` the excess over
   `μ(L)` is supported exclusively on divisors `d ∣ L` with `d > N`:
   `F_{N,μ}(L) - μ(L) = ∑_{d ∣ L, d > N} μ(L/d) s_{N,μ}(d)²`.
-/

noncomputable section

namespace GaloisForLFunctions.BiScaleUncertainty

open Finset ArithmeticFunction RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

/-! ## §1. The Selberg Totient Diagonal and the Signed LCM Fractional-Part Defect -/

/-- The Selberg multiples-coordinate `Y_{N,c}(e) = ∑_{d ∈ [1, N], e ∣ d} c(d) / d`. -/
def selbergMultiplesCoord (N : ℕ) (c : ℕ → ℝ) (e : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 N).filter (fun d => e ∣ d), c d / (d : ℝ)

/-- The Selberg totient-weighted diagonal quadratic form
`Q_Sel(N, c) = ∑_{e=1}^N φ(e) Y_{N,c}(e)²`. -/
def selbergTotientDiagonalForm (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 N, (Nat.totient e : ℝ) * (selbergMultiplesCoord N c e) ^ (2 : ℕ)

/-- `selbergTotientDiagonalForm` is unconditionally non-negative. -/
theorem selbergTotientDiagonalForm_nonneg (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ selbergTotientDiagonalForm N c :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- **Smooth `[1, N]²` LCM Form Equals `selbergTotientDiagonalForm`:**
`∑_{d₁, d₂ ∈ [1, N]} c(d₁) c(d₂) / lcm(d₁, d₂) = selbergTotientDiagonalForm N c`. -/
theorem sum_div_lcm_eq_selbergTotientDiagonalForm (N : ℕ) (c : ℕ → ℝ) :
    (∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      c p.1 * c p.2 / (Nat.lcm p.1 p.2 : ℝ)) =
    selbergTotientDiagonalForm N c :=
  truncated_lcm_smooth_eq_selberg_totient_diagonal N c

/-- The **signed LCM fractional-part defect**
`R_lcm(N, M, c) = ∑_{d₁, d₂ ∈ [1, N]} c(d₁) c(d₂) {M / lcm(d₁, d₂)}`. -/
def signedLcmFractDefect (N M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
    c p.1 * c p.2 * fractDivSeq (Nat.lcm p.1 p.2) M

/-- At `M = 0`, the signed LCM fractional-part defect vanishes identically. -/
@[simp]
theorem signedLcmFractDefect_zero (N : ℕ) (c : ℕ → ℝ) :
    signedLcmFractDefect N 0 c = 0 := by
  unfold signedLcmFractDefect fractDivSeq
  simp

/-- For positive `L` and any `M : ℕ`, `((M / L : ℕ) : ℝ) = (M : ℝ) / (L : ℝ) - fractDivSeq L M`. -/
theorem natCast_div_eq_sub_fractDivSeq {L : ℕ} (hL : 0 < L) (M : ℕ) :
    (((M / L : ℕ) : ℝ)) = (M : ℝ) / (L : ℝ) - fractDivSeq L M := by
  have h1 := natCast_div_succ_eq_floorDivSeq_add_fractDivSeq (L - 1) M
  have hL_eq : L - 1 + 1 = L := Nat.sub_add_cancel hL
  rw [hL_eq] at h1
  unfold floorDivSeq at h1
  linarith

/-- For any `k ≥ 1`, `sievedDivisorSum N c k` is the filtered sum over `d ∈ [1, N]` dividing `k`. -/
theorem sievedDivisorSum_eq_sum_filter_Icc_of_pos (N : ℕ) (c : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    sievedDivisorSum N c k =
      ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ k), c d := by
  have hk_eq : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  rw [hk_eq, sievedDivisorSum_succ_eq_sum_filter_Icc]

/-- At any positive integer `m ≥ 1`, the simultaneous divisibility indicator sum over `[1, N]²`
with `lcm(d₁, d₂) ∣ m` equals the exact square `sievedDivisorSum N c m ^ 2`. -/
theorem sum_lcm_dvd_indicator_eq_sievedDivisorSum_sq (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N),
      c p.1 * c p.2 * (if Nat.lcm p.1 p.2 ∣ m then (1 : ℝ) else 0)) =
    sievedDivisorSum N c m ^ (2 : ℕ) := by
  rw [sievedDivisorSum_eq_sum_filter_Icc_of_pos N c hm, sq,
    Finset.sum_filter, Finset.sum_mul_sum, ← Finset.sum_product']
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Nat.lcm_dvd_iff]
  by_cases h1 : p.1 ∣ m <;> by_cases h2 : p.2 ∣ m <;> simp [h1, h2]

/-! ## §2. Additive-Multiplicative Successor Reciprocity Law & Lossless Prefix Mean Square -/

/-- **Exact Additive-Multiplicative Successor Reciprocity Law (`signedLcmFractDefect_succ_sub_eq`):**
Stepping `M ↦ M + 1` changes the signed LCM fractional-part defect by the difference between the
Selberg totient diagonal `selbergTotientDiagonalForm N c` and the exact square
`sievedDivisorSum N c (M + 1) ^ 2`. -/
theorem signedLcmFractDefect_succ_sub_eq (N M : ℕ) (c : ℕ → ℝ) :
    signedLcmFractDefect N (M + 1) c - signedLcmFractDefect N M c =
      selbergTotientDiagonalForm N c - sievedDivisorSum N c (M + 1) ^ (2 : ℕ) := by
  unfold signedLcmFractDefect
  rw [← Finset.sum_sub_distrib, ← sum_div_lcm_eq_selbergTotientDiagonalForm,
    ← sum_lcm_dvd_indicator_eq_sievedDivisorSum_sq N c (Nat.le_add_left 1 M),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have hL : 0 < Nat.lcm p.1 p.2 :=
    Nat.lcm_pos (Finset.mem_Icc.mp hp1).1 (Finset.mem_Icc.mp hp2).1
  have hL_eq : Nat.lcm p.1 p.2 - 1 + 1 = Nat.lcm p.1 p.2 := Nat.sub_add_cancel hL
  have hstep := addDiff_fractDivSeq_succ (Nat.lcm p.1 p.2 - 1) M
  have hfl := addDiff_floorDivSeq_eq_ite_dvd (Nat.lcm p.1 p.2 - 1) M
  unfold addDiff at hstep
  rw [hfl] at hstep
  rw [hL_eq] at hstep
  calc c p.1 * c p.2 * fractDivSeq (Nat.lcm p.1 p.2) (M + 1) -
        c p.1 * c p.2 * fractDivSeq (Nat.lcm p.1 p.2) M
      = c p.1 * c p.2 * (fractDivSeq (Nat.lcm p.1 p.2) (M + 1) -
          fractDivSeq (Nat.lcm p.1 p.2) M) := by ring
    _ = c p.1 * c p.2 * (1 / (Nat.lcm p.1 p.2 : ℝ) -
          if Nat.lcm p.1 p.2 ∣ (M + 1) then (1 : ℝ) else 0) := by rw [hstep]
    _ = c p.1 * c p.2 / (Nat.lcm p.1 p.2 : ℝ) -
          c p.1 * c p.2 * (if Nat.lcm p.1 p.2 ∣ (M + 1) then (1 : ℝ) else 0) := by ring

/-- **Lossless Signed Selberg Decomposition of the Prefix Mean Square:**
For **every** `N M : ℕ` (whether `M < N`, `M = N`, or `M > N`) and arbitrary signed weights `c`,
`∑_{k=1}^M s_{N,c}(k)² = M · selbergTotientDiagonalForm N c - signedLcmFractDefect N M c`. -/
theorem sievedDivisorPrefixMeanSquare_eq_selberg_sub_signedLcmFractDefect
    (N M : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, sievedDivisorSum N c k ^ (2 : ℕ)) =
      (M : ℝ) * selbergTotientDiagonalForm N c - signedLcmFractDefect N M c := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert (by simp), ih]
    have hstep := signedLcmFractDefect_succ_sub_eq N M c
    push_cast
    linarith

/-- **Lossless Signed Decomposition of any Interval Mean Square (`M₁ < k ≤ M₂`):**
For any `M₁ ≤ M₂`, the window mean square `∑_{k = M₁ + 1}^{M₂} s_{N,c}(k)²` equals
`(M₂ - M₁) · Q_Sel(N, c)` minus the net change in `signedLcmFractDefect`. -/
theorem sievedDivisorIntervalMeanSquare_eq_selberg_sub_defect_diff
    (N M₁ M₂ : ℕ) (hM : M₁ ≤ M₂) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc (M₁ + 1) M₂, sievedDivisorSum N c k ^ (2 : ℕ)) =
      ((M₂ - M₁ : ℕ) : ℝ) * selbergTotientDiagonalForm N c -
        (signedLcmFractDefect N M₂ c - signedLcmFractDefect N M₁ c) := by
  have hunion : Finset.Icc 1 M₂ = Finset.Icc 1 M₁ ∪ Finset.Icc (M₁ + 1) M₂ := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 M₁) (Finset.Icc (M₁ + 1) M₂) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  have hsum := Finset.sum_union hdisj (f := fun k => sievedDivisorSum N c k ^ (2 : ℕ))
  rw [← hunion, sievedDivisorPrefixMeanSquare_eq_selberg_sub_signedLcmFractDefect N M₂ c,
    sievedDivisorPrefixMeanSquare_eq_selberg_sub_signedLcmFractDefect N M₁ c] at hsum
  have hcast : ((M₂ - M₁ : ℕ) : ℝ) = (M₂ : ℝ) - (M₁ : ℝ) := Nat.cast_sub hM
  rw [hcast]
  linarith

/-- **Lossless Origin-Tail Mean Square Decomposition (`N + 1 ≤ k ≤ N + K`):**
Splitting `1 ≤ k ≤ N + K` into the unsieved head `1 ≤ k ≤ N` and the origin tail `N + 1 ≤ k ≤ N + K`
gives the exact tail identity without any `ℓ¹` triangle-inequality loss. -/
theorem tailSievedDivisorMeanSquare_eq_selberg_sub_head_sub_signedLcmFractDefect
    (N K : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc (N + 1) (N + K), sievedDivisorSum N c k ^ (2 : ℕ)) =
      ((N + K : ℕ) : ℝ) * selbergTotientDiagonalForm N c -
        (∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, c d) ^ (2 : ℕ)) -
        signedLcmFractDefect N (N + K) c := by
  have hunion : Finset.Icc 1 (N + K) = Finset.Icc 1 N ∪ Finset.Icc (N + 1) (N + K) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) (N + K)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_Icc] at ha hb
    omega
  have hsplit : (∑ k ∈ Finset.Icc 1 (N + K), sievedDivisorSum N c k ^ (2 : ℕ)) =
      (∑ k ∈ Finset.Icc 1 N, (∑ d ∈ k.divisors, c d) ^ (2 : ℕ)) +
        ∑ k ∈ Finset.Icc (N + 1) (N + K), sievedDivisorSum N c k ^ (2 : ℕ) := by
    rw [hunion, Finset.sum_union hdisj,
      sum_Icc_sievedDivisorSum_eq_full N c (fun x => x ^ (2 : ℕ))]
  have htot := sievedDivisorPrefixMeanSquare_eq_selberg_sub_signedLcmFractDefect N (N + K) c
  linarith

/-- **Zero Fractional-Part Defect at Common Multiples of `[1, N]`:**
Whenever every `d ∈ [1, N]` divides `M` (for instance, when `M` is a multiple of the canonical
clock `lcm(1, …, N)`), `signedLcmFractDefect N M c = 0`. -/
theorem signedLcmFractDefect_eq_zero_of_forall_dvd (N M : ℕ) (c : ℕ → ℝ)
    (hdvd : ∀ d ∈ Finset.Icc 1 N, d ∣ M) :
    signedLcmFractDefect N M c = 0 := by
  unfold signedLcmFractDefect
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  have hL : 0 < Nat.lcm p.1 p.2 :=
    Nat.lcm_pos (Finset.mem_Icc.mp hp1).1 (Finset.mem_Icc.mp hp2).1
  have hLM : Nat.lcm p.1 p.2 ∣ M := Nat.lcm_dvd (hdvd p.1 hp1) (hdvd p.2 hp2)
  obtain ⟨q, hq⟩ := hLM
  have hL_eq : Nat.lcm p.1 p.2 - 1 + 1 = Nat.lcm p.1 p.2 := Nat.sub_add_cancel hL
  have hfr : fractDivSeq (Nat.lcm p.1 p.2) M = 0 := by
    rw [hq, mul_comm, ← hL_eq]
    exact fractDivSeq_mul_eq_zero q (Nat.lcm p.1 p.2 - 1)
  rw [hfr, mul_zero]

/-- **Exact Clock-Period Mean Square Identity:**
Whenever every `d ∈ [1, N]` divides `M`, the prefix mean square `∑_{k=1}^M s_{N,c}(k)²` equals
`M · selbergTotientDiagonalForm N c` with **zero** remainder. -/
theorem sievedDivisorPrefixMeanSquare_eq_selberg_of_forall_dvd (N M : ℕ) (c : ℕ → ℝ)
    (hdvd : ∀ d ∈ Finset.Icc 1 N, d ∣ M) :
    (∑ k ∈ Finset.Icc 1 M, sievedDivisorSum N c k ^ (2 : ℕ)) =
      (M : ℝ) * selbergTotientDiagonalForm N c := by
  rw [sievedDivisorPrefixMeanSquare_eq_selberg_sub_signedLcmFractDefect,
    signedLcmFractDefect_eq_zero_of_forall_dvd N M c hdvd, sub_zero]

/-! ## §3. Exact LCM Fibre Decomposition & Complete-Fibre Möbius Collapse -/

/-- **LCM Fibre Decomposition of `signedLcmFractDefect`:**
Grouping `(d₁, d₂) ∈ [1, N]²` by `L = lcm(d₁, d₂)` expresses `signedLcmFractDefect N M c` as a
single sum over `L ∈ lcm([1, N]²)` of `finiteLcmPairFibre (Icc 1 N) c L * fractDivSeq L M`. -/
theorem signedLcmFractDefect_eq_sum_lcmFibres (N M : ℕ) (c : ℕ → ℝ) :
    signedLcmFractDefect N M c =
      ∑ L ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).image (fun p => Nat.lcm p.1 p.2),
        finiteLcmPairFibre (Finset.Icc 1 N) c L * fractDivSeq L M := by
  unfold signedLcmFractDefect finiteLcmPairFibre
  rw [sum_pair_reindex_lcm]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hlcm : Nat.lcm p.1 p.2 = L := (Finset.mem_filter.mp hp).2
  rw [hlcm]

/-- The divisor-prefix sum `finiteDivisorFibrePrefix (Icc 1 N) c m` at any `m ≥ 1` coincides with
`sievedDivisorSum N c m`. -/
theorem finiteDivisorFibrePrefix_Icc_eq_sievedDivisorSum (N : ℕ) (c : ℕ → ℝ)
    {m : ℕ} (hm : 1 ≤ m) :
    finiteDivisorFibrePrefix (Finset.Icc 1 N) c m = sievedDivisorSum N c m := by
  rw [finiteDivisorFibrePrefix, sievedDivisorSum_eq_sum_filter_Icc_of_pos N c hm]

/-- **Möbius Inversion of the Finite LCM Fibre in Terms of `sievedDivisorSum`:**
For every `L ≥ 1`, `finiteLcmPairFibre (Icc 1 N) c L = ∑_{d ∣ L} μ(L/d) s_{N,c}(d)²`. -/
theorem finiteLcmPairFibre_Icc_eq_sum_divisors_sievedDivisorSum_sq (N : ℕ) (c : ℕ → ℝ)
    {L : ℕ} (hL : 0 < L) :
    finiteLcmPairFibre (Finset.Icc 1 N) c L =
      ∑ d ∈ L.divisors, ((μ (L / d) : ℤ) : ℝ) * sievedDivisorSum N c d ^ (2 : ℕ) := by
  rw [← finiteLcmPairFibre_moebius_inversion (Finset.Icc 1 N) c L hL,
    Nat.sum_divisorsAntidiagonal' (fun x y => ((μ x : ℤ) : ℝ) *
      (finiteDivisorFibrePrefix (Finset.Icc 1 N) c y) ^ 2)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
  rw [finiteDivisorFibrePrefix_Icc_eq_sievedDivisorSum N c hd1]

/-- For the Möbius weight `c(d) = μ(d)`, the sieved divisor sum on the bulk head `1 ≤ k ≤ N` is the
exact unit point indicator `if k = 1 then 1 else 0`. -/
theorem sievedDivisorSum_moebius_eq_ite_one {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    sievedDivisorSum N (fun d => ((μ d : ℤ) : ℝ)) k = if k = 1 then 1 else 0 := by
  have hk_eq : k = (k - 1) + 1 := (Nat.sub_add_cancel hk1).symm
  have hN_eq : N = (k - 1) + 1 + (N - k) := by omega
  rw [hk_eq, hN_eq, sievedDivisorSum_succ_eq_full_divisorSum (k - 1) (N - k), ← hk_eq]
  exact sum_divisors_moebius_real k

/-- **Complete-Fibre Möbius Collapse (`1 ≤ L ≤ N`) and Boundary-Fibre Excess Formula:**
For every `N ≥ 1` and `L ≥ 1`, the Möbius LCM fibre `finiteLcmPairFibre (Icc 1 N) μ L` equals
`μ(L)` plus the sum over divisors `d ∣ L` strictly exceeding `N`:
`finiteLcmPairFibre (Icc 1 N) μ L = μ(L) + ∑_{d ∣ L, N < d} μ(L/d) s_{N,μ}(d)²`. -/
theorem finiteLcmPairFibre_Icc_moebius_eq_moebius_add_gt_divisors
    {N L : ℕ} (hN : 1 ≤ N) (hL : 0 < L) :
    finiteLcmPairFibre (Finset.Icc 1 N) (fun d => ((μ d : ℤ) : ℝ)) L =
      ((μ L : ℤ) : ℝ) +
        ∑ d ∈ L.divisors.filter (fun d => N < d),
          ((μ (L / d) : ℤ) : ℝ) *
            sievedDivisorSum N (fun d => ((μ d : ℤ) : ℝ)) d ^ (2 : ℕ) := by
  classical
  rw [finiteLcmPairFibre_Icc_eq_sum_divisors_sievedDivisorSum_sq N _ hL]
  have hsplit := (Finset.sum_filter_add_sum_filter_not L.divisors (fun d => d ≤ N)
    (fun d => ((μ (L / d) : ℤ) : ℝ) *
      sievedDivisorSum N (fun d => ((μ d : ℤ) : ℝ)) d ^ (2 : ℕ))).symm
  rw [hsplit]
  have hnot : L.divisors.filter (fun d => ¬ d ≤ N) = L.divisors.filter (fun d => N < d) := by
    ext d
    simp only [Finset.mem_filter, not_le]
  rw [hnot]
  congr 1
  have h1mem : 1 ∈ L.divisors.filter (fun d => d ≤ N) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd L, hL.ne'⟩, hN⟩
  rw [Finset.sum_eq_single_of_mem 1 h1mem]
  · rw [Nat.div_one, sievedDivisorSum_moebius_eq_ite_one le_rfl hN, if_pos rfl]
    ring
  · intro d hd hd1
    obtain ⟨hdL, hdN⟩ := Finset.mem_filter.mp hd
    have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hdL
    rw [sievedDivisorSum_moebius_eq_ite_one hdpos hdN, if_neg hd1]
    ring

/-- **Complete-Fibre Collapse on `1 ≤ L ≤ N` (`finiteLcmPairFibre_Icc_moebius_eq_moebius_of_le`):**
For every `1 ≤ L ≤ N`, the `3^{ω(L)}` signed pair terms `(d₁, d₂) ∈ [1, N]²` with `lcm(d₁, d₂) = L`
cancel down to the single Möbius sign `μ(L)`. -/
theorem finiteLcmPairFibre_Icc_moebius_eq_moebius_of_le
    {N L : ℕ} (hL1 : 1 ≤ L) (hLN : L ≤ N) :
    finiteLcmPairFibre (Finset.Icc 1 N) (fun d => ((μ d : ℤ) : ℝ)) L =
      ((μ L : ℤ) : ℝ) := by
  have hN : 1 ≤ N := hL1.trans hLN
  rw [finiteLcmPairFibre_Icc_moebius_eq_moebius_add_gt_divisors hN hL1]
  have hempty : (L.divisors.filter (fun d => N < d)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro d hd
    have hdL : d ≤ L := Nat.le_of_dvd hL1 (Nat.dvd_of_mem_divisors hd)
    omega
  rw [hempty, Finset.sum_empty, add_zero]

end GaloisForLFunctions.BiScaleUncertainty
