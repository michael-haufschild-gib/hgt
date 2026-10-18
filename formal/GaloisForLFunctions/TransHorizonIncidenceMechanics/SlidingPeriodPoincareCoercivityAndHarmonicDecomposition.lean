import GaloisForLFunctions.BezoutValuationIncidence.RenormalizedMobiusDefectAndFirstOctaveCancellation

/-!
# Pillar XVI: Unconditional Harmonic-Subtracted Selberg–Bézout Coercivity, Sliding-Period Invariance, and the Scale-Independent Torus Poincaré Inequality (`SlidingPeriodPoincareCoercivityAndHarmonicDecomposition`)

For a generic periodic function on the discrete torus `ℤ / L_N ℤ` of period
`L_N = lcm(1, ..., N) = e^{(1+o(1))N}`, the discrete Poincaré constant relating the centered
variance to the unit-step Dirichlet oscillation energy scales like `L_N² / (4 π²) ~ e^{2N}`.
Furthermore, in `BezoutValuationIncidence`, the `1/2`-decorrelation inequality
`Q_Sel(N, c) ≤ 2 * sieveSuccessorReserve N c` was only formulated on the harmonic nullspace
`ker P` (`finiteHarmonicSum N c = 0`), which excludes both the literal Möbius weight `c = μ`
and the power-damped Möbius weight `c = c_ε` at finite horizons `N ≥ 2`.

This sixteenth foundational pillar of **Trans-Horizon Arithmetic–Archimedean Incidence Mechanics**
removes the `ker P` restriction completely and establishes the **Unconditional Scale-Independent
Unit-Step Torus Poincaré Inequality** across all sliding period windows `[M + 1, M + L]` (`M ∈ ℕ`):

## Core Main Theorems (100% Unconditional)

1. **Unconditional Harmonic-Subtracted Selberg–Bézout Spectral Identity & Coercivity
   (`sievePoincareExcess`, `sievePoincareExcess_nonneg`,
   `two_mul_sieveSuccessorReserve_sub_selberg_add_harmonic_sq_eq_excess`,
   `selberg_sub_harmonic_sq_le_two_mul_sieveSuccessorReserve`)**:
   For **every** horizon `N ≥ 1` and **every** real weight `c : ℕ → ℝ` (with **zero** hypothesis on
   `finiteHarmonicSum N c`), subtracting the `e = 1` harmonic mean-square mode
   `(finiteHarmonicSum N c)² = Y_{N,c}(1)²` from `selbergTotientDiagonalForm N c` gives the exact
   spectral excess identity:
   $$2 \cdot \operatorname{sieveSuccessorReserve}(N, c) -
       \Bigl(\operatorname{selbergTotientDiagonalForm}(N, c) -
         \bigl(\operatorname{finiteHarmonicSum}(N, c)\bigr)^2\Bigr) =
     \sum_{e=2}^N \bigl(\varphi(e) - 2\mu(e)\bigr) Y_{N,c}(e)^2 \ge 0.$$
   Because `2 μ(e) ≤ φ(e)` for every `e ≥ 2` (with unique resonant equality at `e = 6 = 2 · 3`),
   every divisor sum satisfies the unconditional variance-to-reserve coercivity inequality
   $$\operatorname{selbergTotientDiagonalForm}(N, c) -
       \bigl(\operatorname{finiteHarmonicSum}(N, c)\bigr)^2 \le
     2 \cdot \operatorname{sieveSuccessorReserve}(N, c).$$

2. **Universal Sliding-Window Period Invariance Across All `M ∈ ℕ`
   (`sieveSeq_add_of_common_return`, `sum_Icc_add_period_sub_eq_sum_Icc`,
   `sum_Icc_sliding_period_eq_sum_Icc`,
   `sum_sieveSeq_sq_sliding_period_eq`,
   `sum_sieveSeq_mul_succ_sliding_period_eq`,
   `sum_addDiff_sieveSeq_sq_sliding_period_eq`)**:
   For any common divisibility return period `L ≥ 1` (`∀ d ∈ Icc 1 N, d ∣ L`, including
   `L = (Icc 1 N).lcm id` and `L = N!`) and **every** window offset `M ∈ ℕ`:
   - $\sum_{k=M+1}^{M+L} s_{N,c}(k)^2 = L \cdot \operatorname{selbergTotientDiagonalForm}(N, c)$,
   - $\sum_{k=M+1}^{M+L} s_{N,c}(k) s_{N,c}(k+1) = L \cdot \operatorname{bezoutCoprimeQuadraticForm}(N, c)$,
   - $\sum_{k=M+1}^{M+L} \bigl(s_{N,c}(k+1) - s_{N,c}(k)\bigr)^2 = 2 L \cdot \operatorname{sieveSuccessorReserve}(N, c)$.

3. **Global Periodicity of `sieveCombinedPrefixDefect` & Linear Period Dissipation of
   `sieveRenormalizedPrefixDefect`
   (`sieveRenormalizedPrefixDefect_add_period_eq`,
   `sieveCombinedPrefixDefect_add_period_eq`,
   `sieveRenormalizedPrefixDefect_add_mul_period_eq`,
   `sieveRenormalizedPrefixDefect_euclidean_decomp`)**:
   For every offset `M ∈ ℕ` and multiplier `q ∈ ℕ`:
   $$\operatorname{sieveCombinedPrefixDefect}_N(M + q L; c) = \operatorname{sieveCombinedPrefixDefect}_N(M; c),$$
   $$\widetilde{\mathcal{D}}_N(M + q L; c) = \widetilde{\mathcal{D}}_N(M; c) - q L \cdot \operatorname{sieveSuccessorReserve}(N, c),$$
   and by Euclidean division $M = (M / L) L + (M \bmod L)$,
   $$\widetilde{\mathcal{D}}_N(M; c) = \widetilde{\mathcal{D}}_N(M \bmod L;\, c) -
       \left\lfloor \frac{M}{L} \right\rfloor L \cdot \operatorname{sieveSuccessorReserve}(N, c).$$

4. **Scale-Independent Unit-Step Torus Poincaré Inequality for All Divisor Incidence Sums
   (`sliding_period_dirichletEnergy_sub_variance_eq_excess`,
   `sliding_period_variance_le_dirichletEnergy`)**:
   Because Bézout coprimality $\gcd(k, k+1) = 1$ annihilates all non-coprime divisor correlations
   in a single unit step $k \mapsto k + 1$, the discrete Poincaré constant on every sliding period
   window $[M + 1, M + L]$ is **at most $1$** (independent of $N$ and $L \sim e^N$!) for **every**
   weight $c : \mathbb{N} \to \mathbb{R}$:
   $$\sum_{k = M + 1}^{M + L} s_{N,c}(k)^2 - L \bigl(\operatorname{finiteHarmonicSum}(N, c)\bigr)^2 \le
     \sum_{k = M + 1}^{M + L} \bigl(s_{N,c}(k + 1) - s_{N,c}(k)\bigr)^2,$$
   with exact non-negative excess $L \cdot \operatorname{sievePoincareExcess}(N, c) \ge 0$.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Unconditional Harmonic-Subtracted Selberg–Bézout Spectral Coercivity -/

/-- **The Selberg–Bézout Poincaré Excess (`sievePoincareExcess`):**
The spectral excess between the unit-step Dirichlet energy density
`2 * sieveSuccessorReserve N c = 2 ∑_{e=2}^N (φ(e) - μ(e)) Y_{N,c}(e)²`
and the harmonic-subtracted Selberg variance density
`selbergTotientDiagonalForm N c - (finiteHarmonicSum N c)² = ∑_{e=2}^N φ(e) Y_{N,c}(e)²`. -/
def sievePoincareExcess (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ e ∈ Finset.Icc 2 N,
    ((Nat.totient e : ℝ) - 2 * moebiusReal e) * (selbergMultiplesCoord N c e) ^ (2 : ℕ)

/-- Because `2 * μ(e) ≤ φ(e)` for every `e ≥ 2` (`two_mul_moebiusReal_le_totient`),
`sievePoincareExcess N c ≥ 0` unconditionally for every `N : ℕ` and every weight `c : ℕ → ℝ`. -/
theorem sievePoincareExcess_nonneg (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ sievePoincareExcess N c := by
  unfold sievePoincareExcess
  refine Finset.sum_nonneg fun e he => ?_
  have he2 : 2 ≤ e := (Finset.mem_Icc.mp he).1
  have hgap := (two_mul_moebiusReal_le_totient he2).1
  exact mul_nonneg (by linarith) (sq_nonneg _)

/-- For every `N ≥ 1` and weight `c : ℕ → ℝ`, subtracting `(finiteHarmonicSum N c)²` from
`selbergTotientDiagonalForm N c` isolates the `e ∈ [2, N]` Selberg modes:
`selbergTotientDiagonalForm N c - (finiteHarmonicSum N c)² = ∑_{e=2}^N φ(e) Y_{N,c}(e)²`. -/
theorem selbergTotientDiagonalForm_sub_harmonic_sq {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N c - finiteHarmonicSum N c ^ (2 : ℕ) =
      ∑ e ∈ Finset.Icc 2 N, (Nat.totient e : ℝ) * (selbergMultiplesCoord N c e) ^ (2 : ℕ) := by
  unfold selbergTotientDiagonalForm
  have hIcc : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc, Finset.sum_insert (by simp), Nat.totient_one, Nat.cast_one, one_mul,
    selbergMultiplesCoord_one_eq_finiteHarmonicSum]
  ring

/-- **Unconditional Harmonic-Subtracted Spectral Excess Identity
(`two_mul_sieveSuccessorReserve_sub_selberg_add_harmonic_sq_eq_excess`):**
For every `N ≥ 1` and every weight `c : ℕ → ℝ` (even off `ker P`!),
`2 * sieveSuccessorReserve N c - (selbergTotientDiagonalForm N c - (finiteHarmonicSum N c)²) = sievePoincareExcess N c`. -/
theorem two_mul_sieveSuccessorReserve_sub_selberg_add_harmonic_sq_eq_excess
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    2 * sieveSuccessorReserve N c -
        (selbergTotientDiagonalForm N c - finiteHarmonicSum N c ^ (2 : ℕ)) =
      sievePoincareExcess N c := by
  unfold sieveSuccessorReserve sievePoincareExcess
  rw [selbergSubBezoutQuadraticForm_eq_Icc_two hN c,
    selbergTotientDiagonalForm_sub_harmonic_sq hN c, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => by ring

/-- **Unconditional Harmonic-Subtracted Selberg–Bézout Coercivity Law
(`selberg_sub_harmonic_sq_le_two_mul_sieveSuccessorReserve`):**
For **every** `N ≥ 1` and **every** weight `c : ℕ → ℝ` (including `c = moebiusReal` and
`c = pmPowerDampedRealWeight ε`),
`selbergTotientDiagonalForm N c - (finiteHarmonicSum N c)² ≤ 2 * sieveSuccessorReserve N c`. -/
theorem selberg_sub_harmonic_sq_le_two_mul_sieveSuccessorReserve
    {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N c - finiteHarmonicSum N c ^ (2 : ℕ) ≤
      2 * sieveSuccessorReserve N c := by
  have hex := two_mul_sieveSuccessorReserve_sub_selberg_add_harmonic_sq_eq_excess hN c
  have hnn := sievePoincareExcess_nonneg N c
  linarith

/-! ## §2. Universal Sliding-Window Period Invariance -/

/-- At any common divisibility return period `L` (`∀ d ∈ Icc 1 N, d ∣ L`), `sieveSeq N c` is
strictly `L`-periodic on all of `ℕ`: `sieveSeq N c (k + L) = sieveSeq N c k`. -/
theorem sieveSeq_add_of_common_return {N L : ℕ} (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L)
    (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq N c (k + L) = sieveSeq N c k := by
  unfold sieveSeq
  congr 1
  ext d
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hd, hdvd⟩
    exact ⟨hd, (Nat.dvd_add_left (hL d hd)).mp hdvd⟩
  · rintro ⟨hd, hdvd⟩
    exact ⟨hd, dvd_add hdvd (hL d hd)⟩

/-- **Universal Sliding-Window Period Invariance (`sum_Icc_add_period_sub_eq_sum_Icc`):**
For any sequence `F : ℕ → ℝ` that is `L`-periodic on positive integers
(`∀ k ≥ 1, F (k + L) = F k`) and any `M : ℕ`,
`∑ k ∈ Icc 1 (M + L), F k = (∑ k ∈ Icc 1 M, F k) + ∑ k ∈ Icc 1 L, F k`. -/
theorem sum_Icc_add_period_sub_eq_sum_Icc {L : ℕ} {F : ℕ → ℝ}
    (hper : ∀ k : ℕ, 1 ≤ k → F (k + L) = F k) (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 (M + L), F k) =
      (∑ k ∈ Finset.Icc 1 M, F k) + ∑ k ∈ Finset.Icc 1 L, F k := by
  induction M with
  | zero =>
    simp
  | succ M ih =>
    have h1 : M + 1 + L = (M + L) + 1 := by omega
    rw [h1, Finset.sum_Icc_succ_top (by omega : 1 ≤ M + L + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih]
    have h2 : M + L + 1 = (M + 1) + L := by omega
    rw [h2, hper (M + 1) (by omega)]
    ring

/-- For any `L`-periodic sequence `F : ℕ → ℝ` (`∀ k ≥ 1, F (k + L) = F k`) and any shift `M : ℕ`,
the sliding-window sum over `Icc (M + 1) (M + L)` equals the base-period sum over `Icc 1 L`. -/
theorem sum_Icc_sliding_period_eq_sum_Icc {L : ℕ} {F : ℕ → ℝ}
    (hper : ∀ k : ℕ, 1 ≤ k → F (k + L) = F k) (M : ℕ) :
    (∑ k ∈ Finset.Icc (M + 1) (M + L), F k) = ∑ k ∈ Finset.Icc 1 L, F k := by
  have hsplit : Finset.Icc 1 (M + L) = Finset.Icc 1 M ∪ Finset.Icc (M + 1) (M + L) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) (M + L)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2
    omega
  have hadd := sum_Icc_add_period_sub_eq_sum_Icc hper M
  rw [hsplit, Finset.sum_union hdisj] at hadd
  linarith

/-! ## §3. Exact Sliding-Period Laws for `L²` Energy, Lag-1 Correlation, and Prefix Defects -/

/-- **Sliding-Period Mean-Square Law (`sum_sieveSeq_sq_sliding_period_eq`):**
For every common return period `L` (`∀ d ∈ Icc 1 N, d ∣ L`) and every shift `M : ℕ`:
`∑_{k=M+1}^{M+L} s_{N,c}(k)² = L * selbergTotientDiagonalForm N c`. -/
theorem sum_sieveSeq_sq_sliding_period_eq {N L : ℕ} (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L)
    (c : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.Icc (M + 1) (M + L), sieveSeq N c k ^ (2 : ℕ)) =
      (L : ℝ) * selbergTotientDiagonalForm N c := by
  have hper : ∀ k : ℕ, 1 ≤ k → sieveSeq N c (k + L) ^ (2 : ℕ) = sieveSeq N c k ^ (2 : ℕ) := by
    intro k _
    rw [sieveSeq_add_of_common_return hL c k]
  rw [sum_Icc_sliding_period_eq_sum_Icc hper M,
    sum_sieveSeq_sq_eq_selberg_sub_signedLcmFractDefect N L c,
    signedLcmFractDefect_eq_zero_of_common_return c hL, sub_zero]

/-- **Sliding-Period Lag-1 Bézout Correlation Law (`sum_sieveSeq_mul_succ_sliding_period_eq`):**
For every common return period `L` (`∀ d ∈ Icc 1 N, d ∣ L`) and every shift `M : ℕ`:
`∑_{k=M+1}^{M+L} s_{N,c}(k) s_{N,c}(k + 1) = L * bezoutCoprimeQuadraticForm N c`. -/
theorem sum_sieveSeq_mul_succ_sliding_period_eq {N L : ℕ} (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L)
    (c : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.Icc (M + 1) (M + L), sieveSeq N c k * sieveSeq N c (k + 1)) =
      (L : ℝ) * bezoutCoprimeQuadraticForm N c := by
  have hper : ∀ k : ℕ, 1 ≤ k →
      sieveSeq N c (k + L) * sieveSeq N c (k + L + 1) =
        sieveSeq N c k * sieveSeq N c (k + 1) := by
    intro k _
    have h1 : k + L + 1 = (k + 1) + L := by omega
    rw [h1, sieveSeq_add_of_common_return hL c k, sieveSeq_add_of_common_return hL c (k + 1)]
  rw [sum_Icc_sliding_period_eq_sum_Icc hper M,
    sum_sieveSeq_mul_succ_eq_main_add_sawtooth L N c,
    bezoutSawtoothRemainderForm_eq_zero_of_common_return c hL, add_zero]

/-- **Sliding-Period Dirichlet Oscillation Energy Law (`sum_addDiff_sieveSeq_sq_sliding_period_eq`):**
For every common return period `L` (`∀ d ∈ Icc 1 N, d ∣ L`) and every shift `M : ℕ`:
`∑_{k=M+1}^{M+L} (s_{N,c}(k + 1) - s_{N,c}(k))² = 2 * L * sieveSuccessorReserve N c`. -/
theorem sum_addDiff_sieveSeq_sq_sliding_period_eq {N L : ℕ} (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L)
    (c : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.Icc (M + 1) (M + L), (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) =
      2 * (L : ℝ) * sieveSuccessorReserve N c := by
  have hper : ∀ k : ℕ, 1 ≤ k →
      (sieveSeq N c (k + L + 1) - sieveSeq N c (k + L)) ^ (2 : ℕ) =
        (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ) := by
    intro k _
    have h1 : k + L + 1 = (k + 1) + L := by omega
    rw [h1, sieveSeq_add_of_common_return hL c (k + 1), sieveSeq_add_of_common_return hL c k]
  rw [sum_Icc_sliding_period_eq_sum_Icc hper M]
  rcases Nat.eq_zero_or_pos L with rfl | hL_pos
  · simp
  · have hpol := two_mul_sieveRenormalizedPrefixDefect_eq_neg_dirichlet_add_boundary N hL_pos c
    have hren := (sieveCombinedPrefixDefect_eq_zero_of_common_return c hL).2
    have h1L : L + 1 = 1 + L := by omega
    have hbd : sieveSeq N c (L + 1) = sieveSeq N c 1 := by
      rw [h1L]
      exact sieveSeq_add_of_common_return hL c 1
    rw [hbd] at hpol
    linarith

/-- **Exact Period Dissipation of `sieveRenormalizedPrefixDefect` (`sieveRenormalizedPrefixDefect_add_period_eq`):**
For every common return period `L` (`∀ d ∈ Icc 1 N, d ∣ L`) and every `M : ℕ`:
`sieveRenormalizedPrefixDefect N (M + L) c = sieveRenormalizedPrefixDefect N M c - L * sieveSuccessorReserve N c`. -/
theorem sieveRenormalizedPrefixDefect_add_period_eq {N L : ℕ}
    (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L) (c : ℕ → ℝ) (M : ℕ) :
    sieveRenormalizedPrefixDefect N (M + L) c =
      sieveRenormalizedPrefixDefect N M c - (L : ℝ) * sieveSuccessorReserve N c := by
  have hper : ∀ k : ℕ, 1 ≤ k →
      sieveSeq N c (k + L) * (sieveSeq N c (k + L + 1) - sieveSeq N c (k + L)) =
        sieveSeq N c k * (sieveSeq N c (k + 1) - sieveSeq N c k) := by
    intro k _
    have h1 : k + L + 1 = (k + 1) + L := by omega
    rw [h1, sieveSeq_add_of_common_return hL c k, sieveSeq_add_of_common_return hL c (k + 1)]
  rw [sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff N (M + L) c,
    sum_Icc_add_period_sub_eq_sum_Icc hper M,
    ← sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff N M c,
    ← sieveRenormalizedPrefixDefect_eq_sum_mul_addDiff N L c,
    (sieveCombinedPrefixDefect_eq_zero_of_common_return c hL).2]
  ring

/-- **Strict Periodicity of `sieveCombinedPrefixDefect` Across All `M ∈ ℕ`
(`sieveCombinedPrefixDefect_add_period_eq`):**
For every common return period `L` (`∀ d ∈ Icc 1 N, d ∣ L`) and every `M : ℕ`:
`sieveCombinedPrefixDefect N (M + L) c = sieveCombinedPrefixDefect N M c`. -/
theorem sieveCombinedPrefixDefect_add_period_eq {N L : ℕ}
    (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L) (c : ℕ → ℝ) (M : ℕ) :
    sieveCombinedPrefixDefect N (M + L) c = sieveCombinedPrefixDefect N M c := by
  have h1 : sieveCombinedPrefixDefect N (M + L) c =
      sieveRenormalizedPrefixDefect N (M + L) c + ((M + L : ℕ) : ℝ) * sieveSuccessorReserve N c := by
    unfold sieveRenormalizedPrefixDefect
    ring
  have h2 : sieveCombinedPrefixDefect N M c =
      sieveRenormalizedPrefixDefect N M c + (M : ℝ) * sieveSuccessorReserve N c := by
    unfold sieveRenormalizedPrefixDefect
    ring
  rw [h1, h2, sieveRenormalizedPrefixDefect_add_period_eq hL c M]
  push_cast
  ring

/-- Multi-period shift law: for every `q : ℕ`,
`sieveRenormalizedPrefixDefect N (M + q * L) c = sieveRenormalizedPrefixDefect N M c - q * L * sieveSuccessorReserve N c`. -/
theorem sieveRenormalizedPrefixDefect_add_mul_period_eq {N L : ℕ}
    (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L) (c : ℕ → ℝ) (M q : ℕ) :
    sieveRenormalizedPrefixDefect N (M + q * L) c =
      sieveRenormalizedPrefixDefect N M c - (q : ℝ) * (L : ℝ) * sieveSuccessorReserve N c := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hrew : M + (q + 1) * L = (M + q * L) + L := by ring
    rw [hrew, sieveRenormalizedPrefixDefect_add_period_eq hL c (M + q * L), ih]
    push_cast
    ring

/-- **Euclidean Division Decomposition of `sieveRenormalizedPrefixDefect`
(`sieveRenormalizedPrefixDefect_euclidean_decomp`):**
For every common return period `L` (`∀ d ∈ Icc 1 N, d ∣ L`) and every `M : ℕ`, decomposing
`M = (M % L) + (M / L) * L` separates `sieveRenormalizedPrefixDefect N M c` into its bounded
residue-phase defect at `M % L` minus the linear period drift `(M / L) * L * sieveSuccessorReserve N c`. -/
theorem sieveRenormalizedPrefixDefect_euclidean_decomp {N L : ℕ}
    (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L) (c : ℕ → ℝ) (M : ℕ) :
    sieveRenormalizedPrefixDefect N M c =
      sieveRenormalizedPrefixDefect N (M % L) c -
        ((M / L : ℕ) : ℝ) * (L : ℝ) * sieveSuccessorReserve N c := by
  have hdiv : M = M % L + (M / L) * L := by
    have h := (Nat.div_add_mod M L).symm
    linarith [Nat.mul_comm L (M / L)]
  conv_lhs => rw [hdiv]
  exact sieveRenormalizedPrefixDefect_add_mul_period_eq hL c (M % L) (M / L)

/-! ## §4. Scale-Independent Unit-Step Torus Poincaré Inequality for All Divisor Sums -/

/-- **Exact Sliding-Period Spectral Excess Identity (`sliding_period_dirichletEnergy_sub_variance_eq_excess`):**
For every `N ≥ 1`, every common return period `L` (`∀ d ∈ Icc 1 N, d ∣ L`), every shift `M : ℕ`,
and **every** weight `c : ℕ → ℝ` (with no `ker P` hypothesis!):
`∑_{k=M+1}^{M+L} (s_{N,c}(k+1) - s_{N,c}(k))² - (∑_{k=M+1}^{M+L} s_{N,c}(k)² - L * (finiteHarmonicSum N c)²) = L * sievePoincareExcess N c`. -/
theorem sliding_period_dirichletEnergy_sub_variance_eq_excess {N L : ℕ} (hN : 1 ≤ N)
    (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L) (c : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.Icc (M + 1) (M + L), (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ)) -
        ((∑ k ∈ Finset.Icc (M + 1) (M + L), sieveSeq N c k ^ (2 : ℕ)) -
          (L : ℝ) * finiteHarmonicSum N c ^ (2 : ℕ)) =
      (L : ℝ) * sievePoincareExcess N c := by
  rw [sum_addDiff_sieveSeq_sq_sliding_period_eq hL c M,
    sum_sieveSeq_sq_sliding_period_eq hL c M,
    ← two_mul_sieveSuccessorReserve_sub_selberg_add_harmonic_sq_eq_excess hN c]
  ring

/-- **Unconditional Scale-Independent Unit-Step Torus Poincaré Inequality
(`sliding_period_variance_le_dirichletEnergy`):**
For **every** `N ≥ 1`, **every** common return period `L` (`∀ d ∈ Icc 1 N, d ∣ L`, in particular
`L = (Icc 1 N).lcm id` or `L = N!`), **every** shift `M : ℕ`, and **every** real weight `c : ℕ → ℝ`
(including `c = moebiusReal` and `c = pmPowerDampedRealWeight ε`), the centered mean-square energy
over `[M + 1, M + L]` is bounded with **unit Poincaré constant `C = 1`** by the unit-step Dirichlet
oscillation energy:
`∑_{k=M+1}^{M+L} s_{N,c}(k)² - L * (finiteHarmonicSum N c)² ≤ ∑_{k=M+1}^{M+L} (s_{N,c}(k+1) - s_{N,c}(k))²`. -/
theorem sliding_period_variance_le_dirichletEnergy {N L : ℕ} (hN : 1 ≤ N)
    (hL : ∀ d ∈ Finset.Icc 1 N, d ∣ L) (c : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.Icc (M + 1) (M + L), sieveSeq N c k ^ (2 : ℕ)) -
        (L : ℝ) * finiteHarmonicSum N c ^ (2 : ℕ) ≤
      ∑ k ∈ Finset.Icc (M + 1) (M + L), (sieveSeq N c (k + 1) - sieveSeq N c k) ^ (2 : ℕ) := by
  have hex := sliding_period_dirichletEnergy_sub_variance_eq_excess hN hL c M
  have hnn : 0 ≤ (L : ℝ) * sievePoincareExcess N c :=
    mul_nonneg (Nat.cast_nonneg L) (sievePoincareExcess_nonneg N c)
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
