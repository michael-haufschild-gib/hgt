import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonGramMatrixAndRadicalProjection
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TransHorizonRoughAbsorptionAndReset

/-!
# Pillar XVII: Single-Horizon Buchstab–Gram Renormalization, Prime-Horizon Quotient Collapse, and Quadratic-Window Energy Quantization (`BuchstabFermiCovarianceAndQuotientChainBridge`)

In Pillar IX (`TransHorizonGramMatrixAndRadicalProjection`), we established the algebraic Buchstab
`L²` Gram band identity across `[N₁, N₂]`:
$$\mathcal{E}_{N_2}(M; c) - \mathcal{E}_{N_1}(M; c) =
  \sum_{k=1}^M \bigl(\Delta_{N_1, N_2} s_c(k)\bigr)^2 +
    2 \sum_{k=1}^M s_{N_1, c}(k)\,\Delta_{N_1, N_2} s_c(k).$$
However, a genuine operator renormalization theory across the horizon `N → N + 1` requires
evaluating both the band self-energy and the cross-band inner product by reducing the dilated sum
over multiples `k = (N + 1) * j ≤ M` back to the **quotient prefix `1 ≤ j ≤ ⌊M / (N + 1)⌋`** at
horizon `N`.

In this seventeenth foundational pillar of **Trans-Horizon Arithmetic–Archimedean Incidence
Mechanics**, we fuse Pillar IX's Buchstab Gram decomposition with Pillar II's trans-horizon rough
absorption (`IsTransHorizonRough N (N + 1)` whenever `p = N + 1` is prime) to establish the exact
**Horizon-Step Renormalization Calculus** and evaluate it in closed form across the entire
**quadratic trans-horizon regime `p ≤ M < p²`** (spanning `p - 1` trans-horizon octaves):

## Core Main Theorems (100% Unconditional)

1. **Exact Single-Horizon Band Operator & Quotient-Chain Reduction
   (`sieveSeq_succ_horizon_eq_add_ite`, `sieveBandSeq_succ_eq_ite`,
   `sum_Icc_filter_dvd_eq_sum_Icc_div`, `sum_sieveBandSeq_succ_sq_eq`,
   `sum_sieveSeq_mul_sieveBandSeq_succ_eq`, `sieveL2PrefixEnergy_succ_horizon_sub_eq`)**:
   For **every** horizon `N : ℕ`, prefix `M : ℕ`, and weight `c : ℕ → ℝ`:
   - Pointwise, `sieveBandSeq N (N + 1) c k = if N + 1 ∣ k then c (N + 1) else 0`.
   - Indexing the divisible nodes `k = (N + 1) * j ∈ [1, M]` by the quotient chain
     `j ∈ [1, M / (N + 1)]` reduces the horizon-step `L²` Gram difference to:
     $$\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c) =
       c(N + 1)^2 \left\lfloor \frac{M}{N + 1} \right\rfloor +
         2\,c(N + 1) \sum_{j = 1}^{\lfloor M / (N + 1) \rfloor}
           \operatorname{sieveSeq}_N\bigl(c, (N + 1) \cdot j\bigr).$$

2. **Exact Non-Squarefree Horizon-Step Invariance
   (`sieveBandSeq_succ_eq_zero_of_not_squarefree`,
   `sieveL2PrefixEnergy_succ_eq_of_not_squarefree`)**:
   Whenever `¬ Squarefree (N + 1)` and `c` is supported on squarefree integers (such as
   `moebiusReal` or `pmPowerDampedRealWeight ε`), the band operator vanishes identically and the
   prefix `L²` Gram energy is strictly invariant at every scale `M`:
   $$\mathcal{E}_{N+1}(M; c) = \mathcal{E}_N(M; c).$$

3. **Universal Prime-Horizon Renormalization Law via Rough Absorption
   (`sieveSeq_mul_prime_succ_eq`, `sum_sieveSeq_mul_sieveBandSeq_prime_succ_eq`,
   `sieveL2PrefixEnergy_prime_horizon_sub_eq`)**:
   Whenever `p = N + 1` is prime, `p` exceeds `N` and is therefore `N`-rough
   (`isTransHorizonRough_of_prime_gt`). By Pillar II (`sieveSeq_mul_of_isTransHorizonRough`),
   multiplication by `p = N + 1` is **completely invisible** to the sub-horizon sieve:
   $$\operatorname{sieveSeq}_N\bigl(c, (N + 1) \cdot j\bigr) = \operatorname{sieveSeq}_N(c, j)
     \qquad \forall\, j \in \mathbb{N}.$$
   Consequently, for **every** weight `c : ℕ → ℝ` and **every** prefix `M : ℕ`, stepping across a
   prime horizon `p = N + 1` satisfies the exact renormalization fixed-point identity:
   $$\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c) =
     c(N + 1)^2 \left\lfloor \frac{M}{N + 1} \right\rfloor +
       2\,c(N + 1) \sum_{j = 1}^{\lfloor M / (N + 1) \rfloor} \operatorname{sieveSeq}_N(c, j).$$

4. **Quadratic Trans-Horizon Window (`p ≤ M < p²`) Exact Quantization for `moebiusReal` and
   `pmPowerDampedRealWeight ε`
   (`sieveL2PrefixEnergy_moebiusReal_prime_horizon_sub_of_lt_sq`,
   `sieveL2PrefixEnergy_moebiusReal_prime_horizon_first_band_sub`,
   `sieveL2PrefixEnergy_moebiusReal_prime_horizon_second_band_eq`,
   `sieveL2PrefixEnergy_pmPowerDampedRealWeight_prime_horizon_sub_of_lt_sq`,
   `sieveL2PrefixEnergy_pmPowerDampedRealWeight_prime_horizon_first_band_le`)**:
   - Whenever `p = N + 1` is prime and `p ≤ M < p²`, the quotient `Q = ⌊M / p⌋` satisfies
     `1 ≤ Q ≤ N`, so it lies **entirely inside the sub-horizon exact zone of horizon `N`** even
     though `M` can be as large as `p² - 1` (`p - 1` octaves above the horizon)!
   - For `c = moebiusReal`, sub-horizon Möbius inversion (`sum_sieveSeq_moebiusReal_eq_one_of_le`)
     collapses the quotient sum to `∑_{j=1}^Q s_{N,μ}(j) = 1`, forcing the cross-band inner product
     to equal `-1` and yielding the exact quantized step law across the **entire quadratic window
     `p ≤ M < p²`**:
     $$\mathcal{E}_p(M; \mu) - \mathcal{E}_{p-1}(M; \mu) = \left\lfloor \frac{M}{p} \right\rfloor - 2.$$
     In particular, for `p ≤ M < 2p` (`Q = 1`), $\mathcal{E}_p(M; \mu) = \mathcal{E}_{p-1}(M; \mu) - 1$
     (strict energy contraction by `1`), and for `2p ≤ M < 3p` (`Q = 2`),
     $\mathcal{E}_p(M; \mu) = \mathcal{E}_{p-1}(M; \mu)$ (exact energy conservation)!
   - For `c = pmPowerDampedRealWeight ε` (`ε ≥ 0`), on `p ≤ M < p²` the quotient sum equals the
     exact non-negative Euler-product sum `∑_{j=1}^{⌊M/p⌋} g_ε(j) ≥ 1`, and on the first band
     `p ≤ M < 2p` (`⌊M / p⌋ = 1`),
     $$\mathcal{E}_p(M; c_\varepsilon) - \mathcal{E}_{p-1}(M; c_\varepsilon) =
       p^{-2\varepsilon} - 2 p^{-\varepsilon} \le 0.$$
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Single-Horizon Band Operator & Quotient-Chain Reduction -/

/-- **Pointwise Single-Horizon Step Formula for `sieveSeq` (`sieveSeq_succ_horizon_eq_add_ite`):**
For every `N, k : ℕ` and weight `c : ℕ → ℝ`, stepping the sieve cutoff from `N` to `N + 1` adds
`c (N + 1)` if `N + 1 ∣ k` and `0` otherwise. -/
theorem sieveSeq_succ_horizon_eq_add_ite (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    sieveSeq (N + 1) c k = sieveSeq N c k + (if N + 1 ∣ k then c (N + 1) else 0) := by
  unfold sieveSeq
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- **Pointwise Single-Horizon Band Operator (`sieveBandSeq_succ_eq_ite`):**
For every `N, k : ℕ` and weight `c : ℕ → ℝ`:
`sieveBandSeq N (N + 1) c k = if N + 1 ∣ k then c (N + 1) else 0`. -/
theorem sieveBandSeq_succ_eq_ite (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    sieveBandSeq N (N + 1) c k = if N + 1 ∣ k then c (N + 1) else 0 := by
  unfold sieveBandSeq
  rw [sieveSeq_succ_horizon_eq_add_ite]
  ring

/-- **Quotient-Chain Bijection for Multiples in `[1, M]` (`sum_Icc_filter_dvd_eq_sum_Icc_div`):**
For any `d ≥ 1`, `M : ℕ`, and function `f : ℕ → ℝ`, summing `f k` over multiples `d ∣ k` in
`Finset.Icc 1 M` equals summing `f (d * j)` over `j ∈ Finset.Icc 1 (M / d)`. -/
theorem sum_Icc_filter_dvd_eq_sum_Icc_div {d : ℕ} (hd : 0 < d) (M : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ (Finset.Icc 1 M).filter (fun k => d ∣ k), f k) =
      ∑ j ∈ Finset.Icc 1 (M / d), f (d * j) := by
  have hbij : (Finset.Icc 1 M).filter (fun k => d ∣ k) =
      (Finset.Icc 1 (M / d)).image (fun j => d * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hk1, hkM⟩, ⟨j, rfl⟩⟩
      have hj1 : 1 ≤ j := by
        by_contra h
        have hj0 : j = 0 := by omega
        subst hj0
        omega
      have hjM : j ≤ M / d := (Nat.le_div_iff_mul_le hd).mpr (by linarith)
      exact ⟨j, ⟨hj1, hjM⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hjM⟩, rfl⟩
      have hk1 : 1 ≤ d * j := Nat.mul_pos hd hj1
      have hkM : d * j ≤ M := by
        have h := (Nat.le_div_iff_mul_le hd).mp hjM
        linarith
      exact ⟨⟨hk1, hkM⟩, dvd_mul_right d j⟩
  rw [hbij, Finset.sum_image]
  intro j₁ _ j₂ _ hmul
  exact Nat.eq_of_mul_eq_mul_left hd hmul

/-- **Single-Horizon Band Self-Energy Formula (`sum_sieveBandSeq_succ_sq_eq`):**
For every `N, M : ℕ` and weight `c : ℕ → ℝ`:
`∑_{k=1}^M sieveBandSeq N (N + 1) c k ^ 2 = c (N + 1) ^ 2 * ⌊M / (N + 1)⌋`. -/
theorem sum_sieveBandSeq_succ_sq_eq (N M : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, sieveBandSeq N (N + 1) c k ^ (2 : ℕ)) =
      c (N + 1) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ) := by
  have hpt : ∀ k ∈ Finset.Icc 1 M,
      sieveBandSeq N (N + 1) c k ^ (2 : ℕ) =
        if N + 1 ∣ k then c (N + 1) ^ (2 : ℕ) else 0 := by
    intro k _
    rw [sieveBandSeq_succ_eq_ite]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter,
    sum_Icc_filter_dvd_eq_sum_Icc_div (Nat.succ_pos N) M (fun _ => c (N + 1) ^ (2 : ℕ)),
    Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_comm]

/-- **Single-Horizon Cross-Band Inner Product via Quotient Chain
(`sum_sieveSeq_mul_sieveBandSeq_succ_eq`):**
For every `N, M : ℕ` and weight `c : ℕ → ℝ`:
`∑_{k=1}^M s_{N,c}(k) Δ_{N, N+1} s_c(k) = c(N + 1) * ∑_{j=1}^{⌊M/(N+1)⌋} s_{N,c}((N + 1) * j)`. -/
theorem sum_sieveSeq_mul_sieveBandSeq_succ_eq (N M : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, sieveSeq N c k * sieveBandSeq N (N + 1) c k) =
      c (N + 1) * ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c ((N + 1) * j) := by
  have hpt : ∀ k ∈ Finset.Icc 1 M,
      sieveSeq N c k * sieveBandSeq N (N + 1) c k =
        if N + 1 ∣ k then c (N + 1) * sieveSeq N c k else 0 := by
    intro k _
    rw [sieveBandSeq_succ_eq_ite]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter,
    sum_Icc_filter_dvd_eq_sum_Icc_div (Nat.succ_pos N) M (fun k => c (N + 1) * sieveSeq N c k),
    ← Finset.mul_sum]

/-- **Universal Single-Horizon Buchstab–Gram Energy Step Law
(`sieveL2PrefixEnergy_succ_horizon_sub_eq`):**
For every `N, M : ℕ` and weight `c : ℕ → ℝ`:
$$\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c) =
  c(N + 1)^2 \left\lfloor \frac{M}{N + 1} \right\rfloor +
    2\,c(N + 1) \sum_{j = 1}^{\lfloor M / (N + 1) \rfloor}
      \operatorname{sieveSeq}_N\bigl(c, (N + 1) \cdot j\bigr).$$ -/
theorem sieveL2PrefixEnergy_succ_horizon_sub_eq (N M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c =
      c (N + 1) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ) +
        2 * c (N + 1) * ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c ((N + 1) * j) := by
  rw [sieveL2PrefixEnergy_horizon_band_sub N (N + 1) M c,
    sum_sieveBandSeq_succ_sq_eq, sum_sieveSeq_mul_sieveBandSeq_succ_eq]
  ring

/-! ## §2. Exact Non-Squarefree Horizon-Step Invariance -/

/-- Whenever `¬ Squarefree (N + 1)` and `c` is supported on squarefree numbers, the horizon-step
band sequence `sieveBandSeq N (N + 1) c` vanishes identically. -/
theorem sieveBandSeq_succ_eq_zero_of_not_squarefree (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) (hnsq : ¬ Squarefree (N + 1)) (k : ℕ) :
    sieveBandSeq N (N + 1) c k = 0 := by
  rw [sieveBandSeq_succ_eq_ite, hc (N + 1) hnsq]
  split_ifs <;> rfl

/-- **Exact Non-Squarefree Horizon-Step Invariance (`sieveL2PrefixEnergy_succ_eq_of_not_squarefree`):**
Whenever `¬ Squarefree (N + 1)` and `c` vanishes outside squarefree numbers, stepping the horizon
from `N` to `N + 1` leaves `sieveL2PrefixEnergy` strictly invariant for all `M : ℕ`. -/
theorem sieveL2PrefixEnergy_succ_eq_of_not_squarefree (N M : ℕ) {c : ℕ → ℝ}
    (hc : ∀ s : ℕ, ¬ Squarefree s → c s = 0) (hnsq : ¬ Squarefree (N + 1)) :
    sieveL2PrefixEnergy (N + 1) M c = sieveL2PrefixEnergy N M c := by
  have hsub := sieveL2PrefixEnergy_succ_horizon_sub_eq N M c
  rw [hc (N + 1) hnsq] at hsub
  linarith

/-! ## §3. Universal Prime-Horizon Renormalization Law via Rough Absorption -/

/-- **Prime-Horizon Quotient Invariance (`sieveSeq_mul_prime_succ_eq`):**
Whenever `p = N + 1` is prime, `N + 1` is trans-horizon rough above `N`, so for every weight
`c : ℕ → ℝ` and every `j : ℕ`:
`sieveSeq N c ((N + 1) * j) = sieveSeq N c j`. -/
theorem sieveSeq_mul_prime_succ_eq {N : ℕ} (hp : (N + 1).Prime) (c : ℕ → ℝ) (j : ℕ) :
    sieveSeq N c ((N + 1) * j) = sieveSeq N c j := by
  have hrough : IsTransHorizonRough N (N + 1) :=
    isTransHorizonRough_of_prime_gt hp (Nat.lt_succ_self N)
  rw [mul_comm, sieveSeq_mul_of_isTransHorizonRough hrough c j]

/-- **Prime-Horizon Cross-Band Inner Product Reduction
(`sum_sieveSeq_mul_sieveBandSeq_prime_succ_eq`):**
Whenever `p = N + 1` is prime, the cross-band inner product between `sieveSeq N c` and
`sieveBandSeq N (N + 1) c` on `[1, M]` reduces directly to the undilated quotient sum of
`sieveSeq N c` on `[1, M / (N + 1)]`. -/
theorem sum_sieveSeq_mul_sieveBandSeq_prime_succ_eq {N : ℕ} (hp : (N + 1).Prime)
    (M : ℕ) (c : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 M, sieveSeq N c k * sieveBandSeq N (N + 1) c k) =
      c (N + 1) * ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c j := by
  rw [sum_sieveSeq_mul_sieveBandSeq_succ_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => sieveSeq_mul_prime_succ_eq hp c j

/-- **Universal Prime-Horizon `L²` Renormalization Identity
(`sieveL2PrefixEnergy_prime_horizon_sub_eq`):**
Whenever `p = N + 1` is prime, for every weight `c : ℕ → ℝ` and every prefix `M : ℕ`:
$$\mathcal{E}_{N+1}(M; c) - \mathcal{E}_N(M; c) =
  c(N + 1)^2 \left\lfloor \frac{M}{N + 1} \right\rfloor +
    2\,c(N + 1) \sum_{j = 1}^{\lfloor M / (N + 1) \rfloor} \operatorname{sieveSeq}_N(c, j).$$ -/
theorem sieveL2PrefixEnergy_prime_horizon_sub_eq {N : ℕ} (hp : (N + 1).Prime)
    (M : ℕ) (c : ℕ → ℝ) :
    sieveL2PrefixEnergy (N + 1) M c - sieveL2PrefixEnergy N M c =
      c (N + 1) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ) +
        2 * c (N + 1) * ∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N c j := by
  rw [sieveL2PrefixEnergy_succ_horizon_sub_eq]
  congr 2
  refine Finset.sum_congr rfl fun j _ => sieveSeq_mul_prime_succ_eq hp c j

/-! ## §4. Quadratic Trans-Horizon Window (`p ≤ M < p²`) Exact Quantization for `moebiusReal` and `pmPowerDampedRealWeight ε` -/

/-- Whenever `N + 1 ≤ M` and `M < (N + 1) ^ 2`, the quotient `M / (N + 1)` lies in the sub-horizon
exact zone `1 ≤ M / (N + 1) ≤ N`. -/
theorem div_succ_bounds_of_ge_of_lt_sq {N M : ℕ}
    (hlo : N + 1 ≤ M) (hhi : M < (N + 1) ^ (2 : ℕ)) :
    1 ≤ M / (N + 1) ∧ M / (N + 1) ≤ N := by
  have hpos : 0 < N + 1 := Nat.succ_pos N
  have h1 : 1 ≤ M / (N + 1) := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
  have hlt : M / (N + 1) < N + 1 := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    simpa only [sq] using hhi
  exact ⟨h1, by omega⟩

/-- **Quadratic Trans-Horizon Window (`p ≤ M < p²`) Exact Quantization for `moebiusReal`
(`sieveL2PrefixEnergy_moebiusReal_prime_horizon_sub_of_lt_sq`):**
Whenever `p = N + 1` is prime and `N + 1 ≤ M < (N + 1)²` (spanning `N` trans-horizon octaves above
`N + 1`), sub-horizon Möbius inversion collapses the quotient sum to `1`, forcing the cross-band
inner product to equal `-1` and the `L²` Gram energy step to equal `⌊M / (N + 1)⌋ - 2`:
$$\mathcal{E}_{N+1}(M; \mu) - \mathcal{E}_N(M; \mu) = \left\lfloor \frac{M}{N + 1} \right\rfloor - 2.$$ -/
theorem sieveL2PrefixEnergy_moebiusReal_prime_horizon_sub_of_lt_sq {N M : ℕ}
    (hp : (N + 1).Prime) (hlo : N + 1 ≤ M) (hhi : M < (N + 1) ^ (2 : ℕ)) :
    (∑ k ∈ Finset.Icc 1 M,
        sieveSeq N moebiusReal k * sieveBandSeq N (N + 1) moebiusReal k) = -1 ∧
      sieveL2PrefixEnergy (N + 1) M moebiusReal - sieveL2PrefixEnergy N M moebiusReal =
        ((M / (N + 1) : ℕ) : ℝ) - 2 := by
  obtain ⟨hq1, hqN⟩ := div_succ_bounds_of_ge_of_lt_sq hlo hhi
  have hsum : (∑ j ∈ Finset.Icc 1 (M / (N + 1)), sieveSeq N moebiusReal j) = 1 :=
    sum_sieveSeq_moebiusReal_eq_one_of_le hq1 hqN
  have hmu : moebiusReal (N + 1) = -1 := by
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime hp]
  have hcov : (∑ k ∈ Finset.Icc 1 M,
      sieveSeq N moebiusReal k * sieveBandSeq N (N + 1) moebiusReal k) = -1 := by
    rw [sum_sieveSeq_mul_sieveBandSeq_prime_succ_eq hp M moebiusReal, hmu, hsum]
    ring
  refine ⟨hcov, ?_⟩
  rw [sieveL2PrefixEnergy_prime_horizon_sub_eq hp M moebiusReal, hmu, hsum]
  ring

/-- **First-Band Strict Energy Contraction at Prime Horizons for `moebiusReal`
(`sieveL2PrefixEnergy_moebiusReal_prime_horizon_first_band_sub`):**
Whenever `p = N + 1` is prime and `N + 1 ≤ M < 2 * (N + 1)`, stepping the horizon from `N` to
`N + 1` strictly decreases the prefix `L²` Gram energy of `moebiusReal` by exactly `1`:
`sieveL2PrefixEnergy (N + 1) M moebiusReal = sieveL2PrefixEnergy N M moebiusReal - 1`. -/
theorem sieveL2PrefixEnergy_moebiusReal_prime_horizon_first_band_sub {N M : ℕ}
    (hp : (N + 1).Prime) (hlo : N + 1 ≤ M) (hhi : M < 2 * (N + 1)) :
    sieveL2PrefixEnergy (N + 1) M moebiusReal - sieveL2PrefixEnergy N M moebiusReal = -1 := by
  have hp2 : 2 ≤ N + 1 := hp.two_le
  have hsq : M < (N + 1) ^ (2 : ℕ) := by nlinarith
  have hdiv : M / (N + 1) = 1 := by
    have h1 : 1 ≤ M / (N + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos N)).mpr (by omega)
    have h2 : M / (N + 1) < 2 := (Nat.div_lt_iff_lt_mul (Nat.succ_pos N)).mpr (by omega)
    omega
  rw [(sieveL2PrefixEnergy_moebiusReal_prime_horizon_sub_of_lt_sq hp hlo hsq).2, hdiv]
  norm_num

/-- **Second-Band Exact Energy Conservation at Prime Horizons for `moebiusReal`
(`sieveL2PrefixEnergy_moebiusReal_prime_horizon_second_band_eq`):**
Whenever `p = N + 1` is prime (`p ≥ 3`) and `2 * (N + 1) ≤ M < 3 * (N + 1)`, the band self-energy
`+2` and twice the cross-band inner product `-2` cancel identically:
`sieveL2PrefixEnergy (N + 1) M moebiusReal = sieveL2PrefixEnergy N M moebiusReal`. -/
theorem sieveL2PrefixEnergy_moebiusReal_prime_horizon_second_band_eq {N M : ℕ}
    (hp : (N + 1).Prime) (hp3 : 3 ≤ N + 1)
    (hlo : 2 * (N + 1) ≤ M) (hhi : M < 3 * (N + 1)) :
    sieveL2PrefixEnergy (N + 1) M moebiusReal = sieveL2PrefixEnergy N M moebiusReal := by
  have hsq : M < (N + 1) ^ (2 : ℕ) := by nlinarith
  have hdiv : M / (N + 1) = 2 := by
    have h2 : 2 ≤ M / (N + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos N)).mpr (by omega)
    have h3 : M / (N + 1) < 3 := (Nat.div_lt_iff_lt_mul (Nat.succ_pos N)).mpr (by omega)
    omega
  have hsub := (sieveL2PrefixEnergy_moebiusReal_prime_horizon_sub_of_lt_sq
    hp (by omega : N + 1 ≤ M) hsq).2
  rw [hdiv] at hsub
  norm_num at hsub
  linarith

/-- **Quadratic Trans-Horizon Window (`p ≤ M < p²`) Exact Evaluation for `pmPowerDampedRealWeight ε`
(`sieveL2PrefixEnergy_pmPowerDampedRealWeight_prime_horizon_sub_of_lt_sq`):**
Whenever `p = N + 1` is prime and `N + 1 ≤ M < (N + 1)²`, for every `ε : ℝ`, the quotient sum of
`sieveSeq N (pmPowerDampedRealWeight ε)` reduces to the exact sub-horizon Euler-product sum
`∑_{j=1}^{⌊M/(N+1)⌋} pmPowerDampedDivisorCoeff ε j`:
$$\mathcal{E}_{N+1}(M; c_\varepsilon) - \mathcal{E}_N(M; c_\varepsilon) =
  (N + 1)^{-2\varepsilon} \left\lfloor \frac{M}{N + 1} \right\rfloor -
    2 (N + 1)^{-\varepsilon} \sum_{j = 1}^{\lfloor M / (N + 1) \rfloor} g_\varepsilon(j).$$ -/
theorem sieveL2PrefixEnergy_pmPowerDampedRealWeight_prime_horizon_sub_of_lt_sq
    (ε : ℝ) {N M : ℕ} (hp : (N + 1).Prime)
    (hlo : N + 1 ≤ M) (hhi : M < (N + 1) ^ (2 : ℕ)) :
    sieveL2PrefixEnergy (N + 1) M (pmPowerDampedRealWeight ε) -
        sieveL2PrefixEnergy N M (pmPowerDampedRealWeight ε) =
      (((N + 1 : ℕ) : ℝ) ^ (-ε)) ^ (2 : ℕ) * ((M / (N + 1) : ℕ) : ℝ) -
        2 * ((N + 1 : ℕ) : ℝ) ^ (-ε) *
          ∑ j ∈ Finset.Icc 1 (M / (N + 1)), pmPowerDampedDivisorCoeff ε j := by
  obtain ⟨_, hqN⟩ := div_succ_bounds_of_ge_of_lt_sq hlo hhi
  have hcw : pmPowerDampedRealWeight ε (N + 1) = -(((N + 1 : ℕ) : ℝ) ^ (-ε)) := by
    unfold pmPowerDampedRealWeight
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime hp]
  have hsum : (∑ j ∈ Finset.Icc 1 (M / (N + 1)),
      sieveSeq N (pmPowerDampedRealWeight ε) j) =
      ∑ j ∈ Finset.Icc 1 (M / (N + 1)), pmPowerDampedDivisorCoeff ε j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨hj1, hjQ⟩ := Finset.mem_Icc.mp hj
    exact sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hj1 (hjQ.trans hqN)
  rw [sieveL2PrefixEnergy_prime_horizon_sub_eq hp M (pmPowerDampedRealWeight ε), hcw, hsum]
  ring

/-- **First-Band Energy Contraction at Prime Horizons for `pmPowerDampedRealWeight ε`
(`sieveL2PrefixEnergy_pmPowerDampedRealWeight_prime_horizon_first_band_le`):**
For every `ε ≥ 0`, prime `p = N + 1`, and `N + 1 ≤ M < 2 * (N + 1)`:
$$\mathcal{E}_{N+1}(M; c_\varepsilon) - \mathcal{E}_N(M; c_\varepsilon) =
  (N + 1)^{-2\varepsilon} - 2 (N + 1)^{-\varepsilon} \le 0.$$ -/
theorem sieveL2PrefixEnergy_pmPowerDampedRealWeight_prime_horizon_first_band_le
    {ε : ℝ} (hε : 0 ≤ ε) {N M : ℕ} (hp : (N + 1).Prime)
    (hlo : N + 1 ≤ M) (hhi : M < 2 * (N + 1)) :
    sieveL2PrefixEnergy (N + 1) M (pmPowerDampedRealWeight ε) -
        sieveL2PrefixEnergy N M (pmPowerDampedRealWeight ε) =
      (((N + 1 : ℕ) : ℝ) ^ (-ε)) ^ (2 : ℕ) - 2 * ((N + 1 : ℕ) : ℝ) ^ (-ε) ∧
      sieveL2PrefixEnergy (N + 1) M (pmPowerDampedRealWeight ε) ≤
        sieveL2PrefixEnergy N M (pmPowerDampedRealWeight ε) := by
  have hp2 : 2 ≤ N + 1 := hp.two_le
  have hsq : M < (N + 1) ^ (2 : ℕ) := by nlinarith
  have hdiv : M / (N + 1) = 1 := by
    have h1 : 1 ≤ M / (N + 1) := (Nat.le_div_iff_mul_le (Nat.succ_pos N)).mpr (by omega)
    have h2 : M / (N + 1) < 2 := (Nat.div_lt_iff_lt_mul (Nat.succ_pos N)).mpr (by omega)
    omega
  have heq := sieveL2PrefixEnergy_pmPowerDampedRealWeight_prime_horizon_sub_of_lt_sq
    ε hp hlo hsq
  rw [hdiv] at heq
  simp only [Finset.Icc_self, Finset.sum_singleton, pmPowerDampedDivisorCoeff_one,
    Nat.cast_one, mul_one] at heq
  have hr_nonneg : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ (-ε) := by positivity
  have hr_le_one : ((N + 1 : ℕ) : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_le) (by linarith)
  exact ⟨heq, by nlinarith⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
