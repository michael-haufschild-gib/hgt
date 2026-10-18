import GaloisForLFunctions.BezoutValuationIncidence.OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError

/-!
# Energy-Centered and Mean-Centered Pronic Gram Positivity, Rank-1 Von Mangoldt Lower Bound, and Prime-Dilation Transfer

In `ShortHorizonPronicDiscrepancyAndVonMangoldtDuality` and `TruncatedPronicGramMatrixAndFiniteHorizonVonMangoldtApproximation`,
we established that the infinite pronic-weighted squared discrepancy series
$$\sum_{M=1}^\infty \frac{\operatorname{sievePrefixDiscrepancy}(N, M, c)^2}{\operatorname{pronicSeq}(M)}$$
converges unconditionally to the non-periodic Ramanujan Gram quadratic form
$$\operatorname{sievePronicDiscrepancyGramForm}(N, c) =
  \sum_{p=2}^N \sum_{q=2}^N Y_{N,c}(p)\,Y_{N,c}(q)\,\operatorname{pmRamanujanPrimitiveGram}(p, q).$$

In this module, we complete **Step 5** of the Wall 1 Bézout programme by proving the spectral
decomposition, positive semi-definiteness, rank-1 von Mangoldt lower bound, and prime-dilation
transfer laws of the energy-centered and mean-centered pronic Gram matrices:

1. **Energy-Centered Sieve Discrepancy, Pronic Series & Positive Semi-Definiteness of `pmRamanujanEnergyCenteredGram`
   (`sieveEnergyCenteredPrefixDiscrepancy`,
   `sieveEnergyCenteredPrefixDiscrepancy_eq_add_vonMangoldt`,
   `hasSum_sieveEnergyCenteredPrefixDiscrepancy_div_pronicSeq`,
   `tsum_sieveEnergyCenteredPrefixDiscrepancy_div_pronicSeq`,
   `sieveEnergyCenteredPronicGramForm`,
   `hasSum_sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq`,
   `tsum_sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq`,
   `sieveEnergyCenteredPronicGramForm_nonneg`):**
   - The energy-centered discrepancy
     $$\operatorname{sieveEnergyCenteredPrefixDiscrepancy}(N, M, c) =
       \operatorname{sievePrefixDiscrepancy}(N, M, c) +
       \sum_{e=2}^N \Lambda(e)\,Y_{N,c}(e)$$
     has pronic mean $0$ ($\sum_{M=1}^\infty \frac{\operatorname{sieveEnergyCenteredPrefixDiscrepancy}(N, M, c)}{\operatorname{pronicSeq}(M)} = 0$).
   - Its squared pronic series converges unconditionally to `sieveEnergyCenteredPronicGramForm N c`,
     which is therefore **unconditionally non-negative** (`0 ≤ sieveEnergyCenteredPronicGramForm N c`).

2. **Rank-1 Von Mangoldt Decomposition & Sharp Lower Bound on `sievePronicDiscrepancyGramForm`
   (`sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered`,
   `vonMangoldt_sum_sq_le_sievePronicDiscrepancyGramForm`,
   `abs_vonMangoldt_sum_le_sqrt_sievePronicDiscrepancyGramForm`):**
   - For every cutoff $N$ and sieve weight $c$:
     $$\operatorname{sievePronicDiscrepancyGramForm}(N, c) =
       \left(\sum_{e=2}^N \Lambda(e)\,Y_{N,c}(e)\right)^2 +
       \operatorname{sieveEnergyCenteredPronicGramForm}(N, c)
       \ge \left(\sum_{e=2}^N \Lambda(e)\,Y_{N,c}(e)\right)^2,$$
     and $\bigl|\sum_{e=2}^N \Lambda(e)\,Y_{N,c}(e)\bigr| \le \sqrt{\operatorname{sievePronicDiscrepancyGramForm}(N, c)}$.

3. **Mean-Centered Pronic Gram Quadratic Form, Positive Semi-Definiteness & Bilinear Decomposition
   (`sieveMeanCenteredPronicGramForm`,
   `hasSum_sieveMeanCenteredPrefixDiscrepancy_sq_div_pronicSeq`,
   `tsum_sieveMeanCenteredPrefixDiscrepancy_sq_div_pronicSeq`,
   `sieveMeanCenteredPronicGramForm_nonneg`,
   `sievePronicDiscrepancyGramForm_eq_meanCentered_add`):**
   - The squared pronic series of `sieveMeanCenteredPrefixDiscrepancy N M c` converges unconditionally
     to `sieveMeanCenteredPronicGramForm N c ≥ 0`, yielding the exact decomposition of
     `sievePronicDiscrepancyGramForm N c` into the positive semi-definite mean-centered Gram form
     plus the bilinear coupling between the von Mangoldt functional $\sum_{e=2}^N \Lambda(e) Y_{N,c}(e)$
     and the totient functional $\sum_{e=2}^N \varphi(e) Y_{N,c}(e)$.

4. **Prime-Dilation Transfer from the Rank-1 Von Mangoldt Channel to `pmRamanujanEnergyCenteredGram`
   (`vonMangoldt_prime_mul_eq_zero_of_not_dvd`,
   `pmRamanujanEnergyCenteredGram_prime_mul_left_eq`,
   `pmRamanujanEnergyCenteredGram_prime_pair`,
   `pmRamanujanEnergyCenteredGram_prime_mul_diag`):**
   - Whenever $p$ is prime, $q, r > 1$, $\neg(p \mid q)$, and $\neg(p \mid r)$, coprime prime
     dilation annihilates the von Mangoldt weight ($\Lambda(p q) = \Lambda(p r) = 0$) and transfers
     the rank-1 prime-power product $(p - 1)\Lambda(q)\Lambda(r)$ directly into the energy-centered
     Gram recurrence:
     $$\mathcal{G}^{\text{ec}}(p q, p r) + \mathcal{G}^{\text{ec}}(p q, r) + \mathcal{G}^{\text{ec}}(q, p r) =
       (p - 1)\,\mathcal{G}^{\text{ec}}(q, r) + (p - 1)\,\Lambda(q)\,\Lambda(r).$$
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Energy-Centered Sieve Discrepancy & Positive Semi-Definiteness of `pmRamanujanEnergyCenteredGram` -/

/-- **Energy-Centered Sieve Prefix Discrepancy (`sieveEnergyCenteredPrefixDiscrepancy`):**
The pronic-zero-mean discrepancy obtained by replacing each dual primitive
`(pmRamanujanPrimitive e M).re` by `pmRamanujanEnergyCenteredPrimitive e M = (pmRamanujanPrimitive e M).re + vonMangoldt e`. -/
def sieveEnergyCenteredPrefixDiscrepancy (N M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ e ∈ Finset.Icc 2 N,
    selbergMultiplesCoord N c e * pmRamanujanEnergyCenteredPrimitive e M

/-- **Exact Shift Formula for `sieveEnergyCenteredPrefixDiscrepancy`
(`sieveEnergyCenteredPrefixDiscrepancy_eq_add_vonMangoldt`):**
For every `N, M : ℕ` and `c : ℕ → ℝ`:
`sieveEnergyCenteredPrefixDiscrepancy N M c = sievePrefixDiscrepancy N M c + ∑ e ∈ Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e`. -/
theorem sieveEnergyCenteredPrefixDiscrepancy_eq_add_vonMangoldt
    (N M : ℕ) (c : ℕ → ℝ) :
    sieveEnergyCenteredPrefixDiscrepancy N M c =
      sievePrefixDiscrepancy N M c +
        ∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e := by
  unfold sieveEnergyCenteredPrefixDiscrepancy
  rw [sievePrefixDiscrepancy_eq_ramanujan_diagonal N M c, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold pmRamanujanEnergyCenteredPrimitive
  ring

/-- **Zero Pronic Mean of `sieveEnergyCenteredPrefixDiscrepancy`
(`hasSum_sieveEnergyCenteredPrefixDiscrepancy_div_pronicSeq`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`, the pronic-weighted series of
`sieveEnergyCenteredPrefixDiscrepancy N M c` has exact sum `0`. -/
theorem hasSum_sieveEnergyCenteredPrefixDiscrepancy_div_pronicSeq
    (N : ℕ) (c : ℕ → ℝ) :
    HasSum (fun M : ℕ => sieveEnergyCenteredPrefixDiscrepancy N M c / (pronicSeq M : ℝ)) 0 := by
  have h1 := hasSum_sievePrefixDiscrepancy_div_pronicSeq N c
  have h2 := hasSum_one_div_pronicSeq_nat.mul_left
    (∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e)
  rw [mul_one] at h2
  have h := h1.add h2
  rw [neg_add_cancel] at h
  refine h.congr_fun fun M => ?_
  rw [sieveEnergyCenteredPrefixDiscrepancy_eq_add_vonMangoldt]
  ring

/-- `tsum` formula showing that `∑' M, sieveEnergyCenteredPrefixDiscrepancy N M c / pronicSeq M = 0`. -/
theorem tsum_sieveEnergyCenteredPrefixDiscrepancy_div_pronicSeq
    (N : ℕ) (c : ℕ → ℝ) :
    (∑' M : ℕ, sieveEnergyCenteredPrefixDiscrepancy N M c / (pronicSeq M : ℝ)) = 0 :=
  (hasSum_sieveEnergyCenteredPrefixDiscrepancy_div_pronicSeq N c).tsum_eq

/-- **The Energy-Centered Pronic Gram Quadratic Form (`sieveEnergyCenteredPronicGramForm`):**
The quadratic form on `selbergMultiplesCoord N c` induced by `pmRamanujanEnergyCenteredGram p q`. -/
def sieveEnergyCenteredPronicGramForm (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
    selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
      pmRamanujanEnergyCenteredGram p q

/-- Pointwise bilinear expansion of `(sieveEnergyCenteredPrefixDiscrepancy N M c)² / pronicSeq M`. -/
theorem sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq_eq
    (N M : ℕ) (c : ℕ → ℝ) :
    (sieveEnergyCenteredPrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ) =
      ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
        selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
          (pmRamanujanEnergyCenteredPrimitive p M *
            pmRamanujanEnergyCenteredPrimitive q M / ((M : ℝ) * ((M : ℝ) + 1))) := by
  rw [cast_pronicSeq_eq M]
  unfold sieveEnergyCenteredPrefixDiscrepancy
  rw [sq, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **Exact Pronic Series Representation of `sieveEnergyCenteredPronicGramForm`
(`hasSum_sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`, the pronic-weighted squared series of
`sieveEnergyCenteredPrefixDiscrepancy N M c` converges unconditionally to
`sieveEnergyCenteredPronicGramForm N c`. -/
theorem hasSum_sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq
    (N : ℕ) (c : ℕ → ℝ) :
    HasSum (fun M : ℕ =>
      (sieveEnergyCenteredPrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ))
      (sieveEnergyCenteredPronicGramForm N c) := by
  have hs : HasSum
      (fun M : ℕ => ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
        selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
          (pmRamanujanEnergyCenteredPrimitive p M *
            pmRamanujanEnergyCenteredPrimitive q M / ((M : ℝ) * ((M : ℝ) + 1))))
      (sieveEnergyCenteredPronicGramForm N c) := by
    unfold sieveEnergyCenteredPronicGramForm
    apply hasSum_sum
    intro p hp
    apply hasSum_sum
    intro q hq
    have hp1 : 1 < p := by have := (Finset.mem_Icc.mp hp).1; omega
    have hq1 : 1 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    have hterm := hasSum_pmRamanujanEnergyCenteredGram hp1 hq1
    have hval : pmRamanujanPrimitiveGram p q - vonMangoldt p * vonMangoldt q =
        pmRamanujanEnergyCenteredGram p q := by
      linarith [pmRamanujanPrimitiveGram_eq_energyCentered hp1 hq1]
    rw [hval] at hterm
    exact hterm.mul_left _
  exact hs.congr_fun fun M => sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq_eq N M c

/-- `tsum` formula for `sieveEnergyCenteredPronicGramForm N c`. -/
theorem tsum_sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq
    (N : ℕ) (c : ℕ → ℝ) :
    (∑' M : ℕ, (sieveEnergyCenteredPrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ)) =
      sieveEnergyCenteredPronicGramForm N c :=
  (hasSum_sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq N c).tsum_eq

/-- **Unconditional Positive Semi-Definiteness of `sieveEnergyCenteredPronicGramForm`
(`sieveEnergyCenteredPronicGramForm_nonneg`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`,
`0 ≤ sieveEnergyCenteredPronicGramForm N c`. -/
theorem sieveEnergyCenteredPronicGramForm_nonneg (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ sieveEnergyCenteredPronicGramForm N c := by
  rw [← tsum_sieveEnergyCenteredPrefixDiscrepancy_sq_div_pronicSeq]
  exact tsum_nonneg fun M => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-! ## §2. Rank-1 Von Mangoldt Decomposition & Sharp Lower Bound on `sievePronicDiscrepancyGramForm` -/

/-- **Exact Rank-1 Von Mangoldt + Energy-Centered Decomposition of `sievePronicDiscrepancyGramForm`
(`sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`:
`sievePronicDiscrepancyGramForm N c = (∑ e ∈ Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e)² + sieveEnergyCenteredPronicGramForm N c`. -/
theorem sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered
    (N : ℕ) (c : ℕ → ℝ) :
    sievePronicDiscrepancyGramForm N c =
      (∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) ^ (2 : ℕ) +
        sieveEnergyCenteredPronicGramForm N c := by
  unfold sievePronicDiscrepancyGramForm sieveEnergyCenteredPronicGramForm
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hp1 : 1 < p := by have := (Finset.mem_Icc.mp hp).1; omega
  have hq1 : 1 < q := by have := (Finset.mem_Icc.mp hq).1; omega
  rw [pmRamanujanPrimitiveGram_eq_energyCentered hp1 hq1]
  ring

/-- **Unconditional Rank-1 Von Mangoldt Lower Bound on `sievePronicDiscrepancyGramForm`
(`vonMangoldt_sum_sq_le_sievePronicDiscrepancyGramForm`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`:
`(∑ e ∈ Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e)² ≤ sievePronicDiscrepancyGramForm N c`. -/
theorem vonMangoldt_sum_sq_le_sievePronicDiscrepancyGramForm
    (N : ℕ) (c : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) ^ (2 : ℕ) ≤
      sievePronicDiscrepancyGramForm N c := by
  rw [sievePronicDiscrepancyGramForm_eq_vonMangoldt_sq_add_energyCentered]
  linarith [sieveEnergyCenteredPronicGramForm_nonneg N c]

/-- **Square-Root Von Mangoldt Functional Bound (`abs_vonMangoldt_sum_le_sqrt_sievePronicDiscrepancyGramForm`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`:
`|∑ e ∈ Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e| ≤ √(sievePronicDiscrepancyGramForm N c)`. -/
theorem abs_vonMangoldt_sum_le_sqrt_sievePronicDiscrepancyGramForm
    (N : ℕ) (c : ℕ → ℝ) :
    |∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e| ≤
      Real.sqrt (sievePronicDiscrepancyGramForm N c) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (vonMangoldt_sum_sq_le_sievePronicDiscrepancyGramForm N c)

/-! ## §3. Mean-Centered Pronic Gram Quadratic Form, Positivity & Bilinear Decomposition -/

/-- **The Mean-Centered Pronic Gram Quadratic Form (`sieveMeanCenteredPronicGramForm`):**
The quadratic form on `selbergMultiplesCoord N c` induced by `pmRamanujanMeanCenteredGram p q`. -/
def sieveMeanCenteredPronicGramForm (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
    selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
      pmRamanujanMeanCenteredGram p q

/-- Pointwise bilinear expansion of `(sieveMeanCenteredPrefixDiscrepancy N M c)² / pronicSeq M`. -/
theorem sieveMeanCenteredPrefixDiscrepancy_sq_div_pronicSeq_eq
    (N M : ℕ) (c : ℕ → ℝ) :
    (sieveMeanCenteredPrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ) =
      ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
        selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
          (pmRamanujanMeanCenteredPrimitive p M *
            pmRamanujanMeanCenteredPrimitive q M / ((M : ℝ) * ((M : ℝ) + 1))) := by
  rw [cast_pronicSeq_eq M]
  unfold sieveMeanCenteredPrefixDiscrepancy
  rw [sq, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-- **Exact Pronic Series Representation of `sieveMeanCenteredPronicGramForm`
(`hasSum_sieveMeanCenteredPrefixDiscrepancy_sq_div_pronicSeq`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`, the pronic-weighted squared series of
`sieveMeanCenteredPrefixDiscrepancy N M c` converges unconditionally to
`sieveMeanCenteredPronicGramForm N c`. -/
theorem hasSum_sieveMeanCenteredPrefixDiscrepancy_sq_div_pronicSeq
    (N : ℕ) (c : ℕ → ℝ) :
    HasSum (fun M : ℕ =>
      (sieveMeanCenteredPrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ))
      (sieveMeanCenteredPronicGramForm N c) := by
  have hs : HasSum
      (fun M : ℕ => ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
        selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
          (pmRamanujanMeanCenteredPrimitive p M *
            pmRamanujanMeanCenteredPrimitive q M / ((M : ℝ) * ((M : ℝ) + 1))))
      (sieveMeanCenteredPronicGramForm N c) := by
    unfold sieveMeanCenteredPronicGramForm
    apply hasSum_sum
    intro p hp
    apply hasSum_sum
    intro q hq
    have hp1 : 1 < p := by have := (Finset.mem_Icc.mp hp).1; omega
    have hq1 : 1 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    have hterm := hasSum_pmRamanujanMeanCenteredGram hp1 hq1
    have hval :
        pmRamanujanPrimitiveGram p q + (p.totient : ℝ) / 2 * (-vonMangoldt q) +
          (q.totient : ℝ) / 2 * (-vonMangoldt p) +
          (p.totient : ℝ) / 2 * ((q.totient : ℝ) / 2) =
        pmRamanujanMeanCenteredGram p q := by
      linarith [pmRamanujanPrimitiveGram_eq_meanCentered hp1 hq1]
    rw [hval] at hterm
    exact hterm.mul_left _
  exact hs.congr_fun fun M => sieveMeanCenteredPrefixDiscrepancy_sq_div_pronicSeq_eq N M c

/-- `tsum` formula for `sieveMeanCenteredPronicGramForm N c`. -/
theorem tsum_sieveMeanCenteredPrefixDiscrepancy_sq_div_pronicSeq
    (N : ℕ) (c : ℕ → ℝ) :
    (∑' M : ℕ, (sieveMeanCenteredPrefixDiscrepancy N M c) ^ (2 : ℕ) / (pronicSeq M : ℝ)) =
      sieveMeanCenteredPronicGramForm N c :=
  (hasSum_sieveMeanCenteredPrefixDiscrepancy_sq_div_pronicSeq N c).tsum_eq

/-- **Unconditional Positive Semi-Definiteness of `sieveMeanCenteredPronicGramForm`
(`sieveMeanCenteredPronicGramForm_nonneg`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`,
`0 ≤ sieveMeanCenteredPronicGramForm N c`. -/
theorem sieveMeanCenteredPronicGramForm_nonneg (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ sieveMeanCenteredPronicGramForm N c := by
  rw [← tsum_sieveMeanCenteredPrefixDiscrepancy_sq_div_pronicSeq]
  exact tsum_nonneg fun M => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **Exact Mean-Centered + Bilinear Decomposition of `sievePronicDiscrepancyGramForm`
(`sievePronicDiscrepancyGramForm_eq_meanCentered_add`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`:
`sievePronicDiscrepancyGramForm N c` equals `sieveMeanCenteredPronicGramForm N c` plus
`(∑ e ∈ Icc 2 N, e.totient * Y_{N,c}(e)) * (∑ e ∈ Icc 2 N, Λ(e) * Y_{N,c}(e)) - (1 / 4) * (∑ e ∈ Icc 2 N, e.totient * Y_{N,c}(e))²`. -/
theorem sievePronicDiscrepancyGramForm_eq_meanCentered_add
    (N : ℕ) (c : ℕ → ℝ) :
    sievePronicDiscrepancyGramForm N c =
      sieveMeanCenteredPronicGramForm N c +
        (∑ p ∈ Finset.Icc 2 N, (p.totient : ℝ) * selbergMultiplesCoord N c p) *
          (∑ q ∈ Finset.Icc 2 N, vonMangoldt q * selbergMultiplesCoord N c q) -
        (1 / 4 : ℝ) *
          (∑ p ∈ Finset.Icc 2 N, (p.totient : ℝ) * selbergMultiplesCoord N c p) ^ (2 : ℕ) := by
  unfold sievePronicDiscrepancyGramForm sieveMeanCenteredPronicGramForm
  have h1 :
      (∑ p ∈ Finset.Icc 2 N, (p.totient : ℝ) * selbergMultiplesCoord N c p) *
        (∑ q ∈ Finset.Icc 2 N, vonMangoldt q * selbergMultiplesCoord N c q) =
      ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
        selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
          ((p.totient : ℝ) * vonMangoldt q / 2 + (q.totient : ℝ) * vonMangoldt p / 2) := by
    have hmul1 :
        (∑ p ∈ Finset.Icc 2 N, (p.totient : ℝ) * selbergMultiplesCoord N c p) *
          (∑ q ∈ Finset.Icc 2 N, vonMangoldt q * selbergMultiplesCoord N c q) / 2 =
        ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
          selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
            ((p.totient : ℝ) * vonMangoldt q / 2) := by
      rw [Finset.sum_mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun q _ => by ring
    have hmul2 :
        (∑ p ∈ Finset.Icc 2 N, (p.totient : ℝ) * selbergMultiplesCoord N c p) *
          (∑ q ∈ Finset.Icc 2 N, vonMangoldt q * selbergMultiplesCoord N c q) / 2 =
        ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
          selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
            ((q.totient : ℝ) * vonMangoldt p / 2) := by
      rw [Finset.sum_mul_sum, Finset.sum_comm, Finset.sum_div]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun q _ => by ring
    have hadd :
        ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
          selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
            ((p.totient : ℝ) * vonMangoldt q / 2 + (q.totient : ℝ) * vonMangoldt p / 2) =
        (∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
            selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
              ((p.totient : ℝ) * vonMangoldt q / 2)) +
          (∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
            selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
              ((q.totient : ℝ) * vonMangoldt p / 2)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => by ring
    linarith
  have h2 :
      (1 / 4 : ℝ) *
        (∑ p ∈ Finset.Icc 2 N, (p.totient : ℝ) * selbergMultiplesCoord N c p) ^ (2 : ℕ) =
      ∑ p ∈ Finset.Icc 2 N, ∑ q ∈ Finset.Icc 2 N,
        selbergMultiplesCoord N c p * selbergMultiplesCoord N c q *
          ((p.totient : ℝ) * (q.totient : ℝ) / 4) := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => by ring
  rw [h1, h2, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hp1 : 1 < p := by have := (Finset.mem_Icc.mp hp).1; omega
  have hq1 : 1 < q := by have := (Finset.mem_Icc.mp hq).1; omega
  rw [pmRamanujanPrimitiveGram_eq_meanCentered hp1 hq1]
  ring

/-! ## §4. Prime-Dilation Transfer from the Rank-1 Von Mangoldt Channel to `pmRamanujanEnergyCenteredGram` -/

/-- Whenever `p` is prime, `q > 1`, and `¬ p ∣ q`, the coprime product `p * q` has at least two
distinct prime factors, so `vonMangoldt (p * q) = 0`. -/
theorem vonMangoldt_prime_mul_eq_zero_of_not_dvd {p q : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hpq : ¬ p ∣ q) :
    vonMangoldt (p * q) = 0 :=
  vonMangoldt_mul_eq_zero_of_coprime (hp.coprime_iff_not_dvd.mpr hpq) hp.two_le (by omega)

/-- Whenever `p` is prime, `q > 1`, `r > 1`, and `¬ p ∣ q`, `pmRamanujanEnergyCenteredGram (p * q) r`
coincides with the uncentered Gram entry `pmRamanujanPrimitiveGram (p * q) r`. -/
theorem pmRamanujanEnergyCenteredGram_prime_mul_left_eq {p q r : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hr : 1 < r) (hpq : ¬ p ∣ q) :
    pmRamanujanEnergyCenteredGram (p * q) r = pmRamanujanPrimitiveGram (p * q) r := by
  have hpq1 : 1 < p * q := lt_of_lt_of_le hq (Nat.le_mul_of_pos_left q hp.pos)
  have h := pmRamanujanPrimitiveGram_eq_energyCentered hpq1 hr
  rw [vonMangoldt_prime_mul_eq_zero_of_not_dvd hp hq hpq, zero_mul, zero_add] at h
  exact h.symm

/-- Whenever `p` is prime, `q > 1`, `r > 1`, and `¬ p ∣ r`, `pmRamanujanEnergyCenteredGram q (p * r)`
coincides with the uncentered Gram entry `pmRamanujanPrimitiveGram q (p * r)`. -/
theorem pmRamanujanEnergyCenteredGram_prime_mul_right_eq {p q r : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hr : 1 < r) (hpr : ¬ p ∣ r) :
    pmRamanujanEnergyCenteredGram q (p * r) = pmRamanujanPrimitiveGram q (p * r) := by
  have hpr1 : 1 < p * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)
  have h := pmRamanujanPrimitiveGram_eq_energyCentered hq hpr1
  rw [vonMangoldt_prime_mul_eq_zero_of_not_dvd hp hr hpr, mul_zero, zero_add] at h
  exact h.symm

/-- **Prime-Pair Transfer Recurrence for `pmRamanujanEnergyCenteredGram`
(`pmRamanujanEnergyCenteredGram_prime_pair`):**
For every prime `p` and moduli `q, r > 1` with `¬ p ∣ q` and `¬ p ∣ r`, coprime prime dilation
transfers the rank-1 von Mangoldt term `(p - 1) * Λ(q) * Λ(r)` directly into the energy-centered
Gram recurrence:
`G^ec(p*q, p*r) + G^ec(p*q, r) + G^ec(q, p*r) = (p - 1) * G^ec(q, r) + (p - 1) * Λ(q) * Λ(r)`. -/
theorem pmRamanujanEnergyCenteredGram_prime_pair {p q r : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hr : 1 < r) (hpq : ¬ p ∣ q) (hpr : ¬ p ∣ r) :
    pmRamanujanEnergyCenteredGram (p * q) (p * r) +
      pmRamanujanEnergyCenteredGram (p * q) r +
      pmRamanujanEnergyCenteredGram q (p * r) =
      ((p : ℝ) - 1) * pmRamanujanEnergyCenteredGram q r +
        ((p : ℝ) - 1) * vonMangoldt q * vonMangoldt r := by
  have hpr1 : 1 < p * r := lt_of_lt_of_le hr (Nat.le_mul_of_pos_left r hp.pos)
  rw [pmRamanujanEnergyCenteredGram_prime_mul_left_eq hp hq hpr1 hpq,
    pmRamanujanEnergyCenteredGram_prime_mul_left_eq hp hq hr hpq,
    pmRamanujanEnergyCenteredGram_prime_mul_right_eq hp hq hr hpr,
    pmRamanujanPrimitiveGram_prime_pair hp hq hr hpq hpr,
    pmRamanujanPrimitiveGram_eq_energyCentered hq hr]
  ring

/-- Symmetry of `pmRamanujanEnergyCenteredGram`. -/
theorem pmRamanujanEnergyCenteredGram_symm (p q : ℕ) :
    pmRamanujanEnergyCenteredGram p q = pmRamanujanEnergyCenteredGram q p := by
  unfold pmRamanujanEnergyCenteredGram
  congr 1
  ext N
  ring

/-- **Prime-Dilated Diagonal Recurrence for `pmRamanujanEnergyCenteredGram`
(`pmRamanujanEnergyCenteredGram_prime_mul_diag`):**
For every prime `p` and modulus `q > 1` with `¬ p ∣ q`:
`G^ec(p * q, p * q) = (p - 1) * G^ec(q, q) + (p - 1) * Λ(q)² - 2 * G^ec(p * q, q)`. -/
theorem pmRamanujanEnergyCenteredGram_prime_mul_diag {p q : ℕ}
    (hp : p.Prime) (hq : 1 < q) (hpq : ¬ p ∣ q) :
    pmRamanujanEnergyCenteredGram (p * q) (p * q) =
      ((p : ℝ) - 1) * pmRamanujanEnergyCenteredGram q q +
        ((p : ℝ) - 1) * vonMangoldt q ^ (2 : ℕ) -
        2 * pmRamanujanEnergyCenteredGram (p * q) q := by
  have hpair := pmRamanujanEnergyCenteredGram_prime_pair hp hq hq hpq hpq
  have hsymm := pmRamanujanEnergyCenteredGram_symm q (p * q)
  linarith [show ((p : ℝ) - 1) * vonMangoldt q ^ (2 : ℕ) =
    ((p : ℝ) - 1) * vonMangoldt q * vonMangoldt q by ring]

end
end GaloisForLFunctions.BezoutValuationIncidence
