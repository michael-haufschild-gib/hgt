import GaloisForLFunctions.BezoutValuationIncidence.TruncatedPronicGramMatrixAndFiniteHorizonVonMangoldtApproximation
import GaloisForLFunctions.BezoutValuationIncidence.ArbitraryDepthBezoutShellsAndRoutePMSecondLayerProfile

/-!
# Oscillatory Pronic Tail Summation by Parts and Second-Order `O(1 / ((H + 1)(H + 2)))` Von Mangoldt Error

In `TruncatedPronicGramMatrixAndFiniteHorizonVonMangoldtApproximation`, we proved that for any
uniformly bounded sequence $|g(M)| \le C$, the finite-horizon pronic sum over $1 \le M \le H$
approximates the infinite pronic series within $C / (H + 1)$, yielding the first-order finite-horizon
von Mangoldt approximation
$$\left|\sum_{M=1}^H \frac{\operatorname{Re}(\operatorname{pmRamanujanPrimitive}(q, M))}{\operatorname{pronicSeq}(M)}
  + \Lambda(q)\right| \le \frac{\operatorname{pmRamanujanPrimitiveBound}(q)}{H + 1}.$$

In this module, we complete **Step 4** of the Wall 1 Bézout programme by applying Abel summation by
parts against the antitone pronic tail weight $w_H(k) = \frac{1}{\operatorname{pronicSeq}(H + 1 + k)}$
to sequences with bounded partial sums, gaining an **extra decay factor of $\frac{1}{H + 2}$** and
isolating the exact first-order $\frac{\varphi(q)}{2(H + 1)}$ asymptotic term:

1. **General Summation by Parts Against Antitone Weights & Second-Order Pronic Tail Bound
   (`abs_sum_range_mul_antitone_le`,
   `abs_sum_range_div_pronicSeq_shift_le_of_prefix_bound`,
   `abs_tsum_div_pronicSeq_shift_le_of_prefix_bound`,
   `abs_tsum_div_pronicSeq_sub_sum_Icc_le_of_prefix_bound`):**
   - For any sequence $a : \mathbb{N} \to \mathbb{R}$ whose partial sums satisfy
     $\bigl|\sum_{i < K} a(i)\bigr| \le B$ for all $K \in \mathbb{N}$, any shifted window starting
     at $H + 1$ has partial sums bounded by $2B$.
   - Summing by parts against the antitone pronic reciprocal weight
     $w_H(k) = \frac{1}{\operatorname{pronicSeq}(H + 1 + k)}$ bounds every finite tail partial sum
     — and therefore the infinite tail series — by:
     $$\left|\sum_{M=1}^\infty \frac{a(M)}{\operatorname{pronicSeq}(M)} -
       \sum_{M=1}^H \frac{a(M)}{\operatorname{pronicSeq}(M)}\right|
       \le \frac{2B}{\operatorname{pronicSeq}(H + 1)} = \frac{2B}{(H + 1)(H + 2)}.$$

2. **Exact First-Order `(φ(q) / 2) / (H + 1)` Extraction & Second-Order `O(1 / ((H + 1)(H + 2)))`
   Von Mangoldt Approximation (`hasSum_pmRamanujanMeanCenteredPrimitive_div_pronicSeq`,
   `tsum_pmRamanujanMeanCenteredPrimitive_div_pronicSeq`,
   `sum_Icc_pmRamanujanPrimitive_add_vonMangoldt_sub_totient_tail_eq`,
   `exists_second_order_pmRamanujanPrimitive_vonMangoldt_bound`):**
   - Because $\operatorname{pmRamanujanMeanCenteredPrimitive}(q, M) = \operatorname{Re}(\operatorname{pmRamanujanPrimitive}(q, M)) + \varphi(q)/2$
     is periodic of period $q$ with mean $0$, its partial sums are uniformly bounded (`pmRamanujanPrimitive_centered_prefix_bound`).
   - Subtracting the exact pronic tail $\frac{\varphi(q)}{2(H + 1)}$ of its mean $-\varphi(q)/2$
     cancels the $O(1/(H + 1))$ error term identically and upgrades the finite-horizon von Mangoldt
     approximation to second order $O_q\bigl(\frac{1}{(H + 1)(H + 2)}\bigr)$:
     $$\left|\sum_{M=1}^H \frac{\operatorname{Re}(\operatorname{pmRamanujanPrimitive}(q, M))}{\operatorname{pronicSeq}(M)}
       + \Lambda(q) - \frac{\varphi(q)}{2(H + 1)}\right|
       \le \frac{2 B_q}{(H + 1)(H + 2)}.$$

3. **Mean-Centered Sieve Prefix Discrepancy & Second-Order Finite-Horizon Sieve Duality
   (`sieveMeanCenteredPrefixDiscrepancy`,
   `sieveMeanCenteredPrefixDiscrepancy_eq_add_totient_coord`,
   `tsum_sieveMeanCenteredPrefixDiscrepancy_div_pronicSeq`,
   `sum_Icc_sievePrefixDiscrepancy_add_vonMangoldt_sub_totient_tail_eq`,
   `exists_second_order_sievePrefixDiscrepancy_vonMangoldt_bound`):**
   - For any sieve cutoff $N$ and weight $c$, subtracting the deterministic first-order tail
     $\frac{\sum_{e=2}^N \varphi(e)\,Y_{N,c}(e)}{2(H + 1)}$ reduces the finite-horizon von Mangoldt
     sieve remainder to the pronic tail of `sieveMeanCenteredPrefixDiscrepancy N M c`, which decays
     at the second-order rate $O_{N,c}\bigl(\frac{1}{(H + 1)(H + 2)}\bigr)$.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Summation by Parts Against Antitone Weights & Second-Order Pronic Tail Bound -/

/-- **General Summation-by-Parts Inequality for Antitone Weights (`abs_sum_range_mul_antitone_le`):**
For any sequence `a : ℕ → ℝ`, non-negative antitone weight `w : ℕ → ℝ`, horizon `L : ℕ`, and bound
`B ≥ 0`, if `|∑ i ∈ range K, a i| ≤ B` for all `K ≤ L`, then
`|∑ i ∈ range L, w i * a i| ≤ B * w 0`. -/
theorem abs_sum_range_mul_antitone_le (a w : ℕ → ℝ) (L : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hw : ∀ k : ℕ, 0 ≤ w k) (hanti : Antitone w)
    (hprefix : ∀ K ≤ L, |∑ i ∈ Finset.range K, a i| ≤ B) :
    |∑ i ∈ Finset.range L, w i * a i| ≤ B * w 0 := by
  by_cases hL : L = 0
  · subst hL
    simpa using mul_nonneg hB (hw 0)
  let P : ℕ → ℝ := fun K => ∑ i ∈ Finset.range K, a i
  have he :
      (∑ i ∈ Finset.range L, w i * a i) =
        w (L - 1) * P L + ∑ i ∈ Finset.range (L - 1), (w i - w (i + 1)) * P (i + 1) := by
    have h := Finset.sum_range_by_parts w a L
    simp only [smul_eq_mul] at h
    rw [h]
    simp only [sub_mul, Finset.sum_sub_distrib, P]
    ring
  rw [he]
  calc
    |w (L - 1) * P L + ∑ i ∈ Finset.range (L - 1), (w i - w (i + 1)) * P (i + 1)|
      ≤ |w (L - 1) * P L| +
          ∑ i ∈ Finset.range (L - 1), |(w i - w (i + 1)) * P (i + 1)| :=
        (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ w (L - 1) * B + ∑ i ∈ Finset.range (L - 1), (w i - w (i + 1)) * B := by
        apply add_le_add
        · rw [abs_mul, abs_of_nonneg (hw _)]
          exact mul_le_mul_of_nonneg_left (hprefix L le_rfl) (hw _)
        · refine Finset.sum_le_sum fun i hi => ?_
          have hd : 0 ≤ w i - w (i + 1) := sub_nonneg.mpr (hanti (by omega))
          rw [abs_mul, abs_of_nonneg hd]
          exact mul_le_mul_of_nonneg_left
            (hprefix (i + 1) (by simp only [Finset.mem_range] at hi; omega)) hd
    _ = B * w 0 := by
        rw [← Finset.sum_mul, Finset.sum_range_sub']
        ring

/-- For any horizon `H : ℕ`, the shifted pronic reciprocal weight
`k ↦ 1 / (pronicSeq (H + 1 + k) : ℝ)` is antitone on `ℕ`. -/
theorem antitone_one_div_pronicSeq_shift (H : ℕ) :
    Antitone (fun k : ℕ => 1 / (pronicSeq (H + 1 + k) : ℝ)) := by
  intro i j hij
  have hi : 0 < pronicSeq (H + 1 + i) := by
    unfold pronicSeq; positivity
  have hj : pronicSeq (H + 1 + i) ≤ pronicSeq (H + 1 + j) := by
    unfold pronicSeq
    exact Nat.mul_le_mul (by omega) (by omega)
  exact one_div_le_one_div_of_le (by exact_mod_cast hi) (by exact_mod_cast hj)

/-- **Finite-Window Second-Order Pronic Tail Bound (`abs_sum_range_div_pronicSeq_shift_le_of_prefix_bound`):**
For any sequence `a : ℕ → ℝ` whose prefix sums satisfy `|∑ i ∈ range K, a i| ≤ B` for all `K : ℕ`,
every shifted pronic partial sum over `k ∈ range L` starting at `H + 1` satisfies:
`|∑ k ∈ range L, a (H + 1 + k) / pronicSeq (H + 1 + k)| ≤ 2 * B / pronicSeq (H + 1)`. -/
theorem abs_sum_range_div_pronicSeq_shift_le_of_prefix_bound
    {a : ℕ → ℝ} {B : ℝ} (hB : ∀ K : ℕ, |∑ i ∈ Finset.range K, a i| ≤ B)
    (H L : ℕ) :
    |∑ k ∈ Finset.range L, a (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)| ≤
      2 * B / (pronicSeq (H + 1) : ℝ) := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  let a_shift : ℕ → ℝ := fun k => a (H + 1 + k)
  let w : ℕ → ℝ := fun k => 1 / (pronicSeq (H + 1 + k) : ℝ)
  have hshift_prefix : ∀ K : ℕ, |∑ k ∈ Finset.range K, a_shift k| ≤ 2 * B := by
    intro K
    have hadd := Finset.sum_range_add a (H + 1) K
    have hsub :
        (∑ k ∈ Finset.range K, a_shift k) =
          (∑ i ∈ Finset.range (H + 1 + K), a i) -
            ∑ i ∈ Finset.range (H + 1), a i := by
      dsimp only [a_shift]
      linarith [hadd]
    rw [hsub]
    exact (abs_sub _ _).trans (by linarith [hB (H + 1 + K), hB (H + 1)])
  have hw : ∀ k : ℕ, 0 ≤ w k := fun k => by dsimp only [w]; positivity
  have hanti : Antitone w := antitone_one_div_pronicSeq_shift H
  have hsbp := abs_sum_range_mul_antitone_le a_shift w L (by linarith) hw hanti
    (fun K _ => hshift_prefix K)
  have hcongr :
      (∑ k ∈ Finset.range L, a (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)) =
        ∑ k ∈ Finset.range L, w k * a_shift k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [w, a_shift]
    ring
  rw [hcongr]
  simpa only [w, Nat.add_zero, mul_one_div] using hsbp

/-- **Infinite-Tail Second-Order Pronic Bound (`abs_tsum_div_pronicSeq_shift_le_of_prefix_bound`):**
For any uniformly bounded sequence `a : ℕ → ℝ` (`|a M| ≤ C`) whose prefix sums satisfy
`|∑ i ∈ range K, a i| ≤ B` for all `K : ℕ`, the infinite pronic tail starting at `H + 1` satisfies:
`|∑' k : ℕ, a (H + 1 + k) / pronicSeq (H + 1 + k)| ≤ 2 * B / ((H + 1) * (H + 2))`. -/
theorem abs_tsum_div_pronicSeq_shift_le_of_prefix_bound
    {a : ℕ → ℝ} {C B : ℝ} (hC : ∀ M : ℕ, |a M| ≤ C)
    (hB : ∀ K : ℕ, |∑ i ∈ Finset.range K, a i| ≤ B) (H : ℕ) :
    |∑' k : ℕ, a (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)| ≤
      2 * B / (((H : ℝ) + 1) * ((H : ℝ) + 2)) := by
  have hs : Summable (fun k : ℕ => a (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)) :=
    (summable_div_pronicSeq_of_bounded hC).comp_injective
      (fun x y hxy => Nat.add_left_cancel hxy)
  have hlim :
      Tendsto (fun L : ℕ =>
        |∑ k ∈ Finset.range L, a (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)|)
        atTop (𝓝 |∑' k : ℕ, a (H + 1 + k) / (pronicSeq (H + 1 + k) : ℝ)|) :=
    (continuous_abs.tendsto _).comp hs.hasSum.tendsto_sum_nat
  have hbound := le_of_tendsto hlim (Filter.Eventually.of_forall fun L =>
    abs_sum_range_div_pronicSeq_shift_le_of_prefix_bound hB H L)
  have hpr : (pronicSeq (H + 1) : ℝ) = ((H : ℝ) + 1) * ((H : ℝ) + 2) := by
    rw [cast_pronicSeq_eq (H + 1)]
    push_cast
    ring
  rwa [hpr] at hbound

/-- **Master Second-Order Finite-Horizon Pronic Remainder Theorem
(`abs_tsum_div_pronicSeq_sub_sum_Icc_le_of_prefix_bound`):**
For any uniformly bounded sequence `a : ℕ → ℝ` (`|a M| ≤ C`) whose prefix sums satisfy
`|∑ i ∈ range K, a i| ≤ B` for all `K : ℕ`, the finite-horizon pronic partial sum over `1 ≤ M ≤ H`
approximates the infinite pronic series within `2 * B / ((H + 1) * (H + 2))`:
`|(∑' M : ℕ, a M / pronicSeq M) - (∑ M ∈ Icc 1 H, a M / pronicSeq M)| ≤ 2 * B / ((H + 1) * (H + 2))`. -/
theorem abs_tsum_div_pronicSeq_sub_sum_Icc_le_of_prefix_bound
    {a : ℕ → ℝ} {C B : ℝ} (hC : ∀ M : ℕ, |a M| ≤ C)
    (hB : ∀ K : ℕ, |∑ i ∈ Finset.range K, a i| ≤ B) (H : ℕ) :
    |(∑' M : ℕ, a M / (pronicSeq M : ℝ)) -
      (∑ M ∈ Finset.Icc 1 H, a M / (pronicSeq M : ℝ))| ≤
      2 * B / (((H : ℝ) + 1) * ((H : ℝ) + 2)) := by
  rw [tsum_div_pronicSeq_sub_sum_Icc_eq hC H]
  exact abs_tsum_div_pronicSeq_shift_le_of_prefix_bound hC hB H

/-! ## §2. Exact First-Order `(φ(q) / 2) / (H + 1)` Extraction & Second-Order Von Mangoldt Approximation -/

/-- For every `H : ℕ` (including `H = 0`), `∑ M ∈ Icc 1 H, 1 / pronicSeq M = 1 - 1 / (H + 1)`. -/
theorem sum_Icc_one_div_pronicSeq_all (H : ℕ) :
    (∑ M ∈ Finset.Icc 1 H, (1 : ℝ) / (pronicSeq M : ℝ)) = 1 - 1 / ((H : ℝ) + 1) := by
  by_cases hH : 1 ≤ H
  · exact sum_one_div_pronicSeq_eq hH
  · have h0 : H = 0 := by omega
    subst h0
    simp

/-- `HasSum` evaluation of `1 / pronicSeq M` over `M : ℕ`. -/
theorem hasSum_one_div_pronicSeq_nat :
    HasSum (fun M : ℕ => (1 : ℝ) / (pronicSeq M : ℝ)) 1 :=
  hasSum_pm_reciprocal_weight.congr_fun fun M => by rw [cast_pronicSeq_eq M]

/-- **Exact Pronic Series of `pmRamanujanMeanCenteredPrimitive`
(`hasSum_pmRamanujanMeanCenteredPrimitive_div_pronicSeq`):**
For every modulus `q > 1`:
`HasSum (fun M => pmRamanujanMeanCenteredPrimitive q M / pronicSeq M) (-vonMangoldt q + q.totient / 2)`. -/
theorem hasSum_pmRamanujanMeanCenteredPrimitive_div_pronicSeq {q : ℕ} (hq : 1 < q) :
    HasSum (fun M : ℕ => pmRamanujanMeanCenteredPrimitive q M / (pronicSeq M : ℝ))
      (-vonMangoldt q + (q.totient : ℝ) / 2) := by
  have h1 : HasSum (fun M : ℕ => (pmRamanujanPrimitive q M).re / (pronicSeq M : ℝ))
      (-vonMangoldt q) :=
    (hasSum_pmRamanujanPrimitive_reciprocal hq).congr_fun fun M => by rw [cast_pronicSeq_eq M]
  have h2 := hasSum_one_div_pronicSeq_nat.mul_left ((q.totient : ℝ) / 2)
  rw [mul_one] at h2
  refine (h1.add h2).congr_fun fun M => ?_
  unfold pmRamanujanMeanCenteredPrimitive
  ring

/-- `tsum` formula for `pmRamanujanMeanCenteredPrimitive q M / pronicSeq M`. -/
theorem tsum_pmRamanujanMeanCenteredPrimitive_div_pronicSeq {q : ℕ} (hq : 1 < q) :
    (∑' M : ℕ, pmRamanujanMeanCenteredPrimitive q M / (pronicSeq M : ℝ)) =
      -vonMangoldt q + (q.totient : ℝ) / 2 :=
  (hasSum_pmRamanujanMeanCenteredPrimitive_div_pronicSeq hq).tsum_eq

/-- **Exact Decomposition of the Finite-Horizon Von Mangoldt Remainder into First-Order Drift + Mean-Centered Tail
(`sum_Icc_pmRamanujanPrimitive_add_vonMangoldt_sub_totient_tail_eq`):**
For every modulus `q > 1` and every finite horizon `H : ℕ`, subtracting the deterministic first-order
drift `(q.totient / 2) / (H + 1)` from the finite-horizon von Mangoldt remainder yields the exact
finite-horizon remainder of the mean-centered primitive:
`(∑_{M=1}^H (pmRamanujanPrimitive q M).re / pronicSeq M) + vonMangoldt q - (q.totient / 2) / (H + 1) = (∑_{M=1}^H pmRamanujanMeanCenteredPrimitive q M / pronicSeq M) - ∑' M, pmRamanujanMeanCenteredPrimitive q M / pronicSeq M`. -/
theorem sum_Icc_pmRamanujanPrimitive_add_vonMangoldt_sub_totient_tail_eq
    {q : ℕ} (hq : 1 < q) (H : ℕ) :
    (∑ M ∈ Finset.Icc 1 H, (pmRamanujanPrimitive q M).re / (pronicSeq M : ℝ)) +
      vonMangoldt q - ((q.totient : ℝ) / 2) / ((H : ℝ) + 1) =
      (∑ M ∈ Finset.Icc 1 H,
        pmRamanujanMeanCenteredPrimitive q M / (pronicSeq M : ℝ)) -
        ∑' M : ℕ, pmRamanujanMeanCenteredPrimitive q M / (pronicSeq M : ℝ) := by
  rw [tsum_pmRamanujanMeanCenteredPrimitive_div_pronicSeq hq]
  have hsum :
      (∑ M ∈ Finset.Icc 1 H,
        pmRamanujanMeanCenteredPrimitive q M / (pronicSeq M : ℝ)) =
      (∑ M ∈ Finset.Icc 1 H, (pmRamanujanPrimitive q M).re / (pronicSeq M : ℝ)) +
        ((q.totient : ℝ) / 2) * (1 - 1 / ((H : ℝ) + 1)) := by
    rw [← sum_Icc_one_div_pronicSeq_all H, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun M _ => ?_
    unfold pmRamanujanMeanCenteredPrimitive
    ring
  rw [hsum]
  ring

/-- **Second-Order `O(1 / ((H + 1)(H + 2)))` Finite-Horizon Von Mangoldt Approximation
(`exists_second_order_pmRamanujanPrimitive_vonMangoldt_bound`):**
For every modulus `q > 1`, there exists an explicit finite constant `B ≥ 0` (independent of `H`)
such that for **every** finite horizon `H : ℕ`:
`|(∑_{M=1}^H (pmRamanujanPrimitive q M).re / pronicSeq M) + vonMangoldt q - (q.totient / 2) / (H + 1)| ≤ 2 * B / ((H + 1) * (H + 2))`. -/
theorem exists_second_order_pmRamanujanPrimitive_vonMangoldt_bound
    {q : ℕ} (hq : 1 < q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ H : ℕ,
      |(∑ M ∈ Finset.Icc 1 H, (pmRamanujanPrimitive q M).re / (pronicSeq M : ℝ)) +
        vonMangoldt q - ((q.totient : ℝ) / 2) / ((H : ℝ) + 1)| ≤
        2 * B / (((H : ℝ) + 1) * ((H : ℝ) + 2)) := by
  obtain ⟨B, hB⟩ := pmRamanujanPrimitive_centered_prefix_bound hq
  have hB0 : 0 ≤ B := by simpa using hB 0
  have hC : ∀ M : ℕ,
      |pmRamanujanMeanCenteredPrimitive q M| ≤
        pmRamanujanPrimitiveBound q + (q.totient : ℝ) / 2 := by
    intro M
    unfold pmRamanujanMeanCenteredPrimitive
    have h1 : |(pmRamanujanPrimitive q M).re| ≤ pmRamanujanPrimitiveBound q :=
      (Complex.abs_re_le_norm _).trans (norm_pmRamanujanPrimitive_le hq M)
    have h2 : |(q.totient : ℝ) / 2| = (q.totient : ℝ) / 2 :=
      abs_of_nonneg (by positivity)
    exact (abs_add_le _ _).trans (by linarith)
  refine ⟨B, hB0, fun H => ?_⟩
  rw [sum_Icc_pmRamanujanPrimitive_add_vonMangoldt_sub_totient_tail_eq hq H,
    abs_sub_comm]
  exact abs_tsum_div_pronicSeq_sub_sum_Icc_le_of_prefix_bound hC hB H

/-! ## §3. Mean-Centered Sieve Prefix Discrepancy & Second-Order Finite-Horizon Sieve Duality -/

/-- **Mean-Centered Sieve Prefix Discrepancy (`sieveMeanCenteredPrefixDiscrepancy`):**
The zero-mean oscillatory component of `sievePrefixDiscrepancy N M c`, obtained by replacing each
dual primitive `(pmRamanujanPrimitive e M).re` by `pmRamanujanMeanCenteredPrimitive e M`. -/
def sieveMeanCenteredPrefixDiscrepancy (N M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ e ∈ Finset.Icc 2 N,
    selbergMultiplesCoord N c e * pmRamanujanMeanCenteredPrimitive e M

/-- **Exact Shift Formula for `sieveMeanCenteredPrefixDiscrepancy`
(`sieveMeanCenteredPrefixDiscrepancy_eq_add_totient_coord`):**
For every `N, M : ℕ` and `c : ℕ → ℝ`:
`sieveMeanCenteredPrefixDiscrepancy N M c = sievePrefixDiscrepancy N M c + (1 / 2) * ∑ e ∈ Icc 2 N, e.totient * selbergMultiplesCoord N c e`. -/
theorem sieveMeanCenteredPrefixDiscrepancy_eq_add_totient_coord
    (N M : ℕ) (c : ℕ → ℝ) :
    sieveMeanCenteredPrefixDiscrepancy N M c =
      sievePrefixDiscrepancy N M c +
        (1 / 2 : ℝ) * ∑ e ∈ Finset.Icc 2 N, (e.totient : ℝ) * selbergMultiplesCoord N c e := by
  unfold sieveMeanCenteredPrefixDiscrepancy
  rw [sievePrefixDiscrepancy_eq_ramanujan_diagonal N M c, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  unfold pmRamanujanMeanCenteredPrimitive
  ring

/-- `HasSum` evaluation of `sieveMeanCenteredPrefixDiscrepancy N M c / pronicSeq M`. -/
theorem hasSum_sieveMeanCenteredPrefixDiscrepancy_div_pronicSeq
    (N : ℕ) (c : ℕ → ℝ) :
    HasSum (fun M : ℕ => sieveMeanCenteredPrefixDiscrepancy N M c / (pronicSeq M : ℝ))
      (-(∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) +
        (1 / 2 : ℝ) * ∑ e ∈ Finset.Icc 2 N, (e.totient : ℝ) * selbergMultiplesCoord N c e) := by
  have h1 := hasSum_sievePrefixDiscrepancy_div_pronicSeq N c
  have h2 := hasSum_one_div_pronicSeq_nat.mul_left
    ((1 / 2 : ℝ) * ∑ e ∈ Finset.Icc 2 N, (e.totient : ℝ) * selbergMultiplesCoord N c e)
  rw [mul_one] at h2
  refine (h1.add h2).congr_fun fun M => ?_
  rw [sieveMeanCenteredPrefixDiscrepancy_eq_add_totient_coord]
  ring

/-- **Exact Infinite Pronic Series of `sieveMeanCenteredPrefixDiscrepancy`
(`tsum_sieveMeanCenteredPrefixDiscrepancy_div_pronicSeq`):**
For every `N : ℕ` and `c : ℕ → ℝ`:
`∑' M : ℕ, sieveMeanCenteredPrefixDiscrepancy N M c / pronicSeq M = -∑ e ∈ Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e + (1 / 2) * ∑ e ∈ Icc 2 N, e.totient * selbergMultiplesCoord N c e`. -/
theorem tsum_sieveMeanCenteredPrefixDiscrepancy_div_pronicSeq
    (N : ℕ) (c : ℕ → ℝ) :
    (∑' M : ℕ, sieveMeanCenteredPrefixDiscrepancy N M c / (pronicSeq M : ℝ)) =
      -(∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) +
        (1 / 2 : ℝ) * ∑ e ∈ Finset.Icc 2 N, (e.totient : ℝ) * selbergMultiplesCoord N c e :=
  (hasSum_sieveMeanCenteredPrefixDiscrepancy_div_pronicSeq N c).tsum_eq

/-- **Exact Decomposition of the Finite-Horizon Sieve Von Mangoldt Remainder
(`sum_Icc_sievePrefixDiscrepancy_add_vonMangoldt_sub_totient_tail_eq`):**
For every `N, H : ℕ` and `c : ℕ → ℝ`, subtracting the deterministic first-order totient drift
`((1 / 2) * ∑ e ∈ Icc 2 N, e.totient * selbergMultiplesCoord N c e) / (H + 1)` from the
finite-horizon von Mangoldt sieve remainder yields the pronic tail of
`sieveMeanCenteredPrefixDiscrepancy N M c`. -/
theorem sum_Icc_sievePrefixDiscrepancy_add_vonMangoldt_sub_totient_tail_eq
    (N H : ℕ) (c : ℕ → ℝ) :
    (∑ M ∈ Finset.Icc 1 H, sievePrefixDiscrepancy N M c / (pronicSeq M : ℝ)) +
      (∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) -
      ((1 / 2 : ℝ) * ∑ e ∈ Finset.Icc 2 N, (e.totient : ℝ) * selbergMultiplesCoord N c e) /
        ((H : ℝ) + 1) =
      (∑ M ∈ Finset.Icc 1 H,
        sieveMeanCenteredPrefixDiscrepancy N M c / (pronicSeq M : ℝ)) -
        ∑' M : ℕ, sieveMeanCenteredPrefixDiscrepancy N M c / (pronicSeq M : ℝ) := by
  rw [tsum_sieveMeanCenteredPrefixDiscrepancy_div_pronicSeq N c]
  have hsum :
      (∑ M ∈ Finset.Icc 1 H,
        sieveMeanCenteredPrefixDiscrepancy N M c / (pronicSeq M : ℝ)) =
      (∑ M ∈ Finset.Icc 1 H, sievePrefixDiscrepancy N M c / (pronicSeq M : ℝ)) +
        ((1 / 2 : ℝ) * ∑ e ∈ Finset.Icc 2 N, (e.totient : ℝ) * selbergMultiplesCoord N c e) *
          (1 - 1 / ((H : ℝ) + 1)) := by
    rw [← sum_Icc_one_div_pronicSeq_all H, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [sieveMeanCenteredPrefixDiscrepancy_eq_add_totient_coord]
    ring
  rw [hsum]
  ring

/-- **Second-Order `O(1 / ((H + 1)(H + 2)))` Finite-Horizon Sieve Von Mangoldt Approximation
(`exists_second_order_sievePrefixDiscrepancy_vonMangoldt_bound`):**
For every cutoff `N : ℕ` and sieve weight `c : ℕ → ℝ`, there exists an explicit finite constant
`B ≥ 0` (independent of `H`) such that for **every** finite horizon `H : ℕ`:
`|(∑_{M=1}^H sievePrefixDiscrepancy N M c / pronicSeq M) + (∑_{e=2}^N Λ(e) Y_{N,c}(e)) - ((1/2) ∑_{e=2}^N φ(e) Y_{N,c}(e)) / (H + 1)| ≤ 2 * B / ((H + 1) * (H + 2))`. -/
theorem exists_second_order_sievePrefixDiscrepancy_vonMangoldt_bound
    (N : ℕ) (c : ℕ → ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ H : ℕ,
      |(∑ M ∈ Finset.Icc 1 H, sievePrefixDiscrepancy N M c / (pronicSeq M : ℝ)) +
        (∑ e ∈ Finset.Icc 2 N, vonMangoldt e * selbergMultiplesCoord N c e) -
        ((1 / 2 : ℝ) * ∑ e ∈ Finset.Icc 2 N, (e.totient : ℝ) * selbergMultiplesCoord N c e) /
          ((H : ℝ) + 1)| ≤
        2 * B / (((H : ℝ) + 1) * ((H : ℝ) + 2)) := by
  let B_mode : ℕ → ℝ := fun e =>
    if he : 1 < e then Classical.choose (pmRamanujanPrimitive_centered_prefix_bound he) else 0
  have hB_mode : ∀ e ∈ Finset.Icc 2 N, ∀ K : ℕ,
      |∑ i ∈ Finset.range K, pmRamanujanMeanCenteredPrimitive e i| ≤ B_mode e := by
    intro e he K
    have he1 : 1 < e := by have := (Finset.mem_Icc.mp he).1; omega
    dsimp only [B_mode]
    rw [dif_pos he1]
    exact Classical.choose_spec (pmRamanujanPrimitive_centered_prefix_bound he1) K
  let B : ℝ := ∑ e ∈ Finset.Icc 2 N, |selbergMultiplesCoord N c e| * B_mode e
  have hB_prefix : ∀ K : ℕ,
      |∑ i ∈ Finset.range K, sieveMeanCenteredPrefixDiscrepancy N i c| ≤ B := by
    intro K
    unfold sieveMeanCenteredPrefixDiscrepancy
    rw [Finset.sum_comm]
    calc
      |∑ e ∈ Finset.Icc 2 N,
          ∑ i ∈ Finset.range K,
            selbergMultiplesCoord N c e * pmRamanujanMeanCenteredPrimitive e i|
        ≤ ∑ e ∈ Finset.Icc 2 N,
            |∑ i ∈ Finset.range K,
              selbergMultiplesCoord N c e * pmRamanujanMeanCenteredPrimitive e i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ Finset.Icc 2 N, |selbergMultiplesCoord N c e| * B_mode e := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [← Finset.mul_sum, abs_mul]
          exact mul_le_mul_of_nonneg_left (hB_mode e he K) (abs_nonneg _)
  have hB0 : 0 ≤ B := by simpa using hB_prefix 0
  have hC : ∀ M : ℕ,
      |sieveMeanCenteredPrefixDiscrepancy N M c| ≤
        Real.sqrt (sieveVariance N c * sievePeriodFreeDualCeiling N) +
          |(1 / 2 : ℝ) * ∑ e ∈ Finset.Icc 2 N, (e.totient : ℝ) * selbergMultiplesCoord N c e| := by
    intro M
    rw [sieveMeanCenteredPrefixDiscrepancy_eq_add_totient_coord]
    exact (abs_add_le _ _).trans
      (add_le_add (abs_sievePrefixDiscrepancy_le_periodFree N M c) le_rfl)
  refine ⟨B, hB0, fun H => ?_⟩
  rw [sum_Icc_sievePrefixDiscrepancy_add_vonMangoldt_sub_totient_tail_eq N H c,
    abs_sub_comm]
  exact abs_tsum_div_pronicSeq_sub_sum_Icc_le_of_prefix_bound hC hB_prefix H

end
end GaloisForLFunctions.BezoutValuationIncidence
