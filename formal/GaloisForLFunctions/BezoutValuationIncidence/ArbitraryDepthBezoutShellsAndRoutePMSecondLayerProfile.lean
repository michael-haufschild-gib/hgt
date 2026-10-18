import GaloisForLFunctions.BezoutValuationIncidence.PronicPotentialSelfCancellationAndInteriorGradientConservation

/-!
# Arbitrary-Depth Bézout Shell Calculus, `(2r - 1)`-Step Telescoping, and the Route PM Second-Layer Profile

In `MultiLagBezoutLayerHierarchyAndFourStepInteriorCalculus`, we proved the multi-lag and multi-lead
sawtooth evaluation formulas
$$\operatorname{centeredDiscreteSawtooth}(d, m + r) = -\frac{d - (2r + 1)}{2d},
  \qquad
  \operatorname{centeredDiscreteSawtooth}(d, n) = +\frac{d - (2r - 1)}{2d} \quad (d \mid n + r),$$
and peeled off the second Bézout shell $\{n - 1, n + 2\}$ ($r = 2$, width $2r - 1 = 3$).

In this module, we complete **Step 3** of the Wall 1 Bézout programme by establishing the general
arbitrary-depth ($r \ge 1$) Bézout shell calculus and the exact cutoff-independent Route PM profile
of the second Bézout layer:

1. **Arbitrary-Depth (`r ≥ 1`) Bézout Layer Active Sawtooth Sum, Odd-Midpoint Annihilation & Support Threshold
   (`bezoutLayerActiveSawtoothSum`, `bezoutLayerActiveSawtoothSum_two_eq`,
   `bezoutLayerActiveSawtoothSum_midpoint_summand_eq_zero`,
   `eq_odd_midpoint_of_dvd_shell`,
   `bezoutLayerActiveSawtoothSum_eq_zero_of_lt_odd_midpoint`):**
   - For every depth $r \ge 1$, cutoff $N \in \mathbb{N}$, weight $c : \mathbb{N} \to \mathbb{R}$, and
     integer $m \in \mathbb{N}$, the $r$-th Bézout shell active sawtooth response is
     $$\operatorname{bezoutLayerActiveSawtoothSum}\,r\,N\,c\,m :=
       \frac{1}{2} \sum_{\substack{2r - 1 \le d \le N \\ d \mid m}}
         \left(c(d) - (2r - 1)\frac{c(d)}{d}\right).$$
   - Any divisor $d \ge 2r - 1$ dividing both endpoints $n + 1 - r$ and $n + r$ ($r - 1 \le n$)
     of the $r$-th Bézout shell must equal the odd midpoint $d = 2r - 1$, where the summand
     $c(d) - (2r - 1)c(d)/d$ vanishes identically.
   - For every $1 \le m < 2r - 1$, `bezoutLayerActiveSawtoothSum r N c m = 0`.

2. **General `w`-Step Difference Telescoping & Arbitrary-Depth `(2r - 1)`-Step Bézout Shell Telescoping
   (`sum_range_sub_add_step_eq_boundary`,
   `sum_range_bezoutLayerActiveSawtoothSum_sub_add_eq_head_sub_terminal`):**
   - For any sequence $F : \mathbb{N} \to \mathbb{R}$ and any step width $w \ge 1$:
     $$\sum_{n=0}^{M-1} \bigl(F(n) - F(n + w)\bigr) =
       \sum_{j=0}^{w-1} F(j) - \sum_{j=0}^{w-1} F(M + j).$$
   - Specializing to $F = \operatorname{bezoutLayerActiveSawtoothSum}\,r\,N\,c$ and $w = 2r - 1$
     ($r \ge 1$), all initial terms $F(1), \dots, F(2r - 2)$ vanish identically, so the $r$-th
     Bézout shell sum telescopes to $F(0)$ minus the $2r - 1$ terminal boundary values!

3. **Exact Sieve Formula & Sub-Horizon Cutoff-Independent Route PM Profile of the Second Bézout Layer (`r = 2`)
   (`secondLayerActiveSawtoothSum_eq_sieveSeq_add_low_divisors`,
   `pmSecondLayerSawtoothComponent`,
   `secondLayerActiveSawtoothSum_pmPowerDampedRealWeight_eq`,
   `pmSecondLayerSawtoothComponent_one`, `pmSecondLayerSawtoothComponent_two`,
   `pmFourStepBezoutInteriorPrefix`,
   `pmBezoutInteriorPrefix_eq_secondLayer_pair_add_fourStep`):**
   - For any sieve weight $c : \mathbb{N} \to \mathbb{R}$, cutoff $N \ge 2$, and $m \in \mathbb{N}$:
     $$\operatorname{secondLayerActiveSawtoothSum}\,N\,c\,m =
       \frac{1}{2}\Bigl(\operatorname{sieveSeq}\,N\,c\,m - 3\,\operatorname{sieveSeq}\,N\,\bigl(d \mapsto \tfrac{c(d)}{d}\bigr)\,m\Bigr)
       + c(1) + \left(\text{if } 2 \mid m \text{ then } \frac{1}{4}c(2) \text{ else } 0\right).$$
   - For Route PM ($c = \operatorname{pmPowerDampedRealWeight}\,\varepsilon$) and every sub-horizon
     integer $1 \le m \le N$ ($N \ge 2$), `secondLayerActiveSawtoothSum` coincides with the
     **cutoff-independent** profile:
     $$\operatorname{pmSecondLayerSawtoothComponent}\,\varepsilon\,m :=
       \frac{\tau_\varepsilon(m) - 3\,\tau_{1+\varepsilon}(m)}{2} + 1 -
       \left(\text{if } 2 \mid m \text{ then } \frac{2^{-\varepsilon}}{4} \text{ else } 0\right),$$
     which vanishes at $m = 1$ and $m = 2$ and decomposes `pmBezoutInteriorPrefix ε n` into the
     horizon-free 3-step difference `pmSecondLayerSawtoothComponent ε (n - 1) - pmSecondLayerSawtoothComponent ε (n + 2)`
     plus `pmFourStepBezoutInteriorPrefix ε n`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Arbitrary-Depth (`r ≥ 1`) Bézout Layer Active Sawtooth Sum & Odd-Midpoint Annihilation -/

/-- **Arbitrary-Depth Bézout Layer Active Sawtooth Sum (`bezoutLayerActiveSawtoothSum`):**
For depth `r ≥ 1`, cutoff `N : ℕ`, sieve weight `c : ℕ → ℝ`, and integer `m : ℕ`, the `r`-th Bézout
layer active sawtooth sum weights divisors `d ∈ Icc (2 * r - 1) N` of `m` by
`(1 / 2) * (c d - (2 * r - 1) * c d / d)`. -/
def bezoutLayerActiveSawtoothSum (r N : ℕ) (c : ℕ → ℝ) (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ d ∈ (Finset.Icc (2 * r - 1) N).filter (fun d => d ∣ m),
    (c d - ((2 * r - 1 : ℕ) : ℝ) * c d / (d : ℝ))

/-- At depth `r = 2`, `bezoutLayerActiveSawtoothSum 2 N c m` coincides with
`secondLayerActiveSawtoothSum N c m`. -/
theorem bezoutLayerActiveSawtoothSum_two_eq (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    bezoutLayerActiveSawtoothSum 2 N c m = secondLayerActiveSawtoothSum N c m := by
  unfold bezoutLayerActiveSawtoothSum secondLayerActiveSawtoothSum
  norm_num

/-- **Odd-Midpoint Summand Annihilation (`bezoutLayerActiveSawtoothSum_midpoint_summand_eq_zero`):**
For every `r ≥ 1` and `c : ℕ → ℝ`, at the odd midpoint modulus `d = 2 * r - 1`, the `r`-th Bézout
layer summand `c d - (2 * r - 1) * c d / d` vanishes identically. -/
theorem bezoutLayerActiveSawtoothSum_midpoint_summand_eq_zero
    {r : ℕ} (hr : 1 ≤ r) (c : ℕ → ℝ) :
    c (2 * r - 1) - ((2 * r - 1 : ℕ) : ℝ) * c (2 * r - 1) / ((2 * r - 1 : ℕ) : ℝ) = 0 := by
  have hd_pos : 0 < 2 * r - 1 := by omega
  have hdR : ((2 * r - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
  rw [mul_div_cancel_left₀ _ hdR, sub_self]

/-- **Arbitrary-Depth Bézout Shell Endpoint Disjointness (`eq_odd_midpoint_of_dvd_shell`):**
For any depth `r ≥ 1`, step `n` with `r - 1 ≤ n`, and divisor `d ≥ 2 * r - 1`, if `d` divides both
endpoints `n + 1 - r` and `n + r` of the `r`-th Bézout shell, then `d = 2 * r - 1`. -/
theorem eq_odd_midpoint_of_dvd_shell {r n d : ℕ}
    (hr : 1 ≤ r) (hn : r - 1 ≤ n) (hd : 2 * r - 1 ≤ d)
    (hleft : d ∣ (n + 1 - r)) (hright : d ∣ (n + r)) :
    d = 2 * r - 1 := by
  have hshift : n + r = (n + 1 - r) + (2 * r - 1) := by omega
  rw [hshift] at hright
  have hdvd : d ∣ (2 * r - 1) := (Nat.dvd_add_right hleft).mp hright
  have hle : d ≤ 2 * r - 1 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- **Support Threshold of the `r`-th Bézout Layer (`bezoutLayerActiveSawtoothSum_eq_zero_of_lt_odd_midpoint`):**
For every `r ≥ 1`, `N : ℕ`, `c : ℕ → ℝ`, and `1 ≤ m < 2 * r - 1`,
`bezoutLayerActiveSawtoothSum r N c m = 0`. -/
theorem bezoutLayerActiveSawtoothSum_eq_zero_of_lt_odd_midpoint
    {r : ℕ} (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < 2 * r - 1) :
    bezoutLayerActiveSawtoothSum r N c m = 0 := by
  unfold bezoutLayerActiveSawtoothSum
  suffices h : (Finset.Icc (2 * r - 1) N).filter (fun d => d ∣ m) = ∅ by
    rw [h, Finset.sum_empty, mul_zero]
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
  intro hd hdm
  have hle : d ≤ m := Nat.le_of_dvd (by omega) hdm
  omega

/-! ## §2. General `w`-Step Difference Telescoping & Arbitrary-Depth `(2r - 1)`-Step Shell Telescoping -/

/-- **General `w`-Step Difference Telescoping Identity (`sum_range_sub_add_step_eq_boundary`):**
For any sequence `F : ℕ → ℝ`, any step width `w : ℕ`, and any horizon `M : ℕ`:
`∑ n ∈ Finset.range M, (F n - F (n + w)) = (∑ j ∈ Finset.range w, F j) - ∑ j ∈ Finset.range w, F (M + j)`. -/
theorem sum_range_sub_add_step_eq_boundary (F : ℕ → ℝ) (w M : ℕ) :
    (∑ n ∈ Finset.range M, (F n - F (n + w))) =
      (∑ j ∈ Finset.range w, F j) - ∑ j ∈ Finset.range w, F (M + j) := by
  induction M with
  | zero =>
    simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have hshift :
        (∑ j ∈ Finset.range w, F (k + 1 + j)) =
          (∑ j ∈ Finset.range w, F (k + j)) - F k + F (k + w) := by
      have h1 : (∑ j ∈ Finset.range (w + 1), F (k + j)) =
          (∑ j ∈ Finset.range w, F (k + j)) + F (k + w) :=
        Finset.sum_range_succ (fun j => F (k + j)) w
      have h2 : (∑ j ∈ Finset.range (w + 1), F (k + j)) =
          F k + ∑ j ∈ Finset.range w, F (k + 1 + j) := by
        rw [Finset.sum_range_succ' (fun j => F (k + j)) w]
        simp only [Nat.add_zero]
        have hcongr :
            (∑ j ∈ Finset.range w, F (k + (j + 1))) =
              ∑ j ∈ Finset.range w, F (k + 1 + j) :=
          Finset.sum_congr rfl fun j _ => by congr 1; omega
        rw [hcongr]
        ring
      linarith
    linarith

/-- **Arbitrary-Depth `(2r - 1)`-Step Bézout Shell Telescoping Law
(`sum_range_bezoutLayerActiveSawtoothSum_sub_add_eq_head_sub_terminal`):**
For every depth `r ≥ 1`, cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and `M : ℕ`, because
`bezoutLayerActiveSawtoothSum r N c j = 0` for all `1 ≤ j < 2 * r - 1`, the `(2 * r - 1)`-step
difference sum telescopes to the single `j = 0` term minus the `2 * r - 1` terminal boundary terms:
`∑ n ∈ range M, (F n - F (n + (2 * r - 1))) = F 0 - ∑ j ∈ range (2 * r - 1), F (M + j)`. -/
theorem sum_range_bezoutLayerActiveSawtoothSum_sub_add_eq_head_sub_terminal
    {r : ℕ} (hr : 1 ≤ r) (N : ℕ) (c : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Finset.range M,
      (bezoutLayerActiveSawtoothSum r N c n -
        bezoutLayerActiveSawtoothSum r N c (n + (2 * r - 1)))) =
      bezoutLayerActiveSawtoothSum r N c 0 -
        ∑ j ∈ Finset.range (2 * r - 1), bezoutLayerActiveSawtoothSum r N c (M + j) := by
  rw [sum_range_sub_add_step_eq_boundary (bezoutLayerActiveSawtoothSum r N c) (2 * r - 1) M]
  congr 1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 * r - 1 = k + 1 := ⟨2 * r - 2, by omega⟩
  rw [hk, Finset.sum_range_succ' (bezoutLayerActiveSawtoothSum r N c) k]
  have hzero :
      (∑ i ∈ Finset.range k, bezoutLayerActiveSawtoothSum r N c (i + 1)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact bezoutLayerActiveSawtoothSum_eq_zero_of_lt_odd_midpoint N c (by omega) (by omega)
  rw [hzero, zero_add]

/-! ## §3. Exact Sieve Formula & Cutoff-Independent Route PM Profile of the Second Bézout Layer (`r = 2`) -/

/-- **General Sieve Formula for `secondLayerActiveSawtoothSum`
(`secondLayerActiveSawtoothSum_eq_sieveSeq_add_low_divisors`):**
For every cutoff `N ≥ 2`, sieve weight `c : ℕ → ℝ`, and `m : ℕ`:
`secondLayerActiveSawtoothSum N c m = (1 / 2) * (sieveSeq N c m - 3 * sieveSeq N (fun d => c d / d) m) + c 1 + (if 2 ∣ m then (1 / 4) * c 2 else 0)`. -/
theorem secondLayerActiveSawtoothSum_eq_sieveSeq_add_low_divisors
    {N : ℕ} (hN : 2 ≤ N) (c : ℕ → ℝ) (m : ℕ) :
    secondLayerActiveSawtoothSum N c m =
      (1 / 2 : ℝ) *
        (sieveSeq N c m - 3 * sieveSeq N (fun d => c d / (d : ℝ)) m) +
      c 1 + (if 2 ∣ m then (1 / 4 : ℝ) * c 2 else 0) := by
  let f : ℕ → ℝ := fun d => c d - 3 * c d / (d : ℝ)
  have hIcc : Finset.Icc 1 N = insert 1 (insert 2 (Finset.Icc 3 N)) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot1 : (1 : ℕ) ∉ (insert 2 (Finset.Icc 3 N)).filter (fun d => d ∣ m) := by
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hnot2 : (2 : ℕ) ∉ (Finset.Icc 3 N).filter (fun d => d ∣ m) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hsum_full :
      (∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ m), f d) =
        sieveSeq N c m - 3 * sieveSeq N (fun d => c d / (d : ℝ)) m := by
    unfold sieveSeq
    dsimp only [f]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    refine congrArg₂ (· - ·) rfl ?_
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  have hsplit1 :
      (Finset.Icc 1 N).filter (fun d => d ∣ m) =
        insert 1 ((insert 2 (Finset.Icc 3 N)).filter (fun d => d ∣ m)) := by
    rw [hIcc, Finset.filter_insert, if_pos (one_dvd m)]
  have hsum1 :
      (∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ m), f d) =
        f 1 + ∑ d ∈ (insert 2 (Finset.Icc 3 N)).filter (fun d => d ∣ m), f d := by
    rw [hsplit1, Finset.sum_insert hnot1]
  have hsum2 :
      (∑ d ∈ (insert 2 (Finset.Icc 3 N)).filter (fun d => d ∣ m), f d) =
        (if 2 ∣ m then f 2 else 0) +
          ∑ d ∈ (Finset.Icc 3 N).filter (fun d => d ∣ m), f d := by
    rw [Finset.filter_insert]
    split_ifs with h2m
    · rw [Finset.sum_insert hnot2]
    · ring
  have hf1 : f 1 = -2 * c 1 := by
    dsimp only [f]
    norm_num
    ring
  have hf2 : (if 2 ∣ m then f 2 else 0) =
      if 2 ∣ m then -(1 / 2 : ℝ) * c 2 else 0 := by
    split_ifs with h2m
    · dsimp only [f]
      norm_num
      ring
    · rfl
  unfold secondLayerActiveSawtoothSum
  change (1 / 2 : ℝ) * (∑ d ∈ (Finset.Icc 3 N).filter (fun d => d ∣ m), f d) = _
  have h3 :
      (∑ d ∈ (Finset.Icc 3 N).filter (fun d => d ∣ m), f d) =
        (sieveSeq N c m - 3 * sieveSeq N (fun d => c d / (d : ℝ)) m) -
          f 1 - (if 2 ∣ m then f 2 else 0) := by
    linarith [hsum_full, hsum1, hsum2]
  rw [h3, hf1, hf2]
  split_ifs <;> ring

/-- **Horizon-Free Second-Layer Sawtooth Component for Route PM (`pmSecondLayerSawtoothComponent`):**
The cutoff-independent second-layer (`r = 2`) Bézout sawtooth profile at integer `m`:
`pmSecondLayerSawtoothComponent ε m = (τ_ε(m) - 3 * τ_{1+ε}(m)) / 2 + 1 - (if 2 ∣ m then 2^{-ε} / 4 else 0)`. -/
def pmSecondLayerSawtoothComponent (ε : ℝ) (m : ℕ) : ℝ :=
  (pmPowerDampedDivisorCoeff ε m - 3 * pmPowerDampedDivisorCoeff (1 + ε) m) / 2 +
    1 - (if 2 ∣ m then (2 : ℝ) ^ (-ε) / 4 else 0)

/-- **Sub-Horizon Cutoff-Independence of `secondLayerActiveSawtoothSum` for Route PM
(`secondLayerActiveSawtoothSum_pmPowerDampedRealWeight_eq`):**
For every `ε : ℝ`, cutoff `N ≥ 2`, and sub-horizon integer `1 ≤ m ≤ N`,
`secondLayerActiveSawtoothSum N (pmPowerDampedRealWeight ε) m` equals the horizon-free profile
`pmSecondLayerSawtoothComponent ε m`. -/
theorem secondLayerActiveSawtoothSum_pmPowerDampedRealWeight_eq
    (ε : ℝ) {N m : ℕ} (hN : 2 ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    secondLayerActiveSawtoothSum N (pmPowerDampedRealWeight ε) m =
      pmSecondLayerSawtoothComponent ε m := by
  rw [secondLayerActiveSawtoothSum_eq_sieveSeq_add_low_divisors hN,
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hm1 hmN,
    sieveSeq_pmPowerDampedRealWeight_div_eq_divisorCoeff_add_one ε hm1 hmN]
  have hc1 : pmPowerDampedRealWeight ε 1 = 1 := by
    unfold pmPowerDampedRealWeight moebiusReal
    simp
  have hc2 : pmPowerDampedRealWeight ε 2 = -(2 : ℝ) ^ (-ε) := by
    unfold pmPowerDampedRealWeight moebiusReal
    have hmu2 : ArithmeticFunction.moebius 2 = -1 :=
      ArithmeticFunction.moebius_apply_prime Nat.prime_two
    rw [hmu2]
    norm_num
  rw [hc1, hc2]
  unfold pmSecondLayerSawtoothComponent
  split_ifs <;> ring

/-- At `m = 1`, `pmSecondLayerSawtoothComponent ε 1 = 0`. -/
@[simp]
theorem pmSecondLayerSawtoothComponent_one (ε : ℝ) :
    pmSecondLayerSawtoothComponent ε 1 = 0 := by
  have h := secondLayerActiveSawtoothSum_pmPowerDampedRealWeight_eq ε
    (N := 2) (m := 1) (by omega) (by omega) (by omega)
  rw [secondLayerActiveSawtoothSum_eq_zero_of_lt_three 2 (pmPowerDampedRealWeight ε)
    (by omega) (by omega)] at h
  exact h.symm

/-- At `m = 2`, `pmSecondLayerSawtoothComponent ε 2 = 0`. -/
@[simp]
theorem pmSecondLayerSawtoothComponent_two (ε : ℝ) :
    pmSecondLayerSawtoothComponent ε 2 = 0 := by
  have h := secondLayerActiveSawtoothSum_pmPowerDampedRealWeight_eq ε
    (N := 2) (m := 2) (by omega) (by omega) (by omega)
  rw [secondLayerActiveSawtoothSum_eq_zero_of_lt_three 2 (pmPowerDampedRealWeight ε)
    (by omega) (by omega)] at h
  exact h.symm

/-- The **horizon-free four-step Bézout interior prefix** at step `n`:
`pmFourStepBezoutInteriorPrefix ε n = pmBezoutInteriorPrefix ε n - (pmSecondLayerSawtoothComponent ε (n - 1) - pmSecondLayerSawtoothComponent ε (n + 2))`. -/
def pmFourStepBezoutInteriorPrefix (ε : ℝ) (n : ℕ) : ℝ :=
  pmBezoutInteriorPrefix ε n -
    (pmSecondLayerSawtoothComponent ε (n - 1) - pmSecondLayerSawtoothComponent ε (n + 2))

/-- **Horizon-Free Second-Layer + Four-Step Decomposition of `pmBezoutInteriorPrefix`
(`pmBezoutInteriorPrefix_eq_secondLayer_pair_add_fourStep`):**
For every `ε : ℝ` and `n : ℕ`:
`pmBezoutInteriorPrefix ε n = (pmSecondLayerSawtoothComponent ε (n - 1) - pmSecondLayerSawtoothComponent ε (n + 2)) + pmFourStepBezoutInteriorPrefix ε n`. -/
theorem pmBezoutInteriorPrefix_eq_secondLayer_pair_add_fourStep (ε : ℝ) (n : ℕ) :
    pmBezoutInteriorPrefix ε n =
      (pmSecondLayerSawtoothComponent ε (n - 1) - pmSecondLayerSawtoothComponent ε (n + 2)) +
        pmFourStepBezoutInteriorPrefix ε n := by
  unfold pmFourStepBezoutInteriorPrefix
  ring

/-- **Horizon-Free Two-Layer Bézout Decomposition of `pmPowerDampedCenteredDivisorPrefix`
(`pmPowerDampedCenteredDivisorPrefix_eq_first_and_second_layer_add_fourStep`):**
For every `ε : ℝ` and `n : ℕ`, `pmPowerDampedCenteredDivisorPrefix ε n` decomposes into:
1. The First Bézout Layer (`addDiff (pmActiveSawtoothComponent ε) n`),
2. The Second Bézout Layer (`pmSecondLayerSawtoothComponent ε (n - 1) - pmSecondLayerSawtoothComponent ε (n + 2)`),
3. The Four-Step Bézout Interior (`pmFourStepBezoutInteriorPrefix ε n`). -/
theorem pmPowerDampedCenteredDivisorPrefix_eq_first_and_second_layer_add_fourStep
    (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n =
      addDiff (pmActiveSawtoothComponent ε) n +
        (pmSecondLayerSawtoothComponent ε (n - 1) -
          pmSecondLayerSawtoothComponent ε (n + 2)) +
        pmFourStepBezoutInteriorPrefix ε n := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior,
    pmBezoutInteriorPrefix_eq_secondLayer_pair_add_fourStep]
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence
