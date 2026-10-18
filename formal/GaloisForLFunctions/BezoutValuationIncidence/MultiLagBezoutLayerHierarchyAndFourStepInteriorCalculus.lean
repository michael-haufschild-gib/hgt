import GaloisForLFunctions.BezoutValuationIncidence.ThreeStepBezoutInteriorSawtoothAndSecondOrderSmoothing

/-!
# Multi-Lag Bézout Layer Hierarchy, Odd-Width Midpoint Annihilation, and Four-Step Interior Calculus

In `BezoutPronicInteriorSawtoothAndPredecessorPeakSplit`, the first Bézout layer peeled off the
divisors $d \mid n$ and $d \mid (n + 1)$ (separation $1 = 2\cdot 1 - 1$) from the centered sawtooth
sum $W_{N,c}(n)$, leaving the doubly-inactive interior `bezoutInteriorSawtoothSum N c n` supported
on divisors $d$ dividing neither $n$ nor $n + 1$.

In this module, we establish the **Multi-Lag Bézout Layer Hierarchy** governing the interior
sawtooth sum across all higher lags $r \ge 1$:

1. **General Multi-Lag and Multi-Lead Sawtooth Evaluations & Odd-Midpoint Annihilation
   (`centeredDiscreteSawtooth_add_of_dvd`, `centeredDiscreteSawtooth_of_dvd_add`,
   `centeredDiscreteSawtooth_odd_midpoint_eq_zero`):**
   - For any modulus $d > 0$, any multiple $m$ ($d \mid m$), and any lag $r < d$:
     $$\operatorname{centeredDiscreteSawtooth}(d, m + r) = -\frac{d - (2r + 1)}{2d} = -\frac{1}{2}\left(1 - \frac{2r + 1}{d}\right).$$
   - For any modulus $d > 0$, any step $n$, and any lead $1 \le r \le d$ with $d \mid (n + r)$:
     $$\operatorname{centeredDiscreteSawtooth}(d, n) = +\frac{d - (2r - 1)}{2d} = +\frac{1}{2}\left(1 - \frac{2r - 1}{d}\right).$$
   - Consequently, the $r$-th symmetric Bézout shell $\{n + 1 - r,\, n + r\}$ has width $2r - 1$,
     carries the exact odd-harmonic weight $c(d) - (2r - 1)\frac{c(d)}{d}$, and vanishes identically
     at the odd midpoint modulus $d = 2r - 1$ (`centeredDiscreteSawtooth (2 * r - 1) n = 0`).

2. **Automatic $d \ge 3$ Support of the Bézout Interior & Second-Layer Disjointness
   (`three_le_of_not_dvd_of_not_dvd_succ`, `not_dvd_and_not_dvd_succ_of_three_le_of_dvd_pred`,
   `not_dvd_and_not_dvd_succ_of_three_le_of_dvd_add_two`,
   `eq_three_of_three_le_of_dvd_pred_of_dvd_add_two`):**
   - Because $2 \mid n$ or $2 \mid (n + 1)$ for every $n \in \mathbb{N}$, neither $d = 1$ nor $d = 2$
     ever belongs to the Bézout interior $\{d : \neg(d \mid n) \land \neg(d \mid (n + 1))\}$.
   - Conversely, every divisor $d \ge 3$ with $d \mid (n - 1)$ ($n \ge 1$) or $d \mid (n + 2)$
     is **automatically** inside the Bézout interior $\{d : \neg(d \mid n) \land \neg(d \mid (n + 1))\}$.
   - Any divisor $d \ge 3$ dividing both $n - 1$ and $n + 2$ ($n \ge 1$) must divide
     $(n + 2) - (n - 1) = 3$, forcing $d = 3$, where $\operatorname{centeredDiscreteSawtooth}(3, n) = 0$!

3. **Exact Second-Layer ($r = 2$) Active Pair & Four-Step Bézout Interior Decomposition
   (`secondLayerActiveSawtoothSum`, `fourStepBezoutInteriorSawtoothSum`,
   `bezoutInteriorSawtoothSum_eq_secondLayer_pair_add_fourStep`,
   `weightedCenteredSawtoothSum_eq_first_and_second_layer_add_fourStep`,
   `sum_Icc_secondLayer_pair_eq_three_boundary`):**
   - Peeling off the second Bézout shell $\{n - 1, n + 2\}$ ($d \ge 3$) from `bezoutInteriorSawtoothSum N c n`
     decomposes the interior sawtooth into the 3-step difference
     $$\operatorname{secondLayerActiveSawtoothSum}(N, c, n - 1) - \operatorname{secondLayerActiveSawtoothSum}(N, c, n + 2)$$
     plus the quadruply-inactive `fourStepBezoutInteriorSawtoothSum N c n` (supported on $d \ge 4$).
   - When multiplied by the active impulse at $n + 1$, the right endpoint $n + 2$ is at **lag $1$**
     ($\gcd(n + 1, n + 2) = 1$) while the left endpoint $n - 1$ is at **lag $2$** ($(n + 1) - (n - 1) = 2$),
     transferring lag-1 correlation to lag-2 correlation across the multi-lag hierarchy.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. General Multi-Lag and Multi-Lead Sawtooth Evaluations & Odd-Midpoint Annihilation -/

/-- If `d ∣ m` and `1 ≤ j < d`, then `d` cannot divide `m + j`. -/
theorem not_dvd_add_of_dvd_of_lt {d m j : ℕ} (hdvd : d ∣ m) (hj1 : 1 ≤ j) (hjd : j < d) :
    ¬ (d ∣ (m + j)) := by
  intro hsum
  have hdj : d ∣ j := (Nat.dvd_add_right hdvd).mp hsum
  have hle : d ≤ j := Nat.le_of_dvd (by omega) hdj
  omega

/-- If `d ∣ (n + r)` and `1 ≤ j < r ≤ d`, then `d` cannot divide `n + j`. -/
theorem not_dvd_add_of_dvd_add_of_lt {d n j r : ℕ}
    (hdvd : d ∣ (n + r)) (hj1 : 1 ≤ j) (hjr : j < r) (hrd : r ≤ d) :
    ¬ (d ∣ (n + j)) := by
  intro hnj
  have hsub : n + r = (n + j) + (r - j) := by omega
  rw [hsub] at hdvd
  have hdrj : d ∣ (r - j) := (Nat.dvd_add_right hnj).mp hdvd
  have hle : d ≤ r - j := Nat.le_of_dvd (by omega) hdrj
  omega

/-- **General Multi-Lag Sawtooth Evaluation (`centeredDiscreteSawtooth_add_of_dvd`):**
For every modulus `d > 0`, every multiple `m` (`d ∣ m`), and every lag `r < d`,
`centeredDiscreteSawtooth d (m + r) = -((d : ℝ) - (2 * (r : ℝ) + 1)) / (2 * (d : ℝ))`. -/
theorem centeredDiscreteSawtooth_add_of_dvd {d m r : ℕ}
    (hd : 0 < d) (hdvd : d ∣ m) (hr : r < d) :
    centeredDiscreteSawtooth d (m + r) =
      -((d : ℝ) - (2 * (r : ℝ) + 1)) / (2 * (d : ℝ)) := by
  induction r with
  | zero =>
    simp only [Nat.add_zero, Nat.cast_zero, mul_zero, zero_add]
    rw [centeredDiscreteSawtooth_of_dvd hd hdvd]
    ring
  | succ k ih =>
    have hk_lt : k < d := by omega
    have hstep := centeredDiscreteSawtooth_succ_sub_eq hd (m + k)
    have hndvd : ¬ (d ∣ (m + k + 1)) := by
      have heq : m + k + 1 = m + (k + 1) := by omega
      rw [heq]
      exact not_dvd_add_of_dvd_of_lt hdvd (by omega) hr
    rw [if_neg hndvd, sub_zero] at hstep
    have hih := ih hk_lt
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    have h_eq : centeredDiscreteSawtooth d (m + (k + 1)) =
        centeredDiscreteSawtooth d (m + k) + 1 / (d : ℝ) := by
      have heq : m + (k + 1) = m + k + 1 := by omega
      rw [heq]
      linarith
    rw [h_eq, hih]
    push_cast
    field_simp [hdR]
    ring

/-- **General Multi-Lead Sawtooth Evaluation (`centeredDiscreteSawtooth_of_dvd_add`):**
For every modulus `d > 0`, step `n : ℕ`, and lead `1 ≤ r ≤ d` such that `d ∣ (n + r)`,
`centeredDiscreteSawtooth d n = ((d : ℝ) - (2 * (r : ℝ) - 1)) / (2 * (d : ℝ))`. -/
theorem centeredDiscreteSawtooth_of_dvd_add {d n r : ℕ}
    (hd : 0 < d) (hr1 : 1 ≤ r) (hrd : r ≤ d) (hdvd : d ∣ (n + r)) :
    centeredDiscreteSawtooth d n =
      ((d : ℝ) - (2 * (r : ℝ) - 1)) / (2 * (d : ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, r = k + 1 := ⟨r - 1, by omega⟩
  induction k generalizing n with
  | zero =>
    simp only [Nat.zero_add, Nat.cast_one, mul_one]
    have h2 : (2 : ℝ) - 1 = 1 := by ring
    rw [h2]
    exact centeredDiscreteSawtooth_of_dvd_succ hd hdvd
  | succ j ih =>
    have hstep := centeredDiscreteSawtooth_succ_sub_eq hd n
    have hndvd : ¬ (d ∣ (n + 1)) :=
      not_dvd_add_of_dvd_add_of_lt hdvd (by omega) (by omega) hrd
    rw [if_neg hndvd, sub_zero] at hstep
    have hdvd' : d ∣ ((n + 1) + (j + 1)) := by
      have heq : (n + 1) + (j + 1) = n + (j + 1 + 1) := by omega
      rwa [heq]
    have hih := ih (n := n + 1) (by omega) (by omega) hdvd'
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    have h_eq : centeredDiscreteSawtooth d n =
        centeredDiscreteSawtooth d (n + 1) - 1 / (d : ℝ) := by linarith
    rw [h_eq, hih]
    push_cast
    field_simp [hdR]
    ring

/-- **Odd-Midpoint Sawtooth Annihilation (`centeredDiscreteSawtooth_odd_midpoint_eq_zero`):**
At any odd modulus `d = 2 * r - 1` (`r ≥ 1`), whenever `d ∣ (n + r)`, the step `n` sits at the
exact midpoint of the sawtooth period of `d`, so `centeredDiscreteSawtooth (2 * r - 1) n = 0`. -/
theorem centeredDiscreteSawtooth_odd_midpoint_eq_zero {n r : ℕ}
    (hr : 1 ≤ r) (hdvd : (2 * r - 1) ∣ (n + r)) :
    centeredDiscreteSawtooth (2 * r - 1) n = 0 := by
  have hd_pos : 0 < 2 * r - 1 := by omega
  have hrd : r ≤ 2 * r - 1 := by omega
  rw [centeredDiscreteSawtooth_of_dvd_add hd_pos hr hrd hdvd]
  have hcast : ((2 * r - 1 : ℕ) : ℝ) = 2 * (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * r), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [hcast, sub_self, zero_div]

/-- **Second-Layer Post-Jump Evaluation (`centeredDiscreteSawtooth_of_dvd_pred`):**
For every `d ≥ 2` and `n ≥ 1` with `d ∣ (n - 1)`,
`centeredDiscreteSawtooth d n = -((d : ℝ) - 3) / (2 * (d : ℝ))`. -/
theorem centeredDiscreteSawtooth_of_dvd_pred {d n : ℕ}
    (hd : 2 ≤ d) (hn : 1 ≤ n) (hdvd : d ∣ (n - 1)) :
    centeredDiscreteSawtooth d n = -((d : ℝ) - 3) / (2 * (d : ℝ)) := by
  have h := centeredDiscreteSawtooth_add_of_dvd (by omega : 0 < d) hdvd (by omega : 1 < d)
  rw [Nat.sub_add_cancel hn] at h
  rw [h]
  ring

/-- **Second-Layer Pre-Jump Evaluation (`centeredDiscreteSawtooth_of_dvd_add_two`):**
For every `d ≥ 2` and `n : ℕ` with `d ∣ (n + 2)`,
`centeredDiscreteSawtooth d n = ((d : ℝ) - 3) / (2 * (d : ℝ))`. -/
theorem centeredDiscreteSawtooth_of_dvd_add_two {d n : ℕ}
    (hd : 2 ≤ d) (hdvd : d ∣ (n + 2)) :
    centeredDiscreteSawtooth d n = ((d : ℝ) - 3) / (2 * (d : ℝ)) := by
  have h := centeredDiscreteSawtooth_of_dvd_add (by omega : 0 < d) (by omega : 1 ≤ 2) hd hdvd
  rw [h]
  ring

/-- At `d = 3`, whenever `3 ∣ (n + 2)` (or `3 ∣ (n - 1)` for `n ≥ 1`),
`centeredDiscreteSawtooth 3 n = 0`. -/
theorem centeredDiscreteSawtooth_three_of_dvd_add_two {n : ℕ} (hdvd : 3 ∣ (n + 2)) :
    centeredDiscreteSawtooth 3 n = 0 := by
  rw [centeredDiscreteSawtooth_of_dvd_add_two (by omega : 2 ≤ 3) hdvd]
  norm_num

/-! ## §2. Automatic `d ≥ 3` Support of the Bézout Interior & Second-Layer Disjointness -/

/-- Every natural number `n` has `2 ∣ n` or `2 ∣ (n + 1)`. -/
theorem two_dvd_self_or_succ (n : ℕ) : 2 ∣ n ∨ 2 ∣ (n + 1) := by
  omega

/-- **Automatic `d ≥ 3` Support of the Bézout Interior (`three_le_of_not_dvd_of_not_dvd_succ`):**
If `d ≥ 1` divides neither `n` nor `n + 1`, then `d ≥ 3`. -/
theorem three_le_of_not_dvd_of_not_dvd_succ {d n : ℕ}
    (hd1 : 1 ≤ d) (hdn : ¬ (d ∣ n)) (hdn1 : ¬ (d ∣ (n + 1))) :
    3 ≤ d := by
  by_contra hlt
  have hle : d ≤ 2 := by omega
  interval_cases d
  · exact hdn (one_dvd n)
  · rcases two_dvd_self_or_succ n with h2n | h2n1
    · exact hdn h2n
    · exact hdn1 h2n1

/-- Every divisor `d ≥ 3` dividing `n - 1` (`n ≥ 1`) automatically lies in the Bézout interior
`¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1))`. -/
theorem not_dvd_and_not_dvd_succ_of_three_le_of_dvd_pred {d n : ℕ}
    (hd3 : 3 ≤ d) (hn : 1 ≤ n) (hdvd : d ∣ (n - 1)) :
    ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)) := by
  refine ⟨fun hdn => ?_, fun hdn1 => ?_⟩
  · have hsucc : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    rw [hsucc] at hdn
    have hd1 : d = 1 := eq_one_of_dvd_and_dvd_succ hdvd hdn
    omega
  · have hsucc : n + 1 = (n - 1) + 2 := by omega
    rw [hsucc] at hdn1
    have hd2 : d ∣ 2 := dvd_two_of_dvd_and_dvd_add_two hdvd hdn1
    have hle : d ≤ 2 := Nat.le_of_dvd (by omega) hd2
    omega

/-- Every divisor `d ≥ 3` dividing `n + 2` automatically lies in the Bézout interior
`¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1))`. -/
theorem not_dvd_and_not_dvd_succ_of_three_le_of_dvd_add_two {d n : ℕ}
    (hd3 : 3 ≤ d) (hdvd : d ∣ (n + 2)) :
    ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)) := by
  refine ⟨fun hdn => ?_, fun hdn1 => ?_⟩
  · have hd2 : d ∣ 2 := dvd_two_of_dvd_and_dvd_add_two hdn hdvd
    have hle : d ≤ 2 := Nat.le_of_dvd (by omega) hd2
    omega
  · have hd1 : d = 1 := eq_one_of_dvd_and_dvd_succ hdn1 hdvd
    omega

/-- Any divisor `d ≥ 3` dividing both `n - 1` (`n ≥ 1`) and `n + 2` must equal `3`. -/
theorem eq_three_of_three_le_of_dvd_pred_of_dvd_add_two {d n : ℕ}
    (hd3 : 3 ≤ d) (hn : 1 ≤ n) (hpred : d ∣ (n - 1)) (hadd2 : d ∣ (n + 2)) :
    d = 3 := by
  have h3 : n + 2 = (n - 1) + 3 := by omega
  rw [h3] at hadd2
  have hd3_dvd : d ∣ 3 := (Nat.dvd_add_right hpred).mp hadd2
  have hle : d ≤ 3 := Nat.le_of_dvd (by omega) hd3_dvd
  omega

/-! ## §3. Exact Second-Layer Active Pair & Four-Step Bézout Interior Decomposition -/

/-- **Second-Layer Active Sawtooth Evaluation (`secondLayerActiveSawtoothSum`):**
The weighted second-layer active response at `m`, summing `(1 / 2) * (c d - 3 * c d / d)` over all
divisors `d ∈ Icc 3 N` that divide `m`. (Note that `d = 3` contributes `0` automatically since
`1 - 3 / 3 = 0`.) -/
def secondLayerActiveSawtoothSum (N : ℕ) (c : ℕ → ℝ) (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ d ∈ (Finset.Icc 3 N).filter (fun d => d ∣ m),
    (c d - 3 * c d / (d : ℝ))

/-- **Four-Step Bézout Interior Sawtooth Sum (`fourStepBezoutInteriorSawtoothSum`):**
The weighted centered sawtooth sum at step `n` over all moduli `1 ≤ d ≤ N` that divide **none** of
the four consecutive integers `n - 1, n, n + 1, n + 2`. -/
def fourStepBezoutInteriorSawtoothSum (N : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  -∑ d ∈ (Finset.Icc 1 N).filter
      (fun d => ¬ (d ∣ (n - 1)) ∧ ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)) ∧ ¬ (d ∣ (n + 2))),
    c d * centeredDiscreteSawtooth d n

/-- For every `N, c, n`, the `d ∣ (n + 2)` pre-jump sum inside `bezoutInteriorSawtoothSum N c n`
equals `secondLayerActiveSawtoothSum N c (n + 2)`. -/
theorem sum_not_dvd_and_dvd_add_two_eq_secondLayerActiveSawtoothSum
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ d ∣ (n + 2)),
      c d * centeredDiscreteSawtooth d n) =
      secondLayerActiveSawtoothSum N c (n + 2) := by
  unfold secondLayerActiveSawtoothSum
  have hset :
      (Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ d ∣ (n + 2)) =
        (Finset.Icc 3 N).filter (fun d => d ∣ (n + 2)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd1, hdN⟩, hdn, hdn2⟩
      have hdn1 : ¬ (d ∣ (n + 1)) := not_dvd_succ_of_not_dvd_of_dvd_add_two hdn hdn2
      have hd3 : 3 ≤ d := three_le_of_not_dvd_of_not_dvd_succ hd1 hdn hdn1
      exact ⟨⟨hd3, hdN⟩, hdn2⟩
    · rintro ⟨⟨hd3, hdN⟩, hdn2⟩
      have hboth := not_dvd_and_not_dvd_succ_of_three_le_of_dvd_add_two hd3 hdn2
      exact ⟨⟨by omega, hdN⟩, hboth.1, hdn2⟩
  rw [hset, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd
  have hd2 : 2 ≤ d := by omega
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [centeredDiscreteSawtooth_of_dvd_add_two hd2 hd.2]
  field_simp [hdR]

/-- For every `N, c` and `n ≥ 1`, the `d ∣ (n - 1)` post-jump sum inside
`threeStepBezoutInteriorSawtoothSum N c n` equals `secondLayerActiveSawtoothSum N c (n - 1)`. -/
theorem sum_threeStep_dvd_pred_eq_neg_secondLayerActiveSawtoothSum
    (N : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (∑ d ∈ ((Finset.Icc 1 N).filter
        (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)) ∧ ¬ (d ∣ (n + 2)))).filter
          (fun d => d ∣ (n - 1)),
      c d * centeredDiscreteSawtooth d n) =
      -secondLayerActiveSawtoothSum N c (n - 1) := by
  unfold secondLayerActiveSawtoothSum
  have hsplit := (Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 3 N).filter (fun d => d ∣ (n - 1)))
    (fun d => d ∣ (n + 2))
    (fun d => (1 / 2 : ℝ) * (c d - 3 * c d / (d : ℝ)))).symm
  have hboth_zero :
      (∑ d ∈ ((Finset.Icc 3 N).filter (fun d => d ∣ (n - 1))).filter (fun d => d ∣ (n + 2)),
        (1 / 2 : ℝ) * (c d - 3 * c d / (d : ℝ))) = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    have hd3 : d = 3 := eq_three_of_three_le_of_dvd_pred_of_dvd_add_two hd.1.1.1 hn hd.1.2 hd.2
    subst hd3
    norm_num
  rw [hboth_zero, zero_add] at hsplit
  rw [Finset.mul_sum, hsplit, ← Finset.sum_neg_distrib]
  have hset :
      ((Finset.Icc 1 N).filter
        (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)) ∧ ¬ (d ∣ (n + 2)))).filter
          (fun d => d ∣ (n - 1)) =
      ((Finset.Icc 3 N).filter (fun d => d ∣ (n - 1))).filter (fun d => ¬ (d ∣ (n + 2))) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨hd1, hdN⟩, hdn, hdn1, hdn2⟩, hpred⟩
      have hd3 : 3 ≤ d := three_le_of_not_dvd_of_not_dvd_succ hd1 hdn hdn1
      exact ⟨⟨⟨hd3, hdN⟩, hpred⟩, hdn2⟩
    · rintro ⟨⟨⟨hd3, hdN⟩, hpred⟩, hdn2⟩
      have hboth := not_dvd_and_not_dvd_succ_of_three_le_of_dvd_pred hd3 hn hpred
      exact ⟨⟨⟨by omega, hdN⟩, hboth.1, hboth.2, hdn2⟩, hpred⟩
  rw [hset]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd
  have hd2 : 2 ≤ d := by omega
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  rw [centeredDiscreteSawtooth_of_dvd_pred hd2 hn hd.1.2]
  field_simp [hdR]

/-- **Exact Decomposition of `threeStepBezoutInteriorSawtoothSum` into Second-Layer `n - 1` Peak + Four-Step Interior
(`threeStepBezoutInteriorSawtoothSum_eq_secondLayer_pred_add_fourStep`):**
For every `N, c` and `n ≥ 1`:
`threeStepBezoutInteriorSawtoothSum N c n = secondLayerActiveSawtoothSum N c (n - 1) + fourStepBezoutInteriorSawtoothSum N c n`. -/
theorem threeStepBezoutInteriorSawtoothSum_eq_secondLayer_pred_add_fourStep
    (N : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    threeStepBezoutInteriorSawtoothSum N c n =
      secondLayerActiveSawtoothSum N c (n - 1) +
        fourStepBezoutInteriorSawtoothSum N c n := by
  unfold threeStepBezoutInteriorSawtoothSum fourStepBezoutInteriorSawtoothSum
  have hsplit := (Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)) ∧ ¬ (d ∣ (n + 2))))
    (fun d => d ∣ (n - 1))
    (fun d => c d * centeredDiscreteSawtooth d n)).symm
  have hset :
      ((Finset.Icc 1 N).filter
        (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)) ∧ ¬ (d ∣ (n + 2)))).filter
          (fun d => ¬ (d ∣ (n - 1))) =
      (Finset.Icc 1 N).filter
        (fun d => ¬ (d ∣ (n - 1)) ∧ ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1)) ∧ ¬ (d ∣ (n + 2))) := by
    ext d
    simp only [Finset.mem_filter]
    tauto
  rw [hset, sum_threeStep_dvd_pred_eq_neg_secondLayerActiveSawtoothSum N c hn] at hsplit
  linarith

/-- **Exact Second-Layer (`r = 2`) Bézout Decomposition of `bezoutInteriorSawtoothSum`
(`bezoutInteriorSawtoothSum_eq_secondLayer_pair_add_fourStep`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n ≥ 1`:
`bezoutInteriorSawtoothSum N c n = secondLayerActiveSawtoothSum N c (n - 1) - secondLayerActiveSawtoothSum N c (n + 2) + fourStepBezoutInteriorSawtoothSum N c n`. -/
theorem bezoutInteriorSawtoothSum_eq_secondLayer_pair_add_fourStep
    (N : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    bezoutInteriorSawtoothSum N c n =
      secondLayerActiveSawtoothSum N c (n - 1) -
        secondLayerActiveSawtoothSum N c (n + 2) +
        fourStepBezoutInteriorSawtoothSum N c n := by
  rw [bezoutInteriorSawtoothSum_eq_threeStep_add_two_step_prejump,
    threeStepBezoutInteriorSawtoothSum_eq_secondLayer_pred_add_fourStep N c hn,
    sum_not_dvd_and_dvd_add_two_eq_secondLayerActiveSawtoothSum]
  ring

/-- **Two-Layer Bézout Decomposition of `weightedCenteredSawtoothSum`
(`weightedCenteredSawtoothSum_eq_first_and_second_layer_add_fourStep`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n ≥ 1`, `weightedCenteredSawtoothSum N c n` decomposes into:
1. The First Bézout Layer `{n, n + 1}` (`activeCenteredSawtoothSum N c n n + activeCenteredSawtoothSum N c (n + 1) n`),
2. The Second Bézout Layer `{n - 1, n + 2}` (`secondLayerActiveSawtoothSum N c (n - 1) - secondLayerActiveSawtoothSum N c (n + 2)`),
3. The Four-Step Bézout Interior (`fourStepBezoutInteriorSawtoothSum N c n`). -/
theorem weightedCenteredSawtoothSum_eq_first_and_second_layer_add_fourStep
    (N : ℕ) (c : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    weightedCenteredSawtoothSum N c n =
      (activeCenteredSawtoothSum N c n n + activeCenteredSawtoothSum N c (n + 1) n) +
        (secondLayerActiveSawtoothSum N c (n - 1) -
          secondLayerActiveSawtoothSum N c (n + 2)) +
        fourStepBezoutInteriorSawtoothSum N c n := by
  rw [weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior,
    bezoutInteriorSawtoothSum_eq_secondLayer_pair_add_fourStep N c hn]
  ring

/-- At `m = 1` and `m = 2`, `secondLayerActiveSawtoothSum N c m = 0` because no divisor `d ≥ 3`
can divide `1` or `2`. -/
theorem secondLayerActiveSawtoothSum_eq_zero_of_lt_three
    (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m < 3) :
    secondLayerActiveSawtoothSum N c m = 0 := by
  unfold secondLayerActiveSawtoothSum
  suffices h : (Finset.Icc 3 N).filter (fun d => d ∣ m) = ∅ by
    rw [h, Finset.sum_empty, mul_zero]
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
  intro hd hdm
  have hle : d ≤ m := Nat.le_of_dvd (by omega) hdm
  omega

/-- **Three-Step Telescoping Sum of the Second-Layer Bézout Pair
(`sum_Icc_secondLayer_pair_eq_three_boundary`):**
Because `secondLayerActiveSawtoothSum N c (n - 1) - secondLayerActiveSawtoothSum N c (n + 2)` is a
3-step difference, summing over `1 ≤ n ≤ M` (`M ≥ 2`) cancels all interior terms and leaves only
`secondLayerActiveSawtoothSum N c 0` minus the three terminal values at `M, M + 1, M + 2` (since
the values at `1` and `2` vanish identically). -/
theorem sum_Icc_secondLayer_pair_eq_three_boundary
    (N : ℕ) (c : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M) :
    (∑ n ∈ Finset.Icc 1 M,
      (secondLayerActiveSawtoothSum N c (n - 1) -
        secondLayerActiveSawtoothSum N c (n + 2))) =
      secondLayerActiveSawtoothSum N c 0 -
        (secondLayerActiveSawtoothSum N c M +
          secondLayerActiveSawtoothSum N c (M + 1) +
          secondLayerActiveSawtoothSum N c (M + 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, M = k + 2 := ⟨M - 2, by omega⟩
  induction k with
  | zero =>
    have hIcc : Finset.Icc 1 2 = {1, 2} := by rfl
    rw [hIcc, Finset.sum_pair (by decide)]
    have h1 := secondLayerActiveSawtoothSum_eq_zero_of_lt_three N c (m := 1) (by omega) (by omega)
    have h2 := secondLayerActiveSawtoothSum_eq_zero_of_lt_three N c (m := 2) (by omega) (by omega)
    simp only [Nat.reduceSub, Nat.reduceAdd]
    linarith
  | succ j ih =>
    have hsplit : Finset.Icc 1 (j + 1 + 2) = insert (j + 3) (Finset.Icc 1 (j + 2)) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : j + 3 ∉ Finset.Icc 1 (j + 2) := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hnot, ih (by omega)]
    have hsub : j + 3 - 1 = j + 2 := by omega
    have hadd1 : j + 1 + 2 = j + 3 := by omega
    have hadd2 : j + 1 + 2 + 1 = j + 4 := by omega
    have hadd3 : j + 1 + 2 + 2 = j + 5 := by omega
    have hadd4 : j + 3 + 2 = j + 5 := by omega
    have hadd5 : j + 2 + 1 = j + 3 := by omega
    have hadd6 : j + 2 + 2 = j + 4 := by omega
    rw [hsub, hadd1, hadd2, hadd3, hadd4, hadd5, hadd6]
    ring

end
end GaloisForLFunctions.BezoutValuationIncidence
