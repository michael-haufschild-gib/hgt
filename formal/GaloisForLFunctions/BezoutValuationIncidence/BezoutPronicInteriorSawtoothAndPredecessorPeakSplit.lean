import GaloisForLFunctions.BezoutValuationIncidence.ShiftedExponentSmallDampingCovarianceRateAndActiveDrift

/-!
# Pillar XXIII: Bézout Interior Sawtooth Partition, Predecessor-Peak Telescoping & Centering-Drift Cancellation

In Pillars XVII–XXII, we partitioned the weighted centered sawtooth sum $W_{N,c}(n)$ across step
$n \mapsto n + 1$ into its active pre-jump component `activeCenteredSawtoothSum N c (n + 1) n`
($d \mid (n + 1)$) and its inactive component `inactiveCenteredSawtoothSum N c (n + 1) n`
($d \nmid (n + 1)$).

In this twenty-third pillar of **Bézout–Valuation Incidence Mechanics**, we observe that at step
$n$, the inactive set $\{d \in [1, N] : d \nmid (n + 1)\}$ contains the **just-jumped divisors**
$d \mid n$ ($d \ge 2$), which sit at their **post-jump peak**
$$\operatorname{activeCenteredSawtoothSum}\,N\,c\,n\,n =
  +\frac{1}{2}\bigl(\operatorname{sieveSeq}\,N\,c\,n - \operatorname{sieveSeq}\,N\,(\text{fun } d \Rightarrow c(d)/d)\,n\bigr).$$
Because $\gcd(n, n + 1) = 1$, no divisor $d \ge 2$ can divide both $n$ and $n + 1$, while at $d = 1$
the centered sawtooth $\widetilde{B}_1(1, n) = 0$ vanishes identically!

## Core Main Theorems (100% Unconditional)

1. **Bézout Divisor Disjointness & Exact Three-Way Sawtooth Partition
   (`inactiveCenteredSawtoothSum_eq_predecessor_active_add_bezoutInterior`,
   `weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior`)**:
   For **every** cutoff $N : \mathbb{N}$, weight $c : \mathbb{N} \to \mathbb{R}$, and $n : \mathbb{N}$:
   $$\operatorname{inactiveCenteredSawtoothSum}\,N\,c\,(n + 1)\,n =
     \operatorname{activeCenteredSawtoothSum}\,N\,c\,n\,n +
     \operatorname{bezoutInteriorSawtoothSum}\,N\,c\,n,$$
   $$W_{N,c}(n) =
     \operatorname{activeCenteredSawtoothSum}\,N\,c\,n\,n +
     \operatorname{activeCenteredSawtoothSum}\,N\,c\,(n + 1)\,n +
     \operatorname{bezoutInteriorSawtoothSum}\,N\,c\,n.$$

2. **Exact Forward-Difference (`addDiff`) Form & Telescoping Sum of the Bézout Active Pair
   (`bezout_active_pair_eq_neg_half_addDiff`,
   `sum_Icc_bezout_active_pair_eq_terminal`,
   `sum_Icc_weightedCenteredSawtoothSum_eq_terminal_add_bezoutInterior`)**:
   For every $N : \mathbb{N}$, $c : \mathbb{N} \to \mathbb{R}$, and $n, M : \mathbb{N}$:
   - The combined Bézout active pair is an exact BVI forward difference:
     $$\operatorname{activeCenteredSawtoothSum}\,N\,c\,n\,n +
       \operatorname{activeCenteredSawtoothSum}\,N\,c\,(n + 1)\,n =
       -\frac{1}{2}\,\operatorname{addDiff}\,
         \bigl(\text{fun } k \Rightarrow s_{N,c}(k) - s_{N, c/d}(k)\bigr)\,n.$$
   - Summing over $n \in \operatorname{Icc}\,1\,M$ telescopes every interior peak against its
     predecessor trough, leaving only the terminal pre-jump value at $M + 1$:
     $$\sum_{n=1}^M \bigl(\operatorname{activeCenteredSawtoothSum}\,N\,c\,n\,n +
       \operatorname{activeCenteredSawtoothSum}\,N\,c\,(n + 1)\,n\bigr) =
       \operatorname{activeCenteredSawtoothSum}\,N\,c\,(M + 1)\,M.$$

3. **Horizon-Free Bézout Interior Prefix & Complete Centering-Drift Cancellation for Route PM
   (`pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior`,
   `pmActiveSawtoothComponent_pre_add_post_martingale_eq`)**:
   Pairing the pre-jump active martingale term $\widetilde{\tau}_\varepsilon(m)\,\operatorname{pmActiveSawtoothComponent}\,\varepsilon\,m$
   at step $m - 1 \mapsto m$ with the post-jump active martingale term
   $\widetilde{\tau}_\varepsilon(m + 1)\,\bigl(-\operatorname{pmActiveSawtoothComponent}\,\varepsilon\,m\bigr)$
   at step $m \mapsto m + 1$ **cancels the centering density $(\operatorname{pmPowerDampedDivisorDensity}\,\varepsilon).\text{re}$
   100% identically** and reduces the product $\tau_\varepsilon(m)\,\tau_\varepsilon(m + 1)$ to the
   single pronic coefficient $\tau_\varepsilon(\operatorname{pronicSeq}\,m)$:
   $$\widetilde{\tau}_\varepsilon(m)\,\operatorname{pmActiveSawtoothComponent}\,\varepsilon\,m +
     \widetilde{\tau}_\varepsilon(m + 1)\,\bigl(-\operatorname{pmActiveSawtoothComponent}\,\varepsilon\,m\bigr) =
     -\frac{1}{2}\Bigl(\tau_\varepsilon(m)^2 - \tau_\varepsilon(m)\,\tau_{1+\varepsilon}(m) -
       \tau_\varepsilon(\operatorname{pronicSeq}\,m) + \tau_\varepsilon(m + 1)\,\tau_{1+\varepsilon}(m)\Bigr).$$
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Bézout Divisor Disjointness & Exact Three-Way Sawtooth Partition -/

/-- If `d ∣ n` and `d ∣ (n + 1)`, then `d = 1`. -/
theorem eq_one_of_dvd_and_dvd_succ {d n : ℕ} (hdn : d ∣ n) (hdn1 : d ∣ (n + 1)) :
    d = 1 := by
  have hd_gcd : d ∣ Nat.gcd n (n + 1) := Nat.dvd_gcd hdn hdn1
  have hcop : Nat.Coprime n (n + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n)
  rw [hcop.gcd_eq_one] at hd_gcd
  exact Nat.eq_one_of_dvd_one hd_gcd

/-- At `m = 1`, `activeCenteredSawtoothSum N c 1 k = 0` for all `N, c, k`, because the only
divisor of `1` is `d = 1`, where `centeredDiscreteSawtooth 1 k = 0`. -/
@[simp]
theorem activeCenteredSawtoothSum_one (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    activeCenteredSawtoothSum N c 1 k = 0 := by
  unfold activeCenteredSawtoothSum
  rw [neg_eq_zero]
  refine Finset.sum_eq_zero fun d hd => ?_
  simp only [Finset.mem_filter, Finset.mem_Icc] at hd
  have hd1 : d = 1 := Nat.eq_one_of_dvd_one hd.2
  subst hd1
  simp [centeredDiscreteSawtooth_one]

/-- For every `N : ℕ`, `c : ℕ → ℝ`, and `m : ℕ` (including `m = 0`),
`activeCenteredSawtoothSum N c m m = (1 / 2) * (sieveSeq N c m - sieveSeq N (fun d => c d / d) m)`. -/
theorem activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub_general
    (N : ℕ) (c : ℕ → ℝ) (m : ℕ) :
    activeCenteredSawtoothSum N c m m =
      (1 / 2 : ℝ) *
        (sieveSeq N c m - sieveSeq N (fun d => c d / (d : ℝ)) m) := by
  cases m with
  | zero =>
    unfold activeCenteredSawtoothSum sieveSeq
    have hterm : ∀ d ∈ (Finset.Icc 1 N).filter (fun d : ℕ => d ∣ 0),
        c d * centeredDiscreteSawtooth d 0 =
          -(1 / 2 : ℝ) * (c d - c d / (d : ℝ)) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_Icc] at hd
      have hd_pos : 0 < d := hd.1.1
      have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
      rw [centeredDiscreteSawtooth_of_dvd hd_pos (dvd_zero d)]
      field_simp [hdR]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  | succ n =>
    exact activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c n

/-- **Bézout Interior Sawtooth Sum (`bezoutInteriorSawtoothSum`):**
The weighted centered sawtooth sum at step `n` over all moduli `1 ≤ d ≤ N` that divide **neither**
`n` **nor** `n + 1` (i.e., divisors strictly interior to their sawtooth period across `n ↦ n + 1`). -/
def bezoutInteriorSawtoothSum (N : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  -∑ d ∈ (Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1))),
    c d * centeredDiscreteSawtooth d n

/-- **Decomposition of `inactiveCenteredSawtoothSum` into Predecessor Peak + Bézout Interior
(`inactiveCenteredSawtoothSum_eq_predecessor_active_add_bezoutInterior`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, the inactive sawtooth sum for `n + 1` at `n` splits
into the post-jump active sawtooth sum `activeCenteredSawtoothSum N c n n` of the predecessor `n`
plus the doubly-inactive Bézout interior sum `bezoutInteriorSawtoothSum N c n`. -/
theorem inactiveCenteredSawtoothSum_eq_predecessor_active_add_bezoutInterior
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    inactiveCenteredSawtoothSum N c (n + 1) n =
      activeCenteredSawtoothSum N c n n + bezoutInteriorSawtoothSum N c n := by
  unfold inactiveCenteredSawtoothSum activeCenteredSawtoothSum bezoutInteriorSawtoothSum
  have hsplit_inact := (Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 N).filter (fun d => ¬ (d ∣ (n + 1))))
    (fun d => d ∣ n)
    (fun d => c d * centeredDiscreteSawtooth d n)).symm
  have hsplit_act := (Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 N).filter (fun d => d ∣ n))
    (fun d => d ∣ (n + 1))
    (fun d => c d * centeredDiscreteSawtooth d n)).symm
  have hboth_zero :
      (∑ d ∈ ((Finset.Icc 1 N).filter (fun d => d ∣ n)).filter (fun d => d ∣ (n + 1)),
        c d * centeredDiscreteSawtooth d n) = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    have hd1 : d = 1 := eq_one_of_dvd_and_dvd_succ hd.1.2 hd.2
    subst hd1
    simp [centeredDiscreteSawtooth_one]
  have hset1 :
      ((Finset.Icc 1 N).filter (fun d => ¬ (d ∣ (n + 1)))).filter (fun d => d ∣ n) =
        ((Finset.Icc 1 N).filter (fun d => d ∣ n)).filter (fun d => ¬ (d ∣ (n + 1))) := by
    ext d
    simp only [Finset.mem_filter]
    tauto
  have hset2 :
      ((Finset.Icc 1 N).filter (fun d => ¬ (d ∣ (n + 1)))).filter (fun d => ¬ (d ∣ n)) =
        (Finset.Icc 1 N).filter (fun d => ¬ (d ∣ n) ∧ ¬ (d ∣ (n + 1))) := by
    ext d
    simp only [Finset.mem_filter]
    tauto
  rw [hset1, hset2] at hsplit_inact
  linarith

/-- **Exact Three-Way Bézout Partition of `weightedCenteredSawtoothSum`
(`weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`:
`weightedCenteredSawtoothSum N c n = activeCenteredSawtoothSum N c n n + activeCenteredSawtoothSum N c (n + 1) n + bezoutInteriorSawtoothSum N c n`. -/
theorem weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    weightedCenteredSawtoothSum N c n =
      activeCenteredSawtoothSum N c n n +
        activeCenteredSawtoothSum N c (n + 1) n +
        bezoutInteriorSawtoothSum N c n := by
  rw [weightedCenteredSawtoothSum_eq_active_add_inactive N c (n + 1) n,
    inactiveCenteredSawtoothSum_eq_predecessor_active_add_bezoutInterior]
  ring

/-! ## §2. Exact Forward-Difference (`addDiff`) Form & Telescoping Sum of the Bézout Active Pair -/

/-- **Forward-Difference (`addDiff`) Representation of the Bézout Active Pair
(`bezout_active_pair_eq_neg_half_addDiff`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`, the combined contribution of the post-jump divisors
`d ∣ n` and the pre-jump divisors `d ∣ (n + 1)` at step `n` equals `-1 / 2` times the BVI forward
difference `addDiff` of `k ↦ sieveSeq N c k - sieveSeq N (fun d => c d / d) k`. -/
theorem bezout_active_pair_eq_neg_half_addDiff (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    activeCenteredSawtoothSum N c n n +
      activeCenteredSawtoothSum N c (n + 1) n =
      -(1 / 2 : ℝ) *
        addDiff (fun k => sieveSeq N c k - sieveSeq N (fun d => c d / (d : ℝ)) k) n := by
  rw [activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub_general,
    activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub]
  unfold addDiff
  ring

/-- **Exact Telescoping Sum of the Bézout Active Pair (`sum_Icc_bezout_active_pair_eq_terminal`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `M : ℕ`, summing the Bézout active pair
`activeCenteredSawtoothSum N c n n + activeCenteredSawtoothSum N c (n + 1) n` over `1 ≤ n ≤ M`
cancels every interior pre-jump trough against the next step's post-jump peak, leaving only the
terminal pre-jump value `activeCenteredSawtoothSum N c (M + 1) M`. -/
theorem sum_Icc_bezout_active_pair_eq_terminal (N : ℕ) (c : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M,
      (activeCenteredSawtoothSum N c n n +
        activeCenteredSawtoothSum N c (n + 1) n)) =
      activeCenteredSawtoothSum N c (M + 1) M := by
  induction M with
  | zero =>
    simp
  | succ m ih =>
    have hsplit : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : m + 1 ∉ Finset.Icc 1 m := by
      simp only [Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert hnot, ih]
    have hcancel := activeCenteredSawtoothSum_add_succ_eq_zero N c m
    linarith

/-- **Prefix Sum of `weightedCenteredSawtoothSum` via Bézout Interior + Terminal Active Boundary
(`sum_Icc_weightedCenteredSawtoothSum_eq_terminal_add_bezoutInterior`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `M : ℕ`:
`∑_{n=1}^M weightedCenteredSawtoothSum N c n = activeCenteredSawtoothSum N c (M + 1) M + ∑_{n=1}^M bezoutInteriorSawtoothSum N c n`. -/
theorem sum_Icc_weightedCenteredSawtoothSum_eq_terminal_add_bezoutInterior
    (N : ℕ) (c : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, weightedCenteredSawtoothSum N c n) =
      activeCenteredSawtoothSum N c (M + 1) M +
        ∑ n ∈ Finset.Icc 1 M, bezoutInteriorSawtoothSum N c n := by
  simp_rw [weightedCenteredSawtoothSum_eq_bezout_active_pair_add_interior]
  rw [Finset.sum_add_distrib, sum_Icc_bezout_active_pair_eq_terminal]

/-! ## §3. Horizon-Free Bézout Interior Prefix & Complete Centering-Drift Cancellation for Route PM -/

/-- The **horizon-free Bézout interior residual prefix** of Route PM at step `n`, obtained by
extracting both the pre-jump trough `pmActiveSawtoothComponent ε (n + 1)` at `n + 1` and the
post-jump peak `-pmActiveSawtoothComponent ε n` at `n`:
`pmBezoutInteriorPrefix ε n = pmInactiveResidualPrefix ε n + pmActiveSawtoothComponent ε n`. -/
def pmBezoutInteriorPrefix (ε : ℝ) (n : ℕ) : ℝ :=
  pmInactiveResidualPrefix ε n + pmActiveSawtoothComponent ε n

/-- Decomposition of `pmInactiveResidualPrefix ε n` into the post-jump peak
`-pmActiveSawtoothComponent ε n` of predecessor `n` plus `pmBezoutInteriorPrefix ε n`. -/
theorem pmInactiveResidualPrefix_eq_neg_active_add_bezoutInterior (ε : ℝ) (n : ℕ) :
    pmInactiveResidualPrefix ε n =
      -pmActiveSawtoothComponent ε n + pmBezoutInteriorPrefix ε n := by
  unfold pmBezoutInteriorPrefix
  ring

/-- **Horizon-Free Bézout Active-Pair + Interior Decomposition of `pmPowerDampedCenteredDivisorPrefix`
(`pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior`):**
For every `ε : ℝ` and `n : ℕ`:
`pmPowerDampedCenteredDivisorPrefix ε n = addDiff (pmActiveSawtoothComponent ε) n + pmBezoutInteriorPrefix ε n`. -/
theorem pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior
    (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n =
      addDiff (pmActiveSawtoothComponent ε) n + pmBezoutInteriorPrefix ε n := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq_active_add_inactive,
    pmInactiveResidualPrefix_eq_neg_active_add_bezoutInterior]
  unfold addDiff
  ring

/-- **Complete Centering-Drift Cancellation & Pronic Reduction of Paired Pre/Post-Jump Active Terms
(`pmActiveSawtoothComponent_pre_add_post_martingale_eq`):**
For every `ε : ℝ` and `m : ℕ`, pairing the pre-jump active martingale product
`pmPowerDampedCenteredDivisorCoeff ε m * pmActiveSawtoothComponent ε m` (at step `m - 1 ↦ m`) with
the post-jump active martingale product
`pmPowerDampedCenteredDivisorCoeff ε (m + 1) * (-pmActiveSawtoothComponent ε m)` (at step `m ↦ m + 1`)
**cancels the centering density `(pmPowerDampedDivisorDensity ε).re` 100% identically** and reduces
the product `τ_ε(m) * τ_ε(m + 1)` to the single pronic coefficient `τ_ε(pronicSeq m)`:
`widetilde_τ_ε(m) * A_ε(m) + widetilde_τ_ε(m + 1) * (-A_ε(m)) = -(1 / 2) * (τ_ε(m)² - τ_ε(m) * τ_{1+ε}(m) - τ_ε(pronicSeq m) + τ_ε(m + 1) * τ_{1+ε}(m))`. -/
theorem pmActiveSawtoothComponent_pre_add_post_martingale_eq (ε : ℝ) (m : ℕ) :
    pmPowerDampedCenteredDivisorCoeff ε m * pmActiveSawtoothComponent ε m +
      pmPowerDampedCenteredDivisorCoeff ε (m + 1) * (-pmActiveSawtoothComponent ε m) =
      -(1 / 2 : ℝ) *
        (pmPowerDampedDivisorCoeff ε m ^ (2 : ℕ) -
          pmPowerDampedDivisorCoeff ε m * pmPowerDampedDivisorCoeff (1 + ε) m -
          pmPowerDampedDivisorCoeff ε (pronicSeq m) +
          pmPowerDampedDivisorCoeff ε (m + 1) * pmPowerDampedDivisorCoeff (1 + ε) m) := by
  rw [← pmPowerDampedDivisorCoeff_mul_succ_eq_pronicSeq ε m]
  unfold pmPowerDampedCenteredDivisorCoeff pmActiveSawtoothComponent
  ring

end
end GaloisForLFunctions.BezoutValuationIncidence
