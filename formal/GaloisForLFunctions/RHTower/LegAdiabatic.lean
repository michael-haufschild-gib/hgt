/-
# LegAdiabatic — the exact step ledger for a NON-constant gap field, and its march

`LegLatticeStep`/`LegComparison` treat the constant-step lattice. Here the poles carry
arbitrary gaps. The constraint field of a unit charge sitting between two poles at signed
distance `s` from its nearest AHEAD pole is

`G = Σ (coth of half the distance to each behind pole) − Σ (coth of half the distance to each
ahead pole)`,

and its equilibria are the roots `G = −(total charge)`. The march question is whether the
equilibrium distance decreases from one gap to the next, i.e. whether `ΔG > 0` where `ΔG` is
the field of the next gap minus the field of the current gap, both read at the SAME `s`.

The geometric fact that makes the comparison exact: advancing the charge by exactly the
swapped gap `δ` leaves its distance to the (new) ahead pole equal to `s`, moves every behind
pole `δ` farther and every ahead pole `δ` nearer, and turns the old nearest-ahead pole (at
distance `s`) into the new nearest-behind pole (at distance `δ − s`) while the old
second-ahead pole (at distance `δ + s`) becomes the new nearest-ahead pole (at distance `s`).
The two `coth(s/2)` terms cancel and the difference collapses to two swap extras plus one
`coth`-increment per spectator pole:

* `legFieldOld`, `legFieldNew` — the two consecutive fields, built from the same pole data
  (behind spectator distances `c m`, ahead spectator distances `e r`, swapped gap `δ`,
  ahead distance `s`).
* `adiabatic_ledger` — **the exact identity**
  `ΔG = coth((δ−s)/2) + coth((δ+s)/2) + Σ_m [coth((c m + δ)/2) − coth(c m/2)]
        + Σ_r [coth(e r/2) − coth((e r − δ)/2)]` — finite sums, no approximation.
* `swap_cushion_gt_two` — the two swap extras exceed `2` (each is `coth` of a positive
  argument), the constant-lattice cushion recovered.
* `behind_drift_abs_le`, `ahead_drift_abs_le` — each spectator increment has magnitude at
  most `(δ/2)·csch²(nearer distance/2)` (the mean value theorem for `coth`, `coth' = −csch²`).
* `adiabatic_march_pos` — **the closing**: if the total spectator drift, bounded by the sum
  of those `csch²` weights, stays below the swap cushion, then `ΔG > 0`. No cancellation of
  signs is used; every spectator term is charged at full magnitude against the cushion.
-/
import GaloisForLFunctions.RHTower.AdiabaticLedger
import GaloisForLFunctions.RHTower.LegWindow

noncomputable section

namespace RHTower

open Finset

/-- The constraint field of the charge in the CURRENT gap, read at ahead-distance `s`.
Behind spectator poles are at distances `c 0, …, c (L−1)`; the nearest ahead pole is at `s`;
the next ahead pole (the one about to be swapped) is at `δ + s`; the remaining ahead spectator
poles are at `e 0, …, e (R−1)`. Behind poles contribute `+coth`, ahead poles `−coth`. -/
def legFieldOld (L R : ℕ) (c e : ℕ → ℝ) (δ s : ℝ) : ℝ :=
  (∑ m ∈ range L, rcoth (c m / 2)) - rcoth (s / 2) - rcoth ((δ + s) / 2)
    - (∑ r ∈ range R, rcoth (e r / 2))

/-- The constraint field of the charge one gap ONWARD — advanced by exactly the swapped gap
`δ`, still at ahead-distance `s`. Each behind spectator distance grows to `c m + δ`; the old
nearest-ahead pole is now the nearest behind pole at distance `δ − s`; the swapped pole is now
the nearest ahead pole at distance `s`; each ahead spectator distance shrinks to `e r − δ`. -/
def legFieldNew (L R : ℕ) (c e : ℕ → ℝ) (δ s : ℝ) : ℝ :=
  (∑ m ∈ range L, rcoth ((c m + δ) / 2)) + rcoth ((δ - s) / 2) - rcoth (s / 2)
    - (∑ r ∈ range R, rcoth ((e r - δ) / 2))

/-- **The exact step ledger** (doc-free, self-contained): the next-gap field minus the
current-gap field equals two swap extras `coth((δ−s)/2) + coth((δ+s)/2)` plus, for every
spectator pole, a single `coth`-increment. The `coth(s/2)` of the nearest ahead pole cancels
between the two fields; behind spectators drift outward by `δ`, ahead spectators inward by
`δ`. Pure finite-sum rearrangement. -/
theorem adiabatic_ledger (L R : ℕ) (c e : ℕ → ℝ) (δ s : ℝ) :
    legFieldNew L R c e δ s - legFieldOld L R c e δ s
      = rcoth ((δ - s) / 2) + rcoth ((δ + s) / 2)
        + (∑ m ∈ range L, (rcoth ((c m + δ) / 2) - rcoth (c m / 2)))
        + (∑ r ∈ range R, (rcoth (e r / 2) - rcoth ((e r - δ) / 2))) := by
  have hB : (∑ m ∈ range L, (rcoth ((c m + δ) / 2) - rcoth (c m / 2)))
      = (∑ m ∈ range L, rcoth ((c m + δ) / 2)) - (∑ m ∈ range L, rcoth (c m / 2)) := by
    rw [Finset.sum_sub_distrib]
  have hA : (∑ r ∈ range R, (rcoth (e r / 2) - rcoth ((e r - δ) / 2)))
      = (∑ r ∈ range R, rcoth (e r / 2)) - (∑ r ∈ range R, rcoth ((e r - δ) / 2)) := by
    rw [Finset.sum_sub_distrib]
  rw [hB, hA]
  simp only [legFieldNew, legFieldOld]
  ring

/-- **The swap cushion exceeds `2`**: for `0 < s < δ` the two swap extras `coth((δ−s)/2)` and
`coth((δ+s)/2)` are each `coth` of a positive argument, hence each `> 1`. -/
theorem swap_cushion_gt_two {δ s : ℝ} (hs : 0 < s) (hsδ : s < δ) :
    2 < rcoth ((δ - s) / 2) + rcoth ((δ + s) / 2) :=
  rcoth_add_gt_two (by linarith) (by linarith)

/-- **Behind spectator drift bound**: outward drift of a behind pole from `c` to `c + δ`
lowers its `coth` by at most `(δ/2)·csch²(c/2)` — the mean value theorem for `coth` (with
`coth' = −csch²`) at the nearer endpoint `c/2`. -/
theorem behind_drift_abs_le {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    rcoth (c / 2) - rcoth ((c + δ) / 2) ≤ (δ / 2) * (rcsch (c / 2)) ^ (2 : ℕ) := by
  have h := rcoth_pair_le (a := c / 2) (b := (c + δ) / 2) (by positivity) (by linarith)
  have hbma : ((c + δ) / 2 - c / 2) = δ / 2 := by ring
  rw [hbma] at h
  exact h

/-- **Ahead spectator drift bound**: inward drift of an ahead pole from `e` to `e − δ` (with
`e > δ`) raises its `coth` by at most `(δ/2)·csch²((e−δ)/2)` — the mean value theorem for
`coth` at the nearer endpoint `(e−δ)/2`. -/
theorem ahead_drift_abs_le {e δ : ℝ} (hδ : 0 < δ) (heδ : δ < e) :
    rcoth ((e - δ) / 2) - rcoth (e / 2) ≤ (δ / 2) * (rcsch ((e - δ) / 2)) ^ (2 : ℕ) := by
  have h := rcoth_pair_le (a := (e - δ) / 2) (b := e / 2) (by linarith) (by linarith)
  have hbma : (e / 2 - (e - δ) / 2) = δ / 2 := by ring
  rw [hbma] at h
  exact h

/-- **The no-cancellation march bound**: if the total spectator drift — bounded, term by term,
by the `csch²` weights of `behind_drift_abs_le`/`ahead_drift_abs_le` — stays strictly below the
near swap cushion `coth((δ−s)/2) + coth((δ+s)/2)`, then `ΔG > 0`. Charges every spectator at
full magnitude, no sign cancellation. The hypothesis is TIGHT and fails once `s` leaves a
neighbourhood of `0`: in the pole pairing each behind spectator's distance grows by the full
gap `δ`, so the nearest term `(δ/2)csch²(c₀/2)` alone is of the same order as the cushion. The
decomposition that clears with room is the rank pairing below (`rank_march_pos`), where the
drift increments are gap DIFFERENCES (zero on the constant lattice) against a far cushion. -/
theorem adiabatic_march_pos {L R : ℕ} {c e : ℕ → ℝ} {δ s : ℝ}
    (hs : 0 < s) (hsδ : s < δ)
    (hc : ∀ m ∈ range L, 0 < c m) (he : ∀ r ∈ range R, δ < e r)
    (hcrude : (∑ m ∈ range L, (δ / 2) * (rcsch (c m / 2)) ^ (2 : ℕ))
        + (∑ r ∈ range R, (δ / 2) * (rcsch ((e r - δ) / 2)) ^ (2 : ℕ))
        < rcoth ((δ - s) / 2) + rcoth ((δ + s) / 2)) :
    0 < legFieldNew L R c e δ s - legFieldOld L R c e δ s := by
  have hδ : 0 < δ := lt_trans hs hsδ
  set cushion : ℝ := rcoth ((δ - s) / 2) + rcoth ((δ + s) / 2) with hcush
  set BSum : ℝ := ∑ m ∈ range L, (rcoth ((c m + δ) / 2) - rcoth (c m / 2)) with hBSum
  set ASum : ℝ := ∑ r ∈ range R, (rcoth (e r / 2) - rcoth ((e r - δ) / 2)) with hASum
  -- the ledger: ΔG = cushion + (BSum + ASum)
  have hledger : legFieldNew L R c e δ s - legFieldOld L R c e δ s = cushion + (BSum + ASum) := by
    rw [adiabatic_ledger, hcush, hBSum, hASum]; ring
  -- every spectator term is a loss: BSum ≤ 0, ASum ≤ 0
  have hBneg : BSum ≤ 0 := by
    rw [hBSum]
    apply Finset.sum_nonpos
    intro m hm
    have hcm := hc m hm
    have := rcoth_strictAntiOn_pos.antitoneOn (Set.mem_Ioi.mpr (by positivity : (0:ℝ) < c m / 2))
      (Set.mem_Ioi.mpr (by positivity : (0:ℝ) < (c m + δ) / 2)) (by linarith)
    linarith
  have hAneg : ASum ≤ 0 := by
    rw [hASum]
    apply Finset.sum_nonpos
    intro r hr
    have her := he r hr
    have := rcoth_strictAntiOn_pos.antitoneOn
      (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < (e r - δ) / 2))
      (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < e r / 2)) (by linarith)
    linarith
  -- the total loss magnitude is below the cushion
  have hBmag : -BSum ≤ ∑ m ∈ range L, (δ / 2) * (rcsch (c m / 2)) ^ (2 : ℕ) := by
    rw [hBSum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro m hm
    have := behind_drift_abs_le (hc m hm) hδ
    linarith
  have hAmag : -ASum ≤ ∑ r ∈ range R, (δ / 2) * (rcsch ((e r - δ) / 2)) ^ (2 : ℕ) := by
    rw [hASum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro r hr
    have := ahead_drift_abs_le hδ (he r hr)
    linarith
  have hcushpos : 0 < cushion := by
    have := swap_cushion_gt_two hs hsδ; rw [hcush]; linarith
  -- |BSum + ASum| < cushion, then adb_crude_suffices
  have hbound : |BSum + ASum| < cushion := by
    rw [abs_lt]
    constructor
    · have : -BSum + -ASum ≤ (∑ m ∈ range L, (δ / 2) * (rcsch (c m / 2)) ^ (2 : ℕ))
          + (∑ r ∈ range R, (δ / 2) * (rcsch ((e r - δ) / 2)) ^ (2 : ℕ)) := by linarith [hBmag, hAmag]
      linarith [hcrude, this]
    · linarith [hBneg, hAneg, hcushpos]
  rw [hledger]
  exact adb_crude_suffices hbound

/-!
### The rank pairing: gap-difference increments against a far cushion

The pole pairing above charges each spectator with the full gap `δ`, so its crude bound is
tight. Pairing instead by RANK — the `k`-th nearest behind pole of one gap against the `k`-th
nearest of the next — makes each increment a gap DIFFERENCE and leaves the two FAR poles (the
one that enters behind and the one that leaves ahead) as the cushion. On the constant lattice
every gap difference is zero, so `ΔG` equals the far cushion `> 2` outright; a non-constant
field perturbs the far cushion by the signed drift, which the (ADB) hypothesis controls.
-/

/-- Rank field of the CURRENT gap: behind rank distances `oldB k`, the shared nearest-ahead at
`s`, ahead rank distances `oldA k`, and the far-ahead pole this gap carries (at `fA`) which the
next gap has swapped out. -/
def legRankOld (L R : ℕ) (oldB oldA : ℕ → ℝ) (s fA : ℝ) : ℝ :=
  (∑ k ∈ range L, rcoth (oldB k / 2)) - rcoth (s / 2)
    - (∑ k ∈ range R, rcoth (oldA k / 2)) - rcoth (fA / 2)

/-- Rank field of the NEXT gap: behind rank distances `newB k`, the far-behind pole newly
entered (at `fB`), the shared nearest-ahead at `s`, ahead rank distances `newA k`. -/
def legRankNew (L R : ℕ) (newB newA : ℕ → ℝ) (s fB : ℝ) : ℝ :=
  (∑ k ∈ range L, rcoth (newB k / 2)) + rcoth (fB / 2) - rcoth (s / 2)
    - (∑ k ∈ range R, rcoth (newA k / 2))

/-- **The rank step ledger**: the next-gap field minus the current-gap field equals the two far
swap extras `coth(fB/2) + coth(fA/2)` plus one `coth`-increment per matched rank. The nearest
ahead pole (distance `s`) is shared and cancels. Pure finite-sum rearrangement. -/
theorem adiabatic_ledger_rank (L R : ℕ) (oldB oldA newB newA : ℕ → ℝ) (s fA fB : ℝ) :
    legRankNew L R newB newA s fB - legRankOld L R oldB oldA s fA
      = rcoth (fB / 2) + rcoth (fA / 2)
        + (∑ k ∈ range L, (rcoth (newB k / 2) - rcoth (oldB k / 2)))
        + (∑ k ∈ range R, (rcoth (oldA k / 2) - rcoth (newA k / 2))) := by
  have hB : (∑ k ∈ range L, (rcoth (newB k / 2) - rcoth (oldB k / 2)))
      = (∑ k ∈ range L, rcoth (newB k / 2)) - (∑ k ∈ range L, rcoth (oldB k / 2)) := by
    rw [Finset.sum_sub_distrib]
  have hA : (∑ k ∈ range R, (rcoth (oldA k / 2) - rcoth (newA k / 2)))
      = (∑ k ∈ range R, rcoth (oldA k / 2)) - (∑ k ∈ range R, rcoth (newA k / 2)) := by
    rw [Finset.sum_sub_distrib]
  rw [hB, hA]
  simp only [legRankNew, legRankOld]
  ring

/-- **The far cushion exceeds `2`**: the two far swap poles at positive distances `fA`, `fB`
each give `coth > 1`. Unlike the near cushion this is the ONLY unconditional input the rank
march needs. -/
theorem far_cushion_gt_two {fA fB : ℝ} (hA : 0 < fA) (hB : 0 < fB) :
    2 < rcoth (fB / 2) + rcoth (fA / 2) :=
  rcoth_add_gt_two (by positivity) (by positivity)

/-- **A behind rank increment is a gain when its gap difference is nonpositive**: if the next
gap's `k`-th behind distance does not exceed the current gap's (`0 < newBk ≤ oldBk`, i.e. the
outward gap did not grow), then `coth(newBk/2) − coth(oldBk/2) ≥ 0`. -/
theorem behind_gain_nonneg {newBk oldBk : ℝ} (hnew : 0 < newBk) (hle : newBk ≤ oldBk) :
    0 ≤ rcoth (newBk / 2) - rcoth (oldBk / 2) :=
  driftBehind_nonneg (by positivity) (by linarith)

/-- **An ahead rank increment is a loss when its gap difference is nonpositive**: if
`0 < newAk ≤ oldAk`, then `coth(oldAk/2) − coth(newAk/2) ≤ 0`. -/
theorem ahead_loss_nonpos {newAk oldAk : ℝ} (hnew : 0 < newAk) (hle : newAk ≤ oldAk) :
    rcoth (oldAk / 2) - rcoth (newAk / 2) ≤ 0 :=
  driftAhead_nonpos (by positivity) (by linarith)

/-- **The rank march clears with room under (ADB)**: whenever the net spectator drift is
nonnegative — the total behind gain at least offsetting the total ahead loss — the next-gap
field exceeds the current one by MORE than the full far cushion, `ΔG > 2`. The far cushion `> 2`
is unconditional; the net-drift hypothesis is the genuine (ADB) inequality, trivially satisfied
on the constant lattice (all increments zero) and, on a monotone-gap field, the statement that
the behind gains dominate the ahead losses. No spectator is double-counted; the far cushion is
never consumed. -/
theorem rank_march_pos {L R : ℕ} {oldB oldA newB newA : ℕ → ℝ} {s fA fB : ℝ}
    (hA : 0 < fA) (hB : 0 < fB)
    (hADB : 0 ≤ (∑ k ∈ range L, (rcoth (newB k / 2) - rcoth (oldB k / 2)))
        + (∑ k ∈ range R, (rcoth (oldA k / 2) - rcoth (newA k / 2)))) :
    2 < legRankNew L R newB newA s fB - legRankOld L R oldB oldA s fA := by
  rw [adiabatic_ledger_rank]
  have hcush := far_cushion_gt_two hA hB
  linarith [hADB, hcush]

/-- **The rank march stays positive when the loss falls short of the cushion** — the certificate
that survives where `rank_march_pos` dies. The march needs only `ΔG > 0`, not `ΔG > 2`; from the
ledger `ΔG = cushion + gains − loss` with the behind gains nonnegative, `ΔG > 0` follows the
instant the total ahead loss is below the far cushion, EVEN when it exceeds the gains (net drift
negative, so `rank_march_pos` is inapplicable). As the gap scale grows the ahead losses collapse
— the ahead poles recede — while the cushion stays above `2`, so this bound closes the sparse,
wide-gap regime that the net-drift bound cannot. -/
theorem rank_march_pos_weak {L R : ℕ} {oldB oldA newB newA : ℕ → ℝ} {s fA fB : ℝ}
    (hgain : 0 ≤ ∑ k ∈ range L, (rcoth (newB k / 2) - rcoth (oldB k / 2)))
    (hloss : (∑ k ∈ range R, (rcoth (newA k / 2) - rcoth (oldA k / 2)))
        < rcoth (fB / 2) + rcoth (fA / 2)) :
    0 < legRankNew L R newB newA s fB - legRankOld L R oldB oldA s fA := by
  rw [adiabatic_ledger_rank]
  have hswap : (∑ k ∈ range R, (rcoth (oldA k / 2) - rcoth (newA k / 2)))
      = -(∑ k ∈ range R, (rcoth (newA k / 2) - rcoth (oldA k / 2))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hswap]
  linarith [hgain, hloss]

/-- **The section march stays positive from signs and a loss-below-cushion bound**: the behind
inward-drift signs make the gains nonnegative, and if the total ahead loss is below the far
cushion then `ΔG > 0`. No outer-half count, no per-rank domination, no interval-position
condition — only the behind signs and one summed loss bound. This is the certificate for the
wide-gap sparse regime, where the net drift genuinely turns negative but the receding ahead
poles make the loss negligible against the cushion. -/
theorem section_march_pos_weak {L R : ℕ} {oldB oldA newB newA : ℕ → ℝ} {s fA fB : ℝ}
    (hsignB : ∀ k ∈ range L, 0 < newB k ∧ newB k ≤ oldB k)
    (hloss : (∑ k ∈ range R, (rcoth (newA k / 2) - rcoth (oldA k / 2)))
        < rcoth (fB / 2) + rcoth (fA / 2)) :
    0 < legRankNew L R newB newA s fB - legRankOld L R oldB oldA s fA := by
  refine rank_march_pos_weak (Finset.sum_nonneg (fun k hk => ?_)) hloss
  obtain ⟨hnB, hBle⟩ := hsignB k hk
  exact behind_gain_nonneg hnB hBle

/-- **The rank march stays positive from a gain floor against a raised budget**: if the behind
gains total at least `γ` and the ahead losses stay strictly below `2 + γ`, then `ΔG > 0`. The
far cushion contributes its unconditional `2`, and the gain floor raises the admissible loss
budget above it. The two pure certificates are endpoints: `γ = 0` is the loss-below-cushion
bound, while a loss below the gains alone is the nonnegative-net-drift bound. The interior is
what a configuration with a strong near-behind pair but non-negligible ahead losses needs. -/
theorem rank_march_pos_of_gain_loss {L R : ℕ} {oldB oldA newB newA : ℕ → ℝ}
    {s fA fB γ : ℝ} (hA : 0 < fA) (hB : 0 < fB)
    (hgain : γ ≤ ∑ k ∈ range L, (rcoth (newB k / 2) - rcoth (oldB k / 2)))
    (hloss : (∑ k ∈ range R, (rcoth (newA k / 2) - rcoth (oldA k / 2))) < 2 + γ) :
    0 < legRankNew L R newB newA s fB - legRankOld L R oldB oldA s fA := by
  rw [adiabatic_ledger_rank]
  have hcush := far_cushion_gt_two hA hB
  have hswap : (∑ k ∈ range R, (rcoth (oldA k / 2) - rcoth (newA k / 2)))
      = -(∑ k ∈ range R, (rcoth (newA k / 2) - rcoth (oldA k / 2))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hswap]
  linarith [hgain, hloss, hcush]

/-!
### Discharging (ADB): the net drift is nonnegative for a section gap field

The `hADB` hypothesis of `rank_march_pos` — behind gains offset ahead losses — is reduced here
to three elementary per-rank facts about the gap sequence, no `coth` left in the criterion:

* signs (gaps decreasing outward): every behind rank drifts inward (a gain), every ahead rank
  drifts inward (a loss);
* the midpoint-push places the behind interval to the LEFT of the ahead interval at each rank
  (`oldB ≤ newA`), so `csch²` is uniformly larger on the behind side;
* gap convexity makes the behind increment WIDER than the ahead increment at each rank
  (`oldA − newA ≤ oldB − newB`).

Under these, the `k`-th behind gain dominates the `k`-th ahead loss; the extra behind ranks of
the outer half (`R ≤ L`) are gains with no ahead partner. Sum: net drift `≥ 0`.
-/

/-- **`coth` mean value LOWER bound**: for `0 < a < b`, `(b − a)·csch²(b) ≤ coth(a) − coth(b)` —
the mean value theorem for `coth` (`coth′ = −csch²`) evaluated at the FARTHER endpoint `b`,
where `csch²` is smallest. Companion to `rcoth_pair_le`'s upper bound at the nearer endpoint. -/
theorem rcoth_pair_ge {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (b - a) * (rcsch b) ^ (2 : ℕ) ≤ rcoth a - rcoth b := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hcont : ContinuousOn rcoth (Set.Icc a b) := fun y hy =>
    (rcoth_hasDerivAt (lt_of_lt_of_le ha hy.1).ne').continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope rcoth
    (fun y => -(rcsch y) ^ (2 : ℕ)) hab hcont (fun y hy => rcoth_hasDerivAt (lt_trans ha hy.1).ne')
  have hc0 : 0 < c := lt_trans ha hc.1
  rw [eq_div_iff hba.ne'] at hslope
  have hkey : rcoth a - rcoth b = (b - a) * (rcsch c) ^ (2 : ℕ) := by linear_combination hslope
  rw [hkey]
  have hcsch : (rcsch b) ^ (2 : ℕ) ≤ (rcsch c) ^ (2 : ℕ) := by
    have h1 : rcsch b ≤ rcsch c :=
      (rcsch_strictAntiOn_pos (Set.mem_Ioi.mpr hc0)
        (Set.mem_Ioi.mpr (lt_trans hc0 hc.2)) hc.2).le
    exact pow_le_pow_left₀ (rcsch_pos_of_pos (lt_trans hc0 hc.2)).le h1 2
  exact mul_le_mul_of_nonneg_left hcsch hba.le

/-- Non-strict form of `rcoth_pair_ge` (equality gives `0 ≤ 0`). -/
theorem rcoth_pair_ge' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * (rcsch b) ^ (2 : ℕ) ≤ rcoth a - rcoth b := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  · exact rcoth_pair_ge ha h

/-- Non-strict form of `rcoth_pair_le` (equality gives `0 ≤ 0`). -/
theorem rcoth_pair_le' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    rcoth a - rcoth b ≤ (b - a) * (rcsch a) ^ (2 : ℕ) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  · exact rcoth_pair_le ha h

/-- **Rank domination**: the behind gain at a rank is at least the ahead loss at the same rank,
given the three structural facts — inward drift on both sides (`newB ≤ oldB`, `newA ≤ oldA`),
the behind interval to the left (`oldB ≤ newA`, midpoint-push), and the behind increment wider
(`oldA − newA ≤ oldB − newB`, convexity). Proof: bound the gain below by
`(widthB/2)·csch²(oldB/2)` and the loss above by `(widthA/2)·csch²(newA/2)`, then the wider,
`csch²`-heavier behind box dominates. -/
theorem rank_pair_domination {oldB oldA newB newA : ℝ}
    (hnB : 0 < newB) (hBle : newB ≤ oldB)
    (hnA : 0 < newA) (hAle : newA ≤ oldA)
    (hdist : oldB ≤ newA) (hwidth : oldA - newA ≤ oldB - newB) :
    rcoth (newA / 2) - rcoth (oldA / 2) ≤ rcoth (newB / 2) - rcoth (oldB / 2) := by
  have hnB2 : (0 : ℝ) < newB / 2 := by linarith
  have hnA2 : (0 : ℝ) < newA / 2 := by linarith
  have hoB2 : (0 : ℝ) < oldB / 2 := by linarith
  have hgain : (oldB / 2 - newB / 2) * (rcsch (oldB / 2)) ^ (2 : ℕ)
      ≤ rcoth (newB / 2) - rcoth (oldB / 2) := rcoth_pair_ge' hnB2 (by linarith)
  have hloss : rcoth (newA / 2) - rcoth (oldA / 2)
      ≤ (oldA / 2 - newA / 2) * (rcsch (newA / 2)) ^ (2 : ℕ) := rcoth_pair_le' hnA2 (by linarith)
  have hcschcmp : (rcsch (newA / 2)) ^ (2 : ℕ) ≤ (rcsch (oldB / 2)) ^ (2 : ℕ) := by
    have h1 : rcsch (newA / 2) ≤ rcsch (oldB / 2) :=
      (rcsch_strictAntiOn_pos.antitoneOn (Set.mem_Ioi.mpr hoB2)
        (Set.mem_Ioi.mpr hnA2) (by linarith))
    exact pow_le_pow_left₀ (rcsch_pos_of_pos hnA2).le h1 2
  have hmid : (oldA / 2 - newA / 2) * (rcsch (newA / 2)) ^ (2 : ℕ)
      ≤ (oldB / 2 - newB / 2) * (rcsch (oldB / 2)) ^ (2 : ℕ) :=
    mul_le_mul (by linarith) hcschcmp (sq_nonneg _) (by linarith)
  linarith [hgain, hloss, hmid]

/-- **The net drift is nonnegative** — the (ADB) hypothesis of `rank_march_pos`, discharged.
`R ≤ L` (outer half), every behind rank a gain (`hgain`), and rank domination on the paired
ranks (`hdom`): the ahead losses `Σ_{k<R}` are dominated by the behind gains `Σ_{k<R}`, and the
surplus behind gains `Σ_{R≤k<L}` are nonnegative. -/
theorem net_drift_nonneg {L R : ℕ} {oldB oldA newB newA : ℕ → ℝ} (hRL : R ≤ L)
    (hgain : ∀ k ∈ range L, 0 ≤ rcoth (newB k / 2) - rcoth (oldB k / 2))
    (hdom : ∀ k ∈ range R,
        rcoth (newA k / 2) - rcoth (oldA k / 2) ≤ rcoth (newB k / 2) - rcoth (oldB k / 2)) :
    0 ≤ (∑ k ∈ range L, (rcoth (newB k / 2) - rcoth (oldB k / 2)))
        + (∑ k ∈ range R, (rcoth (oldA k / 2) - rcoth (newA k / 2))) := by
  have hahead : (∑ k ∈ range R, (rcoth (oldA k / 2) - rcoth (newA k / 2)))
      = -(∑ k ∈ range R, (rcoth (newA k / 2) - rcoth (oldA k / 2))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hahead]
  have h1 : (∑ k ∈ range R, (rcoth (newA k / 2) - rcoth (oldA k / 2)))
      ≤ ∑ k ∈ range R, (rcoth (newB k / 2) - rcoth (oldB k / 2)) := Finset.sum_le_sum hdom
  have h2 : (∑ k ∈ range R, (rcoth (newB k / 2) - rcoth (oldB k / 2)))
      ≤ ∑ k ∈ range L, (rcoth (newB k / 2) - rcoth (oldB k / 2)) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hRL))
      (fun k hk _ => hgain k hk)
  linarith [h1, h2]

/-- **The section march clears, from raw gap geometry**: the next-gap constraint field exceeds
the current one by more than the far cushion (`ΔG > 2`) whenever the gap field is one that
decreases outward with convex increments under the midpoint-push. The transcendental (ADB)
inequality is gone: only the far poles' positivity (`fA, fB > 0`), the outer-half count
(`R ≤ L`), the per-rank inward-drift signs, the midpoint-push (`oldB ≤ newA`), and the
convexity width bound (`oldA − newA ≤ oldB − newB`) remain — all elementary facts about the
distances, verified directly on any concrete section gap sequence. -/
theorem section_march_pos {L R : ℕ} {oldB oldA newB newA : ℕ → ℝ} {s fA fB : ℝ}
    (hA : 0 < fA) (hB : 0 < fB) (hRL : R ≤ L)
    (hsignB : ∀ k ∈ range L, 0 < newB k ∧ newB k ≤ oldB k)
    (hrank : ∀ k ∈ range R, 0 < newA k ∧ newA k ≤ oldA k ∧ oldB k ≤ newA k
        ∧ oldA k - newA k ≤ oldB k - newB k) :
    2 < legRankNew L R newB newA s fB - legRankOld L R oldB oldA s fA := by
  refine rank_march_pos hA hB (net_drift_nonneg hRL ?_ ?_)
  · intro k hk
    obtain ⟨hnB, hBle⟩ := hsignB k hk
    exact behind_gain_nonneg hnB hBle
  · intro k hk
    obtain ⟨hnA, hAle, hdist, hwidth⟩ := hrank k hk
    obtain ⟨hnB, hBle⟩ := hsignB k (Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hk) hRL))
    exact rank_pair_domination hnB hBle hnA hAle hdist hwidth

/-!
### The bulk regime: a single summed `csch²` box comparison

Deep ranks violate the interval-position condition `oldB ≤ newA` of `rank_pair_domination`:
the cumulated behind window overtakes the ahead window, placing the behind increment at larger
distances with lighter `csch²` weight, and the per-rank comparison can genuinely fail there.
What survives is the comparison of TOTALS. Boxing every gain below by
`(width/2)·csch²(far endpoint)` and every loss above by `(width/2)·csch²(near endpoint)` turns
the net drift into a difference of two `csch²`-weighted width sums, and the net drift is
nonnegative as soon as the ahead box sum does not exceed the behind box sum. A charge pushed
toward the midpoint of its gap shortens the nearest behind distances to `δ − s` while
lengthening the nearest ahead ones to `δ + s`; since the weight is inverse-quadratic in the
distance, the nearest behind boxes outweigh the nearest ahead boxes severalfold, and this
near-rank surplus is what absorbs every deep-rank deficit.
-/

/-- **The summed `csch²` box comparison discharges (ADB)**: bound each behind gain below by its
mean value box `((oldB−newB)/2)·csch²(oldB/2)` (the `csch²` slope at the FAR endpoint) and each
ahead loss above by `((oldA−newA)/2)·csch²(newA/2)` (the slope at the NEAR endpoint). If the
ahead box sum is at most the behind box sum over the paired ranks, the net drift is
nonnegative. No per-rank comparison is required: individual ranks may lose, only the totals
compare. -/
theorem net_drift_nonneg_csch {L R : ℕ} {oldB oldA newB newA : ℕ → ℝ} (hRL : R ≤ L)
    (hsignB : ∀ k ∈ range L, 0 < newB k ∧ newB k ≤ oldB k)
    (hsignA : ∀ k ∈ range R, 0 < newA k ∧ newA k ≤ oldA k)
    (hbox : ∑ k ∈ range R, ((oldA k - newA k) / 2) * (rcsch (newA k / 2)) ^ (2 : ℕ)
        ≤ ∑ k ∈ range R, ((oldB k - newB k) / 2) * (rcsch (oldB k / 2)) ^ (2 : ℕ)) :
    0 ≤ (∑ k ∈ range L, (rcoth (newB k / 2) - rcoth (oldB k / 2)))
        + (∑ k ∈ range R, (rcoth (oldA k / 2) - rcoth (newA k / 2))) := by
  have hahead : (∑ k ∈ range R, (rcoth (oldA k / 2) - rcoth (newA k / 2)))
      = -(∑ k ∈ range R, (rcoth (newA k / 2) - rcoth (oldA k / 2))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hahead]
  have hloss : (∑ k ∈ range R, (rcoth (newA k / 2) - rcoth (oldA k / 2)))
      ≤ ∑ k ∈ range R, ((oldA k - newA k) / 2) * (rcsch (newA k / 2)) ^ (2 : ℕ) := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    obtain ⟨hnA, hAle⟩ := hsignA k hk
    calc rcoth (newA k / 2) - rcoth (oldA k / 2)
        ≤ (oldA k / 2 - newA k / 2) * (rcsch (newA k / 2)) ^ (2 : ℕ) :=
          rcoth_pair_le' (by linarith) (by linarith)
      _ = ((oldA k - newA k) / 2) * (rcsch (newA k / 2)) ^ (2 : ℕ) := by ring
  have hgainR : (∑ k ∈ range R, ((oldB k - newB k) / 2) * (rcsch (oldB k / 2)) ^ (2 : ℕ))
      ≤ ∑ k ∈ range R, (rcoth (newB k / 2) - rcoth (oldB k / 2)) := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    obtain ⟨hnB, hBle⟩ := hsignB k (Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hk) hRL))
    calc ((oldB k - newB k) / 2) * (rcsch (oldB k / 2)) ^ (2 : ℕ)
        = (oldB k / 2 - newB k / 2) * (rcsch (oldB k / 2)) ^ (2 : ℕ) := by ring
      _ ≤ rcoth (newB k / 2) - rcoth (oldB k / 2) :=
          rcoth_pair_ge' (by linarith) (by linarith)
  have hmono : (∑ k ∈ range R, (rcoth (newB k / 2) - rcoth (oldB k / 2)))
      ≤ ∑ k ∈ range L, (rcoth (newB k / 2) - rcoth (oldB k / 2)) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hRL))
      (fun k hk _ => by
        obtain ⟨hnB, hBle⟩ := hsignB k hk
        exact behind_gain_nonneg hnB hBle)
  linarith [hloss, hgainR, hmono, hbox]

/-- **The bulk march clears from the box comparison alone**: `ΔG > 2` for the outer half
(`R ≤ L`) given the inward-drift signs on both sides and the single summed `csch²` box
inequality. This extends `section_march_pos` past the ranks where the interval-position
condition `oldB ≤ newA` fails: the totals still compare because a midpoint-pushed charge
concentrates inverse-quadratic `csch²` weight on its shortened nearest behind boxes. -/
theorem bulk_march_pos {L R : ℕ} {oldB oldA newB newA : ℕ → ℝ} {s fA fB : ℝ}
    (hA : 0 < fA) (hB : 0 < fB) (hRL : R ≤ L)
    (hsignB : ∀ k ∈ range L, 0 < newB k ∧ newB k ≤ oldB k)
    (hsignA : ∀ k ∈ range R, 0 < newA k ∧ newA k ≤ oldA k)
    (hbox : ∑ k ∈ range R, ((oldA k - newA k) / 2) * (rcsch (newA k / 2)) ^ (2 : ℕ)
        ≤ ∑ k ∈ range R, ((oldB k - newB k) / 2) * (rcsch (oldB k / 2)) ^ (2 : ℕ)) :
    2 < legRankNew L R newB newA s fB - legRankOld L R oldB oldA s fA :=
  rank_march_pos hA hB (net_drift_nonneg_csch hRL hsignB hsignA hbox)

end RHTower
