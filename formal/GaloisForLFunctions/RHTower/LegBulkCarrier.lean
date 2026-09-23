/-
# LegBulkCarrier — rational `csch²` envelopes and certificate satisfiability witnesses

Two algebraic envelopes squeeze `csch²` between rational functions:

* `csch²(v) ≤ (1/v)²` for `v > 0` (from `v ≤ sinh v`);
* `((1 − v²/6)/v)² ≤ csch²(v)` for `0 < v` with `v² ≤ 6` (from the cubic bound
  `sinh v · (1 − v²/6) ≤ v`, itself proved by two derivative passes from
  `sinh v ≤ v · cosh v`).

With both, the summed `csch²` box inequality of `bulk_march_pos` at RATIONAL distances
reduces to exact rational arithmetic, and a march instance can be certified end to end.

The two fixed configurations below are satisfiability witnesses for the two summed march
certificates — exact rational evaluations showing each certificate's premise is non-vacuous
precisely where the other's fails, nothing more. Class-level content lives in the
quantified certificate theorems and in the length-uniform `harmonic_edge_march`:

* `harm_bulk_march` — a 24-pole harmonic carrier (`T m = Σ_{j<m} 2/(j+1)`, charge one third
  into the gap between poles 11 and 12) where the interval condition `oldB ≤ newA` fails at
  eight of the ten paired ranks (`harm_dist_fails` certifies rank 5), so no per-rank
  criterion applies, yet the summed box hypothesis of `bulk_march_pos` holds.
* `wide_bulk_march` — a five-pole wide-gap carrier where the net drift is negative, so the
  box premise fails, yet the loss stays below the far cushion and the weak certificate
  applies.
-/
import GaloisForLFunctions.RHTower.LegAdiabatic
import Mathlib.Tactic.FinCases

noncomputable section

namespace RHTower

open Finset

/-- `cosh y ≤ 1 + (y/3)·sinh y + (y²/6)·cosh y` for `0 ≤ y`: the difference has derivative
`(2/3)(u·cosh u − sinh u) + (u²/6)·sinh u ≥ 0` and vanishes at `0`. -/
theorem cosh_le_one_add_cubic {y : ℝ} (hy : 0 ≤ y) :
    Real.cosh y ≤ 1 + y / 3 * Real.sinh y + y ^ (2 : ℕ) / 6 * Real.cosh y := by
  have hmono : MonotoneOn
      (fun t => 1 + t / 3 * Real.sinh t + t ^ (2 : ℕ) / 6 * Real.cosh t - Real.cosh t)
      (Set.Icc 0 y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 y) (by fun_prop) (by fun_prop)
    intro u hu
    rw [interior_Icc, Set.mem_Ioo] at hu
    have hd : HasDerivAt
        (fun t => 1 + t / 3 * Real.sinh t + t ^ (2 : ℕ) / 6 * Real.cosh t - Real.cosh t)
        (2 * u / 3 * Real.cosh u + u ^ (2 : ℕ) / 6 * Real.sinh u - 2 / 3 * Real.sinh u) u := by
      have h1 : HasDerivAt (fun t : ℝ => t / 3 * Real.sinh t)
          (1 / 3 * Real.sinh u + u / 3 * Real.cosh u) u :=
        ((hasDerivAt_id u).div_const 3).mul (Real.hasDerivAt_sinh u)
      have hp : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) / 6) (2 * u / 6) u := by
        simpa using (hasDerivAt_pow 2 u).div_const 6
      have h2 : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) / 6 * Real.cosh t)
          (2 * u / 6 * Real.cosh u + u ^ (2 : ℕ) / 6 * Real.sinh u) u :=
        hp.mul (Real.hasDerivAt_cosh u)
      have h3 := ((h1.const_add 1).add h2).sub (Real.hasDerivAt_cosh u)
      apply h3.congr_deriv
      ring
    rw [hd.deriv]
    have hsc : Real.sinh u ≤ u * Real.cosh u := sinh_le_mul_cosh hu.1.le
    have hsn : 0 ≤ Real.sinh u := Real.sinh_nonneg_iff.mpr hu.1.le
    have h23 : 2 / 3 * Real.sinh u ≤ 2 / 3 * (u * Real.cosh u) :=
      mul_le_mul_of_nonneg_left hsc (by norm_num)
    have hq : 0 ≤ u ^ (2 : ℕ) / 6 * Real.sinh u :=
      mul_nonneg (by positivity) hsn
    linarith [h23, hq]
  have key := hmono (Set.left_mem_Icc.mpr hy) (Set.right_mem_Icc.mpr hy) hy
  norm_num [Real.sinh_zero, Real.cosh_zero] at key
  linarith [key]

/-- The cubic `sinh` bound `sinh v · (1 − v²/6) ≤ v` for `0 ≤ v`: the odd tail `sinh v − v`
is at most `(v²/6)·sinh v`. The difference vanishes to third order at `0` and its derivative
is nonnegative by `cosh_le_one_add_cubic`. -/
theorem sinh_mul_one_sub_le {v : ℝ} (hv : 0 ≤ v) :
    Real.sinh v * (1 - v ^ (2 : ℕ) / 6) ≤ v := by
  have hmono : MonotoneOn
      (fun t => t + t ^ (2 : ℕ) / 6 * Real.sinh t - Real.sinh t) (Set.Icc 0 v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 v) (by fun_prop) (by fun_prop)
    intro u hu
    rw [interior_Icc, Set.mem_Ioo] at hu
    have hd : HasDerivAt (fun t => t + t ^ (2 : ℕ) / 6 * Real.sinh t - Real.sinh t)
        (1 + 2 * u / 6 * Real.sinh u + u ^ (2 : ℕ) / 6 * Real.cosh u - Real.cosh u) u := by
      have hp : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) / 6) (2 * u / 6) u := by
        simpa using (hasDerivAt_pow 2 u).div_const 6
      have h2 : HasDerivAt (fun t : ℝ => t ^ (2 : ℕ) / 6 * Real.sinh t)
          (2 * u / 6 * Real.sinh u + u ^ (2 : ℕ) / 6 * Real.cosh u) u :=
        hp.mul (Real.hasDerivAt_sinh u)
      have h3 := ((hasDerivAt_id u).add h2).sub (Real.hasDerivAt_sinh u)
      apply h3.congr_deriv
      ring
    rw [hd.deriv]
    have haux := cosh_le_one_add_cubic hu.1.le
    linarith [haux]
  have key := hmono (Set.left_mem_Icc.mpr hv) (Set.right_mem_Icc.mpr hv) hv
  norm_num [Real.sinh_zero] at key
  nlinarith [key]

/-- **Lower `csch²` envelope**: `((1 − v²/6)/v)² ≤ csch²(v)` for `0 < v` with `v² ≤ 6`, from
the cubic bound `sinh v · (1 − v²/6) ≤ v`. Rational in `v`: together with the upper envelope
it reduces `csch²` box comparisons at rational distances to exact rational arithmetic. -/
theorem rcsch_sq_ge_rat {v : ℝ} (hv : 0 < v) (hv6 : v ^ (2 : ℕ) ≤ 6) :
    ((1 - v ^ (2 : ℕ) / 6) / v) ^ (2 : ℕ) ≤ (rcsch v) ^ (2 : ℕ) := by
  have hs : 0 < Real.sinh v := sinh_pos_of_pos hv
  have hnum : 0 ≤ 1 - v ^ (2 : ℕ) / 6 := by linarith
  have h1 : (1 - v ^ (2 : ℕ) / 6) / v ≤ rcsch v := by
    rw [rcsch, div_le_div_iff₀ hv hs]
    nlinarith [sinh_mul_one_sub_le hv.le]
  exact pow_le_pow_left₀ (div_nonneg hnum hv.le) h1 2

/-- Pole positions of the harmonic carrier: the `m`-th pole sits at `Σ_{j<m} 2/(j+1)`, so
consecutive gaps are `2/1, 2/2, 2/3, …` — decreasing and convex. -/
def harmT (m : ℕ) : ℝ := ∑ j ∈ range m, 2 / (j + 1)

/-- Behind distances of the CURRENT charge (in the gap between poles 11 and 12, ahead
distance `2/39` to pole 12): rank `k` reaches pole `11 − k`. -/
def harmOldB (k : ℕ) : ℝ := harmT 12 - harmT (11 - k) - 2 / 39

/-- Behind distances of the ADVANCED charge (in the next gap, ahead distance `2/39` to
pole 13): rank `k` reaches pole `12 − k`. -/
def harmNewB (k : ℕ) : ℝ := harmT 13 - harmT (12 - k) - 2 / 39

/-- Ahead spectator distances of the CURRENT charge: rank `k` reaches pole `13 + k`. -/
def harmOldA (k : ℕ) : ℝ := harmT (13 + k) - harmT 12 + 2 / 39

/-- Ahead spectator distances of the ADVANCED charge: rank `k` reaches pole `14 + k`. -/
def harmNewA (k : ℕ) : ℝ := harmT (14 + k) - harmT 13 + 2 / 39

/-- On the harmonic carrier the interval condition `oldB ≤ newA` FAILS at the fifth paired
rank: the cumulated behind window has overtaken the ahead window, so per-rank domination
(`rank_pair_domination`) is unavailable there — the march below is genuinely closed by the
summed box comparison, not by any per-rank criterion. -/
theorem harm_dist_fails : harmNewA 5 < harmOldB 5 := by
  simp only [harmNewA, harmOldB, harmT]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

/-- **Satisfiability witness for the summed box hypothesis**: a single exact rational
evaluation on the 24-pole harmonic carrier where per-rank domination fails
(`harm_dist_fails`) but the summed `csch²` box comparison still holds, so `bulk_march_pos`
gives `ΔG > 2`. This is a witness that the box premise is non-vacuous in the genuinely
summed regime — a fixed configuration, not a class statement. -/
theorem harm_bulk_march :
    2 < legRankNew 12 10 harmNewB harmNewA (2 / 39) (harmT 13 - 2 / 39)
        - legRankOld 12 10 harmOldB harmOldA (2 / 39) (harmT 23 - harmT 12 + 2 / 39) := by
  have hbox : ∑ k ∈ range 10, ((harmOldA k - harmNewA k) / 2) * (rcsch (harmNewA k / 2)) ^ (2 : ℕ)
      ≤ ∑ k ∈ range 10, ((harmOldB k - harmNewB k) / 2) * (rcsch (harmOldB k / 2)) ^ (2 : ℕ) := by
    calc ∑ k ∈ range 10, ((harmOldA k - harmNewA k) / 2) * (rcsch (harmNewA k / 2)) ^ (2 : ℕ)
        ≤ ∑ k ∈ range 10, ((harmOldA k - harmNewA k) / 2) * (1 / (harmNewA k / 2) ^ (2 : ℕ)) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          fin_cases hk <;>
            exact mul_le_mul_of_nonneg_left
              (rcsch_sq_le_inv_sq (by
                simp only [harmNewA, harmT]
                norm_num [Finset.sum_range_succ, Finset.sum_range_zero]))
              (by
                simp only [harmOldA, harmNewA, harmT]
                norm_num [Finset.sum_range_succ, Finset.sum_range_zero])
      _ ≤ ∑ k ∈ range 10, ((harmOldB k - harmNewB k) / 2)
            * ((1 - (harmOldB k / 2) ^ (2 : ℕ) / 6) / (harmOldB k / 2)) ^ (2 : ℕ) := by
          simp only [harmOldA, harmNewA, harmOldB, harmNewB, harmT]
          norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
      _ ≤ ∑ k ∈ range 10, ((harmOldB k - harmNewB k) / 2) * (rcsch (harmOldB k / 2)) ^ (2 : ℕ) := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          fin_cases hk <;>
            exact mul_le_mul_of_nonneg_left
              (rcsch_sq_ge_rat
                (by
                  simp only [harmOldB, harmT]
                  norm_num [Finset.sum_range_succ, Finset.sum_range_zero])
                (by
                  simp only [harmOldB, harmT]
                  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]))
              (by
                simp only [harmOldB, harmNewB, harmT]
                norm_num [Finset.sum_range_succ, Finset.sum_range_zero])
  refine bulk_march_pos ?_ ?_ (by norm_num) ?_ ?_ hbox
  · simp only [harmT]
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  · simp only [harmT]
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  · intro k hk
    fin_cases hk <;>
      exact ⟨by
          simp only [harmNewB, harmT]
          norm_num [Finset.sum_range_succ, Finset.sum_range_zero],
        by
          simp only [harmNewB, harmOldB, harmT]
          norm_num [Finset.sum_range_succ, Finset.sum_range_zero]⟩
  · intro k hk
    fin_cases hk <;>
      exact ⟨by
          simp only [harmNewA, harmT]
          norm_num [Finset.sum_range_succ, Finset.sum_range_zero],
        by
          simp only [harmNewA, harmOldA, harmT]
          norm_num [Finset.sum_range_succ, Finset.sum_range_zero]⟩

/-!
### Witness that the weak certificate's premise survives where the box premise dies

A carrier of five poles at `0, 12, 18, 22, 25` (gaps `12, 6, 4, 3`) with the charge at
`11.1`: one behind pole, two ahead spectators. The behind gain falls short of the ahead
loss, so the net spectator drift is negative and the common premise of `section_march_pos`
and `bulk_march_pos` fails; the total loss (bounded by `≈ 0.26` through `csch² ≤ 1/v²`)
still sits far below the far cushion `> 2`, so the premise of `section_march_pos_weak`
holds. A fixed configuration certifying the two premises are incomparable — not a class
statement. -/

/-- Behind distance of the current charge (one behind pole, distance `11.1`). -/
def wideOldB : ℕ → ℝ := fun _ => 111 / 10
/-- Behind distance of the advanced charge (the swapped pole becomes the near behind pole). -/
def wideNewB : ℕ → ℝ := fun _ => 51 / 10
/-- Ahead spectator distances of the current charge: `6.9` then `10.9`. -/
def wideOldA : ℕ → ℝ := fun k => if k = 0 then 69 / 10 else 109 / 10
/-- Ahead spectator distances of the advanced charge: `4.9` then `7.9`. -/
def wideNewA : ℕ → ℝ := fun k => if k = 0 then 49 / 10 else 79 / 10

/-- **Satisfiability witness for the weak certificate under negative net drift**: a single
exact rational evaluation on the five-pole carrier where the gains fall short of the losses
(the box premise fails) yet the two ahead losses, boxed by `((oldA−newA)/2)·(1/(newA/2)²)`,
sum to under `2 <` cushion, so `section_march_pos_weak` gives `ΔG > 0`. A fixed
configuration, not a class statement. -/
theorem wide_bulk_march :
    0 < legRankNew 1 2 wideNewB wideNewA (9 / 10) (171 / 10)
        - legRankOld 1 2 wideOldB wideOldA (9 / 10) (139 / 10) := by
  refine section_march_pos_weak ?_ ?_
  · intro k hk
    fin_cases hk
    exact ⟨by norm_num [wideNewB], by norm_num [wideNewB, wideOldB]⟩
  · have hcush : (2 : ℝ) < rcoth (171 / 10 / 2) + rcoth (139 / 10 / 2) :=
      far_cushion_gt_two (by norm_num) (by norm_num)
    have hbd : (∑ k ∈ range 2, (rcoth (wideNewA k / 2) - rcoth (wideOldA k / 2)))
        ≤ ∑ k ∈ range 2, ((wideOldA k / 2 - wideNewA k / 2) * (1 / (wideNewA k / 2) ^ (2 : ℕ))) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      fin_cases hk <;>
        · simp only [wideNewA, wideOldA]
          norm_num only
          refine le_trans (rcoth_pair_le' (by norm_num) (by norm_num)) ?_
          exact mul_le_mul_of_nonneg_left (rcsch_sq_le_inv_sq (by norm_num)) (by norm_num)
    have henv : (∑ k ∈ range 2, ((wideOldA k / 2 - wideNewA k / 2) * (1 / (wideNewA k / 2) ^ (2 : ℕ))))
        < 2 := by
      simp only [wideOldA, wideNewA]
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
    linarith [hbd, henv, hcush]

end RHTower
