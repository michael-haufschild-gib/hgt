/-
# AdiabaticLedger — the doc 30 exact step ledger (task #143 / #142 substrate)

Doc 30 (30-adiabatic-ledger.md) §1/§2/§5 `[PROVED HERE]`. Flat grading: elementary `coth`
monotonicity facts on the exact step decomposition; nothing new. The march criterion for the
equilibrium distance `s_i` is `ΔG(s) := G_{i+1}(s) − G_i(s) > 0`, and doc 30 decomposes
`ΔG` exactly into two swap extras (each a `coth` of a positive argument, `> 1`) plus telescoping
`coth`-increment drift terms (§1). Here are the sign facts of that ledger:

* `rcoth_add_gt_two` — **the swap cushion** `> 2`: the two swap extras `coth((t_{i+2}−t_1−s)/2)`
  and `coth((δ_{i+1}+s)/2)`, being `coth` of positive arguments, each exceed `1` (§1, the
  constant-lattice `ΔG = 2` recovered).
* `driftBehind_nonneg` — for gaps **decreasing outward**, each behind drift term
  `coth((newB−s)/2) − coth((oldB−s)/2) ≥ 0` (a gain), since `newB ≤ oldB` and `coth` is
  strictly decreasing (§2).
* `driftAhead_nonpos` — symmetrically, each ahead drift term
  `coth((oldA+s)/2) − coth((newA+s)/2) ≤ 0` (a loss) (§2).
* `march_positive` — **the (ADB) structure**: cushion `> 2` and total drift `> −2` ⟹ `ΔG > 0`
  (the monotone `s`-march).
* `adb_crude_suffices` — **the (ADB-crude) closing** (§5): if the total-variation-weighted
  spectator drift has magnitude below the swap cushion, then `ΔG > 0` — no cancellation, no
  signs, no convexity. `LHS = O(log/c) ≪ RHS ~ 2i/c` on every Jensen-section field in the bulk.
-/
import GaloisForLFunctions.RHTower.CothInfra

noncomputable section

namespace RHTower

open Set

/-- **The swap cushion `> 2`** (doc 30 §1): the two swap extras are `coth` of positive
arguments, each `> 1`, so together they exceed `2` — the constant-lattice `ΔG = 2` cushion. -/
theorem rcoth_add_gt_two {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 2 < rcoth a + rcoth b := by
  have h1 := one_lt_rcoth_of_pos ha
  have h2 := one_lt_rcoth_of_pos hb
  linarith

/-- **Behind drift is a gain under decreasing gaps** (doc 30 §2): if the new behind distance
does not exceed the old (`0 < newB ≤ oldB`, i.e. `δ_{i+1} ≤ δ_{i+1−k}`), then
`coth(newB/2) − coth(oldB/2) ≥ 0` because `coth` is strictly decreasing. -/
theorem driftBehind_nonneg {newB oldB : ℝ} (hnew : 0 < newB) (hle : newB ≤ oldB) :
    0 ≤ rcoth newB - rcoth oldB := by
  have hle' : rcoth oldB ≤ rcoth newB :=
    rcoth_strictAntiOn_pos.antitoneOn (mem_Ioi.mpr hnew)
      (mem_Ioi.mpr (lt_of_lt_of_le hnew hle)) hle
  linarith

/-- **Ahead drift is a loss under decreasing gaps** (doc 30 §2): if `0 < newA ≤ oldA`
(`δ_{i+1+j} ≤ δ_{i+1}`), then `coth(oldA/2) − coth(newA/2) ≤ 0`. -/
theorem driftAhead_nonpos {newA oldA : ℝ} (hnew : 0 < newA) (hle : newA ≤ oldA) :
    rcoth oldA - rcoth newA ≤ 0 := by
  have hle' : rcoth oldA ≤ rcoth newA :=
    rcoth_strictAntiOn_pos.antitoneOn (mem_Ioi.mpr hnew)
      (mem_Ioi.mpr (lt_of_lt_of_le hnew hle)) hle
  linarith

/-- **The (ADB) march structure** (doc 30 §1): `ΔG = cushion + drift` with `cushion > 2` and
total drift `> −2` gives `ΔG > 0` — the equilibrium distance decreases monotonically. -/
theorem march_positive {cushion drift : ℝ} (hcush : 2 < cushion) (hdrift : -2 < drift) :
    0 < cushion + drift := by linarith

/-- **The (ADB-crude) closing inequality** (doc 30 §5): if the total-variation-weighted
spectator drift has magnitude strictly below the swap cushion, then `ΔG = cushion + drift > 0`.
This is the crude sufficient condition that clears with `1/δ`-room on every regular
(`|δ_{j+1}−δ_j| = O(δ²)`) one-sided section field — no cancellation, no signs, no convexity. -/
theorem adb_crude_suffices {cushion drift : ℝ} (hbound : |drift| < cushion) :
    0 < cushion + drift := by
  have := abs_lt.mp hbound
  linarith [this.1]

end RHTower
