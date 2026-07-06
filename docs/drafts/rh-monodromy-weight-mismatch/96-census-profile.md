# 96 — The census profile as a right-continuous step function; finite agreement; the divisor difference

The forward object doc 95 §4 named is built.  One new Lean module — `CensusProfile.lean` — realises
the census as a right-continuous `ZMod (2^k)`-valued step function of the height, and its two
refinements: the finite-carrier census profile (a) and the signed divisor difference (b).  All
typecheck axiom-clean `[propext, Classical.choice, Quot.sound]`; integrated in `RHTower.lean`.

## 1. The profile (right-continuous step function)

With the **closed** height cutoff, `boxOrderSumLe T = ∑ ord_ξ over {½<Re<1, 0≤Im≤T}` includes the
zeros sitting exactly at height `T`.  This is the right-continuous normalisation:

- **`censusProfile k T := (boxOrderSumLe T : ZMod (2^k))`** — the profile.
- **`boxOrderSumLe_eventuallyConst_right`** — the underlying count is constant on a right
  neighbourhood `[T, T+δ)` of every height (finitely many zeros in any bounded band ⟹ a gap above
  `T` before the next zero height).
- **`censusProfile_continuousWithinAt`** — hence `ContinuousWithinAt (censusProfile k) (Ici T) T`:
  right-continuity into the discrete ring `ZMod (2^k)`, made rigorous.
- **`censusProfile_const_of_no_zeros`** — locally constant off the zero heights (a step function).
- **`censusProfile_eq_left_add_discJump`** — the jump identity:
  `censusProfile k T = discCensusH k T + (discJump T : ZMod (2^k))` for `T ≥ 0`.  The
  right-continuous profile exceeds its left value (the open census `discCensusH`) by exactly the
  jump divisor `discJump T` — the profile's steps ARE the jump divisor of doc 95.

## 2. (a) The finite-carrier census profile

The ξ profile is carried by the reflection-closed strip configuration `stripFinsetLe T`
(`lineReflect_mem_stripFinsetLe`), whose right half is the box (`stripFinsetLe_filter_right`), so
**`censusProfile_eq_windowDiscBit`**: `censusProfile k T = windowDiscBit k (stripFinsetLe T) ord_ξ`.

- **`TransportedProfile N k G mg`** — a height-indexed family of reflection-closed `completedGN N`
  configurations `G T`, order-pinned, with the two boundary congruences (deck + seam, both at level
  `2^{k+1}`) to the ξ strip configuration at every height.
- **`censusProfile_eq_finiteCensusProfile`** — under that data, `censusProfile k = fun T =>
  windowDiscBit k (G T) mg` as functions into `ZMod (2^k)`.  The right side is the **decidable
  finite-carrier census profile**: each value is a finite computation on the finite carrier's window
  zeros (`ZMod (2^k)` is `DecidableEq`, `G T` a Finset).  The equality at every height is exactly
  the transported congruences — a height-indexed family of decidable checks certifying the ξ
  profile.

## 3. (b) The divisor difference

At a single height the reflection-closed slice is `stripHeightFinset t`
(`lineReflect_mem_stripHeightFinset` — reflection preserves the height), whose right-half order sum
is the jump divisor (`windowRightSum_stripHeightFinset`).

- **`finiteDiscJump H mg t := windowRightSum (H t) mg`** — the finite carrier's jump at height `t`.
- **`jumpDiff H mg t := (discJump t : ℤ) − (finiteDiscJump H mg t : ℤ)`** — the **signed divisor
  difference** on ℝ.
- **`jumpDiff_eq_zero_of_no_zeros`** — the difference vanishes where neither carrier has a zero at
  height `t`: its **support lies in the union of the two carriers' zero-height sets**.
- **`two_pow_dvd_jumpDiff`** — for a reflection-closed height-`t` finite-carrier configuration with
  the two boundary congruences, `(2^k : ℤ) ∣ jumpDiff`.  The ξ and finite-carrier jump divisors
  agree mod `2^k`, so their difference is a discrete measure on the line valued in `2^k·ℤ` — its
  `2^k`-classes carry the transported rung datum.

## 4. Status and the seam picture

The profile is unconditional over the ξ divisor.  (a) and (b) consume the finite carrier only
through its actual (finite) zero Finsets and the two boundary congruences — the finite carrier is
represented by its zero data, so nothing here rests on an unproven `completedGN` finiteness lemma;
the analytic content is exactly the transported congruences, typed as hypotheses.

The three faces cohere: the profile is the running total, its jumps are the jump divisor, and the
finite carrier tracks both mod `2^k` — the census as a right-continuous step function, the finite
carrier as its decidable shadow, the divisor difference as the discrete measure of their
disagreement.

## 5. What this opens

The profile being right-continuous and locally constant makes it a **bounded-variation** object:
over `[0,T]` its total variation counts the crossings, and its mod-`2^k` jumps are the rung-failing
heights.  The next object is the **variation functional** `V k T := #{heights below T where the
jump divisor is not `2^k`-divisible}` — a monotone integer profile that is identically `0` iff the
rung holds up to `T`, and whose finite-carrier shadow (through the transport at every height) is a
decidable count.  Two forward moves: (a) the **variation zero-set** as a closed discrete subset of
ℝ whose emptiness on `[0,∞)` is the rung — the boundary program's target reduced to a subset of the
line; (b) the **Stieltjes measure** `d(censusProfile)` of the profile — a `ZMod (2^k)`-weighted
atomic measure on ℝ supported on the zero heights, whose total mass mod `2^k` over a window is the
window's DISC census and whose finite-carrier counterpart differs by a `2^k`-valued atomic measure
(the divisor difference of §3 as a measure).
