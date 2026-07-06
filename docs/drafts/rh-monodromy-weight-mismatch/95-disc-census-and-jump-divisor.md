# 95 — The DISC census on the finite carrier; the DISC jump divisor on the line

The two forward objects doc 94 §5 named are built.  Two new Lean modules — `DiscCensus.lean`,
`DiscJump.lean` — bind the window-level DISC bit to a **decidable finite-carrier value** and to a
**discrete divisor on ℝ**.  Both typecheck axiom-clean; integrated in `RHTower.lean`.

## 1. The finite-side DISC census (`DiscCensus.lean`)

The DISC bit of a window is a value, not just a predicate: the enclosed right-half order sum `N`
reduced mod `2^k`.

- **`windowRightSum t m := ∑_{z∈t, Re z>½} m z`** and **`windowDiscBit k t m := (windowRightSum
  t m : ZMod (2^k))`** — the census, valued in the finite decidable ring `ZMod (2^k)`.
  `windowDiscBit_eq_zero_iff`: vanishes ⟺ `2^k ∣ N`, the window's rung datum.
- **`windowDiscBit_transport`** — under the two boundary congruences at level `2^{k+1}` (deck-side
  total-order + seam-side on-line), the ξ census and the `completedGN N` census are **EQUAL in
  `ZMod (2^k)`**.  This lifts `anneal_window_parity_transport` from a congruence of counts to an
  identity of window *values*: the DISC bit is carrier-invariant across the seam.
- **`completedGN_deckClass_eq_line_iff_right_dvd` / `…_iff_discBit`** — the finite carrier's OWN
  level-`2^{k+1}` loop class equals its line prediction iff its census vanishes.  Reflection
  invariance of the finite-carrier orders is supplied by `completedGN_orderAt_lineReflect`; no
  entire factorization of `completedGN` is required (the presentation is the hypothesis, exactly as
  for ξ in `LineHolography`).  This is the DISC bit as a finite-side deck integral.
- **`xi_rung_of_completedGN_discBit_zero` / `xi_rightSum_dvd_of_completedGN_discBit_zero`** — the
  payoff: the finite carrier's loop-vs-line agreement (census `= 0`, a finite check on the
  computable zeros of a concrete Dirichlet-type object), together with the boundary congruences,
  forces `2^k ∣` ξ's right-half order sum.  ξ's per-window rung datum is read off a **decidable**
  finite-carrier deck class.

The census is genuinely decidable: `ZMod (2^k)` has `DecidableEq`, and `completedGN N`'s window
zeros are finite with computable orders, so `windowDiscBit k t₂ m₂ = 0` is a finite computation —
whereas the ξ census is over the unknown ξ-zeros.  The transport identifies the two.

## 2. The DISC jump divisor on the line (`DiscJump.lean`)

The box order sum `boxOrderSum T = ∑_{z ∈ boxFinset T} ord_ξ(z)` (zeros in `{½<Re<1, 0≤Im<T}`) is
a step function of the height built from the bulk analytic ξ.

- **Step-function structure**: `boxOrderSum_mono` (monotone); `boxOrderSum_add_sdiff` (the jump
  formula — raising `T₁→T₂` adds exactly the total order of the zeros with height in `[T₁,T₂)`,
  `mem_boxFinset_sdiff` identifying that slice); `boxOrderSum_const_of_no_zeros` (**local
  constancy** — flat on any height interval free of box zeros).
- **The divisor**: `boxHeightZeros t` (box ξ-zeros at exact height `t`, finite) and
  **`discJump t := ∑ ord_ξ` over them** — a locally finite `ℕ`-valued divisor on ℝ.
  `discJump_eq_zero_iff`: **support = the set of zero heights**.
  **`boxOrderSum_eq_sum_discJump`**: `boxOrderSum T = ∑_{t below T} discJump t` — the census is the
  partial-sum sequence of the divisor (fiberwise over `Complex.im`).
- **The census as a height function**: `discCensusH k T := (boxOrderSum T : ZMod (2^k))`;
  `discCensusH_const_of_no_zeros` (**locally constant off the zero heights**).
- **Certificate reading**: `dvd_discJump_of_windowCertificate` (the rung certificate makes every
  jump `2^k`-divisible — the divisor is entrywise `2^k·ℕ`); `discCensusH_eq_zero_of_windowCertificate`
  (the census is then flat `= 0`).
- **RH as an empty divisor**: `forall_boxHeightZeros_empty_iff` (an off-axis zero contributes at
  its own height, conjugation carries the lower half-plane to the upper) gives
  **`rh_iff_forall_discJump_eq_zero` : `RiemannHypothesis ↔ ∀ t, discJump t = 0`.**  The boundary
  program interrogates the discrete jump divisor on the line in place of the ξ-zeros in the plane.

## 3. Status and the two-object weld

Both objects are unconditional Lean over the ξ-divisor and the finite carrier.  The finite census
(Object 1) is where the DISC value becomes *computable*; the jump divisor (Object 2) is where it
becomes a *discrete object on the line* whose partial sums are the census and whose support is the
zero-height set.  They meet at `windowDiscBit`/`discCensusH`: the same residue mod `2^k`, once as a
carrier-invariant window value, once as a step function of the height.

The census reads only the **sum** `N` (the loop is blind to the split `D=L+2N`); the per-zero
refinement is the 2D generic-center extraction of doc 94 (`rhLadder_of_lineHolography`).  The jump
divisor, summing per height, likewise reads the per-height total; two box zeros sharing an
imaginary part are separated only by the extraction's center freedom, not by the 1-D divisor.

## 4. What this opens

The census being a decidable `ZMod (2^k)` value on `completedGN` makes the DISC bit a **finite
instrument**: for a fixed window and level, its value is a terminating computation on the finite
carrier's zeros.  The next object is the **census profile** — the map `T ↦ discCensusH k T` as a
right-continuous `ZMod (2^k)`-valued step function of the height, whose jump set is a subset of the
zero heights and whose total variation over `[0,T]` counts the rung-failing crossings.  Two forward
moves: (a) a **finite-carrier census profile** `T ↦ (finite boxOrderSum on completedGN mod 2^k)`
whose agreement with the ξ profile is exactly the transported congruences at every height — a
height-indexed family of decidable checks; (b) the **divisor difference** `discJump_ξ − discJump_g`
between ξ and the finite carrier as a signed divisor on ℝ supported where the two carriers' zero
heights disagree — the object whose vanishing is the seam's exactness and whose `2^k`-classes are
the transported rung data, read directly as a discrete measure on the line.
