# 117 — Pair-reachability, the endpoint no-go as theorem, and the arc-winding dictionary

[PROVED HERE — every claim below is machine-checked, axiom-clean
`[propext, Classical.choice, Quot.sound]`; files: `StaircaseDescent.lean`,
`PairStaircase.lean`, `EndpointNoGo.lean`, `ArcWindingDictionary.lean`.]

## 1. The two-phase staircase (the corrected descent, formalized)

`staircase_drive` (StaircaseDescent.lean): from two disjoint pools whose steps have
the driven coordinate in `[f, δ]` and the banded coordinate in `[f, δ]` resp.
`[−δ, −f]`, any deficit `≤ n·f + δ` is driven into `(−δ, δ]` in `≤ n` steps while the
banded deficit never leaves `(−δ, max D δ]`.  Induction on the step count; the two
pools of the needed half-plane both advance the driven coordinate — the divergent
correction cascade of the naive alternation (doc 116 addendum) never starts.

`staircase_reach_nonneg`: applied twice with the coordinates exchanged (the doubly
positive pool is split between the phases by the `≤ n` card bound), three quadrant
pools steer both nonnegative deficits into the `δ`-box simultaneously.  Budgets are
counts against `f`: `n₁f + δ ≥ T₊`, `n₂f + δ ≥ max T₋ δ`, cards `n₁+n₂ / n₁ / n₂`.

## 2. The pool-form quadrant supply (Chebyshev bulk)

`two_phase_window_pool` (PairStaircase.lean): the two-phase window construction now
returns the WINDOW, scale-pinned to `W ∈ [X, X + 5π/(a−b) + 2π/a]`: EVERY prime of
`(e^W, e^{W+π/(4a)}]` has its fast phase in the prescribed quarter-tile and its
difference phase within `π/8` of the target.  No Bertrand sampling — the pool's
population is counted, not sampled.

`sin_sign_pair_pool`, `tilt_sign_pair_pool_base`: per quadrant, every pool element
carries the sign pair, the `√2/2` sine floors, and the arctangent tilt floors at
exponent `Re ρ`.  `windowPrimes_card_of_scale`: one budget inequality
(mass `e^X(e^L log2 − log4)` vs `N(X+Bt)` + explicit lower-order terms) certifies
`N` primes in every window of the batch.

## 3. Pair-reachability [THE CAPSTONE]

`anchorTilt_pair_reachable_nonneg`: for `0 < Re ρ < 1`, heights `ρ.im ± c` with
`9(2c) ≤ ρ.im + c` and `(ρ.im + c)·4log2 < π`: for all `T₊, T₋ ≥ 0`, `ε > 0`, `Q`,
there is a finite prime set `P`, all elements prime and `> Q`, with

    |T₊ − anchorTilt P (ρ+ci)| ≤ ε   and   |T₋ − anchorTilt P (ρ−ci)| ≤ ε.

Mechanism: three quadrant pools at one common scale `X`; the scale is pushed until
the ceiling `2e^{−σX}` falls under `ε` and the Chebyshev mass `e^X/X` outgrows the
`e^{σX}` step count — possible exactly because floor and ceiling share the exponent
`σ = Re ρ < 1`.  The absorption threshold is explicit (`λ = (3+σ)/4`).
`anchorTilt_pair_reachable_nonneg_mirror`: the same at the mirror basepoints
`1 − conj(ρ ± ci)`.  Since every consumer of these angles is `2π`-periodic,
nonnegative targets already steer both phases everywhere on the torus.

## 4. The endpoint no-go [NOW A THEOREM]

`exists_anchor_rotated_sign_pair` (EndpointNoGo.lean): for any nonzero prime-free
values `z±` and any sign pair, prime sets beyond any bound counter-rotate both into
the prescribed `Im`-sign pair (targets `arg z± ∓ π/2 + 2π`, tolerance `π/4`).

`incidence_endpoint_sign_steerable`: via the cancellation theorem at the mirror
points and `1 − conj(1 − conj w) = w`, the incidence orientation at OUR basepoints is
`‖A_P(ρ±ci)‖⁻¹ · Im(e^{−i·anchorTilt P(ρ±ci)} · (−completedSEM N (ρ±ci)))` — so the
endpoint orientation sign pair takes all four values, given only
`completedSEM N (ρ±ci) ≠ 0` (supplied by split-data domination in context).

`endpoint_orientation_no_go`: two prime sets `P₁, P₂` whose anchored members have
THE SAME deck class (both equal the plain member's, by `anchoredSEM_roots_of_sem_roots`)
and DIFFERENT endpoint orientation sign pairs (`(+,+)` vs `(+,−)`).  Hence no
prime-set-independent function of the two endpoint `Im`-signs computes the deck
class.  The parity dictionary cannot be the raw endpoint signs.

## 5. The arc-winding dictionary [THE SHARPEST COORDINATES]

`ArcWindingDictionary.lean`:

- `anchorLog` — the anchor's GLOBAL canonical logarithm on `Re > 0` (principal
  factor logs; each factor stays in the right half-plane): analytic, exponentiates
  to the anchor, and `Im anchorLog = anchorTilt`.
- `anchor_arc_variation` — **the anchor never winds**: along any continuous path in
  the right half-plane, the `Im`-increment of ANY continuous logarithm of the anchor
  equals the endpoint tilt difference.  The anchor's arc contribution is an exact
  endpoint datum — precisely the steerable pair of §3.
- `anchoredSEM_arc_variation` — the dictionary decomposition: any logarithm of the
  anchored member splits its arc winding as (member log increment) + (endpoint tilt
  difference).
- `deckClass_eq_exp_log_mismatch` and `deckClass_neg_one_zpow_log_mismatch` — the
  deck cocycle in logarithm coordinates: for any chart logarithms `ℓ₁, ℓ₂` of the
  member and ANY analytic square roots (root choices cancel in the double ratio),

      deckClass = exp((ℓ₁−ℓ₂)(pP)/2 − (ℓ₁−ℓ₂)(pM)/2) = (−1)^{k_P − k_M},

  where `k_P, k_M` are the `2πi`-quantization integers of the pointwise log
  mismatches at the two basepoints.  The parity datum IS the parity of the winding
  mismatch between the basepoints.

## 6. Where the weld's conjecture now lives

Composing §4 and §5: the parity is `k_P − k_M mod 2` — a difference of arc-winding
integers of the MEMBER's chart logarithms; the anchor shifts each chart logarithm by
`anchorLog`, whose arc increments are pure endpoint tilt differences (no integer
content of their own) but which move WHICH branch the chart logarithm selects when
the charts are glued by continuation.  The route's central conjecture in these
coordinates [CONJECTURE]: as the anchor's endpoint tilt pair sweeps `(0, 2π)²`
(pair-reachability), the induced motion of `(k_P, k_M)` for the anchored member
detects the member's hole count mod 2 — the Euler-product walk can always be driven
to expose the count-pinned winding, and an FE-only mirror analogue (Davenport–
Heilbronn), having no prime-indexed walk, cannot.  Next formal object: the branch
tracking of the glued chart logarithm under a continuous tilt sweep — the map from
the steered pair to `(k_P, k_M)` on a concrete annulus datum.

## Addendum — the dictionary closes the circle: rigidity IS monodromy-freeness

Two further theorems banked (`ArcWindingDictionary.lean`, axiom-clean, gate green):

- `deckClass_neg_one_zpow_arg_variation` — the two-arc form: the deck class is
  `(−1)^k` with `2πk` the DIFFERENCE of the member's argument variations along the
  two charts between the basepoints.
- `anchoredSEM_deckClass_neg_one_zpow_arg_variation` — **rigidity from
  monodromy-freeness**: adding the canonical anchor logarithm to both chart
  logarithms produces chart logarithms of the ANCHORED member with the same
  pointwise mismatches — the anchor's arc contribution is endpoint-pure and
  identical on the two charts (they share basepoints), so it CANCELS from the
  winding mismatch.  The anchored deck class is `(−1)^k` with the member's own `k`.
  This reproves `anchoredSEM_roots_of_sem_roots` from the dictionary side and
  sharpens it: the prime set cannot move the parity through the winding integers of
  any FIXED chart logarithms.  Its only handle is which branch the gluing selects
  under continuation — and the branch selector is driven by the endpoint tilt pair,
  which is dense (pair-reachability).  The weld's D–H discriminator is now pinned to
  a single object: the branch-tracking map `(φ₊, φ₋) ↦ (k_P, k_M)` of the glued
  chart logarithm under a continuous tilt sweep on a concrete annulus datum.
