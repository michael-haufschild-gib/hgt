# 115 — The two-basepoint torus walk: every sign quadrant supplied

[PROVED HERE, Lean: `TorusWalk.lean`; gate 9225 jobs exit 0, all endpoints
`[propext, Classical.choice, Quot.sound]`.]

Doc 114 collapsed the mirror orientation at each basepoint to ONE steerable angle —
the anchor tilt at the mirror point.  The parity criterion compares the orientations at
the TWO basepoints `ρ ± c·i`, and both angles ride the same prime walk at two nearby
frequencies `a = τ + c`, `b = τ − c`.  This doc proves the walk's step set fills the
torus's four quadrants.

## The theorems

- `exists_prime_two_phase_window` — the core supply: for `b < a` with `9(a−b) ≤ a`
  (any not-too-wide annulus; the annulus is tiny in practice, so this is free) and
  `a·(4·log 2) < π` (the quarter-tile Bertrand cap), and ANY fast offset `o` and
  difference target `d`, primes beyond any bound satisfy simultaneously: fast phase
  `a·log q` in the quarter-tile `(o, o+π/4)` mod 2π AND difference phase `(a−b)·log q`
  within `π/8` of `d` mod 2π.  Mechanism: the difference window is a LONG logarithmic
  interval (length `(π/4)/(a−b)` — inversely proportional to the annulus size), long
  enough to contain a full fast tile; the fast tile has length `π/(4a) > log 2`, so the
  Bertrand-window supply puts a prime in it.
- `sin_pos_of_shifted_window` / `sin_neg_of_shifted_window` — sine signs from
  integer-shifted window membership.
- `exists_prime_sin_sign_pair` — **all four quadrants**: any prescribed pair of sine
  signs at the two frequencies is realized by primes at every scale.  Equal signs:
  difference phase near 0; opposite signs: near π — where the two sines are exact
  negatives of each other up to the `π/8` margin.
- `exists_prime_tilt_sign_pair` — the capstone on the annulus: at the two basepoints of
  a narrow strip annulus (`18c ≤ τ + c`, `(τ+c)·4·log 2 < π`), the pair of
  orientation-steering tilt increments
  `(primeTilt q (1−conj(ρ+ci)), primeTilt q (1−conj(ρ−ci)))` realizes EVERY sign pair
  beyond any bound.

## What this closes and what it opens

The two-point joint sweep named in doc 114 now has its step-set theorem: the torus walk
of the two steering angles is not confined to any half-plane or diagonal — all four
increment quadrants are available at every prime scale, with the same explicit window
machinery as everything upstream (so Chebyshev counts and greedy accumulation extend to
the pair walk the way they did to the single walk; the arctan floors apply per
coordinate through the `π/8`-margined windows, sine floor `sin(π/4−π/8) = sin(π/8)`).

The D–H contrast is now concrete: this quadrant supply is a statement about the joint
value distribution of `(sin(a log q), sin(b log q))` over PRIMES — the walk's support
is the multiplicative spectrum itself.  An Euler-product-free FE function has no such
walk; its mirror data has no prime-indexed steering at all (F2/F3).

Open, next objects: (i) pair-reachability — drive the PAIR of tilt angles to any torus
position (the quadrant supply gives the directions; the window counts give the budget;
what's missing is only the two-dimensional greedy — the increments in a chosen quadrant
window have BOTH coordinates floor-bounded, so the 1-D greedy applies per coordinate in
alternation); (ii) the even/odd deck positions expressed in the two-angle coordinates
via `sem_even_iff_anchored_signs_agree` + `im_incidence_anchored_mirror_tilt_only` at
both basepoints — then the meeting question is: which torus positions force sign
agreement, and can the pair walk reach them from any start.  Heights beyond the caps:
the same statements conditional on `PrimeWindowSupply`, as in doc 113.

## Addendum — the eccentricity-bounded quadrant floors (TorusWalk §floors)

The 2-D greedy's quantitative input is now proven (6 more endpoints, axiom-clean, gate
9225 exit 0):

- `primeTilt_ge` — the single-tilt arctangent floor (extracted standalone from the
  increment floor; the factor's real part never exceeds 2);
- `abs_primeTilt_floor` — **the eccentricity bound**: whenever `|sin| ≥ √2/2`, the tilt
  is at least `arctan(q^(−Re w)·(√2/2)/2)` in absolute value.  Floor AND ceiling
  (`abs_primeTilt_le`) live at the SAME exponent `1 − Re ρ`, so the ratio
  ceiling/floor stays bounded by an absolute constant as the prime scale grows — the
  torus steps in each quadrant have bounded shape;
- `abs_sin_floor_pos_window` / `_neg_window` — sine floors from the shifted windows;
- `exists_prime_sin_sign_pair_floors` / **`exists_prime_tilt_sign_pair_floors`** — the
  quadrant supply upgraded: every sign pair of the two basepoint steering tilts is
  realized at every prime scale with BOTH increments floored by
  `arctan(q^(σ−1)·(√2/2)/2)`.

With directions (all four quadrants), floors (this addendum), ceilings
(`abs_primeTilt_le` at the same exponent), and per-window Chebyshev counts (doc 113),
every ingredient of the two-dimensional greedy staircase is machine-checked; what
remains of pair-reachability is the staircase induction itself (four fixed
finite pools, deficit-reduction invariant `|d₊| ≤ δ` while `d₋` descends).  Beyond it,
the meeting question in final coordinates: which torus positions of the two steering
angles force the two-point sign agreement of `sem_even_iff_anchored_signs_agree`, given
`im_incidence_anchored_mirror_tilt_only` at both basepoints — the position set an odd
order must dodge FOREVER while the pair walk, with all four quadrant directions and
divergent budgets, sweeps the torus.
