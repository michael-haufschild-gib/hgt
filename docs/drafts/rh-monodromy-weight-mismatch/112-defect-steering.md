# 112 — Defect steering quantified: what the anchor turns, by how much, and what it cannot turn

[PROVED HERE, Lean: `DefectSteering.lean`] — the named next object of doc 111: how the
defect angle turns the boundary phases of √anchoredSEM as P grows.

## The steering laws (all machine-checked, axiom-clean)

**The defect is a prime-indexed walk.** `anchorMirrorDefect_insert`: adjoining a prime
`q` to `P` advances the defect by the increment
`mirrorTiltIncrement q s = primeTilt q (1−s̄) + primeTilt q s`; the empty set has defect
zero, a singleton IS its increment. The defect at any `P` is the sum of its per-prime
steps.

**The step's sign is arithmetic.** `im_eulerFactor` gives the Euler factor's imaginary
part at every real part: `q^{−Re s}·sin(Im s·log q)`. Hence (`primeTilt_pos_iff`/
`primeTilt_neg_iff`, `mirrorTiltIncrement_pos`/`mirrorTiltIncrement_neg`): at any strip
point, the increment of `q` is strictly positive when `sin(Im s·log q) > 0` and strictly
negative when `< 0` — BOTH tilt terms share the sign because the mirror point has the
same height and complementary real part. The walk's step directions are read off the
sequence `{τ·log q mod 2π}` — the prime logarithms at the zero's height. This is where
the increments become arithmetic data and where a Davenport–Heilbronn analogue, whose
"anchor" has no Euler factorization over primes, loses the steering wheel.

**The step's size is pinned.** From below (`mirrorTiltIncrement_ge`):
`increment ≥ arctan(q^{−Re s}·sin(Im s·log q)/2)` when the sine is positive — the
factor's real part never exceeds 2. From above (`abs_mirrorTiltIncrement_le`):
`|increment| ≤ 2·q^{−σ₀}/(1−q^{−σ₀})` on a symmetric band. Since `∑ q^{−σ₀}` over
primes diverges for `σ₀ < 1`, the walk's total budget is unbounded in P: the defect can
be driven anywhere its sign-pattern allows.

**The turning at root level is exactly half the defect.**
`canonicalAnchorRoot P s = √‖A‖·e^{i·tilt/2}` squares to the anchor
(`canonicalAnchorRoot_sq`, via the polar identity), never vanishes on the strip, and
pairs across the critical line by a rotation of exactly `defect/2`
(`canonicalAnchorRoot_mul_mirror`):

```
√A(1−s̄) · √A(s) = √(‖A(1−s̄)‖·‖A(s)‖) · e^{i·defect(s)/2}
```

**What the defect cannot turn.** `anchoredSEM_roots_of_sem_roots` (via the banked
`deckClass_mul_global`): the anchor is a unit with a GLOBAL square root on the strip
ball, so chart roots of the symmetric member transport to chart roots of the anchored
member with the SAME two-point deck class. Anchoring twists every boundary phase by
half-tilt increments; the parity certificate itself is anchor-invariant — as it must
be, since the parity equals the intrinsic vanishing order.

## What this fixes about the weld's shape

The instrument panel is now complete and its degrees of freedom are separated:

| datum | steerable? | by what |
|---|---|---|
| hole count | NO — rigid (= order, `splitData_count_rigid`) | nothing |
| deck class of √member | NO — anchor-invariant (`anchoredSEM_roots_of_sem_roots`) | nothing |
| hole-zero positions | YES | truncation length N (`sem_hole_zeros_localize`) |
| boundary phases of √anchoredSEM | YES — by exactly `defect/2` | prime set P, sign per prime = `sign sin(τ log q)` |

So the weld cannot be "turn the class with the defect" — the class is rigid. The
mechanism must instead be a MEETING: the class is evaluated by a boundary functional
(the two-point orientation reading of the parity criterion), the functional's value
moves continuously with the steerable phases, and its admissible positions are
constrained. An odd class must be shown incompatible with SOME reachable position of
the steered phases — an intermediate-value/pigeonhole argument over the P-walk, whose
steps are signed by `sin(τ log q)` and sized by the arctan bounds proven here.

## Next objects

1. **The reachability lemma**: from the sign law + Bertrand (mathlib has it), for
   heights `|τ| ≤ π/log 2` every sign pattern is realizable with primes of prescribed
   size; quantify the reachable defect set (an interval mod 2π?) as P ranges over
   finite prime sets — the walk's step sizes decay like `q^{−σ}` but their sum
   diverges, so the reachable set should be everything.
2. **The meeting functional**: the two-point orientation reading (EdgeEventParity's
   criterion) evaluated on `canonicalAnchorRoot·(root of member)` — express its
   defect-dependence exactly, then ask what position the odd class forces and whether
   a divergent-budget walk can always escape it.

## Addendum — the steering supply is proven (§6 of `DefectSteering.lean`)

The first next-object is discharged in its Bertrand range:

- `exists_prime_log_mem_Ioo` — **Bertrand in logarithmic windows**: any log-interval of
  length `> log 2`, based far enough out, contains the log of a prime beyond any bound
  (the overshoot `log(1 + e^{−b}) ≤ e^{−b}` is absorbed by the basing condition).
- `exists_prime_tau_log_window` — for `0 < τ` with `τ·log 2 < π`, every sine window
  `(2πk + a, 2πk + a + π)` of the phase `τ·log q` is hit by primes beyond any bound.
- `exists_prime_sin_pos` / `exists_prime_sin_neg` — both signs of `sin(τ·log q)` are
  realized by arbitrarily large primes.
- **`exists_prime_mirrorTiltIncrement_pos` / `_neg`** — THE STEERING WHEEL IS LIVE: at
  every strip point of height `0 < Im s < π/log 2`, the defect walk has strictly
  positive AND strictly negative steps available at every prime scale. Combined with
  `mirrorTiltIncrement_ge` the positive steps have explicit arctan floors.

Range note: `π/log 2 ≈ 4.53`. For heights above it the sine windows are shorter than
`log 2` in log-scale and Bertrand cannot certify a prime per window — the same
statements at all heights need prime gaps `log(p'/p) < π/τ`, i.e. PNT-grade input; and
FULL defect reachability (drive the walk to any target angle) additionally needs a
divergent certified budget per window chain, i.e. Chebyshev-type prime counting in
intervals (one prime per window gives a geometrically decaying — summable — budget).
Both are named open supplies, not obstructions: the steering STRUCTURE is complete and
axiom-clean; what remains quantitative is only how much of the wheel's range each prime
density theorem certifies.

The weld now reads: the parity class is rigid and anchor-invariant; the boundary
phases carrying its two-point evaluation turn by exactly `defect/2`; the defect is a
prime-indexed walk with live, sign-controlled steps below height `π/log 2`. The next
generative move is the meeting functional (doc 112 §next-2): the orientation reading
of the parity criterion evaluated on the canonically-anchored root, as an explicit
function of the defect — then the incompatibility argument between an odd class and
the reachable phase set.

## Addendum 2 — the meeting functional's domain (§7 of `DefectSteering.lean`)

- `deckClass_one_iff_signs_agree` — at each basepoint the ratio of the two chart square
  roots is a sign `±1`, and the deck class is trivial exactly when the two signs agree:
  the parity certificate IS a two-point boundary-orientation comparison, literally.
- **`sem_even_iff_anchored_signs_agree`** — the rung parity in its final finite form:
  for any dominating split of the symmetric member and any chart roots of the ANCHORED
  member,

  ```
  Even (hole count)  ⟺  sign at P₊  =  sign at P₋
  ```

  where the signs are `G₁/G₂` evaluated at the two annulus basepoints. Left side:
  intrinsic, anchor-rigid, N-rigid (= order parity). Right side: a comparison of two
  boundary phases living on the object whose mirror structure the defect walk turns by
  exactly `defect/2` per crossing, with live sign-controlled steps below height
  `π/log 2`.

The open weld is now ONE equation between a rigid datum and a steered datum. What
remains — the genuine open core, stated as the route's conjecture — is the
incompatibility argument: show that "signs disagree" (odd order) cannot survive every
position of the steered boundary phases that the prime walk can reach, while a
Davenport–Heilbronn analogue (no Euler product, no walk) must be allowed to keep it.
Every instrument this argument needs is now machine-checked; its missing inputs are
quantitative prime supplies (PNT-grade gaps above height π/log 2, Chebyshev window
counts for full reachability), not structure.
