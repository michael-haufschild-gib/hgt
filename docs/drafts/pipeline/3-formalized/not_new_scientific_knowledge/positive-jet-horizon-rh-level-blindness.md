# Positive-jet horizon geometry cannot mark the RH zero level

- **ID:** `positive-jet-horizon-rh-level-blindness`
- **Stage:** 3-formalized
- **Type:** EXACT RH NO-GO / AFFINE-ORIGIN BLINDNESS
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parents:** `projective-jet-horizon-stabilizer-law`,
  `projective-horizon-one-sided-depth-transition`
- **Statement:** Positive-derivative horizon fields are invariant under constant translation of
  the source. Consequently their complete field topology cannot identify which projective target
  value is the zero level. Even adjoining the completed zeta functional equation, reality, and
  order-one growth does not repair this blindness.

## General theorem

Let `f` lie in a differential field over a constant field `C`. For every `a in C` and every
positive depth `n`,

```text
T_n(f-a)=T_n(f),                                          (1)
```

because

```text
delta^k(f-a)=delta^k f,    k>=1.                          (2)
```

Thus every construction determined by the family of positive jet-tail fields, their joins, their
intersections, or the resulting Tits/current/cusped topology is invariant under changing the
target level designated as zero.

At the same time,

```text
(f-a)(s)=0  iff  f(s)=a.                                  (3)
```

The zero divisor of `f-a` is the `a`-point divisor of `f`, and generally changes with `a`.

## Completed-zeta countermodel

Let `xi` be the completed Riemann xi function and put

```text
a=xi(2),
g(s)=xi(s)-a.                                             (4)
```

Then:

1. `g` is entire of order one, because subtracting a constant preserves both properties.
2. `g(s)=g(1-s)`, because `xi(s)=xi(1-s)`.
3. `g` has the same conjugation/reality symmetry as `xi`, because `xi(2)` is real.
4. Every positive derivative and every positive-jet horizon field of `g` equals the corresponding
   one for `xi`, by `(1)--(2)`.
5. Nevertheless

   ```text
   g(2)=0,                                                 (5)
   ```

   and `Re(2) != 1/2`.

Therefore the complete positive-jet horizon geometry, even together with entire order-one growth,
the completed functional equation, and reality, is logically insufficient to imply the Riemann
hypothesis for the distinguished zero level.

## What data are missing

The horizon system is an unpointed projective target geometry. A zero divisor requires a marked
target point

```text
0 in P^1(C).                                               (6)
```

Constant translations move `(6)` while leaving every positive horizon unchanged. Any RH-facing
use of the horizon theory must therefore add a source-specific orientation that breaks this affine
gauge. For zeta/xi the plausible source of such a marking is arithmetic normalization—Euler
product, Dirichlet coefficient `1`, or an equivalent prime-source datum—not more projective or
current-algebra geometry.

This identifies the exact boundary between the primary HT discovery and RH: the horizon theory
classifies constraint information after value erasure; RH is a statement about one distinguished
value fiber.

## Lean status

The formal theorem

```text
jetTailField_constSlopeAffine_eq
```

in `formal/GaloisForLFunctions/HTGeometry/ProjectiveJetHorizon.lean` proves the stronger field
identity for every nonzero differential-constant affine slope and arbitrary base translation. The
case `alpha=1`, `beta=-a` is `(1)`. No new Lean assumption is required.

## Novelty status

The derivative identity `(2)`, preservation of the xi functional equation under constant
translation, and the counterexample `(4)--(5)` are elementary. The card records their exact
consequence for the new horizon framework and prevents a false RH promotion; it is not claimed as
new scientific knowledge.

## Route exclusion

Any proposed implication of the form

```text
positive horizon topology + xi reflection + order-one growth + reality => RH
```

is false. A viable route must use data that distinguish `xi` from `xi-xi(2)`.


## Lean formalization

Modules (namespace `RHTower` / `GaloisForLFunctions.HTGeometry`), both wired into their area
umbrellas:

- `formal/GaloisForLFunctions/HTGeometry/ProjectiveJetHorizon.lean`
- `formal/GaloisForLFunctions/RHTower/PositiveJetHorizonLevelBlindness.lean`

| Paper statement | Lean declaration |
|---|---|
| `(1)`--`(2)` positive jet-tail fields are level blind | `jetTailField_constSlopeAffine_eq` |
| `(4)` the level-shifted completion `g = xi - a` | `xiLevelShift` |
| `g` entire | `xiLevelShift_differentiable` |
| item 2, `g(s) = g(1-s)` | `xiLevelShift_one_sub` |
| item 3, Schwarz reality (with `xi 2` real) | `xiLevelShift_conj`, `xi_two_conj` |
| item 4, every positive derivative is unchanged | `deriv_xiLevelShift`, `iteratedDeriv_xiLevelShift` |
| item 1, order-one growth envelope preserved | `xiLevelShift_growth` |
| `(5)` `g(2) = 0` with `Re 2 != 1/2` | `xiLevelShift_xiTwo_two`, `re_two_ne_half` |
| the complete countermodel | `xi_levelShift_countermodel` |

The order-one clause is carried in the corpus's unconditional envelope form
`RHTower.xi_growth_order_le_one` (`‖xi s‖ ≤ exp(C(1+‖s‖)log(2+‖s‖))`), which the constant shift
inherits with the constant `1 + ‖xi 2‖`.

Audit: direct `lake env lean` check clean, targeted module build clean, umbrella import wired,
`#print axioms` returns only `propext`, `Classical.choice`, `Quot.sound`.
