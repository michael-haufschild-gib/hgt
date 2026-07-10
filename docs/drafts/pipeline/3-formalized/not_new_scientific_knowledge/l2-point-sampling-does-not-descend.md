# Point sampling does not descend to the canonical L2 theta-source space

- **ID:** l2-point-sampling-does-not-descend
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) - grade **BRIDGE / ROUTE GATE**
- **Source:** `xi-theta-unit-radius-perron-source.md`;
  `archimedean-sampling-total-variation-defect.md`
- **Statement:** No map from complex `L2(R)` can recover `f(x)` from the `L2` class of every
  representative `f`; therefore the literal `L2` theta density and prime-log point sampling do not
  define a Hilbert sampling pair.

## Goal

Audit the most immediate candidate for the canonical Hilbert test norm. The actual positive theta
source is already formalized as an element of complex `L2(R)`, so its literal Riesz representer is
available there. This theorem determines whether prime-log point sampling is simultaneously an
operator on that same Hilbert space.

## Theorem

Fix `x in R`. There is no map

`E : L2(R;C) -> C`

such that, for every `L2` representative `f`,

`E([f]) = f(x)`.

Indeed, the function equal to one at `x` and zero elsewhere is zero almost everywhere, hence has
the zero `L2` class, while its value at `x` is one. Comparing it with the zero representative gives
`E(0)=1` and `E(0)=0`.

## Consequences

- `[PROVED]` Ambient `L2(R)` cannot supply the prime-log sampling operator, even without asking for
  linearity or boundedness.
- `[PROVED]` The canonical `L2` theta class does not by itself define an expression
  `h_theta in Ran(S*)`, because the intended point-sampling `S` does not descend to this space.
- `[NOT CLAIMED]` This does not exclude point sampling on a reproducing-kernel subspace continuously
  embedded in `L2`; it proves that such extra regularity is indispensable.
- `[OPEN CORE]` A source-selected RKHS, de Branges carrier, or other point-evaluable Hilbert space
  must be constructed before the adjoint-range question is mathematically determined. Under a
  changed norm the Riesz representer is generally not the literal theta density.

## Gates

- [x] 0 -> 1 in-progress: the ambient `L2` candidate and quotient obstruction are explicit.
- [x] 1 -> 2 fully-proven: singleton-null-set proof complete.
- [x] 2 -> 3 formalized: `no_l2_pointEvaluator_on_representatives`; focused build green; axiom
  audit reports only `[propext, Classical.choice, Quot.sound]`.
- [ ] 3 -> 4 publication-ready: not a standalone novelty result.

## Scientific status

This is standard measure-theoretic quotient structure, not new scientific knowledge. Its value is
to prevent an ill-posed Hilbert defect from being mistaken for progress on the theta-source range
problem.

## Log

- 2026-07-11 - Formalized the representative obstruction and ruled out ambient `L2` as the common
  space for the literal theta density and prime-log point sampling.
