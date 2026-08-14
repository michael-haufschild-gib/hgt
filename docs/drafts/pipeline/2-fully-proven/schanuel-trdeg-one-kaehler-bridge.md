# Transcendence-degree-one Kähler bridge

- **ID:** schanuel-trdeg-one-kaehler-bridge
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; standard algebraic geometry)
- **Source:** transcendence bases, rational-function differentials, separable base change
- **Statement:** for a characteristic-zero field extension `K/A` of transcendence degree one,
  `dim_K Omega_(K/A)=1`, without a finite-generation hypothesis.

## Theorem

Let `A` and `K` be fields of characteristic zero with an injective `A`-algebra structure on `K`.
If

\[
 \operatorname{trdeg}_A K=1,
\]

then

\[
 \dim_K\Omega_{K/A}=1. \tag{1}
\]

## Proof

The nonzero transcendence degree gives an element `u in K` transcendental over `A`.  The singleton
`{u}` is algebraically independent.  Since its cardinality equals the transcendence degree, it is
a transcendence basis; hence `K` is algebraic over `A(u)`.

The field `A(u)` is `A`-isomorphic to the rational function field `A(X)`.  Localization of the
polynomial differential basis gives

\[
 \Omega_{A(X)/A}\simeq A(X)\,dX,
\]

so its dimension is one.  Characteristic zero makes the algebraic extension `K/A(u)` separable.
For a separable algebraic field extension, formal étaleness gives

\[
 K\otimes_{A(u)}\Omega_{A(u)/A}\simeq\Omega_{K/A}.
\]

Base change preserves the one-element basis, proving `(1)`.

## Route consequence

Every stage-two field of transcendence degree one has a one-dimensional Kähler module.  Combined
with concrete adjugate algebraicity of `K/K_M`, this supplies the previously missing hypothesis of
`schanuelDefect_slope_mem_of_integral_isogeny`.  Finite isogenies therefore preserve the exact
rank-one defect wall for a categorical reason: they are separable algebraic, hence formally
étale.

## Lean status

A single scratch batch now contains four declarations:

1. separable-algebraic Kähler finrank transfer;
2. one-dimensional differentials of `RatFunc A` via localization of `A[X]`;
3. transport to `A⟨u⟩` for transcendental `u`;
4. theorem `(1)` via a singleton transcendence basis.

All four declarations were checked together with `lake env lean` in one foreground scratch batch,
then copied unchanged into
`GaloisForLFunctions.RHTower.SchanuelKaehlerDimension` and wired into the `RHTower` umbrella.
The scratch declarations contain no project-specific assumptions beyond the stated field,
algebra, characteristic-zero, and transcendence-degree hypotheses.  No project build was run.

## Novelty

Mathematics is standard; route-level identification is new internal progress, not a novelty claim.
It closes a real formal dependency rather than assuming Kähler dimension from transcendence
degree.

## Log

- 2026-08-14 -- dependency-closed paper proof isolated; batched Lean scratch implementation
  prepared without starting a build under saturated shared load.
- 2026-08-14 -- scratch proof kernel-checked; four declarations wired into source and umbrella.
