# Exponential-gauge affine-coset law

- **ID:** ht-exponential-gauge-affine-coset
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[BRIDGE]`, not new knowledge
- **Source:** differential-field closure + logarithmic derivative + elementary coset geometry
- **Statement:** For a finite-dimensional differential exponential gauge, the parameters whose
  gauge members lie in a distinguished relatively differential-algebraically closed field form
  either the empty set or one affine coset of the subspace of directions whose logarithmic
  derivatives lie in that field. In one parameter the exceptional set is empty, a singleton, or
  the whole parameter field.

## Goal

Bank the exact algebraic selection mechanism used by the genuinely analytic
`ht-divisor-hermite-saturation` theorem without misgrading it as discovery.

## Parent reduction

Let `u : V -> F^x` be the multiplicative gauge and let `A^x` be the multiplicative group of a
differential field `A`. For fixed `g`, the exceptional set is

`E_g = {v : g u(v) in A^x}`.

After choosing one `v0 in E_g`, elementary group theory already says that `E_g` is the translate of
the subgroup `u^(-1)(A^x)`. The logarithmic derivative identifies that subgroup as

`L = {v : direction(v) in A}`,

provided `A` is derivation-closed and relatively closed under nonzero logarithmic primitives.
Therefore the affine-coset theorem is a useful exact bridge, but its mechanism belongs to parent
group/differential-field theory.

## Multi-parameter theorem `[PROVED HERE, BRIDGE]`

Let `C -> F` be a field extension, `D` a `C`-derivation on `F`, `A` an intermediate field, `V` a
`C`-vector space, and

`direction : V ->_C F`, `u : V -> F`.

Assume:

1. `u(v) != 0`;
2. `u(v+w)=u(v)u(w)`;
3. `D(u(v))/u(v)=direction(v)`;
4. `A` is closed under `D`;
5. if `a in A`, `y != 0`, and `D(y)/y=a`, then `y in A`.

Define

`L = {v : direction(v) in A}`.

Then `L` is a `C`-linear subspace. If `g u(v0) in A`, then

`{v : g u(v) in A} = {v : v-v0 in L}`.

The forward inclusion divides two exceptional members and takes a logarithmic derivative. The
reverse inclusion integrates a logarithmic derivative inside `A` and multiplies the member at
`v0`.

## One-parameter zero-one-all law `[PROVED HERE, BRIDGE]`

For a one-dimensional gauge with derivative direction `dh`, either `dh in A` or `dh notin A`.

- If `dh notin A`, the exceptional parameter set is subsingleton.
- If `dh in A` and one exceptional point exists, every parameter is exceptional.

Thus it is empty, a singleton, or universal. All cases occur, but the classification is the
rank-one form of the parent coset theorem above.

## Lean

Module: `GaloisForLFunctions.ExponentialGaugeSelection`.

- `IsDifferentialExponentialGauge`
- `ClosedUnderLogarithmicPrimitives`
- `IsDifferentialExponentialFamily`
- `differentialRelationSubmodule`
- `exceptionalParameters_eq_relationCoset`
- `exceptionalParameters_subsingleton`
- `gauge_mem_of_direction_mem`
- `exceptionalParameters_subsingleton_or_eq_univ`
- `exceptionalParameters_eq_empty_or_singleton_or_univ`

The module is imported by `GaloisForLFunctions.lean`. The narrow file check and module build pass;
the formal lint gate passes with only pre-existing large-file warnings.

## Gates

- [x] 0 -> 1: exact gauge and selection mechanism
- [x] 1 -> 2: complete abstract proof and honest parent reduction
- [x] 2 -> 3: Lean theorems above, axiom-free
- [ ] 3 -> 4: not eligible as a standalone new-result preprint; retain as support for the analytic
  saturation theorem

## Log

- 2026-07-10 — proved and formalized; downgraded from candidate discovery to `[BRIDGE]` after the
  preimage-of-subgroup reduction.
