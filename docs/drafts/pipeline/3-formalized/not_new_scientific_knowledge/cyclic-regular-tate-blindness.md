# Cyclic regular Tate blindness

- **ID:** `cyclic-regular-tate-blindness`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`, `[POSITIVE NO-GO]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CyclicRegularTateBlindness.lean`
- **Successor route:** `../../1-in-progress/arbitrary-modulus-hurwitz-virtual-anomaly-descent.md`

## Theorem

For a cyclic group of order `q`, ordinary degree-zero Tate descent on the integral trivial lattice
at a fixed orbit is reduction modulo `q`:

```text
charge_q(c)=0  <->  c is a norm  <->  q divides c.
```

For the integral regular `q`-point permutation lattice, every invariant vector is constant and
every constant vector is a norm.  In particular, for `q>1`, the unit residue survives at a fixed
orbit but dies on the regular orbit.

## No-go

This quotient does cancel the regular packet factor, but it does so by reading stabilizer type.
Attaching the fixed-orbit charge to a scalar zeta zero would require knowing that the zero is fixed
under the relevant base-point action; attaching the regular quotient would require knowing that it
lies in a free orbit.  Used without further arithmetic gluing, the proposed detector therefore
restates the orbit classification rather than proving it.

For the actual functional-equation reflection, the base-point orbits have size one or two; choosing
an unrelated modulus `q` in the Hurwitz coefficient packet does not create an order-`q` stabilizer
on the scalar zero germ.

## Positive statement from the no-go

The arbitrary-modulus route must leave untwisted degree-zero Tate theory:

> `[CONJECTURE] [OPEN CORE]` Construct a twisted/projective arithmetic coefficient class whose
> `q`-phase is derived from the Hurwitz distribution law, whose regular-rank contribution is a norm,
> and whose residual exponent descends to the scalar completed-zeta local order without first
> classifying the zero orbit.

This can be a relative determinant line, a nontrivial cocycle, or a higher connecting class, but it
must contain arithmetic incidence data beyond the trivial and regular integral lattices.

## Formal surface

- `cyclicFixedTateCharge_eq_zero_iff_norm`
- `cyclicFixedTateCharge_one_ne_zero`
- `cyclicRegular_invariant_is_norm`
- `cyclicRegular_unit_is_norm`
- `cyclicTate_separates_fixed_regular`

## Verification

`lake env lean GaloisForLFunctions/RHTower/CyclicRegularTateBlindness.lean` passes on the repository
toolchain.

## Novelty and significance gate

This is standard cyclic integral representation theory.  No claim of new scientific knowledge is
made.  Its value is the exact exclusion of untwisted Tate descent as the missing arbitrary-modulus
anomaly.

## Gates

- [x] 0 -> 1: ordinary cyclic Tate escape stated
- [x] 1 -> 2: fixed and regular norm quotients proved
- [x] 2 -> 3: theorem formalized and checked
- [ ] 3 -> 4: not promoted; twisted arithmetic anomaly remains open
