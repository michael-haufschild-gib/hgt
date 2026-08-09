# Fisher-deconvolved same-carrier orientation law

- **ID:** `fisher-deconvolved-same-carrier-orientation-law`
- **Stage:** 3 — formalized
- **Type:** THEOREM / EXACT SOURCE-CARRIER CLASSIFIER
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOT RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/FisherDeconvolvedSameCarrierOrientationLaw.lean`

## Theorem

For ordinary primes put

```text
d(p) = p/(p+1)^2,
I_d = {x : C^P | p |-> d(p)x(p) is summable},
Q_d = C^P/I_d,
u_t(p) = 1 + p^(-t).
```

Then:

1. multiplication by `d` gives a canonical linear equivalence
   `Q_d ≃ C^P/ell^1(P)`;
2. a diagonal multiplier preserves `I_d` iff its coefficient field is bounded;
3. `u_t` induces a bijective quotient map on `Q_d` iff `0 <= t`;
4. `u_-t` induces a bijective quotient map on `Q_d` iff `t <= 0`;
5. both quotient maps exist on the same fixed carrier iff `t=0`;
6. the two unconditional coefficient classes `U_t=[u_t]` and `U_-t=[u_-t]` in `Q_d` satisfy

```text
U_t = U_-t  iff  t = 0;
```

7. their weighted difference is the literal signed Gamma Bockstein:

```text
d(p)(u_t(p)-u_-t(p)) = b_t(p).
```

The proof of item 6 is exact: equality in `Q_d` is absolute summability of the weighted
difference, and the existing all-prime Bockstein theorem says this occurs exactly at neutral
grade.

## What changed

Previous fixed-`ell^1` comparison had coefficient `r_t=d*u_t`: its quotient map was surjective but
noninjective, and reciprocal multiplication did not descend. Moving only source-derived Fisher
density into the ideal makes normalized transport an automorphism in its oriented half-space.
More importantly, both normalized coefficient fields now exist as literal elements of one fixed
carrier at every grade, so no equivariant carrier renaming is needed to compare them.

## Exact frontier

This theorem does not prove equality for actual Xi divisors. It proves that such equality is
exactly horizontal neutrality. Source involution relates `U_t` over `rho` to `U_-t` over the
reflected divisor; it does not identify them in one fixed fibre.

Remaining producer:

`[OPEN CORE] FISHER_DECONVOLVED_ORIENTATION_EQUALITY_SOURCE_LAW` — derive
`U_t=U_-t` at every actual Xi divisor from a pre-divisor rational-adelic/Cartier boundary relation,
while retaining prime labels, the nonzero leading Xi multiplicity coefficient, and both
orientations. Asserting this equality or same-fibre naturality is RH-equivalent by the theorem.

## Verification

- direct `lake env lean` check: passed;
- targeted leaf `lake build`: passed;
- umbrella import wired; umbrella build not run;
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`;
- full corpus lint reached unrelated concurrent HTGeometry umbrella-wiring errors; new RHTower
  module itself has no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
