# The two-spin Lee--Yang block has a sharp coefficient selector

- **ID:** `lee-yang-two-spin-quadratic-selector`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[FINITE CONSUMER] [POSITIVE NO-GO] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/LeeYangQuadraticBlock.lean`
- **Consumer:** `../../1-in-progress/prime-source-ferromagnetic-ising-lee-yang-limit-rh.md`

## Theorem

The normalized fugacity polynomial of a two-spin Ising interaction is

```text
L_c(z) = 1 + 2 c z + z^2.
```

Lean identifies this with the reciprocal quadratic block `iharaBlock 1 (-2c)` and proves

```text
every zero of L_c has |z|=1  <->  c^2 <= 1.
```

In the ferromagnetic chamber, `c=exp(-2J)` with `J>=0`, so `0<c<=1`; the unit-circle conclusion
follows.  The file states the algebraic coefficient version `0<=c<=1`, without importing analytic
facts about the exponential.

## Positive no-go

For every real `c`, the reciprocal identity

```text
z^2 L_c(z^(-1)) = L_c(z)
```

holds away from `z=0`.  Lean verifies at `c=2` that reciprocity still holds while the unit-circle
property fails.  Thus the functional equation is not the selector; the load-bearing datum is the
ferromagnetic coefficient chamber.  For the large Ising detour, the source theorem must therefore
produce nonnegative couplings or an independently verified Lee--Yang measure.  Palindromicity alone
is unusable.

## Formal certificate

The module proves:

- `leeYangPairBlock_eq_iharaBlock`;
- `leeYangPairCircle_iff`;
- `leeYangPairCircle_of_ferromagneticCoefficient`;
- `leeYangPairBlock_reciprocal`;
- `leeYangPair_reciprocity_does_not_force_circle`.

The exact module builds.  Axiom audits of the selector, its ferromagnetic consequence, and the
no-go report only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] normalized pair block defined
- [x] exact circle selector proved
- [x] ferromagnetic chamber consequence proved
- [x] reciprocal-symmetry no-go proved
- [x] exact Lean build
- [x] accepted-axiom audit
