# Completed-flux incidence square

- **ID:** `completed-flux-incidence-square`
- **Stage:** 3-formalized / not-new
- **Type:** THEOREM (paper + Lean), `[PROVED]`, `[SOURCE BRIDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CompletedFluxIncidenceSquare.lean`
- **Successor route:** `../../1-in-progress/quadratic-reflection-anomaly-rh.md`

## Theorem

Let `F_rho(x)` be the removable completed local flux germ

```text
F_rho(x)=x(-Xi'/Xi)(rho+x),
F_rho(0)=-ord_rho(Xi).
```

Then its incidence square

```text
S_rho(x)=F_rho(x)^2
```

is analytic at `x=0`, satisfies

```text
S_rho(0)=ord_rho(Xi)^2,                                  (1)
```

and is reflection-invariant in reflected local coordinates:

```text
S_(1-rho)(-x)=S_rho(x).                                  (2)
```

On the open strip, the exact completed source decomposition gives the germ identity

```text
S_rho
 = P_rho^2 + 2 P_rho A_rho + A_rho^2,                   (3)
```

where `P_rho` is the removable continued infinite-prime flux germ and `A_rho` is the removable
archimedean/boundary flux germ.

## Significance for the quadratic route

Equation `(3)` is the sought local **symmetric arithmetic incidence pairing**.  It does not try to
quadratically refine the alternating weld commutator; it squares the completed source flux itself.
Equation `(1)` proves that the local source incidence reads multiplicity squared, and `(2)` proves
that the two members of a free reflected pair contribute equally rather than canceling.

## Positive statement from the remaining no-go

The local square also survives at a fixed critical-line zero, where it still equals `m^2`.  Hence it
is not yet an off-line detector.  The exact positive successor is:

> construct a source-functorial equivariant fixed-point subtraction that removes the fixed-orbit
> local square while retaining the sum of both squares on a free orbit, then assemble it excisively
> over finite windows.

Any subtraction defined after listing Xi zeros would be circular.  It must arise from the stabilizer
action on the completed source germ.

Moreover, the existing scalar-gluing classification proves that a germ-local gauge-invariant
fixed/free correction factors through orbit shape.  Thus “stabilizer action” here cannot mean only
the rank-one FE/Schwarz arrow coefficients; it must include a source-derived arithmetic lattice,
filtration, pairing, or nonlocal window incidence that reduces the full scalar gauge.

## Formal surface

- `completedFluxIncidenceSquareGermAt_analyticAt_zero`
- `completedFluxIncidenceSquareGermAt_zero`
- `completedFluxIncidenceSquareGermAt_reflection`
- `completedFluxIncidenceSquareGermAt_eq_primeArch_square_eventually`
- `completedFluxIncidenceSquareGermAt_eq_incidence_decomposition_eventually`

## Verification

`lake env lean GaloisForLFunctions/RHTower/CompletedFluxIncidenceSquare.lean` passes on the repository
toolchain.

## Novelty and significance gate

This is a direct algebraic composition of existing removable-germ and prime--archimedean
decomposition theorems.  No claim of new scientific knowledge is made.  Its value is to turn the
quadratic route's proposed symmetric pairing into an exact source object already present in the
corpus.

## Gates

- [x] 0 -> 1: completed-flux square proposed as symmetric incidence source
- [x] 1 -> 2: local order-square, reflection, and source decomposition proved
- [x] 2 -> 3: formalized and checked
- [ ] 3 -> 4: not promoted; equivariant fixed-point subtraction and window closure remain open
