# Theta rank-three D1 automatic grading

- **ID:** S6G-D1-AUTO-GRADE
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / ROUTE-KILL
- **Route:** TCD / S6F finite rank-three D1
- **Novelty:** NOVELTY UNVERIFIED

## Exact attempted RH chain

```text
positive scalar-contravariant form on any source-sl2-stable polynomial carrier containing D1
  -> convergent norm/evaluation certificate for source D1
  -> native rank-three D1 on 0 < x < 137/2000
  -> finite TCD/S6F gate
  -> cofinal all-order Hankel/Bezoutian landing
  -> Weil positivity
  -> RH
```

The conjecture attacks the first arrow. A proof combines with the formal D1 vacuum-string no-go and
kills every scalar proper-carrier rescue, not merely carriers assumed graded.

## Corpus-derived conjecture

- `[CORPUS]` `modularThetaSourcePositiveFieldLie_sl2H_of_adaptedHomogeneous` identifies adapted
  weight `W` with Cartan eigenvalue `2W`.
- `[CORPUS]` `modularThetaSourcePositiveToAdapted_sl2H` identifies the Cartan operator with twice
  the positive weighted Euler operator.
- `[CORPUS]` `lagrangeSpectralProjector_mulVec_eigen` and `aeval_lagrangeBasis_mulVec` implement
  finite Lagrange spectral extraction.
- `[LEAN-PROVED]` Once one positive adapted component of D1 belongs to the carrier, repeated
  lowering produces a finite vacuum string incompatible with positive scalar contravariance.

`[CONJECTURE TCD-D1-AUTO-GRADE]` Every complex submodule of the source polynomial carrier stable
under source `E` and `F` and containing D1 automatically contains every adapted homogeneous
component of D1.

## Proof architecture

`E,F` stability implies `H=[E,F]` stability. Any fixed polynomial has finite adapted-weight
spectrum. On that finite sum, the Lagrange polynomial for eigenvalue `2W`, evaluated at `H`, equals
the adapted-weight projector. Since a submodule stable under `H` is stable under every polynomial
in `H`, the projected component remains in the submodule.

Success closes the scalar-carrier route completely. Failure must exhibit a concrete invariant
submodule violating finite Cartan spectral extraction and would define the exact surviving
non-graded representation route.
