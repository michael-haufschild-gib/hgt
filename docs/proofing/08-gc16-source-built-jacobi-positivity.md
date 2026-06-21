# G-C16 Proof Attempt: Source-Built Jacobi Positivity

Source: `docs/consolidated/08-conjectures-required.md` appendix.

Claim status: `[CONJECTURE]`.

## Target Claim

Euler/PNT/Gamma/pole/FE data construct a canonical completed Jacobi or membrane
system that is a positive contraction at all levels.

## Attempt

If a source-built self-adjoint recurrence/operator `J_xi` satisfies

```text
spec(J_xi) subset [-1,1]
```

and its spectral leakage outside `[-1,1]` is exactly the faithful off-line
index, then positivity/contraction implies RH.

## Weakened Theorem

A source-built self-adjoint contraction whose failure of contractivity equals
`kappa_-` proves RH.

## Obstruction

Constructing finite Jacobi approximants is not enough; finite gates can be
fake-blind. The all-level operator and its no-zero-feeding audit are missing.

## Missing

Canonical recurrence/operator, self-adjointness, all-level contraction, and
fake-family separation.
