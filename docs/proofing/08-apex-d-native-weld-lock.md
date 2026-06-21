# APEX-D Proof Attempt: Native Weld / C5-Star Branchhood Lock

Source: `docs/consolidated/08-conjectures-required.md` §3.

Claim status: `[OPEN CORE]`.

## Target Claim

There is a native weld theorem coupling the unique non-CC archimedean lane to
the CC prime lanes jointly and irreducibly. This C5-star theorem would be the
branchhood lock: no single-prime, single-Frobenius, purely archimedean, or
purely analytic parent can state or prove it.

## Proof Attempt

Use the Door-2 test as a proof constraint. Let a candidate theorem `T` be
formulated with data

```text
(A, {sigma_p}, FE weld),
```

where `A` is the archimedean non-CC lane and `{sigma_p}` are the prime CC lanes.

If the statement and proof of `T` factor through only `A`, then it is
differential-Galois/Holder-side Source A, hence not native. If they factor
through only `{sigma_p}`, then prime lanes decouple into classical
difference/Bohr/Dirichlet theory, hence not native. If the FE is used only as
ordinary symmetry or crystallinity, Davenport-Heilbronn-style FE examples show
it is RH-blind and not enough.

Therefore a C5-star theorem must contain a nonfactorable term. Schematically,
it must use an obstruction of the form

```text
Phi(A, {sigma_p}) != Phi_A(A) + Phi_P({sigma_p})
```

or a relative class whose restrictions to the Source-A-only and Source-B-only
borders vanish or become classical, while the joint class remains nonzero.

## Weakened Theorem Proved Here

**Theorem APEX-D-W.** Any candidate whose statement and proof factor through
only Source A, only Source B, or ordinary FE crystallinity fails to be a native
C5-star theorem.

Proof: this is the Door-2 criterion applied to the three parent projections.
Source A reduces to Holder/differential Galois; Source B decouples
prime-by-prime; FE crystallinity is known to be RH-blind. Thus none is the
joint irreducible weld.

## Attack As False

The danger is that C5-star is only a name for "whatever is missing." Without a
specific invariant, cohomology class, operator, or positivity object, it cannot
be proved. The branchhood lock must be a theorem with a host object and a
falsifiable statement, not a slogan.

## Candidate Shape

A viable statement would look like:

```text
There exists a relative weld class omega_weld in H^*(joint category, borders)
such that:
  restriction to Source A border is classical/zero,
  restriction to Source B border is classical/zero,
  omega_weld obstructs source-built faithful positivity or DSS realization,
  fake-family controls kill all parent reductions.
```

This is only a shape, not a theorem.

## Missing Input

1. Definition of the joint category and its border restriction functors.
2. A concrete relative invariant or class.
3. Proof that the class is nonfactorable across Source A and Source B.
4. Proof it buys either the RH positivity apex, the value apex, or a native
   branchhood theorem independent of both.
