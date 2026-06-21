# C2 Proof Attempt: Affine Weld Holonomy

Source: `docs/consolidated/08-conjectures-required.md` §1.

Claim status: `[CONJECTURE]`.

## Target Claim

The weld phase carrier is the holonomy or 1-cocycle of the affine
`(partial_s, M_p)` weld connection, and the `Gamma` completion is the additive
boundary cocycle trivializing the class exactly on `sigma = 1/2`.

## Proof Attempt

Start with the most literal connection on a trivial complex line bundle over
the zero-free region:

```text
nabla = d - d log xi.
```

For a closed contour `gamma` avoiding zeros,

```text
Hol_gamma(nabla) = exp(int_gamma d log xi).
```

By the argument principle,

```text
int_gamma d log xi = 2 pi i N_gamma,
```

where `N_gamma` is the number of zeros inside `gamma`, counted with
multiplicity. Hence

```text
Hol_gamma(nabla) = exp(2 pi i N_gamma) = 1.                (1)
```

This destroys the naive scalar-holonomy version of C2. The scalar connection
has nontrivial residues, but its exponentiated holonomy is only the integer
winding class and is trivial after exponentiation. If one uses the
non-exponentiated period, one recovers the argument-principle integer, exactly
the kill criterion named in the corpus.

Therefore the desired C2 class cannot be the ordinary scalar holonomy of
`d log xi`. It must live in a relative or enriched cohomology group that keeps
the continuous archimedean-prime splitting data while quotienting out the
integer divisor period.

## Weakened Theorem Proved Here

**Theorem C2-W.** The scalar line-bundle connection `d - d log xi` cannot be the
C2 carrier. Its closed-loop periods are integer multiples of `2 pi i`, and its
exponentiated holonomy is trivial on zero-avoiding loops.

Proof: equation `(1)` above.

## Constructive Next Shape

The right host should be relative:

```text
H^1(U, B; V) or H^2(G_L, V)
```

where:

- `U` is the zero-punctured strip or an adelic/Bohr boundary space;
- `B` is the critical seam or the boundary datum supplied by `Gamma`;
- `V` remembers the affine split `A + P`, not merely the scalar sum;
- ordinary divisor winding maps to zero or to a separately accounted summand.

The candidate class is then not `d log xi`, but the failure of the split pair
`(A, P)` to be globally trivialized relative to the seam.

## Where The Full Proof Fails

The corpus has not supplied the exact base space, coefficient module, relative
boundary map, or comparison theorem that identifies the empirical carrier with
that cohomology class. Without those definitions, C2 cannot be promoted beyond
the no-go above.

## Missing Input

1. Define the affine weld bundle and admissible gauge group.
2. Define the relative seam boundary condition imposed by `Gamma`.
3. Prove the carrier class is nonzero away from the seam and trivial on the seam.
4. Prove the class is not the argument-principle winding number.
