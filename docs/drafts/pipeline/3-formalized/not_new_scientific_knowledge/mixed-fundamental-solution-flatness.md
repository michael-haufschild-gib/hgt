# Mixed fundamental-solution flatness

- **ID:** `mixed-fundamental-solution-flatness`
- **Stage:** 3-formalized
- **Type:** EXACT MIXED-OPERATOR NECESSITY / CORPUS BRIDGE
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [PARENT DIFFERENCE-GALOIS THEORY]`
  `[NOT NEW SCIENCE] [NOT AN RH RESULT]`
- **Source:** research programme 5 successor from
  `../../5-failed/operator-presentation-bounded-innovation-stabilization.md`
- **Statement:** A single invertible fundamental matrix solving compatible difference and
  differential systems forces the mixed zero-curvature identity.

## Exact theorem

Let `E` be a field with derivation `D` and automorphism `sigma` satisfying

```text
D(sigma(f)) = sigma(D(f)).                                  (1)
```

Let `A`, `B`, and `Y` be square matrices over `E`, with `det(Y) != 0`, and suppose

```text
sigma(Y) = A Y,                                             (2)
D(Y)     = B Y.                                             (3)
```

Then

```text
D(A) + A B = sigma(B) A.                                   (4)
```

Here `D` and `sigma` act entrywise on matrices.

## Paper proof

Apply `D` to `(2)` and use the matrix product rule:

```text
D(sigma(Y)) = D(A)Y + A D(Y) = (D(A) + A B)Y.
```

Apply `sigma` to `(3)` and use `(1)`:

```text
sigma(D(Y)) = sigma(B)sigma(Y) = sigma(B)A Y.
```

The left sides are equal by `(1)`.  Right-multiplication by `Y^(-1)` gives `(4)`.  There is no open
core.

## Exact boundary

This is only the elementary necessary direction.  It does **not** claim that differential
algebraicity of an arbitrary solution produces `B`, nor that `(4)` classifies reducible systems.
Those converses are parameterized difference-Galois theorems with precise hypotheses; treating
them as consequences of finite presentation would repackage the parent theory.

The result is nevertheless a useful corpus interface: any future source-specific programme-5
argument which proposes a finite compatible mixed linear state can now be required to exhibit the
actual `B` and discharge `(4)` exactly.

Primary parent source: C. Hardouin and M. F. Singer, *Differential Galois theory of linear
difference equations*, Math. Ann. 342 (2008), 333--377,
`https://singer.math.ncsu.edu/papers/differential_for_difference.pdf`.

## Lean theorem surface

Module: `formal/GaloisForLFunctions/HTGeometry/MixedFundamentalSolutionFlatness.lean`.

- `matrixDifferential_mul`
- `matrixDifferential_map_differenceAut`
- `mixedConnection_flatness_of_fundamentalSolution`

## Gates

- [x] 0 -> 1: exact necessary identity isolated
- [x] 1 -> 2: dependency-closed paper proof complete
- [x] existing commuting-operator and matrix-differential surfaces checked
- [x] converse and novelty boundaries made explicit
- [x] 2 -> 3: unconditional Lean theorem batch
- [x] targeted touched-file check
- [x] touched-slice formal lint and axiom audit

## Log

- 2026-07-17 -- Extracted as the exact mixed-compatibility residue of programme 5 after the
  proposed general Galois filtration conjecture was killed by the parent theory.
- 2026-07-17 -- Promoted to Stage 3 after direct cached compilation.  `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  The project lint reports no proof debt or
  reachability defect for this module; its nonzero repository-wide exit is an unrelated pre-existing
  umbrella-reachability baseline.
