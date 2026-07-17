# Mixed fundamental-solution flatness

- **ID:** `mixed-fundamental-solution-flatness`
- **Stage:** 2-fully-proven
- **Type:** EXACT MIXED-OPERATOR NECESSITY / CORPUS BRIDGE
- **Scientific status:** `[PAPER-PROVED] [PARENT DIFFERENCE-GALOIS THEORY]`
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

## Gates

- [x] 0 -> 1: exact necessary identity isolated
- [x] 1 -> 2: dependency-closed paper proof complete
- [x] existing commuting-operator and matrix-differential surfaces checked
- [x] converse and novelty boundaries made explicit
- [ ] 2 -> 3: unconditional Lean theorem batch
- [ ] targeted touched-file check
- [ ] formal lint and axiom audit

## Log

- 2026-07-17 -- Extracted as the exact mixed-compatibility residue of programme 5 after the
  proposed general Galois filtration conjecture was killed by the parent theory.
