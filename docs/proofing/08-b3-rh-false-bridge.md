# B3 Proof Attempt: RH-False Bridge

Source: `docs/consolidated/08-conjectures-required.md` §2.

Claim status: `[CONJECTURE]`.

## Target Claim

```text
off-line zero <=> off-seam source-carrying transport defect.
```

The forward direction is detection. The reverse direction says every
source-carrying off-seam defect comes from an off-line zero.

## Proof Attempt

If "source-carrying" is defined strictly as nonzero local mass of the divisor
current

```text
mu_xi = (1 / 2pi) Delta log |xi|,
```

then the equivalence is tautologically true:

- nonzero source mass off the line means a zero of `xi` off the line;
- an off-line zero contributes a positive atom to `mu_xi` off the line.

In contour form, a source-carrying defect in a small off-line neighborhood `U`
means there is a loop `gamma` in `U` with

```text
(1 / 2pi i) int_gamma d log xi != 0.
```

By the argument principle, `gamma` encloses a zero. Since `U` is off the line,
that zero is off-line. Conversely, an off-line zero has such a loop.

## Weakened Theorem Proved Here

**Theorem B3-W.** If "source-carrying off-seam defect" means nonzero divisor
measure or nonzero local logarithmic contour charge of `xi`, then

```text
off-line zero <=> off-seam source-carrying defect.
```

Proof: argument principle and the definition of the divisor measure.

## Why This Does Not Prove The Intended B3

The theorem above makes B3 true by definition, but then it carries no
confinement information. It only translates "zero off the line" into "source
charge off the line." The light-tower claim wants empirical defects such as
reset maxima, Berry imbalance, survivor spines, and phase-space vortices to be
equivalent to source charge. That equivalence is not established.

## Missing Input

1. A defect category broader than divisor atoms but narrow enough to exclude
   random artifacts.
2. A theorem that every empirical off-seam defect is source-carrying exactly
   when it has nonzero logarithmic residue.
3. The B2 confinement theorem; without it, the contrapositive does not imply
   RH.
