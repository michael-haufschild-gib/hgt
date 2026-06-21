# B2 Proof Attempt: The Two-Lemma Bridge

Source: `docs/consolidated/08-conjectures-required.md` §2 and
`docs/consolidated/03-theorems-toward-rh.md` §2.

Claim status: `[CONJECTURE + OPEN CORE]`.

## Target Claim

The bridge splits as:

1. Detection: an off-line zero creates at least one off-seam transport defect.
2. Confinement: all source-carrying coupled-lane measure-covariant defects are
   confined to `Re s = 1/2`.

Then RH follows.

## Lemma 1 Attempt: Local Detection

Let `rho = beta + i gamma` be a zero of `xi` of multiplicity `m`. Near `rho`,

```text
xi'/xi(s) = m/(s-rho) + g(s),
```

where `g` is holomorphic. Ignoring the bounded holomorphic term in a small
enough punctured neighborhood, the model detector has magnitude

```text
|m/(sigma + i t - rho)|
  = |m| / sqrt((sigma-beta)^2 + (t-gamma)^2).
```

For fixed `t != gamma`, this is uniquely maximized at `sigma = beta`. Therefore
if `beta != 1/2`, the local pole model creates an off-seam maximum.

The contour-charge detector is even cleaner: a sufficiently small loop around
`rho` has

```text
(1 / 2pi i) int xi'/xi ds = m != 0.
```

If `rho` is off the critical line, this is an off-seam source charge.

## Weakened Theorem Proved Here

**Theorem B2-W1.** Every off-line zero creates a local off-seam source detector
in two precise senses:

1. the pole-magnitude center is at `sigma = beta`;
2. a small loop around the zero has nonzero logarithmic contour charge.

This proves the local, source-level version of Lemma 1.

## Lemma 1 Remaining Gap

The corpus asks for more than the local detector: off-centre reset occupation,
observed-volume anomaly, signed-area defect, survivor spine, zero-shadow tear,
gate/tension seam, and Berry imbalance. The pole model strongly suggests these,
but each requires a statistic-specific theorem showing stability under the
holomorphic background term `g(s)` and under the chosen windowing procedure.

## Lemma 2 Attempt: Confinement

Suppose every source-carrying defect is represented by a nonzero local contour
charge of `d log xi`. Then Lemma 2 says all such charges are confined to the
critical line. But that is exactly RH in transport language. The functional
equation pairs charges across the line; it does not by itself force them onto
the line. An off-line pair at `beta` and `1-beta` is compatible with the
functional equation.

Thus FE symmetry alone cannot prove Lemma 2.

## Open Core

Lemma 2 needs a new global rigidity theorem:

```text
completed transport law + source-carrying condition
  => no off-seam contour charge.
```

No such theorem is currently present in the corpus.

## Missing Input

1. Statistic-specific global detection lemmas for each named transport defect.
2. A definition of "source-carrying" that excludes random artifacts but includes
   logarithmic residues.
3. A confinement principle stronger than FE symmetry and local pole geometry.
