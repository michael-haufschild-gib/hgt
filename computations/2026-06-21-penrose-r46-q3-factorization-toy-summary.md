# R46 - Q3 factorization toy

Status: dead end / generic toy separator only.

Random source chain:
- seed RandomNode: correlations between beta and dynamical variables can invalidate simple mixture models
- broad topic RNG: 12, non-Markovian renewal processes with coupled waiting times
- NODE RNG: 4, coupled waiting times can break the usual factorization of multi-time probabilities
- target-file RNG: 1, `docs/consolidated/08-conjectures-required.md`
- target-topic RNG: 14, `C-2026-06-18-018 (Q_3 / higher-Chowla)`
- scientific-method RNG: 1, split subclaims
- perturbation-method RNG: 14, weaken

## Transfer

The NODE maps cleanly to the Q3 motivation:

```text
Q1 / pairwise PSD / factorized renewal data can be fake-blind.
Q3 / third cumulant / higher-Chowla data can see joint coupling.
```

The subclaim split is:

```text
A. Q3 can separate a fake family invisible to Q1.
B. The source-built Q3 index equals kappa_- for xi data.
```

The experiment only supports A.

## Evidence

Script:

```text
computations/2026-06-21-penrose-r46-q3-factorization-toy.py
```

Use the standard parity construction: choose `X,Y` independent signs and set
`Z=XY`. Then all singles and pair moments match independent fair signs, but
the triple moment differs.

Exact check:

```text
parity singles: [0.0, 0.0, 0.0]
parity pair moments: [0.0, 0.0, 0.0]
parity triple moment=1.0
```

Monte Carlo check:

```text
independent:     Q1_pair_error=0.003735, Q3_triple_moment=-0.001420
parity_coupled:  Q1_pair_error=0.002560, Q3_triple_moment=+1.000000
```

## Verdict

Dead end for non-reducing count. The weakened result is only a generic
pairwise-independent/not-jointly-independent toy. It illustrates why Q3 is a
plausible first fake separator, but the proofing worklog already names the
real obstruction:

```text
define source-built Q3 and prove its index equals kappa_-
```

This run supplies no such formula and no faithful-index readout.
