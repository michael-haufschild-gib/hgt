# Combined Square-Test Positivity Is Insufficient

- **ID:** combined-square-test-positivity-insufficient
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** docs/consolidated/gpt/proof-route.md, Layer B square-test positivity
- **Statement:** Positivity of the combined shifted form `Q_0+Q_1` does not imply sectorwise positivity of `Q_0` and `Q_1`, even at every finite truncation order. The Layer B theorem cannot be weakened to an ungraded combined positivity statement.

## Goal

Block the shortcut

```text
Q_0[p] + Q_1[p] >= 0 for all p
```

as a replacement for the proof-route target

```text
Q_0[p] >= 0 and Q_1[p] >= 0 for all p.
```

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: unconditional theorem
  `HTGeometry.combinedSquareTestPositivity_insufficient` in
  `formal/GaloisForLFunctions/HTGeometry/HankelGuardrailConsequences.lean`;
  exact target build passed and the capstone axiom audit reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Let

```text
a_n = 1 if n is even, and a_n = 0 if n is odd.
```

For each `d>=1`, define

```text
H_0^{(d)}=[a_{i+j}]_{i,j=0}^d,
H_1^{(d)}=[a_{i+j+1}]_{i,j=0}^d.
```

The matrix `H_0^{(d)}` is PSD for every `d`, since `(a_n)` is the moment sequence of `(delta_1+delta_{-1})/2`.

But `H_1^{(d)}` contains the leading principal submatrix

```text
[[a_1,a_2],[a_2,a_3]] = [[0,1],[1,0]],
```

so `H_1^{(d)}` is indefinite for every `d>=1`.

However

```text
H_0^{(d)} + H_1^{(d)}
```

has every entry equal to `1`, because exactly one of `i+j` and `i+j+1` is even. Hence `H_0^{(d)}+H_1^{(d)}` is the rank-one all-ones PSD matrix for every `d`.

Thus combined positivity does not imply sectorwise positivity.

Conversely, set `b_0=0` and `b_{n+1}=a_n`. Then the shifted sector `H_1` is PSD, the unshifted sector `H_0` is indefinite, and their sum is again the all-ones PSD matrix at every order. So either sector can hide a negative direction behind the combined form.

Applying this to the proof-route notation with `m_n=T_{n+1}` shows that one must prove the two shifted square-test forms separately:

```text
Q_0[p]=sum c_i c_j T_{i+j+1},
Q_1[p]=sum c_i c_j T_{i+j+2}.
```

## Computation

Validated through `d=8` in `computations/2026-06-21-penrose-proof-r10-graded-square-tests.py`.

Output archived at `computations/2026-06-21-penrose-proof-r10-graded-square-tests.txt`.

## Log

- 2026-06-21 -- created in 2-fully-proven from the SUSY-QM grading NODE. The external NODE was that ungraded spectra can agree while graded Witten indices differ; the proof-route transfer is that ungraded combined shifted positivity can hide a negative graded sector.
