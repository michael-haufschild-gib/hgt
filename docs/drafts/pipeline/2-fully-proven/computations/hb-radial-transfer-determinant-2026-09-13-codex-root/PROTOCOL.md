# HB radial transfer determinant: frozen protocol

Status: frozen before computation. Numerical falsification experiment; no Lean theorem and no claim about an actual Xi zero.

## Question and object

The four literal first-subtracted fundamental radial moments form the matrix

`A(rho)[branch,side] = M(rho,branch,side)/(2 B(3,w+1))`,

with exactly the source polynomial and endpoint subtraction specified in the existing fundamental-source definition. Does `det A` vanish for a spectral control `0.01 < Re rho < 0.99`, `0.1 < Im rho < 80` even though the matrix entries need not vanish? A zero would exhibit a source-amplitude combination invisible to both radial readers and kill any identification argument based only on availability of one nonzero channel. It would not identify the physical superposition, full action, or an actual Xi zero.

## Prediction audit

Individual channel zeros are known numerically, but they do not determine determinant zeros. Generic dimension counting is inconclusive: `det A` is one complex equation in two real variables, yet branch reflection and retained endpoint terms impose non-generic relations. No sign, factorization, symmetry, or zero-count theorem determining the answer was found. Outcome is not honestly predictable.

## Experiments and interventions

1. Discovery representation: hypergeometric continuation of all four complete moments; argument-principle screens on a fixed 8-by-20 tiling, using 32 and 64 samples per edge at 60 digits.
2. Independent representation: endpoint binomial series for the same four moments on the low 4-by-8 tiling, using 16 and 32 samples per edge at 70 digits. It does not call a hypergeometric evaluator.
3. Every discovered candidate: 60/100/160-digit root refinement; local contour; derivative; both singular values; explicit right-null source mixture; both reader residuals.
4. Boundary intervention: decompose every matrix entry into retained base-period and endpoint-boundary parts using the exact `E M = 2(P J0+Q)` identity. Re-evaluate determinant after deleting `Q`, but label this unphysical. This distinguishes a genuine complete-moment degeneracy from boundary-induced cancellation.
5. Controls: nonzero shifted anchor, implementation identity between hypergeometric and endpoint-series values, matrix reconstruction from base plus boundary, and both individual rows/columns at each determinant root.

## Falsifiers, gates, and consequences

- Candidate rejected unless both representations converge to same interior root, full determinant residual decreases at 60/100/160 digits, local winding is one, and matrix null residual is small while at least one entry is nonzero.
- Discovery and independent total contour counts must agree on their shared low rectangle. Disagreement is reported unresolved; mesh is not tuned.
- A validated zero falsifies strip-wide invertibility of this radial transfer matrix. Positive salvage: classify boundary dependence and surviving orthogonal source mixture.
- No zero yields only bounded numerical evidence, not a zero-free theorem.
- Angular coefficient, fixed onset, SS/SV/VV amplitudes, original causal corrections, contacts, full Einstein action, and spacetime faces remain unknown, never replaced by zero.

## Budget and execution

Each pod gets a unique `/tmp/codex-root-hb-radial-det-*` directory. Maximum 14 workers, one library thread each, one 570-second guard per pod, no detached jobs. Preserve partial rows on timeout. Stop this family after frozen validation; do not enlarge height merely to obtain a result.

Scientific-method mechanics: split channels; attack invertibility as false; change representation; mix branch/reader and boundary interventions; perturb roots; seek positive residue after obstruction; keep implementation validation separate from discovery.
