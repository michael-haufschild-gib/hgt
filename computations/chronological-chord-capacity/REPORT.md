# Chronological chord capacity: computational leads

Exploratory numerical work, 2026-09-05. Results are not proof certificates. Scripts ran on the authorized Runpod (`157.157.221.29:27094`, directory `/root/chronological-chord-capacity`), with 24 Python workers and one BLAS/OpenMP thread per worker. Environment: 32 available CPUs, NumPy 1.24.4, SciPy 1.10.1. Source and result JSON files are retained here.

## Question and method

For a pairing D of ordered endpoints, put `P_D(d)=∏_(i,j in D) Σ_(i≤k<j) d_k`, with variation budget `Σ|d_k|=1`.

`search.py` tested all 121 nonzero ternary coefficient vectors up to overall sign in the five-dimensional noncrossing basis on six endpoints. Each of 32 seeds sampled 72,000 positive and 72,000 signed Dirichlet increment vectors (concentration 0.3). Twelve coefficient vectors with the strongest apparent signed advantage received constrained SLSQP refinement, with analytic gradients, all 16 sign patterns modulo overall sign, and both objective signs. Output: `results.json`.

`basis_probe.py` tested the stronger conjecture `Σ_D |P_D(d)|/cap(D) ≤ 1`, for all noncrossing pairings on 4–12 endpoints. Individual-diagram capacities were supplied by a recursive interval-product formula using rational arithmetic; that implementation is part of the exploratory model, not a formal certificate. For each chord count, six seeds and both sign classes used 2,500 Dirichlet samples and SLSQP refinement from the 12 strongest samples. Output: `basis-results.json`.

## Outcomes

The first experiment found no resolved advantage from signed probe motion. This finite search establishes no equality theorem, and the full signed-versus-monotone question remains open.

The normalized-basis conjecture failed decisively from three chords onward. Best numerical values, rounded:

| Chords | Observed maximum |
|---|---:|
| 2 | 1.000000 |
| 3 | 1.132006 |
| 4 | 1.410792 |
| 5 | 1.896740 |
| 6 | 2.690254 |

These are local numerical optima, not certified global maxima. Signed sampling did not improve the best monotone value at reported precision. Small errors above 1 in degree two are floating-point effects.

## Exact mathematical consequence

The three-chord result suggested the two-term combination `27D+R`, where `D=(01)(23)(45)` and `R=(05)(14)(23)`. At gaps `(1/3,0,1/3,0,1/3)`, cost is exactly 1 and response exactly `10/9`, disproving the proposed bound without numerical inputs.

Independent symbolic reasoning then gave the global optimum: `q=(50-√313)/81` and `K=27q(1-q)²/4+q²`. Gaps `((1-q)/2,0,q,0,(1-q)/2)` attain K. Triangle inequalities, endpoint AM–GM, and a factored cubic optimality gap prove the upper bound for every signed gap vector. This exact argument is checked in `formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor/SixPoint.lean`; no JSON data or optimizer output enters Lean.

Further reasoning resolved the existence of signed advantage outside the first experiment's ternary coefficient class: `27D-R` has monotone capacity exactly 1, while gaps `(1/3,0,-1/3,0,1/3)` give `-28/27`. This is checked independently in `ChronologicalTensor/Reversal.lean`. It is not an output of either search.

Useful next questions concern composition across independent blocks and how nesting suppresses reversal-sensitive response. The degree 4–6 numerical values remain leads only.

## Illustration

`plot_geometry.py` renders the proved formulas and the two explicit probe histories, without optimization. It ran on the same Runpod using Matplotlib 3.7.5 installed into the task's `plot-deps` directory. Downloaded outputs are `geometry.png`, `geometry.svg`, and `geometry.pdf`. The first panel shows the positive coefficient quadrant; the second shows the monotone response curve and its exact supporting line; the third compares equal-budget probe histories. This illustration supplies no further proof evidence.
