# Complete joint-prime raw-energy selection

Exploratory floating computation, not a proof of PE4 or RH. No numerical
result is used in Lean. [Frozen protocol and exact consequence](../../../1-in-progress/ccm-fu-joint-prime-minimax.md).

## Question and outcome

Does selecting two primes jointly retain the original raw-energy ceiling
through complete prime exhaustion, and what signed interactions change
the choice from raw greedy? The policy was frozen before execution;
the ceiling and actual source were unchanged.

Both policies retained the factor-one ceiling at every selected cutoff.
Thus this screen shows no ceiling advantage over raw greedy. It does
expose changes of order and positive first steps compensated by a second
step, including a genuinely interacting audited state.

| Cutoff | All primes processed | Raw greedy peak / diagonal | Joint peak / diagonal | Joint choices abandoning current greedy | Positive first, nonpositive total pair gain |
|---:|---:|---:|---:|---:|---:|
| 512 | 97 | 1 | 1 | 3 | 3 |
| 1024 | 172 | 1 | 1 | 4 | 1 |
| 2048 | 309 | 1 | 1 | 10 | 4 |
| 8192 | 1028 | 1 | 1 | 25 | 10 |

Peaks include the initial state. Complete paths, every one-prime prefix,
selected pair data, and terminal energies are in [summary.json](summary.json).
The strict failure threshold was `1e-10 max(1,Q_empty)`; no crossing
occurred. The initial diagonal remains the original sum of source squares.

## Source and selection

`source_screen.py` is an unchanged copy of the previous exact-label source
generator. It constructs the squarefree Möbius divisor coefficients

    C_d = mu(d) sum_{k=d}^{M-1} (sqrt(k+1)-sqrt(k)) D(floor(k/d)),
    D(n) = log(n!) - sum_{j<=n} floor(n/j) + 2 gamma n.

The screen evaluates this by quotient blocks in binary64. It retains all
literal residual prime-factor labels. For every unused pair p,q, it scores
`max(min(Q_p,Q_q),Q_pq)`, followed by endpoint, smaller first energy, and
increasing unordered prime pair. It then executes both primes in the
better order before rescoring. The raw greedy control chooses the least
one-step raw energy. A final odd prime is processed normally.

The pair scoring uses the exact mixed identity
`Q_pq-Q_p-Q_q+Q = 2 sum_r (F_r F_pqr + F_pr F_qr)`.
Sparse products compute cross-child terms; explicit incidences retain the
joint child. Every selected successor is regrouped directly, and the
identity is checked with tolerance `1e-8 Q_empty`.

## Independent audit and insight

The frozen no-failure branch selected the first changed choice at the
smallest such cutoff: M=512. `audit.py` independently factors the support,
reconstructs coefficients from the original time sum at 80 digits, and
evaluates all 1953 possible pairs by direct sequential fibre regrouping.
It does not use the sparse mixed-difference scoring formula.

The unique optimal unordered pair is {23,467}, ordered 467 then 23.
The gap to the next pair is approximately 0.01219118. Results:

| Quantity | 80-digit audit, displayed rounded |
|---|---:|
| Original diagonal | 311.55126938 |
| Current energy | 33.18633753 |
| Late prime 467 first | 33.33113423 |
| Middle prime 23 first | 33.59436116 |
| Common endpoint | 33.32187625 |
| Active nonscalar labels | 34 |
| Understatement from independent cofactor orders | 2.43415898 |

All candidate scores and signed cofactor entries are retained in
[audit.json](audit.json). The current head is negative (approximately
-0.46086347); the middle singleton is positive (1.32813697); the late
coefficient is negative (-0.15709283). The middle prime acts on nonempty
cofactors 5, 7, and 11 with mixed overlap signs. Both possible first steps
increase energy. Consequently selecting the better order independently
inside each cofactor produces an unattainable lower first-step value.

For this late/middle pair, the exact source laws reduce the genuine peak
gain to `max(min(-2fb,G), G-2(f+a)b)`, where f is the head, a is the middle
singleton, G is the complete middle gain, and -b the late coefficient.
The derived paper proof and subsequent Lean formalization classify the
continuous optimum and exact amplitude window for a prescribed budget.
They do not assert that an unused prime exists in that window at every
stage. This continuing source-supply and energy-budget problem remains
the obstruction to an exhaustive proof.

The 80-digit audit is not interval arithmetic. It checks one selected
state and all its candidate pairs, not all screen states at 80 digits.
Finite passing paths cannot prove an all-cutoff ceiling or exclude a
failure of either policy elsewhere.

## Execution and reproducibility

- RunPod: supplied SSH host, 32 available CPUs; four worker processes.
- NumPy 1.24.4, SciPy 1.10.1, mpmath 1.3.0.
- BLAS/OpenMP/MKL each restricted to one thread per worker.
- Successful screen: 2.7791 seconds. Independent audit: 0.2145 seconds.
- Each job had a 90-second internal deadline and 100-second outer timeout.
- Initial screen attempt exited after 2.6186 seconds because a NumPy
  boolean was not JSON serializable. Only output boolean conversion was
  changed before the successful rerun. [failed-attempt.json](failed-attempt.json)
  preserves its metadata; it contains no completed cutoff results and is
  not mathematical evidence.
- Downloaded scripts and results match remote SHA-256 hashes. Owned jobs
  terminated before cleanup. No local mathematical computation was run.

Run the scripts only on the authorized RunPod, in a fresh owned directory:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 timeout -k 5s 100s python3 screen.py
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 timeout -k 5s 100s python3 audit.py
```

SHA-256:

```text
f13ceff8657f7f93277c66ff28f5d80780afec37f7f394d136c9da55f8899541  screen.py
77bcc9058e05d01f20fdbe49536ab800b5a046512324cb2e5e2605cde2313427  source_screen.py
38b0ba82a69ad2df8bfaff2120c3524bd9c39f3d8048e48fa171e076f514a2e2  audit.py
9e92190b41a7339ea9fb1702b0955e5e18f9489990c9c114c9153a5c8f22445f  summary.json
9fe639a0fff27174893c8f244c93baafb2c535e396e8e517bf97172d93a80232  audit.json
```
