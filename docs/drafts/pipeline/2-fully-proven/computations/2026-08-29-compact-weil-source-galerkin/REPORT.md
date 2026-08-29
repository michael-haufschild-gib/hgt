# Compact-Weil source-Galerkin computation report

Date: 2026-08-29  
Research card: `docs/drafts/pipeline/1-in-progress/compact-weil-source-galerkin-discriminator.md`

## Question

Can the literal source-side Connes--Consani--Moscovici restricted-Weil matrices reveal a
non-numerical sign mechanism for Route O? Two hostile conjectures were frozen before computation:

1. lowest even ground states have nonnegative, nonincreasing zero-extended autocorrelation (`C1`);
2. their autocorrelation weights make cumulative polar mass dominate von Mangoldt mass (`C2`).

No zeta zeros, RH assumption, or zeros-side matrix entered the campaign.

## Computations

### Published source matrices

`source_galerkin.py` assembles the published centered matrix from the polar, prime, and
archimedean terms. It uses Arb/FLINT at 220 decimal digits. The campaign covered all 66 pairs

- apertures `a = 0.34, 0.35, 0.54, 0.56, 0.69, 0.70, 0.8, 1.0, 1.2, 1.4, 1.6`;
- ranks `N = 8, 16, 32, 64, 96, 128`, hence matrices through dimension 257.

The pairs `0.34/0.35` and `0.54/0.56` straddle the first two prime-entry walls. Ground-state
autocorrelations were re-evaluated on a 65,536-point lag grid. Independent high-precision
quadrature checked the closed special-function entries.

Verification summary:

| Check | Outcome |
|---|---:|
| Formula versus independent quadrature, maximum error | `1.7263e-219` |
| Ground eigenpair residual, maximum | `1.2648e-219` |
| Polar + prime + archimedean component residual, maximum | `4.1354e-221` |
| Positive computed ground eigenvalues | 66 / 66 |
| Antitone computed rank sequences | 11 / 11 |
| Even-parity leakage in double post-analysis | `0` |
| `C1` negative cases below tolerance `-1e-10` | 0 |
| `C1` upward cases above tolerance `1e-10` | 0 |
| `C2` cumulative-deficit cases below tolerance `-1e-10` | 0 |

Small FFT-grid undershoots of the autocorrelation were about `1.7e-12`, below the declared
`1e-10` post-analysis tolerance and comparable to interpolation/rounding error. They are not
reported as mathematical positivity.

Representative rank-128 floors:

| `a` | smallest eigenvalue |
|---:|---:|
| 0.34 | `1.6097947e-3` |
| 0.35 | `1.1941055e-3` |
| 0.54 | `1.0661936e-7` |
| 0.56 | `2.7502031e-8` |
| 0.69 | `1.0141862e-12` |
| 0.70 | `4.2132207e-13` |
| 0.8 | `1.6960341e-17` |
| 1.0 | `6.4185336e-30` |
| 1.2 | `8.0058461e-49` |
| 1.4 | `1.7798778e-77` |
| 1.6 | `1.4088634e-118` |

Ranks 96 and 128 are close at the smaller apertures, but not at `a = 1.6`: their ratio is about
`2.03e8`. The last value is therefore far from a converged floor and must not be interpreted as
an asymptotic estimate.

Cancellation is severe. At `a = 0.8`, `N = 128`, ground-state component energies are

```
polar          +1.418302993851302478...
prime          -0.039249527995205549...
archimedean    -1.379053465856096912...
total          +1.696034051123909633...e-17
```

This explains why ordinary double-precision matrix assembly is not a meaningful sign test.

### Completed prime--polar error

`completed_error_scan.py` searches event minima of

```
E(x) = 2*(sqrt(x) - 1/sqrt(x)) - sum_{k <= x} Lambda(k)/sqrt(k).
```

The segmented sieve used multiprocessing, explicit higher prime powers, and compensated summation.
Because `E` increases between prime-power events and jumps down at events, it is enough to inspect
event values. A second `10^8` run used different segmentation and worker count.

| Limit | Primes | Higher prime powers | Least value after first atom | Final `E(x)` | Time |
|---:|---:|---:|---:|---:|---:|
| `10^8` | 5,761,455 | 1,404 | `0.9240844906` at `x=2` | `2.8670813066` | 0.33 s |
| `10^10` | 455,052,511 | 10,084 | `0.9240844906` at `x=2` | `2.2622184577` | 25.94 s |
| `10^11` | 4,118,054,813 | 28,156 | `0.9240844906` at `x=2` | `2.4982954009` | 377.16 s |

Reference prime counts and the independently segmented `10^8` scan were reproduced. No negative
event was found through `10^11`.

## Interpretation and route consequences

### What survived

`C1` survived every tested aperture/rank and is now the strongest new Route O conjecture. It is
not a generic autocorrelation fact: arbitrary compactly supported packets need not have ordered
autocorrelation. A proof must use the literal ground-state equation, likely through a
positivity-improving resolvent, total-positivity law, or a variation-diminishing property of the
source-selected even block.

`C2` also survived for all computed ground states. Post-first-atom cumulative margins were roughly
`1.10` to `1.44`, much larger than numerical noise. This is meaningful evidence for a
ground-specific weighted statement, not for pointwise positivity of `E`.

### What was killed

The tempting proof mechanism “prove `E(x) >= 0` globally, then integrate against every decreasing
autocorrelation” is dead. Suzuki records the Littlewood oscillation result for the weighted
Chebyshev deviation `psi_(1/2)(x) - 2 sqrt(x)`: it has both signs infinitely often. Endpoint and
half-jump convention changes between that deviation and `E` decay, so `E` also eventually takes
both signs. The very long positive range through `10^11` is therefore a finite-range bias, not a
new positivity law. See Masatoshi Suzuki, [On variants of Chebyshev's
conjecture](https://arxiv.org/abs/2411.07436).

This does **not** kill ground-specific `C2`. It kills only the universal raw-cumulative carrier used
to prove it.

### New sharpened route

The corpus already proves Stieltjes integration-by-parts formulas for the prime--polar quadratic.
For an ordered ground autocorrelation, the relevant quantity is an average of the sign-changing
completed error against the source-selected positive lag density `-dC`, plus explicit boundaries.
Route O should therefore ask:

> Why does the CCM ground equation select decreasing autocorrelations whose positive lag density
> averages the oscillatory completed error with the required sign?

This is substantially narrower than pointwise control of primes and is compatible with the known
sign changes. The next analytic attacks should try to kill `C1` by deriving the exact ground
integral equation and searching for a forced sign change of `C'`; failing that, prove a
variation-diminishing or positive-resolvent theorem for its even block. Separately, compare the
resulting `-dC` family with Suzuki's logarithmic averaging kernels, whose eventual sign has an
RH characterization.

## Unconditional Lean consequence

The finite packets seen computationally are now proved to form an exact principal tower:

- `ccmPublishedCenteredInclusion` preserves centered mode, clock, frequency, source, and diagonal;
- `ccmPublishedRestrictedWeilMatrix_apply_inclusion` preserves every matrix entry;
- `ccmPublishedRestrictedWeilMatrix_submatrix_inclusion` identifies the rank-`M` matrix exactly
  with the centered principal submatrix of every rank-`N` matrix for `M <= N`.
- `ccmPublishedRestrictedWeilMatrix_submatrix_succ` states the closed assumption-free successor
  tower law directly, with no inequality premise.

Module:
`formal/GaloisForLFunctions/RHTower/CCMPublishedRestrictedWeilPrincipalTower.lean`.

The proof is universal and imports no computed values. Targeted `lake env lean`, targeted
`lake build`, and `#print axioms` checks passed. Its axiom footprint is only Lean/mathlib's standard
`propext`, `Classical.choice`, and `Quot.sound`—no project axiom, premise, or RH assumption.

This closes exact finite-rank nestedness but not the major missing connector between the published
source matrix and the corpus's abstract convergent Laurent-Galerkin compression. That connector is
now the highest-value unconditional Lean follow-up.

## Reproduction and artifact guide

- `run_campaign.py`: 66-job matrix campaign; forks workers only after expensive imports.
- `source_galerkin.py`: high-precision source matrix and ground/autocorrelation calculations.
- `analyze_campaign.py`: 65,536-grid post-analysis and tables.
- `completed_error_scan.py`: multicore segmented completed-error scan.
- `verify_results.py`: cross-artifact integrity and consistency checks.
- `campaign-results/`: one full JSON record per aperture/rank.
- `campaign-summary.json`, `campaign-analysis.json`, `campaign-analysis.csv`: consolidated results.
- `completed-error-*.json`: completed-error scans, including endpoint/segment evidence.
- `verification.json`: final machine-readable verification verdict.
- `environment.txt`: remote runtime information.
- `SHA256SUMS`: local artifact hashes.

Relevant source construction: Connes--Consani--Moscovici,
[Zeta Spectral Triples](https://arxiv.org/abs/2511.22755). Computations are experimental evidence
only and are not dependencies of any Lean theorem.
