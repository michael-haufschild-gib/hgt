# R65 — two-clock transition affinity

**Verdict:** DEAD END / controls kill the strengthened statistic.

## Setup
- Seed RandomNode: `Fibril ends are usually the main sites of monomer recruitment and conversion`.
- STEP 1 cold list + STEP 2 rng `8`: topic `Nonequilibrium self-assembly`.
- STEP 3 cold list + STEP 4 rng `6`: NODE `Local detailed-balance constraints on transition rates in stochastic assembly models`.
- Standing-order target pick: file rng `3` -> `docs/consolidated/01-landscape-and-weld-geometry.md`; topic rng `17` -> Two-Clock layer.
- STEP 5 constraint: transition ratios/cycle currents matter, not just static state frequencies.
- STEP 8 selected transfer by Levenshtein: `local detailed balance becomes cycle current in phase-weld clocks` (`47`).
- STEP 9 method rng `15` = strengthen.
- STEP 11 method rng `22` = nearby false statements.

## Computation
Archive script: `computations/2026-06-21-penrose-r65-two-clock-affinity.py`.

The strengthened statistic built a four-state process from:
- finite-prime phase agreement with true `zeta'/zeta`;
- true phase-weld tension `Delta(A,P_true)`.

Cycle affinity results:

| sigma | window | finite affinity | random affinity |
|---:|---|---:|---:|
| 0.3 | 100-170 | -0.3414 | 1.3393 |
| 0.3 | 500-570 | -0.4520 | -1.2993 |
| 0.5 | 100-170 | 0.7098 | -0.0073 |
| 0.5 | 500-570 | 1.7692 | -0.1164 |
| 0.7 | 100-170 | -2.6739 | -0.2259 |
| 0.7 | 500-570 | -2.0229 | -0.6852 |
| 1.2 | 100-170 | -2.8426 | 1.9353 |
| 1.2 | 500-570 | 0.1685 | 0.5878 |

## Nearby False Statements
- False: nonzero two-clock cycle affinity is specific to finite-prime/true-clock coupling. Random controls can be larger.
- False: the statistic collapses cleanly on the Euler-convergent side. `sigma=1.2` still shows large finite/random affinities in one window.
- False: directed transition affinity upgrades the Two-Clock layer beyond known phase-carrier transition statistics. It is too sensitive to binarization and random phase controls.

## Reading
The detailed-balance metaphor is useful, but this particular cycle-affinity statistic is not a new native two-clock invariant.
