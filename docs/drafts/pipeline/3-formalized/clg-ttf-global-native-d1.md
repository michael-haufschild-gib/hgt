# Unconditional global native theta D1

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** `∀ x≥0, thetaCuspFullReflectionEighthHankelCurvature x > 0`.
- **Capstone:** `RHTower.thetaCuspFullReflectionEighthHankelCurvature_pos_on_nonnegative` in `ThetaCuspFullReflectionEighthGlobal`.

## Dependency-closed proof

The literal modular differential system gives `−1≤S≤0`, `17≤A≤20`, and `0≤W≤14x≤1` on `0≤x≤137/2000`. The tighter shear bound is `thetaCuspModularTransverseShear_le_one_on_compact` in `ThetaCuspModularCompactTube`.

Set `u=−S`, `t=A−17`. The full 540-monomial polynomial, with no source truncation, is exactly `sum_j p_j(u,W)t^j`. On the unit square, each negative monomial is bounded using `u^i W^k≤1`; every discarded monomial is nonnegative. Exact symbolic bounds are `p_0≥10^9`, `p_3≥10^6`, `p_4≥−14000`, and `p_j≥0` for every other degree. Since `0≤t≤3`, the cubic reserve pays the quartic loss. `HTGeometry.modularThetaCompactD1_lower_on_tight_box` proves the complete polynomial at least `10^9`.

The exact positive-mass modular identity transfers this sign to the raw source determinant, and the raw/native factorization transfers it to native D1. Existing seam and outer-source theorems cover zero and `x≥137/2000`. No unproved source-sign premise remains.

## RH scope

Full chain: completed theta source → Xi Bezoutian → every finite two-channel Weil packet positive semidefinite → RH. Global D1 closes one finite-rank source sign. The actual rank-three center mixture is also proved in `HedenmalmCenterMixedEighthHankelClosure`; uniform actual positivity for all sufficiently small distinct five-point clusters is proved in `ThetaCuspCenterMixedFivePointCluster`. Theta-specific general-packet incidence and cofinal no-escape remain. D1 alone proves neither completed C5 orientation nor RH.

## Verification

- Direct `lake env lean` checks passed for the new compact-reserve and global-source modules and the tightened tube.
- New compact-reserve and global capstone axiom audits return only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint` passed; generated corpus indexes refreshed; new modules wired into their umbrellas.
- The cascading targeted Lake rebuild was stopped at the user's efficiency instruction. No full build or umbrella build was run. Numerical explorations supplied no Lean premise or computational oracle.
