# Theta C5 intrinsic Riccati budget (2026-08-29)

Corpus search route: `ThetaCuspGlobalReflectedRiccati`, likelihood cumulant modules, intrinsic C5 local-minimum/acceleration modules, and strict fourth-Turan. Likelihood third-cumulant sign and global Riccati nonnegativity do not supply the needed upper bound; generic atom/likelihood local architecture was already formally refuted.

New Lean module: `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicRiccatiBudget`, wired into `RHTower.lean`.

For `r=exp(q)-1`, `s=t q1/r`, `b=t^2(q2-q1^2)/r`, `rho=t^3(2q1q2-q3)/r`, define
`P0=99s-123s^2+24s^4-51b+36sb+16s^2b-65b^2` and budget
`P0+100sr rho-8000t^4/r-25r(b+2s^2r)^2`.
At every intrinsic stationary point Lean proves
`5 t^2 * IntrinsicSecondOrderTuranCeiling = sourceDrop^4 * budget`.
Every intrinsic local minimum forces `budget>0`. Hence every modular-center C5 failure forces a negative intrinsic local minimum with strict Riccati overcompensation, strict fourth-Turan, and likelihood-tax overspend. Exact iff makes the live target C5-RB1: prove budget <= 0 at every negative intrinsic local minimum.

Full RH chain: C5-RB1 -> modular-center C5 -> still-open off-center/complement global source C5 -> literal source rank-four odd wall -> physical center-mixed rank four -> still-open higher packets/cofinal no-escape -> universal tilt-flux/TTF or Xi-Weil positivity -> RH. Rank four alone is not RH.

Verification: direct `lake env lean` passed; targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureIntrinsicRiccatiBudget` passed; axiom audit only `propext`, `Classical.choice`, `Quot.sound`. Formal lint reports only unrelated pre-existing unreachable modules. No computations used. Frontier map remained read-only.