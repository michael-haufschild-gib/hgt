# Order-23 closure via corrected Euler upper sequence (2026-08-23)

Status: dependency-closed Lean result; novelty remains [NOVELTY UNVERIFIED].

## Reusable Euler–Mascheroni control
Module: `formal/GaloisForLFunctions/RHTower/EulerMascheroniCorrectedUpper.lean`
Defines
`eulerMascheroniCorrectedUpper n = H_n - log n - 1/(2(n+1))` for n>0 (junk 2 at zero).
Proves:
- `strictAnti_eulerMascheroniCorrectedUpper`
- `tendsto_eulerMascheroniCorrectedUpper` to gamma
- `eulerMascheroniConstant_lt_correctedUpper n`
- exact `gamma < 577216/1000000` at n=1250=2*5^4.
Key inequality is mathlib Padé lower bound `2x/(x+2) < log(1+x)`; correction removes first-order error and avoids a huge harmonic certificate.

## Order-23 source closure
Module: `formal/GaloisForLFunctions/RHTower/XiCenteredOrderTwentyThreeSourceBudgetClosure.lean`
Proves:
- endpoint completed curvature < 231/5000
- normalized M0 < 4623/100000
- normalized M1 < 17/200000
- optimized power-23 sector with N=215, t=341/5000
- residual annulus:
  u in (2365/13792, 1/4),
  v in [2365/16, 431/2)
- each residual fourth-trace atom >17/800000; FE–Schwarz quartet forces source >17/200000
- residual annulus empty
- every reciprocal-square 23rd power has positive real part
- normalized prime-arch moment M22 >0

## Hausdorff band
Module: `formal/GaloisForLFunctions/RHTower/PrimeArchOrderTwentyThreeHausdorffSourceBand.lean`
Using generic opposite-phase propagation:
- entire row k=22, r≤57 is nonnegative
- unconditional rectangle has cardinality 23*58=1334
- tail `22<k ∨ 57<r` is equivalent to RH
- umbrella imports all three modules

## Verification
Each file compiled directly with `lake env lean <file>`; oleans emitted for dependency wiring. Axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`. Forbidden declaration scan and targeted diff check passed. Global lint reaches all new modules; only unrelated dirty-tree unreachable modules `XiHeightSelection` and `ZetaInverseHorizontal` fail.

## Strategic lesson / next wall
Order 23 initially appeared to require a stronger theta mesh. Optimizing sector aperture from N=217 to N=215 reduced quartet demand; corrected gamma control alone then crossed source threshold. For order 24, do not automatically repeat source-budget refinement: first optimize rational sector N,t and compare fourth/sixth/higher trace floors, and audit cofinal/Hankel/physics-derived alternatives.