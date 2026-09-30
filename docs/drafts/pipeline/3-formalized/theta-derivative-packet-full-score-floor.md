# Theta derivative packets preserve the complete first-atom score floor

- **ID:** THETA-PACKET-FULL-SCORE-FLOOR
- **Stage:** 3-formalized; exact joint compatibility capstone verified
- **Type:** THEOREM; source-class obstruction with positive stability survivor
- **Parent:** [actual-current route](../1-in-progress/li-actual-current-small-mass-sinc-scaling.md)
- **Prior work:** [dark divisor packets](../3-formalized/theta/theta-derivative-dark-divisor-packets.md), [polynomial score floor](../3-formalized/prime-arch-theta-polynomial-score-gap.md)

## Exact statement

Write `k=thetaCuspFullSource`, `L g=(1−303x²)g−16xg'`, and `f(x)=πψ_1(x)²(x−1)²`. For each integer `m≥1`, there is `ε>0` such that every `0<t<ε` gives

`L(k+t k^(4m))(x)≥f(x)` for every `x≥0`.

Thus every polynomial-square integral retains the complete prescribed floor, simultaneously, together with the existing positive, even, strongly log-concave packet, literal mass, moments below `4m`, entire transform `XiC(z)(1+t z^(4m))`, complete real divisor and added explicit off-axis zeros. The transform remains order one as a paper consequence of its exact polynomial factorization; growth order itself is not separately stated by the Lean capstones. This does not assert negative fixed third cumulant determinant, preservation of the critical zero strip, half-charge, integer Gaussian assembly, or exact Euler membership.

## Dependency-closed paper proof

Actual slack `E=Lk−f` is continuous and strictly positive on the complete half-line. Atomwise Born–Witten decomposition gives `Lk=πΣ_n[1+32xW_n−303x²]ψ_n²`. Every defect is at least `(x−1)²`. For `x≠1`, the second atom supplies a strictly positive surplus over the first-atom floor. At `x=1`, strict atom-index score order gives a strictly positive second-atom defect. At zero the second atom is positive too. Summability of actual source and its derivative justifies the complete-source identity.

For `h=k^(4m)`, all-order first-atom asymptotics give `h>0` eventually and `h'/h∼−2πe^(2x)`. Consequently `Lh>0` eventually: the positive `32πxe^(2x)` term dominates `303x²`. On the remaining compact interval `[0,R]`, let `e=min E>0` and bound `|Lh|≤M`. Choose `ε=e/(M+1)`. For `0<t<ε`, `E+tLh>0` on the compact interval and `E+tLh>0` on the tail. Linearity of `L` closes the global pointwise inequality. Polynomial-square integration is valid by the existing all-rate derivative decay and Gaussian first-atom bounds. Intersect this ε with the existing dark-divisor positivity/curvature interval.

## Strongest positive survivor

Strict source slack plus eventual nonnegative perturbation score yields a global compact/tail stability theorem; the complete floor survives an entire order-one divisor perturbation at fixed literal mass. This identifies an independent membership burden rather than proving the actual source has a bad divisor. Exact compatibility is now formalized; this is a source-class obstruction, not an actual-source or RH counterexample.

## Novelty and formal status

Existing `ThetaDerivativePacketSpectralBoundary.thetaDerivativePacket_dark_divisor` proves the original packet properties. The complete prescribed score-floor clause is absent from that capstone. Existing Gaussian–Hermite calibrated models address a different negative determinant and have order two. Generic density deletion positivity and all-sieve gauge rigidity are different constraints; packet perturbations need not lie in those rigid source classes.

Documented research query `theta derivative packet full polynomial score floor strict source slack off axis` completed with `partial=false`, complete 63060-file inventory, generation 1144491 (current 1144501); compiler evidence mostly pending/stale. It returned the original packet numerator/transform arguments and unrelated derivative forms, with no proof-idea or ingredient group. This is corpus evidence, not a world-novelty claim. Log: `/tmp/hgt-li-theta-packet-score-floor-research.json`.

## Plan

1. Actual complete-source strict slack and continuity — formalized in `PrimeArchThetaFullScoreSlack.lean`, with stronger bound retaining the entire strictly positive second-atom score. Named build, final exact check and all 14 public axiom audits passed.
2. Exact eventual positivity of derivative-packet score — formalized in `ThetaDerivativePacketScoreTail.lean`; actual slope limit is `h'/h+2πe^(2x)→8m+9/2`, and eventual score is at least `(1+16x)h>0`. Named build, final exact check and both public axiom audits passed.
3. Generic compact/tail stability — formalized in `ThetaScoreFloorCompactTailStability.lean`, with named build, final exact check and all three public axiom audits passed. Actual global pointwise floor and full dark-divisor joint capstone are final in `ThetaDerivativePacketScoreFloor.lean`: named build, final exact direct check and both public axiom audits passed. Raw all-j Ward law, finite-vector and polynomial-square integral identities are final in `ThetaDerivativePacketScoreMoments.lean`: all 11 public axioms foundational. Strict integrated receiver and full joint capstone are final in `ThetaDerivativePacketPolynomialScoreFloor.lean`: one common ε, every nonzero polynomial, all original packet properties. All five public axiom audits are foundational.
4. All six leaves passed named builds, final exact checks and all 37 public axiom audits. Root independently read source and evidence; separate hostile audit passed. Imports wired into `RHTower.lean`.

## Log

- 2026-09-30 — Independent source-membership audit closed paper compatibility; root checked original packet capstone and atom score certificate. Card recorded before new Lean work. Exact critical strip and arithmetic membership remain open.
- 2026-09-30 — Source proof exposed stronger survivor `E≥second-atom score>0` and positive defect for every atom after the first on the complete half-line. Root independently checked strict index-order proof and retained finite sum; this strengthening passes paper/Lean audit. Generic compact/tail stability is final. Packet tail leaf named build passed; final audit and coupled capstones pending.
- 2026-09-30 — Global pointwise floor and original dark-divisor properties hold at one common parameter interval in the exact joint capstone. Raw packet Ward and every signed finite polynomial form are formalized at literal factor two, for arbitrary real parameters. Final direct checks and all public axiom audits passed. Strict integral comparison receiver pending; keep stage two until its exact closure.

- 2026-09-30 — Strict polynomial comparison and exact joint capstone passed named build (13799 jobs, own leaf 142s), final exact check with empty log, and all five public foundation-only axiom audits. Independent audit confirms ε depends only on m, full raw factor two, no polynomial degree cutoff, and exact multiplicity increment `ord XiC+1`. Promoted to stage three. Growth order remains the stated paper consequence; critical-strip/Euler membership is absent.

## Verification evidence

- `/tmp/hgt-theta-packet-polynomial-floor-{build,direct,axioms}.log`
- `/tmp/hgt-theta-packet-score-floor-{build,axioms,direct}.log`
- `/tmp/hgt-theta-score-stability-{build,axioms,direct}.log`
- `/tmp/hgt-theta-full-score-{build,direct,axioms}.log`
- `/tmp/hgt-theta-score-tail.8XYuTt/{build,direct,axioms}.log`
- `/tmp/hgt-theta-score-moments.C3Zi9G/{build,direct,axioms}.log`
