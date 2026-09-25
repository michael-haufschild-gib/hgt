# C1 scalar first-trace landing: hostile audit

## Question

Does current C1 global-mean Plücker carrier land its first scalar trace on
`thetaCuspNormalizedEvenMoment 1 / 2`?

This run is diagnostic only. No numerical value here is admissible in Lean.

## Computation

`run_experiments.py` directly transcribes current Lean definitions for hostile aperture,
adjacent prime/depth Plücker weights, cofinal normalization, squared reciprocal-gap nodes,
raw first moment, and occupation collision energy. It evaluates

`C1 trace = raw first moment - collision energy`

on four nested rectangles up to 100,000 adjacent-prime packets and depth 512. Target theta
moment is evaluated independently at 70 decimal digits. Production used 128 worker processes.

`verify_results.py` independently checks packet formulas with `mpmath`, evaluates theta target
again by 1,024-node Gauss--Legendre quadrature, checks trace decomposition, and checks nested
stability.

## Outcome

Largest rectangle gives:

- raw first moment: `0.04671688650578588`
- collision energy: `0.031083049941600622`
- C1 trace: `0.015633836564185256`
- theta target: `0.02310499311541897`
- difference: `-0.0074711565512337146`
- relative target error: `-0.32335679625231684`

Trace changed by less than `5e-17` from preceding 20,000-packet/depth-256 rectangle. Independent
verifier passed.

## Interpretation

Current scalar landing is overwhelmingly unlikely to be an equality. This attacks present
global-mean carrier, not every conceivable C1 carrier. Formal route kill still requires
computation-free strict inequality in Lean. Large margin suggests feasible proof by exact
head/tail bounds plus already formalized identity
`raw first moment - weighted occupation square`; no computed decimal should be imported.

Files: `results.json`, `run-output.txt`, `verify-output.txt`, scripts, environment record, hashes.
