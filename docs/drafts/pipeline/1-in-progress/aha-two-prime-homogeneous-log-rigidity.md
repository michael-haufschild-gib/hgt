# Two-prime homogeneous logarithmic rigidity

- **ID:** AHA-LOG2
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** For distinct primes `p,q` and every fixed degree `T`, the `T+1` real numbers `(log p)^j (log q)^(T−j)`, `0≤j≤T`, are linearly independent over `ℚ`.

## Mechanism and scope

Factoring out `(log q)^T` turns a homogeneous relation into a polynomial
relation in `log p / log q`. Gelfond–Schneider supplies transcendence of
this ratio. This is qualitative nonvanishing at every fixed homogeneous
degree; it does not establish algebraic independence of `log p, log q`,
which permits relations mixing degrees.

The claim that the two-prime fixed-degree case itself requires full
algebraic independence in
`3-formalized/not_new_scientific_knowledge/friable-dirichlet-auxiliary.md`,
§5b–§6, requires this scope correction. The existing coefficient-surjectivity
theorems remain valid. Uniform inverse-power height bounds are separate
from qualitative nonvanishing and are not claimed here.

## Arithmetic application to audit

For algebraic-coefficient auxiliaries at algebraic torus points, Baker's
linear independence of prime logarithms should identify vanishing of the
first logarithmic-direction derivative with vanishing of every coordinate
Euler derivative. With two prime coordinates, homogeneous log independence
should extend this identification to every finite jet order. These analytic
applications require their own exact statements and Lean proofs.

## Leads

`RHTower/LadderNesting.lean` exposes
`GaloisForLFunctions.RHTower.primeLogs_algClosure_linearIndependent`.
`RHTower/GelfondSchneider.lean` exposes `log_ratio_transcendental`.
Check statements and transitive axioms before use. No new transcendence
theorem is asserted; the contribution is the corrected homogeneous boundary
and its arithmetic jet consequences.
