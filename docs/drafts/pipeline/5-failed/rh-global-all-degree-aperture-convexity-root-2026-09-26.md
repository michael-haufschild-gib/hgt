# Global all-degree theta aperture convexity — falsified

- **Owner:** root; independent of other agents' cards and logs.
- **Stage:** 5-failed.
- **Type:** FALSIFIED auxiliary producer claim; no RH falsification.
- **Frozen claim:** for every `lambda<=0` and every degree `j`, the second degree difference
  `thetaCuspGaussianApertureRatioCurvature lambda j` is nonnegative.

## Exact killing theorem

`ThetaColdCorner.eventually_negative_theta_diagonal` proves, without input hypotheses,

`eventually n, thetaCuspGaussianApertureRatioCurvature (-(n+1/2)/9) n < 0`.

Here the displayed rate abbreviates the formal definition `coldRate 9 n`.
`not_all_degree_aperture_curvature_nonnegative` states the direct negation of the frozen claim.
Both use the literal complete theta source. This is stronger than a surrogate-source counterexample.

## Why the endpoint repair fails

Fixed-degree cold positivity and uniformly large-degree positivity on each compact aperture
interval leave the joint cold/degree corner uncontrolled. The cold starting time of a finite
section depends on its terminal degree. It cannot be replaced by one common initial condition.
The verified cooperative flow does not repair that quantifier gap by itself.

## Strongest positive survivor

For every `u>0`, let `L_n=(n+1/2)/u`. Then

`L_n^4*thetaCuspGaussianApertureRatioCurvature (-L_n) n
 -> (d^3/dy^3) log(thetaCuspFullSource(sqrt(y)))|_(y=u)`.

This is the exact signed incoming-profile law `tendsto_scaled_theta_curvature`, not a restatement
of the negative conclusion. It identifies the missing boundary as a local spatial logarithmic jet.
Original-source falling Euler derivatives provide the exact finite-difference dictionary, and
Gamma concentration supplies the joint limit. The literal profile is strictly negative for `u>=9`.

## Closure and scope

- Dependency-closed paper proof and exact Lean theorem:
  `../3-formalized/rh-cold-degree-corner-2026-09-26.md`.
- Final leaf: `formal/GaloisForLFunctions/RHTower/ThetaColdDegreeCornerLimit.lean`.
- Named build passes. All 39 public theorem audits across this turn's three leaves use only
  `propext`, `Classical.choice`, `Quot.sound`; no new axioms or placeholders.
- Retired: global all-degree convexity as a nonnegative-boundary maximum-principle input.
- Still open: degree-zero GABTC, signed corner influence on low degree, and RH.
- No numerical experiments; no global novelty claim. Other agents' logs were not changed.

**Whole route:** any replacement producer must retain the signed incoming boundary. Proving another
finite-section maximum principle or repeating the two separate endpoint limits cannot close it.
