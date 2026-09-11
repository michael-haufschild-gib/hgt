# PW-B convergent endpoint moment series: excluded shortcut

- **ID:** PW-B-CONVERGENT-ENDPOINT-MOMENT-SERIES-2026-09-11
- **Status:** Negative statement and positive survivor closed in Lean; all targeted leaf builds and formal lint passed.
- **Scope:** Convergence of the power series with the actual endpoint moments as coefficients. PW-B is not retired; RH is not proved.

## Exact obstruction

Let J_k(z) be the actual complete reciprocal-source integral in the
[high-order moment theorem](../3-formalized/pw-b-gamma-moment-detector.md).
For every complex z and nonzero complex w,

`J_k(z)*w^k` does not tend to zero as k tends to infinity.

Consequently the power series `sum J_k(z)*w^k` cannot converge at any
nonzero argument. The shifted tail with coefficients B_(k+2)=J_k has
the same obstruction. This rules out a convergent-power-series
shortcut for the proposed endpoint coefficient extraction.

Proof: if these terms tended to zero, multiply them by
`(1/w)^k/(k+1)!`, which tends to zero because factorial decay beats
every fixed geometric factor. Their product is J_k(z)/(k+1)!, so
that sequence would tend to zero. Its actual limit is the nonzero
coefficient `-sqrt(2)*exp(-z*log(2))`, a contradiction.

## Strongest positive survivor

Every J_k(z) is still an absolutely admitted original-source integral,
with exact complete signed-series equality. Gamma normalization recovers
the nonzero first coefficient, so every sufficiently high moment is
nonzero for each z. These are dependency-closed paper and Lean proofs
in `ThetaCuspHawkingParikhWilczekGammaMobiusMomentDetector`; its targeted
build passed in 175 seconds. The positive kernel substitution and bounds
in `ThetaCuspHawkingParikhWilczekGammaReciprocalMoments` passed their
61-second targeted build.

The surviving [finite asymptotic expansion](../3-formalized/pw-b-gamma-reciprocal-cutoff-expansion.md)
is now proved at every requested order, retaining the original near response,
removed moments, finite far remainder and source loss. The subsequent
[finite-order current classification](pw-b-corrected-gamma-scalar-occurrence.md)
proves a nonzero rescaled limit at every parameter and excludes the specified
corrected scalar equation. All three new leaves passed scratch and targeted
builds. No separate Lean analyticity or nonanalyticity theorem is asserted.

## Verification and corpus transfer

`ThetaCuspHawkingParikhWilczekGammaMomentDivergence` contains the exact
term-decay obstruction and nonsummability theorem. Scratch passed with
exit code 0 and no diagnostics; one umbrella import is wired. The targeted
leaf build passed in 76 seconds; formal lint passed. No numerical experiment or
axiom-print check was used.

The cutoff deep search suggested `HasFPowerSeriesWithinOnBall` geometric
approximation, whose analytic-series premise is not available here. Its
other generated finite-geometric/cutoff plan did not retain the actual
moving diagonal or logarithmic loss. The earlier corpus factorial-decay
argument in `FuchsFloorNoGo` supplied the applicable mathematical idea;
the proof uses the actual mathlib `FloorSemiring.tendsto_pow_div_factorial_atTop`,
verified against this toolchain, without importing that broad module.
