# Full collar response of the normalized Weil trace

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The actual Riesz increment satisfies the complete collar equation. Its actual L² residual, divided by `sqrt(log(1/h))` and rescaled to the unit interval, converges strongly to the corresponding normalized endpoint trace.

## Proof

Let `u_z` be the old Riesz source and `B_b` the full bounded Weil remainder
in an enclosing aperture. The scalar term, finite prime translations of the
continuous source, and its two exponential polar profiles form a continuous
representative of `B_b u_z`. Subtract this from the evaluation exponential.
The exterior Gamma transfer supplies the remaining term. The resulting
literal profile is exactly the actual residual almost everywhere on each
collar. Subtracting the two Riesz equations gives its exact duality with the
kernel increment, independently of the chosen enclosing aperture.

The regular terms vanish after division by `sqrt(log(1/d))`. The exterior
Gamma term tends to the corresponding endpoint readout with the required
sign. The logarithmic ratio at `d=hs` has integrable squared majorant
`C(1+log(1/s))`, so the normalized profile converges in mean square.
Unitary dilation and literal indicator restriction identify this with strong
convergence of the actual L² residual. Consequently its collar mass divided
by `h log(1/h)` tends to the squared modulus of the endpoint readout.

The [actual endpoint traces](normalized-boundary-traces-of-weil-riesz-vectors.md),
[exterior Gamma identification](exterior-gamma-response-reads-the-weil-trace.md),
and [scaled mean-square theorem](scaled-exterior-weil-responses-converge-in-mean-square.md)
provide the analytic inputs.

## Lean

All modules belong to `CanonicalSystemOfTheWindowTower`; declarations below
are in `WeilHilbertBeforeContact`.

| Module | Main declarations |
|---|---|
| `ThePrimeAndPolarWeilResponsesAreContinuous` | `continuous_evalVectorRemainderProfile`, `evalVectorRemainderProfile_ae` |
| `TheWeilCollarProfilesHaveTheirExactBoundaryLimits` | `evalVectorRightCollarProfile_normalized_limit`, `evalVectorLeftCollarProfile_normalized_limit`, and both `*_scaled_mean_square` |
| `TheWeilKernelIncrementSolvesTheFullCollarEquation` | `inner_evalVectorIncrement_rightCollar`, `inner_evalVectorIncrement_leftCollar`, both `*_in_enclosure`, `evalVectorRightCollarResidual_ae`, `evalVectorLeftCollarResidual_ae` |
| `TheWeilCollarResidualsHaveTheirActualL2Limit` | `evalVectorRightCollarResidual_scaled_limit`, `evalVectorLeftCollarResidual_scaled_limit`, `evalVectorRightCollarResidual_mass_limit`, `evalVectorLeftCollarResidual_mass_limit` |

Plain Lean audits pass. Printed main dependencies contain only
`propext`, `Classical.choice`, and `Quot.sound`.
