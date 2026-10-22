# Original retarded field in the admitted causal source pairing

Full temporal/metric/QNM matching remains the target. The corrected future
field's complete weak source equation is proved in ES. The original retarded
field already has actual metric/current identities. The admitted retarded
source-event integral used in reciprocity must be identified with that field.

[BRIDGE] Lean proved, for all real `p=tau+x`, `r=tau-x`:

```
retardedResponse(q,branch,a,tau,x,X,k)
  = fullNullResponse(q,physicalRate(q,branch),a,p,r,X,k).

originalPotential(p,r) - correctedFutureField(tau,x)
  = retardedResponse(tau,x) - response(tau,x) + capBoundaryField(tau,x).
```

The first equality retains the full theta-square kernel, original
smooth onset, both Dirichlet terms, and the null-coordinate Jacobian.
The second equality then identifies the causal difference with the actual
retarded field underlying the existing metric/current results.

**Proof:** the odd full-line source folds to the original negative-ray
direct-minus-image density. Under the null chart
`(a,b) -> ((a+b)/2,(a-b)/2)`, the exact measure pushforward is `2*volume`.
Original onset annihilates negative source characteristics; causal support
restricts the remaining source to `Icc(0,p) x Icc(0,r)`. The transported
integrand is a continuous compact-rectangle density and therefore absolutely
integrable. Its integral, with the original kernel half-factor, is precisely
the existing full null response. If either null endpoint is negative the
rectangle is empty; the identity still holds.

**Exact admitted original-field pairing:** with `S_b` the original reduced
source coefficient and `U_c` the corrected future field,

```
causalSourcePair(b,c) = integral S_b*(originalPotential_c-U_c-cap_c).
```

This integral is absolutely convergent on the complete original source-event
domain. In particular, switching from the reduced future response to the
corrected future field leaves an explicit cap contribution.

**Positive reconstruction:** the same admitted retarded event inverse equals
`-timeAngularSeedField/kappa + retardedNullAction(fullSourceOnsetPulse)/kappa`.
The corpus's original pulse is supported in ingoing time `[0,1]`; this does
not make it compact in the radial variable. The corresponding future
identity and its independently specified cap are fixed in
[the future reconstruction card](hb-eu-future-onset-pulse-reconstruction.md).

Source evidence: `FullSourceRadialReciprocity` supplies the absolutely
admitted event integral and reciprocity; `OriginalRetardedIdentity` supplies
the full null response's two original source triangles. General temporal
transposition supplies the exact null-chart volume transport.

An attempted direct identification of the retarded and corrected future
fields is not established: the latter has zero ingoing trace, whereas the
former has the independently constructed `horizonPotential` trace. No
nonvanishing or equality of that trace is inferred here. Generic wave
uniqueness found by deep search requires Hilbert-space membership and
boundary/Cauchy data not yet established for this comparison.

The causal difference identity is a required attachment, not full metric
or QNM matching. Cap contact, reconstruction and the noncompact physical
reader boundary action must still be proved for this difference.

**Formal status:**
[OriginalCausalDifference](../../../../../../formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMOriginalCausalDifference.lean),
namespace `RHTower.D4BMOriginalCausalDifference`:
`retardedResponse_eq_fullNullResponse`, `original_causal_difference`,
`original_field_pair_integrable`, `causalSourcePair_original_fields`,
`retardedResponse_onset_pulse`.
Scratch passed without errors or warnings. Exact leaf audit passed in
104.81 seconds, two jobs. Umbrella wired without a build. Global lint's
only error remains the pre-existing unrelated unwired
`ThetaCuspHawkingBMOnsetTransgressionHorizon`.
