# The critical Bessel outgoing slope has both signs

- **ID:** SELBERG-ALWAYS-POSITIVE-BESSEL-SLOPE
- **Stage:** 5-failed, the all-positive-coefficient conjecture only.
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 14.

## Tested conjecture and failure

Replacing the elementary Hardy coefficient by the actual critical Bessel mode might make the outgoing seam coefficient nonnegative at every positive frequency and height.

The actual coefficient is `(q(k*Y)-1/2)/Y`, where `q(s)=s*K_1(s)/K_0(s)`. The source derivative and recurrence force `q` to have exact range `(0,infinity)` and strict monotonicity. It therefore has a unique half-value transition. Below that transition the coefficient is strictly negative; above it the coefficient is strictly positive. `outgoing_has_both_signs` proves both signs at every frequency.

This retires only universal nonnegativity of this coefficient. It does not disprove Selberg, a core-plus-cusp argument, or nonnegativity of a particular compact test energy. A negative coefficient does not by itself make the complete square-plus-seam energy negative.

**Subsequent strengthening, cycle 16:** explicit compact approximants now prove that the coefficient is the exact unit-trace energy infimum. Hence a compact negative-energy isolated-tail profile exists exactly below the transition. This is an existence result for suitable profiles, not a claim about every profile with that boundary trace and not an automorphic counterexample. [Sharp trace infimum and proof](../3-formalized/selberg-sharp-cusp-trace-infimum.md).

## Strongest positive survivor after second pass

The second pass proves the complete range and unique sign transition, with transition argument strictly between zero and one half, without a small-argument asymptotic. It also proves the exact compact C¹ cusp energy identity with all integrability obligations discharged. This improves the sufficient dimensionless tail cutoff from one half to the actual transition argument.

**New insight:** the exact Bessel response strengthens the tail estimate but concentrates the unresolved issue in low-frequency seam channels. Its signs depend only on frequency times cutoff height, suggesting a finite adverse-mode decomposition before coupling to the core.

**Paper status:** dependency-closed proof complete. **Lean status:** complete in `SelbergBesselBoundarySlope` and `SelbergBesselBoundaryEnergy`, with fifteen capstone axiom checks and passing serialized targeted builds. [Exact survivor and audit](../3-formalized/selberg-exact-bessel-boundary-energy.md).

## Live successor

Classify the finite set of adverse nonzero integer modes at fixed width and cutoff. Keep the core Schur coupling explicit; no positivity of that coupling follows from finiteness alone.
