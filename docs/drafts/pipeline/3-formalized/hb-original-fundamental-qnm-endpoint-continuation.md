# HB: original endpoint Green response at fundamental Xi QNMs

- **Stage:** formalized in Lean 4.
- **RH:** unproved; complete joint continuation, physical left pairing, and extinction remain open.
- **Scope:** the original native radial source family, including both actual endpoint
  moments, physical dressing, full connection normalization, and fixed smooth onset.
- **Frontier map:** read-only for this work.

## Exact closed statement

`RHTower.D4BMLaplaceRadial.continuedResponse_allXi_fundamental_meromorphic`
proves that the original source-forced radial Green response continues
meromorphically to both fundamental physical QNM frequencies for every Xi
multiplicity copy and every strictly interior radial point. Source amplitudes
and angular coefficients remain arbitrary and fixed. No RH, endpoint-integrability,
continuation, pole-incidence, or nonvanishing-numerator premise is supplied.

`continuedResponse_eq_original` proves equality to the literal Green response
with `onsetTransform(2*s,w)` in its original convergence chamber. Thus the
continued function is tied to the existing source and endpoint integrals.

More generally, `continuedResponse_meromorphicAt` applies to every fixed complex
angular parameter on

`Im w != 0` and `Re w > -2`.

This is a radial response continuation. It does not identify the complete joint
operator's continued response or its physical left residue. Meromorphy does not
assert that a pole survives the source numerator.

## Actual endpoint construction

Write `H` and `N` for the original horizon and normalizable solutions, `C(w)` for
`connection(w,chi)`, and

`F(w,t) = gaussFactor(w,chi,false,t) * sourceRemainder(s,w,a,J,K,1,t)`.

The exact original horizon-source integrand is `t^w F(w,t) T`. The source onset
and the full Wronskian normalization are independent of the integration variable.
The continued unnormalized horizon moment is

`M_H(w,b) = F(w,0) b^(w+1)/(w+1) + integral_(0,b] t^w (F(w,t)-F(w,0)) dt`.

The removed source coefficient is restored exactly. A locally uniform bound
`|F(w,t)-F(w,0)| <= A t` proves absolute convergence of the remainder for
`Re w > -2`. On a frequency ball with `Re w >= beta > -2`, its norm is bounded by
`A t^(beta+1)`. The existing Cauchy-dominated integral theorem proves frequency
holomorphy. For `Re w > -1`, the elementary complex-power integral proves equality
with the original unsplit horizon moment.

The Gauss contribution to the uniform bound comes from the proved coefficient
majorant: after removing the constant term, the shifted majorant is summable,
and the full difference is bounded by a constant times `|t|`. The literal source
remainder has the exponential form with geometric height

`h(t) = log(1+sqrt(1-t))`,

whose actual derivative is

`h'(t) = -1/(2 sqrt(1-t) (1+sqrt(1-t)))`.

The source derivative is jointly continuous on each closed frequency ball times
`[0,b]`, for `b<1`. Compactness supplies one derivative bound, and the real mean
value theorem gives the required first endpoint difference estimate. No source
remainder estimate is assumed at the physical application.

The unnormalized outer moment is the genuine integral

`M_N(w,b) = integral_(b,1] N(w,t) sourceProfile(s,w,a,J,K,1,t) dt`.

It is entire in frequency. The outer Gauss argument lies in `[0,1-b]`, a strictly
smaller disk; its denominator parameter is the fixed `3/2`. Uniform Gauss bounds,
joint continuity of the other source factors, and the retained square-root
factor at the outer endpoint give a uniform integrable bound on every frequency
ball. The value at the actual outer endpoint is handled directly.

Both continued normalized moments retain

`T_cont(w) = 1/(w-2*s) + onsetCorrection(2*s,w)`

and division by `-C(w)`. The continued response is exactly

`N(w,b) M_H(w,b) T_cont(w)/(-C(w)) + H(w,b) M_N(w,b) T_cont(w)/(-C(w))`.

The existing fixed-onset transform identity proves agreement in the genuine
source convergence chamber. No endpoint term or source-tail coefficient is erased.

For an actual Xi spectral point `xi`, the fundamental Laplace QNM real parts are
`Im(xi)/2-5/4` and `-Im(xi)/2-7/4`, and their imaginary parts are
`-Re(xi)/2` and `Re(xi)/2`. The proved strict Xi strip and nonzero real spectral
coordinate put both in the continued domain. Higher overtones are not included
in this first-subtraction theorem.

## Files and audit

General leaves in `formal/GaloisForLFunctions/HTGeometry/`:

- `HypergeometricEndpointBounds.lean`
- `FirstEndpointMellin.lean`

Physical leaves in `formal/GaloisForLFunctions/RHTower/`:

- `ThetaCuspHawkingBMLaplaceSourceEndpoint.lean`
- `ThetaCuspHawkingBMLaplaceHorizonEndpointBounds.lean`
- `ThetaCuspHawkingBMLaplaceHorizonMomentContinuation.lean`
- `ThetaCuspHawkingBMLaplaceOuterEndpointBounds.lean`
- `ThetaCuspHawkingBMLaplaceOuterMomentContinuation.lean`
- `ThetaCuspHawkingBMLaplaceFundamentalContinuation.lean`

All eight individual canonical `lake build <module>` audits passed without
warnings. All 22 new public theorems passed scratch `#print axioms` with only
`propext`, `Classical.choice`, and `Quot.sound`. Sources total 719 lines. Sixteen
installed olean/ilean artifacts are byte-identical to the audited artifacts.
Every leaf is wired once into its theorem-area umbrella. The isolated audit
package used 3,990 existing own dependency oleans and built only eight new oleans.
No full or umbrella build ran. Development used foreground `lake env lean`
checks, with one owned Lean/Lake process at a time. No numerical experiment or
computational proof certificate was used.

Repository-wide `formal_tools.py lint --check-generated` reported no errors in
these leaves and no generated-file drift. Its global gate remains unclean due
to concurrent unwired `SelbergOneSidedCurvatureDecay` and
`SelbergScalarHorizontalAverage`; it also reported 141 existing large-file
warnings. Those concurrent sources were preserved.

## Remaining physical obligation

The complete causal source includes the native residual and three cutoff
commutators. Its `cutoffRadialCoefficient` contains the original principal Green
response minus the full-square lift. Continue those actual coefficients and
retain the resulting source terms in the correct joint angular/radial domain.
Then identify the complete joint response's continuation and physical
advanced/adjoint left residue, the retained spin-two/AIME coefficient, and an
independent Hawking-clock extinction law. Those are still open. Further Taylor
orders would extend the radial statement to higher overtones if needed; that
extension would not itself supply the missing left pairing or extinction.
