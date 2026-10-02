# SZ: signed autocorrelation balance of the actual Abel source

- **ID:** sz-critical-source-autocorrelation-balance
- **Stage:** 5-failed (positive survivor formalized)
- **Type:** FALSIFIED positivity candidate; THEOREM (Lean) signed balance
- **Source:** MobiusDivisorCriticalLogProfile; route SZ in rh-current-frontier-map.md
- **Statement:** For the literal log profile a(t), its autocorrelation C(u) has absolutely admitted second moment equal to -2*(divisorHarmonicBoundary/3)^2; consequently C(u)<0 for some positive lag.

## Goal

Test whether positive source primitives can justify nonnegative signed pairings.
Keep both actual source coordinates, rather than replace either by an absolute
majorant. The resulting bilinear invariant constrains cancellation on SZ. It
does not supply the critical exponentially weighted correlation estimate or RH.

## Gates

- [x] Source-pure statement and corpus search.
- [x] Dependency-closed paper argument below.
- [x] Direct leaf Lean audit, umbrella wiring, and axiom audit.

## Paper proof [PROVED HERE]

The corpus proves a(t)=exp(-3t/2)*A(exp(t)), zero for t<=0,
integrability of (1+t^2)*a(t), mass zero, and first moment m=-H/3,
where H=divisorHarmonicBoundary>0. Define
C(u)=integral_R a(t+u)*a(t) dt.

Absolute quadratic admission makes (s-t)^2*a(s)*a(t) integrable
on R^2: expand its polynomial into three products of admitted moments.
The shear (u,t)->(u+t,t) preserves product Lebesgue measure, so
u^2*a(t+u)*a(t) is also integrable. Fubini and translation give

 integral_R u^2*C(u) du
 = integral_R^2 (s-t)^2*a(s)*a(t) ds dt
 = 2*(integral a)*(integral t^2*a)-2*(integral t*a)^2
 = -2*(H/3)^2.

Translation also gives C(-u)=C(u), while C(0)>=0. The strictly
negative admitted second moment therefore forces C(u)<0 at some u>0.
The negative second moment is an exact bilinear source invariant, not a
pointwise sign conclusion inferred from a Mellin jet.

### Transfer to the original finite critical cutoff [PROVED HERE]

Fix a positive lag u with C(u)<0, and put h(t)=a(t+u)*a(t),
B(T)=integral_0^T exp(t)*h(t) dt. Actual source continuity admits
finite integration by parts and gives the exact identity

 integral_0^T h(t) dt = exp(-T)*B(T) + integral_0^T exp(-t)*B(t) dt.

If B(T)>=0 for every T>=0, both terms are nonnegative. Absolute admission
of h then makes C(u)>=0 on taking T to infinity, a contradiction. Thus
B(T)<0 for some T>0. The original complete normalized head is exactly
f(t)=A(exp(t))/exp(t)=exp(t/2)*a(t), so its pairing at that same cutoff
is integral_0^T f(t+u)*f(t) dt=exp(u/2)*B(T)<0.

The endpoint is not discarded, and no integral of the critical product
over the infinite ray is assumed. This strengthens the no-go to actual
complete finite-cutoff correlations. It does not yet identify a particular
finite prime core covering both continuous source arguments.

## No-go closure

- **Candidate:** every nonnegative lag has nonnegative autocorrelation for
  the actual boundary log profile, or every original finite complete-source
  critical pairing is nonnegative.
- **Killing mechanism:** strictly negative second signed moment.
- **Positive survivor:** exact value and absolute admission of the complete
  two-source quadratic displacement integral; its magnitude is fixed by H^2.
  The finite critical-prefix identity retains its endpoint and provides the
  exact transfer to original critical normalization.
- **New insight:** primitive positivity cannot erase negative correlations
  even at this admitted boundary. Critical-weight control must retain them.
- **Status:** paper proof and both Lean leaves complete. Nine public theorem
  axiom queries report only propext, Classical.choice, and Quot.sound.
  Both leaves pass direct `lake --old env lean` audits and are wired into
  RHTower. No full or umbrella build was run. Broader primitive and
  cumulative original-cutoff correlation bounds remain unresolved.

## Lean certificate

- `MobiusDivisorCriticalSourceAutocorrelation`:
  `integrable_criticalAbelLogProfile_translated_product`,
  `integrable_criticalAbelLogAutocorrelation_second`,
  `criticalAbelLogAutocorrelation_second_moment`,
  `criticalAbelLogAutocorrelation_neg`,
  `exists_criticalAbelLogAutocorrelation_negative`.
- `MobiusDivisorCriticalFiniteCorrelationSign`:
  `criticalAbelCorrelationPrefix_boundary_balance`,
  `exists_criticalAbelExponentialCorrelationPrefix_negative`,
  `criticalAbelCompleteClockPairing_eq_prefix`,
  `exists_criticalAbelCompleteClockPairing_negative`.

## Novelty audit

Two deep corpus searches (generations 1182159 and 1182158; partial,
compiler metadata mostly source/stale) returned the actual mass/first-moment
inputs and general Green identities, but no matching source autocorrelation
theorem. Scoped source-text search found other autocorrelations for different
sources. This is a local corpus novelty check, not a literature priority claim.

## Log

- 2026-10-02 — Paper identity derived while testing the primitive-positivity
  attempt on SZ's signed mixed-correlation problem. Formalization started.
- 2026-10-02 — Both leaves, all nine public theorem axiom queries, and the
  mathlib API scratch pass. Candidate closed with its exact positive survivor.
