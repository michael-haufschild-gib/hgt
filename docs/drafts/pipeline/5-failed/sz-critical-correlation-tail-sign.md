# SZ: eventual correlation positivity is impossible

- **ID:** sz-critical-correlation-tail-sign
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Source:** `MobiusDivisorCriticalSourceAutocorrelation`, `DivisorContinuousHeadMellin`, `DivisorUnsignedChannelExactMean`, `Bottcher/SchwarzReflection`, `LandauIntegralTransfer`.
- **Retired candidate:** Removing a finite lag head makes the literal log-source autocorrelation nonnegative.
- **Positive survivor:** Exact negative real residue, cofinal source-calibrated negative envelopes, and infinite exponential mass of the negative part.

## Goal

Route SZ requires the complete signed correlation/Wronskian at original cutoffs. The existing negative second moment rules out positivity everywhere, but permits an eventual-positive-tail shortcut. Test and formalize the stronger source-specific obstruction. This does not itself bound cumulative leakage or prove RH.

## Dependency-closed paper proof

Write a(t)=exp(-3t/2)A(exp(t)), extended by zero for t<=0, and
C(u)=integral a(t+u)a(t) dt. Existing source results give a in L1 and bounded,
C in L1, and C even. Put B=divisorSourceEntire and

L(s)=s B(1+s)/[(1+s)(3+2s) zetaPoleUnit(1+s)].

For Re(s)>0, L is the Laplace transform of a, by the actual Abel Mellin weld.
It is holomorphic near zero and at every real -1<s<0, since zeta has no real
zeros in (0,1). Let Q(s)=integral_0^infinity exp(-su)C(u)du for Re(s)>=0.
Absolute Fubini on the imaginary axis gives

Q(it)+Q(-it)=L(it)L(-it).

Thus Q continues through a neighborhood of zero: use Q(s) on the right and
L(s)L(-s)-Q(-s) on the left. Boundary continuity and the corpus's holomorphic
gluing theorem across a straight line justify the continuation. On the negative
real interval the same left formula continues Q locally. No exponentially
weighted physical integral is presumed before applying Landau.

Let c=log(2*pi)/2-gamma-1/4. The exact unsigned channel mean and its proved
positive square-root floor imply c>0. The source formula at zero and the
proved zeta derivative there give B(0)=c, hence

lim_(s->-1+) (s+1)L(s)=-2c.

The physical nonnegative unit source and its positive first block imply
B(2)>0 via its admitted Mellin integral. Since zeta(2)>0,
L(1)=B(2)/(10*zeta(2))>0. Consequently the continued Q has the exact residue

lim_(s->-1+) (s+1)Q(s)=-kappa,  kappa=2c L(1)>0.

If C(u)>=-k exp(-u) eventually for any k<kappa, the tail of
C(u)+k exp(-u) is a nonnegative Laplace carrier. Its transform is Q(s)+
k/(s+1) minus an entire compact-head transform. It continues holomorphically
along every real s>-1. Landau's theorem forces physical admission throughout
that interval (otherwise its finite real abscissa would be singular). Its
residue at -1 is k-kappa<0, impossible for a nonnegative carrier. Thus every
cutoff has a later u with C(u)<-k exp(-u); in particular C is not eventually
nonnegative.

For the stronger negative-mass statement, suppose integral exp(u) C^-(u) du
is finite. Its Laplace transform is analytic for Re(s)>-1 and bounded as
s->-1+. Adding it to Q continues the positive-part transform along (-1,0].
Landau again forces positive-part admission for all real s>-1. The negative
residue remains -kappa, contradicting positivity. Hence that exponential
moment of C^- diverges.

## Audit obligations

- Source identities and signs must be Lean checked; no numerical estimates.
- Prove absolute correlation admission and the imaginary-axis product identity.
- Apply straight-line holomorphic gluing with boundary continuity explicitly.
- Formalize Landau's real-abscissa step without assuming critical source admission.
- Retain the compact head for eventual sign claims.
- Final result must be unconditional; no user axioms or placeholders.
- Do not count intermediate transform algebra as a completed frontier result.

## Formal result and audit

All seven leaves pass clean direct `lake --old env lean <leaf> -o <leaf.olean>`
audits and are wired into `RHTower.lean`; no umbrella was built:

- `MobiusDivisorCriticalCorrelationSource.lean`
- `MobiusDivisorCriticalCorrelationRegularity.lean`
- `MobiusDivisorCriticalCorrelationProduct.lean`
- `MobiusDivisorCriticalCorrelationMellin.lean`
- `MobiusDivisorCriticalCorrelationContinuation.lean`
- `LaplaceNegativeRealResidue.lean`
- `MobiusDivisorCriticalCorrelationTailSign.lean`

The terminal leaf proves `criticalAbelLogAutocorrelation_not_eventually_nonneg`,
`criticalAbelLogAutocorrelation_negative_beyond`,
`criticalAbelLogAutocorrelation_below_residue_envelope`, and
`not_integrableOn_criticalAbelLogAutocorrelation_negative_exp`. These are
unconditional source results; the envelope parameter has its stated
domain `k < criticalCorrelationNegativeResidue`. No negative-frequency
physical admission or nonreal zero-cancellation statement is assumed.

All eleven intermediate and terminal axiom queries return only `propext`,
`Classical.choice`, and `Quot.sound`. Formal lint after
wiring reports only the same ten unrelated unreachable modules recorded
in the working log. No forbidden declaration or new unreachable leaf is
reported. No numerical experiment or heartbeat increase was used.

The positive survivor is the proved source-calibrated analytic law and
its exact physical tail consequences, not merely a failed sign guess.
The original-cutoff coupled forcing/Wronskian estimate and RH remain
open. This card retires only eventual correlation positivity, not SZ.

The Landau implementation reuses the corpus's existing tail carrier, including
its compact-head subtraction and reference pole at 1/4. Rescale a physical
correlation by exp(5u/4), so its s=-1 endpoint lands at 1/4. The eventual
nonnegative tail would have abscissa exactly 1/4 by local real analyticity.
Choosing the tail cutoff sufficiently far out makes its retained negative
residue dominate the reference pole. This contradicts positivity without
any nonreal pole counting or zero-cancellation premise.
