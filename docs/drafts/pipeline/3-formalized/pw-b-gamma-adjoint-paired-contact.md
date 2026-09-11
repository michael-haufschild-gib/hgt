# PW-B complete signed pairing of the retained adjoint contact

- **ID:** PW-B-GAMMA-ADJOINT-PAIRED-CONTACT-2026-09-11
- **Stage:** 3-formalized
- **Status:** Fourteen public theorems passed final Lean scratch verification without diagnostics. Exact source promoted and wired once; targeted leaf build passed in26s. Final index and repository formal lint passed.
- **Scope:** Complete two-parameter arithmetic contact pairing, including the moving layer and empty incoming constant loss. Full operator adjoints, Xi occurrence and Ward balance remain open. RH is not proved.
- **Depends on:** [literal contact](pw-b-gamma-adjoint-cutoff-contact.md), [complete reciprocal source bounds](pw-b-gamma-reciprocal-cutoff-source.md).

## Exact complete-source statement

Write g_z(x)=M_z(x)/Q(x), retain the whole signed arithmetic source, and set

`P_z,v(x)=w(x)*conj(g_z(x))*g_v(x)`,

`w(x)=exp(-x-1/x)/x`,

`a_delta(x)=delta/[x*(x-delta)]` for x>delta,

`c_delta(x)=integral_(a_delta(x)..delta) exp(-h)/h dh`,

`L_delta(P)=(integral_(0..delta) P(x) dx)*(integral_(h>delta) exp(-h)/h dh)`.

For every two complex parameters z,v,

`integral_(x>delta) P_z,v(x)*c_delta(x) dx-L_delta(P_z,v)`

`tends to integral_(x>0) P_z,v(x)*2*log(x) dx` as delta tends to0 from above.

Every original integral in this passage is absolutely admitted for
0<delta<=1. No source truncation, scalar occurrence, zero-location hypothesis
or added axiom is used.

## Proof retaining the moving layer

The complete reciprocal polynomial bound gives
`|g_z(x)|<=1+A*x^(-p)`. After expanding the two norm bounds, each inverse
monomial in the density obeys

`w(x)/x^k <= (k+2)!*x*exp(-x)`.

This follows from the exponential-series inequality at1/x. Consequently,
for every z,v there is a finite C>=0 such that

`|P_z,v(x)|<=C*x*exp(-x)` for all positive x.

The actual coordinate derivative of M_z gives continuity of P_z,v.

Positivity and exp(-h)<=1 bound the absolute oriented contact by
`|log(x)|+|log(x-delta)|`. Translate the entire x>delta integral by
x=u+delta. This retains the entire moving layer on the fixed positive u ray.
For0<delta<=1,

`|c_delta(u+delta)|<=2*|log(u)|+u+1`.

The source bound and `u*|log(u)|<=u^2+1` give the fixed majorant

`C*exp(-u)*(2*|log(u)|+3*u^2+2*u+3)`.

It is integrable by the original logarithmic exponential integral and Gamma
moments. Both contact endpoints tend to0 at fixed u; the admitted exponential
remainder gives the limit2*log(u). Dominated convergence and exact additive
Haar translation prove the paired contact limit in its original coordinates.

The empty incoming region remains a separate term. Its tail integral is at
most exp(-delta)/delta; the source integral over0<x<delta has norm at most
C*delta^2. Thus `|L_delta(P)|<=C*delta`, which tends to0. This does not extend
the positive-cutoff contact formula to x<=delta.

## Exact remaining adjoint work

Finite-cutoff gain transposition still requires joint admission, Fubini and
the reciprocal Jacobian on the actual triangle. The transformed source varies
across the mismatched cutoffs. Its additional term is

`integral_(a_delta(x)..delta) H_z(1/x,h) dh`,

where H_z is the complete normalized reciprocal response. It must be proved
to vanish after pairing. The backward response is initially restricted to
x>delta, so its omitted initial region must also be controlled. None of these
response terms is replaced by the constant-field contact proved here.
The [pairing card](../1-in-progress/pw-b-gamma-reversible-pairing.md#remaining-transposition-terms-after-the-paired-contact)
records the full-source majorant attack.

## Lean and verification

Leaf: `ThetaCuspHawkingParikhWilczekGammaAdjointPairedContact.lean`.
The final foreground `lake env lean /tmp/pwb-gamma-adjoint-translated-contact.lean`
exited0 without diagnostics. Main declarations:

- `pwGammaMobiusReversiblePairDensity_bound`;
- `pwGammaMobiusReversiblePairDensity_contact_admission`;
- `pwGammaMobiusReversiblePairDensity_original_contact_tendsto`.

The exact checked source has one RHTower umbrella import. All14 public names
are indexed. The targeted leaf build passed in26s; final repository lint passed. No full/umbrella
build, numerical experiment or axiom-print check was used.

The [whole-corpus search record](../1-in-progress/pw-b-gamma-full-adjoint-searches.json)
retains partial coverage and proposed ingredient plans. The proof uses actual
additive Haar translation, complete source bounds and the corpus logarithmic
exponential majorant. Recent broad arXiv scattering reading suggested testing
source occurrence separately from a positive connecting operator; it supplies
no Xi occurrence or Ward premise here.
