# PW-B finite expansion of the original reciprocal current

- **ID:** PW-B-GAMMA-RECIPROCAL-CUTOFF-EXPANSION-2026-09-11
- **Status:** Ten public theorems passed scratch verification and the targeted leaf build (76 seconds). Final index and repository formal lint passed.
- **Depends on:** [complete source and cutoff bounds](pw-b-gamma-reciprocal-cutoff-source.md).
- **Route:** PW-B remains live. RH is not proved.

## Exact finite expansion

Write S_z and H_z as in the source card, and put

`C_z(v)=SameSourceCurrent_z(v)/Q(v)`,

`B_j(z)=integral_(t>0) exp(-t)*S_z(t)/t^(j+1) dt`.

For every complex z and every natural q there is a finite nonnegative constant
C such that, for all `0<v<=1/2`,

`norm(exp(-v)*C_z(v)-sum_(j<q) v^j*B_j(z))<=C*v^q`.

This is a finite asymptotic expansion at every requested order. It assumes no
analyticity, infinite-series convergence, zero location or scalar equation.
The constants can depend on z and q.

## Original cutoff identity

Define

`N(v)=integral_(0<h<v) H_z(v,h) dh`,

`P_j(v)=integral_(0<t<2v) exp(-t)*S_z(t)/t^(j+1) dt`,

`L(v)=integral_(h>v) exp(-h)*S_z(v)/h dh`,

`R_q(v)=integral_(t>2v) exp(-t)*S_z(t)*v^q/[t^q*(t-v)] dt`.

The exact original-current identity is

`exp(-v)*C_z(v)-sum_(j<q) v^j*B_j(z)`

`= exp(-v)*N(v)-sum_(j<q) v^j*P_j(v)+R_q(v)-exp(-v)*L(v)`.

Each integral is admitted on its stated domain. The near response is retained
before gain and loss are separated. Translation t=h+v carries the far region
h>v to t>2v with the exact exponential factor. Finite geometric division gives
R_q; integrating the admitted finite sum then restores each full B_j together
with its removed initial piece P_j.

## Remainder estimates

The source theorem bounds N and each P_j to every requested power. The loss
uses `1/h<=1/v` on h>v:

`norm(L(v))<=norm(S_z(v))*exp(-v)/v`.

One extra source power absorbs this denominator. No separate logarithmic
estimate is needed.

For t>2v, the exact finite resolvent remainder obeys

`norm(exp(-t)*S_z(t)*v^q/[t^q*(t-v)])`

`<=2*v^q*norm(exp(-t)*S_z(t)/t^(q+1))`.

The complete norm moment is admitted. Integrating and combining the four
bounds proves the displayed finite asymptotic estimate. All signed arithmetic
coefficients remain in S_z; there is no finite-source truncation.

## Verified finite-order consequence

The complete moment detector gives some nonzero B_j at every z. Select its
least such index. The expansion at order j+1 gives

`x^j*exp(-1/x)*C_z(1/x) -> B_j(z) != 0`.

This is the positive finite-order classification of the original current.
It contradicts the all-order flatness required by the corrected scalar
equation. The [exact classification and obstruction](../5-failed/pw-b-corrected-gamma-scalar-occurrence.md)
passed Lean scratch verification and the targeted valuation leaf build.
Full adjoints, actual Xi occurrence and independent Ward balance remain open.

## Verification and source search

`ThetaCuspHawkingParikhWilczekGammaReciprocalCutoffExpansion.lean` is the exact
scratch-verified source with one RHTower umbrella import. The terminal scratch
exit is0, with no diagnostics. The first corrected checker handle disappeared;
no success was inferred from that run. The final check retained an explicit
exit file. The targeted leaf build passed in76s. No full build, numerical experiment or axiom-print check was used.

The [deep/method records](../1-in-progress/pw-b-gamma-reciprocal-cutoff-searches.json)
include partial coverage and reported local-service failures. Actual corpus
half-line translation and Frullani splitting proofs supplied applicable
mechanisms. AsymptoticExpansionAlgebra and PowerExpansionAlongRay confirm that
coefficient extraction can use finite remainders without a convergent series.
