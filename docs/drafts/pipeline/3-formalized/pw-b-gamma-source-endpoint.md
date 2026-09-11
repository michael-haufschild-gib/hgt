# PW-B actual Gamma/Möbius endpoint and Mellin domain

- **ID:** PW-B-GAMMA-SOURCE-ENDPOINT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** For Re(z)>3/2, the unchanged normalized source M_z(x)/sqrt(x) tends to the nonzero coefficient 1/zeta(z-1/2) as x tends to zero from above. Its actual Mellin integral is Lebesgue/Bochner integrable exactly when Re(s)>-1/2.

## Complete source and endpoint proof

Use the same positive-ray source Q(x)=sqrt(x)*exp(-x) and the entire
coefficient family M_z(x)=sum mu(n)*exp(-z*log(n))*Q(n*x).
The value assigned at x=0 is not used; all identities and limits concern
x>0. Dividing each actual atom by sqrt(x) gives

`LSeries.term(mu,z-1/2,n)*exp(-n*x)`.

The zero atom vanishes. When Re(z)>3/2, the full coefficient norm series
converges. Every exponential damping factor is bounded by one and tends
to one at zero. Dominated convergence of the complete series yields

`M_z(x)/sqrt(x) -> 1/zeta(z-1/2)`.

Zeta is nonzero in this coefficient region, so half the norm of that
limit is an eventual strictly positive lower bound. No finite head or
absolute-value replacement stands in for the original signed source.

## Sharp actual domain and positive survivor

The original weighted source norm is exactly

`norm(x^(s-1)*M_z(x)) = x^(Re(s)-1/2)*norm(M_z(x)/sqrt(x))`.

If its Mellin integral were admitted at Re(s)<=-1/2, restriction to a
sufficiently small interval and the positive endpoint lower bound would
make x^(Re(s)-1/2) integrable there. The exact local power-integrability
threshold contradicts this. Conversely, Re(s)>-1/2 and Re(z)>3/2 imply
Re(z+s)>1, so the prior [literal Mellin bridge](pw-b-gamma-mellin-bridge.md)
admits the complete original source. Hence

`MellinConvergent(M_z,s) iff Re(s)>-1/2`, for Re(z)>3/2.

This concerns the full signed integral, beyond the earlier coefficientwise
absolute-admission test. Its positive survivor is the exact nonzero
endpoint coefficient and complete admitted domain, with a quantitative
lower bound in an actual neighborhood of zero.

The spectral argument of the admitted formula is u=z+s. Holding u fixed
and increasing Re(z) therefore fails actual Mellin admission whenever
Re(u)<=Re(z)-1/2. A large-coefficient spatial asymptotic cannot be carried
through this compensating change of weight. This does not exclude a
separately constructed continued or subtracted source, and proves no
critical estimate at z=0.

## Research and remaining mathematical work

[Raw search records](../1-in-progress/pw-b-gamma-source-endpoint-searches.json)
retain partial corpus inventories, candidate statements, stored method
sources, proposed ingredient sets, runtime errors and deferred refresh.
The actual proof uses full-series dominated convergence, a nonzero limit,
and the local power-integrability criterion. Suggested generic finite
energy inequalities and asymptotic uniqueness statements do not supply
these source-specific facts.

A broad date-ordered arXiv query used `trapping`.
[Universal Structure of Horizon Formation in Generic Binary Black Hole Mergers](https://arxiv.org/html/2609.11819v1)
(September10,2026) connects past isolation and outermost stability to a
positive principal mode, then uses a complementary inverse and two
nondegenerate coefficients in a fold reduction. No such stability,
physical elliptic operator or principal-mode realization has been
established for this arithmetic source. No external hypothesis enters
these Lean proofs.

The next candidate tests an explicit complete endpoint subtraction
M_z-C_z*Q, C_z=1/zeta(z-1/2), retaining its source correction and original
integral. Its proposed first normalized remainder coefficient is
C_z-C_(z-1) for Re(z)>5/2. This is a paper candidate; no new continued
source or critical bound is claimed.

RH remains unproved. PW response -> functional-equation imbalance ->
positive Deninger Ward transmutation still needs an independently
source-forced fixed-grade balance at actual Xi occurrences. Physical
pairing/domain, occurrence identification and signed critical source
control remain open.

## Lean audit

Module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusSourceEndpoint.lean`.
The combined scratch and every public axiom audit passed: nine theorems
and one definition use only propext, Classical.choice and Quot.sound.
Identical proof bodies were promoted and the one-copy umbrella import is
wired. The final targeted leaf build passed in161s, rebuilding only the new
leaf and reusing its dependencies. No full or umbrella build ran.

Repository formal lint passed. The earlier unrelated WeightedMinimax
umbrella failures are absent from this run. New-source whitespace,
public-name uniqueness, one-copy umbrella wiring, local card links and
exact equality of promoted proof bodies with the passing scratch were
checked. The targeted build and index audit passed.

Index regeneration passed and refreshed LEAN_API, LEAN_GAPS and
LEAN_OVERVIEW (one changed search entry, zero removed). All ten public
declarations appear in the API and exactly once in the source corpus.
Every owned Lean, research and audit session finished; final process
inspection found no owned Lean/lake process. No numerical experiment,
added axiom, full build, commit or push was used. RH and the goal remain
open.


The [complete endpoint subtraction](pw-b-gamma-endpoint-subtraction.md)
now admits the corrected source at the former Mellin boundary and proves
its retained derivative value and eventual strict sign. It also proves
the first normalized remainder; the full enlarged domain remains open.
