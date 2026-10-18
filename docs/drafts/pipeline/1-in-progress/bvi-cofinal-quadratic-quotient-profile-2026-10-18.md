# Cofinal unshifted quadratic profile from complementary quotients

- **ID:** BVI-COFINAL-QUADRATIC-PROFILE-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / dependency audit
- **Scope:** Literal Möbius source, fixed linear observation ratios; no RH
  work, no receiver assumptions, no numerical experiments.

## Target

Let Q_N(M)=sum_{k=1}^M s_N(k)^2, with
s_N(k)=sum_{d<=N,d|k}mu(d). For each fixed integer A>=2, conjecture

    Q_N(A N)/N -> F(A),

where F(A) is the following finite arithmetic profile. For q,r in [1,A-1],
put g=gcd(q,r), a=q/g, b=r/g, l=lcm(q,r), and

    D(v)=(6/pi^2) product_{p prime, p|v} p/(p+1).
    F(A)=sum_{q,r=1}^{A-1} mu(a)mu(b) D(ab) (A-max(q,r))/l.

This is unshifted quadratic energy. The neighboring-gradient energy
also contains an additive shifted correlation; no formula for that
correlation is assumed or claimed here.

## Paper mechanism and missing dependency

For 1<=k<=AN and N>=1, complementary quotient compression writes
s_N(k)=1_{k=1}-sum_{q<=A-1,q|k,k>qN}mu(k/q). The tail vanishes at k=1.
Expand the square and exchange finite sums. A q,r pair is supported on
k divisible by l and k>max(q,r)N. Write k=l*n. Then k/q=b*n and k/r=a*n.
Möbius multiplication gives the exact identity

    mu(an)mu(bn)=mu(a)mu(b)mu(n)^2 1_{gcd(n,ab)=1}.

Thus the pair contributes a weighted coprime-squarefree count on

    max(q,r)N/l < n <= AN/l.

Its proposed density is D(ab), and the interval length divided by N
tends to (A-max(q,r))/l. A finite sum then proves the target profile.

**Missing audited dependency:** unconditional squarefree counting density
with an arbitrary fixed coprimality modulus. The corpus source read so
far proves prime deletion, not the general finite-modulus version.
Do not mark this paper proof closed until that extension is supplied.

## Candidate way to close the density dependency

Let C_Q(x) count squarefree n<=x coprime to Q. If p is prime and p does
not divide Q, splitting n according to p|n gives exactly

    C_Q(x)=C_{pQ}(x)+C_{pQ}(floor(x/p)).

This follows because squarefree multiples of p are p*m with p not dividing
m, and coprimality to Q is preserved. Given C_Q(x)/x->D(Q), a finite
geometric expansion of this recurrence and the bound 0<=C_{pQ}(x)<=x
force C_{pQ}(x)/x->D(Q)*p/(p+1). Induction over the finite prime divisors
of Q should supply the general density without any unproved analytic
input. This argument still requires a full paper and Lean audit.

## Corpus evidence

- `ComplementaryQuotientAndSecondOctaveLaw.lean`: exact compression.
- `CompositeSquarefreeStepAndMultiOctaveL2Energy.lean`: finite two-band
  energy formulas and exact cutoff-step identities, not a general cofinal
  density profile in inspected source.
- `CoprimeSquarefreeDyadic.lean`: prime-deleted dyadic density.
- `CoprimeSquarefreeWindow.lean`: prime-deleted square-root counting error.
- `CoprimeMoebiusSeries.lean`: prime deletion of the inverse-square series.
- Deep query `sieveL2PrefixEnergy asymptotic density` returned only finite
  energy identities among useful hits; query was partial, coverage pending.
- Follow-up deep query `moebius multiplicative correlation coprime
  squarefree density` is running as session 54382, output
  `/tmp/bvi-cofinal-multiplicative-density-research.json`. Wait for terminal
  status before parsing.

## Status

- [x] Conjecture recorded before new Lean implementation.
- [ ] Complete corpus applicability and novelty audit.
- [ ] Close finite-modulus density proof on paper.
- [ ] Audit exact quotient-pair reindexing and all endpoint floors.
- [ ] Formalize the exact survivor, then original-source and axiom audits.

The three prior cofinal results are already verified and documented in
stage-3 cards. This card does not replace their completed work.
