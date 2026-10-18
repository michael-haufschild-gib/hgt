# Actual dilation-profile coercivity from period-reset cells

- **ID:** bvi-period-reset-profile-coercivity-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Unformalized C14 candidate in
  `bvi-dilation-successor-jump-coupling-2026-10-18.md`; current BVI corpus.
- **Statement:** The actual scaled primitive distance retains explicit harmonic
  energy on disjoint period-reset jump cells, despite cancellation in its
  Möbius residue expansion.

## Goal

Obtain a lower bound on the actual profile, complementing the corpus's upper
residue-gap bound. This must use the literal primitive, not reverse
Cauchy–Schwarz on signed Möbius summands. Neither signed prime-packet dispersion
nor a global cancellation estimate follows from a pairwise lower bound.

## Paper proof under audit

Write `R > 1`, `q = p+h`, with positive integers `p,h`, and
`A(k) = Re(pmRamanujanPrimitive R k)`. Define

`D(p,q) = (p+q) G(R,R) - 2 sqrt(p) sqrt(q) Phi_R(p/q)`.

Existing `hasSum_scaled_pmRamanujanPrimitive_distance` identifies this with
the sum of `(p A(n/p) - q A(n/q))^2 / (n(n+1))` for `n >= 0`.

For `k=R*t`, `t>=1`, and `k*h<=p`, the interval `I_k=[kp,kq)` has exact
quotients `floor(n/p)=k`, `floor(n/q)=k-1`. Periodicity gives `A(k)=0`;
the coefficient at a multiple of R is `phi(R)`, so `A(k-1)=-phi(R)`.
Consequently the literal difference on this interval is `q*phi(R)`.
The existing reciprocal-pronic interval identity then gives exact cell mass

`sum_{n in I_k} distanceTerm(n) = h*q*phi(R)^2/(p*k)`.

For `1<=t<=K=floor(p/(R*h))`, the selected intervals are disjoint:
`k*q <= (k+1)*p <= (k+R)*p`. Their nonnegative masses sum to

`h*q*phi(R)^2/(p*R) * harmonic(K) <= D(p,q)`.

Proof obligations: verify all interfaces against current Lean; implement
quotient boundaries, reset and preceding value, finite interval mass,
disjoint-cell aggregation, and exact HasSum transfer. No numerical evidence.

## Prior-work and significance audit

- Existing `PronicResidueGapEnergyAndPrimePairDistance` already proves harmonic
  upper/lower bounds for a residue difference. Those are not new.
- Existing `RamanujanDilationProfileResidueGapBudget` proves the actual-distance
  HasSum and an upper bound via the signed residue expansion. Its source was
  read fully; it does not provide this actual-carrier lower bound.
- Existing periodicity, successor, real-coefficient/lag, and divisible-lag
  totient interfaces must be reused.
- Fresh deep corpus query in progress:
  `/tmp/bvi-100-actual-profile-research.json`.
- General periodic-step autocorrelation may already imply related cusp laws.
  Classical novelty is not established. Formalizing a previously open corpus
  candidate alone does not establish the user's significance criterion.
- **Accepted contribution status: not accepted; 0 credit.**

## Gates

- [x] Well-posed candidate and explicit distinction from residue bounds.
- [ ] Fresh corpus / classical-baseline audit completed.
- [ ] Complete dependency-closed paper proof, including endpoint cases.
- [ ] Exact Lean capstone with data parameters only.
- [ ] Original-source check, all public axiom closures, wiring and indexing.
- [ ] Significance verdict recorded without claiming unsupported novelty.

## Log

- 2026-10-18 — Candidate carried into new programme; no previous completed
  theorem recounted. Field README remains read-only.

## Stronger conjecture exposed by the cell algebra

For every `1<=k<=K`, `K*h<=p`, the first cell `[kp,kq)` has difference
`p A(k)-q A(k-1)` and the second `[kq,(k+1)p)` has difference `-h A(k)`.
Writing `c(k)=A(k)-A(k-1)`, their combined exact mass simplifies to

`h*c(k)^2/k + (h^2/p)*(A(k-1)^2/k-A(k)^2/(k+1))`.

Since `A(0)=0`, summing **all** quotient cells gives the stronger candidate

`sum_{n < (K+1)*p} distanceTerm(n)`
`  = h*sum_{k=1}^K c(k)^2/k - (h^2/p)*A(K)^2/(K+1)`.

This is an exact identity for the original Ramanujan primitive, including its
signed cancellation. It is stronger than selecting period-reset cells.
At `R|K` the endpoint term vanishes. Search the corpus before formalizing;
fresh deep query `/tmp/bvi100-exact-prefix-research.json` is running.
The arithmetic statement and significance require separate audits; count
remains zero. A generic periodic-step cusp alone is insufficient: Balazard–
Martin already analyze multiplicative fractional-part autocorrelation and its
logarithmic modulus (2013, https://arxiv.org/abs/1305.4395, propositions 31–32).

Fresh first deep query completed: partial=false, errors=[], 74,219 inventoried
files; semantic completeness unmeasured, compiler coverage mostly pending or
stale; background refresh incomplete. All 20 candidate and 20 source statements
reviewed. Proposed ingredient chain only repeats the existing upper bound and
does not prove a lower bound. Broad lexical hits mix unrelated harmonic
results; narrowed exact-profile query is used for the next review.
