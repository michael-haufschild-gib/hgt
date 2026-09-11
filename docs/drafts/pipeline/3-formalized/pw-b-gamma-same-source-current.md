# PW-B original generator on the same reflected arithmetic source

- **ID:** PW-B-GAMMA-SAME-SOURCE-CURRENT-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The original and conjugated nonlocal generators are both admitted on the complete reflected arithmetic family. Their exact difference is a convergent signed L-series with positive scalar weights and a nonzero prime leading coefficient. For every positive source coordinate the complete difference is nonzero at all sufficiently large real coefficient parameters.

## Source and operators retained

Keep the [literal reflected source](pw-b-gamma-reflected-frullani.md),
with Q(x)=sqrt(x)*exp(-x) for x>0 and
`R f(x)=Q(x)*f(1/x)/Q(1/x)`.
The original weighted translation is
`T_h f(x)=exp(-h)*Q(x)*f(x+h)/Q(x+h)`.
Its conjugate is S_h=R T_h R. The previous result identifies the
conjugated Frullani current on R M_b with R E_b, where E_b=partial_b M_b.
Here both generators are evaluated on **the same full input R M_b**.

Define the literal original response
`G_b(x,h)=(T_h(R M_b)(x)-exp(-h)*(R M_b)(x))/h`,
its admitted current `H(R M_b)(x)=integral G_b(x,h) dh`, and
`D_b(x)=H(R M_b)(x)-(R E_b)(x)`.
All h and x integrals below are over their complete positive rays with
Lebesgue measure. No source coefficient, endpoint or normalization is
removed. Q(0) is not set to zero; the zero arithmetic atom vanishes
because its Möbius coefficient does.

## Endpoint-sensitive common estimate

For a=n-1, the original response on the reflected Gamma atom is
`sqrt(n)*Q(x)*K(a,x,h)`, where
`K(a,x,h)=exp(-h)*(exp(-a/(x+h))-exp(-a/x))/h`.
K is nonnegative for a>=0 and strictly positive for a>0, x,h>0.
The unit atom's increment is zero. Put `v=a*h/(x*(x+h))`.
The exponential difference factors as
`exp(-a/(x+h))*(1-exp(-v))`.
The elementary bound `1-exp(-v)<=v` and the corpus's exponential
factorial estimate give, for every natural k,

`K(a,x,h) <= (k+1)!/a^k * exp(-h)*(x+h)^k/x`.

Keeping both reciprocal denominators is essential to this proof.
Replacing x+h by x before integrating loses the useful endpoint weight.
The inequality `(x+h)^k<=2^(k-1)*(x^k+h^k)` gives the separable majorant

`J_k(h,x)=exp(-h)*norm(Q(x))/x*(x^k+h^k)`.

It is integrable on the product and on every fixed-x h section.
The exact source inverse moments are
`integral x^k*norm(Q(x))/x dx=Gamma(k+1/2)`;
the displacement moments are Gamma(k+1). All are obtained from convergent
Gamma integrals, without analytic continuation or numerical evaluation.

For norm(b)<=N, the full arithmetic atom with index n+2 satisfies

`norm(G_b_atom(n+2,h,x))`
`<= 2^(N+1)*(N+4)!*2^(N+2)/(n+1)^2 * J_(N+3)(h,x)`.

The proof retains mu(n+2) and exp(-b*log(n+2)), using their norm bounds,
and costs only an inverse-square summable index factor. Each full atom
is jointly integrable, and the complete sum of its joint norm integrals
converges. The same holds for its h sections at every positive x.

## Exact complete forcing

Pointwise absolute convergence identifies the literal response G_b
with its full atom sum. The common estimates then justify its joint
L1 admission, fixed-x h admission, series/integral interchange and
Fubini for every complex b. Thus H(R M_b), D_b and the two-variable
difference G_b-F_b^R are all integrable in their stated measures.
The h integral of that last difference is exactly D_b.

Define W_0(x)=0 and, for n>=1,

`W_n(x)=sqrt(n)*(integral K(n-1,x,h) dh+log(n)*exp(-(n-1)/x))`.

W_1=0, and W_n(x)>0 for n>1 and x>0. Direct admitted atom integration
proves the complete identity

`D_b(x)=sum_n mu(n)*exp(-b*log(n))*Q(x)*W_n(x)`.

The sum is absolutely convergent for every complex b at every positive x.
This is the positive survivor: explicit positive scalar weights for the
actual signed forcing, together with its full domain and exact identity.
Positivity of the weights does not remove the signed arithmetic factors.

## Leading coefficient and failure of family-wide balance

Set `c_n(x)=mu(n)*Q(x)*W_n(x)`. The exact forcing is the literal L-series
of these coefficients, and this L-series converges at every complex b.
Its first two coefficients vanish, while
`c_2(x)=-Q(x)*W_2(x)` is nonzero for every positive x.
Applying the corpus theorem `LSeries.tendsto_cpow_mul_atTop` gives

`2^r*D_r(x) -> -Q(x)*W_2(x)` as real r tends to infinity.

Consequently D_r(x) is nonzero for every sufficiently large real r,
and D_b(x) cannot vanish identically in b at any positive x.
This is a statement about the complete arithmetic sum, not merely its
individual atoms. It rejects an automatic balance across the entire
coefficient family. No claim is made that D_0 is nonzero or that balance
cannot hold at particular spectral parameters.

## Research and scope

Four deep method searches are retained in
[the search record](../1-in-progress/pw-b-gamma-same-source-searches.json).
All report partial coverage. Three inventories report 723442, 723502 and
723510 declarations; the domain query reports pending coverage, with
no declaration count. Generic positive-kernel suggestions retain
unproved positivity obligations for signed coefficients. Direct corpus
search located the Gamma moment and L-series leading-coefficient tools;
the literal proof checks their applicability.

The broad date-ordered arXiv query was `bistability`.
[Collective Hysteresis and Multistability in Threshold Networks](https://arxiv.org/html/2609.10580v1)
(September 5) derives equilibrium control from nonnegative row-stochastic
feedback and a strict contraction condition. Those source hypotheses
have not been established here.
[Linear Response Predicts Cusp-Pair Births in Networks with a Localized Cubic](https://arxiv.org/abs/2609.11574)
(September 10) concerns a passive network approximation; its abstract
supplied no verified arithmetic transfer. No external premise enters Lean.

PW-B remains active; RH is unproved. Chain: literal PW response -> FE
imbalance -> positive Deninger Ward transmutation -> independent
source-forced fixed-grade balance -> RH. The present results admit both
operators on the same arithmetic input and retain their complete forcing.
They do not identify the coefficient parameter with a Xi spectral label,
derive a physical spectral domain, or supply the missing source balance.

The next candidate is the original spatial pairing of D_b: prove its
mass L-series and retain the integrated prime coefficient before testing
an integrated balance law. A nonzero pointwise response alone does not
settle its total mass. The zero-parameter mass and physical spectral
identification remain separate obligations.

## Lean audit

Modules:

- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusSameSourceKernel.lean: 312 lines, 21 public theorems, four definitions.
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusSameSourceCurrent.lean: 319 lines, 23 public theorems, four definitions.

The complete `lake env lean` scratch checks passed. Both targeted final
`lake build` commands passed, rebuilding only their new leaf; existing
dependencies were reused. No full or umbrella build ran. The current
leaf emits an informational ring-normalization suggestion at line 200;
there is no open proof goal. All 52 public declarations passed the
scratch `#print axioms` audit, using only `propext`, `Classical.choice`
and `Quot.sound`. All names are unique and both umbrella imports are wired.

Repository-wide formal lint did **not** pass: it reports five unrelated
missing umbrella imports, for Sieve.MenonHarmonicRamareBlockSwapped,
Sieve.MenonHarmonicRamareLadderSwapped,
Sieve.MenonHarmonicRamareLadderSwappedVolume,
HTGeometry.WeightedMinimax.Basic and HTGeometry.WeightedMinimax.SignRealization.
Neither new PW-B leaf is flagged. The separate active work was preserved.
New-file whitespace/conflict checks, scoped diff checks and local card
links passed. Index/API and final process results are recorded in the
attack ledger. All owned Lean processes were run serially in the foreground;
no added axiom, numerical experiment, commit or push was used.
