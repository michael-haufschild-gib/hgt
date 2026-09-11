# PW-B reflected Frullani generator and complete global domain

- **ID:** PW-B-GAMMA-REFLECTED-FRULLANI-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The source-fixed inverse-gain reflection conjugates the actual weighted translation to reciprocal motion. The complete reflected arithmetic family, its coefficient current and its joint Frullani response are globally integrable for every complex coefficient parameter. The zero-parameter current remains nonzero.

## Literal reflection and source motion

Keep Q(x)=sqrt(x)*exp(-x) for x>0 and the original complete family
M_b(x)=sum_n mu(n)*exp(-b*log(n))*Q(n*x). Define

`R f(x)=Q(x)/Q(1/x)*f(1/x)`.

This is exactly the previous inverse-gain reflection in log coordinates,
proved using the existing Gamma source transport law. It is involutive
and fixes Q. No new reflection or source normalization replaces the
previous one. The source is nonzero even at zero; only the zero
arithmetic coefficient vanishes.

For the [actual weighted translation](pw-b-gamma-frullani-current.md),

`T_h f(x)=exp(-h)*Q(x)*f(x+h)/Q(x+h)`.

Its literal conjugate S_h=R T_h R therefore satisfies, for x>0,h>=0,

`S_h f(x)=exp(-h)*Q(x)*f(x/(1+h*x))/Q(x/(1+h*x))`.

This proves the proposed additive/reciprocal motion formula with all
weights retained. The complete reflected-family response is defined by

`F^R_b(x,h)=(S_h(R M_b)(x)-exp(-h)*(R M_b)(x))/h`.

Involution gives the exact identity F^R_b(x,h)=Q(x)/Q(1/x)*F_b(1/x,h).
The already admitted fixed-x Frullani integral therefore proves

`integral F^R_b(x,h) dh=(R E_b)(x)`, where E_b=partial_b M_b.

The coefficient derivative of R M_b is exactly R E_b too. These equalities
hold for every complex b and positive x. They concern the conjugated
operator on the reflected source; they do not assert equality of the
original and reflected operators on the same source.

## Actual reflected atoms and polynomial norm estimates

For each positive integer n, direct evaluation of the source gives

`R[Q(n*.)](x)=sqrt(n)*Q(x)*exp(-(n-1)/x)`.

Thus the actual reflected arithmetic atom `A^R_b(n,x)=R[A_b(n,.)](x)`
retains mu(n), exp(-b*log(n)), sqrt(n), and the reciprocal exponential.
The full pointwise series equals R M_b, and its logarithmic current series
equals R E_b. This is equality with the original complete functions.

The reciprocal exponential permits a global estimate absent from the
unreflected absolute atom test. The corpus's exponential series bound
proves, for positive y and every natural p,

`exp(-y)<=p!/y^p`.

The actual Gamma integral also proves, without continuation,

`integral x^p*norm Q(x) dx=Gamma(p+3/2)`, with global L1 admission.

Choose a natural N with norm(b)<=N. For every natural k and n, the exact
tail estimate is

`(n+2)^k*norm A^R_b(n+2,x)`
`<= [2^(N+k+1)*(N+k+3)!]/(n+1)^2`
`   *x^(N+k+3)*norm Q(x)`.

The proof retains the source's half-density factor, bounds sqrt(n+2)
by n+2, bounds the coefficient exponential by (n+2)^N, and applies the
reciprocal exponential estimate with p=N+k+3. The elementary inequality
n+2<=2*(n+1) leaves precisely an inverse-square summable index cost.
Each atom is measurable and globally integrable; index zero vanishes,
while index one is Q. Integrating the common majorant proves

`sum_n n^k*integral norm A^R_b(n,x) dx < infinity`

for every complex b and natural k. In particular, the complete source
and its logarithmic current have summable atom norm integrals at every b;
for the current use norm(log n)<=n. Their global source integrals commute
with their complete arithmetic sums. The original source's absolute
half-plane boundary cannot be transported unchanged through this reflection.

## Joint Frullani admission and surviving current

Let K_n be the actual Frullani kernel from the previous audit. For n>=1,
its absolute h-integral is log(n); the complete zero-index atom vanishes.
Every product K_n(h)*A^R_b(n,x) is jointly integrable. Its product norm
integral equals the norm integral of the corresponding reflected current
atom, so their complete sum is absolutely admitted on both positive rays
for every complex b. The literal response equals that full sum.
Consequently F^R_b is in L1(dh dx), Fubini holds, and its product integral
is exactly integral (R E_b)(x) dx. No value or sign is asserted for this
last unweighted reflected mass.

The zero-parameter current cannot vanish on the whole positive ray:
involution and nonzero source gain would make the original E vanish there,
contradicting its proved mass Gamma(3/2)>0. Thus source fixation, exact
conjugacy and this entire global admission region do not force stationarity.
This is the nontrivial positive survivor: an explicit globally admitted
reflected nonlocal arithmetic generator with every coefficient retained.

## RH scope and next mathematical attack

PW-B remains active and RH unproved. Chain: literal PW response -> FE
imbalance -> positive Deninger Ward transmutation -> independently
source-forced fixed-grade balance -> RH. The present result closes the
actual reflected-operator and complete global-domain candidate. Admission
now holds at every coefficient parameter, so it excludes none of them.
Neither a physical operator domain nor identification of b with a Xi
spectral label has been established.

The next candidate must compare the two operators on the same actual
arithmetic source. The proved S_h(R M_b)=R(T_h M_b) is conjugacy; it does
not give S_h M_b=T_h M_b. Derive the original Frullani operator acting on
R M_b, retain the complete difference from R E_b, and test an independently
source-derived balance for that difference. Do not replace this obligation
by Q fixation, generic trace cyclicity or a source-dependent change of measure.

## Search and primary-source audit

Three deep method searches, each reporting partial coverage of 723426
indexed declarations, are retained with complete metadata in the
[search artifact](../1-in-progress/pw-b-gamma-reflected-frullani-searches.json).
They suggest weighted reflection, Gamma moments and exponential decay;
their abstract candidate hypotheses do not themselves supply the actual
source formula or global bound. Corpus text search located the applicable
exponential factorial bound and convergent Gamma integral. All used
identities were checked in the actual Lean scratch proof.

A broad single-word arXiv search for renewal, ordered by announcement
date, produced September2026 papers. Read the primary abstract, model
section and stationary-state section of
[renewal-reset random walks](https://arxiv.org/html/2609.09738v1)
(September9). Its stationary law retains a nonzero reset probability
derived from the competing waiting-time laws. No such reset law or
probability is identified for this arithmetic source, so that mechanism
cannot supply stationarity here without new source data. Read also the
abstract of [temporal-network identifiability](https://arxiv.org/abs/2609.10399)
(September9); its loss of initiator information concerns statistical
observations and supplies no arithmetic transfer theorem. No external
result is a Lean premise, and no numerical experiments were run.

## Lean audit

Module: formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekGammaMobiusReflectedFrullani.lean.
The leaf has 447 lines, 38 public theorems and six definitions; capstone
pwGammaMobiusReflectedFrullani_closed. Complete scratch and direct
`lake env lean` checks passed, as did the targeted
`lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusReflectedFrullani`.
The accepted proof emits an informational ring-normalization suggestion;
the build also replays existing upstream style warnings. No proof goal
remains open. All 44 public declarations passed the scratch axiom audit,
using only `propext`, `Classical.choice`, and `Quot.sound`.

Formal lint passed. The unrelated umbrella gap seen in the preceding
iteration is now resolved in the shared worktree. All public names have
unique declarations, the RHTower import is wired, and scoped whitespace,
conflict and local Markdown-link checks passed. Index/API and final
process checks are recorded in the attack ledger. Lean checks ran one
at a time in the foreground; no full/umbrella build or numerical
experiment ran. RH remains unproved and the goal active.
