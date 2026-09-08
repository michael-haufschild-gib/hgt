# CCM-FU: fixed processed-core profile and energy tail

- **Stage:** 3-formalized; exact-file and new-declaration axiom checks passed; Lake packaging pending.
- **Parent:** [fixed-core reserve signs](../1-in-progress/ccm-fu-fixed-core-reserve-sign.md).
- **Closed:** Exact common-head representation of every remaining fibre and the whole energy; cancellation of the fixed nonempty head's square-root main term; a common quotient tail with arbitrarily small quadratic energy.
- **Open:** Signed dilation-correlation control, reserve renewal through changing cores, complete selection, uniform signed Abel bound, RH. The [complete energy limit](ccm-fu-fixed-core-energy-limit.md) now assembles all quotient depths.

## Actual source statements

Write H_P(N)=F_P(N,empty). Let R be any remaining finite prime label,
disjoint from the processed set P, and r=product(R). At every cutoff M,

`F_P(M,R)=mu(r)*sqrt(r)*I_P(M,r)`,

where

`I_P(M,r)=(1-w(M,r))*H_P(floor(M/r))+w(M,r)*H_P(floor(M/r)+1)`

uses the literal square-root clipping weight. This is the same fixed P at
both child cutoffs. P need not contain every small prime. Squaring gives
both the active-label and squarefree-integer forms of the full energy:

`Q_P(M)=sum_(R active) r*I_P(M,r)^2`

`=sum_(1<=r<M, squarefree r, primeFactors(r) disjoint P) r*I_P(M,r)^2`.

Now fix a nonempty finite set P of primes and D=product(P). For M>=D,

`H_P(M)=sum_(d divides D) mu(d)*K_d(M)`.

Every fixed positive d has K_d(M)/sqrt(M)->c, where
c=log(2*pi)/2-EulerGamma-1/4. Consequently H_P(M)/sqrt(M)->0.

More strongly, for every epsilon>0 there is one integer T>=1 such that,
for every M and every remaining prime label R with floor(M/product(R))>=T,

`|F_P(M,R)|<=epsilon*sqrt(M)`.

Summing over all such active labels gives

`sum_(R active, floor(M/product(R))>=T) F_P(M,R)^2 <= epsilon^2*M^2`.

The same T works for all labels and cutoffs. It depends on P and epsilon;
no uniformity over changing processed cores is claimed.

## Dependency-closed paper proof

Reindex a fibre by n=r*d. Any shared prime of r and d makes mu(r*d)=0.
For coprime r,d, the source label is R exactly when primeFactors(d) is
contained in P. Apply the already proved masked clipped homothety term by
term. The terminal child term is zero, so both child heads have the same
summation domain. This proves the complete product interpolation identity.

The active labels and squarefree r<M disjoint from P are in bijection under
R->product(R) and r->primeFactors(r). Their Möbius squares equal one.
Reindex the already proved full active-label energy sum using this bijection.

For a fixed processed prime core, a squarefree index with no remaining
prime divides D, and every divisor of D has no remaining prime. Nonsquarefree
channels vanish. Once M>=D, finite source summation therefore gives the
displayed divisor transform. The existing uniform unsigned quotient-tail
mean implies the fixed-d limit. Take the finite sum of these limits; its
coefficient is c*sum_(d divides D)mu(d)=0 because P is nonempty.

Apply this head limit at both floor(M/r) and floor(M/r)+1. The clipping
weights are nonnegative and sum to one, and their square-root-scaled clock
is exactly sqrt(M). The triangle inequality gives the uniform fibre bound.
There are at most M-1 active labels. Squaring the bound and summing proves
the full quotient-tail energy estimate. Every step uses exact source
identities and analytic limits, with no numerical premise.

## Role in the reserve problem

This gives the tail control needed to pass from the actual finite energies
to a fixed-core weighted squarefree limit. For bounded quotient depth,
the remaining expression depends on finitely many adjacent head values.
The [fixed-core density, weighted moments and each actual quotient-block limit](ccm-fu-fixed-core-density-moments.md)
and the [complete energy coefficient series](ccm-fu-fixed-core-energy-limit.md)
are now formalised. The proposed integral correlation formula and its signed
reserve control remain open; the finite experiment does not establish them. A growing processed core requires additional
control beyond these fixed-core statements.

## Lean validation

Module: `GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreProfile`.
Eight public theorems are checked in scratch and the leaf is wired into
`RHTower.lean`. Only the new leaf is emitted. No umbrella or full build is
run. The known Lake packaging audit remains pending to avoid its broad
prerequisite rebuild; exact-file verification is recorded separately.

`lake env lean GaloisForLFunctions/RHTower/MobiusDivisorFixedCoreProfile.lean -o <leaf.olean>`
completed successfully. One external scratch audit checked only these eight
new declarations; each depends solely on `propext`, `Classical.choice`, and
`Quot.sound`. `python3 scripts/formal_tools.py lint` passed, with pre-existing
large-file warnings.

The declaration index was refreshed. All four owned scratch files were
removed after verification; no owned Lean process remained.
