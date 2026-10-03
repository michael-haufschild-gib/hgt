# Natural Ramanujan band: critical divisor profile and moving remainder

- **ID:** pm-ramanujan-band-critical-profile
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Route PM; `pm-paired-cutoff-gram-budget.md`
- **Goal:** Control the actual anchored band norm by separating its source-derived fixed-index profile from the moving signed remainder. RH/admission remain open.

## Exact source

Fix epsilon>0, s=1+epsilon and alpha=1/zeta(s). The actual weight is
`a(q)=alpha*mu(q)/prod_(p|q)(p^s-1)`. Let

`h(n)=mu(n)^2*prod_(p|n)(1-p^(-s))^(-1)`.

Then `|a(n)|=alpha*h(n)/n^s`. For the full band X<q<=2X,

`S_X(N)=sum_(d<=N) b_X(d)*floor(N/d)`,

`b_X(d)=alpha*mu(d)*d^(-epsilon)*h(d)
 *sum_(X/d<m<=2X/d, gcd(m,d)=1) h(m)/m^s`.

All prime/composite channels are retained. Nonsquarefree d has zero cofactor.

## Paper derivation of the fixed-index limit

Write h=zeta*R. The multiplicative residue has local values
`R(p)=1/(p^s-1)`, `R(p^2)=-(1-p^(-s))^(-1)`, and R(p^k)=0 for k>=3.
Thus `sum_n |R(n)|/n` converges by its absolutely convergent Euler product.
Finite hyperbola interchange and dominated convergence give mean

`H=prod_p (1-1/p)*(1+h(p)/p)>0`.

The product is positive because its factors differ from one by a summable
sequence and every factor is positive. Restricting h to gcd(n,d)=1 changes
its mean to `H*prod_(p|d)(1+h(p)/p)^(-1)`. The same residue proof applies;
only finitely many local factors change. Partial summation on [x,2x] gives
the weighted band limit, hence for each fixed d>=1,

`X^epsilon*b_X(d) -> K*mu(d)*prod_(p|d) g(p)`,

`g(p)=p/(p+1-p^(-epsilon))`,
`K=alpha*H*(1-2^(-epsilon))/epsilon > 0`.

The finite floor sum therefore gives, for each fixed N,

`X^epsilon*S_X(N) -> K*F(N)`,

`F(N)=sum_(d<=N) mu(d)*prod_(p|d)g(p)*floor(N/d)
     =sum_(n<=N) f(n)`,

`f(n)=prod_(p|n) (1-p^(-epsilon))/(p+1-p^(-epsilon))` (n>=1).

The second equality is exact finite Möbius/divisor inversion, including
prime powers. Thus F is positive and increasing, with F(1)=1. Each prime
factor of f lies in (0,1/p). For every delta>0,

`sum_n f(n)/n^delta < infinity`:

the local positive Euler mass is
`1+f(p)*p^(-delta)/(1-p^(-delta))`, bounded by exp(C_delta*p^(-1-delta)).
Consequently `F(N)<=C_delta*N^delta`. Taking delta<1/2 proves
`sum_(N>=1) F(N)^2/[N(N+1)]<infinity`.

This derivation is source-based and dependency-closed on paper. Lean work
must certify the actual band limit as well as the positive profile; a
standalone constructed positive sequence is not an adequate replacement.

## Hard remainder conjecture

Prove a uniform anchored L2 bound for `X^epsilon*S_X-K*F`, allowing a
logarithmic loss consistent with the active band-variance conjecture.
Do not infer it from fixed-index convergence or claim strong convergence.
The infinite spatial tail and growing balanced cofactors remain in scope.

Absolute residue-error bounds may control an initial spatial range, but
cannot dispose of the remainder. The next mathematical attack is to keep
the squarefree-residue convolution inside that full signed remainder and
look for cancellation before taking norms.

## Corpus audit and status

Search85 partial: no moving-cofactor producer. Search86 partial: existing
Euler-product, squarefree multiplicativity, and coprime identities; no
ready-made actual band asymptotic. Search87 complete: positive multiplicative
summability machinery is available; no profile theorem returned. All
candidate/source statements and ingredient sets inspected. Compiler
metadata is largely pending/stale, so applicability requires Lean checks.

Relevant sources: `PMPowerDampedMobiusRamanujanCofactors`,
`PMPowerDampedMobiusRamanujanWeights`, `PMPowerDampedMobiusDivisorHaar`,
`PMPowerDampedMobiusRamanujanKernelMass`, and
`Sieve/SquarefreeTotientResidueKernel`. No numerical experiment or RH
premise enters. Lean formalization is not yet complete.

## Remainder target used in the proof attempt

The logarithmic normalized remainder ceiling is stronger than necessary.
The working sufficient target is instead

`sum_(N>=1) |S_X(N)-K*X^(-epsilon)*F(N)|^2/[N(N+1)]
 <= C_epsilon*X^(-epsilon)`.

This reserves damping for the moving tail and still gives summable dyadic
band norms. No sharp critical rate, strong normalized convergence, or
critical-zero simplicity assertion is needed. The earlier logarithmic
comparison remains an optional stronger conjecture, not a required goal.

The residue calculation provides a precise attack on this remainder:
`R(p)=1/(p^(1+epsilon)-1)`, `R(p^2)=-h(p)`, R(p^k)=0 for k>=3.
Absolute weighted residue mass at exponent1 is finite. At the spatial
moving boundary d~X, however, the m=1 cofactor is the original signed
Mobius channel; it cannot be replaced by the positive fixed-index profile.
Keep its cross terms with every smaller cofactor inside the square.

## Exact normalization exposed by the profile

Let `Z=sum_(n>=1) f(n)/n`. This is finite and at least1 by the proved-paper
positive weighted summability. The reciprocal profile mean is exactly Z:
finite Abel summation gives

`sum_(N<=T) F(N)/[N(N+1)] = sum_(n<=T) f(n)/n-F(T)/(T+1)`;

the subpower bound makes the last term tend to zero. The local Euler mass
of Z is `1+f(p)/(p-1)`. Direct algebra gives

`[(1-1/p)*(1+h(p)/p)] * [1+f(p)/(p-1)] = 1`.

Both products are absolutely admitted, so `H*Z=1`. Thus the band constant
can also be written `K=alpha*(1-2^(-epsilon))/(epsilon*Z)`. This fixes the
main term's normalization from an admitted positive profile. It agrees
with the actual reciprocal Mangoldt mean's prime-band asymptotic; no
strong L2 convergence or absence of escaping energy follows.


## Joint-residue cancellation attack (2026-10-02)

Keep the exact coprime weight `h_d(m)` (zero when `(d,m)>1`) and set
`R_d=mu*h_d`. For a prime p put `B=h(p)`. The two-index coefficient
`J(d,r)=mu(d)*h(d)*R_d(r)` has local polynomial

`1+(B-1)y-B*y^2-B*x+B*x*y = (1-y)*(1+B*(y-x))`.

Its diagonal collapse is exact: `sum_(d|l) J(d,l/d)=mu(l)`.
Proof: the degree-one coefficient is `(B-1)-B=-1`, the degree-two
coefficient is `-B+B=0`, and every higher coefficient vanishes. Coprime
factorization then gives the identity for every l. This is an arithmetic
conservation law, not an absolute bound.

Before taking norms, the full band therefore has the exact expansion

`S_X(N)=alpha*sum_(X<l*k<=2X) (l*k)^(-s) * T_l(N)`,
`T_l(N)=sum_(d|l) d*J(d,l/d)*floor(N/d)`.

The linear slope of T_l is mu(l). The complete band's slope cancels by
`mu*zeta=delta`; all remaining terms are anchored residue terms. The
prime-square layer is essential to that cancellation. It must not be
removed as a small correction before the signed square is formed.

Next proof attempt: exploit this exact local cancellation with the
moving product cutoff retained. At one prime the spatial operator is
`1-p*U_p`, where `U_p F(N)=F(floor(N/p))`. Products of these operators do
not preserve positivity, so the joint identity alone supplies no energy
bound. The missing estimate remains the signed anchored energy of the
full moving product sum.


## Lean checkpoint: positive profile

`PMRamanujanBandProfile.lean` now contains the exact finite floor identity,
positive weighted summability for every delta>0, subpower growth, F(1)=1,
and finite anchored energy. All 13 public declarations report only
`propext`, `Classical.choice`, and `Quot.sound`. The old-mode targeted
build passed (only the new leaf built, 106s); final actual-file
`lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandProfile.lean`
passed with no diagnostics. Umbrella wired. An initial combined axiom/API
scratch failed only because a noncomputable API was used in a computable
example; no axiom result or profile declaration failed.

This certifies the constructed profile, not its actual-band limit. The
next scratch proves the literal coprime cofactor identity, signed residue
prime-power values, reciprocal residue admission, and fixed-mask density.
Actual weighted-band asymptotic, normalization, and moving norm remainder
are still separate proof obligations.

Search88–90 were partial with complete inventories and mostly pending or
stale compiler metadata. All candidate/source statements and ingredient
sets were inspected. They supplied multiplicative and squarefree tools;
none supplied the moving signed band estimate or the joint-residue norm
cancellation. No numerical experiment was used.

Global lint ran: no own-module finding, twelve unrelated missing umbrella
imports (CCMApertureChainProfile, CCMApertureTranslationChains,
CCMEulerEventualCarrier, CCMExponentialRampPrimeMoment,
CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
CCMRestrictedWeilPolarShiftLower, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving).


## What the absolute residue argument can and cannot pay

The prime-square coefficient `R_d(p^2)=-B_p` is of order one outside
the finitely many deleted primes. Thus absolute residue summability
extends to every exponent theta>1/2, but not by this Euler bound to the
critical exponent 1/2. The first-prime coefficient is already summable
with a positive extra exponent; prime squares are the limiting layer.
The elementary hyperbola estimate is

`|sum_(n<=x) h_d(n)-H_d*x|
 <= sum_(r<=x)|R_d(r)| + x*sum_(r>x)|R_d(r)|/r`.

This proves fixed-mask density and controls an initial spatial range.
After inserting it separately into each d-cofactor, the spatial floor
factor still grows and the full anchored band tail is unpaid. Therefore
absolute residue admission is only a source-limit ingredient. The hard
conjecture is unchanged: bound the complete signed remainder square,
with prime-square terms and all cross-cofactor terms retained. No
claim of an RH energy improvement follows from the density proof.


## Weighted-band limit without an additional counting error hypothesis

The exact residue expansion permits dominated convergence directly:

`sum_(X<m<=2X) h_d(m)*m^(-1-epsilon)
 = sum_r R_d(r)*r^(-1-epsilon)
     *sum_(X/r<k<=2X/r) k^(-1-epsilon)`.

For y>0 the elementary interval bound
`y^epsilon*sum_(y<k<=2y) k^(-1-epsilon)<=2` holds: there are at most
2y positive integer summands and every k exceeds y. Hence, after
multiplication by X^epsilon, each r term is bounded by
`2*|R_d(r)|/r`, already admitted by the new residue theorem.
The power-tail asymptotic supplies the individual limit
`R_d(r)/r*(1-2^(-epsilon))/epsilon`. Dominated convergence then gives
`X^epsilon*weightedBand_d(X) -> H_d*(1-2^(-epsilon))/epsilon`.
This avoids importing a square-root counting estimate. It remains a
fixed-mask theorem and does not dominate the full spatial energy sum.

Lean next: formalize this scalar window limit using the existing
`RpowHarmonicTailAsymptotic`, then prove the finite local-mask density
ratio and identify the actual fixed-index band limit with K*F. Keep
separate the still-open joint signed norm estimate; these scalar limits
alone do not imply uniform integrability.


Search91 (partial, inventory complete generation1185190) returned generic
dyadic decompositions and dominated-convergence tools, but no direct
power-window limit. The already inspected
`HTGeometry/RpowHarmonicTailAsymptotic.lean` is the relevant local source:
`tendsto_tsum_shift_rpow` gives the scaled tail constant for every negative
power parameter. Subtract the two tails and handle natural floors to
obtain the scalar dyadic window limit above. All Search91 candidate/source
statements and ingredient proposals were inspected.


## Lean checkpoint: actual cofactor residue

`PMRamanujanBandResidue.lean` passed its targeted old-mode build (only the
new leaf built, 255s); umbrella wired. The 18 public declarations include:

- the literal identity `mu(m)*a(d*m)=a(d)*m^(-1-epsilon)*h_d(m)`;
- exact finite cofactor reconstruction from the nonnegative squarefree
  inner weight and its signed residue;
- `R_d(p)=C_d(p)-1`, `R_d(p^2)=-C_d(p)`, and zero for all higher powers,
  where C_d(p) is the actual prime correction, zero when p divides d;
- absolute reciprocal residue summability for every fixed d!=0;
- the actual fixed-mask density limit `sum_(n<=x)h_d(n)/x -> sum_r R_d(r)/r`;
- exact prime profile/source factor `g(p)=B_p/(1+B_p/p)`;
- the complete weighted product-cutoff residue expansion, including the
  multiplier-one boundary.

The first residue scratch had two coercion/rewrite errors; the next
exposed an omitted prime proof and two simplifier issues. All were fixed
without weakening statements. The mean theorem and all core source
identities then passed together. All 18 public declarations passed the /tmp axiom audit with only
propext, Classical.choice, and Quot.sound. Final actual-file
`lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandResidue.lean`
passed with no diagnostics. The initially interrupted axiom process had
no live process or handle and was restarted once; the replacement exited0. The weighted dyadic asymptotic and finite-mask
density product relation remain Lean-open; the full signed norm estimate
remains mathematically open.


## Exact remainder kernel for the hard norm attack

Set `C_epsilon=(1-2^(-epsilon))/epsilon`,
`W(y)=sum_(y<k<=2y)k^(-1-epsilon)`, and
`theta(y)=y^epsilon*W(y)-C_epsilon` for y>0.
It is bounded and tends to zero as y tends to infinity, but equals
`-C_epsilon` for y<1/2. With the proved-paper density identification,
the exact profile-subtracted band is

`E_X(N)=alpha*X^(-epsilon)
 *sum_(d<=N) mu(d)*h(d)*floor(N/d)
   *sum_r R_d(r)/r * theta(X/(d*r))`.

Each inner residue sum is absolutely convergent by the new Lean theorem;
there are finitely many d for each N. Reindexing gives the sharper form

`E_X(N)=alpha*X^(-epsilon)*sum_l theta(X/l)/l*T_l(N)`,
`T_l(N)=sum_(d|l) d*J(d,l/d)*floor(N/d)`.

The l sum is also absolutely convergent at each fixed N, because only
d<=N occur and each corresponding residue reciprocal sum is admitted.
The moving region l>2X has theta=-C_epsilon and cannot be omitted as a
small kernel tail. Its cancellation with l<=2X remains inside the square.

Next hard conjecture: the anchored squared norm of
`sum_l theta(X/l)/l*T_l` is `O_epsilon(X^epsilon)`. This is exactly the
working damping-margin remainder target after the outside X^(-epsilon)
factor. Attack this whole signed kernel sum, retaining the joint local
polynomial and cross terms. Do not spend the next producer attempt on
another absolute cofactor bound or a conditional RH receiver. Scalar
profile/source formalization has advanced, but no upper bound on this
hard kernel norm has yet advanced.


## Continued hard-kernel audit

Search92 was partial with a complete inventory (generation1185273).
Search93 was partial with coverage metadata pending (generation1185289).
All candidate/source statements and ingredient proposals were inspected.
The former returned no matching producer; the latter returned the actual
Farey large-sieve and Ramare decomposition interfaces. The Ramare bounds
retain prime/cofactor supremum hypotheses, so they do not discharge the
PM estimate. Sources `Sieve/LargeSieveDual`, `Sieve/LargeSieveFarey`, and
`Sieve/LargeSieveCircleSharp` were inspected directly. Their general loss
is of denominator-square size. Removing the logarithm does not remove
that size. A sharper source mean-square estimate must also control the
signed totient mean already retained by `PMRamanujanPeriodDiagonal`.
No period average has been substituted for anchored energy.

A clock Mellin separation also has an explicit unpaid boundary. The
subtracted theta kernel is constant near zero, so its Mellin integral
there diverges on the positive real exponent side. Using the unsubtracted
window kernel instead admits the scalar Mellin transform, but clock
X<1 contains the q=1 term alpha*N, which has infinite anchored spatial
energy. It must be removed before any Hilbert-valued interchange. Scalar
Mellin continuation therefore does not supply the missing uniform norm.
Neither observation retires the signed-kernel route.


## Clock-averaged signed quadratic candidate

The pointwise-X bound may demand more than admission needs. Retain the
same actual band S_X, with X real and X>=1. For fixed eta>0 consider

`integral_(1,infinity) X^(eta-1) * ||S_X||_anchored^2 dX`.

Its finiteness would give absolute Bochner integration of S_X against
`dX/X` by Cauchy-Schwarz. The exact clock integral of each q>=2 band
indicator is log2, so this recovers the actual full source. This is a
candidate producer target, not a proved bound or an added Lean receiver.

For a finite denominator set with q,r>=2, the clock overlap is exactly

`L_eta(q,r)=max(0, min(q,r)^eta-(max(q,r)/2)^eta)/eta`.

Therefore the clock-averaged anchored energy is the complete signed
quadratic `sum_(q,r) a(q)*a(r)*G(q,r)*L_eta(q,r)`. The overlap vanishes
when max(q,r)>=2*min(q,r); otherwise all prime and composite cross terms
remain. No cofactor or period mean is separated. The profile main term
is admitted in this norm for eta<2*epsilon, so subtraction does not
change the central finiteness question in that range.

Proof attempt to pursue: use the actual squarefree local residue and
natural product ordering in this complete quadratic. Generic frequency
separation still pays Q^2, and bounding prime-only branches separately
loses the composite cancellations. A largest-prime recursion must retain
the full balanced-cofactor branch and all branch cross products; it
cannot treat fixed-cofactor limits as a uniform estimate. The unresolved
mathematical task is the signed quadratic bound itself, not setting up
its receiver.


Search94 was partial with complete inventory generation1185336; all
candidate/source statements and ingredient groups were inspected. It
returned generic dyadic Fourier/Gram tools, not an actual signed clock
producer. Both new leaves are now fully audited. No own Lean process
remains live. Scratch sources and logs were removed after recording the
certificates; current theorem sources and both formalized cards are the
persistent checkpoint. The RH goal remains active and unmet.

## Complete clock cutoff and joint-residue linear mode

The finite-clock target must retain the clock endpoint T. For q,r>=2,

`L_(eta,T)(q,r)=max(0,min(T,min(q,r))^eta-(max(q,r)/2)^eta)/eta`.

Thus the integral over 1<=X<=T of X^(eta-1) times the squared complete
band norm equals the finite signed sum over 2<=q,r<=2T with this kernel.
Truncating denominators at Q but integrating all clocks instead adds
incomplete final bands on Q/2<X<Q. The all-clock finite-support formula
above is correct, but that truncation cannot silently replace this target.
The producer sought is a bound independent of T on the complete-clock
quadratic, for some 0<eta<2*epsilon.

The common-prime Gram recursion alone does not close it. Simultaneous
prime dilation gives L_(eta,T)(pq,pr)=p^eta*L_(eta,T/p)(q,r), and the
common-prime coefficient is (p-1)*p^eta/(p^(1+epsilon)-1)^2. Its prime
sum converges when eta<2*epsilon. The two single-prime terms, however,
carry different clock overlaps and remain unpaid signed boundary forms.
Also, the Gram recursion assumes both cofactors exceed one: its separate
cofactor-one primitive is N, which has infinite anchored energy. Only
the combined prime difference has finite energy. No discarded term has
been assigned a favorable sign.

Search95/96/97 returned no actual producer. Searches95/96/97 had complete
inventories and partial=false (generations1185399/1185446/1185490).
Direct inspection of GramResidueDecomposition and BaezDuarteGramReduction
shows exact individual-entry reductions, not a signed natural-band
quadratic bound. Search98 was partial with complete inventory1185504;
its endpoint/interpolation candidates supply neither damping convexity
nor the missing Hilbert bound. The already formalized lack of a Hilbert
tangent cannot be used as a disproof of zeroth-order admission.

There is a further exact paper identity in the joint residue. Write
B_p=h(p)=p^(1+epsilon)/(p^(1+epsilon)-1). For fixed l, expanding
`d*floor(N/d)=sum_(q|d)P_q(N)` in T_l gives the following local table for
the coefficient of P_q. If l has p-exponent one, the coefficients at
q-exponents zero and one are -1 and -B_p. If l has p-exponent two they
are zero and B_p. All coefficients vanish for p-exponent at least three.
These follow directly from the audited R_d(p), R_d(p^2), higher-power
formulas, including the masked value C_d(p)=0 when p divides d.
Multiplication of the finite local tables therefore gives, for coprime
squarefree t,u,

`T_(t*u^2)(N)=mu(t)*h(u)*sum_(v|t) h(v)*P_(u*v)(N)`.

T_l is zero unless l is cube-free. Its q=1 coefficient is exactly mu(l).
Consequently `U_l(N)=T_l(N)-mu(l)*N` is a finite combination of nontrivial
periodic primitives and has finite anchored energy. In contrast, T_l
itself has infinite anchored energy whenever l is squarefree: U_l is
bounded, so |T_l(N)|>=N/2 eventually, giving terms bounded below in its
energy series. This is an exact algebraic obstruction to taking Hilbert
norms term by term in the theta-residue expansion. Absolute reciprocal
residue summability for each fixed spatial coordinate does not justify
that interchange.

Status of this local-table classification: paper derivation only; no new
Lean declaration or audit claimed. It is retained inside the active
producer problem, not presented as a completed no-go or RH progress.
The positive periodic part U_l is explicit, but its signed tail still
requires cancellation across squarefree l. Splitting off mu(l)*N in an
infinite series requires a separately justified conditional cancellation;
it cannot be inferred from the absolute convergence of the unsplit
fixed-N expression.

Assessment: corrected the exact target and identified why one tempting
norm interchange fails. No small-positive anchored upper bound has been
proved. The next estimate must group the squarefree linear mode before
any Hilbert estimate and retain the natural product boundary. A generic
Euler contraction over arbitrary prime supports would contradict the
completed-aperture obstruction and is not a candidate producer.

## Finite cancellation before the Hilbert estimate

The linear obstruction can be removed at a complete finite cutoff,
without taking a conditional infinite sum. Use the literal coefficients

`K(d,r)=a(d)*r^(-1-epsilon)*R_d(r)`.

The exact product-fibre drift is

`sum_(d*r=l) K(d,r)=a(1)*mu(l)*l^(-1-epsilon)`.

Proof: expand R_d=mu*h_d and use the audited identity
`a(d)*m^(-1-epsilon)*h_d(m)=mu(m)*a(d*m)`.
Reindex the finite triple sum by k=d*m. The inner mu divisor sum
vanishes unless k=1. This proof uses the actual source, including all
masked cofactor primes; it does not assume the paper local-table
classification above.

Define bounded atoms and the retained clock by

`V_l(N)=-sum_(d*r=l)K(d,r)*d*fract(N/d)`,
`W_Q(l)=sum_(k<=Q/l)k^(-1-epsilon)`.

Then V_l is the uncentered joint floor atom minus
`a(1)*mu(l)*l^(-1-epsilon)*N`. Its norm is at most
`sum_(d*r=l)|K(d,r)|*d`, uniformly in N, so each atom has finite
anchored energy. Exact finite hyperbola interchange reconstructs the
literal centered natural prefix as `sum_(l<=Q)W_Q(l)*V_l`.
Consequently the actual band X<q<=Y is exactly the difference of these
two complete finite sums at Y and X.

The scalar drift cancels already in each complete finite band:
`sum_(l*k in (X,Y])mu(l)*(l*k)^(-1-epsilon)=0` for X>=1,
by mu*zeta=1. Thus no infinite Mertens rearrangement is required to
remove it. The earlier warning remains applicable to estimating the
uncentered theta atoms separately.

Lean scratch passed the actual drift, centered-atom identity, uniform
atom bound, atom-energy summability, exact prefix and band reconstruction.
Promoted to PMRamanujanJointResidue; the targeted old leaf build passed
(new leaf 105s), all ten public axiom audits passed with standard axioms,
and final actual-file lake env lean exited0 with an empty log. Umbrella
wired exactly once. A nested-sum inference timeout was
resolved by giving the reindexing function explicitly; no heartbeat
increase. No new mathematical energy bound has been obtained: the
complete signed sum of bounded atoms still needs a uniform upper bound.

The first local energy conjecture for this representation was that the
prime-square partner might erase the large prime channel. The exact
paper calculation instead gives, with s=1+epsilon,

`V_(p^2)=-p^(-s)*V_p`,
`W_Q(p)*V_p+W_Q(p^2)*V_(p^2)
  =(sum_(k<=Q/p, p does not divide k) k^(-s))*V_p`.

This follows from R_1(p)=B_p-1, R_1(p^2)=-B_p, R_p(p)=-1,
a(p)=-a(1)*B_p*p^(-s), and fract(N)=0. The clock identity is
finite multiples reindexing. The remaining coefficient is positive
when Q>=p, so this pairing does not erase the prime channel. This
local check is paper-only; it neither bounds nor retires the full signed
producer. The next estimate must retain squarefree-composite cross terms.

Search100 was partial with complete inventory1185571; Search101 was
partial with complete inventory1185617. Candidates, source arguments,
and ingredient proposals were inspected. Direct reading of
EulerDeletionCoprimeColumnCancellation confirms its near-linear bound
uses a complete inner coprime floor column. The moving PM product cutoff
does not supply that complete column. No such hypothesis was silently
inserted into the new finite source identities.

## Signed-correlation and retained prime-block attempt (2026-10-02)

Assessment: the preceding finite drift theorem supplies valid atoms, but
this continuation has not proved a small-damping energy upper bound.
No new Lean leaf or conditional receiver was added.

The attempted short-interval transfer does not close the estimate.
`Sieve/ScaledTwoRangeWindow.lean` supplies a normalized little-o mean
square, whereas PM requires an integrable power-weighted anchored square.
The sharper statements in `MoebiusDiscreteMeanSquare` and
`MoebiusUnweighted` retain a twist/correlation bound as a premise.
`MobiusAdditiveTriangleChowlaFrontier` similarly retains the one-sided
subpower off-diagonal bound; `MobiusOffDiagonalAnalyticSourceUniversalityLaw`
propagates that premise. Neither is an unconditional producer. Taking
absolute values of the shifted correlations would also discard the
composite cross terms being sought. The existing generic Farey estimate
still has its denominator-square loss. These observations reject the
proposed transfers, not the PM route or a signed correlation proof.

A more local calculation retains the clock boundary exactly. Extend the
unscaled atoms to real x by

`U_n(x)=-sum_(d*r=n) J(d,r)*d*fract(x/d)`.

Here J is the actual residue from the local polynomial above; in
particular `U_1(x)=-fract(x)`, which must not be replaced by zero between
integers. For p prime, p not dividing n, and B=(1-p^(-s))^(-1), the local
table gives the exact paper identities

`U_(p*n)(x)=(B-1)*U_n(x)-B*p*U_n(x/p)`,
`U_(p^2*n)(x)=-B*U_n(x)+B*p*U_n(x/p)`,
`U_(p*n)(x)+U_(p^2*n)(x)=-U_n(x)`.

These follow directly by grouping the (d,r) prime exponents (0,1),
(1,0), (0,2), and (1,1); they also preserve the already audited drift.
They are paper-only statements in this checkpoint.

For an integer cutoff Q define

`L_Q(n)=sum_(k<=Q/n, p does not divide k) k^(-s)`.

Finite multiples reindexing gives
`L_Q(n)=W_Q(n)-p^(-s)*W_Q(p*n)`. Thus the entire n,p*n,p^2*n block,
after extracting the common factor alpha*n^(-s), is exactly

`L_Q(n)*U_n(x)
 +B*p^(-s)*L_Q(p*n)*(U_n(x)-p*U_n(x/p))`.

Both L factors are nonnegative and `L_Q(p*n)<=L_Q(n)`. This is a genuine
finite-cutoff cancellation, but does not show that its spatial dilation
cross term has the sign needed for an upper bound. Summing the blocks
before squaring introduces all cross terms between distinct p-free n.
No termwise sign or independent-phase law is available for that sum.
In particular, this calculation does not justify the false
support-independent completed-prime budget already ruled out in Lean.

Next direct mathematical target: bound that full p-free mixed form with
the two different retained clocks L_Q(n) and L_Q(p*n). Keep the source
change and product boundary in the form. Do not formalize this identity
alone and describe it as a solution of the upper-bound problem.

Corpus audit: searches102--107 inspected candidate statements, source
arguments, and proposed ingredients. Inventory was complete in the
reported snapshots; generations were 1185864, 1185913, 1185948, 1185989,
1186003, and 1186087 respectively. Searches102/104 were complete;
103/105/106/107 were partial. Compiler metadata remains largely
pending/stale. Search107's logarithmic raw-prefix energy saving does not
cross the already documented half-damping threshold. Its damping-flow
proposal is an existing open attempt, not a new producer. All six search
processes exited, and their owned scratch JSON files were removed.


## Nearby-prime resonance after reciprocal-mean removal (2026-10-02)

The growing-cofactor test now has an exact positive covariance profile.
`PMRamanujanNearbyPrimeResonance` realizes the actual primitive as
`F_r(x)=P_r(floor x)/x` in the full-line Hilbert space. For normalized
dilation D, its profile `K_r(c)=Re <F_r,D_c F_r>` is continuous on c>0,
with `K_r(1)=G(r,r)>0` and `|K_r(c)|<=G(r,r)`. Exact prime insertion gives

`|G(p*r,q*r)-sqrt(p)*sqrt(q)*K_r(p/q)|
 <= (sqrt(p)+sqrt(q)+1)*G(r,r)`.

For every r>1 and B, there are distinct primes r<p<q<2p with
`G(p*r,q*r)>B`. If r is not a prime power, both reciprocal means vanish
and the centered Gram is still greater than B. Thus reciprocal-mean
removal cannot give a uniform growing-cofactor covariance estimate.
The positive survivor is the finite continuous profile/error law, not
merely the negative conclusion. Scratch and targeted old leaf build passed;
all 14 public declarations have only standard Lean axioms. Final actual-file
audit passed with exit 0 and no diagnostics. The detailed paper proof,
formal scope, and unrelated global-lint failures are on
`../5-failed/pm-ramanujan-nearby-prime-resonance.md`. Umbrella wired once;
no full or umbrella build.

Assessment against the RH producer: this resolves a failed local estimate
and identifies a coherent same-cofactor contribution that survives mean
removal. No upper bound on the complete signed energy was gained. The
next proof attempt must combine different cofactor branches before taking
norms, preserving their moving prime intervals and the clock boundary.
The exact finite joint-residue reconstruction remains the source to bound.
Do not replace the signed sum by absolute profile overlaps: the new law
shows why that discards the required cancellation.

Search112/113 returned exact dilation and cofactor decompositions, but no
such upper estimate. Their complete coverage and the explicit retained
boundary obligations are recorded on the resonance card. The suggested
antidiagonal ingredient still says “Ensure cancellation”; this is the
unproved mathematical step, not an available lemma or an admissible premise.


## Coupled-moment and shifted-covariance attack (2026-10-02)

Assessment: the preceding nearby-prime leaf was verified mathematical
progress, but this continuation has not improved the small-damping
anchored-energy upper bound. No new Lean receiver, axiom, or auxiliary
bound was added. The mathematical problem remains the complete signed
quadratic form, with growing cofactors and the moving cutoff retained.

First attempt: keep the actual zeta/Mobius product together on the Mellin
side and ask whether the current critical moment plus three-lines bound
pays the missing cofactor energy. Direct reading of
`MoebiusMollifiedCriticalMoment.exists_integral_normSq_zeta_mul_edPoly_mob_critical_le`
and `MoebiusMollifiedErrorThreeLines.exists_integral_normSq_mobMollifiedError_le_threeLines`
shows the present estimate still separates the two factors by
Cauchy--Schwarz. Its critical-edge bound contains
`sqrt((2N+8X^2(1+log(X^2)))*(1+log(X^2))^4*D*N*(1+log N)^4)`.
For a fixed physical frequency window and an auxiliary height N growing
only logarithmically with X to control the Gaussian tail, this upper
bound retains an X factor, up to logarithms. The right-edge bound at
Re(s)=3 is O(X^(-2)). Three-lines therefore leaves the power
`X^(1-3*lambda)`, `lambda=(sigma-1/2)/(5/2)`, which does not decay for
1/2<sigma<=1. This diagnoses this particular estimate; it is not a
falsification of a coupled-moment proof or of PM. Changing the Gaussian
window alone does not remove the critical-edge length cost.

Second attempt: use the actual truncated Mobius convolution before
Cauchy--Schwarz. `convolution_one_cutIcc_mobCoeff_of_le` and
`mobTailCoeff_eq_zero_of_le` give exact vanishing through the cutoff.
`MollifierDetection.detection_poly_eq` retains the entire product, and
the mollified twisted-diagonal leaves identify its exact collision
energy. But a vanishing head and a coefficient-square sum do not control
a fixed frequency window: the signed unequal-index contribution remains.
The returned proposed ingredient set explicitly retains “Bound
off-diagonal term”. No such premise was treated as a theorem. The
available long-window mean-square estimates cannot be used as uniform
estimates for the fixed windows required by the full anchored norm.

Third attempt: recover the missing cancellation from physical shifted
correlations and exact finite counting. Direct reading of
`MobiusDivisorFiniteClockCountingCancellation` shows that its nonpositive
quantity is energy increment PLUS the signed mixed term. The mixed term
cannot be dropped. Search118 returns an exact CRT floor-count expression
for joint divisibility and an lcm-fibre double-centering identity, not an
upper bound on the complete moving signed remainder. These are valid
source identities, but no comparison of translation-averaged covariance
with the actual anchored source has been proved here. A fixed-lag density
calculation would leave that same uniformity problem unpaid and was not
substituted for the requested frontier work.

The coupled spectral target remains concrete. For the literal finite
power-damped Mobius Fermi sum, the finite-sum generator Mellin formula
has multiplier

`(1-2^(1-s))*zeta(s)/s * sum_(d<=X) mu(d)*d^(-s-epsilon)`.

On Re(s)=1/2 the entire product must remain inside the squared modulus.
A common bound on its full t-integral, with the literal Fermi/parity and
1/s factors, would bound the finite native prefixes and then the actual
source by Fatou. This is a proof target, not a new formal implication or
a proved upper bound. The existing Ramanujan transfer-kernel mass is
already finite; proving another transfer estimate would not pay this
native coupled moment. The next proof attempt must attack its signed
unequal-index term, or the same term in the finite joint-residue form.

Corpus searches114--118 all terminated successfully. 114,116,117,118
were complete; 115 was partial with semantic retrieval unfinished.
Reported generations were 1186682,1186682,1186729,1186737,1186775;
inventories complete, compiler metadata largely pending/stale. Candidate
statements, source arguments, and ingredient obligations were inspected.
No relevant search result was accepted as compiled proof. No build was
needed because this turn changed only the research log. RH remains
unproved and the goal remains active.

## Growing cofactor packets and the actual large-prime sector (2026-10-02)

The direct cofactor-cancellation conjecture fails more strongly than the
fixed-cofactor resonance showed. Include r=1 and write
`B(p,R,N)=sum_(1<=r<=R) a(pr)P_pr(N)`. For R<p and N<p, the actual
weight and primitive recursions give
`B(p,R,N)=(alpha*N+Z_(R-1)(N))/(p^(1+epsilon)-1)`.
The existing uniform sublinear bound on Z makes this head positive
uniformly in every growing R. No averaging over residue classes is used.

At the literal natural cutoff P^2, take all primes P<p<=2P and all
cofactors r<=P^2/p. Denominator membership and nonduplication are proved.
The anchored sector energy on 1<=N<P is eventually at least
`alpha^2*P*(sum_p 1/(p^(1+epsilon)-1))^2/16` and tends to infinity for
every 0<epsilon<1/2, by the existing unconditional prime-shell lower
bound. This is a subset of actual denominators; no inference to the
complete signed prefix energy is made.

`PMRamanujanGrowingCofactorHead` contains ten public declarations. The
scratch proof, targeted old-mode build, all ten standard-axiom audits,
and final actual-file Lean audit passed; umbrella wired. Global lint
reports eleven unrelated missing umbrella imports, with no own-module
issue.

Assessment: this creates a source-specific obstruction and its uniform
positive survivor, but does not improve the hard small-damping upper
bound. A successful proof must control the complementary sector's
signed interaction with these whole growing packets. The next candidate
is an actual relative-cancellation law on the moving head, using finite
Hilbert-valued Abel summation, signed density-tail decay, and the actual
Ramanujan truncation tail. Its estimates still leave the positive power
P^(1-2epsilon); eliminating that growth remains the RH-producing problem.
The derivation and a further source-reproduction profile are recorded in
`../3-formalized/pm-growing-cofactor-prime-head.md`. No receiver with new premises was
added. Searches119--122 terminated; 120--122 complete, with mixed
compiler freshness. Their proposed ingredients were treated as proof
suggestions only.


## 2026-10-02 — signed complementary-source estimates closed

Route PM; hard producer remains complete finite energy for dampings cofinally
approaching zero. New `PMRamanujanComplementarySourceBounds` proves the exact
signed hyperbola split, an eventual logarithmic centered-source bound, and a
quantitative natural Ramanujan truncation error. All three exports passed the
targeted old-mode build, final actual-file audit, and standard-axiom audit.
Umbrella wired; no own lint finding. Searches123–125 completed; compiler
freshness mixed, semantic coverage unmeasured. All source applicability was
checked in Lean.

Assessment: source estimates needed for actual complementary cancellation are
now discharged. They have not removed the positive power in the hard energy
upper bound. The next active proof compares whole-prefix energy with the
already divergent large-prime sector on 1<=N<P at denominator cutoff P^2,
then identifies the literal complement and proves its negative mixed-energy
law. Spatial splitting at sqrt(P), followed by weighted Cauchy–Schwarz, is the
current argument. See `../3-formalized/pm-complementary-prime-sector-cancellation.md` and
`../3-formalized/pm-complementary-source-bounds.md`. No RH claim.

## 2026-10-02 — actual complementary cancellation closed

`PMRamanujanComplementaryCancellation` proves all three moving-head ratios: complete/sector energy tends to zero, literal complement/sector energy tends to one, mixed/sector energy tends to minus one. Targeted old-mode build, final actual-file check and all eight standard-axiom audits passed. Umbrella wired once. Global lint has eleven unrelated unreachable-module errors, no owned finding. Source-bound and exported mass-bound audits also passed.

Contribution: the actual complementary interaction cancels the divergent growing-cofactor sector at leading order. Limitation: the residual upper estimate retains P^(1-2epsilon), so the global small-damping producer remains open. Closed card: `../3-formalized/pm-complementary-prime-sector-cancellation.md`.

Search127 (index1188058, coverage1188071/current1188072, complete inventory, mixed compiler metadata, unmeasured semantic coverage) returned complete-period diagonalization, reciprocal means and joint residues. All20 candidates, all20 source arguments and generated ingredients inspected. Its period-diagonal chain leaves the original reciprocal-weight correction unbounded. Next attack must control that signed moving-boundary correction, or an equivalent full-source cancellation, rather than merely recenter or improve logarithmic powers.

### Residual quadratic attack after closing complementary cancellation

The next target remains the actual complete denominator band, not a selected prime sector. For X<q<=2X, write S_X(N)=sum a(q)P_q(N), m_a=-sum a(q)Lambda(q), m_p=-sum a(q)phi(q)/2 and D_X=(1/12)sum J_2(q)|a(q)|^2. The existing hard conjecture is

    sum_N |S_X(N)-m_a|^2/[N(N+1)]
      <= C_epsilon log(2X) D_X/X.

It is unproved. A signed reciprocal-clock formulation may expose its required cancellation. For a common period L, put W_L(r)=sum_(k>=0)1/[(r+kL)(r+kL+1)], 1<=r<=L, and f=S_X-m_p. Exact period identities give, on paper,

    Var_anchored(S_X)
      = D_X + sum_(r=1..L) f(r)^2 (W_L(r)-1/L) - (m_a-m_p)^2.

The correction and final mean square must be kept together. Merely exporting this identity would not move the upper-bound frontier. A proof must show that their signed sum cancels the order-D_X contribution down to the required scale. Uniform period averaging, a support-independent comparison, and fixed-cofactor limits do not do this; the latter's constants grow with the cofactor. No assertion of the conjectured estimate follows from the formula.

Search128 completed (index1188117; coverage1188128/current1188129; complete inventory, mixed compiler metadata, semantic coverage unmeasured). All20 candidate statements, all20 returned source arguments and both generated ingredient steps inspected. It rediscovered the exact cutoff source difference and boundary, fixed-cofactor covariance bounds, and completed-aperture obstructions. The proposed dilation chain supplies no growing-cofactor constant and no complete-band bound. Direct inspection of PMRamanujanCutoffPrimeBalance confirms the physical input is not prime invariant, so its negative invariant-input cross form cannot be substituted here.

Evaluation: the complementary cancellation theorem is genuine new signed-source knowledge. Subsequent retrieval did not improve the residual bound. The next proof attempt must work on the full signed quadratic above, rather than repeat coefficient estimates, scalar centering, or generic prime contraction. No new receiver with an energy premise has been added. All own Lean/search processes are terminal; owned completed scratch files and search outputs cleaned. Goal remains active and unmet.

## 2026-10-02 — complete-band Mellin source and spectral escape attack

The exact finite-source transform is now audited in `PMRamanujanBandMellin`: the reciprocal primitive is a finite signed Nyman combination, its Mellin transform is zeta(s)*J_s(q)/s, and the complete natural band retains every actual coefficient. Seven exports passed targeted old-mode build, final actual-file Lean and standard-axiom checks. Umbrella wired; no own lint finding. Closed card: `../3-formalized/pm-ramanujan-band-mellin.md`.

New paper mechanism: normalize the complete band by X^epsilon and move it by the unitary spatial dilation. Its proposed two-variable transform has actual quotient zeta(1+z-s)/zeta(z), a normally summable Euler correction and the literal dyadic-band factor. A critical-zero residue, paired over a compact frequency interval, may force energy to escape every fixed profile. This is not yet a proved obstruction and would not disprove the weaker damping-margin bound sufficient for RH. Exact formula, continuation argument, integer-cutoff obligation and remaining gaps are recorded in `pm-ramanujan-band-spectral-escape.md`.

Assessment: the finite-source identity closes a necessary input, but no global small-damping energy ceiling has been improved. Current attack keeps the full signed band and its moving spectral component. The next proof obligation is the actual Euler correction and its analytic nonvanishing, followed by the double-transform identity and bounded Hilbert test. Searches129/130 complete; 131 partial with interrupted text retrieval; all returned statements and ingredients inspected, mixed compiler freshness acknowledged. Goal remains active and unmet.

### Actual analytic correction closed

`PMRamanujanBandEulerCorrection` discharges the local analytic obligation: literal prime identity, absolutely and locally uniformly convergent correction, joint continuity, holomorphy in the scale variable, critical-diagonal nonvanishing and a joint nonzero neighborhood. Fifteen exports passed targeted old-mode build, final actual-file Lean and standard-axiom audits. Umbrella wired once. Lint reports thirteen unrelated unreachable modules, no own finding. Closed card: `../3-formalized/pm-ramanujan-band-euler-correction.md`.

This removes one possible cancellation of the proposed critical-zero residue, but does not bound the physical energy or prove spectral escape. Next actual-source obligation: identify the infinite arithmetic series with its Euler product in Re(z)>1, using exact divisor-symbol convolution and absolute summability, then preserve the literal cutoff in the second Mellin transform. Search132 partial semantic retrieval; complete inventory, mixed compiler freshness; all20 candidates/source arguments inspected. The current series scratch is still being checked and is not a theorem claim.

### Complete arithmetic Euler identity closed

`PMRamanujanBandEulerSeries` now proves the actual infinite cleared identity, including coprime factorization and an unconditional absolute-convergence majorant. Its thirteen exports passed targeted old-mode build, final actual-file Lean and standard-axiom audits. Umbrella wired once; lint eleven unrelated unreachable modules, no own finding. Closed card: `../3-formalized/pm-ramanujan-band-euler-series.md`.

Assessment: a previously missing exact source identity is now proved; the global small-damping upper bound has not improved. Next hard obligation is the literal cutoff Mellin integral, followed by a compact-frequency Hilbert test and critical-zero residue. Search133 was partial semantic retrieval, index1189028, coverage1189051/current1189053, complete inventory and mixed compiler freshness. All20 candidate statements and all20 source arguments inspected; unrelated Gamma bounds were rejected. Active cutoff scratch retains the exact interval [q/2,q), the q>=2 restriction and q=1 subtraction. No escape or RH conclusion claimed.

### Literal cutoff integral — current proof attempt

Search134 returned the generic integral/series interchange and compact-support dilation arguments, but no actual moving-band cutoff theorem. All twenty candidate statements, twenty source arguments and generated ingredient obligations were inspected. Retrieval was partial (text/source stages), inventory complete, compiler freshness mixed; no retrieved statement is treated as verified without Lean.

The current proof keeps the exact half-open window [q/2,q). Its norm integral equals q^Re(r) times the fixed positive-window integral, so absolute convergence follows from the audited complete arithmetic majorant. The whole cutoff integrand is also being proved integrable via the ENNReal norm-sum bound; a totalized integral equality alone is insufficient. The arithmetic q=1 term must be subtracted exactly. Scratch proof is under foreground Lean checking; no closure or new energy estimate is claimed yet.


### Literal cutoff identity closed

`PMRamanujanBandCutoffMellin` now proves the complete scale integral, actual integrability, exact window norm identity and q=1 subtraction. All sixteen exports passed targeted old-mode build (only the new leaf, 192 seconds), final actual-file Lean and standard-axiom audits. Umbrella wired once. Lint has twelve unrelated unreachable modules and no finding for this leaf. Closed card: `../3-formalized/pm-ramanujan-band-cutoff-mellin.md`.

Contribution: the actual cutoff/Fubini input is closed with no unknown energy premise. No global small-damping energy bound was improved. The next attack is the actual logarithmic Hilbert realization and compact tested continuation. The cleared identity removes the need for zero multiplicities or Laurent expansions: differentiability alone controls zeta(rho+delta)/delta. The explicit conjugate-residue test is recorded in the active spectral-escape card. RH remains unproved and unfalsified; goal remains active.


The next Hilbert scratch prefix has now passed Lean with no diagnostics: actual log source, finite-band L1/L2 admission, complete critical Mellin trace, Fourier identification and Plancherel. It is not promoted yet: the original discrete-energy norm, moving dilation and bounded test remain to be connected. The scalar Abel refinement avoids an unnecessary operator-valued resolvent; the cleared identity avoids zero multiplicity. All own processes are terminal; only the active Hilbert scratch and empty log remain. Continue from that checked prefix rather than redoing the audited cutoff leaf.


## 2026-10-02 — exact Hilbert energy and bounded frequency test

Previous turn was verified progress: the actual cutoff integral was closed and fully audited, while the small-damping signed-energy ceiling stayed open. This turn revalidated the active scratch and frontier map. The logarithmic-source norm is now scratch-verified to equal the exact original discrete energy: exponential change of variables, removal of the zero head, and separate real/imaginary applications of `hasSum_stepGram` retain the complete square and every mixed contribution. One duplicate simp warning was removed.

The actual critical trace is realized as an L2 vector. The new statements identify its literal frequency integral with the Hilbert inner product and bound its square by 2*pi*||test||² times the complete discrete energy. Pairing integrability is proved explicitly; no totalized-integral shortcut or unknown energy premise is used. The complete leaf is now fully audited. Closed card: `../3-formalized/pm-ramanujan-band-hilbert.md`.

Search137 was complete in retrieval, with complete inventory and mixed compiler freshness (background refresh still running). All twenty candidate statements, twenty source-argument statements and generated ingredient obligations were inspected. The actual stepGram and L2 integral/pairing facts are relevant; the proposed log-curvature/product-derivation continuation concerns unrelated sources. Applicability of the actual energy mechanism has been checked in Lean. The growing-cutoff bound remains the hard RH-producing problem.

### Hilbert audit closed; moving-carrier attack

The Hilbert leaf passed its targeted old-mode build (249 seconds), final actual-file Lean audit and all twenty-two standard-axiom queries. Umbrella wired once; lint has eleven unrelated unreachable modules and no own finding. The P2 card is now P3. No cutoff-uniform or small-damping energy upper bound follows from this closure.

The next scratch has passed exact phase and norm identities: at real cutoff X>=1, the actual normalized critical-frequency vector, multiplied by the unitary phase exp(i*tau*log X), represents X^(epsilon+i*tau)*T_X(tau). Its squared norm is exactly 2*pi*X^(2*epsilon) times the original complete band energy. The literal scale integral and its cleared zeta identity are now being checked. No moving-carrier project leaf has been promoted yet.

The compact-test support can stay a positive distance d from the critical ordinate gamma. Its fixed-profile Abel contribution is then bounded by delta/d times the integrable frequency-pairing norm. This replaces a general dominated-convergence argument with the exact spectral-gap estimate. The source-specific analytic continuation and profile remainder remain missing, and no spectral-escape theorem or RH conclusion is claimed.

The moving carrier is now fully audited in `PMRamanujanBandMovingMellin`: nine exports, targeted old-mode build261s, final actual-file audit, standard axioms only, umbrella wired once. Lint13 unrelated unreachable modules; no own finding. Closed card: `../3-formalized/pm-ramanujan-band-moving-mellin.md`. This closes the exact moving-source/scale-transform identification; it does not improve the small-damping energy ceiling.

Active scratch files now separate two remaining analytic obligations: `/tmp/pm_band_abel.lean` is checking the exact L1 phase Laplace/resolvent identity and the L2 phase-unitary Abel zero limit for a test separated from the chosen ordinate. `/tmp/pm_band_residue.lean` is an unverified draft proving a whole punctured interval of nonzero literal residue numerator. The latter uses actual zeta-zero discreteness, Re>=1 zeta nonvanishing and the audited joint Euler correction. Complete tested continuation and the variable-profile remainder remain open.

### Actual phase-unitary Abel term closed

`PMRamanujanBandAbel` now proves the scalar Laplace/resolvent identity, frequency-gap Abel zero, actual scalar phase-pairing integrability and its L2 phase-unitary specialization. Four exports passed targeted old-mode build43s, mandatory final actual-file Lean with no diagnostics, and standard-axiom audits. Umbrella wired once. Lint13 unrelated unreachable modules; none own. Closed card: `../3-formalized/pm-ramanujan-band-abel.md`.

Contribution: the fixed-profile Abel term is fully formalized with the literal phase unitary. The global small-damping energy ceiling has still not improved. Current next check is `/tmp/pm_band_residue.lean`: a punctured interval of nonzero complete numerator and continuity away from gamma. Initial API failures were repaired explicitly, without increased heartbeats. Compact positive testing, actual tested analytic continuation, profile remainder and spectral escape are not yet proved.

The residue prefix now passes with no diagnostics. Its actual numerator includes alpha, both zeta factors, the literal dyadic factor and H. The proof finds a nonzero punctured interval beside every critical zero and proves continuity away from its ordinate, with no simplicity assumption. The positive compact-test paper proof is recorded in `../3-formalized/pm-ramanujan-band-residue-test.md`; its L2 admission, integrable pairing and strict positivity are the next Lean obligations. All processes terminal; only checked residue scratch and empty log remain. Completed artifacts cleaned. Search142 fully inspected and recorded in the spectral-escape card. The global small-damping energy problem remains open; goal active and unmet.


### Positive complete-residue test fully audited

`PMRamanujanBandResidueTest` is closed: nine exports, targeted old-mode leaf build172s, mandatory final actual-file Lean with no diagnostics, standard axioms only, umbrella wired once. Lint11 unrelated unreachable modules, none own. Card: `../3-formalized/pm-ramanujan-band-residue-test.md`. The actual compact test has a positive support gap and strictly positive pairing with the complete numerator. This advances the actual cleared-identity obstruction; it does not improve the global complete-energy ceiling or prove spectral escape/RH.

The next foreground scratch checks actual tested-scale measurability, local norm boundedness, joint guarded-trace measurability and literal L2 pairing integrability/identity. Search146 completed, inventory64622 complete, compiler freshness mixed. All twenty candidate statements, twenty source arguments and both ingredient steps were inspected. The generic joint-integrability/Fubini mechanism is useful; separate product domination is not supplied for the actual moving family. The planned proof uses the integrated L2 square bound and derives the global source bound internally from a convergence contradiction.


### Actual tested source continuation advances

The complete thirteen-export tested-scale scratch passed with no diagnostics. `PMRamanujanBandTestedScale` is promoted and wired once. Targeted old-mode leaf build17s passed; mandatory final actual-file Lean passed with no diagnostics. Separate axiom queries are running; lint has ten unrelated unreachable modules and no own finding. The proof derives global boundedness internally from the proposed normalized-profile convergence, proves the full product integrable, applies actual Fubini, and identifies the literal scale integral with a holomorphic reciprocal Mellin transform. The complete initial arithmetic identity is retained. This closes actual-source obligations but does not improve the small-damping complete signed-energy ceiling.

The next draft `/tmp/pm_band_kernel.lean` continues the literal compactly tested identity using joint Euler-correction continuity and holomorphy, compact-parameter domination, and analytic uniqueness on a connected ordinate tube. Its paper proof is `../3-formalized/pm-ramanujan-band-tested-continuation.md`. No Lean verification yet. The variable-profile Abel remainder has a direct rescaling/dominated-convergence paper mechanism, recorded in the spectral-escape card; it remains unformalized.


The tested-scale leaf is fully audited: thirteen exports, targeted old-mode build17s, final actual-file Lean exit0 empty, standard axioms only, umbrella wired once. Card moved to `../3-formalized/pm-ramanujan-band-tested-scale.md`. Completed pairing/search artifacts are cleaned. The arithmetic continuation scratch is now in its first foreground check; its success is not yet claimed. The goal remains active and unmet.


### Complete tested identity reaches the boundary approach

`PMRamanujanBandTestedContinuation` now has a complete scratch proof and is promoted/wired. Its targeted old-mode leaf build185s and mandatory final actual-file Lean both passed, the latter with no diagnostics. Eight-export axiom audit is running; lint12 unrelated unreachable modules, none own. The exact complete arithmetic kernel is jointly continuous and holomorphic, compact L2 testing preserves holomorphy, and analytic uniqueness extends the actual cleared identity from Re(z)>1 to Re(z)>1/2 in the separated ordinate tube. No simplicity or extra arithmetic bound enters.

The remaining actual Abel boundary term is drafted in `/tmp/pm_band_remainder.lean`: bounded-null rescaling, actual norm-null profile remainder, exact X=exp(u) substitution and combination with the audited fixed-profile gap limit. It is still unverified. The positive residue contradiction and unconditional positive-zero instantiation remain; global complete-energy control at small damping is still open.


The complete tested-continuation leaf is fully audited: eight exports, targeted old-mode build185s, final actual-file Lean exit0 empty, standard axioms only, umbrella wired once. P3: `../3-formalized/pm-ramanujan-band-tested-continuation.md`. The remainder scratch is now in its first foreground check; no success is claimed yet. Completed kernel and search artifacts are cleaned. Goal remains active and unmet; the global small-damping signed-energy ceiling is unchanged.


The profile-remainder leaf is fully audited: seven exports, targeted old-mode build73s, mandatory final actual-file Lean exit0 with no diagnostics, standard axioms only, umbrella wired once. P3: `../3-formalized/pm-ramanujan-band-profile-remainder.md`. Lint11 unrelated unreachable modules; none own. The scalar contradiction scratch is checking for the first time. The global small-damping complete-energy ceiling is still open.

Search151 completed, inventory64656 complete, compiler freshness mixed. All twenty candidate statements, twenty source statements and both generated ingredient steps were inspected. The completion-construction chain is unnecessary: actual L2 is already complete. Current `Metric.cauchySeq_iff` and `cauchySeq_tendsto_of_complete` give a stronger positive survivor. No fixed limit implies a positive cofinal tail diameter; the triangle inequality yields one positive separation radius independent of the proposed profile. This new paper extension is recorded on the no-fixed-profile P2 card and awaits Lean checking.


The complete spectral-escape scratch passed with no diagnostics. Four exports are promoted in `PMRamanujanBandSpectralEscape` and wired once; targeted old-mode leaf build is running. Unconditional Hardy supplies the positive critical zero. The literal cleared identity, actual Abel zero and positive complete residue rule out every fixed strong limit, and L2 completeness gives one positive cofinal separation radius independent of the profile. No RH or energy upper bound follows.

Search152 completed, inventory64659 complete, compiler freshness mixed. All twenty candidate statements, twenty source statements and both generated ingredient steps were inspected. Its generated Frobenius/correlation chain does not apply to the anchored physical energy. The exact existing Plancherel identity can transport norm statements; the actual signed cutoff recurrence, rather than a selected sector or complete-period average, remains the next upper-bound mechanism to test. Search153 targets that recurrence.


`PMRamanujanBandSpectralEscape` is fully audited: four exports, targeted old-mode build144s, final actual-file Lean exit0 empty, standard axioms only, umbrella once. P3: `../3-formalized/pm-ramanujan-band-no-fixed-profile.md`. The complete actual normalized critical-frequency family has a common positive cofinal distance from every fixed L2 vector. This is the strongest current positive survivor; it does not exclude bounded oscillation or prove the small-damping upper ceiling. Global lint13 unrelated unreachable modules, none own.

Search154 completed with inventory64667 complete, mixed compiler freshness. All20 candidate and20 source statements plus both ingredients inspected. Coefficient variance, the half-damping endpoint and absolute remainder bounds do not supply the missing cumulative small-damping energy estimate. Search155 was partial with inventory64671 complete and mixed compiler freshness; all20+20 statements and both ingredient steps inspected. Actual `dilationUnitary` and existing AE Fourier transport suffice for the exact physical vector identity. `/tmp/pm_band_physical.lean` is now in its first check, seven exports drafted; paper proof in `../2-fully-proven/pm-ramanujan-band-physical-separation.md`. Original signed-energy norm and every denominator are retained. Goal remains active and unmet.
