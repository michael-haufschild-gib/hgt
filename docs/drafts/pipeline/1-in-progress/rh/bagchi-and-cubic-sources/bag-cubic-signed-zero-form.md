# BAG cubic signed zero form

- **ID:** BAG-C28.56l
- **Stage:** 1-in-progress
- **Target:** the existing C28.44 full signed noncontracting Gaussian cubic,
  at o(N/log²N), as part of BAG; no change to the RH goal.
- **Status:** paper investigation. No new Lean theorem or full explicit-formula
  substitution for the literal cubic has been proved here.

## Source basis checked

`ChiPrimeGaussianCubicMain` defines the literal entry, both contraction families
and their single overlap. `ChiPrimeGaussianCubicRationalRows` retains the exact
removed q=r atom. `ChiPrimeGaussianProgressionProfile` and
`ChiPrimeGaussianCubicHalfResonance.primeProfile_fourier_once` supply the smooth
profile/one-integration mechanisms; they do not bound the current joint sum.

The installed corpus **does** contain the unconditional compact C² explicit
formula `Zeta23.WeilEF.EF_lit_zetaZeroConfig`, in
`formal/.lake/packages/Zeta23/Zeta23/WeilEF/Main.lean:272`. Its actual definition
is in `Zeta23/ExplicitFormula.lean:84`: the multiplicity-weighted zero sum is
absolutely summable for each compact C² test and equals the pole terms minus
the prime-power term plus the Gamma integral. No RH premise occurs in this
declaration. A fresh `/tmp` probe using `lake --old env lean` exited0; this
declaration and `primeGaussianCubicMain_eq_contractions` both report exactly
`propext`, `Classical.choice`, `Quot.sound`. Audit log:
`/tmp/bag-ef-source-audit-01a0.log`. This audits the imported source ingredients,
not the unproved cubic substitution or its asymptotic.

Do not substitute `WeilProducerPerronExplicitFormula.tsum_lamC_mul_max_eq`:
it has a `WeilPositiveFull` premise. `XiGuinandWeilExplicitFormula` concerns a
finite regularized-resolvent test algebra. The actual compact C² formula above
is the relevant source for this attempted mechanism.

## Why the last amplification did not close

The precise costs are in `bag-signed-medium-additive-factor.md`. A unit-phase
Mobius estimate does not control the full q,r weight. Its direct joint version
has an unproved weighted comparison energy, incomplete determinant correlations,
and masks/variation costs. The present attempt keeps the outer prime sums
together while changing the representation of the complete middle-prime row.

## Paper kernel and common physical window

Write V for the actual Gaussian cutoff, W for the physical window and
alpha=p/r. A candidate zero-density integral for a prime row is

    K_rho(N,alpha) = integral_N^{2N}
      V(x/N) W(alpha*x/N) x^(rho-1) exp(2*pi*i*alpha*x) / log(x) dx.

This formula is a proposed piece of a full explicit-formula expansion, not an
identity already justified for the sharp row. For rho=beta-i*gamma, gamma>0,
its oscillatory phase is 2*pi*alpha*x-gamma*log(x). Differentiation gives

    x0 = gamma/(2*pi*alpha),
    phi''(x0) = gamma/x0²,
    W(alpha*x0/N) = W(gamma/(2*pi*N)).

Thus the stationary value of the physical window depends on the zero height,
not on the two remaining primes. The ratio-dependent Gaussian factor is still
V(gamma*r/(2*pi*p*N)); it cannot be replaced by a constant. The phase at x0 is

    gamma*(1-log(gamma/(2*pi))) + gamma*log(p/r).

Consequently a stationary expansion would leave a **signed outer prime
bilinear form sampled at actual zeros**, with a common chi-type height phase.
Neither zero-count bounds nor a positive mean-square estimate discard that
phase legitimately. This is the hard object to evaluate, not a new assumed
correlation input.

## Required main term: it is not zero

Let E(N,p,x,r) denote the literal cubic entry extended in its middle argument
to real x. For p!=r define the continuous prime-density row

    J(N,p,r) = integral_N^{2N} E(N,p,x,r)/log(x) dx,

and the exact signed density discrepancy

    D(N) = sum_{p,r prime in (N,2N], p!=r}
      [sum_{q prime in (N,2N]} E(N,p,q,r) - J(N,p,r)].

The original off-diagonal is then, by its definition,

    Off(N) = D(N) + sum_{p!=r} J(N,p,r) - C(N),
    C(N) = sum_{p,r prime in (N,2N], p!=r} E(N,p,r,r).

The already formalized contraction algebra identifies C(N) exactly as

    2*pi * [BandEnergy(N) * sum_{p prime} primeGaussianProfile(p/N)
             - sum_{r prime} |V(r/N)|²/r * primeGaussianProfile(r/N)].

The second term is the all-equal overlap; it must remain. One signed
integration in the continuous row, including both endpoints and the derivative
of 1/log(x), suggests a uniform O(1/(N log N)) row bound, hence
O(N/log³N) after the source prime-count upper bound. This aggregate estimate
has not been Lean-proved in this card. Even after proving it, the actual hard
target is **D(N)=C(N)+o(N/log²N)**. A conjecture D(N)=o(N/log²N) would remove
the contraction that the transformed arithmetic must reproduce.

## Obligations before any claimed explicit-formula closure

1. Construct a compact C² test or a justified limiting procedure reproducing
   the literal sharp prime row. The band endpoints need not have zero Gaussian
   amplitude. A smooth surrogate alone is not the original source.
2. Retain the finite proper-prime-power corrections, or remove them by a proved
   exact inversion. The compact formula's arithmetic term is Lambda, not the
   prime indicator. A triangle bound on the correction may lose the conductor
   power and cannot silently be called negligible.
3. Retain pole/Gamma terms, zero multiplicities, both signs of the ordinates,
   and the complete zero tail. Pointwise summability of a test does not supply
   an N-uniform bound after summing p,r.
4. Prove the signed zero-side bilinear asymptotic with the nonzero contraction
   main above. Prove uniform saddle/end-point remainders at the aggregate scale.
   The stationary geometry alone proves no asymptotic.
5. Restore all original factors and show the remainder is o(N/log²N), then
   perform the direct leaf and axiom audits. Do not add a receiver with the
   signed zero-form estimate as a premise.

The earlier reciprocal-window source gives conjugation, not an automatic
opposite-real-sign involution. Any proposed reciprocity cancellation here must
be derived with its signs and boundary terms; do not reuse the rejected shortcut.

## Current evaluation

The source formula and its applicability conditions have been identified;
paper stationary geometry exposes a common zero-height window and the required
nonzero contraction main. No analytic estimate for that signed zero form has
been obtained. No proof or falsification of C28.44, positive self-return or RH
is claimed. Continue this hard signed estimate rather than formalizing only
the kernel identity or the easier continuous-density bound.

## C28.56n — reflection check

For the actual compact-test formula, put k_rev(u)=k(-u). Direct substitution
gives H_rev(s)=H(1-s). The two pole terms exchange; the arithmetic term contains
k(log n)+k(-log n) and is unchanged; the Gamma bracket is even. Thus reflection
preserves the zero functional. It does not negate it. An odd test kills the
arithmetic term as well as the zero functional and cannot represent the literal
prime row. This is a paper sign check, not a new Lean no-go or retirement of BAG.

## C28.56o — exact prime-only compact-test construction, paper

The sharp-band and proper-power obligations can be handled together without an
unsmoothing limit. This construction is not yet Lean formalized. Work at the
original integer conductors N>=2, including the already used cofinal family.
Choose a smooth eta_N with support in (N+1/4,2N+3/4), equal to one on
[N+1,2N], between zero and one, and transition derivatives bounded independently
of N. Its values on natural numbers are exactly the band indicator. Set

    F(x)=eta_N(x)*E(N,p,x,r),
    K(s)=integral F(x)*x^(s-1)/log(x) dx,
    k_j(u)=exp(u/2)*F(exp(j*u))/u,   j>=1,

with k_j=0 near u=0. Each k_j is a legitimate compact smooth test, supported
strictly on the positive u-axis. The substitution x=exp(j*u) gives H_j(s)=K(s/j).
Choose J by 2^J<=2N<2^(J+1). Its arithmetic term is

    S_j=sum_n Lambda(n)/log(n)*F(n^j).

All contributing n are at least two. Group n=l^a with l prime. Then

    sum_{j=1}^J mu(j)/j*S_j
      =sum_{l prime} sum_{b>=1} F(l^b)/b * sum_{j|b}mu(j)
      =sum_{l prime in (N,2N]} E(N,p,l,r).

Every sum involved in this grouping is finite; no summability estimate for a
Möbius series is used. The coefficient is mu(j)/j, not mu(j). In particular,
proper powers are cancelled by the complete exponent aggregate rather than
estimated separately. Mathlib's actual vonMangoldt prime-power formulas and
divisor Möbius identity were inspected. The corpus's
PositivePrimeDensityMobiusInversion concerns a different continuous, monotone
density and is not an instantiated proof of this signed finite identity.

Retaining the source formula's Gamma integral A_j, the exact proposed row is

    sum_{j=1}^J mu(j)/j * [K(0)+K(1/j)+A_j
                           -sum_rho mult(rho)*K(rho/j)].

The minus sign on the zero term is essential. With positive test support, the
digamma integral representation gives on paper

    K(0)+A_j = -integral F(x)/[x*log(x)*(x^(2/j)-1)] dx.

This removes the Gamma integral only after proving this identity, not by
discarding it. One signed integration against exp(2*pi*i*p*x/r), with eta_N
and every original Gaussian/window factor, gives pole and trivial-zero
aggregate errors at most O(N/log^3 N) after the source prime-count bound.
This estimate is a paper deduction, not an audited theorem. The finite harmonic
cost from j>=2 is dominated by the N^(1/2) pole scale; the j=1 pole gives the
displayed N/log^3 N scale. The transitions have fixed total variation, so their
derivatives cannot be replaced by O(1/N), but are still retained in this cost.

Consequently the candidate full signed zero object is

    Z_N = sum_{p,r primes in band, p!=r} sum_{j=1}^J mu(j)/j
            * sum_rho mult(rho)*K_{N,p,r}(rho/j),

and the required main term has sign **Z_N=-C(N)+o(N/log^2 N)**. All exponents,
all actual zeros and multiplicities remain. This exact-source construction
does not prove that asymptotic. Fixed-width endpoint transitions also mean that
pointwise compact-test summability is not a uniform zero-tail estimate.

## C28.56p — two-zero stationary geometry and the remaining signed twist

Applying the same construction to q and r, before subtracting both contraction
families and their overlap, exposes more structure. This is a paper mechanism;
the full double explicit-formula identity and its estimates are unproved.
For rho1=beta1-i*gamma1 at exponent j and rho2=beta2+i*gamma2 at exponent k,
make the exact change q=u*v, r=v. The oscillatory phase is

    2*pi*p*u - (gamma1/j)*log(u)
                + (gamma2/k-gamma1/j)*log(v).

An interior joint stationary point therefore requires

    gamma1/j=gamma2/k,  u=gamma1/(2*pi*j*p).

After v=N*w the scale integral retains
N^(rho1/j+rho2/k-1), the original two Gaussian cutoffs, both interpolated band
cutoffs, and both log denominators. It is a Mellin transform on the literal
intersection of the q/r band constraints. It resolves a whole near-diagonal
packet in gamma2/k-gamma1/j, not only identical zeros. At the ratio saddle the
remaining phase is

    (gamma1/j)*(1-log((gamma1/j)/(2*pi)))
      +(gamma1/j)*log(p),

and W again becomes W(gamma1/(2*pi*j*N)). The remaining prime twist and this
common height phase must stay inside the signed sum. Mixed pole/zero and
Gamma/zero terms from the two formulas are also not yet estimated or discarded.

Direct source reads found an unconditional, all-zero pair-form theorem in
MontgomeryPairCorrelationLeadingOrder and its uniform version. Their stated
scale is x=T^alpha with fixed 0<alpha<1, uniformly only on compact subintervals
of that interval. The actual Montgomery kernel is
x^(rho+conj(rho')-1)*4/(4-(rho+conj(rho')-1)^2). It is not the current moving
Mellin kernel with a signed remaining prime twist. The proposed two-zero
kernel's j=k=1 term has x comparable to N at height comparable to N. The inspected
source proof includes an x/T mean-square cost and an O(x*log^3 T) truncation
cost; inserting x comparable to T does not make these errors negligible.
No equivalence with Montgomery's pair form or extension of its theorem is
claimed. Improving an untwisted mean-square estimate alone would still leave
the current signed prime twist unestimated.

Both actual pair-correlation declarations were checked in a fresh `/tmp` probe
with `lake --old env lean`: exit0, only propext/Classical.choice/Quot.sound.
The output verifies the strict alpha<1 / b<1 restrictions. Log:
`/tmp/bag-zero-pair-source-audit-01a0.log`. The probe was deleted after completion.

Next mathematical target: evaluate this complete near-diagonal zero-pair
packet WITH its prime twist, original scale kernel, mixed terms and contraction
subtractions. Neither an identical-zero estimate nor the already proved
subcritical pair-correlation law is a solution. Turn evaluation remains:
new paper source representation and phase geometry, no closed hard analytic
gap and no new unconditional Lean cancellation theorem.

## C28.56q — stationary trace producing the contraction, open

For the j=k=1 zero-pair term put a=gamma/(2*pi). After the ratio saddle the
remaining prime phase is gamma*(1-log a)+gamma*log p. If the prime sum admits a
justified decomposition into additive rational modes b=A/Q, its b-mode has
phase gamma*log p-2*pi*b*p and an interior saddle at p=a/b. At that saddle the
complete phase is exactly -gamma*log b. The ratio saddle was u=a/p, so it is
now u=b. The positive curvature in u and negative curvature in p have opposite
Fresnel factors.

Thus b=1 has zero remaining phase and u=1: it lands on the original q=r
contraction. This is a concrete candidate for its spectral main, with the
original Gaussian and physical-window weights still to be carried through.
Every b!=1 retains exp(-i*gamma*log b); no sign-free bound replaces that twist.
This is only phase algebra. No prime Poisson formula, minor-arc error estimate,
prime square-root-window asymptotic, zero-pair asymptotic or uniform double
stationary expansion is being assumed.

A continuous-density replacement of the prime sum is not justified here:
the phase changes by order one between consecutive integers. Other rational
modes remain, including denominators growing with N. Even an improved
untwisted critical mean square would not sum these signed modes. The old
fixed-rational cancellation theorem already treats each fixed A/Q, so proving
that again in the zero representation would not advance the frontier.

The next conjecture is the complete stationary trace law: the b=1 contribution
reconstructs the exact removed contraction and the aggregate of all other
modes, all exponent pairs, endpoint terms and mixed explicit-formula terms is
o(N/log^2 N). Attack the growing-mode aggregate directly. This is a proposed
proof mechanism for the same full cubic, not a new premise or a proved law.

## C28.56r — simultaneous phase and transfer check

Revalidation of the actual sources did not supply a new cancellation estimate.
For the dominant exponent pair j=k=1, retain the remaining rational mode b and
write the two-variable phase before either stationary approximation:

    Phi_b(p,u)=2*pi*p*(u-b)-gamma*log(u).

Its stationary point is u=b, p=gamma/(2*pi*b), and its value is -gamma*log b.
The Hessian in (p,u) is [[0,2*pi],[2*pi,gamma/u^2]], with determinant
-4*pi^2. Thus this is one nondegenerate saddle with zero signature. After
p=N*z, its normalized phase has large parameter N and two-variable factor
N^(-1), while dp contributes N. Equivalently the u saddle costs N^(-1/2)
and the p saddle has width N^(1/2). The complete unscaled (p,u) integral
therefore has order-one saddle size, before its literal arithmetic weights.
It does not acquire an additional negative power of N by treating the second
stationary step as an independent cancellation estimate.

The equivalent Fourier-in-p viewpoint also has a qualification. The sharp
band profile V(x)*W(u*x) generally has a nonzero endpoint: at u=3/2 its lower
endpoint is V(1), as the existing HalfResonance source already proves. The
integer-matching eta_N transitions have width O(1) in p, hence O(1/N) in x.
Their scaled derivatives are not uniformly bounded. One cannot assign the
completed mode a uniform N*(1+N*|u-b|)^(-k) tail for arbitrary k. The boundary
term of one integration has size O(1/|u-b|); the full derivative integral and
transition terms must accompany it. The b=1 stationary ratio is special
because W kills both band endpoints there; it does not repair all other modes.

Two checked existing source identities identify the remaining transfer cost:

* MontgomeryPrimeSideBounds.tsum_montgomeryZeroTerm_eq_primeSide_add_remainder
  returns the actual prime Dirichlet series plus its explicit remainder.
  Squaring it under a remaining complex weight gives a WEIGHTED prime mean
  square. The existing unweighted pair-form leading term does not evaluate it.
* ChiInverseStationaryKernel.chiInverseStationaryKernel_physical_pairing and
  exists_chiStationaryFrequencyKernel_bilinear_remainder keep the full
  finite-height frequency convolution. For f=P^2 and g=P that convolution
  is the same adjacent cubic's signed main. Their O(1/T)*norm(f)*norm(g)
  error is useful, but neither identity estimates the signed convolution.

These are applicability checks from the actual source, not a theorem that
every possible zero-side argument must fail. No unsupported equality between
the moving BAG kernel and the Montgomery kernel is asserted. The stationary
trace conjecture stays open; its near-zero packet and noninteger-mode boundary
terms must be controlled jointly. A new unweighted pair statistic, isolated
stationary identity or scalar prime estimate would leave precisely this cost.

Evaluation: this check changes the attempted proof by requiring simultaneous
phase analysis and the full boundary contribution. It proves no hard analytic
bound and does not justify a new production Lean leaf. The next attack must
bound the actual weighted prime/zero correlation, without inserting that bound
as a hypothesis and without counting an explicit-formula round trip as a gain.

### C28.56s positive continuation: actual sharp-to-smooth transfer, FORMALIZED

The endpoint obstruction exposed a useful producer. Weighted integer Gram
correlations and finite Schur control each fixed-index actual Gaussian prime
slice. Retaining both contraction exclusions gives a complete three-edge
comparison with squared error C*(H+1)^2*N*(1+log(N+1)). An explicit smooth bump
and H=N^(1/4) then give o(N/log^2 N) transfer along integer scales.

Production leaf ChiPrimeGaussianCubicSharpEdges and all three public axiom
queries pass, standard logical axioms only; umbrella wired. Full proof and
audit record: `../../../3-formalized/bag-cubic-sharp-edge-removal.md`.
This supersedes the sharp-transfer obstruction, but not the derivative costs
of the scale-dependent smooth cutoff. The complete signed interior
stationary trace, nearby-ordinate packet, growing rational modes and mixed
terms remain unestimated. Do not replace that target by another identity.


### C28.56t/u — growing critical pair producer and connected continuation

ChiPrimeGaussianGrowingTwists now proves o(1/log N) for the complete normalized
Gaussian prime-pair average, uniformly over positive reduced distinct twists
A/B with A,B<=sqrt(N), all height centres and N=K^2. Full determinant fibres,
singular factors, sieve remainder and literal prime coefficients remain.
Direct leaf and both public axiom audits pass; standard logical axioms only.
Record: ../../../3-formalized/bag-cubic-growing-twisted-pairs.md.

This is a new growing-family critical pair estimate, not an identification of
the moving BAG zero-trace kernel or an estimate for its full signed mode sum.
That all-real continuation is now formalized in the same leaf. The exact
connected average subtracts the entire p=q Gaussian packet, including
near-identity nonzero twists. Dirichlet approximation, translated b*K blocks
and least-prime anchors give a full affine sieve of progression length K;
all Gaussian tails and the final partial block remain. The uniform vanishing
envelope holds for every real beta in[1/2,2] and every height centre, N=K^2.
Direct production63415 and all five public axiom queries51041 pass; only
standard logical axioms occur. Record:
../../../3-formalized/bag-all-real-connected-prime-pairs.md.

The next conjecture is still the ACTUAL complete signed stationary trace,
not a new isolated mode bound. Preserve the nonzero contraction main, moving
Mellin/Gaussian weights, nearby distinct zeros, all exponent pairs and mixed
terms. Uniform pair control is not a proof that its weighted mode aggregate
vanishes. No cubic/RH closure.


**C28.56v — connected mixing does not control the signed cubic, FORMALIZED.**
ChiPrimePacketConnectedCubicSeparation constructs actual prime packets with
exact unit coefficient energy, maximum coefficient<=1/K, and complete
connected Gaussian average<=C/K for every real beta in[1/2,2] and every centre.
The SAME selected packet has ORIGINAL signed noncontracting physical chi cubic
>=T*K^2/1024. All positive and negative difference fibres, Gaussian tails,
diagonal packets, contraction exclusions and physical remainders remain.

Generic quadratic-to-cubic promotion is therefore refuted; its simultaneous
positive survivor is fully formalized. Production14031 and all six public
axiom queries13295 pass, exactly propext, Classical.choice and Quot.sound.
Umbrella wired; index29684 refreshed. Lint18740 reports17 unrelated unreachable
modules and no finding for this leaf. Record:
../../../3-formalized/bag-connected-pair-cubic-separation.md.

The actual full Gaussian weighted cubic/zero trace is still open. Next work
must attack that complete signed source, retaining the nonzero contraction
main, moving weights, nearby distinct zeros, exponent pairs and mixed terms.
Growing moments, moving cofactors, positive self-return and RH remain open.
