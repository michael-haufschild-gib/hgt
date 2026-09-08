# CCM-FU: changing-core pair costs and even-core reserves

- **Stage:** 3-formalized; four leaves passed foreground scratch and exact-file checks, new-closure axiom audit and global formal lint. Lake packaging audit remains pending.
- **Proof chain:** Actual divisor source → renewable signed reserve → exhaustive selection → uniform signed Abel bound → RH.
- **Closed:** Exact changing-core mean update; uniform next-dilation remainder; comparable-pair costs; separated-pair reserves after every even nonempty core; arbitrary-large-prime existence and transfer to actual finite-cutoff energies.
- **Open:** Exhaustive prime inclusion, intermediate-step budget, uniform cutoff thresholds, complete successor-envelope control and RH.

## Actual-source statements

Let G_P be the literal continuous processed divisor head,
W_P(Y)=integral_(x>1) G_P(Y*x)G_P(x)/x^3,
rho_P=squarefreeDensity*product_(r in P) r/(r+1), and
kappa_P=sum_n fixedCoreBlockMass(P,n). These are the existing independent
source definitions. The discrete release identity is already proved.

For any finite prime core P and unprocessed prime p, Lean proves

G_(P+p)(x)=G_P(x)-sqrt(p)G_P(x/p),

W_(P+p)(Y)=(1+1/p)W_P(Y)-sqrt(p)/p^2 W_P(pY)-sqrt(p)W_P(Y/p)

for every positive Y. For nonempty P there is B_P>=0 with
|W_P(Y)|<=B_P for every Y>=1. Consequently

|W_(P+p)(Y)+sqrt(p)W_P(Y/p)|<=3B_P

simultaneously for every unprocessed prime p and every Y>=1.
This controls a growing core and the entire next-dilation ray. It is
stronger than taking the distant-dilation limit separately for each
already enlarged core. The remaining core dependence is explicit.

The actual W_P is continuous at every positive ratio, and W_P(1)>0.
Hence there are eta,c>0 and T such that

W_(P+p)(Y)<=-c sqrt(p)

whenever p>=T and p<=Y<=(1+eta)p. Density factors and the exact release
identity give constants eta,c>0 and a real threshold T such that
all distinct unprocessed primes p,q with p>=T and p<=q<=(1+eta)p satisfy

kappa_(P+p+q)-kappa_(P+p)>=c/p,

and, with adjusted c,T,

kappa_(P+p+q)-kappa_P>=c/p.

The first merger's possible release is only O_P(p^(-3/2)), so it cannot
pay this comparable-pair cost. The corpus prime-interval theorem supplies
such pairs beyond every prescribed lower prime cutoff. For each selected
pair, the actual energies satisfy

Q_(P+p+q)(M)-Q_P(M)>=c*M^2/p

at every sufficiently large M, with adjusted positive c.

There is also a constructive source branch. If P is nonempty and has
even cardinality, its actual residue is negative. Lean proves existence
of L>=1, c>0 and T with

W_(P+p)(Y)>=c sqrt(p) whenever p>=T and Y>=L*p.

In the bounded window L*p<=q<=(L+1)*p, this gives

kappa_P-kappa_(P+p+q)>=c/p

for sufficiently large distinct unprocessed primes. Such pairs exist
beyond every prescribed lower cutoff and leave the core even. For each
selected pair, Lean also proves

Q_P(M)-Q_(P+p+q)(M)>=c*M^2/p

at every sufficiently large physical cutoff. Thus the same source theorem
can be reapplied to the enlarged even core. No reserve, analytic sign or
computed value is an input.

## Dependency-closed paper proof

Index the divisors of product(P) by subsets of P. Splitting subsets of
P+p according to whether they contain p and using multiplicativity of
Mobius gives the continuous head update, including x<=1 and all clips.
For positive A,B, changing variables u=B*x gives

integral_(x>0) G_P(A*x)G_P(B*x)/x^3 = B^2 W_P(A/B).

All paired integrands are absolutely integrable: the already established
W integrability extends below one because G_P vanishes there, and the
same dilation transfers it to arbitrary A,B. Expand both updated factors
under the integral. The four terms are W_P(Y), -sqrt(p)/p^2 W_P(pY),
-sqrt(p)W_P(Y/p), and W_P(Y)/p. This proves the exact renewal formula.

The proved contour formula on Y>=1 is the residue plus the Fourier
integral of the entire boundary remainder. Its exponential has norm one,
so B_P can be chosen as the residue norm plus (2*pi)^(-1) times that
boundary's L1 norm. Since 1/p<=1 and sqrt(p)/p^2<=1, the remaining two
terms in the renewal formula have total magnitude at most 3B_P.

On the central Mellin line, factor exp(a) out of the contour mean at
Y=exp(a). The remaining integral has a norm-one oscillatory factor and
an integrable majorant. Dominated convergence proves continuity in a,
and composition with log proves continuity for Y>0.

At Y=1 the integrand is G_P(x)^2/x^3>=0. If its integral were zero,
G_P would vanish almost everywhere on x>1. Its inverse-cube signed
moment would then vanish, contradicting the already proved strictly
positive actual moment. Thus W_P(1)>0. Continuity supplies a positive
margin near ratio one. The bounded renewal error is absorbed by
sqrt(p) times half that margin, giving the negative comparable band.

For distinct p,q>=2, rho_(P+p+q)>=rho_P/4. If p<=q<=U*p, then

sqrt(p)*sqrt(q)/q^2 >= 1/(U^2*p).

Indeed, sqrt(p)sqrt(q)>=p and q^2<=U^2*p^2. The exact discrete release
formula therefore transfers either sign of the mean, with its sqrt(p)
margin, to a coefficient change of order 1/p. Also rho_(P+p)<=rho_P
and |W_P(p)|<=B_P, so the absolute first change is at most
2*rho_P*B_P*sqrt(p)/p^2. Choosing p large makes this at most half the
second change. This proves the complete two-merger comparison with no
omitted first-step cost.

For even nonempty P the source residue is strictly negative. The proved
physical mean limit gives W_P(lambda)<=-2c throughout some lambda>=L,
where L can be increased to at least one. Applying the same uniform
renewal estimate gives W_(P+p)(Y)>=c sqrt(p) on Y>=L*p. Restrict to
q<=(L+1)p and apply the preceding density and first-cost comparison.
This proves the positive pair reserve. The two new primes increase the
cardinality by two, preserving evenness.

The corpus theorem prime_between gives a prime in (x,(1+epsilon)x)
for every sufficiently large x. Apply it at x=p in the comparable case
and at x=L*p with epsilon=1/L in the reserve case. Choose p beyond
both analytic thresholds and every member of P. This proves the
arbitrary-large-prime assertions without a finite search or a computed
prime. Finally, subtract the two already proved normalized energy limits.
Half the strict coefficient margin then holds at all sufficiently large
integer cutoffs; multiply by M^2 to obtain the actual energy comparison.

## Lean implementation and validation

- `MobiusDivisorDilationMeanRenewal.lean`: continuous head insertion and exact physical renewal, two public theorems.
- `MobiusDivisorDilationMeanUniformRenewal.lean`: all-dilation bound, uniform ratio remainder, continuity, positive diagonal and negative comparable band, five public theorems.
- `MobiusDivisorComparablePrimeCost.lean`: second-merger cost, complete pair cost, arbitrarily large prime pairs and actual energy transfer, four public theorems.
- `MobiusDivisorEvenCorePrimeReserve.lean`: positive separated-ratio ray, complete pair reserve, arbitrarily large parity-preserving pairs and actual energy transfer, four public theorems.

Each leaf passed a foreground `lake env lean` scratch check and its exact
source-file check with leaf olean emission. Imports are wired into RHTower;
no umbrella was built. No old prerequisite olean was rebuilt. No numerical
experiment or computational proof premise was used. The known Lake
packaging audit remains pending because it would rebuild broad stale
prerequisites. All fifteen new public theorems passed one external axiom
audit, each using only propext, Classical.choice and Quot.sound. No old
declaration was re-audited. Global formal lint and the scoped whitespace
check passed. The declaration index was refreshed.

## Exact remaining global problem

Comparable pairs and separated pairs have opposite, source-determined
behaviour. The positive survivor is the uniform ratio profile and the
closed even-core reserve theorem; this work does not retire CCM-FU or
reject general prime orders.

Repeated application preserves evenness but changes B_P, the ratio window,
the reserve coefficient and the physical cutoff threshold. It does not
force inclusion of any particular omitted small prime. The first merger
can also temporarily increase energy; a positive net pair release is not
an intermediate-step ceiling. Finally, Q comparisons do not by themselves
control Psi, the maximum of current and all immediate-successor energies.
A full solution must pay those steps, include every prime, and retain one
bound at every cutoff. None of those requirements is assumed or declared
proved here. RH remains unproved.
