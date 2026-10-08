# Critical logarithmic one-pole recovery

Cycle33. Status: paper argument assembled and audited below; Lean
formalization IN PROGRESS. No critical recovery capstone is yet compiled.
Universal WP02 and its RH receiver remain OPEN. Verdict: SURVIVES
PRELIMINARY ATTACK as an exact endpoint conjecture; the individual
Bochner/ODE and Dirichlet-series techniques are classical. Scientific
novelty of their application here is not established by failed searches.

## Exact statement and scope

Put w(t)=1+log(2+|t|). For every finitely supported real raw integer trace
v, the weighted-L1 closures of the following two sets are equal:

- spectral densities of finite nonnegative mixtures of actual compact
  complex C2 sources, each with at least one of Fhat(i/2),Fhat(-i/2) zero,
  and total raw trace v at EVERY integer n>=2;
- the same mixtures with BOTH zeros on EVERY row.

Different original rows may choose different poles. Recovery has no
uniform aperture or row-count requirement. The all-integer equality
includes the entire zero tail. No positivity, RH, coefficient growth,
energy bound or recovery hypothesis is added to this statement.

The exact separating-form statement used to prove it is: for every
real continuous linear functional ell on real L1 and every real sequence
b, if Q(f)=ell(w*|Fhat|^2)-A_b(f) is nonnegative on all actual polar
sources, then it is nonnegative on every actual one-pole source.
This is an intermediate implication about arbitrary separators, not a
positivity assumption in the final recovery theorem.

The full-source beta<1 conjecture from cycle33 remains OPEN. A surviving
simple-pole term is not removed here. The literal negative Fejer source
is not one-pole. No universal WP02 energy floor follows from this theorem.

## 1. Paid source estimates

Use the actual polar resonators from WeilWorkExposingRaySublogSources
and the proof of log_toeplitz_of_polar_bound in
WeilWorkExposingRayLogLocalMass at beta=1. There are constants C0,C>=0,
depending only on the separator, such that for every N>=1 and every
complex vector c supported on {1,...,N},

  2 Re sum_(2<=n<=N) b_n sum_(m<=N) c_(nm) conj(c_m)
       <= C0*(1+log N)*sum_(m<=N)|c_m|^2.                 (1)

Also, the already compiled exists_sqrt_log_mass_of_polar_bound gives

  sum_(2<=n<=N)|b_n| <= C*sqrt(N)*(1+log N).              (2)

Neither estimate assumes coefficient signs or full positivity. The
profile in (1) is polar for every complex vector, and its raw atom
formula includes the zero tail. These two source estimates are the
arithmetic input; an arbitrary abstract cosh kernel does not supply them.

## 2. Exact finite Gibbs test and its truncation error

For sigma>0 and real t, define

  H_M(sigma)=sum_(1<=m<=M) m^(-1-2sigma), H_0=0,
  B(z)=sum_(n>=2) b_n*n^(-1/2-z), Re z>0.

This Dirichlet series converges absolutely and locally normally on that
half-plane. Indeed, with a_n=|b_n|/sqrt(n), (2) gives, for every integer
k>=0,

  sum_(e^k<=n<e^(k+1), n>=2) a_n <= A*(k+2),
  A=C*exp(1/2).                                         (3)

Use N=floor(exp(K/sigma)), K>=1, 0<sigma<=1/4, and
c_m=m^(-1/2-sigma-it) for1<=m<=N, zero otherwise. This is an actual
finite vector, not an infinite eigenvector. Direct multiplication gives

  sum_(m<=N)c_(nm)conj(c_m)
    =n^(-1/2-sigma-it)*H_floor(N/n)(sigma).

Its squared norm is H_N>0. Thus (1), divided by H_N, says

  2 Re W_N(sigma+it) <= C0*(1+log N),                    (4)
  W_N(z)=sum_(2<=n<=N) b_n*n^(-1/2-z)*H_floor(N/n)/H_N.

There is a constant E>=0, depending only on C, such that uniformly in
K>=1, 0<sigma<=1/4 and all real t,

  |B(sigma+it)-W_N(sigma+it)|
       <= E*sigma^(-2)*(1+K)*exp(-K).                   (5)

Here is a complete bound, including the finite-section weights. Write
L=log N. Since exp(K/sigma)>=2, N lies between exp(K/sigma)/2 and
exp(K/sigma), so K-sigma*log2<=sigma*L<=K. Integral comparison gives

  H_N >= (1-(N+1)^(-2sigma))/(2sigma)
       >= (1-exp(-2K))/(2sigma).

For n<=N, M=floor(N/n)>=N/(2n). Since x^(-1-2sigma) decreases,

  0<=1-H_M/H_N
    <= M^(-2sigma)/(1-exp(-2K))
    <=4*N^(-2sigma)*n^(2sigma).                        (6)

The omitted tail is bounded by (3) and

  sum_(k>=J)(k+2)q^k
    =q^J*((J+2)/(1-q)+q/(1-q)^2), q=exp(-sigma).

Taking J=floor L, using 1-exp(-sigma)>=sigma/2, yields an absolute
constant E1 with tail <=E1*A*sigma^(-2)*(1+sigma*L)*exp(-sigma*L).
The included-weight error from (6) is at most

  4*N^(-2sigma)*sum_(n<=N)a_n*n^sigma.

By (3), this last sum is bounded by
A*exp(sigma)*sum_(k=0..floor L)(k+2)*exp(sigma*k).
Use k+2<=floor L+2, the finite geometric sum, and exp(sigma)-1>=sigma.
It is at most an absolute constant times
A*sigma^(-2)*(1+sigma*L)*exp(sigma*L). Multiplication by N^(-2sigma)
gives the same bound as the tail. Finally exp(-sigma*L)<=2exp(-K)
and1+sigma*L<=1+K. Enlarging E proves (5). All constants are independent
of t because only the modulus of n^(-it) was used.

## 3. Both signs of a double pole are excluded

Suppose that near0 in Re z>0 this ACTUAL B has an expansion

  B(z)=D/z^2+F/z+R(z),                                (7)

where D is real and R is bounded. The existence of this expansion is
proved in section5, not assumed in the recovery theorem.

Fix K>=1, use (4)-(5), and take t=c*sigma, with c fixed real. Multiplying
by sigma^2 and sending sigma down to0 gives

  Re(D/(1+i*c)^2) <= E*(1+K)*exp(-K).

Indeed sigma^2(1+log N)<=sigma^2+K*sigma tends to0. This inequality
holds for EVERY K>=1, so sending K to infinity gives a nonpositive
left side. At c=0 it says D<=0. At c=2 it says -3D/25<=0. Hence D=0.
No coefficient sign, Tauberian theorem, positive-symbol norm identity,
RH or numerical experiment enters this exclusion. A negative simple
pole has no analogous sign flip in the open right half-plane.

## 4. A source kernel has only two possible unbounded terms

For each smooth compact complex g, let r_g(x)=Re(g*tilde(g))(x).
It is smooth, compactly supported, real and even. Define the actual
real even kernel

  k_g(x)=ell(w(t)*|Ghat(t)|^2*cos(x*t))
         -sum_(n>=2)b_n*(r_g(log n-x)+r_g(log n+x)).     (8)

Its value at0 is Q(g); the normalization agrees exactly with
logSeparatorKernel at beta=1. Arithmetic sums are locally finite.
For real coefficients u_j,

  Q(sum_j u_j*tau_(x_j)g)=sum_(i,j)u_i*u_j*k_g(x_j-x_i). (9)

Set P=D_x^2-1/4. Integration by parts gives
Fhat(Pg)(z)=-(z^2+1/4)*Ghat(z), so Pg is polar. Every finite linear
combination of its translates is also polar. Equation (9) says k_(Pg)
is positive definite for real vectors. Since it is real and even, its
complex quadratic form is the sum of the forms on the real and imaginary
parts of the vector (the imaginary cross terms cancel by symmetry).
Thus k_(Pg) is positive definite in the ordinary complex sense.

Differentiating the spectral cross term in real L1 and the locally
finite arithmetic sum gives

  P_x^2 k_g = k_(Pg).                                  (10)

All these differentiations are legitimate: a compact smooth source has
Fourier decay of every finite order by repeated integration by parts,
so w(t)*|Ghat(t)|^2*|t|^j is integrable for every fixed j. This supplies
the L1 derivative majorants. For the arithmetic part, derivatives
commute with a finite sum on every compact x interval; integration by
parts in the correlation transfers P from both factors to P_x^2.

The continuous positive-definite function k_(Pg) has a finite positive
Bochner measure nu. This is ordinary Bochner on R, already compiled as
HTGeometry.exists_charFun_eq_of_positiveDefinite. It needs no full-cone
Weil positivity. Define

  h_g(x)=integral cos(x*t)/(t^2+1/4)^2 dnu(t).

It is real, even, bounded and positive definite. Derivatives through
order4 pass under this integral because
|t|^j/(t^2+1/4)^2 is bounded for0<=j<=4. Therefore P^2 h_g=k_(Pg).
Consequently the C4 function k_g-h_g solves
(D^2-1/4)^2 u=0. Factoring the differential operator as
(D-1/2)^2(D+1/2)^2, the integrating-factor formula twice at each root
(or uniqueness for the four-dimensional constant-coefficient system)
gives u=(a+bx)e^(x/2)+(c+dx)e^(-x/2). Evenness forces c=a,d=-b.
Thus there are real c_g,d_g with

  k_g(x)=h_g(x)+c_g*cosh(x/2)+d_g*x*sinh(x/2).          (11)

This is a classical kernel decomposition derived here from POLAR
positivity. It has not been obtained by assuming full positivity.

## 5. The actual arithmetic series supplies the common double pole

Choose a nonzero nonnegative real smooth compact source g0. Its
correlation r is nonnegative and not identically zero. For general g
write J_g(s)=integral exp(s*u)*r_g(u)du. This is entire, real for real s,
and J_g0(1/2)>0.

The spectral part S_g of (8) is bounded. Its Laplace transform is
holomorphic for Re s>0, by dominated differentiation on compact
subsets. If support(r_g) is in[-R,R], then for log n>R,

  integral_(x>=0) exp(-s*x)*r_g(log n-x)dx
       =n^(-s)*J_g(s),
  integral_(x>=0) exp(-s*x)*r_g(log n+x)dx=0.

The finitely many terms log n<=R have compact x support. Their corrections
to these two identities are entire functions of s. For Re s>1/2,
absolute interchange with the n sum follows from (2), equivalently from
the absolute convergence established using (3). Thus with z=s-1/2,

  Laplace(k_g)(1/2+z)=Laplace(S_g)(1/2+z)
                    -J_g(1/2+z)*B(z)+E_g(z),          (12)

where E_g is entire. On the other hand, (11) and boundedness of h_g give

  Laplace(k_g)(1/2+z)
     =c_g/2*(1/z+1/(1+z))
       +d_g/2*(1/z^2-1/(1+z)^2)
       +Laplace(h_g)(1/2+z).                           (13)

All Laplace transforms of bounded parts are holomorphic in a full
neighborhood of z=0. For g=g0 the multiplier J_g0 is nonzero in a
neighborhood of1/2. Equations (12)-(13) therefore give precisely (7),
with D=-d_g0/(2*J_g0(1/2)) real and bounded analytic remainder. Section3
forces D=0. For ANY other smooth g, multiply (12)-(13) by z^2 and take
real z down to0. The left arithmetic term tends to J_g(1/2)*D=0;
the only surviving right term is d_g/2. Hence d_g=0 for every smooth g,
including those with J_g(1/2)=0. No division by those profiles is used.

## 6. Critical cosh majorant and C2 passage

With d_g=0, positive definiteness of h_g gives h_g(0)>=0 and
h_g(x)<=h_g(0). Since cosh(x/2)>=1, (11) implies

  k_g(x)<=k_g(0)*cosh(x/2)                              (14)

for every smooth compact g, even when c_g or k_g(0) is negative.

To extend (14) to every compact C2 source f, convolve f with real
nonnegative normalized smooth mollifiers of support shrinking to0.
Call the results f_j. They are smooth, share a compact support, converge
uniformly to f, and their Fourier transforms are Fhat*Mhat_j, where
|Mhat_j|<=1 and Mhat_j(t)->1 for every real t. Dominated convergence by
w*|Fhat|^2 gives weighted L1 convergence of their spectral densities and
of their cosine cross-densities at every fixed x. Uniform convergence
and the common support give uniform convergence of their correlations.
At fixed x only finitely many integer atoms can occur, with a common
finite cutoff. Hence k_fj(x)->k_f(x), including x=0. Passing to the
limit in (14) proves it for every compact C2 f. No pole preservation is
needed in this mollification step.

## 7. One-pole extension and exact whole-fibre recovery

For r=exp(x/2) or exp(-x/2), the exact existing translated-difference
identity is

  Q(tau_x g-r*g)=(1+r^2)*k_g(0)-2r*k_g(x).

Since 1+r^2=2r*cosh(x/2) and r>0, (14) makes this nonnegative for every
compact C2 g. Now let f be C2 compact and Fhat(s*i)=0, s=+/-1/2.
The already compiled exists_compact_onePole_primitive supplies a compact
C3 g with g'=s*g+f. Its small differences
(tau_h g-exp(-s*h)*g)/h converge to -f. The exact cycle32 transfer
proof supplies both limits needed for Q:

- weighted L1 convergence of the squared transforms, with integrable
  majorant 9*w*|Fhat|^2;
- convergence of the finite arithmetic pairing, using the common
  support cutoff and uniform atom continuity.

The domination and convergence lemmas in WeilWorkExposingRayOnePoleTransfer
allow beta<=1; only its final invocation of the cosh majorant used beta<1.
Replacing that invocation by (14) proves Q(f)>=0 at beta=1.

Finally apply the existing strict-separation/exact-coordinate argument
from cycle32, section5 of ONE-POLE-SUBLOG-PROOF.md and the proof of
WeilWorkExposingRayOnePoleFibreDensity. Its nonemptiness, whole-integer
coordinate repair, separation and finite-mixture algebra depend only on
separator extension and continuity of the weighted density/atom maps.
Those continuity statements already hold at beta=1 (weight>=1 and
integrable on every C2 source). The extension just proved supplies its
one previously strict endpoint step. Separation of any one-pole density
from the polar closure is therefore impossible, in each EXACT whole
integer fibre. The reverse inclusion is literal. This proves the exact
statement above on paper.

## Hostile and novelty audit

- Abstract x*sinh(x/2) satisfies the homogeneous differential equation
  and the polar finite-difference constraints. It defeats a growth-only
  endpoint proof. It is not a counterexample to the actual theorem:
  equations(1)-(6) are additional consequences of integer resonators.
- Thorn2018, arXiv:1801.09478, theorem2.2 requires nonnegative coefficients;
  its signed-symbol remark2.3 prevents replacing our signed matrix form
  by an absolute coefficient sum. We use neither norm identity.
- Nikolski–Pushnitski2020, arXiv:2001.01474, and Guo–Li–Zhou2023,
  arXiv:2305.07860, provide adjacent multiplicative Toeplitz theory with
  bounded-symbol hypotheses. They do not supply our growing-cost step.
- Chung–Kim2005, Publ.RIMS41, definition3.1, requires homogeneous
  differential constraints. Here P=D^2-1/4 is not homogeneous. Ordinary
  Bochner plus a directly solved ODE is used instead.
- Jablonski–Jung–Stochel, arXiv:2008.09494v3, uses the semigroup Hankel
  form gamma_(i+j), not our difference kernel. It is not an imported
  endpoint theorem.
- Exact mechanism corpus search4 was partial (reranking deadline),
  68881 indexed files, background refresh incomplete and compiler
  coverage mostly pending. All20 candidates,20 arguments and ingredient
  steps were inspected. No absence or novelty conclusion follows.

Formalization remains required for every new step, especially the
kernel-to-Laplace identity and signed finite-section error. No external
or internal theorem has been used with an unpaid full-positivity premise.

## Preferred formal proof of section3: signed Abel integration

Sections2-3 above are a direct finite-section proof. A shorter argument
uses the corpus's already compiled signedCumulative_laplace_ceiling.
For each real t put lambda_t(n)=b_n*sqrt(n)*cos(t*log n). For N>=1 take
c_m=exp(-i*t*log m)/sqrt(m), 1<=m<=N, and zero otherwise, in(1).
Only positive m,n enter the multiplication identity. This gives

  U_t(log N)=sum_(2<=n,1<=m,nm<=N)lambda_t(n)/(n*m)
           <=(C0/2)*(1+log N)^2.

For any Y>=0, the same sum with nm<=exp Y equals the sum at
N=floor(exp Y); since0<=log N<=Y, U_t(Y)<=(C0/2)*(1+Y)^2.
At Y<0 it vanishes. The constants do not depend on t.

For every sigma>0, the product-pair weights have absolutely summable
Laplace transforms: section2's local bound(3) makes
sum_n |b_n|*n^(-1/2-sigma) finite, and the second factor
sum_(m>=1)m^(-1-sigma) converges by integral comparison. Thus signed
Fubini is legitimate. Since sigma*integral_(Y>=log(nm))e^(-sigma Y)dY
=(nm)^(-sigma), it gives the exact identity

  Re B(sigma+i*t)*Z(sigma)
    =sigma*integral_(Y>=0)e^(-sigma Y)*U_t(Y)dY,
  Z(sigma)=sum_(m>=1)m^(-1-sigma).

Consequently, for0<sigma<=1,

  Re B(sigma+i*t)*Z(sigma)
     <=(C0/2)*(1+2/sigma+2/sigma^2)
     <=5*C0/(2*sigma^2).

The decreasing function x^(-1-sigma) has integral1/sigma on[1,infinity),
so Z(sigma)>=1/sigma>0. Division yields the UNIFORM one-sided bound

  Re B(sigma+i*t)<=5*C0/(2*sigma), all real t.           (15)

Insert the source-derived Laurent expansion(7) and take t=0 and t=2sigma.
Multiplying(15) by sigma^2 gives D<=0 and -3D/25<=0 in the limit, hence
D=0. This proves exactly the same exclusion, with no finite-section
error estimate. The existence of(7) is still paid by sections4-5.

A precise parent-API trap: critical_twisted_density_bound in
WeilWorkPBAPCriticalCoefficients requires multiplicativity and unit norm
at ALL natural numbers, including0. These hypotheses force chi(n)=1
for every n because chi(0)=chi(0)*chi(n) and chi(0) is nonzero. Its
nontrivial-twist reading is therefore unavailable. The owned proof uses
positive-integer multiplicativity only; no application at0 occurs.
This repairs the required application without editing the read-only
parent. The signed Abel integration theorem itself has no such defect.

Further primary-source comparison: Suzuki2023, JLMS108, section3.3,
uses a compact primitive at the REAL Fourier origin for the specific
Weil distribution. It supplies classical ancestry, not our arbitrary
weighted separator theorem. Zhu2026, arXiv:2608.24827v2, theorem1.1,
uses a fixed-window pointwise-symbol certificate and an explicit tail
block; it does not give the all-aperture exact-fibre endpoint here.
No computational certificate from that paper is used.


## Formalization checkpoint: arithmetic producer

Four new owned leaves are saved and wired:
CriticalTwists (positive-integer characters and uniform finite harmonic
ceiling), CriticalSeries (absolute convergence from actual local mass),
CriticalAbel (signed pair Fubini and the product ceiling), and
CriticalBoundary (uniform first-order cosine-series upper bound and
quadratically scaled upper-tail vanishing). All four saved-leaf audits pass without diagnostics. All11 public
theorem axiom checks pass with only propext, Classical.choice and
Quot.sound. Global lint reports seven unrelated unreachable modules,
with no owned WP02 finding.

The fourth leaf uses the already proved mathlib zeta residue instead of
reproving the stronger all-sigma integral comparison in section3. The
residue supplies sigma*Z(sigma)>1/2 eventually. Together with the product
ceiling this gives a single M>=0 with sigma*Re B(sigma+i*t)<=M for ALL
real t on one radial neighborhood. Consequently, for every epsilon>0,
sigma^2*Re B(sigma+i*t)<=epsilon eventually, uniformly in t. This is
exactly sufficient for the two approach paths excluding a double pole.
It does not prove the required Laurent expansion by itself.

Next required source work, in dependency order:
1. Actual real finite-packet identity for logSeparatorKernel, polar
   stability of those packets, real-to-complex positive definiteness,
   and continuity. Ordinary Bochner may then be applied to Pg.
2. C4 source specialization of P=D^2-1/4, exact multiplier, weighted
   moments, and P_x^2 k_g=k_Pg. Reuse the existing jet uniqueness theorem
   to solve the fourth-order inhomogeneous ODE.
3. Exact source Laplace-window identity, nonzero fixed profile and the
   actual meromorphic double/simple coefficients. Apply the uniform
   arithmetic upper tail above at t=0 and t=2*sigma to remove the double
   coefficient for every source.
4. Common-support mollification to compact C2 sources; then invoke the
   already paid beta<=1 one-pole primitive and limit lemmas, replacing
   only the strict-beta cosh-majorant call. Finish exact whole-fibre
   recovery and audit its unconditional capstone.

The stronger unique full-positive pole completion remains a separately
logged conjecture; no Lean capstone establishes it at this checkpoint.
Universal WP02, critical gamma-energy control and RH remain OPEN.


## C4 source refinement used in the kernel formalization

The smooth-source argument of sections4–5 only needs compact C4 profiles
until the final mollification. Let g be compact C4 and Pg=g''-g/4. Then
Pg is compact C2. The already established C2 integration-by-parts
formula gives Fhat(Pg)(z)=-(z²+1/4)Fhat(g)(z) at EVERY complex z, so both
half-poles vanish exactly. For real t its density is
rho_Pg(t)=(t²+1/4)²rho_g(t).

For each integer0<=j<=4, |t|^j<=1+|t|^4<=1+(t²+1/4)². The first bound
splits |t|<=1 from |t|>=1; the second follows by expanding the square.
Multiplication by the nonnegative logarithmic weight times rho_g shows
absolute integrability of w(t)rho_g(t)t^j, bounded by the sum of the
already integrable weighted densities of g and Pg. No new arbitrary-
order Fourier decay theorem is needed.

For the L1 derivative step, the pointwise cosine/sine difference
quotients are bounded in absolute value by |t|, since sine and cosine
are1-Lipschitz. After multiplication by w*rho_g*t^j, their errors are
dominated by2*w*rho_g*|t|^(j+1), j<4. Pointwise differentiation and
ordinary dominated convergence therefore prove all four derivatives in
REAL L1. Applying ell is legitimate by its norm continuity. Compact
C4 autocorrelations and their derivatives remain compactly supported;
each bounded x interval has a common finite arithmetic cutoff, so the
same fourth-order operator commutes with the arithmetic sum. The
source correlation identity may be established by differentiating
convolutions or by Fourier injectivity using the exact multiplier.
This supplies the same C4 ODE (10), with no new regularity premise in
the final C2 endpoint: the final common-support mollification supplies
the required C4 approximants.

Cycle34 checkpoint: complete finite real-packet identity, polar
stability, complex PD, weighted L1 continuity, and positive Bochner
measure producer are now saved in WeilWorkExposingRayPolarKernel.
Final saved-leaf audit exits0/no diagnostics. This is the first part of
section4 only; the unrestricted-profile differential/ODE/Laplace link
and critical endpoint capstone are still pending.
