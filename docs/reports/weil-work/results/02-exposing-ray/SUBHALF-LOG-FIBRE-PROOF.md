# Exact-fibre recovery below the square-root logarithmic weight

Cycles30–31. Status: dependency-closed paper proof and all saved Lean
leaf audits complete; all ten new public axiom audits pass with exactly
the standard three logical axioms. Verdict: BRIDGE, with external scientific novelty
unestablished. This proves a proposed strict subrange of the earlier
sublogarithmic conjecture, not its whole range. WP02 and both energy
diagnostics remain open.

## Statement and normalization

For every 0<=beta<1/2, put omega(t)=1+log(2+|t|)^beta. For every finitely
supported real integer trace v, the actual finite positive compact complex
C2 mixtures satisfy

    closure_L1(omega dt) Kpol(v) = closure_L1(omega dt) K(v).

The definitions of K and Kpol are exactly those in
POLAR-FIBRE-DENSITY-PROOF.md: raw integer atoms at EVERY n>=2, including
the entire zero tail, and both polar zeros on EVERY polar row. No common
profile, aperture bound, row bound or energy hypothesis is introduced.
Equivalently each actual full mixture has arbitrarily accurate weighted
recovery by actual polar mixtures in the same whole fibre. In particular
this applies to the literal negative Fejer source.

Write A_b(f)=sum_{n>=2} b(n)*atomCoeff(f,n), m(f)=integral |f|^2,
rho_f=|paperFT f|^2 and M(f)=2*pi*m(f). These atom sums are finite for
each individual compact source. The argument never assumes an absolute
coefficient envelope: it DERIVES one from the separator using primitive
sets. The useful new estimate is in section3.

## 1. Actual resonators give the growing ceiling

Let ell be any continuous real linear functional on L1(omega dt), and
suppose A_b(f)<=ell(rho_f) for all actual polar sources. The actual compact
polar resonators in WeilWorkPBAPCriticalResonator have

    M(F)=2*pi*m_N*sum_{m<=N}|c_m|^2,
    E(F)<=M(F)*(log N+C0),
    A_b(F)=2*m_N*sum_{n=2}^N b(n)*Re sum_{m=1}^N c_(nm)*conj(c_m),

where c vanishes above N and m_N>0. The last identity follows from the
exact integer samples and zero tail, as in the constant transfer proof.
The proved digamma lower estimate gives log(2+|t|)<=gamma(t)+C1.
Consequently integral rho_F*log(2+|t|)<=M(F)*(log N+C0+C1).
For M(F)>0, concavity of x^beta on positive x, integrated against
rho_F/M(F), gives

    integral omega*rho_F <= M(F)*(1+(log N+C0+C1)^beta).

Enlarge the fixed constants to positive ones if necessary. If M(F)=0,
the continuous source is zero and the same estimate holds directly.
Thus for a constant D depending only on ell and beta,

    2*sum_{n=2}^N b(n)*Re sum_{m=1}^N c_(nm)*conj(c_m)
      <= B_N*sum_{m=1}^N |c_m|^2,
    B_N = D*(1+log N)^beta >=0.                         (1)

All weighted densities used here are integrable: compact C2 Fourier
transforms have O((1+|t|)^-2) decay. This is also sufficient for every
weighted density below.

## 2. Primitive layers retain signed information

For a primitive set S contained in [2,N], take c_1=1,
c_n=u*b(n) for n in S, and zero otherwise. Since no distinct pair in S
has integer ratio, (1) becomes, with Q=sum_S b(n)^2,

    2*u*Q <= B_N*(1+u^2*Q)    for every real u.

If B_N>0, use u=1/B_N to obtain Q<=B_N^2. If B_N=0,
u=1 gives Q=0. This is the already established primitive-set mechanism,
with the actual growing bound retained; it is not a new matrix theorem.

Let Omega(n) count prime factors with multiplicity. Each set
S_k={2<=n<=N: Omega(n)=k} is primitive: Omega(ab)=Omega(a)+Omega(b),
and Omega(a)>0 for a>=2. Therefore

    sum_{n in S_k} b(n)^2 <= B_N^2.                    (2)

## 3. Derived absolute harmonic envelope

Fix z with 1<z<2. Uniformly for integers N>=2,

    sum_{n=1}^N z^Omega(n)/n <= C_z*(1+log N)^z.       (3)

Here is an elementary proof that specifies the arithmetic input. Set
sigma=1+1/(1+log N). Finite unique factorization and nonnegative geometric
series give

    sum_{n<=N} z^Omega(n)/n^sigma
      <= product_{p<=N}(1-z*p^(-sigma))^(-1).

For 0<=x<=1/2 the power series for -log(1-x) gives

    -log(1-z*x)+z*log(1-x)
      = sum_{j>=2}(z^j-z)*x^j/j <= C'_z*x^2,

with finite C'_z, since z/2<1. For example discard the negative term
and 1/j to bound the series by z^2*x^2/(1-z/2).
Since sum_p p^(-2*sigma)<=sum_{n>=2}n^(-2)<=1, the product is at most

    exp(C'_z)*[product_{p<=N}(1-p^(-sigma))^(-1)]^z
      <= exp(C'_z)*[sum_{n>=1}n^(-sigma)]^z
      <= exp(C'_z)*(1+1/(sigma-1))^z.

The middle inequality is again the finite Euler product, whose smooth
integers are a subset of all integers. The last inequality is the integral
comparison for the decreasing function x^(-sigma). Multiply by
N^(sigma-1)<=exp(1), and absorb 2^z to obtain (3). No PNT,
zero statement, asymptotic Euler product or computational estimate is used.

Put H_k=sum_{n in S_k}1/n. Cauchy--Schwarz first within each primitive
layer and then across layers gives

    H_b(N):=sum_{n=2}^N |b(n)|/sqrt(n)
      <= B_N*sum_k sqrt(H_k)
      <= B_N*sqrt(sum_{k>=1}z^(-k))*sqrt(sum_k z^k*H_k)
      <= C_z*D*(1+log N)^(beta+z/2).                 (4)

Choose 1<z<2*(1-beta). Then theta=beta+z/2<1. This proves
H_b(N)=O((1+log N)^theta)=o(log N). It supplies precisely the
absolute envelope that was missing in the first hostile audit. Its proof
uses the entire primitive-set constraint, not just individual coefficient
bounds or dyadic primitive intervals. No claim is made at beta>=1/2.

## 4. Simultaneous remote errors vanish on actual shifts

Fix any compact C2 source f with correlation supported in [-2a,2a], a>=0.
Use the actual polar source

    f_X=f-sech(X/2)/2*(f(.-X)+f(.+X)).

It has both exact half-pole zeros. Write c_X=sech(X/2),
B(y)=sum_{2<=n<=floor(y)}|b(n)|. Expanding its correlation and using
|corr_f(u)|<=m(f) bounds the arithmetic error by

    |A_b(f_X)-A_b(f)|
      <= C_f*[c_X^2+c_X*B(exp(X+2a))
                         +c_X^2*B(exp(2X+2a))].      (5)

For completeness, the five correlation translates have coefficients
1+c_X^2/2 at0, -c_X at each of +/-X, and c_X^2/4 at each of +/-2X.
Subtract the original correlation. Its fixed central contribution is
c_X^2*A_b(f)/2. Each remote translate contributes at most its coefficient
times 2*m(f)*B at the indicated cutoff. This proves (5) with a finite
constant depending on f and its finite central arithmetic pairing.

Since c_X<=2*exp(-X/2), average the two remote bounds over X in [R,2R],
R>=1. Interchange only finite sums and ordinary nonnegative integrals.
For every n,

    integral_[R,2R] exp(-X/2)*1_{n<=exp(X+2a)} dX
      <=2*exp(a)/sqrt(n),
    integral_[R,2R] exp(-X)*1_{n<=exp(2X+2a)} dX
      <=exp(a)/sqrt(n).

These follow by integrating from max(R,log(n)-2a), respectively
max(R,(log(n)-2a)/2), to infinity; if the threshold exceeds2R the
integral is zero. Only n<=exp(2R+2a), respectively exp(4R+2a), occur.
Using (4), the average in (5) is O_f(R^(theta-1))+O_f(exp(-R)),
which tends to zero. There are consequently shifts X_j in [j,2j]
(or any integer subsequence R_j tending to infinity) with

    A_b(f_(X_j)) -> A_b(f).

Meanwhile the exact Fourier multiplier gives, for EVERY X,

    integral omega*|rho_(f_X)-rho_f|
      <=(2*c_X+c_X^2)*integral omega*rho_f ->0.

The polar inequality therefore passes to f along these shifts:
A_b(f)<=ell(rho_f). This proves weighted polar/full separator extension.
No positivity of a full-cone completion or prescribed arithmetic residue
has been assumed. Both X and2X errors are controlled simultaneously by
the same average, not by intersecting two unrelated good subsequences.

### 4a. Discrete simultaneous-scale proof using the corpus good-scale lemma

The same limit can be proved without continuous averaging. This is an
alternative proof of section4, not a stronger recovery claim. Put a_m=|b(m)|
for m>=2 and a_0=a_1=0, B(N)=sum_{m<=N}a_m and
H(N)=sum_{1<=m<=N}a_m/sqrt(m). Define the nonnegative sequence

    w_j = a_(j+1) + (1/sqrt(j+1))*sum_{j^2<m<=(j+1)^2} a_m.

The square blocks partition [1,N^2]. For N>=1, summing j=0,...,N-1 gives

    B(N)+B(N^2)/sqrt(N) <= sum_{j<N} w_j,
    sum_{j<N} w_j/sqrt(j+1) <= H(N)+H(N^2).

For the first inequality, sqrt(j+1)<=sqrt(N) in every block. For the
second, each m in that block satisfies sqrt(m)<=j+1, hence
a_m/(j+1)<=a_m/sqrt(m). These are finite nonnegative sums; no rearrangement
of a conditionally convergent series occurs. The envelope (4) makes the
second line o(log N). It therefore meets the all-cutoff affine envelope
in `WeilSingularArithmetic.exists_small_sqrt_mass_of_sublog_envelope`:
for every eta>0, absorb the finite initial segment into A>=0 and bound
the rest by eta*log N. That proved corpus theorem supplies arbitrarily
large N with

    B(N)/sqrt(N)+B(N^2)/N < epsilon.

Take the source aperture a>=0 and X=log N-2a. Then
exp(X+2a)=N, exp(2X+2a)<=N^2, c_X<=2*exp(a)/sqrt(N), and
c_X^2<=4*exp(2a)/N. Thus both remote terms in (5) are small at this SAME
X, which can be arbitrarily large. Together with the weighted spectral
estimate, this proves exactly the separator extension already obtained
above. The good-scale lemma is an existing finite partial-summation result;
the square-block device is elementary. Scientific novelty is not claimed.
This discrete version is implemented in `WeilWorkExposingRaySublogScales`
and `WeilWorkExposingRaySublogTransfer`. It reuses the actual source-checked
corpus theorem and preserves both scales. Both saved-leaf audits pass
without diagnostics.

## 5. Exact finite fibres

Repeat section5 of POLAR-FIBRE-DENSITY-PROOF.md in the real Banach space
L1(omega dt). The two signed coordinate resonators remain actual compact
polar sources with finite weighted norm, so every finite trace is attained.
The fibre is convex and nonempty. If an actual full mixture density were
outside the closed polar fibre, strict separation would supply ell and s.
Append the artificial row(-v,-s). For a nonnegative augmented null
combination, normalize its actual part when the artificial coefficient is
positive; when that coefficient is zero, add multiples of the null
combination to a fixed actual representative of v. Exactly the same
argument proves nonnegative augmented costs. Algebraic cone duality gives
b with b(v)>=s and A_b(f)<=ell(rho_f) on every polar row, in the raw
normalization. Section4 extends that inequality to every full row. Sum
the given full mixture to contradict strict separation.

Thus every actual full density lies in the closed polar fibre. Reverse
inclusion is immediate because every polar source is full. Taking closures
gives the asserted equality, and metric closure gives the finite recovery
statement. All algebraic and separation parents are the exact ones already
verified in WeilWorkExposingRayFibreDensity; only their ambient weighted
L1 space changes. This closes the paper argument for 0<=beta<1/2; beta=0 also follows
from the earlier ordinary L1 theorem by multiplying the norm by2.

## Hostile and novelty audit

- Primitive-layer square bounds alone are existing corpus mathematics.
  The finite geometric Euler-product estimate and both Cauchy--Schwarz
  steps are classical. Do not advertise those as scientific novelty.
- The application joins those bounds to simultaneous X/2X arithmetic
  control and exact weighted fibre recovery. Current searches did not
  locate that exact source theorem; absence and scientific novelty are
  not established. Relevant external ancestry includes Hardy-space
  coefficient estimates for Dirichlet polynomials, especially
  Bondarenko--Heap--Seip, arXiv:1405.6516 (2014; revised2015).
- Booker's L-data classification, arXiv:1308.3067, requires discrete
  multiplicities and other hypotheses absent here. It is not used.
- The conclusion stops strictly below1/2. It does not prove the previous
  beta<1 conjecture, the critical logarithmic estimate, E-recovery,
  E-escape, or the universal nonzero exposing-ray inequality.
- Weighted convergence with beta<1/2 does not imply convergence or even
  boundedness of gamma energy. No such limit passage occurs in the proof.

## Formalization status

1. DONE: arithmetic estimate (3) and primitive-layer inequality (4),
   retaining constants and quantifiers, in
   `WeilWorkExposingRaySublogArithmetic.lean`; final leaf and axioms pass.
2. DONE: actual resonator weighted budget and far-polar weighted
   convergence in `WeilWorkExposingRaySublogSources.lean`; final leaf and
   all6 public axioms pass. The actual-separator envelope passes final
   saved-leaf and both public axiom audits in
   `WeilWorkExposingRaySublogEnvelope.lean`. No coefficient envelope is
   postulated in the recovery theorem.
3. DONE: the discrete square-block proof in `WeilWorkExposingRaySublogScales`
   controls N and N^2 at the same cutoff. The actual remote arithmetic
   error and separator extension are proved in
   `WeilWorkExposingRaySublogTransfer`. Both final leaf audits pass.
4. DONE: exact finite-fibre separation and literal Fejer null recovery in
   `WeilWorkExposingRaySublogFibreDensity`, namespace
   `RHTower.ExposingRayTransfer.SublogFibre`. Final saved-leaf audit passes
   without diagnostics. Both poles and every integer atom are preserved.
   All29 owned leaves are umbrella-wired. The combined ten-public-theorem
   axiom audit passes with propext/Classical.choice/Quot.sound only.
   Global lint has six unrelated reachability
   errors; no WP02 finding. No full or umbrella build was run.
