# Scalar prime-phasor contraction of the deterministic level-2 entropy-budget conjecture

- **ID:** `prime-log-kronecker-coherence-capacity-conjecture`
- **Stage:** 1-in-progress
- **Type:** SUBORDINATE CONTRACTION / DETERMINISTIC PRIME-PHASE LARGE DEVIATIONS /
  CONNES APPLICATION / PRIME-PRODUCT SPECTRAL PRESSURE
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED] [SUBORDINATE; NOT THE ACTIVE CLAIM]`
- **Statement:** This card retains the scalar regularly varying phasor contraction, its arithmetic
  pressure form, and its Connes consequence.  The only active conjecture in this research lane is
  the stronger level-2 law in `prime-log-level-two-entropy-budget-law.md`; its contraction by
  the weighted phase map gives `(V5)` below.

## Subordination to the level-2 conjecture

No active conjecture is asserted by this card.  Equation `(V5)` is the contraction of the active
level-2 conjecture by the map sending a prime-phase empirical field to its regularly weighted
complex phasor.  The entrance-process, scalar-capacity, and superextensive statements retained
below are downstream tests.  They are not counted as additional conjectures, evidence, or partial
solutions.  This separation is load-bearing: a proof of one scalar estimate cannot be presented as
the full level-2 entropy law.

## Goal

The finite critical Mellin source has two apparently incompatible limits.

1. The prime number theorem makes its rescaled boundary measure converge weakly to the Laplace
   density `e^{-r/2}dr`.
2. At each finite aperture the source is atomic.  Its Fourier transform therefore has recurrent
   high-frequency phases and cannot converge uniformly to the Fourier transform of the continuous
   limit.

Fixed-frequency PNT convergence and abstract weak compactness do not identify where the missing
operator norm goes.  This conjecture predicts the complete phase diagram of that loss.  It is a
quantitative statement about one deterministic orbit in a torus whose dimension tends to
infinity, not an invocation of random independent prime phases.

For the Connes--Consani--Moscovici route, the conjecture would close a structural hole in the
prolate--boundary normal-form programme.  It would prove that carrier-frequency escape is absent
throughout every logarithmic Gamma graph window and becomes macroscopic only after the phase-time
budget reaches order `\pi(X)`.  Thus the low-energy normal form may contain prolate and spatial
boundary profiles without an additional uncontrolled prime-phase channel.

## Frontier certificate

The conjecture is not defined by the Connes application.  Its arithmetic core is the following
independent frontier problem:

```text
Determine the exponential-scale signed pressure of k-fold prime-product
near-collisions when

  k asymp pi(X),
  |log(m/n)| asymp exp(-tau pi(X)).
```

Solving it would simultaneously give:

1. a quenched high-dimensional entrance-process law for one fixed arithmetic Kronecker flow,
   including dimension-driven Poissonization beyond the known fixed-dimensional non-Poisson
   regime;
2. a deterministic large-deviation principle for a prime-supported Dirichlet polynomial at its
   full macroscopic deviation scale;
3. the first sharp shrinking-target law for the specific growing-dimensional Kronecker vector
   `(log p)_(p<=X)`;
4. an exact extreme-value clock `log H_X(q)~I_alpha(q)pi(X)`, rather than an existence or
   infinite-time equidistribution statement;
5. the missing prime-frequency estimate in the Connes critical-Mellin boundary channel.

The closest approximately-independent prime-phase machinery controls moment depth of order
`log T/log X`.  At `log T asymp pi(X)` the conjecture needs depth of order `pi(X)`.  The missing
factor `log X` is therefore a precise theorem gap, not a change of vocabulary.  General shrinking-
target theorems concern fixed-dimensional mixing systems or metric-almost-every frequency vectors;
the prime-log flow is nonmixing, arithmetically fixed, and its dimension tends to infinity.

The anti-theatre falsifier is equally precise: if the signed collision pressure at this depth has
any extra exponential term, then the proposed Bessel rate is false.  Proving only the independent
model, fixed moments, compact-time PNT convergence, or eventual Kronecker recurrence does not count
as progress on the conjecture.

## 1. The exact critical boundary transform

Put

```text
X>1,
k_X=pi(X),

D_X(t)
 =X^(-1/2) sum_(n<=X) Lambda(n)n^(-1/2)
      exp(i t(log X-log n))
  -1/(1/2-it).                                               (1)
```

The first term is the Fourier transform of the rescaled prime boundary measure

```text
mu_X
 =X^(-1/2) sum_(n<=X)Lambda(n)n^(-1/2)
      delta_(log X-log n),                                   (2)
```

and the second is the Fourier transform of

```text
nu(dr)=exp(-r/2)1_(r>=0)dr.                                  (3)
```

The prime number theorem gives

```text
mu_X => nu,
mu_X(R)->2,
D_X(t)->0 for every fixed t.                                 (4)
```

At each fixed `X`, however, the formalized cofinal annular recurrence of the finitely many prime
logarithms gives

```text
limsup_(|t|->infinity)|D_X(t)|=mu_X(R).                      (5)
```

Thus pointwise convergence and uniform convergence differ by an asymptotic norm exactly equal to
`2`.  The open question is only the least phase-time budget needed to recover a prescribed
fraction of that norm as `k_X->infinity`; full cofinal recurrence and simultaneous polar decay are
already unconditional.

## 2. The candidate rate function

Let `I_0` denote the modified Bessel function.  For `lambda>=0` define

```text
Lambda_*(lambda)
 =integral_0^1 log I_0(lambda/(2 sqrt(v)))dv,                 (6)

I_*(q)
 =sup_(lambda>=0){lambda q-Lambda_*(lambda)},
       0<=q<1.                                               (7)
```

The integral in `(6)` is finite.  It is the limiting logarithmic moment functional of the
independent-phase comparison model

```text
(1/(2 sqrt(X))) sum_(p<=X)(log p)/sqrt(p) exp(i theta_p),     (8)
```

at speed `pi(X)`.  The nonconstant weight `1/(2sqrt(v))` is forced by the prime density and the
critical coefficient `(log p)/sqrt(p)`; replacing it by an iid equal-weight model changes the
rate function and is not admissible.

Let `q_*(tau)` be the unique value in `[0,1)` satisfying

```text
I_*(q_*(tau))=tau,
q_*(0)=0.                                                    (9)
```

Equivalently, `q_*` is the inverse radial large-deviation cost.  It is increasing,
`q_*(tau)->1` as `tau->infinity`, and contains no zeta zero or RH hypothesis.

### Universal regular-variation family

The critical profile above is one member of a sharper conjectural universality class.  For
`0<=alpha<1`, put

```text
W_(X,alpha)=sum_(p<=X)(log p)p^(-alpha),
Z_(X,alpha)(t)=W_(X,alpha)^(-1)
  sum_(p<=X)(log p)p^(-alpha-it),
w_alpha(v)=(1-alpha)v^(-alpha).                            (9a)
```

The prime number theorem gives `W_(X,alpha)~X^(1-alpha)/(1-alpha)` and, for
`p~vX`,

```text
pi(X) (log p)p^(-alpha)/W_(X,alpha) -> w_alpha(v).         (9b)
```

Define

```text
Lambda_alpha(lambda)
 =integral_0^1 log I_0(lambda w_alpha(v))dv,

I_alpha(q)
 =sup_(lambda>=0){lambda q-Lambda_alpha(lambda)}.          (9c)
```

More generally, replace `p^(-alpha)` by `p^(-alpha)L(p)`, where `L` is any positive slowly
varying function for which the usual uniform convergence and Potter bounds hold.  Karamata
normalization leaves the limiting profile `w_alpha` unchanged.

The regular-variation universality assertion is precisely `(V5)` below with
`S_(X,alpha)`, `Lambda_alpha`, and `J_alpha`, at the same speed `pi(X)`, for every fixed
`alpha in [0,1)` and every such slowly varying perturbation.  Its scalar consequences predict an intrinsic
three-regime phase transition at the square-summability boundary `alpha=1/2`:

```text
alpha<1/2:
  I_alpha(q)~[(1-2alpha)/(1-alpha)^2]q^2,

alpha=1/2:
  I_alpha(q)~2q^2/log(1/q),

alpha>1/2:
  I_alpha(q)~C_alpha q^(1/(1-alpha))                      (9d)
```

as `q->0+`, where

```text
K_alpha=((1-alpha)^(1/alpha)/alpha)
  integral_0^infinity log I_0(x)x^(-1/alpha-1)dx,

C_alpha=(1-alpha)alpha^(alpha/(1-alpha))
  K_alpha^(-alpha/(1-alpha)).                             (9e)
```

At the opposite endpoint the logarithmic coherence coefficient is universal throughout the
family:

```text
I_alpha(q)
 =1/2 log(1/(1-q))
  +1/2 log(pi(1-alpha))-(1-alpha)/2+o(1)                  (9f)
```

as `q->1-`.  Thus the conjecture predicts two different kinds of universality at once:

1. the low-coherence exponent changes exactly when the continuum weight leaves `L^2(0,1)`;
2. the high-coherence entropy coefficient remains `1/2` for every integrable power profile.

The endpoint laws `(9d)`--`(9f)` follow from the independent weighted cumulant and regular
variation; that calculation is parent theory.  The frontier assertion is that the **single actual
prime-log orbit** realizes these rate functions, with hard finite-time entropy censoring, uniformly
through all three regimes.  No fixed-dimensional Kronecker theorem, random Euler-product model,
or currently available Dirichlet-polynomial large-value estimate gives this statement.

## 3. Scalar contraction: deterministic entropy-censored Varadhan law

The scalar superlevel formulation is a consequence of a single functional law.  Retain the
normalized weights `a_(p,X)` in `(9g)` and define the complex prime phasor

```text
S_(X,alpha)(t)=sum_(p<=X)a_(p,X)exp(-it log p).             (V1)
```

For `u,z in R^2`, identify `R^2` with `C` and put

```text
Lambda_alpha(u)
 =integral_0^1 log I_0(|u|w_alpha(v))dv,

J_alpha(z)
 =sup_(u in R^2){<u,z>-Lambda_alpha(u)}.                   (V2)
```

Rotational symmetry gives `J_alpha(z)=I_alpha(|z|)` on the closed unit disk.  For every sequence
`T_X->infinity` with

```text
log T_X/pi(X)->tau in [0,infinity),                        (V3)
```

let `m_(X,T_X)` be the remote empirical probability law

```text
m_(X,T_X)
 =(1/T_X) integral_(T_X)^(2T_X) delta_(S_(X,alpha)(t))dt.  (V4)
```

### Prime-log entropy-censored Varadhan principle `[SUBORDINATE SCALAR CONTRACTION]`

For every continuous real potential `phi` on the closed unit disk,

```text
lim_(X->infinity) (1/pi(X)) log
  integral exp(pi(X)phi(z)) dm_(X,T_X)(z)

 =sup_{|z|<=1, J_alpha(z)<=tau}{phi(z)-J_alpha(z)}.        (V5)
```

The convergence is required locally uniformly for `tau` in compact subsets of
`[0,infinity)`.  Slowly varying perturbations of the weights are included exactly as in `(9a)`--
`(9f)`.

Equation `(V5)` is the scalar contracted law.  It says positively that the finite observation
clock carries precisely the rate states whose independent-torus information cost fits inside its
time entropy:

```text
accessible deterministic phase space at entropy tau
 ={z:J_alpha(z)<=tau}.                                    (V6)
```

There is no averaging over the frequency vector, no random Euler product, and no random initial
phase.  The only measure in `(V4)` is ordinary time along the single orbit
`t(log p)_(p<=X)`.

The functional formulation is strictly stronger than one moment estimate.  Approximation of
indicators from above and below gives the entropy-censored occupation law for every regular Borel
target.  Truncating the potential `2lambda log|z|` gives the high-moment free energy.  Taking a
potential with a sufficiently high plateau on a target of cost greater than `tau`, together with
the elementary derivative bound for `S_(X,alpha)`, forces eventual non-entry rather than merely
exponentially small occupation.  Thus first-hit exclusion is encoded in `(V5)` and is not an
additional axiom.

The anti-theatre core is the quantifier over **all continuous potentials** on the complex disk.
Proving only the independent Haar LDP, one superlevel estimate, one high moment, or a subsequence
of clocks does not prove `(V5)`.  Conversely, a single potential for which a prime-product
near-collision cluster creates an extra exponential pressure falsifies the conjecture.

### Arithmetic local-REM interpretation

At `k_X~lambda pi(X)`, expand

```text
S_(X,alpha)(t)^k=sum_m b_(X,k)(m)m^(-it).                  (V7)
```

The states are exponent vectors of `k` prime selections, their deterministic energies are
`log m`, and `b_(X,k)(m)` is the multinomial Gibbs weight after permutation degeneracies have been
collapsed.  Equation `(V5)` asserts a deterministic, weighted local-random-energy law for this
prime-product landscape at resolution `exp(-tau pi(X))`.  This is where the conjecture meets an
actual second frontier: local-REM theorems prove Poisson energy statistics for random coefficient
landscapes, while `(V5)` asks for the cofinal deterministic landscape with coefficients
`(log p)_(p<=X)` and with nonuniform regular-variation Gibbs weights.

The exact scalar pressure gate is `(10i)`--`(10l)`.  The critical-scale point-process refinement
below requires the corresponding connected factorial pressures, just as local-REM Poissonization
requires more than convergence of a free energy.

## 3A. Downstream critical refinement: dimension-driven quenched entrance universality

The large-deviation law below records only occupation exponents.  The stronger object is the
entrance process of the growing-dimensional prime-log flow.

For the normalized weights

```text
a_(p,X)=(log p)p^(-alpha)L(p)/W_(X,alpha,L)
```

with `L=1` giving `(9a)`, put

```text
S_(X,alpha)(theta)=sum_(p<=X)a_(p,X)exp(i theta_p),
A_(X,alpha)(q)={theta in T^(pi(X)): |S_(X,alpha)(theta)|>=q},
omega_X=(-log p)_(p<=X).                                  (9g)
```

The actual prime orbit is `theta_X(t)=t omega_X mod 2pi`.  For every regular value `q` of
`|S_(X,alpha)|`, let `E_(X,alpha)(q)` be the set of inward crossing times of
`partial A_(X,alpha)(q)` by this orbit.  Define the normalized Haar entrance flux

```text
nu_(X,alpha)(q)
 =(2pi)^(-pi(X)) integral_(partial A_(X,alpha)(q))
    <omega_X,n(theta)>_+ d sigma(theta),                  (9h)
```

where `n` is the inward unit normal.  This is the stationary mean number of entrances per unit
time for a Haar-random starting phase.  The point-process assertion is made for fixed thresholds
that are regular values for all sufficiently large `X`.  The first-return and occupation
exponents are required for every `q in (0,1)`; nonregular thresholds are obtained by bracketing
with regular levels and using continuity of `I_alpha`.

### Quenched high-dimensional entrance law `[DOWNSTREAM TEST; NOT THE ACTIVE CONJECTURE]`

For every `0<=alpha<1` and every eventually regular `q in (0,1)`:

```text
(1/pi(X)) log nu_(X,alpha)(q) -> -I_alpha(q).             (9i)
```

Let `H_(X,alpha)(q)` be the first inward return after the coherent component containing `t=0`
has been left.  Then

```text
(1/pi(X)) log H_(X,alpha)(q) -> I_alpha(q).               (9j)
```

More strongly, take any `T_X` with

```text
log T_X/pi(X) -> tau>I_alpha(q),                          (9k)
```

and let `B_X` be uniform on `[T_X,2T_X]`.  Viewed as a random point measure through this random
remote origin, the deterministic entrance process satisfies

```text
sum_(t in E_(X,alpha)(q))
  delta_(nu_(X,alpha)(q)(t-B_X))
  ==> PPP(1)                                               (9l)
```

vaguely on `R`, where `PPP(1)` is the stationary unit-intensity Poisson point process.  The same
law is required jointly for finitely many disjoint coherence bands and finitely many thresholds.
Thus the conjecture predicts not only the logarithm of a first hit but the loss of the
fixed-dimensional affine-lattice correlations in the cofinal prime limit.

Equation `(9l)` is deliberately **not** a generic assertion that Kronecker flows are Poisson.
At fixed dimension their shrinking-target limit is known to be an affine-lattice process and is
generally non-Poisson.  The new claim is that the second limit

```text
target Haar mass ->0 while dimension=pi(X)->infinity       (9m)
```

Poissonizes that process for the single arithmetic direction `omega_X`, at exactly the
large-deviation clock forced by the regularly varying target geometry.  It is a quenched
arithmetic statement: Haar randomness is used only to define the intrinsic flux in `(9h)`, while
the crossings in `(9l)` belong to the actual orbit `t(log p)_(p<=X)`.

The predicted mechanism has two parents that do not combine in the literature.  Fixed-dimensional
integrable-flow hitting statistics are governed by random affine lattices and are non-Poisson;
high-dimensional random lattices can Poissonize.  The conjecture asserts a new arithmetic bridge:
the growing prime-log flow enters the high-dimensional Poisson regime without averaging the
frequency vector and with an exponentially rare, non-Euclidean phasor target.

### Consequences and equivalent arithmetic face

The entrance-flux exponent `(9i)`, the first-return law `(9j)`, and the remote Poisson law `(9l)`
force the entropy-censored occupation law `(10c)`--`(10d)` below; excursion widths are
subexponential in `pi(X)` and hence do not change its speed.  Exponential tilting then gives the
free energy `(10g)`.  Conversely, the full hierarchy of signed prime-product factorial moment
pressures strengthens `(10l)` to `(9l)`.  In this sense:

```text
quenched entrance process
  => first-return clock + occupation LDP + free energy
  => signed prime-product pressure,                         (9n)
```

while the reverse implication requires all factorial pressures rather than the single scalar
pressure in `(10l)`.

The first genuinely new proof obligation is therefore not the independent Steinhaus LDP.  It is
the following arithmetic decorrelation statement:

```text
At depth k asymp pi(X), all connected signed factorial
pressures of distinct prime-product near-collision clusters
vanish after the one-cluster pressure is removed.          (9o)
```

This is the exact high-dimensional Poissonization gate.  A surviving connected pressure would
produce a non-Poisson limit, falsify `(9l)`, and identify the residual arithmetic correlation that
the scalar large-deviation law cannot see.

## 3B. Macroscopic face: entropy-censored prime-log large deviations

The earlier first-hit formulation is only the zero/nonzero shadow of a stronger deterministic
law.  Put

```text
W_X=sum_(p<=X)(log p)/sqrt(p),
Z_X(t)=W_X^(-1)sum_(p<=X)(log p)/sqrt(p) exp(-it log p),
d_X=pi(X),

V_X(q;T)=meas{t in [T,2T]: |Z_X(t)|>=q}.                 (10a)
```

The normalization gives `W_X~2sqrt(X)`.  The prime-power and polar terms in `(1)` are negligible
on every positive exponential clock, so `Z_X` and `D_X/2` have the same macroscopic capacity
away from the bounded-frequency window.

### Entropy-censored deterministic LDP `[SCALAR CONSEQUENCE FORM]`

For every `q in (0,1)` and every sequence `T_X->infinity` with

```text
log T_X/d_X -> tau in [0,infinity),                         (10b)
```

the actual prime-log orbit obeys the sharp censoring alternative

```text
tau<I_*(q)  =>  V_X(q;T_X)=0 eventually,                   (10c)

tau>I_*(q)  =>  (1/d_X)log(V_X(q;T_X)/T_X)->-I_*(q).       (10d)
```

The convergence in `(10d)` is conjectured locally uniformly on compact subsets of
`{(q,tau):0<q<1, tau>I_*(q)}`.  The scalar occupation law alone makes no assertion at the critical
surface `tau=I_*(q)`; the downstream entrance-process law `(9l)` supplies the stronger critical-scale
prediction after normalization by the exact Haar flux.

This is an **entropy-censored** large-deviation principle: the independent-phase probability
`exp(-I_*(q)d_X)` is visible only after the deterministic observation window contains enough
phase-time entropy to pay for it.  Below that threshold the rare event is not merely small in
measure; it is absent.  Above it, every exponential dyadic window has the same logarithmic
occupation density as the independent weighted torus model.

Equation `(10c)` is the new arithmetic exclusion theorem.  Equation `(10d)` is the matching
deterministic abundance theorem.  Together they give the exact first-hit law

```text
log H_X(q)/pi(X) -> I_*(q),                                (10e)
```

and hence the complete capacity profile `(11)` below.  The older positive-entropy statement is
the weaker assertion that the left-hand side of `(10e)` has a positive lower limit.

### Equivalent thermodynamic form: entropy-censored free energy

For `lambda,tau>0`, define

```text
F_*(lambda,tau)
 =sup{2lambda log q-I_*(q):0<q<1 and I_*(q)<=tau}.          (10f)
```

If `k_X/pi(X)->lambda` and `log T_X/pi(X)->tau`, the predicted quenched high-moment law is

```text
(1/pi(X))log[
  (1/T_X)integral_(T_X)^(2T_X)|Z_X(t)|^(2k_X)dt]
 ->F_*(lambda,tau).                                        (10g)
```

This is not the ordinary independent-phase moment law.  The constraint `I_*(q)<=tau` is
load-bearing: a time window with entropy `tau*pi(X)` cannot sample a phase level whose cost is
larger than `tau*pi(X)`.  Once `tau` exceeds the cost of the unconstrained maximizer, `(10g)`
saturates at the independent Steinhaus free energy.  Before saturation, the maximizer lies on the
accessible entropy boundary and the free energy is frozen by the finite observation clock.

The occupation law `(10c)`--`(10d)` implies `(10g)` by a truncated Laplace principle.  Conversely,
the full family `(10g)`, together with the elementary derivative bound for `Z_X`, forces the
subcritical exclusion clause by exponential separation.  Thus `(10g)` is the moment/energy face
of the same conjecture, not a second route.

### Exact arithmetic form: prime-product spectral pressure

The thermodynamic law has a source-pure formulation with no probabilistic vocabulary.  Put

```text
a_(p,X)=1_(p<=X)(log p)/(sqrt(p)W_X),
P_X(t)=sum_(p<=X)a_(p,X)p^(-it),
P_X(t)^k=sum_m b_(X,k)(m)m^(-it),
K_(A,U)(L)=cosInt(L,A,U)/U.                                (10h)
```

Unique factorization makes `b_(X,k)` the exact weighted occupation law of `k`-fold prime
products.  The now-formalized arbitrary-window identity gives

```text
(1/U)integral_A^(A+U)|P_X(t)|^(2k)dt
 =sum_(m,n)b_(X,k)(m)b_(X,k)(n)K_(A,U)(log(n/m)),          (10i)

|K_(A,U)(L)|<=min(1,2/(U|L|)).                             (10j)
```

For `A=U=T_X`, define the signed prime-product pressure

```text
Psi_X(lambda,tau)
 =(1/pi(X))log[
   sum_(m,n)b_(X,k_X)(m)b_(X,k_X)(n)
      K_(T_X,T_X)(log(n/m))],                              (10k)
```

where `k_X/pi(X)->lambda` and `log T_X/pi(X)->tau`.  The macroscopic pressure face of the scalar
conjecture is

```text
Psi_X(lambda,tau)->F_*(lambda,tau).                        (10l)
```

Equation `(10l)` is the **prime-product spectral-pressure law**.  It is the sharpest arithmetic
statement on the card: it says that exponentially fine, signed multiplicative near-collisions
have a universal pressure determined solely by the weighted one-prime rate and the available
clock entropy.  Neither the diagonal nor the absolute off-diagonal energy has this limit by
itself in the censored phase.  The law concerns their signed interference.

This formulation gives an immediate falsifier.  Any additional exponential-scale pressure from
prime-product clusters at `|log(m/n)|asymp exp(-tau pi(X))` changes the right-hand side of `(10l)`
and kills the Bessel profile, even if ordinary fixed moments remain asymptotically independent.

### Endpoint fingerprints

The proposed rate is not a generic quadratic Cramer curve.  The singular critical weights force
the two asymptotic fingerprints

```text
I_*(q)~2q^2/log(1/q)                         as q->0+,      (10m)

I_*(q)=1/2 log(1/(1-q))+1/2 log(pi/2)-1/4+o(1)
                                               as q->1-.   (10n)
```

The logarithmic correction in `(10m)` comes from the non-square-integrable limiting weight
`v^(-1/2)/2`; the coefficient `1/2` in `(10n)` is the high-coherence phase-resolution entropy.
These are rigid predictions of the law, not adjustable constants.  A different small-coherence
scale or high-coherence coefficient falsifies the stated universal profile.

## 3C. Superextensive completion: prime-log minimax saturation

The fully proved ambient theorem exposes a sharper arithmetic frontier in the simultaneous
high-resolution limit.  For the normalized weights `a_(p,X)` in `(9g)`, define the intrinsic
projective water entropy

```text
H_(X,alpha)^proj(eta)
 =min_(p0<=X) inf {
    (1/2) sum_(p<=X,p!=p0) log x_p :
    x_p>=1,
    sum_(p<=X,p!=p0) a_(p,X)/x_p<=eta }.                 (10o)
```

The infimum is attained by the exact active/inactive reverse-water-filling rule, and the minimum
is attained by a prime pivot.  Let the first positive **integer** prime-log return be

```text
R_(X,alpha)(eta)
 =min {n>=1:
   |sum_(p<=X) a_(p,X) exp(-i n log p)|>=1-eta}.          (10p)
```

The unconditional projective water-entropy theorem proved in this project gives, uniformly in the
weights,

```text
log R_(X,alpha)(eta)
 <=H_(X,alpha)^proj(eta)
   +(pi(X)-1)log(2 pi sqrt(2)).                           (10q)
```

Thus the upper half of the following law is already a theorem.

### Prime-log minimax saturation `[DOWNSTREAM SUPEREXTENSIVE TEST]`

For every regularly varying family in `(9a)`--`(9g)` and every sequence `eta_X in (0,1]` such
that

```text
eta_X->0,
H_(X,alpha)^proj(eta_X)/pi(X)->infinity,                  (10r)
```

one has

```text
log R_(X,alpha)(eta_X) /
  H_(X,alpha)^proj(eta_X) -> 1.                           (10s)
```

Equivalently, for every fixed `epsilon>0`, eventually no integer

```text
1<=n<=exp((1-epsilon)H_(X,alpha)^proj(eta_X))             (10t)
```

returns the weighted prime phases to coherence `1-eta_X`, while the proved universal recurrence
theorem supplies a return before

```text
exp((1+epsilon)H_(X,alpha)^proj(eta_X)).                  (10u)
```

This is the exact deterministic statement that the prime-log vector receives no
**superextensive arithmetic entropy discount** relative to the worst-frequency projective
carrier.  It is not an equidistribution assertion and not an independent-phase calculation.  The
only open direction is the lower bound `(10t)` for the one vector `(log p)_(p<=X)`.

The conjecture is a double-scaling completion of `(V5)`, not a redundant restatement of its
compact-`tau` clause: here the information cost per prime diverges.  Conversely, any version of
the entropy-censored Varadhan principle uniform as `q->1` and `tau->infinity` implies `(10s)`.

### Exact anti-theatre gate

The theorem cannot be obtained from Kronecker density, Dirichlet simultaneous approximation,
the independent Haar target volume, or the now-proved minimax law: all four provide `(10q)` or an
ambient comparison, whereas `(10t)` is source-specific.  A proof must exclude exponentially early
integer solutions to a growing family of simultaneous linear forms

```text
n log(p/p0)-2 pi r_p,                                    (10v)
```

at the anisotropic water scales selected by `(10o)`.  In the moment language this is exactly the
absence of an additional superextensive signed pressure from prime-product near-collision
clusters.  A single sequence with

```text
H_(X,alpha)^proj(eta_X)-log R_(X,alpha)(eta_X)
  asymp H_(X,alpha)^proj(eta_X)                           (10w)
```

falsifies the conjecture and measures the arithmetic entropy discount.  Proving a Baker-type
bound for one coordinate, a fixed-depth moment estimate, or a metric theorem for almost every
frequency vector does not address `(10t)`.

## 4. First-hit consequence: positive prime coherence entropy

For `0<q<1`, define the first macroscopic coherence clock

```text
H_X(q)=inf{T>=1:
  sup_(1<=|t|<=T)|D_X(t)|>=2q}.                              (11a)
```

### Prime coherence-entropy law `[WEAK CONSEQUENCE FORM]`

For every `q in (0,1)`,

```text
liminf_(X->infinity) log H_X(q)/pi(X)>0.                    (11b)
```

Equivalently, for every positive time scale `T_X`,

```text
log T_X=o(pi(X))
  => sup_(1<=|t|<=T_X)|D_X(t)|->0.                          (11c)
```

This is the irreducible theorem target.  It says positively that every nonzero macroscopic
prime--polar coherence level must pay a positive exponential cost in the number of independent
prime phases.  It is a deterministic statement about the actual orbit `t(log p)_p`; random phases,
almost-every frequency vectors, and infinite-time Bohr recovery do not imply it.

The opposite finiteness statement is unconditional.  The delayed positive-weight recurrence gives,
for every integer `Q>=0` and every clock floor `L>=1`, a return by time

```text
L(Q+1)^(pi(X)+o(pi(X)))                                    (10d)
```

whose relative phase loss is at most `2pi^2/(Q+1)^2` and whose polar loss is at most `1/L`.
Consequently, for each `q<1`,

```text
limsup_(X->infinity) log H_X(q)/pi(X)
 <=inf{log(Q+1): 1-2pi^2/(Q+1)^2>q}<infinity.               (10e)
```

In particular, the proved high-coherence cost has the correct square-root resolution order

```text
log H_X(q)/pi(X)
 <=(1/2)log(1/(1-q))+O(1)       as q->1-.                  (10f)
```

Thus the genuine frontier is not whether the coherence clock is at most exponential.  It is the
matching positive lower entropy `(10b)` for the one arithmetic prime-log orbit.

The ambient minimax scale is no longer conjectural.  For the least worst-frequency deadline
`T_(d,Q)` at defect

```text
delta_Q=(2pi/(Q+1))^2/2,
```

the formalized universal dimension--resolution law gives

```text
(d-1)log(Q+1)-O(d)-log d
  <log T_(d,Q)<=d log(Q+1),                                (10g)
```

with every constant explicit.  In normalized form,

```text
1-1/d-C/log(Q+1)
 <log T_(d,Q)/(d log(Q+1))<=1.                             (10h)
```

Hence the quadratic defect entropy coefficient `1/2` is a theorem for the universal minimax
problem.  Conjecture `(10b)` asks whether the deterministic prime-log vector belongs to the
positive-entropy side of this universal law.  It cannot be answered by another ambient packing
argument; it needs arithmetic information about the prime-log orbit.

## 5. Capacity profile

For `tau>=0`, set

```text
C_X(tau)=sup_{1<=|t|<=exp(tau pi(X))}|D_X(t)|.               (10)
```

### Prime-log coherence-capacity profile `[SCALAR PROFILE PREDICTED BY (V5)]`

For every `tau>=0`,

```text
lim_(X->infinity) C_X(tau)=2 q_*(tau).                       (11)
```

The convergence is locally uniform in `tau`.  More generally, for every positive time scale
`T_X`, writing

```text
tau_X=log T_X/pi(X),                                        (12)
```

one has the trichotomy

```text
tau_X->0       => sup_(1<=|t|<=T_X)|D_X(t)|->0,
tau_X->tau     => sup_(1<=|t|<=T_X)|D_X(t)|->2q_*(tau),
tau_X->infinity=> sup_(1<=|t|<=T_X)|D_X(t)|->2.              (13)
```

Prime powers of exponent at least two do not alter `(11)`: their total critical weight is
`o(sqrt(X))`.  The subtraction in `(1)` is load-bearing.  It removes the deterministic continuum
coherence visible at bounded `t`; without it, the value at `t=0` would make every capacity equal
to the trivial total mass.

The Bessel profile in `(11)` is a sharpened candidate, not protected from falsification.  The
irreducible frontier statement is `(10b)`--`(10c)`, equivalently the first implication in `(13)`:

```text
log T_X=o(pi(X))
  => sup_(1<=|t|<=T_X)|D_X(t)|->0.                          (13a)
```

If deterministic prime-log correlations change `q_*` at critical scale while `(13a)` survives,
the exact profile claim is retired but the Connes consequence remains.  If `(13a)` fails, the
two-channel prolate--boundary architecture must retain an independent phase carrier.

## 6. Equivalent aperture exponent law

Write `X=e^(2a)`.  For `theta>=0`, define

```text
E_theta(a)
 =sup_(1<=|t|<=exp(exp(theta a)))|D_(exp(2a))(t)|.           (14)
```

Since

```text
pi(exp(2a))~exp(2a)/(2a),                                   (15)
```

equation `(13)` predicts the sharp exponent transition

```text
theta<2 => E_theta(a)->0,
theta>2 => E_theta(a)->2.                                   (16)
```

The line `theta=2` has a logarithmic boundary layer.  Its nontrivial coordinate is

```text
log T/pi(exp(2a)),                                          (17)
```

and its universal profile is `2q_*`.  Thus the exponent `2` is not dimensional decoration: it is
the prime-counting cost of resolving the `pi(e^(2a))` independent phase directions.

## 7. Connes consequence

The archimedean multiplier in the corrected CCM symbol grows like

```text
m_Gamma(t)=log(2+|t|)+O(1).                                 (18)
```

A state whose Gamma energy is at most the natural aperture frame scale `e^a` can therefore occupy
only frequencies satisfying

```text
log(2+|t|)=O(e^a).                                          (19)
```

But

```text
e^a=o(pi(e^(2a))).                                          (20)
```

The subcritical clause of `(13)` then gives

```text
sup_(log(2+|t|)<=C e^a)|D_(e^(2a))(t)|->0                  (21)
```

for every fixed `C`.  Hence prime-phase recurrence cannot carry a nonzero leading boundary
defect inside the Gamma-admissible low-energy window.

In fact `(21)` and the uniform mass bound imply the global moving-graph estimate

```text
sup_(t in R)
 |D_(e^(2a))(t)|/[1+e^(-a)log(2+|t|)] ->0.                  (21a)
```

To see the implication, first restrict to `log(2+|t|)<=C e^a` and use `(21)`; on the complement
the denominator is at least `C`, while the numerator is bounded by the total prime and Laplace
masses.  Let `a->infinity` and then `C->infinity`.  Equation `(21a)` is the exact relative
operator-norm statement: the normalized prime--polar boundary defect is infinitesimal with
respect to the natural logarithmic Gamma graph weight.

This is the precise positive structural statement needed by the cofinal prolate--boundary
normal-form conjecture:

```text
bounded Gamma budget
  => subcritical prime-phase capacity
  => uniform boundary dephasing
  => no independent carrier-frequency escape channel.       (22)
```

The remaining RH-bearing term is still the sign of the subleading assembled boundary form.  The
conjecture does not call that sign new and does not derive it from `(11)`.

## 8. Why this is not a known theorem in disguise

The following parent results do not imply `(11)`.

1. **Kronecker and Dirichlet approximation.**  They prove density and a coarse recurrence upper
   bound at each fixed dimension.  They do not give an extreme-value law when the dimension is
   `pi(X)` and the observation time is exponential in that dimension.
2. **Prime number theorem.**  It proves `(4)` at each fixed frequency and on compact frequency
   sets.  It gives no control of the exponentially growing window `(10)`.
3. **Granville--Lamzouri approximate independence.**  Their large-deviation theorem explicitly
   treats `p^(it)` and is the closest parent.  For primes up to `Q` in a time interval of length
   `T`, their elementary product-separation argument supplies approximate independence only to
   moment depth

   ```text
   L=O(log T/log Q).
   ```

   At our critical cutoff `Q=X` and clock `log T asymp pi(X)`, this is
   `L=O(pi(X)/log X)`, whereas a fixed macroscopic deviation of the critical equal-mass prime
   field requires exponential tilting, or moments, of order `pi(X)`.  The missing factor
   `log X` is exactly the exponentially fine near-collision problem `(23c)` below.  Their theorem
   validates the random comparison model but does not reach `(10c)` or `(10d)`.
4. **Random Euler products and zeta value distribution.**  They replace prime phases by random
   independent phases or work in ranges whose available independence depth is subcritical.
   The new law is a deterministic censoring and occupation theorem for the one actual prime-log
   orbit.
5. **Resonance methods.**  They construct selected large values of zeta or its logarithmic
   derivative.  They do not identify the complete capacity curve, its weighted Bessel rate, or
   the subcritical uniform dephasing threshold.
6. **Infinite-torus Kronecker dynamics.**  Minimality and unique ergodicity do not give the
   growing-dimensional hitting-time asymptotic `(11)`.
7. **Universal hitting statistics for integrable flows.**  The Dettmann--Marklof--Strombergsson
   limit keeps the torus dimension fixed while the target shrinks and obtains a generally
   non-Poisson affine-lattice process after averaging admissible initial data or parameters.  The
   scalar contraction instead sends the dimension to `pi(X)`, fixes the prime-log direction, uses a
   large-deviation phasor target, and predicts that the affine-lattice correlations themselves
   disappear.  Sodergren's high-dimensional length process and Klartag's exponentially accurate
   Poisson approximation for random lattices supply a mechanism for the second limit, but not this
   deterministic arithmetic specialization.
8. **Local random-energy universality.**  Borgs--Chayes--Mertens--Nair prove local Poisson energy
   statistics for number partitioning with iid random coefficients, including a sharp breakdown
   scale for growing energies.  Recent linear-REM results obtain Poisson--Dirichlet Gibbs weights
   after random coefficients and independent thinning.  These results identify the correct
   factorial-moment mechanism but do not cover a deterministic coefficient vector, multinomial
   prime-product degeneracies, regular-variation Gibbs weights, or one time orbit.  Replacing
   `(log p)` by iid coefficients proves a parent model and does not prove `(V5)`.

A targeted exact-object Google/arXiv audit through 2026-07-20 found quantitative Kronecker density, the
Granville--Lamzouri large-deviation framework for approximately independent arithmetic families,
Guth--Maynard large-value estimates, random Euler products, resonance methods, and
metric discrepancy laws for almost every Kronecker vector, shrinking-target results for mixing
flows, fixed-dimensional non-Poisson integrable-flow hitting laws, high-dimensional random-lattice
Poissonization, and infinite-dimensional Kronecker minimality.  No source found states the
regular-variation entropy-censoring law, the deterministic prime specialization
`(10c)`--`(10d)`, moment depth `asymp pi(X)` at `log T asymp pi(X)`, or the
functional all-potential law `(V5)`, nor the critical-Mellin/Connes consequence `(21)`.  Beck-type
metric results do not apply to the single arithmetic vector `(log p)_(p<=X)` and do not furnish a
growing-dimensional weighted rate curve.  The exact-object audit therefore passes the project's
novelty filter.  As always, historical priority remains defeasible by a source outside the audited
literature; that scientific caveat does not weaken the mathematical content or make the statement
conditional.

## 9. Anti-theatre kill tests

This card is killed, not promoted, if any of the following occurs.

1. **Fixed-dimension collapse.**  The proof holds only after fixing a finite prime set.
2. **Random-model substitution.**  Independent random phases prove `(7)` but are silently
   substituted for the deterministic orbit in `(10)`.
3. **Average-for-supremum substitution.**  A mean-value theorem in `t` is presented without both
   parts of the censoring law: eventual absence below cost and the sharp occupation exponent above
   cost.
4. **PNT theatre.**  Only compact-frequency convergence in `(4)` is proved.
5. **Dirichlet theatre.**  Only the supercritical recurrence `limsup>=2` is obtained.
6. **Wrong normalization.**  The continuum transform in `(1)`, the prime weights, or the speed
   `pi(X)` is changed to force a convenient iid model.
7. **RH circularity.**  A zero-free region of RH strength, the Weil criterion, or positivity of
   the completed boundary form is used to prove `(11)`.
8. **Literature collision.**  A published theorem already supplies the deterministic weighted
   extreme-value curve `(11)` for the prime-log orbit.  Generic Kronecker, Cramer, or resonance
   theorems do not meet this test.
9. **Fixed-dimensional Poisson theatre.**  A random-initial-condition theorem for a fixed
   integrable flow is substituted for `(9l)`.  The known fixed-dimensional limit is generally
   non-Poisson.  The conjecture lives or dies on the additional cofinal dimension limit for the
   one prime-log direction.
10. **Scalar-pressure theatre.**  Only `(10l)` is proved and Poisson entrance statistics are
    inferred without controlling connected factorial pressures.  A scalar moment exponent cannot
    rule out clustered or affine-lattice limits.
11. **Random-energy theatre.**  A local-REM theorem with random coefficients, random thinning, or
    probability over the frequency vector is substituted for the deterministic prime-log
    empirical law `(V5)`.
12. **Single-potential theatre.**  One potential, one moment order, or one superlevel set is
    controlled and presented as the functional principle.  The scalar law quantifies over every
    continuous potential on the disk and every exponential clock entropy.
13. **Ambient-minimax theatre.**  The universal projective water-entropy sandwich is substituted
    for prime-log minimax saturation `(10s)`.  The proved theorem supplies the upper return clock
    for every frequency vector; it gives no source-specific lower bound for `(log p)`.

## 10. Research attack

The proof problem has four sharply separated gates.

### A. Independent-phase variational law

Prove the weighted triangular-array large-deviation principle with cumulant `(6)`, including the
radial contraction `(7)` and the negligibility of higher prime powers.  This is parent-theory
infrastructure and is not the new core.

### B. Deterministic exponential-time upper bound

For every `q` and `epsilon>0`, prove

```text
meas{t in [1,T]: |D_X(t)|>=2q}
 <=T exp(-(I_*(q)-epsilon)pi(X))                             (23)
```

uniformly for `log T=O(pi(X))`, with an error strong enough to imply absence of a hit when
`log T<(I_*(q)-2epsilon)pi(X)`.  This is the principal new Diophantine/exponential-sum gate.

The exact arithmetic object behind this gate can be stated without probabilistic language.  For
the normalized prime polynomial

```text
P_X(t)=sum_(p<=X) a_(p,X)p^(-it)
```

write

```text
P_X(t)^k=sum_m b_(X,k)(m)m^(-it).                           (23a)
```

Then the finite-time moment has the exact sinc-kernel decomposition

```text
(1/(2T)) integral_(-T)^T |P_X(t)|^(2k)dt
 =sum_(m,n)b_(X,k)(m)conj(b_(X,k)(n))
    sinc(T log(n/m)).                                      (23b)
```

The diagonal is the independent-phase moment.  Every deterministic obstruction is concentrated
in the weighted near-collision energy

```text
E_(X,k)(T)
 =sum_(m!=n)|b_(X,k)(m)b_(X,k)(n)|
    min(1,1/(T|log(m/n)|)).                                (23c)
```

The actual Gate B is therefore the signed spectral-pressure law `(10l)` at orders
`k asymp pi(X)`.  It is **not** correct to demand that `(23c)` always be negligible relative to the
diagonal.  When the clock entropy `tau` is below the independent moment saddle, near-collisions can
dominate the diagonal and must reproduce the censored free energy `(10f)`.  The correct target is
the full exponential asymptotic `(10g)`, with the diagonal-dominated independent phase law only
after the saturation threshold.  The crude integer-spacing bound loses an entire factor `log X`
in the available moment depth; ordinary mean-value theory therefore cannot reach this transition.
This censored collision/free-energy law is the exact nonclassical arithmetic core, not the already
solved torus-volume problem.

### C. Deterministic hitting lower bound

Prove that every superlevel with `I_*(q)<tau` is hit before `exp(tau pi(X))`.  A quantitative
Kronecker theorem must be weighted and asymptotically rate-optimal; the ordinary pigeonhole bound
does not recover the curve.

The endpoint `tau_X->infinity` is already proved by the delayed weighted recurrence.  Phase
resolution `Q` and clock floor `L` are independent and cost at most

```text
log L+pi(X)log(Q+1),                                       (24)
```

while the phase error is at most `2pi/(Q+1)` and the polar term is at most `1/L`.  Taking
`Q,L->infinity` sufficiently slowly under `tau_X->infinity` proves full coherence.  Gate C
therefore concerns only the finite critical-rate curve, not eventual full coherence or polar
decay.

### D. Gamma-window transfer

Transfer the subcritical result through the exact critical Mellin Stieltjes pairing and the
variable-width parity principalization.  Prove `(21)` as an operator estimate in the logarithmic
Gamma graph norm, then insert it into the prolate--boundary relative normal form without changing
the subleading Weil sign.

## Gates

- [x] source-pure observable `(1)` identified
- [x] correct growing dimension and critical time scale identified
- [x] candidate weighted variational rate `(6)`--`(9)` derived
- [x] anti-theatre and initial literature audit completed
- [x] sharp finite-dimensional pigeonhole budget formalized in
  `quantitative-finite-prime-log-phase-recurrence.md`
- [x] weighted-source recurrence and deterministic norm-capacity floor formalized in the same
  card
- [x] delay--resolution recurrence with simultaneous critical-pole decay formalized; the
  `tau_X->infinity` branch is unconditional
- [x] universal worst-frequency dimension--resolution law formalized, including the exact
  normalized entropy squeeze
- [x] arbitrary-weight projective reverse-water-filling law formalized: canonical active/inactive
  levels, exact pivot optimization, matching Haar floor and recurrence ceiling, active-set support,
  and the finite normalized superextensive law
- [x] prime-log superextensive minimax saturation isolated as the one-sided frontier `(10s)`;
  its limsup is unconditional and only the early-return exclusion `(10t)` remains open
- [x] prime-specific open core isolated as the cofinal weighted local multiplicative-energy law
  `(10l)`
- [x] exact shifted-window signed collision identity and universal kernel envelope formalized
- [x] exact finite weighted Steinhaus Laplace product, half-period symmetry, positivity, and
  exponential envelopes formalized
- [x] independent-phase triangular-array LDP paper proof completed as a bridge
- [x] endpoint rate fingerprints `(10m)`--`(10n)` paper proof completed as a bridge
- [x] scalar deterministic empirical contraction isolated in the functional form `(V5)`
- [x] random-coefficient local-REM parent identified and separated from the deterministic
  prime-log obligation
- [ ] prove the entropy-censored Varadhan principle `(V5)`
- [ ] prove prime-log minimax saturation `(10s)` in the superextensive regime
- [ ] prove the Haar entrance-flux exponent `(9i)`
- [ ] prove vanishing of every connected signed factorial pressure `(9o)`
- [ ] prove the quenched Poisson entrance law `(9l)`
- [ ] prove subcritical eventual absence `(10c)`
- [ ] prove supercritical occupation exponent `(10d)`
- [ ] prove the equivalent entropy-censored high-moment free energy `(10g)`
- [ ] deduce the exact first-hit and capacity laws
- [ ] formalize every unconditional layer in Lean
- [ ] transfer the subcritical law and `(21a)` to the exact CCM Gamma graph

## Preliminary comparison sources

- A. Granville and Y. Lamzouri, *Large deviations of sums of random variables*,
  arXiv:2104.02048.  This is the closest conceptual parent: it includes `p^(it)` and proves
  arithmetic large-deviation laws from finite approximate independence.  Its available moment
  depth at the present critical cutoff is smaller than `pi(X)` by a factor of order `log X`.
- K. Soundararajan, *Extreme values of zeta and L-functions*, arXiv:0708.3990.
- L. Guth and J. Maynard, *New large value estimates for Dirichlet polynomials*,
  arXiv:2405.20552, v2 (2026).  This is the strongest nearby general large-values input for Gate B,
  but it does not
  state the finite-time prime-log capacity law `(11)` or the subcritical uniform dephasing
  assertion `(13a)`.
- O. F. Brevig, *On the Sidon Constant for Dirichlet Polynomials*, arXiv:1306.0403.  Infinite-time
  Bohr/Sidon norm recovery is parent theory; the growing finite-time horizon is the missing datum.
- A. Gorodnik and P. Vishe, *Simultaneous Diophantine approximation -- logarithmic
  improvements*, arXiv:1601.03525.
- L. Baroni, *Kronecker Flow on the Infinite Torus*, arXiv:2604.02213.
- C. P. Dettmann, J. Marklof, and A. Strombergsson, *Universal hitting time statistics for
  integrable flows*, arXiv:1606.04068.  Their fixed-dimensional shrinking-target process is
  explicitly non-Poisson and is described by affine lattices; it is the principal hostile parent
  of `(9l)`, not evidence for it.
- A. Sodergren, *On the Poisson distribution of lengths of lattice vectors in a random lattice*,
  arXiv:1001.3623.  This proves a high-dimensional Poisson limit for random lattices.  It motivates
  the dimension-driven mechanism but does not treat a deterministic prime-log direction, phasor
  targets, or exponential hitting clocks.
- B. Klartag, *Poisson approximation of random lattices*, arXiv:2605.10479.  This gives
  exponentially accurate total-variation Poisson approximation for a random covolume-one lattice
  restricted to suitable sets of volume `O(d)`.  It makes the random-lattice parent substantially
  stronger, but the conjecture's missing step remains quenched arithmetic equidistribution of the
  single prime-log orbit and its regularly varying phasor target.
- C. Borgs, J. Chayes, S. Mertens, and C. Nair, *Proof of the local REM conjecture for number
  partitioning I: Constant energy scales*, arXiv:cond-mat/0501760, and *II: Growing energy
  scales*, arXiv:cond-mat/0508600.  These are the closest energy-landscape parents, but their
  coefficients are iid random variables; the deterministic prime-log vector and its multinomial
  product landscape are not covered.
- F. Concetti and S. Franchini, *REM universality and Poisson--Dirichlet Gibbs weights for linear
  random energy*, arXiv:2606.07757.  This sharpens the random-coefficient/thinned parent in 2026;
  it does not remove the quenched arithmetic gate in `(V5)`.
- J. Beck, *Probabilistic Diophantine approximation, I. Kronecker sequences*, Ann. of Math. 140
  (1994), 451--502.  This is a metric/almost-every-frequency parent, not a theorem about the
  growing prime-log vector.
- Classical Kronecker and Dirichlet simultaneous approximation theorems.
- Classical Cramer/Gartner--Ellis large-deviation theory for triangular arrays.

Exact-phrase and exact-object searches on 2026-07-20 for weighted Kronecker recurrence,
reverse-water-filling recurrence, weighted phasor first-return entropy, and simultaneous prime-log
return found reverse water filling only in Gaussian rate--distortion theory, quantitative
Kronecker results without the phasor/Haar sandwich, and isolated simultaneous logarithm problems.
No source found the joined projective theorem `(10)` or the source-specific saturation law
`(10s)`.  This is evidence for priority, not a mathematical proof of novelty.

## Log

- 2026-07-20 -- Proved and formalized the certificate-free projective water-entropy sandwich for
  every finite probability packet, including canonical active/inactive selection, global pivot
  minimization, exact active-set support, and a finite normalized superextensive law.  This turns
  the prime application into the sharper one-sided conjecture `(10s)`: the ambient limsup is now a
  theorem, and the only missing assertion is that the one prime-log vector receives no
  superextensive arithmetic entropy discount.  Exact-object searches found no joined recurrence
  theorem or prime-log saturation theorem.  Verdict: unconditional ambient theorem complete;
  arithmetic saturation remains a frontier conjecture.
- 2026-07-20 -- Recast the programme as the single entropy-censored empirical Varadhan principle
  `(V5)`.  The occupation LDP, high-moment law, first-hit threshold, and Connes graph-window
  estimate are now consequences of one functional identity; the entrance PPP is its finer
  critical-scale refinement.  Hostile comparison with local-REM theory isolated the genuine new
  bridge: random-coefficient energy landscapes Poissonize, while the deterministic multinomial
  prime-product landscape at resolution `exp(-tau pi(X))` is untreated.  Verdict:
  `SURVIVES EXACT-OBJECT SEARCH`; proof remains open.
- 2026-07-20 -- Strengthened the scalar entropy-censoring law to the quenched entrance-process
  conjecture `(9i)`--`(9l)`.  The hostile comparison found the correct opposing parents:
  fixed-dimensional integrable-flow hitting limits are non-Poisson affine-lattice processes,
  whereas high-dimensional random lattices Poissonize.  The surviving arithmetic frontier is the
  vanishing of connected signed prime-product factorial pressures for the one cofinal prime-log
  direction.  Verdict: `SURVIVES PRELIMINARY ATTACK`; novelty remains unverified.
- 2026-07-19 -- Created after the variable-width boundary principalization exposed an omitted
  carrier-frequency channel.  Compact-frequency PNT and fixed Sobolev regularization were demoted
  as parent theory; the surviving frontier is the deterministic `log T~pi(X)` capacity curve.
- 2026-07-20 -- **Historical scalar selection; superseded later the same day.**  At this stage the
  active conjecture was the functional entropy-censored Varadhan law `(V5)`.  The entrance-process statement `(9l)` and
  superextensive saturation statement `(10s)` are retained only as downstream strengthening tests;
  neither is being counted as a second solved or active master claim.  A renewed parent-theory
  audit checked the `p^{it}` large-deviation framework of Granville--Lamzouri, the 2026 Annals
  large-value theorem of Guth--Maynard, fixed-dimensional non-Poisson integrable-flow hitting laws
  of Dettmann--Marklof--Strombergsson, infinite-torus Kronecker minimality of Baroni, and
  high-dimensional Poisson approximation for random lattices of Klartag.  None supplies a quenched
  finite-clock LDP for the single growing vector `(log p)_(p<=X)`, and none reaches the signed
  prime-product pressure at `k asymp pi(X)` and spacing `exp(-tau pi(X))`.  Exact-object searches
  for deterministic prime-log large deviations, growing-dimensional Kronecker shrinking targets,
  and finite-time Bohr-lift pressure found no matching statement.  Verdict:
  `SURVIVES EXACT-OBJECT SEARCH`; novelty and priority remain unverified.
  The first open implication is exactly the convergence of
  the signed Bessel/Fourier resonance pressure to the censored variational functional; proving an
  independent-phase LDP or an eventual recurrence theorem does not touch that implication.
- 2026-07-20 -- Subordinated `(V5)` to the stronger active level-2 conjecture in
  `prime-log-level-two-entropy-budget-law.md`.  The scalar Bessel law is now explicitly a
  contraction of conditional relative entropy on the full empirical prime-phase field; this card
  remains the detailed arithmetic-pressure and Connes application record, not a second active
  conjecture.
