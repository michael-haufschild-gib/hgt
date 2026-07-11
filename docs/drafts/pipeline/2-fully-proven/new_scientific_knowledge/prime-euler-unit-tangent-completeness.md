# Prime Euler-unit tangents are complete at the zeta source

- **ID:** `prime-euler-unit-tangent-completeness`
- **Stage:** 2-fully-proven / candidate-new
- **Type:** theorem (paper), `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Scientific status:** Provisional pending independent expert verification of both the proof and
  the literature claim.  The exact theorem and its FE--Schwarz strengthening were not located in
  the checked completeness, Muntz, Fourier--Borel, analytic-functional, or Lambert-series
  literature.  Unlike the trivial-source completeness bridge, the proof must invert the tied
  prime-power Lambert tail and then use separated analytic-functional carriers.
- **Statement:** Let `D` be a bounded convex complex domain whose closure lies in `Re s>0`.  For
  every finite prime set `S`, the functions

  ```text
  w_p(s) = (log p) p^(-s)/(1-p^(-s))^2,    p prime, p notin S,
  ```

  have dense complex span in `O(D)` with the compact-open topology.  If, more strongly, `D` lies
  strictly between `Re s=1/2` and `Re s=1`, then the functional-equation-symmetric tangents

  ```text
  u_p(s)=w_p(s)-w_p(1-s)
  ```

  also have cofinite dense complex span.  On a small quartet-disjoint domain around a nonreal
  off-line point, their real span is dense in the underlying real holomorphic-germ space.  Consequently,
  the local orbit of the actual zeta Euler source under finite degree-one Euler-factor modifications
  is a determining set for continuous analytic germs, even after the modifications are paired with
  their FE reflections and restricted to real parameters preserving Schwarz symmetry.

## Goal

Move the source-image obstruction from the trivial Euler product to the actual zeta parameter
`a_p=1`.  At a strip zero, changing finitely many Euler factors by local units preserves the zero
and its multiplicity but changes the regular completed-flux germ.  The theorem proves that the
resulting tangent directions are complete: no nonzero continuous analytic equation on the local
regular germ can be invariant under all finite Euler-unit modifications.

This is a static source-orbit theorem, not a flow or limiting construction.

## Gates

- [x] 0 -> 1: actual-source tangent family and dual Lambert transform isolated
- [x] 1 -> 2: complete paper proof by sectorial Blaschke uniqueness and Mobius inversion
- [x] parent-theory audit: compared against generalized Muntz systems, perturbed exponential
  completeness, Fourier--Borel duality, and Lambert-kernel inversion
- [x] preliminary literature audit: exact and equivalent searches, stronger/general parent
  searches, and English/French/German/Russian terminology searches completed; independent expert
  review remains required
- [x] significance gate: excludes every continuous local analytic source constraint at the actual
  zeta Euler point, including the FE--Schwarz-symmetric orbit
- [x] provisional novelty verdict: `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- [ ] 2 -> 3: not selected for Lean before the scientific audit; the full proof requires analytic
  functionals and a sectorial Blaschke theorem not currently exposed by the project API

## The source tangent

For one prime put

```text
phi_p(a)(s) = (log p) a p^(-s)/(1-a p^(-s)).
```

This is the logarithmic flux of the degree-one local factor `(1-a p^(-s))^(-1)`.  At the zeta
parameter `a=1`,

```text
partial_a phi_p(a)(s)|_(a=1)
  = (log p) p^(-s)/(1-p^(-s))^2
  = w_p(s).
```

Because `closure(D)` lies in `Re s>0`, every denominator is nonzero on `D`, and a complex
parameter neighbourhood of `a=1` is available for each finite prime set.

## Completeness theorem

Assume that a continuous linear functional `L : O(D) -> C` annihilates `w_p` for every prime
outside a finite set.  Compact-open continuity supplies a compact `K subset D` and `C_K>0` with

```text
|L(f)| <= C_K sup_(s in K) |f(s)|.
```

Define the Fourier--Borel transform

```text
F(z) = L(s |-> exp(-zs)).
```

Then `F` is entire.  Put

```text
delta = min_(s in K) Re s > 0,
M     = max_(s in K) |Im s|.
```

Choose `theta>0` so small that

```text
c = delta cos(theta) - M sin(theta) > 0.
```

For `z` in the sector `|arg z|<theta`,

```text
Re(zs) >= c |z|       for every s in K,
```

and therefore

```text
|F(mz)| <= C_K exp(-c m |z|),    m>=1.
```

The Lambert transform

```text
H(z) = sum_(m>=1) m F(mz)
```

is consequently holomorphic in that sector and bounded on every translated closed subsector away
from the vertex.

On `K`, the geometric derivative series converges uniformly:

```text
p^(-s)/(1-p^(-s))^2 = sum_(m>=1) m p^(-ms).
```

Thus for every retained prime,

```text
0 = L(w_p) = (log p) H(log p),
```

so `H(log p)=0`.

## Sectorial uniqueness

Fix `0<theta'<theta` and `R>0` so that the translated sector

```text
Omega = R + {r exp(i phi) : r>0, |phi|<theta'}
```

lies inside `|arg z|<theta`.  The function `H` is bounded and holomorphic on `Omega`.  The power map

```text
w = (z-R)^alpha,    alpha = pi/(2 theta'),
```

maps `Omega` conformally onto the right half-plane.  If `H` were nonzero, the zeros of the induced
bounded right-half-plane function would satisfy the Blaschke condition

```text
sum_j Re(w_j)/(1+|w_j|^2) < infinity.
```

For the zeros `z=log p`, this would require

```text
sum_p 1/(log p)^alpha < infinity.
```

The series diverges, even after deleting finitely many primes, by the prime number theorem.  Hence
the bounded function, and therefore `H`, is identically zero.

## Mobius inversion recovers the Fourier--Borel transform

For every sufficiently large positive real `x`, all `nx` lie in the sector and `H(nx)=0`.  Absolute
convergence follows from the exponential estimate above, so the double series may be regrouped:

```text
0
 = sum_(n>=1) mu(n) n H(nx)
 = sum_(n,m>=1) mu(n) n m F(mnx)
 = sum_(k>=1) k (sum_(n|k) mu(n)) F(kx)
 = F(x).
```

Thus `F` vanishes on a real ray.  Since it is entire, `F` is identically zero.  Differentiation at
zero gives

```text
L((-s)^j)=F^(j)(0)=0
```

for all `j`.  Polynomials are dense in `O(D)` for convex `D`, so `L=0`.  Hahn--Banach now proves
that the cofinite span of the `w_p` is dense.  QED.

## Nonlinear determining consequence at `a_p=1`

For a finite prime set `P` and parameters `b_p` near zero, define the actual-source increment

```text
Psi_P(b)(s)
  = sum_(p in P) [phi_p(1+b_p)(s) - phi_p(1)(s)].
```

It is a holomorphic map from a neighbourhood of zero in `C^P` to `O(D)`, with

```text
d Psi_P(0)(b) = sum_(p in P) b_p w_p.
```

Let `A` be a continuous analytic germ at zero in `O(D)` and suppose

```text
A(Psi_P(b))=0
```

for every finite `P` and all sufficiently small `b`.  If `A_k` were its first nonzero homogeneous
Taylor coefficient, the degree-`k` part of `A o Psi_P` would force the continuous polynomial

```text
f |-> A_k(f,...,f)
```

to vanish on the span of the `w_p`.  Completeness, continuity, and complex polarization give
`A_k=0`, a contradiction.  Therefore `A` is the zero germ.

Equivalently, the finite Euler-unit orbit of the zeta source is analytically determining at the
actual source point.

## FE-symmetric tangent completeness on the right of the line

Assume now that

```text
closure(D) subset {s : 1/2 < Re s < 1}.
```

Pair a finite local modification with its functional-equation reflection.  At the logarithmic-flux
level its tangent at `a_p=1` is

```text
u_p(s)=w_p(s)-w_p(1-s).
```

The sign is forced by the chain rule: if a multiplicative gauge is `r(s)r(1-s)`, the negative
logarithmic derivative of the reflected factor is the negative of the reflection of the first
negative logarithmic derivative.

Suppose a continuous functional `L` on `O(D)` annihilates a cofinite set of the `u_p`, and again put

```text
F(z)=L(exp(-zs)).
```

Since both `K` and `1-K` lie in `Re s>0`, a sector about the positive real axis can be chosen on
which both `Re(zs)` and `Re(z(1-s))` are positive uniformly for `s in K`.  The function

```text
H_FE(z)
  = sum_(m>=1) m [F(mz)-exp(-mz)F(-mz)]
```

is therefore bounded and holomorphic on a translated subsector.  The equality `L(u_p)=0` says

```text
H_FE(log p)=0
```

for every retained prime.  The same sectorial Blaschke argument gives `H_FE=0`.

Apply the same absolutely convergent Mobius inversion to

```text
G(z)=F(z)-exp(-z)F(-z).
```

It gives `G=0`, hence

```text
F(z)=exp(-z)F(-z)                              (FE-dual symmetry)
```

for every complex `z`.  Differentiating at zero says

```text
L(P(s))=L(P(1-s))
```

for every polynomial `P`.

This symmetry forces `L=0` because its carrier and its reflected carrier are separated.  An
elementary Runge argument makes the last step explicit.  Let `K_0` be a compact convex
neighbourhood of `K` still lying strictly to the right of `Re s=1/2`.  Then `K_0` and `1-K_0` are
disjoint, and their union has connected complement.  Given a polynomial `P`, Runge approximation
supplies polynomials `P_j` converging uniformly to `P` on `K_0` and to zero on `1-K_0`.  The
FE-dual symmetry gives

```text
L(P_j(s))=L(P_j(1-s)).
```

The left side tends to `L(P)` and the right side tends to zero.  Thus `L(P)=0` for every polynomial;
polynomial density in `O(D)` gives `L=0`.  Hahn--Banach proves cofinite completeness of the `u_p`.

The same lowest-homogeneous-term argument now shows that the FE-paired finite Euler-unit charts are
analytically determining on `D`.

## FE--Schwarz real completeness on a quartet-disjoint germ

Let `D` now be a sufficiently small bounded convex neighbourhood of a point

```text
rho with 1/2 < Re rho < 1 and Im rho != 0,
```

so that the four closures

```text
closure(D),  1-closure(D),  conj(closure(D)),  1-conj(closure(D))
```

are pairwise disjoint.  Regard `O(D)` as a real locally convex space.  Then the cofinite **real**
span of the same FE tangents `u_p` is dense in `O(D)`.

Suppose a continuous real-linear functional `ell : O(D) -> R` annihilates the `u_p`.  Write

```text
ell(f)=Re L(f)
```

for a continuous complex-linear functional `L`.  Restricting `L` to entire functions gives an
analytic functional carried by a compact `K subset D`.  Let `L#` be its Schwarz-reflected analytic
functional, carried by `conj(K)`.  Since every `u_p` is Schwarz real,

```text
(L+L#)(u_p)=2 Re L(u_p)=0.
```

Run the FE Lambert-transform proof above on the analytic functional `L+L#`.  Its transform is the
sum of the transform for `L` and its Schwarz reflection, and the prime-log zero set again forces

```text
L+L# = R_*(L+L#),
```

where `R(s)=1-s` and `R_*` denotes reflected pushforward of an analytic functional.

The left side is carried by the two right-half compacts `K union conj(K)`.  The right side is
carried by the two disjoint left-half compacts `(1-K) union (1-conj(K))`.  A single analytic
functional carried by two polynomially separable compact sets is zero: Runge approximation of one
on the first carrier and zero on the second forces every test value to vanish.  Therefore

```text
L+L#=0.
```

Now `L=-L#` is simultaneously carried by the disjoint upper and lower compacts `K` and `conj(K)`.
The same Runge separation gives `L=0`, hence `ell=0`.  Real Hahn--Banach proves real density.

For real parameters `a_p` near `1`, the gauge

```text
r_(p,a)(s) r_(p,a)(1-s),
r_(p,a)(s)=(1-p^(-s))/(1-a_p p^(-s)),
```

preserves both the functional equation and Schwarz reality on the strip, and its real tangent is
`u_p`.  Therefore the FE--Schwarz finite-prime orbit is determining for continuous real-analytic
germs on the fundamental domain `D`.

This is the symmetry-compatible form relevant to an off-line zero quartet: no local continuous
real-analytic compatibility of the regular completed-flux germ survives the exact elementary
symmetries and all finite Euler-unit changes.

## Comparison with arbitrary symmetric order-one realizers

The arbitrary-realizer class has the same local real-analytic closure for an elementary reason.
Write `z=s-1/2`.  Let `P(z)` be a real even polynomial and, for sufficiently small real `epsilon`,
put

```text
Q_epsilon(s)=1+epsilon P(s-1/2).
```

Then `Q_epsilon` is FE invariant and Schwarz real.  It is nonzero on the selected quartet of small
germ domains when `epsilon` is small.  Multiplying an entire order-one realizer by `Q_epsilon`
preserves entire order one, both symmetries, and the selected zero with its multiplicity.  The
regular logarithmic-flux tangent is

```text
-d/ds log Q_epsilon(s)|_(epsilon=0) = -P'(s-1/2),
```

a centered real odd polynomial.

Centered real odd polynomials are real-dense in `O(D)` on one quartet fundamental domain.  Given
`f in O(D)`, extend it to the four disjoint domains by FE oddness and Schwarz reality.  Runge
approximation on their union gives a polynomial approximation; averaging that polynomial under
the two involutions produces a centered real odd polynomial with the same approximation on `D`.
Conversely, every centered real odd polynomial is the derivative of a centered real even
polynomial.

Thus the symmetric entire order-one gauge orbit is locally determining as well.  Combining this
elementary `[BRIDGE]` with the Euler-unit theorem gives the exact local classification:

```text
local compact-open real-analytic closure of the completed Euler-source orbit
  = local compact-open real-analytic closure of the arbitrary
    entire FE/Schwarz-real order-one realizer orbit
  = the whole fundamental germ space.
```

Therefore no continuous all-order local jet equation can separate the completed Euler source from
the arbitrary realizer class named in the research objective.  The separator must be a weighted
arithmetic-at-infinity condition, not merely an equation involving infinitely many Taylor
coefficients.

## Topological classification of the completed source image

Let `A_>1` be the Frechet space of coefficient streams `c=(c_n)_(n>=2)` with

```text
||c||_sigma = sum_(n>=2) |c_n| n^(-sigma) < infinity
```

for every `sigma>1`; a countable defining family is `sigma=1+1/k`.  Coordinate evaluation is
continuous on `A_>1`, and the Dirichlet--Laplace map

```text
L(c)(s)=sum_(n>=2)c_n n^(-s)
```

is continuous and injective from `A_>1` to `O(Re s>1)`.

Inside `A_>1`, the degree-one Euler locus `V_Euler` is cut out by the closed all-order system

```text
c_n=0                                             off prime powers,
c_(p^m)c_(p^n)=(log p)c_(p^(m+n))                 for all p,m,n>=1.
```

The equations are closed because every coordinate functional is continuous.  The existing exact
coefficient theorem identifies every point of `V_Euler` with a unique prime parameter field.  Hence

```text
Gamma_Euler={(c,L(c)):c in V_Euler}
```

is a closed source graph in `A_>1 x O(Re s>1)`.  Adding the fixed archimedean flux is an affine
translation and gives the completed prime--archimedean graph.  The von Mangoldt stream is its
distinguished point `a_p=1`.

The completeness theorems above give the opposite local statement after continuation to a
quartet-disjoint strip germ `D`:

```text
weighted arithmetic topology at infinity:
  the completed Euler source is a closed all-order ray-compatible graph;

compact-open topology on the regular germ at a selected zero:
  the FE--Schwarz Euler-unit orbit and the arbitrary symmetric order-one
  realizer orbit have the same full real-analytic closure O(D).
```

This is the exact source-image boundary.  The all-order compatibility not satisfied by arbitrary
realizers is the closed weighted coefficient-ray condition, but its local continued germ has no
continuous analytic trace capable of locating zeros.  An RH implication therefore requires a new
**pointed** invariant on the weighted graph that couples `c` to a pole/zero of its continuation and
is not continuous after forgetting `c`.

Equivalently, the unresolved map is not source recovery but incidence:

```text
(c in V_Euler, rho, continued regular germ at rho)
    -> a tail invariant whose FE--Schwarz self-dual locus forces Re rho=1/2.
```

The present theorem proves that such an invariant cannot factor through the compact-open regular
germ, even with all Taylor orders retained.

## Pointed zero-incidence consequence

Let `rho` lie in the open critical strip and choose `D` to be a small convex neighbourhood of
`rho`.  A finite modification

```text
zeta_a(s) = zeta(s) product_(p in P) (1-p^(-s))/(1-a_p p^(-s))
```

is multiplication by a holomorphic unit near `rho` when the parameters are near `1`.  Hence it
preserves a zero at `rho` and its multiplicity, while its logarithmic-flux regular germ changes by
`Psi_P`.

The theorem therefore classifies the local quotient positively:

> after the principal part/multiplicity is fixed, the regular completed-flux germ has no nonconstant
> continuous analytic invariant under all finite Euler-unit changes.

The surviving RH information cannot be a continuous analytic function of the local regular jet,
even at the actual zeta Euler point.  It must couple the selected divisor point to a weighted
all-prime tail topology that does not complete finite Euler changes to the whole local germ space.

## Attacks and boundaries

1. **The result does not prove RH.**  It removes a class of possible local compatibility equations.
2. **The principal part survives.**  Finite Euler units preserve multiplicity; the theorem concerns
   the regular flux germ after that principal part is removed.
3. **FE and Schwarz symmetry are included at germ level.**  The real-completeness theorem treats a
   quartet-disjoint fundamental germ and real Euler parameters.  It does not assert that the
   rational Euler-unit gauges are entire functions on all of `C`; they are holomorphic units on the
   critical strip neighbourhoods used by the pointed incidence problem.
4. **The right-half-plane condition is essential to this proof.**  It gives a sector on which the
   Lambert transform is bounded.  Every hypothetical right-half RH counterexample admits such a
   neighbourhood.
5. **No support limit is used.**  Cofinite completeness is proved by duality; no sequence of Euler
   cutoffs is promoted into a carrier.
6. **The arbitrary-realizer comparison is a bridge.**  Its Runge symmetrization is standard.  The
   provisional novelty claim concerns the actual Euler-unit Lambert/Mobius completeness and its
   FE--Schwarz carrier separation, not polynomial-gauge density.

## Parent and literature audit

The pure exponential predecessor is classical Fourier--Borel/Muntz completeness.  The present
family is a Lambert transform of the exponential system, and the dual Lambert transform is
invertible by ordinary Mobius inversion.  Sectorial zero uniqueness is classical Blaschke theory.
The FE strengthening additionally uses separated-carrier Runge approximation.

Exact searches for the kernel family `exp(-lambda s)/(1-exp(-lambda s))^2`, its generalized-monomial
form `x^lambda/(1-x^lambda)^2`, and the prime specialization did not locate this completeness
statement.  Adjacent parents include generalized Muntz--Szasz theorems, completeness of exponential
systems in holomorphic spaces, and Lambert-series inversion.

Absence of an exact search hit is not by itself a novelty verdict.  The parent comparison therefore
focused on whether the transference

```text
exponential uniqueness + invertible Lambert transform -> Euler-tangent completeness
```

is already a standard theorem in one of those parent theories or is regarded as an immediate
corollary.  The checked sources treat pure exponential systems, ordinary Muntz monomials, stability
under frequency perturbation, or Lambert-series identities separately.  They do not supply the
Euler-tangent kernel, the dual Lambert/Mobius completeness transfer, or the FE--Schwarz
separated-carrier strengthening.

The theorem therefore passes the preliminary parent and rediscovery gates as a **provisional**
candidate rather than a confirmed novelty.  Independent specialists may still identify an older
generalized-exponential theorem subsuming it; if so, it must be downgraded immediately.

Primary and authoritative parents checked include:

1. B. N. Khabibullin and E. G. Kudasheva, *Completeness of exponential systems in spaces of
   functions on a compact or domain and their area*, arXiv:2306.15899.
2. I. S. Galimov, *On the completeness of the exponential system in nonconvex domains*, Math.
   USSR-Sb. 27 (1975), 39--50, DOI `10.1070/SM1975v027n01ABEH002497`.
3. A. Poltoratski, *A problem on completeness of exponentials*, Ann. of Math. 178 (2013),
   983--1016, DOI `10.4007/annals.2013.178.3.4`.
4. Classical Fourier--Borel duality for analytic functionals and the half-plane Blaschke condition.
5. Classical Muntz--Szasz completeness and ordinary Lambert-series Mobius inversion.

## Scientific contribution if the novelty verdict survives

The theorem identifies a previously missing boundary at the **actual** Euler source:

```text
finite Euler-unit changes + FE + Schwarz
    generate an analytically determining local regular-jet orbit;

therefore every RH-bearing source constraint
    must be nonlocal in a weighted all-prime tail topology.
```

This is stronger than finite-jet openness, trivial-source completeness, and rational-gauge
divisor-blindness.  It says that the elementary symmetries do not leave even a continuous
real-analytic local invariant after the principal part is fixed.  The surviving object is forced to
be a pointed arithmetic-at-infinity incidence class rather than a local completed-flux equation.
