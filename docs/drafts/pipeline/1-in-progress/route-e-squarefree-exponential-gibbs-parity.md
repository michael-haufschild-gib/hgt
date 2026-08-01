# Route E squarefree exponential-Gibbs parity source

- **ID:** `ROUTE-E-GIBBS-PARITY-001`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / HOSTILE SOURCE AUDIT
- **Source:** `mobius-additive-frontier-research-ledger.md` · `OPEN-SOURCE-001`
- **Statement:** Möbius--Laplace cancellation is the parity Fourier coefficient of a positive
  squarefree exponential-Gibbs law; every conditional two-prime table is strictly Rayleigh, but
  three primes already destroy real stability, so any successful parity estimate must use the
  multiplicative cutoff boundary rather than generic negative-dependence machinery.

## Goal

For `x>0`, put

```text
Z(x)   = sum_(n>=1) mu(n)^2 exp(-nx),
nu_x(n)= mu(n)^2 exp(-nx)/Z(x),
eta(n) = mu(n) on the squarefree support.
```

Then

```text
Phi(x)=sum_(n>=1) mu(n) exp(-nx)=Z(x) E_(nu_x)[eta].       (G1)
```

Since `Z(x)` has order `x^(-1)`, the exact Route E source can be written as the all-prime parity
mixing law

```text
for every epsilon>0,
  |E_(nu_x)[eta]| <= C_epsilon x^(1/2-epsilon),  0<x<=1.  (G2)
```

Indeed `Z(x)<=sum_(n>=1)exp(-nx)<=x^(-1)` for `0<x<=1`, so `(G2)` gives
`|Phi(x)|<=C_epsilon x^(-1/2-epsilon)`, the every-strict-half growth law consumed by
`MobiusDiscreteLaplaceAllStrictHalfPowerDecay`, and hence RH.  Conversely, the classical
squarefree-density lower bound `Z(x)>=c x^(-1)` turns every-strict-half Möbius--Laplace growth
back into `(G2)`.  The signs of both powers are essential: Route E needs control of growth
`x^(-b)` with `b>1/2`, not decay of `Phi` to zero.  The claim is not admitted as proved. Its
purpose is to force a producer to act on a genuine positive source law while retaining the signed
parity observable.

## Gates

- [x] 0 → 1  in-progress: source-pure probability law, exact RH-bearing parity target, and first
  hostile mechanism fixed
- [ ] 1 → 2  fully-proven: prove `(G2)` without RH, zero locations, or an equivalent Mertens bound
- [ ] 2 → 3  formalized: only after dependency-closed paper proof
- [ ] 3 → 4  publication-ready: only after external priority audit and complete Lean certificate

## Exact positive source representation

For a finite prime set `P`, define the multiaffine partition polynomial

```text
F_(P,x)(z)=sum_(S subset P) exp(-x product(S)) product_(p in S) z_p,  (G3)
```

with `product(empty)=1`. All coefficients are positive. Evaluation at the all-minus prime
orientation is the finite Möbius partition sum:

```text
F_(P,x)(-1,...,-1)
  =sum_(S subset P) (-1)^#S exp(-x product(S)).            (G4)
```

Cofinal prime exhaustion converges absolutely to `Phi(x)`. Thus `(G3)` is an honest positive
carrier for the exact signed observable, not an analytic continuation or zero-selected model.

## Theorem A — conditional two-prime Rayleigh law `[PROVED HERE]`

Fix a squarefree spectator product `a>=1` and distinct primes `p,q`. The four conditional weights
are

```text
w00=exp(-ax),   w10=exp(-apx),
w01=exp(-aqx), w11=exp(-apqx).
```

For every `x>0`,

```text
w10 w01-w00 w11
 =exp(-a(p+q)x)-exp(-a(1+pq)x)>0,                         (G5)
```

because `1+pq-(p+q)=(p-1)(q-1)>0`. Hence every two-coordinate conditional table of `(G3)` is
strictly log-submodular/Rayleigh. This recovers the useful sign behind the renewal anti-TP2 law in
a genuinely positive probability table.

## Theorem A2 — global negative lattice law and its exact limit `[PROVED HERE]`

The pairwise sign extends to arbitrary Boolean lattice pairs.  For subsets `S,T` of a finite
prime set, write the products on `S intersect T`, `S \ T`, and `T \ S` as `c,a,b`.  Then

```text
product(S)=ca,  product(T)=cb,
product(S union T)=cab,  product(S intersect T)=c,
```

and `(a-1)(b-1)>=0` gives

```text
exp(-x product(S)) exp(-x product(T))
 >= exp(-x product(S union T)) exp(-x product(S intersect T)). (G5a)
```

Thus the complete finite Gibbs carrier is log-submodular, not merely pairwise Rayleigh.  This is a
real structural survivor, but it still cannot supply `(G2)` abstractly.  Indeed independent
Bernoulli laws are log-modular (equality in the lattice law), while for `m` sites with occupation
probability `theta_m=m^(-2)` their parity expectation is

```text
(1-2 theta_m)^m -> 1.                                    (G5b)
```

So neither log-submodularity nor negative lattice dependence plus growing dimension forces any
parity cancellation.  A valid use of `(G5a)` must also exploit the multiplicative physical-scale
boundary; generic negative-dependence theory remains excluded.

## Theorem B — three-prime real-stability obstruction `[PAPER-PROVED HERE]`

Let `1<p<q<r`. The three-variable polynomial `F_({p,q,r},x)` is not real stable for all
sufficiently large `x`.

For a real multiaffine polynomial, real stability implies nonnegativity of every Rayleigh
difference on every real specialization. Specializing `z_r=t`, the `(p,q)` Rayleigh difference is

```text
Delta_(p,q)(t)=A_x+B_x t+C_x t^2,                         (G6)

A_x=exp(-(p+q)x)-exp(-(1+pq)x)>0,
C_x=exp(-r(p+q)x)-exp(-r(1+pq)x)>0,
B_x=exp(-(p+qr)x)+exp(-(q+pr)x)
      -exp(-(1+pqr)x)-exp(-(r+pq)x).
```

Put `D=r+pq`. Since

```text
D < p+qr,  D < q+pr,  D < 1+pqr,
```

one has `exp(Dx) B_x -> -1`. Also

```text
exp((p+q)x) A_x -> 1,
exp(r(p+q)x) C_x -> 1.                                   (G7)
```

Finally,

```text
(p+q)(r+1)-2(r+pq)>0.                                    (G8)
```

Indeed the left side is increasing in `r`, and at `r=q` it is
`(q-p)(q-1)>0`. Equations `(G7)`--`(G8)` give

```text
B_x^2/(A_x C_x) -> +infinity.                             (G9)
```

For all sufficiently large `x`, therefore, `B_x<0` and `B_x^2>4A_xC_x`. The quadratic `(G6)`
has two positive real roots and is negative between them. This violates the Rayleigh-difference
criterion, proving the claim.

No numerical test enters this proof. The obstruction is uniform for every ordered triple
`1<p<q<r`.

## Theorem B2 — diagonal real-rootedness also fails `[PAPER-PROVED HERE]`

Collapsing all prime variables to one cardinality variable does not repair stability.  For a
finite prime set `P` of size `m`, put

```text
Q_(P,x)(z)=sum_(S subset P) exp(-x product(S)) z^(#S).      (G9a)
```

At `x=0`, `Q_(P,0)(z)=(1+z)^m`, while the first scale derivative is

```text
partial_x Q_(P,x)(z)|_(x=0)
 =-sum_(S subset P)product(S)z^(#S)
 =-product_(p in P)(1+pz).                                 (G9b)
```

Let `C_P=product_(p in P)(p-1)>0`, write `z=-1+x^(1/m)u`, and divide by `x`.  The finite Taylor
expansion gives, locally uniformly in `u`,

```text
x^(-1) Q_(P,x)(-1+x^(1/m)u)
 -> u^m-(-1)^m C_P.                                       (G9c)
```

Every zero of the limit is simple, and for `m>=3` at least one conjugate pair is nonreal.
Disjoint-circle Rouche around those roots therefore gives nonreal zeros of `Q_(P,x)` for every
sufficiently small positive `x`.  Thus the cardinality law is not Poisson-binomial and no
univariate real-rooted/ultra-log-concave parity theorem can prove `(G2)`.

The positive survivor is the exact microscopic root constellation `(G9c)`: the coalesced root
`z=-1` splits on the fractional scale `x^(1/m)`, with orientation and radius determined solely by
`m` and `product(p-1)`.  This is stronger than merely exhibiting one failed discriminant.

## Theorem C — exact dilation recursion and finite-section jet amplification `[PROVED HERE]`

Write

```text
A_(P)(x)=F_(P,x)(-1,...,-1).
```

If `p` is not in `P`, subset separation according to whether `p` is occupied gives the exact
scale recursion

```text
A_(P union {p})(x)=A_P(x)-A_P(px).                         (G10)
```

For every integer `m>=0`, termwise differentiation of the finite exponential polynomial gives

```text
A_P^(m)(0)=(-1)^m product_(p in P)(1-p^m).                 (G11)
```

Indeed the subset sum in the derivative is
`(-1)^m sum_(S subset P)(-1)^#S product_(p in S)p^m`, which is the elementary product expansion
in `(G11)`.  In particular, when `P` is nonempty, `A_P(0)=0` and

```text
A_P'(0)=-product_(p in P)(1-p) != 0.
```

Consequently

```text
lim_(x downarrow 0) A_(P union {p})(x)/A_P(x)=1-p.         (G12)
```

Thus adjoining `p` amplifies the first nonzero finite-section jet by the factor `p-1`; at order
`m` the multiplier is `|p^m-1|`.  No fixed-prime induction, uniform normal-family argument at
`x=0`, or primewise contraction can prove `(G2)`.  The required cancellation is necessarily a
noncommuting cofinal limit in which aperture and physical scale move together.

## Theorem D — logarithmically oversized aperture is source-exact `[PROVED HERE]`

Let `P_Y` contain every prime at most the integer `Y`, and put `A_Y=A_(P_Y)`.  Absolute cofinal
convergence has the explicit remainder

```text
|Phi(x)-A_Y(x)|
 <= sum_(n>Y) exp(-nx)
 = exp(-(Y+1)x)/(1-exp(-x)).                               (G13)
```

The reason is arithmetic, not analytic: every omitted squarefree integer has a prime factor
larger than `Y`, hence is itself larger than `Y`.  For `0<x<=1`,
`1-exp(-x)>=x/2`.  Therefore any moving aperture satisfying

```text
(Y(x)+1)x >= (1/2) log(1/x)                               (G14)
```

obeys

```text
|Phi(x)-A_(Y(x))(x)| <= 2 x^(-1/2).                        (G15)
```

It follows that the finite, moving all-minus estimate

```text
for every epsilon>0,
  |A_(Y(x))(x)| <= C_epsilon x^(-1/2-epsilon)              (G16)
```

is equivalent to strict-half Möbius--Laplace decay for any aperture schedule satisfying `(G14)`.
Unlike matching additive apertures, this analytic aperture must overshoot the physical resolution
`x^(-1)` by a logarithm.  Under the prime number theorem this logarithmic overshoot is sharp up to
`log log(1/x)` for an *absolute* truncation argument, because the omitted absolute mass already
contains `sum_(p>Y)exp(-px)`.

## Theorem E — one-large-prime boundary reduction `[PROVED HERE]`

Fix an integer `z>=2`.  Partition squarefree integers by the number of prime factors larger than
`z`.  Unique factorization gives

```text
Phi(x)=A_z(x)-sum_(p>z, p prime) A_z(px)+R_(>=2,z)(x),     (G17)
```

where `R_(>=2,z)` is the signed contribution of squarefree integers having at least two prime
factors larger than `z`.  Such an integer is larger than `z^2`, so

```text
|R_(>=2,z)(x)|
 <= exp(-(floor(z^2)+1)x)/(1-exp(-x)).                     (G18)
```

Choose `z=z(x)` with

```text
(floor(z(x)^2)+1)x >= (1/2)log(1/x).                       (G19)
```

Then `R_(>=2,z)(x)=O(x^(-1/2))`.  Hence the exact open source is reduced, with an already adequate
absolute error, to the genuinely all-prime first-boundary law

```text
|A_z(x)-sum_(p>z)A_z(px)|
  <= C_epsilon x^(-1/2-epsilon).                           (G20)
```

This is not the killed one-prime local tent.  The summand `A_z(px)` retains every small-prime
parity interaction and the outer sum ranges over the full moving prime tail.  Nor is `(G20)`
claimed proved: it is the sharpened source target exposed by the exact two-large-prime remainder.

### Theorem E2 — exact prime-renewal defect and unique transition `[PROVED HERE]`

The zero/one comparison has a second exact factorization.  Define, for `t>0`,

```text
K_z(t)=exp(-t)-sum_(p>z)exp(-pt)
      =exp(-t)(1-R_z(t)),                                 (G20a)

R_z(t)=sum_(p>z)exp(-(p-1)t).
```

Absolute convergence permits swapping the finite `z`-smooth squarefree sum with the prime tail:

```text
A_z(x)-sum_(p>z)A_z(px)
 =sum_(m: p|m => p<=z) mu(m) K_z(mx).                    (G20b)
```

The kernel has exactly one transition.  The function `R_z` is continuous and strictly decreasing
on `(0,infinity)`.  It tends to zero at infinity by comparison with the full geometric tail.  It
tends to infinity at zero: for every `J`, choose `J` primes beyond `z`, then their partial sum tends
to `J`.  Therefore there is a unique `tau_z>0` such that

```text
R_z(tau_z)=1,
K_z(t)<0 for 0<t<tau_z,
K_z(t)>0 for t>tau_z.                                    (G20c)
```

This identifies the transition, not the missing estimate.  Equation `(G20b)` says the hard source
is a Möbius sample of a one-sign-change renewal defect.  Taking absolute values still discards
exactly the required correlation between the `z`-smooth Möbius parity and the entire negative and
positive parts of the kernel.  The finite version of `(G20a)`--`(G20b)` is formalized
unconditionally.  Lean also packages the literal moving-aperture zero/one estimate as
`MobiusLargePrimeBoundaryAllStrictHalf` and proves it implies every strict-half
Möbius--Laplace bound and RH after absorbing `(G18)`.  The infinite transition proof is
dependency-closed on paper.

### Theorem E3 — critical aperture is transition-self-dual but not transition-local
`[PAPER-PROVED HERE]`

The prime number theorem plus partial summation determines the transition scale.  Uniformly for
`y=log z+O(log log z)`,

```text
R_z(y/z)
 =(1+o(1)) z exp(-y)/(y log z).                           (G20d)
```

Bracketing first with `y=log z-3 log log z` and
`y=log z-log log z`, then solving `R_z(y/z)=1`, gives

```text
z tau_z=log z-2 log log z+o(1).                           (G20e)
```

Hence any minimal critical schedule satisfying

```text
z^2 x / log z -> 1
```

has

```text
(tau_z/x)/z -> 1.                                        (G20f)
```

So the kernel changes sign at the same multiplicative scale as the small/large-prime aperture.
That self-duality is genuine.  It does **not** mean the required cancellation is local to a narrow
window around `m=z`.  On the same schedule, `zx->0`, and a second PNT partial-summation estimate
gives

```text
K_z(x)=-(1+o(1))/(x log(1/x)).                            (G20g)
```

Thus the single `m=1` summand in `(G20b)` already exceeds
`x^(-1/2-epsilon)` for every fixed `epsilon<1/2`.  A proof must cancel a macroscopic negative bulk
against many signed `z`-smooth terms before it can exploit the transition.  Any conjecture claiming
only transition-window cancellation is false as a source mechanism.

## Competing normalization: additive-circle lattice evaluation

Put

```text
F_x(t)=sum_(n>=1) mu(n) exp(-nx) exp(int),   t in R/(2 pi Z). (G21)
```

Normalized Haar Parseval gives the exact positive energy law

```text
||F_x||_2^2=sum_(n>=1)mu(n)^2 exp(-2nx)=Z(2x),             (G22)
F_x(0)=Phi(x).                                               (G23)
```

Consequently the Möbius-specific lattice-evaluation estimate

```text
for every epsilon>0,
  |F_x(0)| <= C_epsilon x^(-epsilon) ||F_x||_2,  0<x<=1,    (G24)
```

implies the exact every-strict-half source, because
`Z(2x)<=sum_(n>=1)exp(-2nx)<=1/(2x)`.  Conversely the elementary positive density of squarefree
integers gives `Z(2x)>=c/x`, so the source implies `(G24)` after changing epsilon.  Thus `(G24)` is
another source-exact normalization, not a weaker mean-square surrogate.

The normalization identifies the hard statement precisely: the additive lattice point `t=0`
may exceed the root-mean-square size only by a subpower.  This is false for coefficient-blind
Hardy-space estimates.  The flat Littlewood polynomial

```text
H_N(t)=sum_(1<=n<=N) exp(int)
```

has `H_N(0)=N` and `||H_N||_2=sqrt(N)`.  Any proof of `(G24)` must therefore consume the Möbius
divisor law rather than only coefficient bounds, analyticity, or Parseval.

## Exact signed dilation Gram law

For positive integers `k,l`, define the Lambert dilation carrier

```text
G_(k,x)(t)=F_(kx)(kt).
```

Then the exact Lambert identity holds pointwise and in `L2`:

```text
sum_(k>=1)G_(k,x)(t)=exp(-x)exp(it).                         (G25)
```

Let `d=gcd(k,l)`, `a=k/d`, `b=l/d`, and `L=lcm(k,l)=dab`. Character orthogonality and
`kn=lm iff (n,m)=(br,ar)` give

```text
<G_(k,x),G_(l,x)>
 =sum_(r>=1)mu(br)mu(ar)exp(-2Lrx).                         (G26)
```

Since `gcd(a,b)=1`, `(G26)` is zero if `a` or `b` is not squarefree.  Otherwise it is the signed
positive partition

```text
mu(ab) sum_((r,ab)=1) mu(r)^2 exp(-2Lrx).                  (G27)
```

This exposes exactly where a positive Gram argument can retain Möbius signs: they occur in the
off-diagonal orientation `mu(ab)`, before absolute values are taken.

For each fixed pair `(k,l)`, the elementary squarefree-density law yields

```text
x <G_(k,x),G_(l,x)>
 -> [mu(ab)/(2L)] [6/pi^2] product_(p|ab) p/(p+1),          (G28)
```

with value zero in the nonsquarefree case.  Since
`x||G_(k,x)||_2^2 -> 3/(pi^2 k)`, the limiting normalized correlation is

```text
mu(ab) product_(p|ab) sqrt(p)/(p+1).                        (G29)
```

On any fixed prime-exponent box this is a tensor product of local tridiagonal kernels: diagonal
entry `1`, adjacent-exponent entry `-sqrt(p)/(p+1)`, and zero beyond distance one.  Against the
Lambert coefficient ray `p^(-j/2)`, the local Rayleigh quotient is exactly

```text
(p-1)/(p+1).                                                (G30)
```

Hence prime-local fixed-index Gram tensorization compresses only by
`product_(p<=y)(p-1)/(p+1)`, a logarithmic-square factor, not a power of the physical scale.
The fixed-index limit therefore cannot prove `(G24)`.  Any viable signed-Gram theorem must be
nonuniform in the indices and extract its missing square root from the moving boundary
`lcm(k,l)x` of order one.

There is an exact row resummation which makes the remaining obstruction explicit.  Use the
carriers at half scale in `(G26)` and pair their first row with the positive Hardy evaluation
kernel.  Since every monomial has the divisor decomposition
`E_q=sum_(d>=1)G_(qd,x/2)`, the evaluation kernel has Gram coordinates `tau(k)`, where `tau` is
the divisor-counting function.  Absolute regrouping gives

```text
Phi(x)=sum_(k>=1) mu(k)tau(k)
          sum_((r,k)=1)mu(r)^2 exp(-krx).                  (G31)
```

Coefficientwise, a squarefree `n` contributes
`sum_(k|n)mu(k)tau(k)=product_(p|n)(1-2)=mu(n)`; a nonsquarefree `n` contributes zero because it
cannot split into coprime squarefree factors.  Thus `(G31)` is exact and not a heuristic Euler
model.

The outer orientation has Dirichlet series

```text
sum_(k>=1)mu(k)tau(k)k^(-s)
 =product_p(1-2p^(-s))
 =zeta(s)^(-2) H(s),                                      (G32)

H(s)=product_p (1-2p^(-s))/(1-p^(-s))^2.
```

The Euler product for `H` is absolutely convergent for `Re(s)>1/2`, because every local linear
term cancels.  This does not prove a half-power estimate: `zeta(s)^(-2)` has double poles at zeta
zeros.  In coefficient language, `mu(k)tau(k)` is the Dirichlet convolution of `mu*mu` with the
benign prime-power correction having local coefficients `h(p^j)=1-j`.  The fixed-index Gram row
therefore contains exactly the double reciprocal-zeta source already exposed by
`OPEN-SOURCE-001`; it is not an independent way around it.

The complete dilation family can in fact be diagonalized exactly, including the moving boundary.
Put

```text
E_(m,x)(t)=exp(-mx)exp(imt).
```

Then

```text
G_(k,x)=sum_(n>=1)mu(n)E_(kn,x),
E_(k,x)=sum_(d>=1)G_(kd,x),                               (G32a)
```

where the second identity is Möbius inversion and both series are absolutely convergent for
`x>0`.  Hence, for every finitely supported coefficient vector `c`, circle orthogonality gives

```text
||sum_k c_k G_(k,x)||_2^2
 =sum_(m>=1)exp(-2mx)|sum_(k|m)c_k mu(m/k)|^2.            (G32b)
```

Moreover, the closed span of the proper dilates `G_(k,x)`, `k>=2`, is exactly the closed span of
the pure modes `E_(m,x)`, `m>=2`: one inclusion is immediate from the first identity in `(G32a)`,
and the reverse inclusion follows from the second.  Consequently the orthogonal residual of
`G_(1,x)` after projection onto all proper dilates is exactly `E_(1,x)`, with norm

```text
dist(G_(1,x), closure(span{G_(k,x):k>=2}))=exp(-x).        (G32c)
```

Thus no hidden positive Gram gap remains at `lcm(k,l)x` of order one.  The full boundary geometry
is the weighted divisor--Möbius incidence norm `(G32b)`.  Any estimate strong enough to imply
`(G24)` must prove cancellation in those incidence coefficients; calling that estimate a spectral
gap does not provide an independent source.

## Hostile audit

1. **Strongly-Rayleigh concentration is unavailable.** `(G5)` is only the two-coordinate shadow.
   Theorem B gives an exact three-coordinate failure of the real-stability hypothesis needed by
   strongly-Rayleigh and stability-preserving concentration theorems.
1a. **Global log-submodularity still does not mix parity.** Theorem A2 upgrades `(G5)` to the full
    negative lattice inequality, but the sparse product family `(G5b)` has parity tending to one.
    Any theorem using `(G5a)` must add an integer-specific moving-boundary input.
2. **Pairwise negative dependence cannot yield a power by itself.** Independent small-prime
   divisibility heuristics produce parity decay of logarithmic size; the missing square-root law is
   created at the moving multiplicative cutoff, where prime occupations cease to be independent.
3. **Fixed safe Dirichlet Gibbs law is not enough.** At weight `mu(n)^2/n^2`, prime occupations
   factor independently, but the critical observable localizes in the rare tail `n` of order
   `sqrt(k)`; absolute tail mass gives only the known Báez--Duarte `k^(-1/2)` floor.
4. **No probability-language substitution.** `(G2)` is exactly the Möbius--Laplace source after
   division by `Z(x)`; proving it is RH-strength. The positive carrier prevents sign smuggling but
   does not weaken the theorem.
5. **Finite/local stability is not closure.** Theorem B kills one proposed producer only. It does
   not close Route E and cannot be cited as permission to retire `OPEN-SOURCE-001`.
5a. **Diagonalization does not restore stability.** Theorem B2 kills the weaker hope that only the
    distribution of the prime count is real-rooted/Poisson-binomial.  Its nonreal roots arise
    uniformly at the small-`x` coalescence boundary, not from a special finite numerical example.
6. **Primewise contraction has the wrong sign and scale.** `(G11)`--`(G12)` show arbitrarily large
   amplification in every fixed finite-section jet.  Any valid square function must be
   boundary-renormalized before taking absolute values.
7. **Matching aperture is not Laplace aperture.** Coefficient stabilization at resolution
   `x^(-1)` leaves an absolute tail far above the critical scale.  `(G14)` identifies the first
   source-exact aperture available without signed tail cancellation.
8. **The one-large-prime formula is a reduction, not a bound.** Estimating the prime sum in `(G20)`
   term by term loses the parity cancellation in `A_z` and returns only PNT-scale information.
8a. **One kernel sign change is geometry, not cancellation.** `(G20c)` identifies the unique
    transition, but `(G20g)` shows that even the `m=1` negative-bulk term is supercritical.  A norm
    bound or a transition-window argument forgets the global Möbius cancellation required by
    `(G20b)`.
9. **Parseval is normalization, not cancellation.** `(G22)` fixes the RMS scale, but the flat
   polynomial countermodel shows that generic point evaluation loses another square root.
10. **Fixed-index dilation Gram asymptotics are too weak.** `(G26)`--`(G30)` retain the correct
    signs, yet their primewise tensor product produces only logarithmic-square compression.  Taking
    the limit at fixed dilation indices discards the physical boundary where a power could arise.
11. **Positive-norm dilation repair remains excluded.** The existing critical prime
    `p^(-1/2)` nonsummability theorem kills absolute contraction.  The survivor in `(G26)` is
    specifically a signed off-diagonal boundary law; replacing it by entrywise norms returns that
    certified wall.
12. **Gram-row Euler factorization is not a source.** `(G31)` is exact, but `(G32)` contains
    `zeta(s)^(-2)`.  Absolute convergence of the correction `H` does not control its reciprocal-zeta
    factor; asserting otherwise simply assumes the zero-free half-plane the route is meant to
    prove.
13. **Full Gram diagonalization removes the proposed boundary mystery.** `(G32a)`--`(G32c)` retain
    every dilation and every physical-scale entry, yet reduce the Gram form exactly to weighted
    divisor incidence.  The only one-dimensional residual is the trivial first Fourier mode.
    Therefore an abstract boundary spectral gap cannot be the missing source; it must already
    encode Möbius cancellation in `(G32b)`.

## Strengthened surviving conjecture

`[CONJECTURE: GIBBS-BOUNDARY-MIXING]` Prove `(G20)`, hence `(G2)`, from a boundary-sensitive
multiscale inequality for `(G3)` which:

1. retains the all-minus parity observable before taking norms;
2. couples prime blocks whose products straddle the physical scale `1/x`;
3. gains one square root from the moving cutoff, not merely logarithmic small-prime decorrelation;
4. is stable under cofinal prime exhaustion; and
5. fails for phase-twisted or Beurling fake sources with known off-line zeros.

The conjectured inequality must compare the zero-large-prime sector `A_z(x)` with the entire
one-large-prime sector `sum_(p>z)A_z(px)` *before* either is normed.  A bound on the two sectors
separately is disallowed: each sector can be much larger than the required square-root remainder.
Equivalently, using `(G20b)`, it must prove global cancellation of the `z`-smooth Möbius signs
against both sides of the single-transition kernel `K_z(mx)` without replacing either factor by
its absolute value.  Restriction to a window around `m=tau_z/x` is disallowed by `(G20g)`.

Generic strong-Rayleigh theory, pairwise covariance, fixed-prime induction, positive diagonal
energy, and independent-prime approximation are excluded by the hostile audit. A proof must use a
genuinely integer-specific boundary interaction.

`[CONJECTURE: LATTICE-EVALUATION-DELOCALIZATION]` Prove `(G24)` by combining the exact divisor
collapse `(G25)` with the signed Gram kernel `(G26)`, while retaining entries with
`lcm(k,l)x` of order one.  Equivalently, prove a boundary-uniform subpower norm for evaluation at
the distinguished additive lattice point on the one-dimensional Möbius divisor orbit.  The
inequality must fail for the flat polynomial and for Beurling systems with off-line zeta zeros.

`[REJECTED: DILATION-GRAM-BOUNDARY-GAP]` The exact all-scale diagonalization
`(G32a)`--`(G32c)` shows that this conjecture did not name an independent mechanism.  Its claimed
boundary gain is precisely a bound for the divisor--Möbius incidence coefficients in `(G32b)`;
the sole orthogonal residual after all proper dilates is the elementary mode `E_(1,x)`.  The
positive survivor is the exact diagonalization itself.  `LATTICE-EVALUATION-DELOCALIZATION`
remains a valid source normalization, but requires a new integer-specific cancellation input.

### Bold surviving producer: multitype boundary transport

Let `beta_z(n)` be the coefficient of `exp(-nx)` in the combined zero-plus-one-large-prime
boundary.  Thus `beta_z(n)` is in `{-1,0,1}`.  At the minimal aperture take `T=z^2`; the absolute
tail beyond `T` is already `O(x^(-1/2))` by the same geometric estimate as `(G18)`.  Split the
remaining nonzero atoms into `P={n<=T:beta_z(n)=1}` and `N={n<=T:beta_z(n)=-1}`.

For a partial opposite-sign matching `M` between `P` and `N`, define its damped transport defect by

```text
D_x(M)=sum_(unmatched n) exp(-nx)
       +x sum_((m,n) in M) |m-n| exp(-min(m,n)x).          (G39)
```

The elementary mean-value estimate

```text
|exp(-mx)-exp(-nx)|
 <= x|m-n|exp(-min(m,n)x)                                 (G40)
```

immediately gives

```text
|sum_(n<=T) beta_z(n)exp(-nx)| <= D_x(M).                 (G41)
```

`[CONJECTURE: MULTITYPE-BOUNDARY-TRANSPORT]` For every `epsilon>0`, at a critical aperture there is
such a matching with `D_x(M)<=C_epsilon x^(-1/2-epsilon)`, generated from two local edge types.

1. A one-large-prime atom `n=ap`, `p>z`, may be paired across sectors with a zero-large-prime atom

```text
m=a q_1 q_2 q_3 q_4,
```

   where the `q_i<=z` are distinct primes and avoid `a`.  Removing one large prime and adding four
   small primes toggles five prime coordinates, hence flips Möbius sign.
2. Residual atoms in the same sector may be paired by replacing one small prime `q` with two
   distinct small primes `r,s`, all avoiding the spectator.  This toggles three prime coordinates,
   again flips sign, and is required because cross-sector atom counts are not balanced.

The union of both edge families must be injective and obey the aggregate cost `(G39)`.  Equations
`(G18)` and `(G41)` then give `(G20)`, and the formal consumer gives RH.

This is stronger than the desired cancellation but is not a renaming of it: it requires an
integer-local, bounded-congestion coupling with explicit parity-flipping factor replacements.
It also passes two immediate falsification gates.

1. Replacing the large prime by only two small primes cannot work even on the spectator slice
   `a=1`: there are only `O(z^2/log^2 z)` products `qr` with `q,r<=z`, versus
   `asymp z^2/log z` primes through `z^2`.  Even if those products are assigned to the smallest
   available large primes, the unmatched primes begin at scale `z^2/log z`, which is comparable
   to `1/x`; PNT then leaves damped mass `asymp 1/(x log(1/x))`, still supercritical.
2. Four-prime products pass the cardinality gate, but prime-counting alone does not prove the
   conjecture.  One still needs short-interval supply after excluding prime factors of every
   spectator, an injective Hall-type assignment, and the global damped displacement bound.  These
   are the hard problems; none is claimed here.
3. Four-prime cross-sector edges alone fail: at the `u=2` smoothness boundary, zero-large and
   one-large sectors have different densities.  Same-sector residual matching is mandatory, which
   is why the second `one-small <-> two-small` edge type is part of the conjecture rather than an
   optional repair.

There is also an exact anti-theatre warning.  Since two distinct primes greater than `z` have
product greater than `T=z^2`, every squarefree `n<=T` lies in the zero-or-one boundary and

```text
beta_z(n)=mu(n)  for every n<=T.                           (G42)
```

Consequently the unmatched mass of *any* partial matching is at least the absolute signed Gibbs
mass it is meant to bound.  Merely asserting a low-defect matching, without deriving it from the
factor-replacement incidence structure, is a strengthening of the source rather than an
explanation of it.

#### Theorem F — symmetric fractional boundary flow `[PROVED HERE]`

Injectivity is stronger than needed.  Let `V={n<=T:beta_z(n)!=0}`, put
`sigma(n)=beta_z(n)` and `w_x(n)=exp(-nx)`, and let `c(m,n)>=0` be a finite conductance satisfying

```text
c(m,n)=c(n,m),
c(m,n)>0  =>  sigma(m)=-sigma(n),
q(n):=sum_m c(n,m) <= w_x(n).                              (G43)
```

Symmetry and parity reversal give exact cancellation after swapping the two finite sums:

```text
sum_n sigma(n)q(n)
 = (1/2)sum_(m,n)(sigma(m)+sigma(n))c(m,n)=0.
```

Therefore

```text
|sum_(n in V)sigma(n)w_x(n)|
 <= sum_(n in V)(w_x(n)-q(n)).                             (G44)
```

This removes the global injective-Hall requirement while preserving the literal source.  It does
not permit arbitrary flow: `c` must be constructed on the two explicit factor-replacement edge
families above, independently of the value of the signed sum.

There is a canonical positive specialization.  Write `m~n` for adjacency in the undirected
replacement graph, let `d(n)` be its simple degree, and for non-isolated vertices set

```text
a_x(n)=w_x(n)/d(n),
c_x(m,n)=1_(m~n) min(a_x(m),a_x(n)).                       (G45)
```

Then `(G43)` is automatic.  Pairing the two directed contributions of each undirected edge gives
the exact capacity-defect identity

```text
sum_n(w_x(n)-q_x(n))
 = sum_(n isolated)w_x(n)
   +sum_({m,n} edge)|a_x(m)-a_x(n)|.                       (G46)
```

`[CONJECTURE: LOCAL-FRACTIONAL-BOUNDARY-FLOW]` For every `epsilon>0`, at a critical aperture the
two replacement edge families can be pruned or positively reweighted, using only their local
factor data, so that the right side of `(G44)` is
`O_epsilon(x^(-1/2-epsilon))`.  For the canonical flow `(G45)`, it is enough to prove the same
bound for `(G46)`.

This is a strictly more concrete producer than an existential matching: `(G46)` is a positive,
unsigned incidence-regularity estimate with no cancellation left inside it.  It also exposes its
own likely failure modes.  Cross-sector prime-to-four-prime degrees have different raw densities,
so the unweighted graph need not have small normalized-degree variation; same-sector edges or
nonuniform conductances must absorb that density mismatch.  Vertices in the small smooth core may
be isolated, but their entire mass is admissible only while it is `O(z^{1+o(1)})` on the critical
schedule.  Neither `(G44)` nor `(G46)` may be justified by first assuming a Mertens bound.

The conjecture is deliberately incompatible with Beurling fake-prime systems lacking dense
integer four-almost-prime replacements.  Unlike positive Gram, generic negative dependence, and
`U^2` proposals, it names a specific arithmetic operation which would create the missing sign
cancellation.

#### Transport literature collision audit

Existing short-interval almost-prime theorems supply part of the local-density input, not the
transport.  Teräväinen proves that almost all intervals of length `log^(1+epsilon) X` contain an
integer with exactly three prime factors and gives general fixed-`k` variants whose interval length
approaches `log X` as `k` grows
([paper](https://arxiv.org/abs/1510.06005)).  Matomäki proves almost-all supply of integers with at
most two prime factors in intervals `h(X)log X`, for arbitrary `h(X)->infinity`; that `P_2` theorem
explicitly avoids the exact-factor-count parity barrier
([paper](https://arxiv.org/abs/2012.11565)).  Matomäki--Teräväinen obtain exact two-prime products
in almost all intervals of length `log^2.1 X` using a new Type II estimate, while their all-interval
exact-three-prime result has length `sqrt(X)log^1.55 X`
([paper](https://arxiv.org/abs/2207.05038)).

None of these results supplies the conjecture as stated.  They do not simultaneously enforce four
distinct factors below the moving aperture, exclude every spectator prime, choose opposite-sign
partners injectively, and bound one global damped Hall displacement.  The almost-all theorems are
nevertheless relevant: `(G39)` is an aggregate cost, so a controlled exceptional set could be
absorbed.  The concrete next lemma is therefore a spectator-uniform weighted incidence estimate,
not a new pointwise short-interval theorem.

## Rejected producer: all-orders additive restriction

For `N>=1`, put

```text
S_N(t)=sum_(1<=n<=N)mu(n)exp(int),
```

with normalized Haar norms on the additive circle.  Consider the hierarchy

```text
[CONJECTURE: MOBIUS-LAMBDA-2M-SUBPOWER]
for every integer m>=1 and delta>0, there is C_(m,delta) such that
  ||S_N||_(2m) <= C_(m,delta) N^delta ||S_N||_2            (G33)
for every N>=1.                                             
```

`[REJECTED AS AN INDEPENDENT PRODUCER: COLLIDES WITH MOBIUS-GOWERS-NOGO-001]`.

The hierarchy would be an exact source producer.  The analytic-polynomial Nikolskii inequality gives

```text
|S_N(0)| <= C_m N^(1/(2m)) ||S_N||_(2m).                  (G34)
```

Since `||S_N||_2^2=sum_(n<=N)mu(n)^2<=N`, `(G33)`--`(G34)` imply

```text
|M(N)| <= C_(m,delta) N^(1/2+delta+1/(2m)).                (G35)
```

Given any `epsilon>0`, choose a fixed `m` with `1/(2m)<epsilon/2` and then a fixed
`delta<epsilon/2`.  This yields `M(N)=O_epsilon(N^(1/2+epsilon))`, hence the exact Laplace source
and RH.  Equivalently one may apply the weighted version to `(G21)` after a logarithmically
oversized absolute tail truncation.

Expansion of `(G33)` shows what must be proved:

```text
||S_N||_(2m)^(2m)
 =sum_(n_1+...+n_m=r_1+...+r_m)
    product_i mu(n_i)mu(r_i).                              (G36)
```

The diagonal permutations have order `m! N^m`, exactly compatible with `(G33)`.  The apparently
new required input would be that all off-diagonal additive resonances contribute only
`N^(m+o(1))`, with their Möbius signs retained.  At `m=2`, this is the near-random bound for the
averaged squared two-point correlation

```text
sum_h |sum_n mu(n)mu(n+h)|^2 <= N^(2+o(1)),                (G37)
```

up to the exact endpoint weights from the additive parallelogram.  But the change of variables
`m=n+h_1`, with the correlation shift `h=h_2`, identifies the expanded summand as

```text
mu(n)mu(n+h_1)mu(n+h_2)mu(n+h_1+h_2).
```

Consequently `(G37)` is exactly, up to boundary normalization,

```text
N^3 ||mu||_(U^2[N])^4 <= N^(2+o(1)),                      (G38)
```

or `||mu||_(U^2[N])<=N^(-1/4+o(1))`.  This is the polynomial-strength `U2` input already isolated
and frozen as `MOBIUS-GOWERS-NOGO-001`.  The higher moment hierarchy does not evade that wall; it
contains it at its first nontrivial level.

Additional hostile audit: a flat coefficient sequence has moment scale `N^(1-1/(2m))`, so `(G33)`
is false coefficient-blindly.  Known fixed-order Gowers/nilsequence decay supplies logarithmic
suppression of a cubic absolute scale, not `(G38)`.  Logarithmically averaged Chowla does not imply
the unweighted square correlation `(G37)`.  Thus `(G33)` remains a correct implication to RH, but
it is not new source infrastructure and is removed from the surviving conjecture set.

External collision audit agrees with that separation.  Matomaki--Radziwill--Tao's
[averaged Chowla theorem](https://arxiv.org/abs/1503.05121) proves, for fixed order, an `L1` average
of the absolute shifted correlations of size `o(H^m N)`; even at `m=2`, the trivial conversion from
that `L1` statement to the square in `(G37)` loses one full factor `N`.  The later
[higher-uniformity theorem](https://annals.math.princeton.edu/2023/197-2/p03) proves qualitative
average short-interval Gowers decay and polynomial-phase cancellation, not an unweighted
near-diagonal `N^(m+o(1))` moment.  Green--Tao's
[nilsequence orthogonality](https://annals.math.princeton.edu/2012/175-2/p03) gives arbitrary
logarithmic savings against each fixed nilsequence, again not `(G36)`.  No primary source located
in this audit states `(G37)` or the hierarchy `(G33)`.

## No-go status of the stability submechanism

- **Exact killing theorem/mechanism:** Theorem B; a three-prime Rayleigh difference has a negative
  interval for every sufficiently large physical scale.
- **Strongest positive survivor:** Theorem A; every conditional two-prime table is strictly
  Rayleigh, uniformly in the spectator product and scale.  The complete additive-dilation family
  also has the exact divisor-incidence diagonalization `(G32b)` and pure-tone inversion `(G32c)`.
- **New insight:** local negative dependence is real but stops at order two. Required source lives
  in scale-dependent higher-prime boundary interaction, not a global stable polynomial.
- **Status:** dependency-closed paper proofs for all stated reductions and no-go survivors. Lean
  formalization now covers Gibbs normalization/source consumption, finite aperture and sector
  decomposition, finite additive Parseval plus its hostile flat model, two-prime Rayleigh,
  cardinality coalescence/tangent identities, finite divisor-incidence diagonalization, Hall
  selection with damped displacement, and symmetric fractional-flow capacity consumption.
  The all-prime estimate `(G20)` remains unproved, so Route E remains open.

Lean modules:

- `MobiusExponentialGibbsBoundary.lean`
- `MobiusAdditiveCircleBoundary.lean`
- `MobiusGibbsCardinalityBoundary.lean`
- `MobiusAdditiveDilationDiagonalization.lean`
- `MobiusPrimeRenewalDefectBoundary.lean`
- `MobiusBoundaryOppositeSignTransport.lean`

## Log

- 2026-08-01 — created after exact `OPEN-SOURCE-001` re-audit; derived positive Gibbs parity form,
  proved conditional two-prime Rayleigh law, and paper-proved uniform three-prime real-stability
  obstruction without computation.
- 2026-08-01 — hostile normalization audit checked `(G2)` directly against Lean's
  `MobiusDiscreteLaplaceAllStrictHalfPowerDecay`: `Phi` may grow as `x^(-1/2-epsilon)`, so division
  by `Z(x)` gives the exact parity exponent `1/2-epsilon`.  A transient sign-error draft was
  rejected before formalization.
- 2026-08-01 — proved exact dilation recursion and all Taylor jets, showing finite sections amplify
  rather than contract; proved logarithmically oversized aperture estimate; and reduced the
  all-prime source to the zero/one-large-prime boundary comparison with an unconditional
  `O(x^(-1/2))` two-large-prime remainder.
- 2026-08-01 — derived additive-circle source normalization and exact signed Lambert-dilation Gram
  law.  Hostile limit audit shows fixed-index prime tensorization gains only a logarithmic square;
  surviving Gram conjecture must act nonuniformly at `lcm(k,l)x` of order one.
- 2026-08-01 — resummed the first signed Gram row exactly as `(G31)` and factored its outer Euler
  orientation as `zeta^(-2)H`.  This identifies the fixed-index route with the existing double
  reciprocal-zeta source and prevents a benign-Euler-factor circularity.
- 2026-08-01 — proved the diagonal cardinality polynomial also loses real-rootedness: its
  `m`-fold root at `-1` splits at scale `x^(1/m)` toward the nonreal root constellation `(G9c)` for
  every `m>=3`.
- 2026-08-01 — isolated the all-orders additive restriction hierarchy `(G33)`.  Nikolskii gives a
  dependency-closed implication to the Mertens strict-half bound; hostile reparameterization then
  identified its first nontrivial case `(G37)` with the frozen polynomial `U2` wall `(G38)`, so the
  hierarchy was rejected as an independent producer before Lean formalization.
- 2026-08-01 — primary-literature collision audit separated `(G37)` from averaged Chowla `L1`,
  qualitative average short-interval Gowers uniformity, and logarithmic nilsequence orthogonality;
  no existing near-diagonal square-moment theorem was located.
- 2026-08-01 — diagonalized the complete Lambert dilation family as the weighted
  divisor--Möbius incidence norm `(G32b)`, including all moving-boundary entries.  This proved the
  proper-dilate residual law `(G32c)` and killed `DILATION-GRAM-BOUNDARY-GAP` as a falsely
  independent source; the exact diagonalization is retained as its positive survivor.
- 2026-08-01 — upgraded conditional two-prime Rayleigh to the global Gibbs negative lattice law
  `(G5a)`.  Sparse log-modular Bernoulli laws have parity tending to one, so hostile audit rejects
  log-submodularity alone as an all-prime source while retaining the exact lattice inequality.
- 2026-08-01 — factored the exact zero/one-large-prime source through the scalar renewal defect
  `(G20a)`--`(G20b)` and proved that its full prime-tail kernel has one unique sign transition.
  PNT scaling places that transition at `m~z` for the minimal critical aperture, but the individual
  `m=1` term is already of order `1/(x log(1/x))`; hostile audit therefore rejects any
  transition-window-only mechanism.
- 2026-08-01 — isolated `MULTITYPE-BOUNDARY-TRANSPORT`.  Its exact matching-cost implication to
  `(G20)` is elementary.  Large-prime-to-two-small-prime transport fails by a logarithmic
  cardinality deficit; four-small-prime cross-sector transport passes that gate but cannot cover
  the sector-density imbalance alone.  The surviving conjecture adds same-sector
  one-small-to-two-small edges; short-interval, coprimality, global Hall, and aggregate displacement
  remain the explicit construction gates.
- 2026-08-01 — primary-literature audit found almost-all polylogarithmic short-interval supply for
  exact almost-primes and Type II technology, but no spectator-uniform injective opposite-sign
  transport or damped Hall bound.  Existing theorems may feed the aggregate incidence estimate;
  they do not close it.
- 2026-08-01 — hostile audit observed that the `T=z^2` boundary coefficients are literally
  `mu(n)` through the whole truncation, so an existential low-defect matching without local
  incidence estimates is source repackaging.  Replaced injectivity as the primary target by the
  exact symmetric fractional-flow law `(G43)`--`(G46)`: canonical unused capacity equals isolated
  Gibbs mass plus normalized-degree edge variation.  Lean formalizes both the general symmetric
  cancellation consumer and the minimum-endpoint conductance defect reduction.  The unsigned
  arithmetic incidence bound remains open.
