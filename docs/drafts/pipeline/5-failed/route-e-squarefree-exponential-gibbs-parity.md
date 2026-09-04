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

#### Theorem F1 — unrestricted fractional transport is exactly source-optimal
`[PAPER- AND LEAN-PROVED HERE]`

There is no hidden gain from optimizing the conductance after forgetting arithmetic locality.
Let

```text
P=sum_(sigma(n)=+1)w_x(n),   N=sum_(sigma(n)=-1)w_x(n).
```

For any admissible conductance on any opposite-sign graph, put
`F=sum_(sigma(m)=+1,sigma(n)=-1)c(m,n)`.  Row capacity gives
`F<=min(P,N)`, while symmetry gives the exact unused mass

```text
U(c)=P+N-2F >= |P-N|.                                    (G46c)
```

The bound is sharp on the complete opposite-sign graph.  If `P<=N` and `N>0`, set

```text
c(m,n)=w_x(m)w_x(n)/N   for sigma(m)=+1, sigma(n)=-1,     (G46d)
```

and extend symmetrically, with zero same-sign conductance.  Every positive row is saturated,
every negative row uses the fraction `P/N` of its capacity, and

```text
U(c)=N-P=|sum_n sigma(n)w_x(n)|.                          (G46e)
```

The other ordering is symmetric.  Lean formalizes the construction and equality as
`completeBipartiteProportionalConductance_exact_unused` and
`completeBipartiteProportionalConductance_attains_signedImbalance`.

This is an exhaustive theorem for unrestricted fractional transport, not a no-go for arithmetic
local transport.  It proves the exact burden: a low-defect existence assertion on an unspecified
graph is merely the source written as a flow.  New knowledge can enter only through an explicit
arithmetic graph or an independent analytic cancellation theorem.  The next audit proves that the
arithmetic graph cannot be uniformly value-local: macroscopic edges are forced on a
positive-density friable sector.

To test the value-local branch rather than assume it, for `H>=0` define the windowed relation by

```text
m ~_(z,H) n  iff  m~_z n and m<=n+H and n<=m+H.            (G46f)
```

Lean defines this literal relation as `MobiusBoundaryFactorReplacementWindowAdjacent`, proves it
symmetric and parity-flipping, and instantiates the canonical defect theorem as
`abs_truncatedMobiusLaplace_le_degreeNormalizedWindowedFactorReplacementDefect`.  Its degrees now
measure short-interval supply at a stated physical resolution.  This infrastructure makes the
following obstruction literal.

**Theorem F1b (friable macroscopic-gap law; paper-proved here).**  Let every prime divisor of
`n` be at most `y`, with `y<z`.  If `m~_z n` in the undirected `{one prime <-> two primes,
one prime >z <-> four primes <=z}` replacement graph, then

```text
                         |m-n| >= n/y^4.                  (G46h)
```

Proof.  For a same-sector edge written `n=aq`, `m=ars`, primality gives `q!=rs`; hence
`|m-n|=a|q-rs|>=a` and `n=aq<=ay<=ay^4`.  In the reverse orientation,
`n=ars`, so `n<=ay^2<=ay^4`.  A cross edge with `n=ap`, `p>z`, is impossible because
`p|n` would give `p<=y<z`.  In the remaining orientation `n=aq1q2q3q4`, and all four
prime divisors are at most `y`.  A prime cannot equal their fourfold product, so again
`|m-n|>=a` and `n<=ay^4`.  These cases exhaust the relation.  No distributional estimate
or Möbius cancellation is used.

Lean formalizes this division-free as
`le_pow_four_mul_dist_of_boundaryFactorReplacementAdjacent_of_primeFactors_le`:

```text
              n <= y^4 * Nat.dist n m.                   (G46h-L)
```

**Corollary F1c (sublinear-window isolation; paper-proved here).**  Put `N=1/x`.  Fix
`theta<1`, choose

```text
             0<alpha<min(1/2,(1-theta)/4),   y=N^alpha.
```

On the critical schedule `z^2` is of order `N log N`, so `y<z` and every `n in [N/2,N]`
lies inside the truncation.  The fixed-parameter Dickman asymptotic together with the
Ivić--Tenenbaum squarefree-smooth density gives `Omega_alpha(N)` squarefree `y`-smooth
integers in `[N/2,N]`.  Theorem F1b gives

```text
                  |m-n| >= (1/2)N^(1-4 alpha) > N^theta. (G46i)
```

Every one of these Möbius vertices is therefore isolated in the displacement-`N^theta`
graph.  Since `exp(-nx)` lies between `exp(-1)` and `exp(-1/2)` on this interval, their
total isolated Gibbs capacity is `Omega_alpha(N)`, not
`O_epsilon(N^(1/2+epsilon))` for `epsilon<1/2`.

Lean formalizes the finite isolation implication as
`not_boundaryFactorReplacementWindowAdjacent_of_primeFactors_le_of_pow_mul_lt`:
if `y^4 H<n`, no displacement-`H` replacement edge can leave `n`.

For the squarefree-smooth input, see Ivić--Tenenbaum's asymptotic as quoted with its range
in [Gorodetsky, §1.4](https://link.springer.com/article/10.1007/s00209-024-03601-w):
`Psi_(mu^2)(X,Y)=Psi(X,Y)/zeta(2)(1+o(1))`; Hildebrand's unconditional Dickman
asymptotic applies to `Y=X^alpha`.  Applying it at `X=N` and `X=N/2` gives the stated
dyadic positive density.

`[FALSIFIED: WEIGHTED-FIBER-INCIDENCE-REGULARITY WITH SUBLINEAR HARD SUPPORT]`
The proposed physical support `a|p-Q|<=z^(1+o(1))` has integer displacement
`N^(1/2+o(1))` on the critical schedule.  Corollary F1c applies with any fixed
`theta>1/2` and leaves linear isolated capacity.  Analogous sublinear windows for the
same-sector edges do not repair it.  Thus neither pointwise short-interval supply nor an
aggregate capacity split on this hard-support graph can prove `(G20)`.  This is a
falsification of the windowed producer, not of raw/macroscopic fractional transport and
not of Route E.  Failed-route record:
`../5-failed/route-e-sublinear-factor-replacement-flow.md`.

#### Rejected replacement: sectorwise friable cancellation

The macroscopic-gap law suggests splitting at a lower smoothness threshold and estimating the
friable signed sector separately.  This also fails, for a stronger reason than lack of a known
bound.

Put

```text
M_fri(X,Y)=sum_(n<=X, P+(n)<=Y) mu(n).
```

`[PUBLISHED THEOREM; CORRECTED PROJECT EXTRACTION]` Fix `1<u<2` and set
`Y=X^(1/u)`.  For `f=mu`, the zeta exponent in de la Bretèche--Tenenbaum is `z=-1`,
so their parameters are `m=1`, `m_z=-1`, and `theta_z=0`.  Crucially, their
Definition (1.28) makes the leading profile

```text
psi_(-1)=phi_(-1)^(m+1)=phi_(-1)'',
```

not `phi_(-1)` itself.  Theorem 1.2 and Corollary 1.3(i) therefore give

```text
M_fri(X,Y) = X/(log Y)^2 {psi_(-1)(u)+O(1/log Y)}.         (G46j)
```

The delay solution obeys

```text
v phi_(-1)'(v)=phi_(-1)(v-1),   phi_(-1)(v)=1 on 0<v<=1. (G46k)
```

For `1<u<2`, this gives

```text
phi_(-1)(u)=1+log u,     psi_(-1)(u)=phi_(-1)''(u)=-1/u^2.
```

Also `a_0(mu)=1`, since
`s^(-1)/((1+s)zeta(1+s))=1+O(s)`.  Since `log Y=log X/u`, the aperture dependence
cancels exactly:

```text
M_fri(X,X^(1/u))
  = -X/log^2 X + O(X/log^3 X).                            (G46l)
```

The expansion remains uniform on the Route E approach `u->2-`: below `2`, the previous integer
delay is `1`, so the theorem's distance condition stays bounded away from zero.  The hypotheses
of the cited theorem are literal here:
`sum mu(n)n^(-s)=zeta(s)^(-1)` has analytic factor `B(s)=1`, and `mu^2` admits a standard
positive divisor-function majorant.

The profile itself has a quantized seam jump.  On `2<u<3`,

```text
phi_(-1)'(u)=(1+log(u-1))/u,
```

so `psi_(-1)(2-)=-1/4` and `psi_(-1)(2+)=+1/4`.  Thus the raw profile jump is
`1/2`, while the normalized profile `u^2 psi_(-1)(u)` jumps from `-1` to `+1`.
At `u=2` the published expansion includes its explicit `U_J` boundary correction; this is a
profile jump, not a claimed discontinuity of the arithmetic sum.

Source: [de la Bretèche--Tenenbaum, *Friable averages of complex arithmetic functions*,
Theorem 1.2 and Corollary 1.3](https://arxiv.org/abs/2305.06486).
Full corrected extraction:
`../2-fully-proven/new_scientific_knowledge/route-e-mobius-friable-u2-seam-charge.md`.
Lean formalizes the elementary profile identities in
`MobiusFriableIntegerSeamProfile.lean`.

`[FALSIFIED: FRIABLE-SIFTED SPLIT SOURCE]` No proof may assign the fixed-power friable sector an
independent strict-half bound and then transport only the rough complement.  The friable sector
has the deterministic negative near-linear bias `(G46l)`.  Any successful source must cancel
that bias against the positive non-friable mass across macroscopic edges, or exploit the full
integer-delay seam before taking absolute values.

This identifies the next exact hard object.  The critical Route E aperture has
`log N/log z=2-o(1)`, so it approaches the integer seam `u=2` from the left.  The
zero/one-large-prime comparison is not a sum of two independently small sectors: it is the seam
cancellation between the universal charge `-N/log^2 N` and its positive one-large-prime
correction.  PNT-scale theory cancels these algebraic main charges but leaves a
zero-free-region remainder far above `N^(1/2+epsilon)`.
Square-root control of this beyond-all-orders seam remainder remains `OPEN-SOURCE-001`; renaming
it “friable cancellation” would be theatre.

#### Scalar renewal cannot bootstrap a power saving

The sharp-cutoff analogue makes the remaining obstruction quantitative.  For fixed `1<u<2`, put
`Y=X^(1/u)`.  Since an integer at most `X<Y^2` has at most one prime factor above `Y`,
largest-prime factorization gives the exact identity

```text
M(X)=M_fri(X,Y)-sum_(Y<p<=X) M(X/p).                       (G46m)
```

Consider the positive majorant of the renewal operator

```text
(T_(X,Y)f)=sum_(Y<p<=X) f(X/p)
```

in the weighted sup norm `|f(t)|<=t^alpha`.  Its exact norm on the positive extremizer
`f(t)=t^alpha` is

```text
X^(-alpha) T_(X,Y)f = sum_(Y<p<=X) p^(-alpha).             (G46n)
```

`[PAPER-PROVED BRIDGE; NOVELTY UNVERIFIED]` PNT and partial summation give

```text
sum_(Y<p<=X) p^(-alpha)
  ~ X^(1-alpha)/((1-alpha)log X)       (0<=alpha<1),       (G46o)
sum_(Y<p<=X) 1/p
  = log u+o(1)                         (alpha=1).           (G46p)
```

Thus the operator is contractive at the linear PNT norm when `log u<1`, but its absolute norm
diverges in every fixed power-saving norm, including `alpha=1/2+epsilon`.  This is the exact
exponent barrier behind the Daboussi renewal method: it can force `M(X)=o(X)` by a linear-norm
limsup argument, but no scalar magnitude bootstrap can reach `M(X)=O(X^alpha)` for any
`alpha<1`.

`[FALSIFIED: SCALAR-RENEWAL-POWER-BOOTSTRAP]` Reusing `(G46m)` with a stronger inductive sup bound
does not contract.  A viable seam source must prove signed orthogonality across prime scales in
`sum_p M(X/p)`, or replace the scalar norm by a structure that sees that orthogonality.  Merely
improving the friable main-term expansion or the PNT error does not cross `(G46o)`.

#### Primitive Gamma/co-Poisson completion of the seam

The supplied source paper suggests a specific non-scalar replacement for the prime tail, but the
replacement must first be compared to the literal Route E boundary.  Define the divided-log
prime-power current

```text
J_z^Gamma(x)
  =sum_(p>z) sum_(k>=1) (1/k) A_z(p^k x),
B_z^Gamma(x)=A_z(x)-J_z^Gamma(x).                         (G46q)
```

This is not an arbitrary smoothing.  Since

```text
Lambda(p^k)/log(p^k)=1/k,                                 (G46r)
```

`J_z^Gamma` is the physical Laplace realization of the primitive Euler--Gamma/co-Poisson normal
current: divide the already formalized confluent interval jet by one additional logarithmic
action.  Termwise, for every prime `p` and `k>=1`,

```text
-EulerGammaCoPoissonPrimitiveTerm(p^k,s)
  =(1/k) LSeries.term(1,s,p^k).                           (G46s)
```

The completion is source-exact at strict-half scale.  Indeed,

```text
B_z^Gamma(x)
 -(A_z(x)-sum_(p>z)A_z(px))
 =-sum_(p>z)sum_(k>=2)(1/k)A_z(p^k x).                   (G46t)
```

Absolute convergence permits the displayed rearrangement.  The elementary envelope

```text
|A_z(y)| <= sum_(m>=1)exp(-my)
          =1/(exp(y)-1) <= 1/y
```

then gives, for `z>=1`,

```text
|right side of (G46t)|
 <= x^(-1) sum_(p>z)sum_(k>=2)1/(k p^k)
 <= x^(-1) sum_(n>z)1/(n(n-1))
 =1/(xz).                                                 (G46u)
```

On the critical schedule `(G19)`, `z>=x^(-1/2)` once `x<=exp(-4)`, so `(G46u)` is
`O(x^(-1/2))`; the remaining compact `x`-range is absorbed into the constant.  Consequently the
original zero/one boundary estimate `(G20)` is equivalent, in both directions, to the same
strict-half estimate for `B_z^Gamma`.  No zero-free input enters this equivalence.

Mellin transformation on `Re(s)>1` identifies its exact source symbol:

```text
M[B_z^Gamma](s)
 =Gamma(s) product_(p<=z)(1-p^(-s))
    {1-sum_(p>z)sum_(k>=1)1/(k p^(ks))}.                  (G46v)
```

The bracket is the linearized primitive logarithmic Euler tail
`1+sum_(p>z)log(1-p^(-s))`.  Thus Route E's hard seam is, up to an already-critical error, the
primitive Gamma/co-Poisson current native to `main-universal.tex`, before scalarization.  This is
the first exact provider bridge to that paper; it does **not** supply the missing critical
orientation or estimate.  The remaining theorem is now sharply typed:

`[RETIRED AS MIS-TYPED: PRIMITIVE-GAMMA-COPOISSON-SEAM-ORIENTATION]` The first formulation asked
joint Wold breadth and exponent depth to create the missing norm on all of `B_z^Gamma`.  The
depth audit below shows that this assigns the hard work to the wrong source axis.  Positive depth
is already contained in the allowed strict-half error; only the depth-zero infinite-breadth face
remains hard.

Lean module `MobiusGammaCoPoissonPrimePowerBoundary.lean` formalizes `(G46r)`--`(G46t)` at every
finite prime and exponent aperture, including the exact primitive Gamma/co-Poisson term and the
pre-scalar small-prime parity boundary.  The analytic estimate `(G46u)` is the elementary
cofinal passage.  A targeted literature search found explicit formulas for the Möbius discrete
Laplace transform and standard log-Euler prime-power expansions, but no published coupling of
this Route E zero/one seam to a primitive Gamma/co-Poisson current; the individual ingredients are
classical, while the provider equivalence is recorded as project-new synthesis rather than
claimed independent resolution of RH.

#### Depth-axis hostile audit: Route E is singular only in breadth

At critical half-density, the divided-log Route E atom at valuation depth `e+1` is

```text
d_(p,e) = p^(-(e+1)/2)/(e+1).
```

The conditional Gamma valuation atom in the supplied source paper is

```text
g_(p,e) = p^(-1/2)(1-p^(-1))p^(-e).
```

Their exact gauge is therefore

```text
d_(p,e)/g_(p,e)
  = p^(e/2)/((e+1)(1-p^(-1))).                           (G46w)
```

This comparison separates the two source axes.  For fixed `p`, `(G46w)` is exponentially
unbounded with exponent depth, matching the paper's beyond-finite-Rees obstruction.  At depth
zero, however,

```text
d_(p,0)/g_(p,0)=1/(1-p^(-1)) in [1,2].                  (G46x)
```

The entire singular-depth sector `e>=1` is exactly the higher-prime-power difference in `(G46t)`,
already bounded by `1/(xz)=O(x^(-1/2))` on the critical schedule.  Consequently no proof can cite
unbounded primitive depth promotion as the mechanism controlling Route E's hard seam: all capacity
created only at positive depth acts on a sector which the existing absolute remainder estimate
has already removed.  The unresolved source is the depth-zero prime face

```text
B_z^(0)(x)=A_z(x)-sum_(p>z)A_z(px),
```

with infinitely many Wold breadth labels.  Gamma recovery on that face is uniformly bounded by
`(G46x)`.  The supplied paper's depth singularity remains essential for its full modular source
problem, but it is not the active singularity of Route E.

`[CONJECTURE: DEPTH-ZERO-WOLD-BREADTH-SEAM-ORIENTATION]` Construct a source-defined,
cofinally continuous signed orientation on the depth-zero prime face `B_z^(0)` with norm
`O_epsilon(x^(-1/2-epsilon))`.  It must act across unbounded Wold breadth before the unit
codiagonal is scalarized, retain the literal small-prime Möbius parity, and fail on Beurling
prime systems having strict-right zeros.  Positive exponent depth may enter only through the
already-proved `O(x^(-1/2))` correction; it may not be used as hidden amplification of the hard
face.

`MobiusGammaCoPoissonDepthZeroReduction.lean` proves `(G46w)` and the uniform prime-fibre
certificate `(G46x)` unconditionally.  A March 2026 theorem of Tenenbaum
([paper](https://tenenb.perso.math.cnrs.fr/PPP/On-Mobius-series.pdf)) independently confirms the
first-breadth phenomenon: the divisor transform of `mu(n) omega(n)` is supported on prime powers,
and the corresponding `1/n` series has PNT-level cancellation.  That theorem controls one Wold
normal derivative, not the singular unit response across all breadths required here.  It therefore
supports the axis diagnosis but does not supply the conjectured orientation.

#### Updated source-category audit: scalar phase nodes cannot carry the hard face

`[PAPER- AND LEAN-PROVED NO-GO]`  The updated modular-superselection paper closes the formerly
surviving infinite one-prime phase-node tower in the global prime-clock quotient.  Combining that
result with `(G46x)` gives a sharper Route E theorem.  The canonical hard-face profile is

```text
d(p,e)=p^(-1/2)  if e=0,
d(p,e)=0         if e>=1.                               (G46y)
```

Every rational-prime ray is active, so its class is nonzero modulo finite-prime Euler profiles.
At any nonzero carrier frequency, however, prime-logarithm independence forces every prime-power
phase-node profile to have active prime-base support of cardinality at most one; the updated
quotient theorem then makes its global class zero.  Therefore `(G46y)` cannot be realized by a
scalar phase-node multiplier.  This uses no boundedness, finite-depth, or finite-Rees hypothesis:
an infinite one-prime tower is still local Euler data and cannot orient Route E's all-prime
breadth current.

The exact survivor is narrower than the preceding conjecture: a valid source must couple
infinitely many prime rays outside scalar prime-power phase-node screening, through
non-prime-power singular support, a relation-valued breadth correspondence, reflection-breaking
pre-scalar transport, or an ordinary-lattice/co-Poisson global law.

Full proof:
`../2-fully-proven/new_scientific_knowledge/route-e-depth-zero-prime-clock-phase-node-no-go.md`.
Lean:
`MobiusDepthZeroPrimeClockPhaseNodeNoGo.lean`.

#### Beurling firewall: local prime geometry is not enough

`[PAPER-PROVED BRIDGE; NOVELTY UNVERIFIED]` The remaining breadth conjecture must now pass a
strict countermodel test.  Diamond--Montgomery--Vorhauer construct a **discrete** Beurling prime
system with

```text
N_P(X)=kappa X+O(X^theta),  1/2<theta<1,
```

a de la Vallée Poussin-scale PNT, and infinitely many zeta zeros with real part greater than
`1/2`.  On that same free prime-factor monoid, all local and PNT-level ingredients retained above
survive:

1. every finite exponential-Gibbs table remains strictly log-submodular and conditionally
   two-prime Rayleigh, since the proof uses only `(r-1)(s-1)>0`;
2. unique factorization gives the identical zero/one-large-prime decomposition;
3. `N_P(X)=kappa X+O(X^theta)` bounds the sector with at least two primes above `z` by
   `O(x^(-1/2))` whenever `xz^2>=(1/2)log(1/x)`;
4. PNT partial summation gives the same unique transition
   `z tau_z/log z -> 1` and the same scalar renewal barrier;
5. `Lambda_P(p^k)/log|p^k|=1/k`, and after deleting finitely many initial primes the depth-zero
   Gamma gauge remains in `[1,2]`.

Nevertheless its Möbius--Laplace transform cannot obey an `O(x^(-a))` bound for any
`a<Re rho` at a strict-right zero `rho`: Mellin transformation would continue
`Gamma(s)/zeta_P(s)` holomorphically through its pole.  Since the higher-large-prime remainder is
already `O(x^(-1/2))`, the zero/one boundary fails the same bound.

Thus the exact axiom package

```text
prime-factor monoid + PNT + local Gibbs/Rayleigh geometry
+ critical zero/one aperture + scalar renewal
+ divided-log Gamma completion + bounded depth-zero gauge
```

has a strict-right-zero model.  It cannot imply `(G20)`.  A viable Wold-breadth orientation must
use an ordinary-integer-specific discriminator absent from that model: the additive lattice,
its archimedean functional equation/co-Poisson reflection, or an equivalent global invariant.
Calling the missing discriminator “integer arithmetic” is not progress; the next conjecture must
name it and derive a quantitative source estimate from it.

Complete theorem and proof:
`../2-fully-proven/route-e-beurling-local-axiom-firewall.md`.

The firewall is sharp at the generalized-integer counting threshold.  Zhang constructs, after
any prescribed finite ordinary-prime prefix, a discrete dyadic-rational Beurling system satisfying

```text
N_P(X)=X+X^(1/2) exp(O((log X)^(2/3))),
```

whose zeta function continues analytically through `Re(s)>1/2` apart from the pole at one, yet has
infinitely many zeros on `Re(s)=1-1/log|t|`.  Since this error is
`O_delta(X^(1/2+delta))`, the same critical higher-large-prime remainder proof applies; the Mellin
argument then rules out every `O(x^(-a))` seam bound with `1/2<a<Re(rho)`.  Therefore neither
near-critical integer counting, strict-half continuation, nor agreement with arbitrarily much
finite ordinary-prime data is the missing discriminator.  It must consume exact all-scale
additive self-duality, not an asymptotic or finite approximation to it.

Integer-level collisions admit an exact incidence lift.  If a squarefree target `m` has
`r=omega(m)` prime factors, it has exactly `binom(r,k)` choices of a `k`-factor replacement label.
Give every lifted copy `(m,Q)` the capacity

```text
w_x(m,Q)=w_x(m)/binom(omega(m),k),  Q|m, omega(Q)=k.
```

Then

```text
sum_(Q|m, omega(Q)=k) w_x(m,Q)=w_x(m).                    (G46a)
```

Thus repeated representations of the same target consume exactly its available capacity, not a
worst-case congestion multiple.  For a cross-sector copy `m=aQ` with `omega(Q)=4` and `(a,Q)=1`,
the denominator is the explicit `binom(omega(a)+4,4)`.  The corresponding target supply in a token
interval `I` is therefore the positive weighted incidence sum

```text
nu_4(a,I;x)=sum_(Q in I, omega(Q)=4, P^+(Q)<=z, (a,Q)=1)
              exp(-aQx)/binom(omega(a)+4,4).              (G46b)
```

The same construction with one- and two-factor labels applies to the same-sector edges.  Lean
formalizes `(G46a)` as
`sum_uniform_fixedCardinalityIncidenceCapacity_eq_one`; it is a finite binomial identity and adds
no source assumption.

Lean also defines the literal aperture-bounded edge relation
`MobiusBoundaryFactorReplacementAdjacent`, proves its symmetric closure reverses the embedded
Möbius coefficient, and instantiates the canonical flow theorem as
`abs_truncatedMobiusLaplace_le_degreeNormalizedFactorReplacementDefect`.  Its left side is the
actual Möbius--Laplace truncation through `z^2`; its right side is the positive isolated-mass plus
normalized-edge-variation expression.  No unnamed graph or sign hypothesis remains in this
consumer.

`[RETIRED CONJECTURE: WEIGHTED-FIBER-INCIDENCE-REGULARITY]` The falsified proposal split every
vertex capacity between the cross
four-factor lift and the same-sector one/two-factor lifts by an explicit function of its factor
count.  For a fixed spectator `a`, regard the cross source and target as measures on token value,

```text
lambda_a = sum_(p>z, ap<=z^2, (a,p)=1) theta_(omega(a)) exp(-apx) delta_p,
nu_a     = sum_(Q, omega(Q)=4, P+(Q)<=z, (a,Q)=1)
               theta'_(omega(a)) exp(-aQx)/binom(omega(a)+4,4) delta_Q. (G46g)
```

It required the cross coupling to be supported on
`a|p-Q|<=z^(1+o(1))`, with analogous physical windows for the one/two-factor measures.  The
required statement is an *aggregate unbalanced capacity bound*: after adding those same-sector
measures, there are sub-couplings whose unused source and target mass, summed over all spectators
and dyadic value windows, is `O_epsilon(z^(1+epsilon))`.  Under `(G43)`--`(G46)`, this positive
weighted statement implies `LOCAL-FRACTIONAL-BOUNDARY-FLOW`.

No displacement moment was added to this fractional objective.  Conductance couples portions of
the already weighted masses `exp(-nx)`, so equal coupled capacity cancels exactly even when the
integer labels differ.  A cost `min(1,xa|p-Q|)` belongs to the unsplit atom-matching formulation
`(G39)`; mixing it into `(G43)` would double-charge displacement.  Value locality remains a hard
support condition only in this retired short-interval branch.

Corollary F1c now disproves the required aggregate bound before any incidence estimate is invoked.
The binomial lift remains valid infrastructure; it cannot create neighbors for isolated friable
vertices.

`[RETIRED IN SUBLINEAR-WINDOW FORM: LOCAL-FRACTIONAL-BOUNDARY-FLOW]` The conjecture required, for
every `epsilon>0`, pruning or positive reweighting of the two replacement families at a critical
aperture so that the right side of `(G44)` was `O_epsilon(x^(-1/2-epsilon))`.  Corollary F1c
rules this out whenever all retained edges have displacement `N^theta`, `theta<1`.  A replacement
flow conjecture can remain viable only if it permits macroscopic edges on the friable bulk and
proves a genuinely arithmetic capacity theorem for them.

The failed conjecture was more concrete than an existential matching because `(G46)` is positive
and unsigned.  Its exposed failure is now exact: the “small smooth core” is not a negligible
`O(z^(1+o(1)))` fringe at effective scale `N=1/x`; power-smooth squarefree vertices have linear
mass.  Neither `(G44)` nor `(G46)` may be justified by assuming a Mertens bound or by deleting
this bulk.

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

#### Corollary F2 — prime-only atoms have pointwise close four-small replacements
`[PAPER-PROVED HERE]`

The all-interval part of Matomäki--Teräväinen contains more factor information than its abstract.
For every large `y`, their proof produces

```text
r_1 r_2 r_3 in (y,y+h_y],
h_y=sqrt(y)(log y)^1.55,
r_1 asymp (log y)^1.1,
r_2 asymp sqrt(y/(log y)^1.1),                            (G47)
```

with a lower-bound count of order at least
`sqrt(y)/((log y)^0.45 log log y)`.  Let `z` be large, let `z<p<=z^2` be prime, and apply `(G47)`
at `y=p/2`.  Put `Q=2r_1r_2r_3`.  The factor ranges give, for large `z`,

```text
p<Q<=p+C z(log z)^1.55,
every prime factor of Q is <=z.                           (G48)
```

The produced triples may a priori include `r_2=r_3`.  This does not obstruct squarefreeness: for
each `r_1`, the condition `r_1 r_2^2 in (y,y+h_y]` permits only
`O(h_y/(r_1 sqrt(y/(log y)^1.1))+1)=O(log y)` integer values of `r_2`.  Summing over the
`O((log y)^1.1/log log y)` possible `r_1` gives only
`O((log y)^2.1/log log y)` diagonal products, negligible against the lower bound in `(G47)`.
The other factor ranges are disjoint, and exclude the fixed factor `2`.  Hence one may choose `Q`
squarefree with four distinct prime factors, so `mu(Q)=+1=-mu(p)`.

Thus every prime-only negative atom through `z^2` has a pointwise parity-flipping cross edge whose
Gibbs relative displacement is

```text
x|Q-p| <= C (log z)^2.55/z                                (G49)
```

on the minimal critical schedule.  This is below every required `z^(-1+epsilon)` relative scale.
It closes the prime-center *existence* gate unconditionally; it does not close the flow.

For a general one-large atom `ap`, multiplication by `a` requires the four replacement primes to
avoid every prime factor of `a`.  The proof of `(G47)` uses one polylogarithmic prime factor and two
factors near `sqrt(y/(log y)^1.1)`.  A spectator `a<=z^2/p` excludes only a
`O((log z)^(-0.1))` fraction of the first factor interval and only `O(1)` primes in either large
factor interval, but the published theorem is not stated uniformly after these exclusions.

`[POINTWISE STRENGTHENING, NOT THE ACTIVE TARGET: SPECTATOR-COPRIME-E3-ALL-INTERVAL]` Uniformly for squarefree
`a<=z^2/p` and prime `z<p<=z^2`, there are four-small-prime replacements `Q` with
`a|Q-p|<=z^{1+o(1)}`, with `(a,Q)=1`, in the factor ranges of `(G47)`; quantitatively there are
enough such `Q` to
retain the lower bound in `(G47)` up to `z^{o(1)}`.  This is the precise modification of the
all-interval Type-II theorem needed for cross-edge degree.  Even this conjecture gives only row
supply.  The combined cross/same-sector graph must still satisfy `(G46)`; pointwise non-isolation
alone cannot control its normalized-degree variation.

The pointwise statement is stronger than Route E needs and is no longer the primary conjecture.
It also has the wrong proof interface: a lower bound for the number of candidates in each source
row gives no upper bound on target load.  In the top `p asymp z^2` regime, the published lower
bound supplies only `z/((log z)^0.45 log log z)` candidates in a window of length
`z(log z)^1.55`; even Brun--Titchmarsh-scale target co-degree control leaves logarithmic factors
unresolved.  Those factors are fatal if paid as unused Gibbs mass.  The unbalanced measure target
`(G46g)` therefore requires a two-sided incidence estimate or a multiscale capacity split, not
pointwise existence followed by an arbitrary selector.

Corollary F1c adds a terminal limitation: even a proof of this pointwise prime-center statement
would cover only vertices containing a prime above `z`.  It cannot supply any edge for the
positive-density `N^alpha`-smooth bulk in a sublinear window.  The prime-center theorem remains a
correct prime-only incidence survivor, but it is no longer a candidate source without a separate
macroscopic mechanism for friable vertices.

The factor `a` in this statement is essential.  Corollary F2 uses the all-interval
`sqrt(p)(log p)^1.55` gap and therefore handles `a=z^{o(1)}`.  At the opposite corner
`p asymp z`, `a asymp z`, the allowed token gap is only `z^{o(1)}`.  The almost-all
polylogarithmic `E_k` theorems live at that scale, but their published exceptional set may contain
all prime centers and they are not uniform under spectator-factor deletion.  Combining these two
regimes, rather than citing either theorem alone, is the exact cross-edge supply bottleneck.

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
  selection with damped displacement, exact parity reversal of both local replacement types, and
  symmetric fractional-flow capacity consumption.  It also covers the complete-bipartite
  proportional optimizer and the literal displacement-windowed replacement graph.
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
- 2026-08-01 — proved the sharp converse for fractional transport: every opposite-sign
  conductance leaves at least the signed Gibbs imbalance, while proportional transport on the
  complete bipartite graph attains equality.  This exhausts unspecified conductance optimization
  without retiring the local arithmetic producer.  Added a displacement-windowed replacement
  relation and its concrete Lean defect theorem; replaced the overstrong every-spectator
  pointwise conjecture by an aggregate unbalanced incidence-capacity target with hard physical
  support and explicit source/target masses.  A hostile recheck separated this fractional target
  from the displacement cost used only by unsplit atom matching.
- 2026-08-01 — extracted a pointwise prime-only four-small replacement from the factor ranges in
  Matomäki--Teräväinen's all-interval `E_3` proof.  A second scale audit showed that general
  spectators require `a|Q-p|<=z^{1+o(1)}`; at `a,p asymp z` this returns to the unresolved
  polylogarithmic prime-center regime.  Introduced the binomial incidence-capacity lift `(G46a)` to
  remove representation congestion exactly, and formalized its uniform capacity partition in
  Lean.  Weighted spectator-fiber incidence regularity was the resulting hard source theorem; the
  next audit falsified its sublinear hard support.
- 2026-08-01 — falsified that hard-support target.  Every neighbor of a `y`-smooth vertex in the
  `{1<->2,1>z<->4}` replacement graph has displacement at least `n/y^4`.  Fixed-power
  squarefree-smooth density therefore gives `Omega(N)` isolated Gibbs capacity in every
  displacement-`N^theta` pruning with `theta<1`, including the proposed
  `z^(1+o(1))=N^(1/2+o(1))` support.  The exact gap law is the positive survivor; Route E remains
  open and any replacement transport must permit macroscopic friable edges or provide an
  independent signed friable cancellation theorem.
- 2026-08-01 — rejected the latter sectorwise repair.  A primary-source re-audit corrected the
  specialization of de la Bretèche--Tenenbaum at zeta exponent `-1`: their leading profile is
  `psi_(-1)=phi_(-1)''`, not `phi_(-1)`.  For `1<u<2` it gives the universal negative main
  charge `-X/log^2 X`, exactly independent of `u`; its normalized profile jumps from `-1` to
  `+1` at the integer seam.  This charge must be cancelled against the positive one-large-prime
  sector, not bounded separately.  Strict-half control of the localized zero/one-sector
  remainder is still literal `OPEN-SOURCE-001`.
- 2026-08-01 — completed the first exact provider bridge from Route E to the supplied
  Gamma/co-Poisson source.  Adjoining every higher prime power with coefficient `1/k` changes the
  zero/one boundary by at most `1/(xz)=O(x^(-1/2))` on the critical aperture, hence preserves the
  strict-half problem exactly.  The completed tail is the primitive Gamma/co-Poisson confluence
  current `Lambda(p^k)/log(p^k)=1/k`; its finite pre-scalar identity is Lean-proved in
  `MobiusGammaCoPoissonPrimePowerBoundary.lean`.  The bridge relocates, but does not assume, the
  remaining signed orientation theorem.
- 2026-08-01 — hostile source-alignment audit separated exponent depth from Wold breadth.  The
  exact Gamma-to-divided-log gauge is `p^(e/2)/((e+1)(1-p^(-1)))`; it is uniformly in `[1,2]` at
  depth zero and singular only for positive depth.  Positive depth is precisely the already
  admissible `O(x^(-1/2))` higher-prime-power correction.  Retired the mis-typed joint-axis
  orientation target and replaced it by `DEPTH-ZERO-WOLD-BREADTH-SEAM-ORIENTATION`.
  `MobiusGammaCoPoissonDepthZeroReduction.lean` formalizes the exact axis separation
  unconditionally.
- 2026-08-01 — proved the Beurling local-axiom firewall.  A discrete
  Diamond--Montgomery--Vorhauer system retains the finite Gibbs Rayleigh/log-submodular law,
  PNT-scale critical transition, zero/one decomposition with critical higher-sector remainder,
  scalar-renewal barrier, divided-log Gamma completion, and bounded depth-zero gauge, while its
  zeta function has infinitely many strict-right zeros.  Mellin continuation forces the
  corresponding zero/one seam to violate every exponent below such a zero.  Therefore those
  local/PNT/Gamma inputs cannot produce Route E; the next breadth conjecture must use a named
  ordinary-integer-specific additive or archimedean discriminator.  Full paper proof:
  `../2-fully-proven/route-e-beurling-local-axiom-firewall.md`.

## Exact ordinary-lattice successor: rough-composite Lambert image

`[PAPER-PROVED BRIDGE; NOVELTY UNVERIFIED]`  The first named discriminator surviving the
Beurling firewall is the ordinary integer dilation lattice itself.  Let

\[
{\cal L}f(x)=\sum_{k\ge1}f(kx)
\tag{G47}
\]

and retain the fixed-aperture depth-zero boundary

\[
B_z^{(0)}(x)=A_z(x)-\sum_{p>z}A_z(px).
\tag{G48}
\]

Absolute convergence permits product-index regrouping.  If
\[
P^-(n)>z
\quad\Longleftrightarrow\quad
p\mid n\Longrightarrow p>z
\]
with the convention that \(1\) is \(z\)-rough, then

\[
{\cal L}B_z^{(0)}(x)
=e^{-x}
-\sum_{\substack{n\ge2,\ P^-(n)>z\\\omega(n)\ge2}}
   (\omega(n)-1)e^{-nx}.
\tag{G49}
\]

Indeed, the coefficient of \(e^{-nx}\) after Lambert dilation is the divisor sum of the
zero/one-large-prime coefficient.  If \(n\) has a prime factor at most \(z\), Boolean
inclusion--exclusion over its small-prime support makes that divisor sum zero.  If \(n\) is
\(z\)-rough, only the divisor \(1\) and the \(\omega(n)\) squarefree prime divisors occur in the
zero/one coefficient, giving \(1-\omega(n)\).  Thus every rough prime-power fibre is annihilated
exactly; only genuinely transverse rough support remains, with one fixed sign.

Write the positive tail in `(G49)` as \(C_z(x)\).  Since
\(\omega(n)\le\log n/\log2\), every term has \(n>z^2\), and elementary geometric-tail
summation gives, uniformly for \(0<x\le1\),

\[
C_z(x)
\ll e^{-xz^2}x^{-1}
   \bigl(\log(1/x)+xz^2+1\bigr).
\tag{G50}
\]

On `(G19)`, this is

\[
C_z(x)=O\!\left(x^{-1/2}\log(1/x)\right)
       =O_\varepsilon(x^{-1/2-\varepsilon}).
\tag{G51}
\]

Consequently the complete ordinary-lattice image of the hard boundary is already at the required
strict-half scale and has a positive normal form.  Missing arrow is now exact:

```text
positive rough-composite defect (G49)--(G51)
  -- singular inverse of ordinary Lambert dilation -->
depth-zero Wold-breadth boundary B_z^(0).
```

This is not a proof of the inverse estimate.  The limiting datum \(e^{-x}\) has inverse
\(\Phi(x)\), and bounded inverse control at every strict-half weight is the reciprocal-zeta/RH
problem.  Hence generic Lambert inversion, a positive-cone Tauberian bound, or a bounded
finite-prefix-stable inverse would merely assume `OPEN-SOURCE-001`.  A survivor must exploit the
specific co-moving rough tail in `(G49)` through a nonclosable or relation-valued inverse whose
admission is tied to exact integer self-duality.  The local-prefix nonrobustness theorem in
`../2-fully-proven/route-e-beurling-local-axiom-firewall.md` proves that such admission cannot
have a uniform finite-prefix margin.

Collision audit: the classical identity \({\cal L}\Phi=e^{-x}\), generic Möbius inversion, and
truncated divisor convolutions are known and already frozen.  No located source states the
zero/one Route E boundary image `(G49)`, its prime-power annihilation, or its critical positive
tail estimate `(G51)`.  These are recorded as project-new synthesis, not claimed as a solution of
RH.  `MobiusRoughLambertBoundary.lean` proves the literal finite support-divisor regrouping,
small-prime fibre cancellation, rough prime-power annihilation, and fixed negative orientation of
every transverse rough support unconditionally.  It also proves that the complementary
two-or-more-large sector has coefficient \(\omega(n)-1\), so the positive rough-composite current
belongs exactly to that remainder before any cofinal passage.  The infinite regrouping and
`(G50)` are the elementary absolutely convergent cofinal passage.

- 2026-08-01 — sharpened Zhang's construction to the local-prefix nonrobustness theorem: every
  sound strict-half certificate holding at the ordinary primes is non-open in finite-prefix
  topology.  This rules out uniform cofinal-continuity language and forces joint
  aperture/critical-scale singularity.
- 2026-08-01 — found the first exact ordinary-additive-lattice successor to the Beurling
  firewall.  Lambert dilation of the fixed-aperture depth-zero boundary kills all rough
  prime-power fibres and leaves the one-signed rough-composite defect `(G49)`.  Its entire image
  is already \(O_\varepsilon(x^{-1/2-\varepsilon})\) at critical aperture; unresolved source is
  precisely singular inverse-Lambert orientation on this co-moving cone, not construction of a
  small forward image.  The exact finite divisor-fibre law and both support strata are formalized
  unconditionally in `MobiusRoughLambertBoundary.lean`.

## Critical breadth-two concentration of the Lambert image

`[PAPER-PROVED CANDIDATE NEW SCIENTIFIC KNOWLEDGE; NOVELTY UNVERIFIED]`  The positive tail in
`(G49)` is not spread over unbounded Wold breadth at the self-dual scale.  Let \(z\to\infty\),
put

\[
x_z=\frac{\lambda_z}{z^2},
\qquad
\frac{\lambda_z}{\log z}\longrightarrow1,
\tag{G52}
\]

and retain

\[
C_z(x)=
\sum_{\substack{n\ge2,\ P^-(n)>z\\\omega(n)\ge2}}
(\omega(n)-1)e^{-nx}.
\]

Then

\[
C_z(x_z)
\sim
\frac{z^2e^{-\lambda_z}}
     {2\lambda_z^2(\log z)^2}.
\tag{G53}
\]

The main term is exactly the squarefree rough-semiprime stratum

\[
\sum_{z<p<q}e^{-x_zpq}.
\tag{G54}
\]

Every support of breadth at least three and every breadth-two support with a repeated valuation
has \(n>z^3\), and hence contributes

\[
\ll
\sum_{n>z^3}\log n\,e^{-x_zn}
=e^{-\lambda_z z}z^{O(1)}
=o\!\left(
\frac{z^2e^{-\lambda_z}}
     {\lambda_z^2(\log z)^2}
\right).
\tag{G55}
\]

For `(G54)`, first order the two primes and remove the diagonal.  The PNT, twice by Stieltjes
partial summation, gives

\[
\sum_{p>z}\sum_{q>z}e^{-x_zpq}
\sim
\int_z^\infty\int_z^\infty
\frac{e^{-x_zuv}}{\log u\log v}\,du\,dv.
\tag{G56}
\]

The relevant prime intervals have length \(z/\lambda_z\asymp z/\log z\); the classical
de la Vallée Poussin PNT remainder is \(o(z/\log^2z)\), so `(G56)` is uniform on every fixed
boundary layer.  Set

\[
u=z(1+a/\lambda_z),\qquad
v=z(1+b/\lambda_z).
\]

After factoring out \(e^{-\lambda_z}\), the integrand tends to \(e^{-a-b}\), while elementary
Chebyshev/PNT bounds dominate the complement of \(0\le a,b\le A\) by \(O(e^{-A})\) times the
main scale.  Letting first \(z\to\infty\) and then \(A\to\infty\) yields

\[
\int_z^\infty\int_z^\infty
\frac{e^{-x_zuv}}{\log u\log v}\,du\,dv
\sim
\frac{z^2e^{-\lambda_z}}
     {\lambda_z^2(\log z)^2}
\int_0^\infty\int_0^\infty e^{-a-b}\,da\,db.
\tag{G57}
\]

The diagonal prime-square sum is

\[
O\!\left(\frac{ze^{-\lambda_z}}
               {\lambda_z\log z}\right)
=o\!\left(\frac{z^2e^{-\lambda_z}}
                {\lambda_z^2(\log z)^2}\right).
\tag{G58}
\]

Dividing the ordered off-diagonal sum by two proves `(G53)`.

There is a canonical sharp aperture.  Let \(\lambda_z>0\) be the unique solution

\[
\lambda_z+\frac12\log\lambda_z=\log z,
\qquad x_z=\lambda_z/z^2.
\tag{G59}
\]

Then \(x_zz^2=\frac12\log(1/x_z)\), so `(G19)` holds, and
\(e^{-\lambda_z}=\sqrt{\lambda_z}/z\).  Equations `(G53)` and `(G59)` give the sharper physical
law

\[
C_z(x_z)
\sim
\frac{x_z^{-1/2}}
     {2\lambda_z(\log z)^2}
\sim
\frac{x_z^{-1/2}}
     {2(\log z)^3}.
\tag{G60}
\]

`[RETIRED: ROUGH-SEMIPRIME-LAMBERT-RETURN]`  A hostile source audit prevents treating this
near-square-root positive mass as capacity for the hard boundary.  Let
\(R_{\ge2,z}\) be the two-or-more-large-prime remainder in `(G17)`.  Since

\[
\Phi=B_z^{(0)}+R_{\ge2,z},\qquad
{\cal L}\Phi=e^{-x},\qquad
{\cal L}B_z^{(0)}=e^{-x}-C_z,
\]

linearity gives the exact identity

\[
{\cal L}R_{\ge2,z}=C_z.                                  \tag{G61}
\]

Thus `(G53)` is the forward image of the sector already controlled absolutely in `(G18)`.
Any inverse-Lambert lift of the rough-semiprime current reconstructs \(R_{\ge2,z}\), not the hard
zero/one boundary.  After subtracting it, the remaining datum is the bare vacuum
\(e^{-x}\), whose physical inverse is exactly \(\Phi\).  Claiming that `(G54)` sources
\(B_z^{(0)}\) would therefore be circular source reassignment.

The positive survivor is still sharp and useful: ordinary Lambert scalarization sends all
critical positive capacity into the already-admissible remainder and erases the hard Möbius
preimage.  Hence neither the one-signed rough-composite cone, its breadth-two concentration, nor a
subpower inverse bound on that cone can orient Route E.  A successful ordinary-lattice source
must act **before** this Lambert scalarization or supply an independent co-Poisson boundary
condition selecting the vacuum preimage; it cannot be extracted from \(C_z\).

Collision audit found general semiprime counting, higher Mertens constants for almost primes, and
standard Laplace/PNT machinery, but no source stating the moving lower-prime-cutoff asymptotic
`(G53)`, its occurrence as the exact Route E Lambert image, or the canonical critical law
`(G60)`.  Ingredients are classical; combined theorem is retained as candidate new knowledge
pending external priority audit.

- 2026-08-01 — proved critical breadth-two concentration `(G53)`.  At canonical critical
  aperture the entire positive forward image is asymptotic to
  \(x^{-1/2}/(2(\log z)^3)\), carried by rough squarefree semiprimes; higher breadth and positive
  valuation depth are exponentially negligible.  Hostile audit then proved `(G61)`: this current
  is exactly the Lambert image of the already-controlled two-large-prime remainder.  Retired
  `ROUGH-SEMIPRIME-LAMBERT-RETURN`; it reconstructs the error sector, not the hard boundary.

## Second-order multiplicative rectangle cubature

`[LEAN-PROVED CANDIDATE NEW SOURCE MECHANISM; ARITHMETIC CAPACITY OPEN]`  Pairwise transport is
not the terminal transport geometry.  Its cost is first order in one integer displacement and
therefore multiplies a token gap by the entire spectator.  Two independent parity reversals form
a multiplicative rectangle and cancel both first-order edge defects.

For nonnegative reals

\[
0\le a_0\le a_1,\qquad 0\le b_0\le b_1,\qquad x\ge0,
\]

put \(F_x(a,b)=e^{-xab}\).  Then the exact global inequality is

\[
\left|F_x(a_0,b_0)-F_x(a_1,b_0)-F_x(a_0,b_1)+F_x(a_1,b_1)\right|
\le x(a_1-a_0)(b_1-b_0).
\tag{G62}
\]

This has no hidden compact-range constant.  With

\[
\begin{aligned}
Y&=xa_0b_0,&
U&=x(a_1-a_0)b_0,\\
V&=xa_0(b_1-b_0),&
W&=x(a_1-a_0)(b_1-b_0),
\end{aligned}
\]

the bracket after factoring out \(e^{-Y}\) is

\[
(1-e^{-U})(1-e^{-V})-e^{-(U+V)}(1-e^{-W}).
\]

The inequalities \(0\le1-e^{-t}\le t\) give absolute value at most
\(UV+W\).  Finally

\[
e^{-Y}(UV+W)
=x(a_1-a_0)(b_1-b_0)(1+Y)e^{-Y}
\le x(a_1-a_0)(b_1-b_0),
\]

proving `(G62)`.  Equivalently,
\(\partial_a\partial_b e^{-xab}=x(xab-1)e^{-xab}\) and
\(\sup_{t\ge0}|t-1|e^{-t}=1\).

The Möbius admission is literal.  Suppose all four displayed products are coprime
factorizations and

\[
\mu(a_1)=-\mu(a_0),\qquad \mu(b_1)=-\mu(b_0).
\tag{G63}
\]

Multiplicativity gives the checkerboard

\[
\mu(a_1b_0)=-\mu(a_0b_0),\qquad
\mu(a_0b_1)=-\mu(a_0b_0),\qquad
\mu(a_1b_1)=\mu(a_0b_0).
\]

Thus `(G62)` bounds the actual signed four-atom packet, not a positive surrogate.  Lean module
`MobiusMultiplicativeRectangleCubature.lean` proves `(G62)`, the three corner-sign identities,
the literal complex Möbius--Laplace packet bound, finite packet aggregation, and its
nonnegative fractionally weighted form, all unconditionally.

The finite hypergraph form makes the new arithmetic burden exact.  Let \({\cal R}\) be a fixed
family of admitted rectangles in the zero/one-large-prime boundary and let \(c_R\ge0\).  Count
corner multiplicity and put

\[
q(n)=\sum_{R\in{\cal R}}c_R\,
  \#\{(i,j)\in\{0,1\}^2:a_i(R)b_j(R)=n\}.
\]

If \(q(n)\le1\), finite regrouping and `(G62)` give

\[
\left|\sum_{n\in V}\mu(n)e^{-nx}\right|
\le
\sum_{n\in V}(1-q(n))e^{-nx}
+x\sum_{R\in{\cal R}}c_R
 |a_1(R)-a_0(R)|\,|b_1(R)-b_0(R)|.
\tag{G64}
\]

Unlike unrestricted opposite-sign conductance, `(G64)` is not tautologically optimized by the
signed imbalance.  Its packets must satisfy the rank-one multiplicative relation

\[
n_{00}n_{11}=n_{10}n_{01}
\tag{G65}
\]

and two independent factorwise parity reversals.  The cost is a mixed area, not the sum of its
edge lengths.

### Why this escapes the proved sublinear-flow obstruction

Write \(N=1/x\), and consider \(n=a_0b_0\asymp N\).  If the two token replacements obey

\[
|a_1-a_0|\le a_0^{1/2}N^{o(1)},\qquad
|b_1-b_0|\le b_0^{1/2}N^{o(1)},
\tag{G66}
\]

then one rectangle costs

\[
x|a_1-a_0||b_1-b_0|
\le N^{-1/2+o(1)}.
\tag{G67}
\]

An \(O(N)\)-mass fractional cover therefore has total cost
\(N^{1/2+o(1)}\), exactly the strict-half allowance.  By contrast, either individual edge costs
\(xb_0|a_1-a_0|\) or \(xa_0|b_1-b_0|\); this is the spectator amplification which killed the
sublinear pair graph.  The friable macroscopic-gap theorem `(F1)` is first order and does not
apply to the product cost `(G67)`.

The already-audited all-interval \(E_3\) construction supplies the correct pointwise exponent.
Its factor ranges give, for every sufficiently large target \(u\), a squarefree exact-three-prime
integer in

\[
(u,u+O(\sqrt u(\log u)^{1.55})].
\]

If \(\mu(u)=+1\), this is an opposite-parity token.  If \(\mu(u)=-1\), applying the same
construction at \(u/2\) and adjoining the prime \(2\) gives a squarefree exact-four-prime token
of sign \(+1\) in the same square-root-length range.  The diagonal count used in Corollary F2
removes repeated prime factors.  In the Route E range \(u\le z^2\), the produced prime factors
are at most \(z\) for large \(z\).  Therefore the known all-interval theorem supplies
factorwise square-root-scale parity reversals before spectator multiplication.  This is exactly
the scale which was insufficient for edges but is source-critical for rectangles.

This pointwise observation is not yet `(G64)`.  Four hard gates remain.

1. The two replacement tokens must avoid every prime in the opposite factor and each other, so
   all four corners retain nonzero Möbius coefficient.
2. Pointwise token supply must be promoted to a two-sided fractional rectangle capacity theorem;
   repeated use of one target is charged by \(q(n)\le1\).
3. Integers with a bounded token, and the thin upper strip where a replacement crosses the
   truncation, need a separate first-order or absolute residual of strict-half size.
4. The deterministic negative friable charge forbids covering the friable sector by internal
   rectangles alone.  The cover must include rectangles crossing the zero/one-large-prime seam;
   otherwise it would contradict `(G46j)`--`(G46l)`.

`[CONJECTURE: SECOND-ORDER-WOLD-RECTANGLE-CAPACITY]`  On the critical Route E schedule, the fixed
hypergraph generated by two independent square-root-scale \(E_3/E_4\) token replacements has
nonnegative rectangle weights with vertex load at most one for which the right side of `(G64)` is
\(O_\varepsilon(N^{1/2+\varepsilon})\).  Rectangle admission must be defined before inspecting
the signed total, must retain literal factor coprimality and the zero/one-large-prime boundary,
and must carry the negative zero-large-prime charge and positive one-large-prime charge across
that seam before cancellation.

This is a concrete realization of `DEPTH-ZERO-WOLD-BREADTH-SEAM-ORIENTATION`: each rectangle is
a second exterior difference across two Wold labels, and cofinal capacity uses unbounded breadth
before scalarization.  It is ordinary-integer-specific because the square-root token supply is an
additive short-interval theorem for exact almost primes.  Zhang's arbitrary finite-prefix
Beurling matching does not preserve this co-moving all-scale incidence law.

Hostile audit:

- The analytic inequality alone is not a source; setting the uncovered residual equal to the
  original sum is disallowed.
- Arbitrary four-tuples are disallowed; `(G65)`, coprimality, and factorwise sign reversal are
  mandatory.
- Pointwise \(E_3/E_4\) existence is not a capacity theorem.  A valid proof must control both
  row supply and corner co-degree.
- Sectorwise friable rectangle coverage is false by `(G46j)`--`(G46l)`; cross-seam capacity is
  mandatory.
- No literature collision was found for multiplicative Möbius rectangle transport with the
  mixed exponential cost `(G62)` or its Route E square-root token coupling.  Mixed finite
  differences and almost-prime short-interval supply are classical ingredients; the combined
  source architecture is recorded as candidate project-new knowledge, not as a proved RH source.

- 2026-08-01 — replaced the falsified first-order local-flow geometry by a literal second-order
  multiplicative rectangle law.  Lean proves the sharp no-spectator kernel bound and actual
  Möbius checkerboard packet.  Existing all-interval exact-almost-prime supply has precisely the
  factorwise square-root gap needed by this consumer.  Remaining hard core is now a fixed
  coprime fractional rectangle-capacity theorem crossing the friable/one-large-prime seam, not
  a short-edge matching and not a scalar Lambert inverse.

### Sector-marginal conservation and the required co-moving flux

`[LEAN-PROVED CORRECTION]`  A seam-crossing rectangle does **not** transfer static signed
coefficient mass between the zero- and one-large-prime sectors.  Put

\[
\ell_z(n)=\#\{p\mid n:p>z\}.
\]

For a coprime product this breadth is additive:

\[
\ell_z(ab)=\ell_z(a)+\ell_z(b).                           \tag{G68}
\]

Let \(s_{00},s_{10},s_{01},s_{11}=s,-s,-s,s\) be the four actual Möbius
coefficients of an admitted rectangle.  Additivity gives

\[
\sum_{i,j\in\{0,1\}}(-1)^{i+j}\ell_z(a_i b_j)=0.
\]

If all four corners lie in the zero/one boundary, then
\(\mathbf 1_{\ell_z=1}=\ell_z\) and
\(\mathbf 1_{\ell_z=0}=1-\ell_z\).  Consequently, separately for
\(k=0,1\),

\[
\sum_{\substack{i,j\in\{0,1\}\\ \ell_z(a_i b_j)=k}}
   s_{ij}=0.                                              \tag{G69}
\]

Lean proves `(G68)` from disjoint filtered prime-factor supports and proves both literal
Möbius-sector identities `(G69)` as
`mobiusParityRectangle_zeroLargePrime_cornerSum_eq_zero` and
`mobiusParityRectangle_oneLargePrime_cornerSum_eq_zero`.

This corrects the phrase “rectangles carry the friable bias across the seam.”  They cannot do so
as a static finite coefficient cover.  If a finite vertex set \(V\) contains every corner of
every retained rectangle and \(q(n)\) is its rectangle load, then

\[
\sum_{\substack{n\in V\\\ell_z(n)=k}}\mu(n)q(n)=0
\quad(k=0,1).                                             \tag{G70}
\]

Thus a small uncovered load on such a closed \(V\) would prove a small signed sum in each sector
separately.  Away from an integer delay, this is impossible for the zero sector by `(G46j)`--`(G46l)`.
At the critical \(u\to2\) schedule it would simply hide `OPEN-SOURCE-001` in the unproved
integer-delay boundary correction.

The only surviving rectangle interpretation is **co-moving cutoff flux**.  Rectangles must be
formed on an extended vertex set and their two sectorwise opposite-sign pairs must cross the
moving physical cutoff.  For a sharp cutoff \(X\), define the sector flux of one rectangle by

\[
J_{k,X}(R)=
\sum_{i,j} s_{ij}\,
 \mathbf 1_{\ell_z(a_i b_j)=k}\mathbf 1_{a_i b_j\le X}.
\tag{G71}
\]

Equation `(G69)` makes this exactly minus the complementary outside-corner sum.  After weighting
and aggregation, \(J_{0,X}\) must reproduce the normalized friable charge \(-1\) and
\(J_{1,X}\) the one-large-prime charge \(+1\); only their sum receives the mixed second-order
bound.
This identifies a new mandatory gate:

`[CONJECTURE: CO-MOVING-RECTANGLE-SEAM-FLUX]` Construct a source-fixed, capacity-bounded family
on an extended zero/one-large-prime window whose induced loads cover the effective Gibbs core,
whose outside Gibbs load is strict-half, and whose sector fluxes realize the full integer-delay
boundary correction before their mixed cancellation.  A static sector-closed fractional cover
is disallowed by `(G69)`.

The original `SECOND-ORDER-WOLD-RECTANGLE-CAPACITY` wording is therefore retired unless
“crossing the seam” includes this cutoff-flux condition.  Rank-one incidence plus pointwise
\(E_3/E_4\) supply does not create the flux; proving its capacity is the arithmetic source.

### Full Wold-breadth cube: factorial derivative growth is globally affordable

`[PAPER-PROVED ANALYTIC SURVIVOR; ARITHMETIC CUBE CAPACITY OPEN]`  Rectangles are only the
second exterior face.  For \(r\ge1\), let

\[
F_x(t_1,\ldots,t_r)=\exp(-x t_1\cdots t_r),\qquad
y=x t_1\cdots t_r.
\]

Writing \(S(r,k)\) for a Stirling number of the second kind and

\[
Q_r(y)=\sum_{k=1}^r(-1)^kS(r,k)y^{k-1},
\]

the exact full mixed derivative is

\[
\partial_{t_1}\cdots\partial_{t_r}F_x
   =x e^{-y}Q_r(y).                                      \tag{G72}
\]

Indeed, \(\partial_{t_i}=t_i^{-1}(y\partial_y)\) and the \(r\) distinct reciprocal-coordinate
factors are untouched by the other derivatives, while

\[
(y\partial_y)^r e^{-y}
=e^{-y}\sum_{k=1}^r(-1)^kS(r,k)y^k.
\]

There is a simple global bound with no coordinate spectators:

\[
\sup_{y\ge0}e^{-y}|Q_r(y)|\le r^r.                        \tag{G73}
\]

For \(k\ge1\), \(e^{-y}y^{k-1}\le(k-1)!\).  Moreover
\(k!S(r,k)\le k^r\), since the left side counts surjections from an \(r\)-set to a \(k\)-set.
Thus the \(k\)-th absolute contribution is at most \(k^{r-1}\), and summing over
\(1\le k\le r\) proves `(G73)`.

Repeated one-variable fundamental theorem of calculus now gives the \(2^r\)-corner law

\[
\left|
\sum_{\varepsilon\in\{0,1\}^r}
 (-1)^{|\varepsilon|}
 e^{-x\prod_i t_{i,\varepsilon_i}}
\right|
\le
x r^r\prod_{i=1}^r|t_{i,1}-t_{i,0}|.                    \tag{G74}
\]

If every coordinate replacement reverses Möbius parity and every selected coordinate product is
coprime, `(G74)` is the literal Möbius cube packet.  Factorwise square-root gaps make the product
of displacements \(n^{1/2+o(1)}\).  The apparently dangerous \(r^r\) breadth constant is not an
aggregate obstruction.  If \(A_r(N)\) counts squarefree \(n\le N\) with \(\omega(n)=r\), then

\[
A_r(N)
\le {N\over r!}\left(\sum_{p\le N}{1\over p}\right)^r.
\tag{G75}
\]

This follows by majorizing the \(r\)-th elementary symmetric sum in \(1/p\) by the full ordered
power sum divided by \(r!\).  Since \(r!\le n\le N\) and
\(\sum_{p\le N}1/p=\log\log N+O(1)\),

\[
\sum_{\substack{n\le N\\\mu(n)\ne0}}
 \omega(n)^{\omega(n)}
\le
N\sum_{r! \le N}
 {r^r\over r!}(\log\log N+O(1))^r
=N^{1+o(1)}.                                             \tag{G76}
\]

Here \(r^r/r!\le e^{O(r)}\) and \(r!\le N\) implies
\(r=O(\log N/\log\log N)\), so the last geometric exponent is \(o(\log N)\).
Consequently, even assigning one admitted full-breadth cube to every squarefree \(n\le N\)
has total analytic mixed cost

\[
{1\over N}\sum_{n\le N}
 \omega(n)^{\omega(n)}n^{1/2+o(1)}
=N^{1/2+o(1)}.                                           \tag{G77}
\]

Thus unbounded Wold breadth is analytically compatible with the strict-half target; neither the
\(2^r\) corner count nor factorial-size Touchard derivatives force a loss.  This is the first
mechanism found here that uses every prime-support coordinate and still has the correct global
critical scale.

The hard gate is now genuinely arithmetic:

`[CONJECTURE: COPRIME-WOLD-BLOCK-CUBE-CAPACITY]` Partition each squarefree support into
source-fixed factor blocks and assign opposite-parity \(E_3/E_4\) replacements so that all
corners remain squarefree, at most one corner-coordinate can carry a prime above \(z\), the
replacement blocks are jointly coprime, and a fractional family has vertex load at most one with
strict-half uncovered and outside Gibbs capacity.  The product of block gaps must be
\(n^{1/2+o(1)}\).

The Matomäki--Teräväinen all-interval theorem supplies each block replacement before exclusions.
It does not supply simultaneous avoidance of the other \(O(\omega(n))\) prime supports, nor
incoming-corner co-degree, nor the co-moving seam flux `(G71)`.  Those three properties are the
remaining source theorem.  One-axis binomial incidence splitting remains useful locally, but it
does not prove this cube capacity.

Collision audit found the classical Euler-operator/Touchard identity, standard Stirling and
prime-reciprocal estimates, and the cited almost-prime interval theorems.  No source was found
combining them into the spectator-free multiplicative cube bound `(G74)`, aggregate breadth law
`(G76)`--`(G77)`, or the Route E cube-capacity problem.  The formulas are retained as candidate
project-new synthesis; no RH claim is attached while cube admission and capacity remain open.

- 2026-08-01 — proved and Lean-formalized sector-marginal conservation `(G68)`--`(G69)`.
  Corrected the rectangle source: static seam crossing cannot transport sector coefficient bias;
  only co-moving cutoff flux can.  Derived the all-breadth Touchard cube estimate `(G72)`--`(G74)`
  and proved that its factorial derivative growth aggregates to the strict-half scale
  `(G75)`--`(G77)`.  Remaining frontier is simultaneous coprime block replacement, corner
  co-degree, and integer-delay seam flux—not analytic kernel growth.

### Polynomial-forbidden-support \(E_3\) stability closes finite-block coprimality

`[PAPER-PROVED HERE]`  The simultaneous avoidance clause in
`COPRIME-WOLD-BLOCK-CUBE-CAPACITY` is available for any fixed number of polynomial-scale blocks.
The all-interval proof is stable under an adversarial but multiplicatively bounded forbidden
prime support.

Fix \(B>0\), \(A\le y^B\), and use the Matomäki--Teräväinen Section 7 scales

\[
P_1=(\log y)^{1.1},\qquad
R=\tfrac12\sqrt{y/P_1},\qquad
h=\sqrt y(\log y)^{1.55}.
\tag{G78}
\]

Then the interval \((y,y+h]\) contains

\[
\gg_B {h\over(\log P_1)(\log y)^2}
\tag{G79}
\]

squarefree \(E_3\) numbers coprime to \(A\), with one prime at scale \(P_1\) and two at scale
\(R\).

The hard deletion is the small prime variable.  If
\({\cal S}_1=\{p\mid A:p\asymp P_1\}\) and
\(D_1(s)=\sum_{p\in{\cal S}_1}p^{-s}\), then

\[
\|D_1\|_{\Re s=1,\infty}
\le {\#{\cal S}_1\over P_1}
\ll_B {(\log y)^{-0.1}\over\log\log y}.                  \tag{G80}
\]

Replacing the prime polynomial \(P_1(s)\) in their proof by \(P_1(s)-D_1(s)\) adds at most

\[
2\|D_1\|_\infty^2\int|P(1+it)|^2dt.
\]

Their improved mean-value theorem plus the same two-dimensional upper-bound sieve gives

\[
\int_{T_0}^{T}|P(1+it)|^2dt
\ll {T\over R\log y}+{1\over(\log y)^2}.
\]

For every fixed \(\varepsilon<0.1\), the product with `(G80)` is smaller than the Section 7
target \(T(y/h)^{-1}(\log y)^{-2-2\varepsilon}\).  The deleted long-interval harmonic mass is
only \(O_B((\log y)^{-0.1})\) of the full \(p_1\)-mass.  At either large-factor scale, the product
bound \(A\le y^B\) permits only \(O_B(1)\) forbidden primes.  Fixing one such prime leaves only
\(O(\log y)\) choices for the other large integer per \(p_1\), a total
\(O_B((\log y)^{2.1}/\log\log y)=o((G79))\).  The same estimate removes the diagonal.

Full proof:
`../2-fully-proven/route-e-forbidden-support-e3-stability.md`.

For blocks \(u_i\ge N^\delta\), \(r=O_\delta(1)\), process replacements sequentially and take
the accumulated original/replacement prime support as \(A\).  It is \(u_i^{O_\delta(1)}\), so
`(G78)`--`(G80)` apply.  A positive-parity block uses an \(E_3\) replacement.  A negative-parity
block first chooses a fresh prime \(\ell_i\ll_\delta\log N\) and uses
\(\ell_i E_3(u_i/\ell_i)\), giving a squarefree \(E_4\) replacement.  All block pairs are jointly
coprime and

\[
|Q_i-u_i|
\ll \sqrt{u_i\ell_i}(\log u_i)^{1.55}
=u_i^{1/2}N^{o(1)}.                                      \tag{G81}
\]

Thus simultaneous pointwise cube admission is closed for every fixed balanced block
decomposition.  This does not address how anchored cubes share physical vertex capacity.

- 2026-08-01 — proved forbidden-support stability `(G78)`--`(G81)` by perturbing the published
  Type-II proof rather than postulating spectator uniformity.  Finite-block joint coprimality is
  no longer an open gate.  Remaining hard core: incoming-corner co-degree/fractional capacity and
  co-moving integer-delay seam flux.

### Literal finite rectangle load consumer

`[LEAN-PROVED]`  The formal rectangle theorem no longer leaves the arithmetic residual as an
arbitrary complex number.  For a finite rectangle family with weights \(c_R\), Lean defines the
literal physical corner load

\[
q(n)=\sum_R c_R\#\{(i,j):a_i(R)b_j(R)=n\},
\tag{G82}
\]

counting repeated corners with multiplicity.  If every corner lies in the finite physical vertex
set \(V\), finite regrouping proves exactly

\[
\sum_{n\in V}\mu(n)e^{-nx}
=\sum_Rc_R\,{\cal P}_R(x)
+ \sum_{n\in V}(1-q(n))\mu(n)e^{-nx}.                    \tag{G83}
\]

When \(c_R\ge0\), rectangles are admitted, and \(q(n)\le1\), the sharp packet estimate gives the
fully literal version of `(G64)`:

\[
\left|\sum_{n\in V}\mu(n)e^{-nx}\right|
\le x\sum_Rc_R|\Delta a_R||\Delta b_R|
+ \sum_{n\in V}(1-q(n))e^{-nx}.                          \tag{G84}
\]

Lean theorem
`norm_sum_mobiusRectangleLaplaceAtom_le_secondOrderCost_add_unusedCapacity`
proves `(G84)` unconditionally.  Supporting declarations prove exact regrouping and bound the
literal unused vector.  The source obligation is now syntactically confined to constructing
nonnegative arithmetic weights with small mixed cost and unused load; it cannot be hidden in a
caller-selected residual.

- 2026-08-01 — closed the finite rectangle consumer gap by formalizing literal vertex loads,
  exact packet-plus-unused decomposition, and positive unused-capacity norm bound.  This is
  infrastructure, not a capacity theorem.

### Sharp exceptional-fallback threshold

`[LEAN-PROVED CLASSIFICATION]`  An almost-all short-partner theorem cannot be combined with an
arbitrarily expensive pointwise fallback.  At a block scale \(U\), suppose ordinary centers have
displacement \(U^{\eta+o(1)}\), at most \(U^{1-\kappa+o(1)}\) exceptional centers use fallback
displacement \(U^{\theta+o(1)}\), and balanced products have \(N=U^r\).  The exact one-axis split
is

\[
\sum_{u\asymp U}d(u)
\ll U^{1+\eta+o(1)}+U^{1-\kappa+\theta+o(1)}.             \tag{G85}
\]

The Cartesian \(r\)-axis displacement sum is the \(r\)-th power of `(G85)`, while the number of
tuples is \(U^r\).  Therefore the normalized mixed-cube cost exponent is

\[
\max\{\eta,\theta-\kappa\}.                              \tag{G86}
\]

Consequently the strict-half target requires, sharply,

\[
\eta\le\tfrac12,\qquad
\boxed{\kappa\ge\theta-\tfrac12}.                         \tag{G87}
\]

Matomäki--Radziwiłł's explicit dense exceptional-set estimate, applied to \(\mu\) with
\(h=U^\eta\) and fixed \(0<\delta_0<10^{-3}\), is

\[
E(U)\ll U^{1-\eta\delta_0/15}
       +U^{1-\delta_0^4/10^{16}}.
\tag{G88}
\]

Its usable saving is
\(\kappa=\min\{\eta\delta_0/15,\delta_0^4/10^{16}\}<10^{-28}\).
The all-interval arbitrary-sign Möbius fallback at exponent
\(\theta=0.55+\varepsilon\) needs \(\kappa\ge0.05+\varepsilon\), so this hybrid is
quantitatively impossible.  Increasing Wold breadth does not improve `(G87)`.

Menon's 2026 mean-square improvement gives the Möbius analogue of

\[
{1\over U}\int_U^{2U}
\left|{1\over h}\sum_{x<n\le x+h}\mu(n)\right|^2dx
\ll {(\log\log h)^2\over(\log h)^2}
   +{(\log\log U)^4\over(\log U)^2}.                     \tag{G89}
\]

At a fixed sign-detection threshold this supplies logarithmic exceptional density, hence
\(\kappa=0\) in `(G87)`; it also cannot carry the \(0.55+\varepsilon\) fallback.

The positive survivor is exact: the square-root \(E_3/E_4\) fallback `(G81)` has
\(\theta=\tfrac12+o(1)\), so every positive power saving is analytically sufficient.  Its
remaining gate is not exponent arithmetic but a **local Hall theorem** preventing exceptional
centers from concentrating beyond the physical balanced-token capacity.

Lean module `MobiusExceptionalFallbackThreshold.lean` proves the finite split `(G85)` and both
equivalent forms of `(G87)`.  Full no-go record:
`../5-failed/route-e-almost-all-pointwise-fallback-hybrid.md`.

- 2026-08-01 — retired the \(0.55+\varepsilon\) almost-all/fallback hybrid by the sharp
  exceptional-saving threshold `(G87)`.  Preserved square-root \(E_3/E_4\) fallback as the unique
  exponent-compatible survivor and localized its missing input to anti-concentration/Hall
  capacity, rather than global exceptional cardinality.

### Balanced-token marker entropy cannot create physical capacity

`[PAPER-PROVED NO-GO; LEAN HALL CONSUMER ALREADY AVAILABLE]`  The square-root \(E_3/E_4\)
fallback survives `(G87)`, but the published balanced Type-II slice cannot be promoted to
capacity by attaching many marker labels.  For a marker prime \(\ell\), its physical \(E_4\)
targets at scale \(U\) have the form

\[
q=\ell p_1p_2p_3,\qquad
p_1\asymp(\log U)^{1.1},\qquad
p_2,p_3\asymp\sqrt{\frac{U}{\ell(\log U)^{1.1}}}.
\tag{G90}
\]

Prime upper bounds give, for each fixed \(\ell\),

\[
\#T_\ell(U)
\ll
{U\over
 \ell(\log\log U)(\log U)^2}.                            \tag{G91}
\]

Even after taking every prime marker \(\ell\le U^C\), Mertens' bound yields

\[
\#\bigcup_\ell T_\ell(U)
\le\sum_\ell\#T_\ell(U)
\ll_C {U\over(\log U)^2}.                                \tag{G92}
\]

Prime-coordinate sources number \(\asymp U/\log U\); arbitrary blocks number \(\asymp U\).
Thus marker amplification misses respectively one or two full logarithms of **physical** target
capacity.  Incidence labels cannot repair this: the Lean theorem
`sum_conductance_le_neighborUnionCapacity` bounds total admitted flow by the weight of the
physical neighbor union, irrespective of how many labels represent each target.

Across dyadic scales `(G92)` also implies that balanced marked targets have convergent reciprocal
mass, whereas source primes have divergent reciprocal mass.  Thinning source coordinates to the
available target density therefore leaves a positive-density ordinary-integer sector untouched.

The positive survivor is a precise missing-logarithm gate:

`[CONJECTURE: SQUARE-ROOT-PHYSICAL-HALL-EXPANSION]`  Construct an opposite-parity replacement
relation at scale \(U\) with \(U^{1/2+o(1)}\) displacement whose physical neighbor union has
prime-scale density \(\gg U/\log U\) and satisfies weighted Hall expansion for every source
subset, or construct a higher-order image not confined to a reciprocal-summable token family.
Repeated balanced-factor labels and marker codebooks are disallowed by `(G92)`.

Full no-go record:
`../5-failed/route-e-balanced-e3-marker-capacity.md`.

- 2026-08-01 — proved that balanced \(E_3/E_4\) marker entropy cannot furnish incoming-corner
  capacity: all polynomial-scale prime markers still produce only \(O(U/\log^2 U)\) physical
  targets.  Replaced row-supply language by the exact missing-logarithm/local-Hall gate.

### Cofactor amplification closes conditional global fallback supply

`[PAPER-PROVED; LEAN PARITY/GAP CONSUMER]`  Marker labels fail because their physical harmonic
mass is too small.  Genuine squarefree cofactors do recover one full logarithm.  Fix
\(0<\eta<1/6\), put \(T=U^{2\eta}\), and for a source block \(u\asymp U\) take every squarefree
\(t\le T\) with

\[
\mu(t)=\mu(u).                                            \tag{G93}
\]

Exclude from \(t\) the widened polylogarithmic band used by the small prime in the
Matomäki--Teräväinen construction, apply their theorem at \(y=u/t\), and write its token as
\(m=p_1p_2p_3\).  Then \(p_2,p_3>T\) when \(\eta<1/6\), so \(t\) is coprime to \(m\) and is
uniquely recoverable from the physical product \(q=tm\).  Moreover

\[
\mu(q)=\mu(t)\mu(m)=-\mu(u),                              \tag{G94}
\]

\[
0<q-u
\ll \sqrt{Ut}(\log U)^{1.55}
\le U^{1/2+\eta}(\log U)^{1.55}.                         \tag{G95}
\]

For fixed \(t\) and one distinguished-prime slice, the published quantitative count contributes
\[
\gg {\sqrt{U/t}\over(\log U)^{0.45}\log\log U}
\]
tokens.  The underlying minorant theorem is uniform for
\(a\in[1.1-10^{-4},1.1]\), where \(p_1\asymp(\log(U/t))^a\).  There are
\(\asymp\log\log U\) disjoint dyadic \(p_1\)-slices in that fixed exponent band.  Partition the
common \(a=1.1\) window into each lower slice's natural all-interval windows; their counts then add
as distinct physical integers and cancel the single-slice \(\log\log U\) loss.

Exclude the full \(p_1\)-band from \(t\).  This costs only a fixed Euler factor.  Pairing each odd
allowed squarefree \(s\le T/2\) with \(2s\) gives one cofactor of each parity without using signed
Möbius cancellation.  Consequently the two parity classes satisfy

\[
\sum_{\substack{t\le T\\\mu(t)=\sigma\\t\ {\rm allowed}}}t^{-1/2}
\asymp\sqrt T,
\qquad
\sum_{\substack{t\le T\\\mu(t)=\sigma\\t\ {\rm allowed}}}t^{-1}
\asymp\log T
\quad(\sigma=\pm1).                                      \tag{G96}
\]

Unique factor-range decoding lets these counts add as physical integers, not representations.
Consequently every row has

\[
\#{\cal Q}_\eta(u)
\gg_\eta {U^{1/2+\eta}\over
                 (\log U)^{0.45}},                       \tag{G97}
\]

and disjoint source intervals across one dyadic scale give

\[
\#\bigcup_{u\asymp U}{\cal Q}_\eta(u)
\gg_\eta {U\over\log U}.                                 \tag{G98}
\]

If an independent decomposition genuinely leaves \(U^{1-\kappa+o(1)}\) unmatched exceptional
centers, choose
\(0<\eta<\min\{\kappa,1/6\}\).  Then `(G98)` exceeds their total cardinality, while fallback
exponent \(\theta=\tfrac12+\eta\) satisfies the sharp budget `(G87)` strictly.  The hybrid now
passes both global physical capacity and analytic cost for that fallback subproblem.

What remains in the fallback subproblem is exactly local:

`[CONJECTURE: EXCEPTIONAL-COFACTOR-TOKEN-HALL]`  For the exceptional centers arising from a
fixed almost-all Möbius short-interval theorem, the cofactor-amplified relation `(G93)`--`(G97)`
satisfies weighted Hall expansion for every source subset, with the analogous statement after
the Route E co-moving cutoff.  A global exceptional-set count is insufficient.

Lean module `MobiusCofactorAmplifiedToken.lean` proves `(G94)` and the exact gap-scaling identity
behind `(G95)`.  Full paper proof:
`../2-fully-proven/route-e-cofactor-amplified-e3-token-supply.md`.

- 2026-08-01 — amplified the balanced all-interval \(E_3\) slice by uniquely decoded squarefree
  cofactors.  This recovers one full logarithm of physical capacity, closes total exceptional
  cardinality and strict-half cost simultaneously for every genuine power-saving unmatched set,
  and leaves local Hall anti-concentration for that fallback.
- 2026-08-01 — strengthened cofactor supply by using every disjoint distinguished-prime slice in
  the published uniform \(a\)-interval.  Common-window partitioning removes the fixed-slice
  \(\log\log U\) loss, improving row supply to
  \(U^{1/2+\eta}/(\log U)^{0.45}\) and physical union to \(U/\log U\).  Elementary
  \(s\leftrightarrow2s\) pairing supplies either cofactor parity without importing Möbius
  cancellation.

#### Strict-half ceiling for every single-\(E_3\) pre-cofactor amplification

`[PAPER-PROVED EXHAUSTIVE SUBARCHITECTURE NO-GO]`  The multiband gain is optimal up to the
available small-prime harmonic mass for any construction that scales one balanced \(E_3\) core.
Allow every representation
\[
q=t\,p_1p_2p_3\asymp U,\qquad
t\le T,\quad p_1\le P,\quad
p_2,p_3\asymp\sqrt{U/(tp_1)}.
\]
Strict-half displacement forces \(TP=U^{o(1)}\).  Even before quotienting representation
collisions, the physical target count is bounded by
\[
\#\{q\}
\ll {U\over\log^2U}
    \left(\sum_{t\le T}{1\over t}\right)
    \left(\sum_{p\le P}{1\over p}\right)
\ll {U\log T\,\log\log P\over\log^2U}.                  \tag{G98a}
\]
Since \(\log T=o(\log U)\) and \(\log\log P\le(1+o(1))\log\log U\),
\[
\#\{q\}
=o\!\left({U\log\log U\over\log U}\right).              \tag{G98b}
\]

The right side of `(G98b)` is exactly the ordinary \(L^1\) defect scale permitted by Menon's
sharp mean-square theorem.  The two-phase sequence in `(G115)` attains that defect scale, has
zero total, and still has a Gibbs current of the same order.  Thus Menon input plus any
single-balanced-\(E_3\) pre-cofactor family cannot close ordinary capacity at strict-half cost.
Taking \(T=U^\eta\) restores a full harmonic logarithm only by moving displacement to
\(U^{1/2+\eta}\), which fails the exact threshold at exceptional saving \(\kappa=0\).

This no-go is deliberately narrow but exhaustive within its boundary: additional cofactor
factorizations and marker labels collapse to the same physical product \(t\), and counting
representations in `(G98a)` already favors the proposed construction.  The positive survivors are
the improved exceptional union `(G98)` and the signed cumulative-energy source `(G114)`.
Full record:
`../5-failed/route-e-strict-half-e3-cofactor-capacity-ceiling.md`.

### Forward interval Hall reduces every subset to a Carleson estimate

`[PAPER-PROVED EXACT REDUCTION]`  The remaining local Hall gate is not an unrestricted
hypergraph mystery.  Fix one parity, a source set \(E\subset[U,2U]\), a physical target set
\(T\), and a common forward radius \(H\).  Join \(e\) to \(q\) exactly when
\[
e<q\le e+H,\qquad q\in T.                                \tag{G99}
\]

There is an injective physical token assignment if and only if every integer interval
\(I=[a,b]\) satisfies

\[
\#(E\cap I)\le\#\bigl(T\cap(a,b+H]\bigr).                \tag{G100}
\]

Necessity is Hall's inequality for \(E\cap I\).  Conversely, for an arbitrary \(S\subseteq E\),
decompose \(\bigcup_{s\in S}(s,s+H]\) into disjoint interval components.  One component is
\((a_j,b_j+H]\), its sources lie in \(E\cap[a_j,b_j]\), and its target neighbor set is exactly
\(T\cap(a_j,b_j+H]\).  Apply `(G100)` to each component and sum; Hall's theorem then gives the
injection.

Restrict `(G93)` to cofactors \(t\in[T_0/2,T_0]\), \(T_0=U^{2\eta}\).  Their radii are comparable
to
\[
H=U^{1/2+\eta}(\log U)^{1.55},
\]
and every \(H\)-interval contains
\[
D\gg_\eta
{U^{1/2+\eta}\over(\log U)^{0.45}}                       \tag{G101}
\]
distinct physical targets.  Longer intervals can be partitioned into \(H\)-blocks, so `(G100)`
follows from the explicit Carleson estimate

\[
\#(E_\sigma(U)\cap I)
\ll_\eta
{U^{1/2+\eta}\over(\log U)^{0.45}}
+{|I|\over(\log U)^2}                                    \tag{G102}
\]

with a constant strictly below the target lower-bound constant.  This condition is permissive
below the fallback radius and demands density \(O(1/\log^2U)\) only on longer
intervals.

If one throws away all local information and uses only
\(\#E_\sigma(U)\le U^{1-\kappa+o(1)}\), the trivial estimate
\(\#(E_\sigma\cap I)\le\min\{|I|,\#E_\sigma\}\) can bridge the interval criterion only when

\[
U^{1/2+\eta}\ge U^{1-\kappa+o(1)},
\quad\text{or}\quad
\eta+\kappa\ge\tfrac12.                                  \tag{G103}
\]

Strict-half fallback cost requires \(\eta<\kappa\).  Therefore a cofactor exponent satisfying
both constraints exists exactly when

\[
\boxed{\kappa>\tfrac14}.                                 \tag{G104}
\]

Lean theorem
`exists_cofactorExponent_globalHall_and_strictHalf_iff` proves this phase boundary.  For the
published \(\kappa<10^{-28}\), global exceptional cardinality is not merely quantitatively weak:
it is on the wrong side of the exact quarter threshold.  A local estimate such as `(G102)` is
logically indispensable.

`[CONJECTURE: MOBIUS-EXCEPTIONAL-CARLESON]`  Choose the exceptional centers from a fixed
power-saving almost-all Möbius sign theorem and prove `(G102)` for both parities, uniformly over
all intervals, together with its Gibbs-weighted form after multiplication by admissible
cofactors.  At the Route E cutoff, prove the same inequalities sectorwise on the extended window
so the one-sided assignments produce the two fluxes `(G71)`.

This is the exact arithmetic capacity statement for the exceptional fallback.  Global exceptional
cardinality is only the largest-interval case of `(G102)`; singleton row supply is only its
smallest-interval case.

Full proof of the interval reduction:
`../3-formalized/route-e-forward-interval-hall-reduction.md`.

- 2026-08-01 — collapsed arbitrary-subset Hall verification for one-sided cofactor tokens to the
  exact interval criterion `(G100)`.  Quantitative token supply turns it into
  `MOBIUS-EXCEPTIONAL-CARLESON` `(G102)`, isolating the remaining analytic source as a local
  exceptional-set density theorem rather than an undefined co-degree condition.  Proved the
  sharp quarter-saving boundary `(G104)` separating cases where global cardinality can or cannot
  substitute for local information.

### Almost-all windows leave an ordinary signed defect current

`[LEAN-CERTIFIED NO-GO CORRECTION]`  A published exceptional set of window starts is not a
power-saving set of unmatched Möbius vertices.  Partition a block scale into short windows
\(B_j\), let \(P_j,N_j\) be their positive and negative squarefree counts, and define

\[
d_j=P_j-N_j=\sum_{n\in B_j}\mu(n).                       \tag{G105}
\]

Even with complete-bipartite opposite-sign incidence inside \(B_j\), the exact optimal unused
capacity is

\[
\boxed{|d_j|}.                                           \tag{G106}
\]

Lean theorems
`completeBipartiteProportionalConductance_exact_unused` and
`completeBipartiteProportionalConductance_attains_signedImbalance` prove `(G106)`.

An almost-all theorem at fixed accuracy \(\delta\) says only
\(|d_j|\le\delta|B_j|\) on ordinary windows.  Its direct capacity consequence is

\[
\sum_{j\ {\rm ordinary}}|d_j|\le\delta U,                \tag{G107}
\]

which is linear.  A power-saving number of exceptional windows and the cofactor supply
`(G93)`--`(G102)` do not remove `(G107)`.  Even imposing zero total unweighted defect does not
help: defects \(+\delta h\) on the first half of the scale and \(-\delta h\) on the second have
zero total but an exponentially weighted sum of order \(\delta U\).

The surviving source therefore has two independent obligations:

1. prove `MOBIUS-EXCEPTIONAL-CARLESON` for the genuinely unmatched hard-window component;
2. orient the ordinary signed defect current by

\[
\left|\sum_j d_j e^{-x\xi_j}\right|
\le U^{1/2+o(1)},                                       \tag{G108}
\]

with its sectorwise co-moving cutoff flux.

Taking absolute values in `(G108)` returns `(G107)` and fails.  Treating the \(d_j\) as random
is an additional unproved source.  Equation `(G108)` is the remaining renormalized Möbius law,
not an output of current almost-all theorems.

Full no-go record:
`../5-failed/route-e-almost-all-window-to-vertex-capacity.md`.

- 2026-08-01 — corrected the window/vertex conflation.  Cofactor amplification remains a valid
  conditional fallback theorem, but published almost-all input leaves the exact ordinary defect
  current `(G105)`--`(G108)`.  Route E is not reduced to exceptional Hall alone.

### Exact compression and the cumulative-defect energy source

`[PAPER- AND LEAN-PROVED REDUCTION]`  The ordinary defect current is not a lossy proxy.  Partition
a dyadic shell into consecutive blocks \(B_j\) of width at most \(h\), put
\(\xi_j=\min B_j\), and retain \(d_j\) from `(G105)`.  For \(x\ge0\),

\[
\left|
\sum_{U<n\le2U}\mu(n)e^{-xn}
-\sum_jd_je^{-x\xi_j}
\right|
\le xh\sum_{U<n\le2U}e^{-x\xi_{j(n)}}.                  \tag{G109}
\]

At \(x\asymp U^{-1}\), the right side is \(O(h)\).  Hence every
\(h\le U^{1/2+o(1)}\) partition preserves the critical Route E bound.  Lean theorem
`norm_atom_sum_sub_blockDefectCurrent_le` proves `(G109)` for arbitrary complex coefficients of
norm at most one, after
`sum_atom_eq_sum_blockDefect_mul_weight` proves exact fiber regrouping.

Now let
\[
D_j=\sum_{i\le j}d_i.                                   \tag{G110}
\]
Discrete Abel summation gives
\[
\sum_{j=0}^{N}d_jw_j
=D_Nw_N+\sum_{j<N}D_j(w_j-w_{j+1}),                    \tag{G111}
\]
and finite Cauchy--Schwarz gives
\[
\left|\sum_{j=0}^{N}d_jw_j\right|
\le |D_N||w_N|
+\left(\sum_{j<N}D_j^2\right)^{1/2}
 \left(\sum_{j<N}(w_j-w_{j+1})^2\right)^{1/2}.           \tag{G112}
\]
For \(w_j=e^{-x\xi_j}\) on a monotone mesh of width \(h\),

\[
\sum_{j<N}(w_j-w_{j+1})^2
\le(xh)^2\sum_{j<N}e^{-2x\xi_j}
\ll {h\over U}.                                         \tag{G113}
\]

Use global cumulative defects \(D_j=M(\xi_{j+1})\) and send the terminal endpoint to infinity;
the exponential kills it using only \(|M(y)|\le y\).  Equations `(G111)`--`(G113)` identify the
exact quadratic source law

\[
\boxed{\quad
\sum_{\xi_j\in[U,2U]}M(\xi_j)^2
\le {U^{2+o(1)}\over h}.
\quad}                                                   \tag{G114}
\]

Summing dyadic shells shows `(G114)` implies the \(U^{1/2+o(1)}\) Gibbs current. At the critical
mesh \(h=U^{1/2+o(1)}\), it asks for energy \(U^{3/2+o(1)}\) across
\(U^{1/2+o(1)}\) endpoints. A previous draft incorrectly inferred that an actual Mertens sample
could then be \(U^{3/4+o(1)}\). Since \(|M(n+1)-M(n)|\le1\), a height-\(A\) spike persists across
\(\gg A/h\) mesh points and costs \(\gg A^3/h\); `(G114)` instead gives
\(A\le U^{2/3+o(1)}\). Blockwise interpolation also gives
\[
\sum_{U<n\le2U}M(n)^2
\le 2h\sum_jM(\xi_j)^2+O(Uh^2)
\le U^{2+o(1)}.
\tag{G114a}
\]
Thus `(G114)` is an exact Gibbs-facing discretization of the classical all-\(\varepsilon\)
Mertens mean-square RH criterion, not an independently weaker arithmetic source. Full proof and
novelty correction:
`../3-formalized/not_new_scientific_knowledge/route-e-mesh-energy-classical-mean-square-bridge.md`.

This exposes the missing low-frequency object precisely.  Menon's mean-square theorem controls
one-block increments \(d_j\); `(G114)` controls the quadratic energy of their cumulative walk.
No Poincaré inequality can remove the low-frequency mode without an additional mean/endpoint
input.  The two-phase hostile sequence following `(G107)` has small increments and zero terminal
sum but macroscopic cumulative energy.  In fact, for \(m\) defects \(+A\) followed by \(m\)
defects \(-A\), its geometric current \(S_m(r)\) obeys the exact law

\[
S_m(r)(1-r)=A(1-r^m)^2.                                 \tag{G115}
\]

Taking \(A=\delta h\), \(r=e^{-xh}\), \(m\asymp U/h\), and \(x\asymp U^{-1}\) gives
\(S_m(r)\asymp\delta U\).  Lean theorems `twoPhase_zeroTotal` and
`twoPhase_geometricCurrent_transfer` certify both zero total and `(G115)`.  Thus published
almost-all input does not imply `(G114)`.

The same energy coordinate sharpens co-moving seam flux.  Order an extended rectangle sector's
loaded coefficients as \(c_{k,j}\) on the physical mesh and put
\[
J_{k,j}=\sum_{i\le j}c_{k,i}.                            \tag{G116}
\]
Static sector-marginal conservation `(G69)` gives
\(\sum_jc_{k,j}=0\).  Therefore discrete Abel summation has no terminal term:
\[
\sum_jc_{k,j}e^{-x\xi_j}
=\sum_{j<N}J_{k,j}
  \left(e^{-x\xi_j}-e^{-x\xi_{j+1}}\right).              \tag{G117}
\]
At a sharp cutoff \(\xi_j\le X<\xi_{j+1}\), \(J_{k,j}\) is exactly the aggregated flux
`(G71)`.  Hence the analytic part of `CO-MOVING-RECTANGLE-SEAM-FLUX` is the sectorwise energy law
\[
\sum_{\xi_j\in[U,2U]}J_{k,j}^2
\le {U^{2+o(1)}\over h},\qquad k=0,1.                   \tag{G118}
\]
Together with `(G113)`, `(G118)` gives strict-half weighted sector currents.  It does not create
the rectangle cover or Hall capacity: those remain arithmetic obligations.  Lean theorems
`sum_range_mul_eq_sum_prefix_mul_sub_of_total_eq_zero` and
`abs_exp_zeroTotalSectorFluxCurrent_le_prefixEnergy` prove `(G117)` and its exact Gibbs bound.

Thus ordinary defect orientation and co-moving seam orientation are not two unrelated analytic
conjectures.  Both are instances of cumulative prefix energy; sector conservation removes the
endpoint only in the extended rectangle case.

#### Exact spectral wall for local mean square plus all-interval cancellation

`[LEAN-CERTIFIED HOSTILE INPUT MODEL]`  The two strongest unconditional short-interval inputs do
not combine coefficient-blindly into `(G114)`.  Take block width \(h=U^\beta\), number of blocks
\(N=U^{1-\beta}\), and an all-interval exponent \(\theta>\beta\).  Put
\[
L(U)={\log\log U\over\log U},\quad
K\asymp U^{1-\theta},\quad
z=e^{2\pi iK/N},\quad
d_j=hL(U)z^j.                                           \tag{G119}
\]
Choose \(K\) integral with \(z^N=1\), \(z\ne1\).  Then
\[
\sum_{j<N}d_j=0,\qquad
\sum_{j<N}|d_j|^2=UhL(U)^2,                             \tag{G120}
\]
exactly the Menon block-energy scale.  Every consecutive sum is at most
\[
{2hL(U)\over|1-z|}
\asymp U^\theta L(U)=o(U^\theta),                       \tag{G121}
\]
so the mode also passes an all-interval \(o(H)\) theorem at physical length \(H\ge U^\theta\).

For Gibbs ratio \(r=e^{-xh}\), \(x\asymp U^{-1}\), the exact transfer function is
\[
\left(\sum_{j<N}hL(U)(rz)^j\right)(1-rz)
=hL(U)\left(1-(rz)^N\right).                            \tag{G122}
\]
Since \(|1-rz|\asymp K/N\) and \(r^N\asymp e^{-1}\), the current in `(G122)` is
\[
\asymp hL(U){N\over K}=U^\theta L(U).
\]
A phase-rotated real part gives the same obstruction with real defects.  Lean theorems
`geometricDefectMode_zeroTotal` and `geometricDefectMode_weighted_transfer` prove the exact
algebraic identities.

Equivalently, its cumulative energy is
\[
U^{1+2\theta-\beta}L(U)^2;
\]
multiplication by the Gibbs gradient scale \(U^{\beta-1}\) and square roots returns exponent
\(\theta\), independent of block width.  Therefore local mean square plus an all-interval
exponent \(\theta\) reaches critical current only if \(\theta\le1/2\).  Current unconditional
\(\theta>0.55\) technology is pinned at \(U^{0.55+o(1)}\); logarithmic improvements cannot cross
the wall.

Full no-go and positive survivor:
`../5-failed/route-e-local-mean-square-all-interval-spectral-split.md`.

Lean module `MobiusBlockDefectEnergy.lean` proves `(G111)`--`(G113)` unconditionally.  Full proof:
`../3-formalized/route-e-block-defect-energy-reduction.md`.

`[BRIDGE / RH-BEARING SOURCE RESTATEMENT: MOBIUS-CRITICAL-MESH-ENERGY]`  Prove `(G114)` uniformly on a nested
square-root-width mesh, together with the sectorwise co-moving version whose terminal boundary
is the pair of seam fluxes `(G71)`.  This is the positive source invariant surviving the
almost-all-window no-go; it is not implied by total defect variation or exceptional-window
counts. Equation `(G114a)` and the existing Mertens mean-square criterion show that it is not a
new producer. The live conjecture must additionally name an ordinary-integer Wold-breadth law
that excludes the zero and coherent near-zero modes.

- 2026-08-01 — proved exact critical block compression and its discrete Abel/Cauchy energy law.
  Replaced vague ordinary “defect-current cancellation” by explicit cumulative energy `(G114)`.
  Subsequent bounded-increment audit corrected the false \(U^{3/4}\) spike claim, proved the
  \(U^{2/3}\) ceiling and `(G114a)`, and reclassified the mesh law as a classical-mean-square
  bridge rather than a new source. The strict separation of increment estimates from coherent
  low-frequency energy remains valid.

## Coprime square-root product-sign law and prime-anchor multiplicity barrier

`[PAPER-PROVED / FINITE SKELETON LEAN-PROVED]`  Matomäki--Radziwiłł's all-interval bilinear
theorem can be applied separately to \(\mu\) and \(\mu^2\), but Möbius requires a coprimality
extraction absent from their completely multiplicative sign corollary.  If
\(h/\log\log x\to\infty\), then for each \(\varepsilon\in\{-1,+1\}\),
\[
\#\left\{\begin{array}{c}
x\le n_1n_2\le x+h\sqrt x,\ \sqrt x\le n_1\le2\sqrt x,\\
\mu^2(n_1)=\mu^2(n_2)=1,\ (n_1,n_2)=1,\
\mu(n_1)\mu(n_2)=\varepsilon
\end{array}\right\}
\ge
\left(D^2\left(\frac12-A\right)+o(1)\right)h\sqrt x\log2,
\tag{G123}
\]
where \(D=6/\pi^2\) and \(A=\sum_p(p+1)^{-2}<13/36<1/2\).

For fixed \(p\), scaling \(n_i=pm_i\) and applying the same bilinear theorem to
\(\mu^2(m)\mathbf1_{p\nmid m}\) gives exact shared-\(p\) density
\(D^2/(p+1)^2\).  The infinite-prime tail is uniform because
\[
\#\{p\mid n_1,n_2\}
\le
\left(\frac{\sqrt x}{p}+1\right)\left(\frac hp+1\right),
\]
and \(h/\log\log x\to\infty\).  Thus every interval
\([x,x+h\sqrt x]\) contains both nonzero Möbius signs.  Full proof and novelty audit:
`../2-fully-proven/new_scientific_knowledge/route-e-coprime-square-root-mobius-product-sign-law.md`.

This closes all-interval coprime **representation** supply, not physical Hall capacity.  The
obvious collision-perfect weight is terminally circular: for squarefree \(m\),
\[
\sum_{d\mid m}2^{-\omega(m)}=1,\qquad
\sum_{d\mid m}2^{-\omega(m)}\mu(d)\mu(m/d)=\mu(m).       \tag{G124}
\]
Hence full Boolean factor-split normalization pushes forward to the original Möbius coefficient.
Balanced restriction avoids `(G124)` but a weight strong enough to cap every representation has
signal \(\asymp1/\log x\), below the published bilinear theorem's uniform
\((\log x)^{-1/100}\) error.  `MobiusCoprimeProductSignExtraction.lean` formalizes the exact
both-sign-minus-bad-mass inequality and both Boolean pushforward identities unconditionally.

The sharpened prime-anchor gate is now:

`MOBIUS-PRIME-ANCHOR-PHYSICAL-HALL` — convert `(G123)` into
\(\gg H/\log U\) distinct positive-Möbius targets in every relevant one-sided interval, or prove
the corresponding Hall expansion directly, without invoking `(G124)`.  Prime-corner
factorization rigidity prevents higher Wold breadth from diluting this one-dimensional gate.

## Reciprocal marker primes close the prime-anchor Hall gate

`[PAPER-PROVED / FINITE SKELETON LEAN-PROVED]`  The missing physical multiplicity bound does
not require quotienting the balanced representations in `(G123)`.  Fix
\[
\frac12<\beta<1,\qquad
h(X)=\exp((\log X)^\beta),\qquad H(X)=\sqrt X\,h(X).
\tag{G125}
\]
For every fixed \(C>0\) and either \(\sigma\in\{-1,+1\}\), every sufficiently large physical
interval satisfies
\[
\#\{X<n\le X+H(X):\mu(n)=\sigma\}
\ge C\,\frac{H(X)}{\log X}.                             \tag{G126}
\]
The constant may be made arbitrarily large because it is produced by an arbitrarily large but
fixed number of disjoint marker blocks, not hidden in asymptotic notation.

The construction is reciprocal.  Put \(N=\sqrt X\).  In marker block \(k\), take primes
\[
2^kN<p\le2^{k+1}N,\qquad
t_p=\lfloor X/p\rfloor,\qquad
L_k=\lfloor h(X)/2^{k+2}\rfloor.                        \tag{G127}
\]
Menon's unconditional Möbius mean square implies that all but \(o(N/\log N)\) starts in the
cofactor range have both Möbius signs on \((t,t+L_k]\).  The decisive exponent is
\[
\frac{(\log\log L_k)^2}{(\log L_k)^2}
+\frac{(\log\log N)^4}{(\log N)^2}
=o(1/\log N),                                           \tag{G128}
\]
which uses \(\beta>1/2\).  The reciprocal map \(p\mapsto\lfloor X/p\rfloor\) has
\(O_k(1)\) fibres, so its prime samples cannot concentrate in that exceptional set.
An elementary truncated square-divisor argument separately shows that all but
\(o(N/\log N)\) cofactor intervals contain \(\gg L_k\) squarefree integers.  Therefore every
good marker has \(\gg L_k\) cofactors of either sign.

For a negative cofactor \(a\),
\[
X<ap\le X+pL_k\le X+H(X),\qquad \mu(ap)=+1.             \tag{G129}
\]
Moreover \(p>N>a\).  If \(ap=a'p'\) are two constructed products, primality forces
\(p\mid a'\) or \(p=p'\); the first is impossible, so \(p=p'\) and \(a=a'\).  Physical products
are therefore uniquely decoded.  Each fixed marker block contributes
\(\gg H(X)/\log X\) distinct targets, and the blocks add.  Positive cofactors give the negative
target version.

Brun--Titchmarsh bounds source primes in the same interval by
\[
\pi(X+H)-\pi(X)
\le (4+o(1))H/\log X.                                  \tag{G130}
\]
Taking enough fixed marker blocks makes `(G126)` dominate `(G130)`.  Matching independently
inside consecutive \(H\)-cells gives a literal prime-to-positive-Möbius injection with
displacement \(X^{1/2+o(1)}\) and normalized aggregate Gibbs cost
\[
\ll H(X)/\log X=X^{1/2+o(1)}.                           \tag{G131}
\]
Thus `MOBIUS-PRIME-ANCHOR-PHYSICAL-HALL` is closed unconditionally.

The companion all-breadth obstruction is also now quantitative.  If a multiplicative cube has
prime base corner \(p\), at least two active positive axes, and its opposite corner lies below
\(p+H\) with \(3H\le p\), then
\[
p\le3\prod_i |b_i-a_i|.                                \tag{G132}
\]
Indeed the base factorization has one coordinate \(p\) and only unit coordinates elsewhere.
Changing an auxiliary unit makes its opposite endpoint at least two; the nearby product then
forces the prime-axis gap to be at least \(p/3\).  Thus a genuine multi-axis prime packet has
order-one Gibbs cost.  Affordable prime transport is exactly the one-dimensional Hall problem
closed above.

Full proof and novelty audit:
`../2-fully-proven/new_scientific_knowledge/route-e-reciprocal-marker-mobius-hall-law.md`.
Lean module `MobiusReciprocalMarkerPrimeCapacity.lean` proves the exact finite window, sign,
unique-decoding, arbitrary-breadth prime-corner, and linear mixed-displacement theorems.

This is genuine frontier movement but not `OPEN-SOURCE-001`: the remaining composite sector has
positive density, whereas `(G126)` gives arbitrarily large fixed multiples of \(H/\log X\), still
\(o(H)\).  The live hard core is composite cube capacity plus the
`MOBIUS-EXCEPTIONAL-CARLESON` co-moving seam law.

## Growing reciprocal blocks close every fixed lower-tail Wold breadth

`[PAPER-PROVED / FINITE SKELETON LEAN-PROVED]`  The fixed-\(K\) restriction in
`(G125)`--`(G131)` is not sharp.  Let \(h=h(X)\), \(H=\sqrt Xh\), and choose \(w=w(X)\) with
\[
\log h=o(\log X),\qquad
\sqrt{\log X}(\log\log X)^2=o(w),\qquad
w=o(\log h).
\tag{G133}
\]
Retain every marker block
\[
1\le k\le
K=\left\lfloor{\log h-w\over\log2}\right\rfloor-4.
\tag{G134}
\]
The shortest cofactor interval has \(\log L_k\ge w+O(1)\), while its start scale still has
\(\log A_k=(1/2+o(1))\log X\).  Hence Menon's error is uniformly \(o(1/\log X)\).

The reciprocal fibre is no longer \(O(1)\): at block \(k\),
\[
\#\{p:\lfloor X/p\rfloor=t\}\ll4^k.
\tag{G135}
\]
But the bad-start population is \(o(A_k/\log X)\) with \(A_k\asymp2^{-k}\sqrt X\), so `(G135)`
discards only
\[
4^k\,o(A_k/\log X)
=o(2^k\sqrt X/\log X),
\tag{G136}
\]
smaller than the dyadic marker-prime population.  The independent squarefree-tail exceptional
set is \(O(A_k/\sqrt{L_k}+\sqrt{A_k})\) and obeys the same bound under `(G133)`.
Every block therefore still contributes \(\gg H/\log X\) distinct targets of either sign, and
the \(K\asymp\log h\) blocks add:
\[
\boxed{\quad
\#\{X<n\le X+H:\mu(n)=\sigma\}
\gg {H\log h\over\log X},
\qquad \sigma=\pm1.
\quad}
\tag{G137}
\]

Take
\[
h(X)=\exp\!\left({\log X\over\log\log X}\right),
\qquad w(X)=(\log X)^{2/3}.
\tag{G138}
\]
Then `(G137)` supplies \(\gg H/\log\log X\) physical targets of each sign in every \(H\)-cell.

This density closes far more than fixed Wold breadth.  For fixed \(0<c<1\), Shiu's
short-interval bound applied to \(z^{\omega(n)}\), optimized at \(z=c\), gives
\[
\#\{X<n\le X+H:\mu(n)\ne0,\ \omega(n)\le c\log\log X\}
\ll_c
H(\log X)^{-I(c)},
\quad
I(c)=1-c+c\log c>0.
\tag{G139}
\]
The right side is \(o(H/\log\log X)\).  Delete every low-breadth vertex from the target
reservoirs; enough targets of both signs remain to pair every low-breadth vertex inside its
\(H\)-cell with a distinct opposite-sign vertex outside the low-breadth set.  Across a dyadic
shell the first-order Gibbs cost is
\[
x\cdot O(X)\cdot H=O(H)=X^{1/2+o(1)}.
\tag{G140}
\]

Thus the prime anchor was not an isolated sparse victory: every fixed lower deviation from normal
Wold breadth is now unconditionally transported.  A symmetric Chernoff audit also removes every
fixed upper deviation.  For fixed \(c_+>1\), Shiu applied to
\(c_+^{\omega(n)}\) gives
\[
\#\{X<n\le X+H:\omega(n)\ge c_+\log\log X\}
\ll_{c_+}H(\log X)^{-I(c_+)},
\quad I(c_+)=1-c_++c_+\log c_+>0.
\tag{G139a}
\]
The same \(H/\log\log X\) opposite-sign reservoirs therefore transport the union of any fixed
lower and upper breadth tails.  The remaining physical cube-capacity source is confined to exact
normal order:
\[
\frac{\omega(n)}{\log\log n}\longrightarrow1
\tag{G141}
\]
plus the sectorwise co-moving seam flux.  It is still positive density and is not
`OPEN-SOURCE-001`.

Full dependency-closed proof and novelty audit:
`../2-fully-proven/new_scientific_knowledge/route-e-growing-reciprocal-marker-low-breadth-transport.md`.
Two-sided extension:
`../2-fully-proven/new_scientific_knowledge/route-e-two-sided-off-normal-wold-breadth-transport.md`.
Lean rate certificate:
`MobiusWoldBreadthTwoSidedDeviationRate.lean`.

- 2026-08-01 — removed the fixed-block ceiling from reciprocal-marker transport.  The exact
  \(4^k\) fibre growth cancels against the \(2^{-k}\) cofactor-scale exceptional count, giving
  \(H\log h/\log X\) distinct targets.  At the near-maximal subpower schedule this is
  \(H/\log\log X\).  Combining it with Shiu's optimized lower-tail law closes every
  \(\omega(n)\le c\log\log n\), \(c<1\), sector at strict-half cost.  Remaining capacity is now
  normal-order/high Wold breadth, not all composites.
- 2026-08-01 — applied the same fixed-tilt Shiu argument above normal order.  Both fixed breadth
  tails are \(o(H/\log\log X)\), so the reciprocal-marker reservoir transports their union.
  Remaining physical capacity is confined to \(\omega(n)/\log\log n\to1\), not the upper tail.

## Central normal-order audit: fixed Wold moments are parity-blind

`[PAPER- AND LEAN-PROVED NO-GO / POSITIVE CLASSIFICATION]`  The two-sided marker theorem leaves
only \(\omega(n)/\log\log n\to1\).  Finite Wold-moment closure nevertheless cannot orient this
central band.  For fixed \(d\), put \(n=d+1\), choose any central layer \(r\), and define
\[
c_k=(-1)^{n-k}\binom nk,\qquad 0\le k\le n.             \tag{G142}
\]
For every polynomial \(P\) with \(\deg P\le d\),
\[
\sum_{k=0}^n c_kP(r+k)=0,                              \tag{G143}
\]
because this is \(\Delta^nP(r)\).  Möbius parity behaves oppositely:
\[
\sum_{k=0}^n c_k(-1)^{r+k}
=(-1)^{n+r}2^n\ne0.                                   \tag{G144}
\]
Splitting positive and negative coefficients and normalizing by \(2^{n-1}\) gives two positive
probability measures on the same \(n+1\) adjacent breadth layers.  They have identical moments
through degree \(d\), but their parity expectations are exactly \(+1\) and \(-1\).

Taking \(P=1\) in `(G143)` gives zero total packet mass.  The source-horizon paper's bounded
label-blind factorization law therefore kills this packet after breadth fusion, whereas `(G144)`
detects it maximally.  This is a literal Route E separation defect, not an analogy: parity must be
read while adjacent Wold labels remain distinct.

This obstruction is sharp in polynomial order.  Any polynomial agreeing with parity on
\(n+1\) consecutive layers has degree at least \(n\), since otherwise `(G143)` would make its
packet response zero while `(G144)` makes it nonzero.  Lagrange interpolation supplies degree at
most \(n\).  Exact polynomial parity reading therefore costs order exactly equal to resolved
breadth width.  Moreover
\[
\sum_{k=0}^n c_k(r+k)^n=n!,                            \tag{G145}
\]
so after normalizing the two sign measures and the breadth coordinate by \(L\), any degree-\(n\)
reader returning parity must have leading coefficient
\[
|a_n|={2^nL^n\over n!}\ge2^n\qquad(n\le L).             \tag{G146}
\]
The surviving growing-order moment source is therefore exponentially ill-conditioned in breadth
resolution, exactly the singular/nonclosable category selected by the updated source law.  But it
is not over budget.  For a diagonal central window \(n=o(L)\), Stirling gives
\[
\log {2^nL^n\over n!}
=n\log {2eL\over n}+O(\log n)=o(L),
\tag{G147}
\]
so the exact conditioning is \((\log X)^{o(1)}=X^{o(1)}\).  A cofinally growing Wold reader is
therefore topologically singular yet quantitatively compatible with strict-half Gibbs capacity.
Conditioning alone cannot retire this survivor.  But its first breadth seam is rigid.  If a
degree-\(n\) polynomial \(Q\) agrees with parity on \(r,\ldots,r+n\), then
\[
Q(r+n+1)
=(-1)^{r+n+1}(1-2^{n+1}),                              \tag{G148}
\]
so its adjacent-layer error is exactly
\(-(-1)^{r+n+1}2^{n+1}\).  A single global moment interpolant is therefore closed.  Local patching,
however, has no interior scalar seam: \(Q_r\) and \(Q_{r+1}\) both equal parity on their \(n\)
common integral layers.  Their polynomial extensions differ exactly by the rank-one channel
\[
Q_{r+1}(t)-Q_r(t)
={(-1)^{r+n+1}2^{n+1}\over n!}
  \prod_{j=1}^n(t-r-j).                                \tag{G149}
\]
On integral exterior layers,
\[
\prod_{j=1}^n(t-r-j)
=n!\binom{t-r-1}{n},                                  \tag{G150}
\]
Moreover adjacent transitions form an exact additive coboundary:
\[
\sum_{j=0}^{m-1}\bigl(Q_{r+j+1}-Q_{r+j}\bigr)
=Q_{r+m}-Q_r.                                          \tag{G151}
\]
Every internal scalar seam therefore cancels algebraically; only endpoint readers survive a
finite patch chain.  This corrects the earlier conjectural status of seam cancellation.
Equation `(G150)` interfaces with the existing binomial incidence lift, but representation labels
still cannot increase physical Hall capacity.  Remaining problem is not polynomial gluing: it is
realization of retained labels by a physical ordinary-integer relation, together with the
independent integer-delay cutoff flux.

`[CONJECTURE: SOURCE-POINTED-BIFILTERED-CENTRAL-HALL]`  Let
\(L=\log\log X\).  Choose source-defined breadth patches of width \(n(X)=o(L)\) covering the
remaining \(\omega=(1+o(1))L\) sector, with a nonnegative partition of unity supported inside the
patches.  Retain the paired source grade
\[
\bigl(\omega(n),\,M(n)=\max_pv_p(n)\bigr)
\]
and the physical integer identifier throughout; neither marginal multiset nor any one-parameter
additive compression is admissible under the updated source-horizon rank-two theorem.  On each
patch use the unique degree-\(n\) parity reader and the proved coboundary `(G151)`.  Construct,
from ordinary factorization/additive/co-Poisson data fixed before any partial sum or divisor is
observed, a physical fractional cube relation \(R_X\) such that:

1. integer row load and incoming corner co-degree are at most one after normalization;
2. for every \(H=X^{1/2+o(1)}\) cell and every integer interval
   \(I=[a,b]\) inside it, central unmatched source load in \(I\) is at most capacity of its
   **physical** opposite-parity neighbor set in \((a,b+H]\), i.e. exact interval Hall criterion
   `(G100)` holds for \(R_X\);
3. the same source-pointed relation realizes the normalized friable/one-large-prime cutoff flux
   `(G71)` rather than conserving both sectors separately;
4. outer breadth-patch endpoints land in fixed off-normal sectors already covered by
   `(G139)`--`(G140)`, and total mixed displacement has Gibbs cost \(X^{1/2+o(1)}\).

Condition 2 is a concrete expansion theorem for a predeclared physical relation, not the
RH-bearing prefix-energy bridge `(G114)` and not a restatement in terms of \(M(x)\).  The
conjecture is false if incidence labels are counted without physical normalization, if two source
grades are unpaired, if one global interpolant is used, or if `(G151)` is replaced by
absolute-value seam counting.  Its new content is local Hall anti-concentration for actual
central ordinary integers jointly with the integer-delay cutoff seam; polynomial patch
compatibility is now proved.

Thus no fixed finite panel of polynomial Wold statistics can distinguish the literal squarefree
Möbius sign, even after localization to consecutive normal-order layers.  A surviving breadth
source must have order growing cofinally with the aperture, retain an exact non-polynomial parity
coordinate, or be singular/relation-valued before scalarization.  This theorem is an
information-source no-go, not an arithmetic cancellation estimate.

Full proof:
`../2-fully-proven/new_scientific_knowledge/route-e-central-wold-finite-moment-parity-blindness.md`.
Lean:
`MobiusWoldFiniteMomentParityBlindness.lean`.

## Explicit grade-recurrent entropy-spread relation

`[PAPER-PROVED RELATION / ROW ADMISSION / MIXED COST / SEAM ADMISSION; PHYSICAL CAPACITY OPEN]`

The formula-less relation in `SOURCE-POINTED-BIFILTERED-CENTRAL-HALL` is now replaced by one exact
source-predeclared hypergraph.  Put

\[
 L=\log\log X,\quad k=\lfloor\sqrt L\rfloor,\quad
 Y=\exp((\log X)^{1/3}),\quad
 W=\exp(\exp\sqrt L),\quad Z=X^{1/L^2},
\]

and let (\mathcal P_X) be the primes in ((W,Z]).  For central squarefree (n), split its ordered
prime factors into consecutive blocks (u_i) of breadth (k_i\asymp\sqrt L).  Define, before any
reservoir choice,

\[
 I(n)=\{i:u_i\ge YZ^{k_i-2}\},\qquad a(n)=\prod_{i\notin I(n)}u_i=X^{o(1)}.
\]

Enumerate (I(n)=\{i_1<\cdots<i_d\}), put

\[
 \sigma_{i_j}=(-1)^{j+1},\qquad b_{i_j}=k_{i_j}-3+\sigma_{i_j},
\]

and include **every** pairwise-disjoint allocation (R_i\subset\mathcal P_X\setminus\operatorname{supp}n)
with (\#R_i=b_i).  Set (t_i=\prod_{p\in R_i}p).  Sparse-forbidden structured-(E_3) stability gives
pairwise coprime (m_i) with

\[
 {u_i\over t_i}<m_i\le {u_i\over t_i}
   +\sqrt{u_i/t_i}(\log u_i)^{1.55},\qquad q_i=t_im_i.
\]

The physical cells are

\[
 v_S=a\prod_{i\in S}q_i\prod_{i\in I\setminus S}u_i,qquad S\subseteq I.
\]

Call their family (R_X^{\rm gr}).  It is fixed by ordinary factorization, (X), prime order, the
annular pool, and the structured-(E_3) ranges; it does not inspect (M(X)), a block defect, an
exceptional sign, or a divisor observation.

The following are now paper theorems.

1. (\mu(v_S)=(-1)^{|S|}\mu(n)) and
   (\omega(v_S)=\omega(n)+\sum_{i\in S}\sigma_i).
2. Full-terminal grade drift is exactly zero or one; all corners remain central.
3. Every row exists after (O(L)) adversarial prime exclusions, and all corners have scale
   (v_S/n=1+o(1)).
4. Per-cube mixed Gibbs cost is (X^{-1/2+o(1)}), hence (O(X)) anchored rows cost
   (X^{1/2+o(1)}).
5. At the critical prime aperture, every replacement is smooth and the block containing a unique
   large source prime is forced active.  That coordinate has exact sector law (1\to0).
6. Deterministic least-prime reservoirs fail: a fixed active reservoir packet divides every full
   terminal on an (X^{1-o(1)}) anchor class.
7. Any pool forcing (K) primes into every terminal has physical capacity at most
   \[
   O(X)\,{S(\mathcal P)^K\over K!},\qquad S(\mathcal P)=\sum_{p\in\mathcal P}{1\over p}.
   \]
   Thus every polylogarithmic pool is dead.  The annulus above has
   (S(\mathcal P_X)=L-2\log L-\sqrt L+O(1)) while total reservoir product is (X^{O(1/L)}).
8. Weighting allocations by (1/T) has a source-uniform normalizer: for every deleted source
   support (O) of size at most (2L) and (m\le2L),
   \[
   e_m((1/p)_{p\in\mathcal P_X\setminus O})
   ={S(\mathcal P_X)^m\over m!}(1+o(1)).
   \]

The finite physical harmonic-capacity theorem is Lean-proved in
`RHTower/Sieve/HarmonicReservoirCapacity.lean` and wired into the `RHTower` umbrella.  It counts
physical integers, not labels.

`[CONJECTURE: ENTROPY-SPREAD-GRADE-RECURRENT-CUBE-CAPACITY]`  On the fixed relation
(R_X^{\rm gr}), choose nonnegative cube weights, source-first, such that:

1. every physical corner has incoming load at most one and uncovered central Gibbs load is
   (X^{1/2+o(1)});
2. every physical subinterval satisfies interval Hall expansion for the actual opposite-parity
   corner union;
3. endpoint truncation of the exact seam coordinate realizes the normalized friable (-1) and
   one-large-prime (+1) fluxes; and
4. the already-proved mixed-cost sum remains (X^{1/2+o(1)}).

This supersedes the earlier formula-less (R_X) clause.  Remaining frontier is cross-anchor physical
co-degree/interval expansion and weighted co-moving endpoint flux.  Row admission, reservoir
normalization, Wold recurrence, seam existence, and analytic mixed cost are no longer open.

Full proof and hostile audit:
`../2-fully-proven/new_scientific_knowledge/route-e-grade-recurrent-sparse-reservoir-cube-admission.md`.

## 2026-09-05 — falsification pass on the harmonic Menon residue

Target audited: the frontier map's Route E residue "prove that the explicit active-box
complementary-cost sum in the complete selected-factor mean-square theorem has the required decay
under its literal eighth-root factor lengths and full-frequency parameters; then sum active boxes,
colors, and ladder steps at Menon normalization" (`Sieve/MenonHeathBrownActiveBoxCofactorMeanSquare`,
cost `menonHeathBrownSelectedFactorCofactorCost`).

Verdict: `REDISCOVERED` and `INSIGNIFICANT` for RH; the route's RH-bearing step is `CIRCULAR`.

- The residue is the last computation of S. Menon, *Improved bounds for multiplicative functions
  in almost all short intervals*, arXiv:2607.15574 (17 Jul 2026), Proposition 3.1, Case II(a)/(b)
  (pp. 29–30): after the Heath–Brown decomposition of the long prime polynomial on the exceptional
  frequency set `U`, one factor of length in `[Q^{1/8}, Q^{1/3}]` is bounded pointwise by Lemma
  2.10/2.11 (zero-free region), and the complementary product is paid by Halász–Montgomery
  (Lemma 2.3) over a well-spaced set with `|E| ≪ X^ε`. The corpus's `a^{1/8}` factor-length
  threshold, "complementary Montgomery cost", and "full-frequency" `|t| ≤ X` parameters are this
  step. Closing it certifies Menon's Theorem 1.1 in Lean:
  `(1/X)∫_X^{2X} |(1/h)Σ_{x≤n≤x+h} χ(n)λ(n)|² dx ≪_B (log log h)²/(log h)² + (log log X)⁴/(log X)²`
  (`X ≥ h ≥ 10`, `q ≤ (log X)^B`; Möbius identical). Literature formalization, not new knowledge.
- Significance for RH: none. Menon's rate is `o(1/log Y)` at `L = exp((log Y)^β)`, `β > 1/2`, which
  is exactly what the marker cards consume (Markov step, exceptional starts `o(Y/log Y)`); it feeds
  sign-supply combinatorics only. Menon himself records that the Matomäki–Radziwiłł framework
  cannot show decay much beyond `1/log H` (p. 3) and that RH gives substantially better error
  (Chinis). No almost-all short-interval mean square, at any rate, is an RH producer.
- The RH content of Route E sits in the structured-cell endpoint, and Lean proves it is RH:
  `routeEParityColumnDefectAllStrictHalfPowerBound_implies_riemannHypothesis` (route kill),
  `finiteMobiusCoprimeSignatureAllStrictHalfPowerBound_iff_riemannHypothesis`,
  `mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis` (Littlewood both ways). The live
  conjecture `ENTROPY-SPREAD-GRADE-RECURRENT-CUBE-CAPACITY` (interval Hall expansion for
  opposite-parity corner unions at strict-half Gibbs cost) is a reformulation whose success is
  strict-half Möbius cancellation itself; the Boundary paragraph already records that signed column
  balance is a receiver.
- Relentless interrogation: there is no intermediate statement between Menon-type log savings and
  the strict-half bound that is (i) not RH-equivalent and (ii) known to imply anything on the RH
  side; every strengthening of the residue toward RH passes through Littlewood's criterion. The
  harmonic front should be finished, if at all, as `3-formalized/not_new_scientific_knowledge`.

## 2026-09-05 — rate no-go formalized; route retired

Lean, module `Sieve/RouteEShortIntervalRateStrictHalfNoGo` (built, axiom-clean, wired into
`RHTower`):

- `routeE_shortIntervalRate_not_strictHalfPower`: a `±1`-valued sequence `logThinnedSign`
  (`(-1)^n` with one sign in every `2(⌊log₂ n⌋+1)` flipped) has
  `|∑_{a≤n<a+h} f| ≤ 5 + 2h/(⌊log₂ a⌋+1)` at **every** start `a` and every length `h ≤ a`
  (`abs_sum_Ico_logThinnedSign_le`), Menon-shape discrete mean square
  `≤ (5/h + 2/(⌊log₂ X⌋+1))²` over `X ≤ x < 2X` (`meanSquare_logThinnedSign_le`, better than
  Menon's rate), the corpus's MR-reduced hypothesis `AveragedShortInterval f hh` for every window
  law `hh → ∞` with `hh + 2 ≤ √x/2` (`averagedShortInterval_logThinnedSign`), and partial sums
  `≥ 2^(m−1)/m − 3m` at `N = 2^m` (`sum_range_pow_logThinnedSign_ge`), so every bound
  `|∑_{n<N} f| ≤ C (N+1)^(1/2+δ)`, `0 < δ < 1/2`, fails (`logThinnedSign_not_strictHalfPowerBound`).
- General schedule `blockThinnedSign K` (any nondecreasing `K ≥ 1`): interval sums
  `≤ 5 + 2h/K_J` (`abs_sum_Ico_blockThinnedSign_le`), partial sums
  `≥ ∑_{j<⌊log₂ N⌋} (2^j/K_j − 3) − 1` (`sum_range_blockThinnedSign_ge`) — the rate/growth
  trade-off for an arbitrary short-interval rate.

Consequence. Any argument that uses of `μ` only `|μ| ≤ 1`, a short-interval bound of Menon's
shape (any rate `φ` with `N φ(N) ≫ N^(1/2+δ)`, even pointwise in the start), and the averaged
fibre hypothesis cannot reach the Möbius strict-half-power bound. Together with
`routeEParityColumnDefectAllStrictHalfPowerBound_implies_riemannHypothesis` and
`finiteMobiusCoprimeSignatureAllStrictHalfPowerBound_iff_riemannHypothesis` (the route's RH step
is Littlewood's criterion), Route E has no non-receiver core left. The harmonic Menon front is a
formalization of Menon 2026 (arXiv:2607.15574) Theorem 1.1 and belongs under
`3-formalized/not_new_scientific_knowledge` if completed. Card moved to `5-failed`.
