# A pointed cusp screen makes finite-prime theta sources converge divisor-faithfully to Xi

- **ID:** `finite-prime-theta-cusp-screen-divisor-transfer`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE FINITE-PRIME HILBERT--POLYA TRANSFER / BRIDGE
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Naive finite-prime truncations of Hedenmalm's theta dilation source converge
  smoothly on compact logarithmic intervals but lose all global Fourier control through an
  order-`pi(N)` cusp pole.  A slowly receding archimedean cutoff, retained as part of a pointed
  carrier and then FE-symmetrized, produces positive even finite-prime kernels whose entire Fourier
  transforms converge locally uniformly and zero-preservingly to `Xi`.  Against any fixed signed
  finite-Gamma differential field, the marked packet positively carries an arithmetic complement
  of rank at least `pi(N)-delta_beta-2m(n+1)`; the completion phase, polynomial boundary jets, and
  finite differential state cannot replace this complement.

## 1. Correctly normalized theta source

Put

```text
h(t)=2pi(2pi t^4-3t^2) exp(-pi t^2).                       (1)
```

Its Mellin transform is

```text
Mh(s)=int_0^infinity h(t)t^(s-1)dt
     =1/2 s(s-1) pi^(-s/2) Gamma(s/2).                    (2)
```

Indeed, integrate the `t^4` and `t^2` terms separately and use
`Gamma(s/2+1)=(s/2)Gamma(s/2)` and
`Gamma(s/2+2)=(s/2+1)(s/2)Gamma(s/2)`.

Let

```text
E f(t)=sum_(n>=1)f(nt),
k(x)=exp(x/2) E h(exp x).                                  (3)
```

Then Hedenmalm's theta identity, with its normalization corrected, is

```text
k(x)=2 VarTheta_00(i exp(2x)),
hat k(z)=int_R k(x)exp(izx)dx=Xi(z).                       (4)
```

The factor `2` is load-bearing only for exact normalization.  It adds a constant to the theta
potential and leaves the differential operator `L=kDk^(-1)` unchanged.

### Normalization audit of the June 2026 preprint

The preprint displays

```text
h_00(t)=pi/2(2pi t^4-3t^2)exp(-pi t^2).                   (5)
```

Direct comparison with its preceding theta series shows

```text
t^(1/2) E h_00(t)=1/2 VarTheta_00(i t^2).                  (6)
```

Moreover, direct Mellin transformation of the displayed `VarTheta_00` gives `Xi/2`, not `Xi`.
Thus `(1)=4h_00` is the unique scalar correction making both identities in `(4)` exact.  The
paper's zero characterization is unaffected because all discrepancies are nonzero constants.

## 2. Finite-prime dilation sources

For `N>=2`, let

```text
P_N={p prime:p<=N},
S_N={product_(p in P_N)p^(a_p):a_p in N},

E_N f(t)=sum_(n in S_N)f(nt),
k_N(x)=exp(x/2) E_N h(exp x).                              (7)
```

The sum is over every integer whose prime factors lie in `P_N`.  It contains all powers and mixed
monomials of the retained primes but no unmarked arithmetic direction.

For `Re s>0`, absolute convergence and `(2)` give

```text
int_R k_N(x) exp(i z x)dx
 =Mh(s) product_(p<=N)(1-p^(-s))^(-1),
s=1/2+iz.                                                  (8)
```

The right side is initially the Mellin transform on its natural strip, not an entire completed
function.

## 3. Local convergence and the exact global failure `[PROVED HERE]`

### Smooth compact-local convergence

For every `R>0` and derivative order `m`,

```text
sup_(|x|<=R)|partial_x^m(k_N(x)-k(x))| -> 0.               (9)
```

To prove `(9)`, note that an integer omitted from `S_N` is greater than `N`.  On
`exp(-R)<=t<=exp(R)`, every logarithmic derivative of

```text
exp(x/2)h(n exp x)                                        (10)
```

is bounded by a fixed polynomial in `n exp x` times `exp(-pi n^2 exp(2x))`.  The resulting tail
over `n>N` is summable uniformly on the compact interval and tends to zero.

### Divergence of the zeroth Fourier moment

For fixed `N`, Fubini is justified even with absolute values because

```text
sum_(n in S_N)n^(-1/2)
 =product_(p<=N)(1-p^(-1/2))^(-1)<infinity.                (11)
```

Hence

```text
int_R k_N(x)dx
 =Mh(1/2) product_(p<=N)(1-p^(-1/2))^(-1).                (12)
```

Here `Mh(1/2)!=0`, and the product in `(12)` diverges as `N->infinity`.  Therefore `k_N` does not
converge to `k` in `L^1`, in any topology controlling the real Fourier value at zero, or in any
zero-preserving entire-Fourier topology.

The right tails are nevertheless uniformly double-exponentially small:

```text
sup_N |partial_x^m k_N(x)|
 <=C_m exp(C_m x-pi exp(2x))                               (13)
```

for all large positive `x`.  Combining `(9)`, `(12)`, and `(13)`, the complete failure escapes
through the cusp

```text
x->-infinity  (equivalently t->0+).                        (14)
```

## 4. The cusp carries exactly the prime dimension `[PROVED HERE]`

Let `d_N=pi(N)`.  At `s=0`,

```text
Mh(0)=-1,

product_(p<=N)(1-p^(-s))^(-1)
 =1/(s^d_N product_(p<=N)log p)(1+O(s)).                  (15)
```

Thus the finite-prime Mellin source in `(8)` has a pole of exact order `d_N` at the cusp boundary.
Its top principal part is

```text
-1/(s^d_N product_(p<=N)log p).                            (16)
```

Mellin inversion identifies `(16)` with the logarithmic cusp jet

```text
- (log(1/t))^(d_N-1)
  /((d_N-1)! product_(p<=N)log p).                         (17)
```

Nonzero pole lattices from two distinct primes do not overlap: a common nonzero pole would make
`log p/log q` rational and hence give `p^a=q^b`, contradicting unique factorization.  They therefore
do not change the top logarithmic degree in `(17)`.

The positive carrier law is:

> The `pi(N)` finite-prime directions do not disappear under theta completion.  Before completion
> they are compressed into an order-`pi(N)` cusp pole.  A viable approximation must retain and
> screen this pointed cusp object; compact-local convergence of the scalar kernel alone forgets
> it.

### Exact prime-resolvent realization of the carrier `[PROVED HERE]`

The prime module is an actual bounded operator carrier, not only the pole-order count `(15)`.
Put `g_0(t)=exp(-pi t^2)` and let `D_times=t partial_t` be the multiplicative scaling generator.  A
direct differentiation gives the exact seed identity

```text
h=(D_times^2+D_times)g_0.                                 (17a)
```

This is the symmetric scaling-Hamiltonian differential seed used by Connes--Consani in their
Poisson/Sonine construction.  Its Mellin symbol is

```text
D_times -> -s,
D_times^2+D_times -> s(s-1),                             (17b)
```

which explains the polynomial factor in `(2)` before any zero or spectral condition is imposed.

Now put

```text
a(x)=exp(x/2)h(exp x),
(tau_ell f)(x)=f(x+ell).                                  (17c)
```

The asymptotics of `h` at zero and infinity show that `a` is Schwartz, and every `tau_ell` is
unitary on `L2(R)`.  For `Re sigma>0`, define

```text
R_N(sigma)
 =product_(p<=N)(I-p^(-sigma)tau_(log p))^(-1)
 =sum_(n in S_N)n^(-sigma)tau_(log n).                    (17d)
```

Both the product and series in `(17d)` converge in operator norm.  Indeed, there are only finitely
many prime factors, each inverse is its norm-convergent geometric series, and

```text
sum_(n in S_N)n^(-Re sigma)
 =product_(p<=N)(1-p^(-Re sigma))^(-1)<infinity.           (17e)
```

For every `n`, direct translation gives

```text
n^(-1/2)tau_(log n)a(x)=exp(x/2)h(n exp x).               (17f)
```

Consequently the unscreened finite-prime theta source is exactly

```text
k_N=R_N(1/2)a.                                            (17g)
```

Under the Fourier convention in `(4)`, `tau_(log p)` has multiplier `p^(-iz)`, while

```text
hat a(z)=Mh(1/2+iz).                                      (17h)
```

Thus `(17g)` is precisely the operator lift of the Mellin identity `(8)`.  Together with `(17a)`,
it gives the source factorization

```text
finite-prime Hedenmalm theta state
 = prime resolvent
   * logarithmically transported Connes--Consani scaling seed.             (17i)
```

The logarithmic derivative of the same resolvent recovers the von Mangoldt prime-power generator.
Since all factors commute, operator-norm differentiation of `(17d)` gives

```text
-partial_sigma R_N(sigma) R_N(sigma)^(-1)
 =sum_(p<=N) (log p)p^(-sigma)tau_(log p)
      *(I-p^(-sigma)tau_(log p))^(-1)

 =sum_(p<=N)sum_(r>=1)
      (log p)p^(-r sigma)tau_(r log p)

 =sum_(q=p^r, p<=N) Lambda(q)q^(-sigma)tau_(log q).       (17j)
```

Therefore the same bounded prime resolvent carries both source levels needed by the direct
Hilbert--Polya architecture:

```text
Euler theta state:            R_N(1/2)a=k_N,
Euler logarithmic derivative: -partial_sigma R_N R_N^(-1). (17k)
```

The group generated by the translations in `(17d)` is a faithful copy of `Z^(P_N)`: a rational
relation among their lengths would be a rational relation among `{log p:p<=N}`, contrary to unique
factorization.  Hence its rational rank is exactly `pi(N)`.  This realizes the full prime carrier
before the scalar completion and before any positivity assertion.

### Arbitrary-scale signed-Gamma conservation law for the pointed carrier

Let

```text
V_N=span_Q{log p:p<=N prime}.                              (17l)
```

Then `dim_Q V_N=pi(N)`.  Fix any finite signed product of positive-scale affine Gamma factors and
let `K_G` be its differential field.  The arbitrary-scale alien-charge theorem gives the exhaustive
carrier dichotomy

```text
R_G=0  -> exponential--rational and DA,
R_G!=0 -> nonzero scaled alien charge and HT.              (17m)
```

Incommensurable scales supply no third DA carrier.  Under the stated neutral/recurrent boundary
hypotheses, both branches have the terminal functional-projective chain

```text
K_G
  -> C[z,exp(beta z),exp(-beta z)]
  -> C[exp(beta z),exp(-beta z)].                          (17n)
```

For a recurrent output DA over `K_G`, let `n` be the minimal limiting ADE order, let `m` be the
size of a finite regular-sample atlas, and let `D` be the rational frequency space carried by that
finite differential state.  The signed-Gamma boundary law gives

```text
dim_Q(span_Q(beta)+D)<=delta_beta+2m(n+1),
delta_beta=rank_Q(beta Z) in {0,1}.                        (17o)
```

Define the arithmetic complement

```text
A_N=V_N/(V_N intersection (span_Q(beta)+D)).               (17p)
```

Rank additivity and `(17o)` give the positive conservation inequality

```text
dim_Q A_N>=pi(N)-delta_beta-2m(n+1).                       (17q)
```

For the packet `(23)` below, this complement has a concrete carrier: the prime resolvent `R_N` and
the marked Euler factors in the unscreened source `k_N`, equivalently the individually labelled
prime directions whose joint cusp compression has exact order `pi(N)`.  Completion does not create
those directions.  Its single phase `beta Z` accounts for at most `delta_beta`; polynomial jets and
Stokes or asymptotic corrections control boundary depth but contribute no terminal compact
character rank.

Consequently a cofinal Hilbert--Polya architecture has the following positive resource law:

> After subtracting the signed-Gamma phase and finite differential-state budget, it must transport
> the quotient `A_N` in a separate pointed coefficient, operator, test-space, determinant, or
> divisor carrier.  If `m` and `n` remain bounded, `dim_Q A_N->infinity`.

The theta-cusp packet realizes this requirement before any zero estimate is attempted: its scalar
completed trace performs the divisor transfer, while its unscreened marked component transports the
complementary prime-character module through completion.

## 5. Cofinal pointed cusp screen `[PROVED HERE]`

Fix a smooth cutoff `eta:R->[0,1]` with

```text
eta(x)=0 for x<=-1,
eta(x)=1 for x>=0.                                        (18)
```

There are strictly increasing prime cutoffs `N_j` such that, with

```text
eta_j(x)=eta(x+j),
r_j(x)=eta_j(x)k_(N_j)(x),
g_j(x)=1/2(r_j(x)+r_j(-x)),                               (19)
```

the following hold.

1. `g_j` is smooth, real, even, and strictly positive.
2. Each `g_j` uses only the marked primes `p<=N_j`, their powers, FE reflection, and the
   archimedean cutoff.
3. For every `A>=0` and derivative order `m`,

   ```text
   int_R exp(A|x|)|partial_x^m(g_j(x)-k(x))|dx ->0.        (20)
   ```

### Choice of the cofinal sequence

The exact theta source `k` is strictly positive.  Choose `X_0` so that `h(exp x)>0` for `x>=X_0`;
then every term in `(7)` is positive there.  On the compact interval `[-j-1,X_0]`, positivity of
`k` gives a positive minimum.  By `(9)`, choose `N_j>N_(j-1)` so large that:

```text
k_(N_j)>0 on [-j-1,X_0],                                  (21)

max_(m<=j) sup_(|x|<=j+1)
  |partial_x^m(k_(N_j)-k)| <=exp(-j^2).                   (22)
```

Equations `(13)` and `(21)` make `k_(N_j)` positive wherever `eta_j` is nonzero.  For every `x`,
at least one of `eta_j(x),eta_j(-x)` equals `1`, so `(19)` is strictly positive and even.

To prove `(20)`, split the line into `|x|<=j+1` and its two tails.  The central contribution tends
to zero by `(22)`.  On the tails, one reflected summand is cut off, while `(13)` and the
double-exponential decay of `k` dominate every exponential weight.  This proves `(20)` by a
diagonal argument in `A` and `m`.

The marked object is not only the scalar `g_j`.  It is the pointed incidence packet

```text
I_j=(P_(N_j), a, R_(N_j)(1/2), k_(N_j),
     eta_j, r_j, r_j reflected, g_j).                      (23)
```

The operator and unscreened components in `(23)` retain the faithful rank-`pi(N_j)` translation
module, its exact cusp order, and the individual Euler-factor labels; `g_j` is their completed
scalar trace.

## 6. Entire FE--Schwarz divisor transfer `[PROVED HERE]`

Define

```text
F_j(z)=int_R g_j(x)exp(izx)dx.                             (24)
```

The cutoff gives `r_j` a finite left endpoint, while `(13)` gives double-exponential right decay.
After reflection, `g_j` has double-exponential decay in both directions.  Therefore `F_j` is
entire.  Since `g_j` is real and even,

```text
F_j(-z)=F_j(z),
F_j(conjugate(z))=conjugate(F_j(z)).                       (25)
```

For a compact set `K subset C`, choose `A` with `|Im z|<=A` on `K`.  Equations `(4)`, `(20)`, and
`(24)` give

```text
sup_(z in K)|F_j(z)-Xi(z)|
 <=int_R exp(A|x|)|g_j(x)-k(x)|dx ->0.                    (26)
```

Thus

```text
F_j -> Xi locally uniformly on C.                         (27)
```

Let `Omega` be any bounded domain whose boundary contains no zero of `Xi`.  Rouché's theorem and
`(27)` give, for all sufficiently large `j`,

```text
#Div(F_j) in Omega = #Div(Xi) in Omega                     (28)
```

with multiplicity.  Hence `(27)` is zero-preserving in the exact cofinal sense required by the
finite-prime logarithmic-boundary transfer theorem.

## 7. What has and has not been achieved

The construction proves two of the three independent finite-prime obligations:

```text
phase obligation:   pointed carrier rank >=pi(N_j),
Gamma complement:   rank A_(N_j)>=pi(N_j)-delta_beta-2m(n+1),
divisor obligation: F_j -> Xi locally uniformly and zero-preservingly.   (29)
```

It does not prove the remaining horizontal obligation

```text
E_(N_j)(horizontal defect)=o((log N_j)^2)
on every zero of F_j.                                     (30)
```

Indeed, proving `(30)` together with `(27)` would prove RH by the already formalized transfer
theorem.  Positivity of the kernels `g_j` and FE--Schwarz symmetry of `F_j` do not imply that their
zeros are real.

The exact next problem is now narrower:

> Choose the cofinal screen, or enrich the pointed incidence packet `(23)`, so that the zeros of
> its completed trace satisfy the sub-log-square reflected-energy bound `(30)`.

This is a genuine boundary-control problem, not a carrier-construction or convergence problem.

## 8. Attacks and exact boundary

1. **Naive finite Euler products fail.**  Equation `(12)` proves that compact-local theta
   convergence cannot be Fourier-completed without a cusp screen.
2. **The screen is not a target-zero cutoff.**  It is chosen only from source-kernel convergence,
   positivity, and tail bounds; no zero of `Xi` enters its definition.
3. **The scalar trace alone is insufficient.**  If `(23)` is discarded and only `F_j` retained,
   the exact prime labels and the cusp order are no longer visibly recoverable.
4. **Finite-prime does not mean finite sum.**  Each stage retains finitely many prime generators
   but all their nonnegative exponent vectors.  This is forced by the Euler dilation factors.
5. **Kernel positivity is weaker than Laguerre--Polya membership.**  A positive even Fourier kernel
   need not have an all-real zero divisor.
6. **The cofinal subsequence is sufficient.**  Every transfer theorem used by the route is cofinal;
   no claim is made for every integer cutoff.
7. **The cusp jet is not the `1/log N` horizontal defect.**  It is the source-side noncompactness
   which must be screened before the spectral boundary layer can even be posed.  Equation `(30)`
   remains the distinct zero-fibre condition.

## 9. Parent and novelty audit

The inputs are classical Mellin transformation, Euler factorization over smooth integers,
commuting Neumann series, dominated convergence, diagonal cutoff selection, and Rouché's theorem.
The one-prime inverse `I-p^(-1/2)U_p` is already formalized in
`one-prime-euler-fredholm-seam.md`; equations `(17d)`--`(17k)` are its direct commuting
smooth-integer assembly on the theta seed.  The scaling seed `(17a)` and its all-integer summation
parent occur in A. Connes and C. Consani, *The Scaling Hamiltonian*, while the exact comparison to
Hedenmalm's seed and the retained-prime resolvent are the short bridge recorded here
(arXiv:1910.14368).  The direct 2026 parent is
H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494, which records the
theta dilation factorization but does not study finite-prime truncations, their cusp pole, or a
cofinal screen.

The arbitrary-scale dichotomy `(17m)` is supplied by
`incommensurable-gamma-orbit-free-quasianalyticity.md`, with the scaled charge classifier and
finite-shift peeling in its two companion cards.  It removes commensurability from the complement
law but does not alter the source-screen proof.

Searches through 11 July 2026 did not locate the exact construction `(19)`--`(28)`.  Nevertheless,
after erasing the Hilbert--Polya vocabulary, the proof is a direct diagonal approximation theorem
for Fourier kernels.  It therefore fails the parent-theory and anti-theatre novelty gates and is
classified honestly as a `[BRIDGE]`.

Its research value is substantive: it constructs the previously missing source-pure, pointed,
finite-prime cofinal divisor carrier and leaves only the reflected-energy control required to prove
RH.

## Lean status

The normalization is already authoritative in
`formal/GaloisForLFunctions/RHTower/XiThetaCriticalTrace.lean`:
`completedRiemannZeta₀_critical_eq_fourier_xiThetaLogSource` proves that the completed critical
value is one half of the unrenormalized theta-source Fourier transform.  Thus no normalization
wrapper is needed.

`formal/GaloisForLFunctions/RHTower/ThetaCuspFinitePrimeSource.lean` now defines the normalized
polynomial--Gaussian seed `h`, proves the exact scaling-generator identity
`h=(D_times^2+D_times)g_0`, proves the normalized logarithmic-translation formula `(17f)`, defines
the finite-prime source as the absolutely convergent sum over `(N+1)`-smooth integers, and proves
the exact absolutely convergent smooth-integer resolvent-series identity `k_N=R_N(1/2)a` on the
seed.  It also proves
uniform convergence of these sources to the all-integer theta-cusp state on every compact
logarithmic interval.  These declarations are unconditional and begin with the actual source rather
than an abstract approximation interface.

`formal/GaloisForLFunctions/RHTower/ThetaCuspMellinPole.lean` defines the actual finite Euler
denominator `product_(p<=N)(1-exp(-s log p))`.  It proves that every prime factor has analytic order
one at `s=0`, that the full denominator has exact order `pi(N)`, and that its reciprocal has
meromorphic order `-pi(N)`.  Thus the exact cusp pole order is formalized, rather than represented
by a finite-dimensional count.

The formal tree still lacks smooth compact-local convergence of all derivatives, the exact
order-`pi(N)` Mellin cusp pole, the finite product resolvent and its logarithmic derivative,
exponentially weighted cutoff convergence, the cofinal pointed screen, and the entire Rouché
divisor transfer in `(28)`.  The zero-fibre energy estimate `(30)` remains the separate RH-bearing
open theorem.

### Lean gates

- [x] normalized polynomial--Gaussian seed and scaling-generator identity
- [x] physical dilation as normalized logarithmic translation
- [x] absolutely convergent finite-prime smooth-integer source
- [x] exact smooth-integer resolvent-series action on the theta seed
- [x] compact-local uniform convergence to the all-integer source
- [ ] compact-local convergence of every positive derivative order
- [x] Mellin cusp pole of exact order `pi(N)`
- [ ] bounded finite-prime resolvent and von Mangoldt logarithmic derivative
- [ ] cofinal pointed screen and exponentially weighted convergence
- [ ] entire transform and Rouché divisor transfer
- [ ] sub-log-square reflected energy on every approximant zero

## Gates

- [x] theta/dilation normalization corrected
- [x] finite-prime smooth-integer source defined
- [x] compact-local convergence proved
- [x] global Fourier failure and escaping cusp proved
- [x] exact cusp pole order `pi(N)` proved
- [x] exact prime-resolvent carrier and von Mangoldt logarithmic derivative proved
- [x] signed-Gamma arithmetic complement law integrated
- [x] positive even pointed screen constructed
- [x] exponentially weighted source convergence proved
- [x] entire FE--Schwarz transforms constructed
- [x] local uniform and zero-preserving convergence to `Xi` proved
- [x] source provenance retained in a pointed incidence packet
- [x] novelty claim rejected as a bridge
- [ ] sub-log-square reflected energy on every zero
- [ ] RH
