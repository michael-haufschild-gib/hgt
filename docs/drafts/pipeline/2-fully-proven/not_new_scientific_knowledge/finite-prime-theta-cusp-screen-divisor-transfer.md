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

### Signed-Gamma conservation law for the pointed carrier

Let

```text
V_N=span_Q{log p:p<=N prime}.                              (17a)
```

Then `dim_Q V_N=pi(N)`.  Fix a commensurable signed finite-Gamma differential field `K_G` whose
full functional-projective upper boundary is

```text
K_G
  -> C[z,exp(beta z),exp(-beta z)]
  -> C[exp(beta z),exp(-beta z)].                          (17b)
```

For a recurrent output DA over `K_G`, let `n` be the minimal limiting ADE order, let `m` be the
size of a finite regular-sample atlas, and let `D` be the rational frequency space carried by that
finite differential state.  The signed-Gamma boundary law gives

```text
dim_Q(span_Q(beta)+D)<=delta_beta+2m(n+1),
delta_beta=rank_Q(beta Z) in {0,1}.                        (17c)
```

Define the arithmetic complement

```text
A_N=V_N/(V_N intersection (span_Q(beta)+D)).               (17d)
```

Rank additivity and `(17c)` give the positive conservation inequality

```text
dim_Q A_N>=pi(N)-delta_beta-2m(n+1).                       (17e)
```

For the packet `(23)` below, this complement has a concrete carrier: the marked Euler factors in
the unscreened source `k_N`, equivalently the individually labelled prime directions whose joint
cusp compression has exact order `pi(N)`.  Completion does not create those directions.  Its
single phase `beta Z` accounts for at most `delta_beta`; polynomial jets and Stokes or asymptotic
corrections control boundary depth but contribute no terminal compact character rank.

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
I_j=(P_(N_j), k_(N_j), eta_j, r_j, r_j reflected, g_j).    (23)
```

The unscreened component in `(23)` retains the exact `pi(N_j)` cusp order and the individual Euler
factor labels; `g_j` is its completed trace.

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
dominated convergence, diagonal cutoff selection, and Rouché's theorem.  The direct 2026 parent is
H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494, which records the
theta dilation factorization but does not study finite-prime truncations, their cusp pole, or a
cofinal screen.

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

The formal tree does not define the smooth-integer dilation source `E_N`, its order-`pi(N)` Mellin
cusp pole, exponentially weighted cutoff convergence, or the Rouché divisor transfer in `(28)`.
Formalizing only the final abstract convergence implication would be wrapper bloat.  A meaningful
stage-3 target begins with the finite-prime source and the cusp-screen construction themselves.

## Gates

- [x] theta/dilation normalization corrected
- [x] finite-prime smooth-integer source defined
- [x] compact-local convergence proved
- [x] global Fourier failure and escaping cusp proved
- [x] exact cusp pole order `pi(N)` proved
- [x] signed-Gamma arithmetic complement law integrated
- [x] positive even pointed screen constructed
- [x] exponentially weighted source convergence proved
- [x] entire FE--Schwarz transforms constructed
- [x] local uniform and zero-preserving convergence to `Xi` proved
- [x] source provenance retained in a pointed incidence packet
- [x] novelty claim rejected as a bridge
- [ ] sub-log-square reflected energy on every zero
- [ ] RH
