# Universal radial leakage and the arithmetic trace-class spectrum of constrained prolate modes

The primary object is the zero-integral `h_0`--`h_4` constrained prolate source used in the
Connes--Consani--Moscovici finite-Weil construction. No hypothesis on zeta zeros is used.

## Abstract

We determine the complete leakage-scale dilation spectrum of the constrained fixed-mode prolate
source that underlies the current CCM approximation to the Riemann-Xi kernel. Its exterior Fourier
energy converges, after normalization by the first admissible concentration deficit, to an explicit
universal measure. The associated infinite dilation Gram matrices converge to a diagonal operator
in a logarithmically weighted nuclear topology. After insertion of the exact finite-aperture von
Mangoldt divisor mask, the symmetrized arithmetic dilation operators converge in trace norm to an
explicit positive diagonal operator. This yields an arcsine spectrum, a locally uniform Fredholm
determinant limit, and the full radial prime charge as the negative trace of the limiting operator.
The result is a theorem about prolate spheroidal wave functions and arithmetic dilation sampling; it
assumes no zero-location statement, Weil positivity, or Riemann Hypothesis. We also isolate the
distinct graph-domain theorem still required before these component asymptotics can be promoted to
a full CCM Weil-form asymptotic.

## 1. Constrained source

Let `e_(0,lambda)` and `e_(4,lambda)` be the normalized even fixed-mode eigenfunctions of the
time--band limiting operator on `[-lambda,lambda]`, extended by zero. Write

```text
chi_m(lambda)  = compressed Fourier eigenvalue,
d_m(lambda)    = 1-chi_m(lambda)^2,
ell_m(lambda)  = integral_R e_(m,lambda).
```

Define

```text
g_lambda=(ell_4 e_(0,lambda)-ell_0 e_(4,lambda))
          /sqrt(ell_0^2+ell_4^2),
q_lambda=Fourier(g_lambda).                                    (1.1)
```

Then `||g_lambda||_2=1` and `integral g_lambda=0`. Put `d_lambda=d_4(lambda)`. Fixed-mode Fuchs
asymptotics and the two-mode secular calculation give

```text
||1_(|y|>lambda)q_lambda||_2^2/d_lambda ->8/11.                 (1.2)
```

## 2. Universal radial leakage measure

Define finite measures on `[1,infinity)` by

```text
d nu_lambda(x)
 =lambda |q_lambda(lambda*x)|^2/d_lambda dx.                    (2.1)
```

### Theorem A

The measures `nu_lambda` converge weakly, with convergence of total masses, to

```text
d nu_infinity(x)
 =8/(11*pi) dx/[x sqrt(x^2-1)].                                 (2.2)
```

In particular

```text
nu_infinity([1,infinity))=4/11.                                 (2.3)
```

### Proof

Set `c=2*pi*lambda^2`. Dunster's radial Bessel expansion, uniformly for `1<x<infinity`, is

```text
Ps_n^0(x,c^2)
 =C_(n,c) A_(n,c)(x)
  [J_0(c xi_(n,c)(x))+O(c^(-1)) env J_0(c xi_(n,c)(x))],        (2.4)
```

where for fixed mode

```text
xi_(n,c)(x)->sqrt(x^2-1),
A_(n,c)(x)->x^(-1/2).                                          (2.5)
```

On compact subintervals of `(1,infinity)`, the large-argument Bessel formula and
`cos^2(theta)=(1+cos(2theta))/2` give the weak density

```text
dx/[pi*x*sqrt(x^2-1)].                                         (2.6)
```

Dunster's Bessel envelope gives uniform endpoint tightness `O(sqrt(eta))` on `[1,1+eta]` and
uniform far-tail tightness `O(R^(-1))` on `[R,infinity)`. Thus no mass escapes either end. The
endpoint-response identity

```text
|Fourier(e_(n,lambda))(lambda)|^2/[lambda*d_n(lambda)]->2*pi    (2.7)
```

fixes the normalization. The `n=0` exterior norm is smaller than the `n=4` exterior norm by
`O(lambda^(-4))`; its square and cross term vanish after division by `d_lambda`. The squared
`n=4` coefficient in `(1.1)` tends to `8/11`. This proves `(2.2)`. Finally

```text
integral_1^infinity dx/[x sqrt(x^2-1)]=pi/2,
```

which proves `(2.3)`.

## 3. Dilation Gram operator

For `k>=1`, put

```text
H_(lambda,k)(s)
 =sqrt(lambda*e^s)q_lambda(k*lambda*e^s),  s>=0,

G_lambda(j,k)=inner(H_(lambda,j),H_(lambda,k))_(L2(ds)).        (3.1)
```

The diagonal identity is exact:

```text
G_lambda(k,k)
 =1/k integral_(k*lambda)^infinity |q_lambda(y)|^2dy.           (3.2)
```

Define

```text
w_k=8/(11*pi*k) arcsin(1/k),
Omega_k=1+log k.                                                (3.3)
```

### Theorem B: weighted nuclear diagonalization

Let `W=diag(w_1,w_2,...)`. The Gram matrices define positive trace-class operators on `ell^2(N+)`,
and

```text
||Omega^(1/2)[d_lambda^(-1)G_lambda-W]Omega^(1/2)||_(S1)->0.    (3.4)
```

More strongly, their matrices converge in the weighted projective norm

```text
sum_(j,k>=1) (Omega_j+Omega_k)
 |G_lambda(j,k)/d_lambda-delta_(j,k)w_k| ->0.                   (3.5)
```

Consequently every coefficient matrix `B=(B_jk)` satisfying

```text
sup_(j,k)|B_jk|/(Omega_j+Omega_k)<infinity                      (3.6)
```

has the universal limit

```text
1/d_lambda sum_(j,k)B_jk G_lambda(j,k)
 ->sum_k B_kk w_k.                                             (3.7)
```

### Proof

Theorem A and `(3.2)` give

```text
G_lambda(k,k)/d_lambda->w_k,
G_lambda(k,k)/d_lambda<=C/k^2.                                 (3.8)
```

Since `sum Omega_k/k^2<infinity`, dominated convergence proves the diagonal part of `(3.5)`.

For `j,k>=2`, `j!=k`, the exact exterior Liouville phase gives

```text
|G_lambda(j,k)|
 <=C*d_lambda/[c*j*k*|j-k|].                                   (3.9)
```

The load-bearing phase-preserving representation is obtained from the transformed ODE, not by
factoring Dunster's additive remainder through an exponential. If

```text
W''+c^2 W=psi W,
```

the exact interaction amplitudes satisfy

```text
a_+'= exp(-i*c*xi)psi W/(2*i*c),
a_-'=-exp( i*c*xi)psi W/(2*i*c).                               (3.10)
```

Dunster's exterior potential is short range, so `(3.10)` gives the uniform bounded-variation
symbol estimates required for one nonstationary integration by parts. This derives the needed
phase-preserving remainder control from the differential equation itself.

The Hilbert-kernel sum gives

```text
sum_(k>=2)Omega_k sum_(j>=2,j!=k)|G_lambda(j,k)|
 =O(d_lambda/c).                                                (3.11)
```

The exceptional first row has a stationary point approaching the Bessel endpoint. In the low
range `2<=k<=lambda^2`, the pole-uniform Bessel coordinate gives

```text
|G_lambda(1,k)|/d_lambda
 <=C*c^(-1/2)k^(-2)+C*c^(-1)k^(-1).                            (3.12)
```

For `k>lambda^2`, the second factor is uniformly exterior and the interaction-picture BV estimate
gives

```text
|G_lambda(1,k)|/d_lambda<=C/k^2.                               (3.13)
```

Thus the logarithmically weighted low row is
`O(c^(-1/2)+log(c)^2/c)` and the high row is
`O(log(lambda)/lambda^2)`. Symmetry handles the first column. This proves `(3.5)`. The trace-norm
bound in `(3.4)` follows by decomposing the weighted matrix into rank-one matrix units and using
`2sqrt(Omega_j Omega_k)<=Omega_j+Omega_k`. Equation `(3.7)` is immediate from `(3.5)`.

## 4. Arithmetic trace-class spectrum

At logarithmic aperture `[-log lambda,log lambda]`, only prime shifts `q<=lambda^2` occur. The
radial multiplier remains infinite. Define

```text
a_lambda(k)=sum_(q|k, 2<=q<=lambda^2)Lambda(q),

PPrime_lambda
 =-2 sum_(k>=2)a_lambda(k)sum_(j>=1)G_lambda(j,k).               (4.1)
```

Then

```text
0<=a_lambda(k)<=log k,
a_lambda(k)=log k  for k<=lambda^2.                             (4.2)
```

On the finite-sequence core of `ell^2(N_+)`, define the symmetric matrix

```text
A_lambda(j,k)
 =(a_lambda(j)+a_lambda(k))G_lambda(j,k).                       (4.3)
```

It is useful to write this formally as the anticommutator

```text
A_lambda=M_(a_lambda)G_lambda+G_lambda M_(a_lambda),            (4.4)
```

but `(4.3)` is the definition: no separate domain assertion for the two unbounded products in
`(4.4)` is needed.

Put

```text
kappa_k=2(log k)w_k
       =16/(11*pi) *log(k)/k*arcsin(1/k),
A_infinity=diag(kappa_1,kappa_2,...).                           (4.5)
```

### Theorem C: arithmetic operator and determinant limit

Every `A_lambda` extends to a self-adjoint trace-class operator, and

```text
||A_lambda/d_lambda-A_infinity||_(S1)->0.                      (4.6)
```

More strongly,

```text
sum_(j,k>=1)
 |A_lambda(j,k)/d_lambda-delta_(j,k)kappa_k|->0.                (4.7)
```

Consequently the total negative spectral mass vanishes,

```text
Tr[(A_lambda/d_lambda)_-]->0,                                  (4.8)
```

and the Fredholm determinants converge locally uniformly on the complex plane:

```text
det(I+z A_lambda/d_lambda)
 ->D_arith(z):=product_(k>=2)(1+z kappa_k).                    (4.9)
```

The entire function `D_arith` has order `1/2`; its negative real zeros, counted with
multiplicity, are `-1/kappa_k`.

### Proof

Set

```text
E_lambda(j,k)
 =G_lambda(j,k)/d_lambda-delta_(j,k)w_k.                       (4.10)
```

Since `a_lambda(k)<=log k<Omega_k`, Theorem B gives

```text
sum_(j,k)(a_lambda(j)+a_lambda(k))|E_lambda(j,k)|->0.           (4.11)
```

The remaining diagonal error is

```text
2sum_k|a_lambda(k)-log k|w_k.                                  (4.12)
```

Each summand is eventually zero, and the summable sequence `2(log k)w_k` dominates it. Dominated
convergence proves `(4.7)`. The projective matrix norm dominates the trace norm because every
matrix unit has trace norm one, proving `(4.6)`. The limit is positive, so the negative trace mass
in `(4.8)` is bounded by the trace-norm error. Continuity of the Fredholm determinant in trace norm
proves `(4.9)`. Finally

```text
kappa_k~16/(11*pi)*log k/k^2.                                 (4.13)
```

Thus the exponent of convergence of the zero sequence is `1/2`; the genus-zero product in `(4.9)`
has order `1/2`.

### Theorem D: full finite-aperture prime charge

The full finite-aperture radial prime charge has the universal limit

```text
PPrime_lambda/d_lambda
 ->-16/(11*pi)
   sum_(k>=2) log(k)/k * arcsin(1/k)
  =-Tr(A_infinity).                                             (4.14)
```

The series is absolutely convergent and strictly negative. Equivalently,

```text
sum_(k>=2)log(k)/k*arcsin(1/k)
 =-sum_(r>=0) binom(2r,r)/[4^r(2r+1)] zeta'(2r+2).              (4.15)
```

### Proof

Symmetry gives the exact identity

```text
PPrime_lambda=-sum_(j,k>=1)A_lambda(j,k).                      (4.16)
```

Projective convergence `(4.7)`, which is stronger than trace-norm convergence, permits pairing
with the all-ones matrix and gives `(4.14)`. Equivalently, the off-diagonal estimates in the proof
of Theorem B remain summable after multiplication by `a_lambda(k)<=log k`; on the diagonal use
`(4.2)`, `(3.8)`, and dominated convergence. The divisor identity

```text
sum_(q|k,q>=2)Lambda(q)=log k                                  (4.17)
```

produces `(4.14)`. Expanding `arcsin` into its absolutely convergent positive power series and
differentiating the zeta Dirichlet series at even integers gives `(4.15)`.

## 5. What this proves for CCM

Theorems A--D identify a genuine infinite arithmetic carrier:

```text
exterior radial energy
 -> logarithmically weighted nuclear dilation spectrum
 -> positive arithmetic trace-class spectrum
 -> locally uniform Fredholm determinant
 -> explicit all-prime von-Mangoldt trace.                     (5.1)
```

This carrier is stronger than fixed-pair asymptotics, a finite spectrum, or a scalar leakage
estimate. It transports every logarithmically bounded arithmetic coefficient mask through the
cofinal radial limit, and it retains the complete limiting arithmetic spectrum and multiplicity.

It is not the full Weil form. The exact finite-aperture form couples the prime module to a rank-two
polar block and to the critical Mellin defect. At the critical Mellin boundary the Poisson radial
sum and its central correction must be evaluated as one closed graph-domain bracket. Therefore the
remaining source theorem is precisely

```text
the intact Poisson-resummed constrained prolate tail
converges at leakage scale in the polar--prime critical-Mellin graph topology.       (5.2)
```

Only after `(5.2)` may the regular archimedean `d_lambda log c` law and `(4.3)` be assembled into a
full CCM Rayleigh asymptotic. The subsequent RH-bearing obligations remain a true even-sector
spectral lower bound/gap comparison and locally uniform zero-preserving determinant convergence to
`Xi`.

## 6. Relation to existing literature

### Inputs from the literature

- Dunster proves the uniform radial Bessel/Liouville expansions and error bounds.
- Fuchs and Slepian prove fixed-mode concentration asymptotics.
- Connes--Consani--Moscovici identify the constrained prolate source and the finite-Weil route.
- Standard nonstationary/stationary phase supplies the analytic summation tools.

### New conclusions

The universal measure `(2.2)`, the arcsine dilation spectrum `(3.3)`, the weighted nuclear
convergence `(3.4)`--`(3.5)`, the arithmetic trace-class spectrum `(4.5)`--`(4.9)`, and the
von-Mangoldt trace `(4.14)` do not occur in the cited PSWF or CCM sources. The result is independent
of RH language: it is an operator-limit theorem for a constrained fixed-mode prolate family under
all integer dilations.

### Scope

The weighted nuclear topology controls the entire cofinal arithmetic
dilation module rather than every fixed coordinate. It closes the raw finite-aperture prime channel
of the current CCM source and isolates one exact graph-domain theorem as the next source gate.

## 7. References

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- W. H. J. Fuchs, *On the eigenvalues of an integral equation arising in the theory of band-limited
  signals*, J. Math. Anal. Appl. 9 (1964), 317--330.
- D. Slepian, *Some Asymptotic Expansions for Prolate Spheroidal Wave Functions*, J. Math. Phys. 44
  (1965), 99--140.
- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.
