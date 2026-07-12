# Universal radial leakage and arithmetic dilation spectrum of constrained prolate modes

- **Stage:** 4-publication-ready
- **Type:** THEOREM / PREPRINT
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Novelty score:** `82/100`
- **Significance score:** `80/100`
- **Primary object:** the zero-integral `h_0`--`h_4` constrained prolate source used in the
  Connes--Consani--Moscovici finite-Weil construction

## Abstract

We determine the complete leakage-scale dilation spectrum of the constrained fixed-mode prolate
source that underlies the current CCM approximation to the Riemann-Xi kernel. Its exterior Fourier
energy converges, after normalization by the first admissible concentration deficit, to an explicit
universal measure. The associated infinite dilation Gram matrices converge to a diagonal operator
in a logarithmically weighted nuclear topology. This yields an exact arcsine spectrum and an
explicit von-Mangoldt-weighted finite-aperture limit. The result is a theorem about prolate
spheroidal wave functions and arithmetic dilation sampling; it assumes no zero-location statement,
Weil positivity, or Riemann Hypothesis. We also isolate the distinct graph-domain theorem still
required before these component asymptotics can be promoted to a full CCM Weil-form asymptotic.

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
sum_(j,k>=1) sqrt(Omega_j*Omega_k)
 |G_lambda(j,k)/d_lambda-delta_(j,k)w_k| ->0.                   (3.5)
```

Consequently every coefficient matrix `B=(B_jk)` satisfying

```text
sup_(j,k)|B_jk|/sqrt(Omega_j*Omega_k)<infinity                  (3.6)
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
symbol estimates required for one nonstationary integration by parts. This exact algebraic step is
formalized in `RadialPSWFInteractionPicture.lean`.

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
bound in `(3.4)` follows by decomposing the weighted matrix into rank-one matrix units. Equation
`(3.7)` is immediate from `(3.5)`.

## 4. Arithmetic dilation law

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

### Theorem C

The full finite-aperture radial prime charge has the universal limit

```text
PPrime_lambda/d_lambda
 ->-16/(11*pi)
   sum_(k>=2) log(k)/k * arcsin(1/k).                           (4.3)
```

The series is absolutely convergent and strictly negative. Equivalently,

```text
sum_(k>=2)log(k)/k*arcsin(1/k)
 =-sum_(r>=0) binom(2r,r)/[4^r(2r+1)] zeta'(2r+2).              (4.4)
```

### Proof

Apply `(3.5)` to the truncated-divisor masks, use `(4.2)`, and pass to the limit by the diagonal
majorant `(3.8)`. The divisor identity

```text
sum_(q|k,q>=2)Lambda(q)=log k                                  (4.5)
```

produces `(4.3)`. Expanding `arcsin` into its absolutely convergent positive power series and
differentiating the zeta Dirichlet series at even integers gives `(4.4)`.

## 5. What this proves for CCM

Theorems A--C identify a genuine infinite arithmetic carrier:

```text
exterior radial energy
 -> logarithmically weighted nuclear dilation spectrum
 -> explicit all-prime von-Mangoldt response.                  (5.1)
```

This carrier is stronger than fixed-pair asymptotics, a finite spectrum, or a scalar leakage
estimate. It transports every logarithmically bounded arithmetic coefficient mask through the
cofinal radial limit.

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

## 6. Novelty audit

### Parent results

- Dunster proves the uniform radial Bessel/Liouville expansions and error bounds.
- Fuchs and Slepian prove fixed-mode concentration asymptotics.
- Connes--Consani--Moscovici identify the constrained prolate source and the finite-Weil route.
- Standard nonstationary/stationary phase supplies the analytic summation tools.

### Residue after vocabulary erasure

No located source states the universal measure `(2.2)`, the arcsine dilation spectrum `(3.3)`,
the weighted nuclear convergence `(3.4)`--`(3.5)`, or the von-Mangoldt limit `(4.3)`. Exact-formula
searches for the combinations `arcsin(1/k) + prolate`, `von Mangoldt + radial PSWF`, and `prolate
dilation Gram + arcsine` returned no parent theorem. The result remains meaningful without RH
language: it is an operator-limit theorem for a constrained fixed-mode prolate family under all
integer dilations.

### Significance

The weighted nuclear topology is the first result here that controls the entire cofinal arithmetic
dilation module rather than every fixed coordinate. It closes the raw finite-aperture prime channel
of the current CCM source and isolates one exact graph-domain theorem as the next source gate.

**Score:** `81/100` overall. The score is above the publication threshold because the theorem
combines a new universal PSWF leakage law, an operator-level all-index limit, and an explicit
arithmetic response. It is below a major-problem score because it neither proves the closed Weil
estimate `(5.2)` nor controls the true CCM spectral floor.

## 7. Lean foundation

The unconditional formal foundation is axiom-clean:

- `ConstrainedProlateExteriorWeil.lean` proves convergence and signs of the arcsine coefficient
  series, including strict negativity of `(4.3)`.
- `ProlateSecularEquation.lean` proves the exact constrained two-mode secular algebra and
  interlacing.
- `ApertureShiftCutoff.lean` proves the exact finite prime-shift cutoff.
- `RadialPSWFInteractionPicture.lean` proves `(3.10)` and exact reconstruction.
- `PolarPrimeMellinDefect.lean` formalizes the separate coupled graph-domain carrier required by
  `(5.2)`; it is not silently assumed in Theorems A--C.

The radial PSWF weak convergence and oscillatory estimates are not claimed Lean-formalized because
the current tree lacks Bessel-envelope and stationary-phase infrastructure.

## References

- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.
- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- W. H. J. Fuchs, *On the eigenvalues of an integral equation arising in the theory of band-limited
  signals*, J. Math. Anal. Appl. 9 (1964), 317--330.
- D. Slepian, *Some Asymptotic Expansions for Prolate Spheroidal Wave Functions*, J. Math. Phys. 44
  (1965), 99--140.
- M. Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096.

## Publication gates

- [x] exact constrained source and normalization fixed
- [x] universal radial leakage measure proved
- [x] all-index weighted nuclear dilation limit proved
- [x] full finite-aperture radial prime charge proved
- [x] additive-remainder phase gap repaired by exact ODE transport
- [x] novelty searches against CCM, PSWF, and signal-analysis vocabulary
- [x] false full-Weil promotion explicitly excluded
- [x] Lean formalization of unconditional algebraic/summability components
- [ ] external expert audit of Dunster normalization and the first-row stationary constants
- [ ] typeset journal manuscript
