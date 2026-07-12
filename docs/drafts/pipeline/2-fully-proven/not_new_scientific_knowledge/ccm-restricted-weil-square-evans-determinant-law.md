# The restricted Weil eigenproblem has an exact square Evans determinant

- **ID:** `ccm-restricted-weil-square-evans-determinant-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Paley--Wiener Toeplitz compression, logarithmic Dirichlet reconstruction, and
  `ccm-rational-residual-finite-evans-matrix-law.md`

## Statement

Fix `a>0`, put `I=(-a,a)`, and let `A_a` be the self-adjoint operator associated with the
restricted Weil form. Its exact Fourier symbol is

```text
W_a(xi)
 =Re psi(1/4+i xi/2)-log pi
  -2 sum_(n<=exp(2a)) Lambda(n)n^(-1/2)cos(xi log n)
  +P_a(xi),                                               (1)

P_a(xi)
 =[2sinh(a)cos(2a xi)+4xi cosh(a)sin(2a xi)]/(xi^2+1/4).
```

For every real spectral parameter `lambda`, the eigenvalue equation is exactly

```text
(A_a-lambda I)v=0
 iff supp v subset [-a,a] and
     1_I (W_a(D)-lambda)v=0.                              (2)
```

Let `Z_(a,lambda)` be the finite real zero multiset of `W_a-lambda`. If it is empty, then
`W_a-lambda>0` and `(2)` has only the zero solution. Otherwise put

```text
p_(a,lambda)(xi)
 =product_(tau in Z_(a,lambda))(xi-tau)^(nu_tau),
d_(a,lambda)=degree p_(a,lambda)=2L_(a,lambda),

b_(a,lambda)(xi)
 =p_(a,lambda)(xi)/(1+xi^2)^(L_(a,lambda)),

c_(a,lambda)(xi)
 =(W_a(xi)-lambda)/b_(a,lambda)(xi)>0.                   (3)
```

Let

```text
F_(a,lambda)
 ={f:p_(a,lambda)(D)f=0 on I},

R_(a,lambda)
 =span{x^j exp(x),x^j exp(-x):0<=j<L_(a,lambda)}.        (4)
```

Both spaces have dimension `d_(a,lambda)`. The positive logarithmic Dirichlet operator associated
with `c_(a,lambda)` reconstructs, for every `f in F_(a,lambda)`, a unique supported vector

```text
v_f=C_(a,lambda,I)^(-1)f,
V(f)=c_(a,lambda)(D)v_f.                                 (5)
```

The exact residual

```text
N_(a,lambda)f
 :=1_I b_(a,lambda)(D)V(f)                               (6)
```

belongs to `R_(a,lambda)`. Hence `(6)` is a square linear map

```text
N_(a,lambda):F_(a,lambda)->R_(a,lambda)                  (7)
```

and

```text
ker(A_a-lambda I) isomorphic to ker N_(a,lambda).        (8)
```

Consequently

```text
lambda in spec(A_a)
 iff det N_(a,lambda)=0,                                 (9)
```

where the determinant is intrinsically a section of

```text
det(F_(a,lambda))^* tensor det(R_(a,lambda)).            (10)
```

Unlike the screw-variable map, no mean condition or affine anchors occur, so there are no three
excess target channels.

## Proof

### 1. Exact restricted multiplier equation

Suzuki proves on the smooth core that

```text
(A_a v)(x)=integral_I (-g''(x-y))v(y)dy.                 (11)
```

The corrected Fourier calculation identifies this distribution with `(1)`. Equivalently, under
the Fourier transform from supported functions to `PW_a`, the restricted operator is the Toeplitz
compression

```text
P_(PW_a) M_(W_a) P_(PW_a).                               (12)
```

The representation theorem for the closed restricted Weil form extends `(11)`--`(12)` from the
core to the operator domain. This proves `(2)`.

### 2. Characteristic reduction and global logarithmic regularity

The symbol `W_a-lambda` is even, real analytic, and tends to `+infinity` like `log|xi|`. Its real
zero multiset is therefore finite, symmetric, and of even total multiplicity. Factoring it as in
`(3)` gives

```text
c_(a,lambda)(xi)
 =(1/2)log(1+xi^2)+q_(a,lambda)(xi),
q_(a,lambda) in L_infinity,
inf c_(a,lambda)>0.                                      (13)
```

Let `v` solve `(2)` and put `V=c_(a,lambda)(D)v` distributionally. Then

```text
b_(a,lambda)(D)V=0 on I.                                (14)
```

Applying the local differential operator `(1+D^2)^L` gives

```text
p_(a,lambda)(D)V=0 on I.                                (15)
```

Thus `V|_I` is an exponential polynomial and belongs to `F_(a,lambda)`. Since `v` is supported and
belongs to `L2(I)`, the Carleman-bounded cross-boundary block of the logarithmic multiplier gives

```text
1_(R minus I)V
 =1_(R minus I)c_(a,lambda)(D)1_Iv in L2.                (16)
```

Together with `(15)`, this places `V` in global `L2`, hence `v` in the global operator domain of
`c_(a,lambda)(D)`. Coercive Dirichlet uniqueness then shows that `v` is exactly the reconstruction
`v_f` in `(5)` for `f=V|_I`.

### 3. Square residual

The rational Bessel-potential calculation applies without change to `(3)`. The interior
zero-extension defect of `f` and the exterior trace of `V(f)` both propagate through
`b_(a,lambda)(D)` into the space `R_(a,lambda)`. This proves `(6)`--`(7)`.

For an eigenvector, `(14)` makes `N_(a,lambda)f=0`, so the map from the left kernel of `(8)` to the
right kernel is defined. Conversely, if `N_(a,lambda)f=0`, the reconstructed supported vector
`v_f` belongs to the global logarithmic domain and satisfies

```text
1_I(W_a(D)-lambda)v_f
 =1_I b_(a,lambda)(D)V(f)=0.                            (17)
```

Equation `(2)` makes it an eigenvector. Dirichlet uniqueness makes the correspondence bijective,
proving `(8)`.

Since source and target in `(7)` have equal dimension, `(8)` gives `(9)` and the intrinsic
determinant-line statement `(10)`. `QED`

## Exact Morse and RH consequences

The spectrum of `A_a` is discrete, lower bounded, and accumulates only at `+infinity`. Therefore
its negative Morse index is finite and

```text
kappa(a)
 =sum_(lambda<0, det N_(a,lambda)=0)
    dim ker N_(a,lambda).                                (18)
```

Moreover,

```text
A_a>0
 iff det N_(a,lambda)!=0 for every lambda<=0,            (19)

RH
 iff det N_(a,lambda)!=0
     for every a>0 and every lambda<=0.                  (20)
```

The weaker zero-fiber criterion is also exact cofinally:

```text
RH iff det N_(a,0)!=0 for every a>0,                     (21)
```

using Suzuki's continuity of the lowest eigenvalue, its positivity for small aperture, and
Yoshida's aperture criterion.

Equations `(18)`--`(21)` are reformulations, not proofs of the required nonvanishing.

## Determinant-line consequence

The earlier screw-variable map had type

```text
F_a -> R_a direct_sum C^3
```

and therefore produced only a Pluecker vector and its squared Gram norm. The restricted-Weil
eigenfunction variable removes the derivative's zero-mean condition and the two affine constants
lost by differentiating the screw equation. The map `(7)` is square, so `(10)` is already a genuine
determinant line.

What remains is not an artificial scalarization. A successful cofinal construction must identify
`(10)` with the intrinsic determinant line of `A_a-lambda I` and prove that its section has no zeros
on the nonpositive spectral half-line.

`[PROVED SUBSEQUENT CLOSURE]` Weierstrass continuation retains a characteristic pair as a nonreal
conjugate pair when its real zeros disappear. This stabilizes the finite dimension locally, and
analytic Grushin reduction glues the square determinants across all characteristic-stratum changes
to the intrinsic Fredholm determinant line. The proof is in
`ccm-weierstrass-stabilized-square-evans-line-law.md`. The remaining task is aperture-coherent
source normalization and nonvanishing.

Reflection supplies a canonical grading:

```text
N_(a,lambda)=N_(a,lambda)^+ direct_sum N_(a,lambda)^-,
dim source(N^+)=dim target(N^+)=L_(a,lambda),
dim source(N^-)=dim target(N^-)=L_(a,lambda).             (22)
```

Thus the remaining comparison has no excess parity channels.

## Scope and classification

The proof is an application of Suzuki's published restricted form, standard Toeplitz compression,
constant-coefficient ODE regularity, closed logarithmic Dirichlet forms, and Bessel kernels. It is a
route bridge, not new scientific knowledge. A faithful Lean formalization requires the restricted
Weil form, Paley--Wiener compression, logarithmic multiplier, and Dirichlet reconstruction, which
are absent from the formal tree. No wrapper is added.

Primary source:

- [Suzuki, *Weil's quadratic form via the screw function*, Sections 2, 3, and 8](https://arxiv.org/abs/2606.09096)

## Gates

- [x] restricted-Weil eigenproblem written as the exact supported multiplier equation
- [x] shifted real-characteristic factorization constructed
- [x] eigenvectors lifted to the global logarithmic multiplier domain
- [x] logarithmic Dirichlet reconstruction extended to every real spectral parameter
- [x] rational residual reduced to an equal-dimensional target
- [x] exact square Evans kernel equivalence proved
- [x] determinant-line section and parity split isolated
- [x] exact fixed-aperture Morse formula recorded
- [x] glue the determinant line across characteristic-stratum changes
- [x] select a continuous explicit source normalization chamber in aperture
- [ ] prove nonvanishing on `lambda<=0` for every aperture
- [ ] RH
