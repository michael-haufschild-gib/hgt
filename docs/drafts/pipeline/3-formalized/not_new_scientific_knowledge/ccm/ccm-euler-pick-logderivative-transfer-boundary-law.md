# CCM Euler-Pick transfer requires dephased logarithmic derivatives across the half-strip boundary

- **ID:** `ccm-euler-pick-logderivative-transfer-boundary-law`
- **Stage:** 2-fully-proven / paper proof complete
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** CCM's regularized-determinant formula and
  `critical-logderivative-two-channel-weil-resolvent-law.md`
- **Statement:** Even real-rooted CCM spectral factors have positive logarithmic-derivative Pick
  kernels. Local convergence of those dephased kernels to the centered Xi logarithmic derivative
  on the Euler half-plane would prove RH. The canonical aperture phase contributes a negative
  Cauchy kernel of size `2 log(lambda)`, so real spectral zeros alone do not transfer this
  positivity. A successful implementation must transport a positive background renormalization
  through the boundary `Re w=1/2`, or carry the Xi divisor by a different cofinal limit.

## 1. Positive kernel of an even real-rooted spectral factor

Let `F` be a nonzero even entire function of order at most one, real on the real axis, whose zeros
are all real. Put

```text
G(w)=F(-iw),
L_G(w)=G'(w)/G(w).                                           (1)
```

Then, on the right half-plane `Re w>0`, the kernel

```text
K_G(w,v)
 =(L_G(w)+conjugate(L_G(v)))/(w+conjugate(v))                (2)
```

is positive semidefinite.

### Proof

Evenness removes the linear exponential in the genus-one Hadamard factorization. If zero has
multiplicity `2r` and the positive nonzero zeros are `gamma_k`, counted with multiplicity, then

```text
G(w)=C w^(2r) product_k (1+w^2/gamma_k^2),
sum_k gamma_k^(-2)<infinity.                                 (3)
```

Hence

```text
L_G(w)=2r/w+sum_k 2w/(w^2+gamma_k^2).                        (4)
```

The zero mode contributes the positive rank-one kernel

```text
2r/(w conjugate(v)).                                         (5)
```

For every `gamma>0`, elementary algebra gives

```text
1/(w+conjugate(v))
 *(2w/(w^2+gamma^2)
   +2conjugate(v)/(conjugate(v)^2+gamma^2))

 =2*[w/(w^2+gamma^2)]
      *conjugate([v/(v^2+gamma^2)])
  +2*[gamma/(w^2+gamma^2)]
      *conjugate([gamma/(v^2+gamma^2)]).                    (6)
```

Thus every paired spectral zero contributes a sum of two positive rank-one kernels. The locally
uniformly convergent sum in `(4)` proves positivity of `(2)`.

## 2. Euler-half-plane transfer theorem

Put

```text
X(w)=xi(1/2+w),
L(w)=X'(w)/X(w).                                             (7)
```

Let `F_j` be functions satisfying the hypotheses of Section 1, let `G_j(w)=F_j(-iw)`, and assume

```text
L_(G_j)->L locally uniformly on Re w>1/2.                    (8)
```

Then RH holds.

Indeed, for any finite nodes `w_1,...,w_n` in `Re w>1/2`, the matrices formed from `(2)` are
positive semidefinite. Equation `(8)` gives entrywise convergence to

```text
K_L(w,v)=(L(w)+conjugate(L(v)))/(w+conjugate(v)).             (9)
```

The positive cone of finite Hermitian matrices is closed, so every finite matrix of `K_L` is
positive. The complete-detector theorem in
`critical-logderivative-two-channel-weil-resolvent-law.md` identifies this with full Weil
positivity and hence RH.

The same proof only needs pointwise convergence of the logarithmic derivatives at every finite
node system. Local uniform convergence is the natural analytic formulation.

This is a genuine alternative transfer interface:

```text
real finite spectra
  + dephased Euler-half-plane logarithmic-derivative convergence
  -> positive complete Euler Pick kernel
  -> RH.                                                      (10)
```

It does not require prior global locally uniform convergence of the entire determinants or an
explicit zero-preserving limit. The entire burden is instead concentrated in `(8)`.

## 3. Exact CCM aperture-phase defect

Under the CCM simple-even hypothesis, Theorem 5.10 of *Zeta Spectral Triples* gives

```text
D_(lambda,N)(z)
 =det_reg(D_log^(lambda,N)-z)
 =-i lambda^(-iz) F_(lambda,N)(z),                           (11)
```

where `F_(lambda,N)=hat(xi_(lambda,N))` is even and entire and all its zeros are real. Set

```text
a=log lambda,
G_(lambda,N)(w)=F_(lambda,N)(-iw).                           (12)
```

The spectral factor `G_(lambda,N)` has the positive kernel of Section 1. But the regularized
determinant itself satisfies

```text
D_(lambda,N)(-iw)
 =-i exp(-aw)G_(lambda,N)(w),

d/dw log D_(lambda,N)(-iw)
 =-a+L_(G_(lambda,N))(w).                                   (13)
```

Therefore its logarithmic-derivative kernel is

```text
K_D(w,v)=K_G(w,v)-2a/(w+conjugate(v)).                       (14)
```

The second term is `-2a` times the positive Cauchy kernel of the right half-plane. It is negative
and grows with the aperture. Thus the fact that every finite determinant has real spectral zeros
does not make the canonically phased kernel `(14)` positive.

Multiplying `(11)` by the nonvanishing factor `i lambda^(iz)` removes `(14)` and recovers the even
spectral factor. That normalization is legitimate for zeros, but positivity can pass to Xi only if
the dephased logarithmic derivatives themselves satisfy `(8)`, or if a source-defined relative
kernel cancels the background term while remaining positive.

## 4. Exact spectral-discrepancy representation of the phase

First separate the periodic scaling background. With `a=log(lambda)`, its regularized determinant
is

```text
D_(0,a)(z)=1-exp(-2iaz),
D_(0,a)(-iw)=1-exp(-2aw).                                    (14a)
```

Hence

```text
L_(0,a)(w)
 =d/dw log D_(0,a)(-iw)
 =2a/(exp(2aw)-1).                                           (14b)
```

This background kernel is not positive at finite aperture. For

```text
w=x+i*pi/(2a),       x>0,
```

one has `exp(2aw)=-exp(2ax)`, so `L_(0,a)(w)<0` and its diagonal Pick value is negative.

Nevertheless it vanishes exponentially on the exact source region. If `Re w,Re v>=sigma>0`, then

```text
|L_(0,a)(w)|<=2a/(exp(2a sigma)-1),

|K_(0,a)(w,v)|
 <=2a/(sigma*(exp(2a sigma)-1))->0.                          (14c)
```

Thus the periodic background is finite-aperture indefinite but cofinally invisible on every
compact subset of `Re w>0`.

The determinant factorization

```text
D_(lambda,N)=D_(0,a) R_(lambda,N)                            (14d)
```

gives an additive kernel split

```text
K_D=K_(0,a)+K_(R,lambda,N),                                 (14e)
```

where `K_R` is formed from `d/dw log R_(lambda,N)(-iw)`. Consequently a successful relative route
may prove local convergence and asymptotic positivity for `K_R`; the universal background error
then disappears by `(14c)`. Exact finite-aperture positivity of the periodic factor is neither
true nor required.

For `gamma>=0`, define the paired-zero kernel

```text
kappa_gamma(w,v)
 =2*[w/(w^2+gamma^2)]
      *conjugate([v/(v^2+gamma^2)])
  +2*[gamma/(w^2+gamma^2)]
      *conjugate([gamma/(v^2+gamma^2)]).                    (15)
```

This is the positive kernel in `(6)`. For `Re w,Re v>0`,

```text
integral_0^infinity kappa_gamma(w,v) d gamma
 =2pi/(w+conjugate(v)).                                     (16)
```

Indeed, the left side may be rewritten as

```text
1/(w+conjugate(v))
 *integral_0^infinity
    (2w/(w^2+gamma^2)
     +2conjugate(v)/(conjugate(v)^2+gamma^2)) d gamma,
```

and each of the two integrals in parentheses equals `pi`.

Let the positive nonzero zeros of `F_(lambda,N)` be `gamma_k`, counted with multiplicity, and let
its zero at the origin have multiplicity `2r`. Combining `(14)` and `(16)` gives the exact
spectral-discrepancy formula

```text
K_D(w,v)
 =2r/(w conjugate(v))
  +integral_0^infinity kappa_gamma(w,v) d nu_(lambda,N)(gamma),

nu_(lambda,N)
 =sum_k delta_(gamma_k)-(log(lambda)/pi)d gamma.             (17)
```

Thus the aperture phase subtracts the universal Weyl continuum of density `log(lambda)/pi` from
the paired discrete spectral measure. It is not an arbitrary normalization artifact.

For finite nodes `w_j` and coefficients `c_j`, formula `(17)` reads

```text
sum_(j,k)c_j conjugate(c_k)K_D(w_j,w_k)
 =2r*|sum_j c_j/w_j|^2
  +2 integral_0^infinity
      (|sum_j c_j w_j/(w_j^2+gamma^2)|^2
       +|sum_j c_j gamma/(w_j^2+gamma^2)|^2)
    d nu_(lambda,N)(gamma).                                 (18)
```

Consequently the exact positive-background target is:

> prove that the signed discrepancy `nu_(lambda,N)` is nonnegative on the complete two-channel
> resolvent-square cone in `(18)`, uniformly enough to pass to the Euler half-plane limit.

This is weaker than positivity of `nu_(lambda,N)` as a measure and stronger than reality of the
finite spectrum. It is the spectral counterpart of the source two-channel Weil Gram in
`critical-logderivative-two-channel-weil-resolvent-law.md`.

## 5. The boundary is exact

The existing CCM Mellin transfer targets convergence of `F_(lambda,N)(z)` to `Xi(z)` on closed
substrips of

```text
|Im z|<1/2.                                                   (19)
```

Under `z=-iw`, this becomes

```text
|Re w|<1/2.                                                   (20)
```

The complete source Pick kernel `(9)` lives on

```text
Re w>1/2.                                                     (21)
```

Hence `(8)` is not a reformulation of the already targeted Mellin convergence. It asks the
dephased spectral carrier to cross the exact half-strip boundary. The phase defect `(14)` is the
operator form of that boundary layer.

This produces two positive cofinal alternatives:

1. **Divisor transport:** prove locally uniform, zero-preserving convergence of normalized
   determinants to `Xi` through the critical strip.
2. **Pick transport:** prove `(8)` for the dephased even spectral factors, or construct a positive
   relative-background kernel whose limit is `(9)`.

Either theorem carries more than real finite spectra. The first transports the divisor; the second
transports the complete Euler-region positive kernel.

## 6. Exact relative-determinant interlacing criterion

The periodic scaling determinant provides a canonical background with the same aperture phase.
Let

```text
d_j=2pi*j/L,       -N<=j<=N,
L=2log(lambda),
xi=sum_j xi_j V_j,
c_j=L^(-1/2)xi_j,
sum_j c_j=1.                                                 (22)
```

The CCM finite-dimensional determinant identity gives the relative determinant

```text
R_(lambda,N)(z)
 =det_reg(D_log^(lambda,N)-z)/det_reg(D_log^(lambda)-z)
 =sum_(j=-N)^N c_j/(d_j-z).                                  (23)
```

The aperture phase cancels exactly in this ratio. Moreover:

> **Relative Herglotz criterion.** `R_(lambda,N)` maps the upper half-plane to its closure if and
> only if `c_j>=0` for every `j`, equivalently `xi_j>=0` for every `j`.

Indeed, for `z=x+iy`, `y>0`,

```text
Im R_(lambda,N)(z)
 =y sum_j c_j/((d_j-x)^2+y^2).                              (24)
```

Nonnegative coefficients make `(24)` nonnegative. Conversely, if `c_k<0`, take `x=d_k` and let
`y` decrease to zero. The `k`-th term is `c_k/y`, while all other terms are `O(y)` away
from coincident poles, so the imaginary part becomes negative. This proves the equivalence.

Consequently ordinary Herglotz interlacing between the perturbed spectrum and the periodic
background is available exactly when the finite-Weil ground vector is a nonnegative measure in the
periodic Fourier basis. Self-adjointness in the modified Weil metric proves reality of the zeros,
but does not prove this coefficient sign condition.

Herglotz interlacing of `R_(lambda,N)` must not be confused with positivity of its logarithmic
derivative kernel. If `xi_j!=0`, then `R_(lambda,N)` has a simple pole at `z=d_j`. Therefore

```text
M_R(w)=d/dw log R_(lambda,N)(-iw)
      =-1/(w-id_j)+O(1)                                    (24a)
```

near `w=id_j`. Taking `w=epsilon+id_j` with `epsilon>0` small makes `Re M_R(w)<0`, so the diagonal
value of the Pick kernel of `M_R` is negative. Thus that kernel is never positive on the full right
half-plane when a genuine base eigenvalue is canceled.

The positive route must recombine the relative displacement with the periodic background as in
`(14e)`, or prove only the cofinal Euler-region limit after `(14c)` has made the background
negligible. Exact finite-stage positivity of the relative logarithmic derivative is impossible.

### Cofinal scalar-Herglotz interlacing is incompatible with the Xi limit

The coefficient-sign condition cannot remain the positive mechanism in a successful cofinal CCM
limit. Let `R_n` be a cofinal sequence of relative determinants `(23)` and assume

```text
c_(n,j)>=0 for every n,j.                                   (24b)
```

Put

```text
H_n(w)=i R_n(-iw).                                          (24c)
```

Because `R_n` is Herglotz on the upper half-plane and has real coefficients, `H_n` has strictly
positive real part on `Re w>0`. Fix a real `w_0>1/2` and normalize

```text
h_n(w)=H_n(w)/H_n(w_0),       h_n(w_0)=1.                   (24d)
```

Suppose the relative logarithmic derivatives supplied the required source limit:

```text
H_n'(w)/H_n(w)
 ->L(w)=xi'(1/2+w)/xi(1/2+w)
locally uniformly on Re w>1/2.                             (24e)
```

The half-plane `Re w>1/2` is simply connected and `xi(1/2+w)` is zero-free there. Choose the
logarithms in `(24d)` to vanish at `w_0`. Integrating `(24e)` along paths from `w_0` gives

```text
h_n(w)->xi(1/2+w)/xi(1/2+w_0)                              (24f)
```

locally uniformly. The limit therefore has nonnegative real part, and the harmonic minimum
principle makes its real part strictly positive.

This is impossible. Harnack's inequality on the shifted right half-plane implies that every
positive-real function normalized at `w_0` has at most linear growth on the positive real axis:

```text
h(x)=O_(w_0)(x),       x->infinity.                         (24g)
```

On the other hand, Stirling's formula and `zeta(x+1/2)->1` give

```text
log xi(1/2+x)
 =x/2*log x+O(x),       x->infinity,                        (24h)
```

which violates `(24g)`. Hence `(24b)` and `(24e)` cannot both hold.

> **Signed-coordinate necessity law.** Every successful CCM relative-determinant limit must leave
> the nonnegative Fourier-coordinate cone cofinally, or replace the scalar relative determinant by
> a genuinely operator-valued covariance. Ordinary Herglotz interlacing cannot transport the Xi
> logarithmic derivative.

This gives a concrete positive relative-background mechanism:

```text
nonnegative ground coordinates
  -> Herglotz relative determinant and spectral interlacing
  -> positive relative spectral measure
  -> candidate background renormalization of the aperture charge.          (25)
```

To complete the route one would still have to prove the coordinate signs cofinally and show that
the relative spectral measures, combined with the explicitly renormalized periodic background,
converge to the Xi logarithmic-derivative kernel. If the coordinate signs fail, a successful
background cancellation must be genuinely operator-valued rather than an ordinary scalar
Herglotz ratio.

## 7. Carrier budget

At cutoff `N`, the Pick-transport alternative must still retain

```text
V_N=span_Q{log p:p<=N}.                                      (26)
```

Under the joint almost-periodic finite-state hypotheses, the combined coefficient--state and
bounded-syntax law gives

```text
pi(N)
 <=dim_Q(V_N intersection Gamma(a_N))+2B(n_N,d_N).           (27)
```

Thus a relative-background cancellation of `(14)` is admissible only when its coefficient module,
order/degree, or genuinely infinite-dimensional state visibly carries the new prime directions.
A scalar phase subtraction removes exponential type but does not by itself transport arithmetic
incidence.

Within the bounded scalar autonomous class this is exhaustive. Outside it, growing state arity, an
exact global constraint, or a separately justified noncompact carrier are additional positive
locations for the same resource; none is silently counted as bounded scalar Kolchin capacity.

## 8. Exact scope

- `[PROVED]` Even real-rooted order-one spectral factors have the positive kernel `(2)`.
- `[PROVED]` Convergence `(8)` implies RH by the complete two-channel Euler kernel.
- `[PROVED]` The CCM aperture phase changes the kernel by the exact negative Cauchy term `(14)`.
- `[PROVED]` The phase is exactly subtraction of the Weyl continuum in `(17)`; positive
  renormalization is equivalent to resolvent-square positivity of that spectral discrepancy.
- `[PROVED]` The periodic background kernel is finite-aperture indefinite but decays exponentially
  on compact subsets of the Euler half-plane.
- `[PROVED]` The current Mellin strip and the Euler Pick half-plane meet only at their boundary.
- `[PROVED]` The phase-canceling relative determinant is Herglotz exactly when all periodic Fourier
  coordinates of the finite-Weil ground vector are nonnegative.
- `[PROVED]` Its logarithmic-derivative kernel is nevertheless finite-stage indefinite whenever a
  periodic eigenvalue is genuinely canceled; positivity must be recombined or cofinal.
- `[PROVED]` Cofinal nonnegative Fourier coordinates are incompatible with relative
  logarithmic-derivative convergence to Xi; the successful carrier must be signed or
  operator-valued.
- `[NOT PROVED]` The CCM factors are not shown to satisfy `(8)`.
- `[NOT PROVED]` No positive background renormalization of `(14)` is constructed.
- `[NOT PROVED]` No divisor-preserving determinant limit is constructed.
- `[NOT PROVED]` This theorem does not prove RH.

## 9. Scientific classification and Lean decision

The proof is Hadamard factorization plus closure of the positive-kernel cone and the existing
Euler-resolvent criterion. It is a route bridge, not new scientific knowledge.

The Lean tree now formalizes the unconditional multiplicity-exact order-one Hadamard product for
centered Xi in `XiHadamardFactorization.lean` and `XiHadamardGrowth.lean`, including
`XiC_eq_constant_mul_canonicalProduct`; `XiRelativeResolventTrace.lean` identifies its
logarithmic derivative with the exact divisor resolvent away from zeros.  Thus the Xi
Hadamard/log-derivative input is discharged.  The tree still does not formalize the CCM
regularized determinant, the general real-rooted spectral-factor Pick kernel, or the cofinal
dephased convergence `(8)`.  A finite-matrix closure wrapper would omit those remaining analytic
inputs, so no Lean file is added here.

**Superseded, 2026-08-15.**  A Lean module is added.  It is not a closure wrapper: it proves the
paired-zero kernel identity `(6)`, the closure of the positive cone (the transfer step of section
2), the aperture defect `(14)`, the complete periodic-background analysis `(14a)`-`(14c)` including
the finite-aperture indefiniteness, and the relative Herglotz criterion `(24)`.

## Lean status

Module `formal/GaloisForLFunctions/RHTower/CCM/CCMEulerPickTransferBoundary.lean` (wired, axiom-clean,
9 declarations).

- `pairedZeroKernel`, **`pairedZeroKernel_eq`** — equation `(6)`: the logarithmic-derivative
  contribution of one paired spectral zero is exactly the sum of two rank-one Gram kernels.  This is
  the mechanism behind positivity of `(2)`.
- **`posSemidef_of_tendsto_entrywise`** — the transfer step of section 2: the positive cone of
  finite Hermitian complex matrices is closed under entrywise limits.  So convergence `(8)` really
  does transport positivity to the limit kernel `(9)`; no compactness or uniformity is used beyond
  entrywise convergence, exactly as the card states.
- `rightCauchyKernel`, **`aperturePhaseDefect`** — equation `(14)`: the canonically phased kernel is
  the spectral-factor kernel minus `2a` times the Cauchy kernel.
- `periodicBackground`, **`hasDerivAt_periodicBackground`**, `periodicBackgroundLogDeriv`,
  **`periodicBackgroundLogDeriv_eq`** — equations `(14a)`, `(14b)`:
  `D_{0,a}(-iw) = 1 - e^{-2aw}` and its logarithmic derivative `2a/(e^{2aw} - 1)`.
- **`norm_periodicBackgroundLogDeriv_le`** — equation `(14c)`:
  `|L_{0,a}(w)| <= 2a/(e^{2a sigma} - 1)` for `Re w >= sigma > 0`, so the background is cofinally
  invisible on every compact subset of the Euler half-plane.
- **`periodicBackgroundLogDeriv_neg`** — the finite-aperture indefiniteness: at
  `w = x + i pi/(2a)` the background logarithmic derivative equals the *negative real* number
  `2a/(-e^{2ax} - 1)`, so its diagonal Pick value is negative.
- `relativeDeterminant`, **`im_relativeDeterminant`** — equation `(24)`:
  `Im R(z) = sum_j c_j (Im z)/((d_j - Re z)^2 + (Im z)^2)`.
- **`im_relativeDeterminant_nonneg`** — the sufficiency half of the relative Herglotz criterion:
  nonnegative coefficients make the relative determinant map the upper half-plane to its closure.

`#print axioms` on all nine declarations returns exactly `[propext, Classical.choice, Quot.sound]`.

Imported, not reproved: the Hadamard factorization `(3)` (already in the tree as
`XiC_eq_constant_mul_canonicalProduct` and `XiRelativeResolventTrace`), the CCM regularized
determinant `(11)`, the complete-detector theorem identifying `(9)` with Weil positivity, the
integral identity `(16)` and hence the spectral-discrepancy representation `(17)`-`(18)`, and the
Harnack/Stirling incompatibility `(24g)`-`(24h)`.

## Gates

- [x] positive kernel of dephased finite spectral factors
- [x] Euler-half-plane logarithmic-derivative transfer theorem
- [x] exact CCM aperture-phase defect
- [x] exact two-channel spectral-discrepancy representation
- [x] periodic-background kernel isolated and proved cofinally negligible
- [x] half-strip boundary identified
- [x] exact scalar relative-Herglotz/interlacing criterion
- [x] scalar Herglotz interlacing ruled out as a cofinal Xi carrier
- [x] four-currency carrier budget attached
- [ ] construct positive relative-background renormalization
- [ ] or prove dephased Euler-half-plane convergence
- [ ] or prove divisor-preserving determinant convergence
- [ ] RH
