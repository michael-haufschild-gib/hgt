# CCM direct cofinal Weil-floor theorem

- **ID:** `ccm-direct-cofinal-weil-floor`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE, `[OPEN RH CORE]`
- **Scientific status:** `[CONJECTURE] [RH-SUFFICIENT]`
- **Parent results:** `ccm-cofinal-weil-spectral-floor-criterion.md`,
  `ccm-rayleigh-transfer-collapses-to-spectral-floor.md`, Suzuki's restricted Weil operator, and
  the CCM radial-prolate incidence laws
- **Statement:** On one cofinal aperture sequence, the lowest eigenvalue of the true even
  restricted Weil operator tends to zero.

## Exact target

Let `A_lambda` be the true compact-resolvent restricted Weil operator in the even sector and put

```text
epsilon_0(lambda)
 =inf{QW(f,f): f in D_lambda, ||f||_2=1}.                        (1)
```

The live CCM theorem is

```text
there exists lambda_j->infinity such that
epsilon_0(lambda_j)->0.                                         (2)
```

By `ccm-cofinal-weil-spectral-floor-criterion.md`, `(2)` implies the full Weil criterion and RH.
It is not a preliminary estimate.

## Quantized form of the target

`ccm-aperture-morse-index-conservation-law.md` replaces the vanishing-error language by the exact
integer carrier

```text
kappa(lambda)=Tr 1_(-infinity,0)(A_lambda).                 (2a)
```

This finite number is nondecreasing with aperture, starts at zero, and satisfies

```text
RH
 <-> kappa(lambda)=0 for every lambda
 <-> ker(G_lambda)=0 for every lambda,                     (2b)
```

where `G_lambda` is Suzuki's compact continuous-kernel screw operator. Thus the positive theorem is
conservation of a quantized aperture charge. A negative eigenvalue cannot be made harmless by
shrinking its magnitude through the logarithmic boundary layer.

## Positive no-negative-birth formulation

Let

```text
N_lambda=(-A_lambda)_+                                          (3)
```

be the negative spectral part. Since `A_lambda` has compact resolvent,

```text
||N_lambda||=max(0,-epsilon_0(lambda)).                          (4)
```

The formal norm statement would be

```text
the negative Weil spectral mass evacuates in operator norm:
||N_(lambda_j)||->0.                                            (5)
```

But `ccm-negative-spectrum-no-evacuation-law.md` proves that the restricted floors are
nonincreasing. Hence `||N_lambda||` is nondecreasing: `(5)` can hold only when

```text
N_lambda=0 for every lambda.                                    (5a)
```

The positive CCM statement is absence of negative spectral birth at every aperture, followed by
approach to the radical from above. It is stronger and more precise than saying that finite
determinants have real zeros or that a specified prolate source has small Rayleigh value.

## Exact Paley--Wiener Toeplitz formulation

Suzuki's Fourier formula for the restricted Weil form is

```text
QW_a(v,v)=1/(2*pi) integral_R w_a(t)|hat(v)(t)|^2dt,             (6)

w_a(t)=log|t|-log(2*pi)
 -2 sum_(n<=exp(2a))Lambda(n)/sqrt(n)*cos(t*log n)
 +hat(r_a'')(t).                                                (7)
```

Here `v` is supported in `[-a,a]`; hence `hat(v)` belongs to the Paley--Wiener space `PW_a`.
Let `P_(PW_a)` denote its orthogonal projection. The bounded-below restricted Weil operator is the
Toeplitz compression

```text
T_a=P_(PW_a) M_(w_a) P_(PW_a).                                  (8)
```

Consequently the exact live theorem is the uncertainty lower bound

```text
integral_R w_a(t)|F(t)|^2dt
 >=-eta_a integral_R |F(t)|^2dt
for every F in PW_a,
eta_a->0.                                                       (9)
```

This is `(5)` in native coordinates. The prime cutoff `n<=exp(2a)` and the exponential type `a`
must grow together; separating either one produces only a finite approximation.

## What the completed radial analysis supplies

The constrained prolate work now proves:

1. exact cofinal radial prime response, including the infinite radial multiplier;
2. exact scalar leading archimedean law
   `A(R_lambda)=log(c)||R_lambda||^2+O(d_1)`;
3. two or more fixed-depth orthogonal trial vectors with Rayleigh values tending to zero;
4. finite-Gamma completion supplies one archimedean valuation direction while the prime incidence
   remains an infinite divisibility carrier.

These results prove upper bounds on the first fixed spectral levels. They do not prove `(5)`,
because a negative vector may lie outside every fixed prolate trial subspace.

## Three competing positive mechanisms

### A. Paley--Wiener Toeplitz contraction

`[CONJECTURE]` Split the exact symbol `(7)` as

```text
w_a=d_a-k_a,                                                    (10)
```

where `d_a` is a positive reference symbol after the exact constant/radical mode has been removed
and `k_a` is the complete prime-incidence part. Prove on `PW_a`

```text
||D_a^(-1/2)K_a D_a^(-1/2)||<=1+eta_a,
eta_a*||D_a||->0,                                               (11)
```

where `D_a=P_(PW_a)M_(d_a)P_(PW_a)` and similarly for `K_a`. Then `(11)` gives `(9)`.
The load-bearing point is that `K_a` must retain the truncated-divisor weighted infinite
radial carrier; a finite-prime or finite-rank contraction is insufficient.

### B. No-negative-birth theorem

`[CONJECTURE]` Let `P_lambda^-` be the negative spectral projection. Prove

```text
P_lambda^-=0 for every lambda.                                  (13)
```

Strong convergence or asymptotic smallness is not an alternative: nested-floor monotonicity shows
that any negative vector at one aperture survives as a uniform negative upper bound at every later
aperture.

### C. Trace-ideal negative mass

`[CONJECTURE]` Construct a trace-class negative part and prove

```text
Tr(N_lambda)->0.                                                 (9)
```

Since `||N_lambda||<=Tr(N_lambda)`, `(9)` implies `(5)`. This mechanism is compatible with the
Connes--Sonin trace architecture, but only if the trace sees every omitted radial/divisor channel.

## Attack and selection

- Fixed-dimensional prolate ladders cannot prove `(5)`; they control only trial upper bounds.
- Compact-open germ, finite Gamma rank, or finite determinant data cannot prove `(5)`; the corpus
  relocation and maximal-quotient theorems make them transverse-blind.
- Strong convergence of negative projections cannot prove `(5)` without norm control.
- A finite Schur matrix cannot prove `(5)` without kernel/channel exhaustion.

Mechanism A is the preferred attack because `(7)` is the exact finite-prime symbol and `PW_a` is
the exact aperture constraint, while the radial work supplies the complete arithmetic incidence
weights. The next theorem must be an infinite-carrier compressed-multiplier estimate, not a new
source vector.

## Exact next lemma

There are now two exact, source-compatible versions of the next lemma.

The aperture version is the injectivity law

```text
ker(G_a)=0 for every a>0.                                  (12a)
```

The Euler-resolvent version uses

```text
A_w(alpha)=w/(w^2+alpha^2),
B_w(alpha)=alpha/(w^2+alpha^2),
Re w>1/2.                                                  (12b)
```

`critical-logderivative-two-channel-weil-resolvent-law.md` proves the unconditional identity

```text
(L(w)+conjugate(L(v)))/(w+conjugate(v))
 =q_W(A_w,A_v)+q_W(B_w,B_v),                              (12c)
```

where `L(w)=d/dw log xi(1/2+w)`. It also proves that this two-channel family is complete for RH.
Hence the source-side alternative is to construct a compatible Gram factorization of every finite
matrix in `(12c)` from the absolutely convergent Euler--Gamma formula in `Re w>1/2`.

Equivalently, in the original Paley--Wiener coordinates one may still prove the source-free
Toeplitz inequality

```text
<T_a F,F>
 >=-eta_a||F||_2^2
for every even F in PW_a,
eta_a->0.                                                       (12)
```

Equation `(12)` is exactly `(5)`. But `(12a)` and `(12c)` show the sharper positive architecture:

```text
Euler two-channel Gram positivity
  -> index-preserving transport into the growing screw spaces
  -> no finite-aperture kernel birth
  -> conserved zero Morse charge
  -> RH.                                                     (12d)
```

The transport must be uniform on the entire relevant closure and must use the complete
prime/source incidence, including the high radial divisor tail. Matching finitely many resolvent
entries does not preserve inertia.

The proved neutral signed-Gamma boundary law makes the carrier requirement quantitative. At prime
cutoff `N`, any recurrent DA realization must allocate

```text
pi(N)
 <=delta_beta+2m(n+1)+rank_Q A_N,                          (12e)
```

with `delta_beta in {0,1}` and `A_N` the complementary arithmetic module. Hence the Gram/aperture
transport in `(12d)` must visibly carry `A_N` unless its differential-state complexity grows
cofinally. Gamma logarithmic phases, polynomial jets, and Stokes corrections cannot be counted as
that module.

The stronger orbit-charge dichotomy and
`ccm-compressed-prime-shift-arithmetic-complement-law.md` identify this module exactly. If `D` is
the rational phase space carried by the finite signed-Gamma completion, then

```text
A_N=V_N/(V_N intersection D),
V_N=span_Q{log p:p<=N}.                                  (12f)
```

The compressed weighted shifts `T_(A,log p)` are linearly independent whenever `log N<A`, and
their operator quotient by the image of `V_N intersection D` is canonically isomorphic to `A_N`.
Thus the CCM source already possesses the forced complementary carrier. The remaining theorem is
not to invent arithmetic state: it is to factor the completed form positively while preserving the
inertia of this explicit quotient through the cofinal aperture limit.

The corpus-level factorization of that carrier is now recorded in
`ccm-sonin-three-grade-relative-carrier-law.md`. The canonical source has three inseparable grades:

```text
noncompact principal Calkin shell carrying A_N
  + Hilbert--Schmidt linear cross carrying the unsquared log(p^m) coefficient
  + positive trace-class residual Gram.                  (12g)
```

The first grade is too large for an all-prime compact sum, the third deletes the principal mode and
squares coefficients, and the second has no canonical trace without a genuine relative
functional. Therefore the preferred version of the Gram/aperture transport in `(12d)` is a closed
principal--relative extension carrying all three grades, followed by a cofinal contraction whose
principal symbol is faithful on `A_N` and whose degree-one functional is Connes's semilocal
logarithmic trace.

The degree-one operator is explicit before Sonin compression. By
`critical-euler-position-commutator-carrier-law.md`, logarithmic position `X_A` and the skew Euler
logarithm `Z_A` satisfy

```text
[X_A,Z_A]
 =sum_(n<e^A)Lambda(n)/n
    (T_(A,log n)+T_(A,log n)^*).                         (12h)
```

The coefficient of the `p^k` term in `Z_A` is exactly `1/(k p^k)`, while the commutator produces
the orbital length `log(p^k)`. Hence the next construction is no longer an unspecified relative
functional: it is the closed transport of `(12h)` through the three-grade Sonin carrier and its
coupling to Burnol's Gamma conductor.

Compression no longer introduces an unspecified error term. For any orthogonal constraint `Q`,
the position/Euler commutator obeys

```text
Q[X_A,Z_A]Q
 =[QX_AQ,QZ_AQ]
  +L_(X,A)^*L_(Z,A)+L_(Z,A)^*L_(X,A),                   (12i)
```

with `L_(X,A)=(1-Q)X_AQ` and `L_(Z,A)=(1-Q)Z_AQ`. Under an admissible relative trace the internal
commutator vanishes, so the exact degree-one source is the polarized leakage Gram. The next theorem
is to put these two leakage maps on a common closed graph, identify their relative trace with the
semilocal logarithmic functional, and prove the completed Gamma--prime square/contraction.

### D. Euler-Pick boundary transport

There is a fourth exact interface which bypasses a direct lower bound on `(7)` but does not bypass
the cofinal carrier. Under the CCM simple-even hypothesis, remove the canonical aperture phase and
write

```text
F_(lambda,N)(z)
 =i lambda^(iz)det_reg(D_log^(lambda,N)-z),
G_(lambda,N)(w)=F_(lambda,N)(-iw).                       (12j)
```

Every `F_(lambda,N)` is even with only real zeros. Therefore, with
`L_(lambda,N)=G_(lambda,N)'/G_(lambda,N)`,

```text
K_(lambda,N)(w,v)
 =(L_(lambda,N)(w)+conjugate(L_(lambda,N)(v)))
   /(w+conjugate(v))>=0                                  (12k)
```

on `Re w>0`. By `ccm-euler-pick-logderivative-transfer-boundary-law.md`, the source convergence

```text
L_(lambda_j,N_j)(w)->xi'(1/2+w)/xi(1/2+w)
locally uniformly on Re w>1/2                            (12l)
```

would pass `(12k)` to the complete two-channel Euler kernel and prove RH.

The dephasing is load-bearing. The canonical determinant in the `w` coordinate has logarithmic
derivative `-log(lambda)+L_(lambda,N)`, so its Pick kernel is

```text
K_(lambda,N)(w,v)-2log(lambda)/(w+conjugate(v)).          (12m)
```

Thus self-adjoint finite spectra do not automatically make the normalized source kernel positive.
The existing Mellin convergence lives in `|Re w|<1/2`, whereas `(12l)` lives in `Re w>1/2`.
A successful Pick implementation must construct a positive relative-background renormalization
of `(12m)` or carry the dephased logarithmic derivatives across that exact boundary. This is the
kernel analogue of the divisor-preserving determinant theorem, not a finite-spectrum shortcut.

The phase has an exact two-channel spectral meaning. If `gamma_k(lambda,N)>0` are the positive
zeros of the dephased determinant, then the signed discrepancy

```text
nu_(lambda,N)
 =sum_k delta_(gamma_k(lambda,N))
   -(log(lambda)/pi)d gamma                              (12n)
```

has Gram transform `(12m)`: the subtracted continuum is exactly the Cauchy background
`2log(lambda)/(w+conjugate(v))`. Hence the positive relative-background theorem can be stated
without choosing a phase convention: prove that `(12n)` is nonnegative on the complete
two-channel resolvent-square cone and converges there to the Xi kernel. Reality of the discrete
spectrum alone does not control this signed discrepancy.

## Gates

- [x] determinant transfer collapsed to the direct floor criterion
- [x] negative-part norm formulation isolated and evacuation excluded
- [x] compact-kernel repair threshold identified
- [x] fixed-source upper bounds separated from global lower bounds
- [x] three possible global mechanisms compared
- [x] exact Paley--Wiener Toeplitz compression identified
- [x] finite-aperture Morse charge isolated and proved monotone
- [x] RH reduced to compact screw injectivity at every aperture
- [x] complete two-channel Euler--Weil resolvent family constructed
- [x] exact arithmetic-complement operator carrier `A_N` constructed
- [x] three-grade principal--relative carrier forced by the formalized Sonin corpus
- [x] exact degree-one Euler position commutator constructed
- [x] exact compressed position/Euler leakage Gram identity constructed
- [x] dephased finite-spectrum Euler-Pick transfer and aperture-phase defect isolated
- [ ] construct a positive reference splitting `(10)`
- [ ] prove the infinite-carrier contraction `(11)`
- [ ] or construct a source-defined Gram factorization of `(12c)` and an index-faithful aperture
      transport
- [ ] or construct a positive relative-background kernel and prove `(12l)`
- [ ] prove absence of negative spectral birth `(5a)`
- [ ] invoke the cofinal floor criterion to prove RH
