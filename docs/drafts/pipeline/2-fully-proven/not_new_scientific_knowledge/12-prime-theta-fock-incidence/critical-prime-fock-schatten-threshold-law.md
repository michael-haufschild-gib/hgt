# Critical prime incidence has an exact polynomial-Fock Schatten threshold

- **ID:** `critical-prime-fock-schatten-threshold-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / HILBERT--POLYA DETERMINANT LAW / BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For the superquartic doubling-Fock carrier `phi_m(z)=(1+|z|^2)^(m/2)`, `m>4`,
  the positive critical-prime incidence operator `T_m=S_m^*S_m` belongs to the Schatten class
  `S_q` exactly when `q>m/(m-4)`.  It is compact but never trace class.  Any determinant built from
  this incidence must therefore use a regularized determinant of explicitly bounded order.

## Setup

Use the Hilbert space `H_m=F_m^2`, reproducing kernel `K_m`, and normalized critical-prime sampling
operator

```text
(S_m f)_p=sqrt(w_p) f(log p)/sqrt(K_m(log p,log p)),
w_p=(log p)^2/p,                                            (1)
```

from `critical-prime-doubling-fock-phase-transition.md`.  For `m>4`, `S_m` is compact.  Put

```text
T_m=S_m^* S_m.                                              (2)
```

This is a positive compact operator on `H_m`.

Let

```text
rho_m(z) asymp (1+|z|)^(1-m/2)                             (3)
```

be the adapted doubling-Fock radius, and put

```text
a=m/2-1>1,
rho_m(x) asymp x^(-a)                                      (4)
```

on the positive real tail.

## Toeplitz realization `[PROVED]`

The diagonal kernel estimate identifies `T_m`, up to bounded positive equivalence, with the
doubling-Fock Toeplitz operator of the measure

```text
mu_m=sum_p w_p rho_m(log p)^2 delta_(log p).                (5)
```

More precisely, their closed quadratic forms satisfy

```text
c <T_(mu_m)f,f> <= <T_m f,f> <= C <T_(mu_m)f,f>.
```

The min--max principle therefore compares their singular values term by term up to fixed constants,
so they have exactly the same Schatten membership.

For a fixed adapted radius `r>0`, its averaging function is

```text
A_m(z)=mu_m(D(z,r rho_m(z)))/rho_m(z)^2.                    (6)
```

The doubling-Fock Schatten theorem says, for every `0<q<infinity`,

```text
T_m in S_q  iff A_m in L^q(C,d sigma_m),
d sigma_m=dA/rho_m^2.                                      (7)
```

The equivalence includes `0<q<1`, where `S_q` is a quasi-ideal.

## Arithmetic averaging profile `[PROVED]`

The support of `mu_m` is the positive prime-log axis.  In an adapted tube around a large positive
real point `x`, the logarithmic-window PNT gives

```text
A_m(z) asymp
  sum_(|log p-x|<=C rho_m(x)) (log p)^2/p
  asymp x rho_m(x).                                        (8)
```

Outside a fixed enlargement of this tube, `A_m` vanishes.  A tube segment of horizontal length
`dx` and vertical width comparable to `rho_m(x)` has

```text
d sigma_m-volume asymp dx/rho_m(x).                        (9)
```

Consequently

```text
int_C A_m(z)^q d sigma_m(z)
 asymp int_1^infinity (x rho_m(x))^q dx/rho_m(x)
 asymp int_1^infinity x^q rho_m(x)^(q-1) dx
 asymp int_1^infinity x^(a-q(a-1)) dx.                    (10)
```

The last integral converges exactly when

```text
a-q(a-1)<-1,
q>(a+1)/(a-1)=m/(m-4).                                    (11)
```

Equations `(7)` and `(11)` prove the theorem:

```text
T_m in S_q  iff q>m/(m-4).                                (12)
```

## Consequences for the sampling operator `[PROVED]`

The singular values satisfy

```text
s_n(T_m)=s_n(S_m)^2.
```

Hence

```text
S_m in S_r  iff r>2m/(m-4).                               (13)
```

In particular:

```text
T_m notin S_1 for every finite m>4,
S_m notin S_2 for every finite m>4.                        (14)
```

The second statement also follows directly from the Hilbert--Schmidt norm calculation

```text
||S_m||_2^2=sum_p ||sqrt(w_p)e_(log p)^*||^2
           =sum_p w_p
           =infinity,                                     (15)
```

because normalized evaluation has norm one.

For integer regularization orders, `det_n(1+zT_m)` is available whenever

```text
n>m/(m-4).                                                 (16)
```

For example, a second regularized determinant is available exactly when `m>8`; at smaller
superquartic degrees a higher order is required.

## Positive Hilbert--Polya law

The correct conclusion is not merely that a trace-class attempt fails:

> Polynomial confinement assigns a precise determinant genus to the critical prime incidence.
> A viable determinant architecture must choose `m` and a regularization order `n` satisfying
> `(16)`, transport the corresponding counterterms through completion, and then prove that the
> resulting characteristic entire function is the completed zeta trace.

The regularization order is not cosmetic.  Changing it changes the exponential counterterm in the
canonical determinant.  Since zero-free factors are spectrally invisible but completion-sensitive,
an RH architecture must fix this counterterm from the Euler--Gamma source rather than normalize it
after reading `Xi`.

The theorem supplies the exact ideal class in which that positive construction must live.  It does
not claim that `det_n(1+zT_m)` itself equals `Xi`.  Indeed, because `T_m` is positive, its coupling
parameter zeros lie on the negative real axis; identifying that parameter with zeta height would be
an unjustified reparametrization.

## Attacks and boundaries

1. **Trace-class attack.** Increasing the polynomial degree makes the threshold tend to `1` from
   above but never reaches trace class at finite `m`.
2. **Finite-cutoff attack.** Every finite prime cutoff is finite rank.  Equation `(12)` classifies
   the cofinal all-prime operator and cannot be inferred from any one cutoff.
3. **Support-tube attack.** The `d sigma_m` volume factor `dx/rho_m(x)` in `(9)` is load-bearing.
   Omitting it gives the wrong Schatten exponent.
4. **Weight attack.** The threshold is specific to `w_p=(log p)^2/p`; changing the source weight
   changes `(8)` and hence `(11)`.
5. **Determinant attack.** Membership in `S_q` only permits a regularized determinant.  It supplies
   neither the `Xi` identity nor self-adjoint spectral localization.
6. **Gauge attack.** Normalized evaluations make `S_m`, `T_m`, and the Schatten threshold invariant
   under zero-free RKHS gauge multiplication.

## Scientific verdict

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The Schatten characterization is a theorem of standard
doubling-Fock Toeplitz theory.  The exponent in `(11)` is a direct integration of the adapted prime
mass profile.  The exact threshold is useful for this Hilbert--Polya architecture but introduces no
new parent mechanism.

Primary parent source:

- R. Oliver and D. Pascuas, *Toeplitz operators on doubling Fock spaces*, Journal of Mathematical
  Analysis and Applications 435 (2016), 1140--1170, `https://arxiv.org/abs/1508.02887`.

## Lean status

`formal/GaloisForLFunctions/RHTower/CriticalPrimeSamplingIncidence.lean` now formalizes the shared
operator endpoint unconditionally: divergence of the literal weight `(log p)^2/p`, failure of the
normalized sampler to be Hilbert--Schmidt from its adjoint coordinate norms, compactness and
positivity of `S^*S` from compactness of `S`, and failure of `S^*S` to be Schatten one.  The existing
rectangular Gram-spectrum module and
`formal/GaloisForLFunctions/RHTower/CriticalPrimeSamplingSchattenBridge.lean` supply the exact
all-exponent law `S in S_(2q) iff S^*S in S_q`.
`formal/GaloisForLFunctions/RHTower/CriticalPrimeKernelSampling.lean` constructs the literal
all-prime analysis operator from any proved Bessel estimate for unit normalized kernel vectors and
derives its coordinate norms, so no operator or endpoint law remains assumed.  The substantive
doubling-Fock Toeplitz/Carleson theorem and its specialization to the concrete carrier remain to be
formalized; the scalar power-integral test alone is not counted as completion.
`CriticalPrimeKernelSamplingCompact.lean` and `CriticalPrimeKernelSchurSampling.lean` additionally
derive boundedness and compactness from finite normalized-kernel Gram-row estimates, including the
vanishing tail form, without assuming a Bessel or compact operator.  Exact all-exponent Schatten
membership still requires the doubling-Fock Toeplitz averaging theorem and the adapted tube
integrability classification.
`MomentFockKernel.lean` and `PolynomialMomentFock.lean` now supply the exact polynomial radial
moment carrier, bounded point evaluations, literal normalized prime-log kernels, and their exact
kernel series.  `PolynomialMomentFockNorm.lean` proves that this carrier has integrable literal
weighted square density on `C` and that its coefficient norm is exactly the weighted plane norm.
Thus neither carrier nor normalized kernels are abstract placeholders; remaining producers are the
doubling-Fock Gram/Toeplitz estimate and the all-exponent adapted-tube comparison.
`PolynomialMomentFockKernelBound.lean` also proves a concrete geometric diagonal-kernel bound and
point-evaluation envelope; the missing ideal classification is still off-diagonal/Toeplitz rather
than carrier existence or diagonal growth.

`PolynomialFockPotentialGeometry.lean` now proves the exact polynomial potential's radial slope,
radial curvature, Laplacian density, positivity, uniform two-sided density comparison, and exact
adapted-radius bounds for `m>=2`.  The targeted leaf build and axiom audit passed.  This closes the
potential/metric part of the averaging profile but not the load-bearing normalized-kernel
localization or doubling-Fock Toeplitz Schatten averaging theorem; the card remains at Stage 2.

`PolynomialFockTangentGaussian.lean` and `PolynomialMomentFockKernelLower.lean` now also prove the
exact real-axis lower diagonal-kernel scale by constructing a tangent exponential in the literal
moment carrier and bounding its plane norm.  This removes one diagonal asymptotic premise from the
Toeplitz averaging route.  Direct checks, targeted leaf builds, and the new-declaration axiom audit
passed with only `propext`, `Classical.choice`, and `Quot.sound`.  Off-diagonal localization and the
all-exponent adapted-tube Schatten comparison remain open, so the card stays at Stage 2.

`CriticalPrimeFockSchattenExponent.lean` now also proves the exact degree/order conversion

```text
m/(m-4) < q  iff  4q/(q-1) < m,
```

for `m>4`, including `m/(m-4)<2 iff 8<m`.  This closes the stated determinant-order arithmetic,
with direct check, targeted build, and standard-axiom audit passing.  It does not replace the open
operator theorem identifying the literal incidence's approximation-number ideal with the adapted
tube integral.

## Gates

- [x] prime incidence identified with a positive doubling-Fock Toeplitz operator
- [x] averaging profile computed in the adapted tube
- [x] metric volume factor included
- [x] exact Schatten threshold proved
- [x] non-Hilbert--Schmidt and non-trace-class consequences proved
- [x] determinant regularization order isolated
- [x] parent-theory novelty claim rejected
- [ ] complete unconditional Lean formalization
