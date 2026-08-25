# Exponential-Fock geometry makes critical prime incidence compact but non-Hilbert--Schmidt

- **ID:** `critical-prime-exponential-fock-compact-incidence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE HILBERT--POLYA CARRIER / BRIDGE
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For every `0<a<1/2`, a rapidly increasing radial Fock space with adapted scale
  `tau_a(x) asymp exp(-ax)` carries the normalized critical-prime evaluation map compactly.  The map
  is not Hilbert--Schmidt, its positive incidence operator is compact but not trace class, and the
  completed two-sided theta trace is continuous on the same pointed Hilbert space.

## Rapid source Hilbert space

Choose a smooth radial subharmonic function `phi_a` which agrees for large `r` with

```text
phi_a(r)=exp(2ar),  0<a<1/2,                                (1)
```

and put

```text
H_a={f entire:int_C |f(z)|^2 exp(-2phi_a(z))dA(z)<infinity}.  (2)
```

The associated rapid-Fock scale is

```text
tau_a(r) asymp (Delta phi_a(r))^(-1/2)
             asymp exp(-ar).                               (3)
```

The potential is in the rapidly increasing radial class `I` of Constantin--Pelaez.  Their kernel
estimate gives

```text
K_a(z,z) exp(-2phi_a(z)) asymp tau_a(z)^(-2).               (4)
```

Let `one(z)=1`; then `one in H_a`.

## Normalized critical-prime evaluation

For primes `p`, put

```text
lambda_p=log p,
w_p=(log p)^2/p,
(S_a f)_p=sqrt(w_p) f(lambda_p)/sqrt(K_a(lambda_p,lambda_p)).  (5)
```

By `(4)`, the square of the sampling norm is comparable to the rapid-Fock embedding associated
with the discrete positive measure

```text
mu_a=sum_p w_p tau_a(lambda_p)^2 exp(-2phi_a(lambda_p))
       delta_(lambda_p).                                    (6)
```

Indeed,

```text
sum_p w_p |f(lambda_p)|^2/K_a(lambda_p,lambda_p)
 asymp int_C |f(z)|^2 dmu_a(z).                             (7)
```

## Vanishing Carleson law `[PROVED]`

For `p=q=2`, the rapid-Fock embedding theorem says that `(7)` is bounded exactly when

```text
sup_x tau_a(x)^(-2)
  int_(D(x,delta tau_a(x))) exp(2phi_a(z))dmu_a(z)<infinity,  (8)
```

and compact exactly when the displayed quantity tends to zero as `|x|->infinity`.

On an adapted disk meeting the positive prime-log tail, `tau_a(lambda_p)` is comparable to
`tau_a(x)`.  The factors `exp(2phi_a(lambda_p))` and `exp(-2phi_a(lambda_p))` cancel exactly at each
atom of `(6)`; no false additive comparability of the rapidly varying potential is used.  Thus the
quantity in `(8)` is comparable to

```text
sum_(|log p-x|<=C tau_a(x)) (log p)^2/p.                    (9)
```

The logarithmic-window prime-mass theorem gives

```text
sum_(|log p-x|<=C tau_a(x)) (log p)^2/p
 =2C x tau_a(x)+o(1)
 ->0.                                                       (10)
```

The error here is additive, not relative.  The global weighted PNT remainder has a finite limit,
so its difference across any window of radius at most one is `o(1)` uniformly.  This is enough for
vanishing Carleson compactness even when `tau_a(x)` is below the unconditional relative
short-interval PNT scale.  No local prime asymptotic is claimed in this theorem.

Disks away from the positive real tail contain no mass, and bounded regions contribute a finite
constant.  Therefore `mu_a` is vanishing Carleson and

```text
S_a:H_a->ell^2(P) is compact.                               (11)
```

## Exact non-Hilbert--Schmidt endpoint `[PROVED]`

Each normalized evaluation functional has norm one.  Hence

```text
||S_a||_(S_2)^2
 =sum_p ||sqrt(w_p) e_(lambda_p)^*||^2
 =sum_p (log p)^2/p
 =infinity.                                                 (12)
```

Thus

```text
S_a notin S_2.                                              (13)
```

Put

```text
T_a=S_a^*S_a.                                               (14)
```

Then `T_a` is positive and compact.  Since `T_a` is trace class exactly when `S_a` is
Hilbert--Schmidt,

```text
T_a notin S_1.                                              (15)
```

This is the correct trace endpoint for an `Xi` determinant carrier, though no eigenvalue asymptotic
is claimed here.

## Completed theta trace on the same space `[PROVED]`

Let `h=xiThetaLogSource`.  Its exact theta expansion and reflection give

```text
|h(u)|<=C exp(|u|/4-pi exp(|u|)).                           (16)
```

Point evaluation in `H_a` satisfies

```text
|f(u)|<=C ||f||_(H_a) exp(phi_a(u))/tau_a(u).               (17)
```

Because `2a<1`,

```text
exp(phi_a(u))/tau_a(u)
 =exp(exp(2a|u|)+O(|u|))
 =o(exp(pi exp(|u|)))                                      (18)
```

on both tails.  Therefore, for every compact `Q subset C`,

```text
sup_(z in Q)
 |int_R f(u)h(u)exp(-2pi Iuz)du|
 <=C_Q ||f||_(H_a).                                        (19)
```

The trace is entire by dominated differentiation.  At `f=one`, the formal theorem
`completedRiemannZeta0_critical_eq_fourier_xiThetaLogSource` gives the exact completed-zeta trace,
and the identity theorem extends it from real frequency to the complexified variable.

Thus one pointed Hilbert space carries

```text
compact all-prime incidence
+ exact completed trace and all trace moments.              (20)
```

## Positive Hilbert--Polya consequence

The polynomial-Fock carriers were too large in Schatten exponent.  Exponential localization proves
the next required structural step:

> A source-defined analytic carrier can make the full critical prime incidence compact while
> retaining its non-trace-class arithmetic mass and the exact completed theta trace.

The remaining operator theorem is quantitative, not existential: determine the eigenvalue counting
of `T_a`.  The adapted cell geometry predicts

```text
lambda_n(T_a) asymp (log n)/n,                              (21)
```

which is the ideal law forced by `Xi`, but `(21)` is not proved here.

## Attacks and boundaries

1. **Rapid-versus-doubling attack.** The exponential weight is not in the polynomially controlled
   doubling-Fock class.  The proof uses the rapid radial class and its own embedding theorem.
2. **Normalization attack.** The diagonal kernel factor in `(6)` is essential.  Raw point values
   would define a different measure.
3. **Compactness attack.** The vanishing local mass `(10)` proves compactness even though the total
   coordinate-norm sum diverges.  Compact does not imply Hilbert--Schmidt.
4. **Theta-growth attack.** The restriction `a<1/2` ensures the theta decay `exp(-pi exp |u|)` beats
   the evaluation growth `exp(exp(2a|u|))`.
5. **Spectral attack.** Positivity and compactness of `T_a` do not identify its eigenvalues with
   reciprocal zeta heights.
6. **Divisor attack.** The exact theta trace carries `Xi`, but zeros of that trace are not yet the
   spectrum of `T_a`.

## Scientific verdict

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The compactness proof is a direct specialization of the
rapid-Fock Carleson embedding theorem, and non-Hilbert--Schmidt behavior is the coordinate norm
identity `(12)`.  Coupling the theta trace uses its classical double-exponential decay.  The result
constructs a useful positive carrier but introduces no new parent mechanism.

Primary parent source:

- O. Constantin and J. A. Pelaez, *Integral operators, embedding theorems and a Littlewood--Paley
  formula on weighted Fock spaces*, Journal of Geometric Analysis 26 (2016), 1109--1154,
  `https://arxiv.org/abs/1304.7501`.

## Lean status

The exact theta trace is already formalized.
`formal/GaloisForLFunctions/RHTower/CriticalPrimeSamplingIncidence.lean` now proves the common
operator endpoint unconditionally: the literal normalized prime weight is nonsummable, the sampling
map is not Hilbert--Schmidt once its adjoint coordinate vectors have the normalized kernel norms,
and compact sampling gives a positive compact incidence which is not Schatten one.  Rapid-Fock
kernels, adapted Carleson measures, and the concrete compact embedding remain open.
`formal/GaloisForLFunctions/RHTower/CriticalPrimeKernelSampling.lean` now constructs the literal
sampling map from any proved unit-kernel Bessel estimate and discharges the normalized coordinate
identity automatically; this shared endpoint is not counted as a complete formalization of the
card.  `CriticalPrimeKernelSamplingCompact.lean` proves compactness from vanishing finite-tail
Bessel constants, and `CriticalPrimeKernelSchurSampling.lean` removes the Bessel premise by
constructing the sampler directly from uniform finite Gram-row bounds and proving compactness from
vanishing tail Gram rows.  The remaining card-specific producer is the rapid-Fock normalized-kernel
Gram estimate and its concrete prime-log specialization.

`PolynomialFockPotentialGeometry.lean` supplies reusable polynomial-carrier geometry: exact radial
slope, radial curvature, Laplacian density, positivity, sharp uniform density comparison with
`(1+r^2)^(m/2-1)`, and corresponding two-sided reciprocal-square-root adapted-radius bounds.  Its
targeted leaf build and axiom audit passed.  This polynomial infrastructure does not establish the
rapid exponential carrier's kernel/Carleson estimate, so it does not close this card.

## Gates

- [x] exponential rapid-Fock carrier constructed
- [x] exact normalized discrete measure identified
- [x] vanishing Carleson condition proved from the PNT window law
- [x] compactness of prime incidence proved
- [x] non-Hilbert--Schmidt and non-trace-class endpoints proved
- [x] exact completed theta trace proved continuous on the same space
- [x] parent-theory novelty claim rejected
- [ ] exact eigenvalue counting law
- [ ] complete unconditional Lean formalization
