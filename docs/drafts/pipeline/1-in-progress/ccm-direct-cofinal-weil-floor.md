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

Prove the source-free Toeplitz inequality

```text
<T_a F,F>
 >=-eta_a||F||_2^2
for every even F in PW_a,
eta_a->0.                                                       (12)
```

Equation `(12)` is exactly `(5)`. Its proof must be uniform on the entire even unit sphere and
must use the complete prime/source incidence, including the high radial divisor tail.

## Gates

- [x] determinant transfer collapsed to the direct floor criterion
- [x] negative-part norm formulation isolated and evacuation excluded
- [x] compact-kernel repair threshold identified
- [x] fixed-source upper bounds separated from global lower bounds
- [x] three possible global mechanisms compared
- [x] exact Paley--Wiener Toeplitz compression identified
- [ ] construct a positive reference splitting `(10)`
- [ ] prove the infinite-carrier contraction `(11)`
- [ ] deduce negative-part evacuation `(5)`
- [ ] invoke the cofinal floor criterion to prove RH
