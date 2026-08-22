# Finite spectral rank as an RH selector

- **ID:** `finite-spectral-rank-rh-selector`
- **Stage:** 5-failed
- **Type:** RETIRED SOURCE--DIVISOR ROUTE
- **Status:** `[RETIRED: SOURCE READING IS KNOWN HT; DIVISOR READING IS TRANSVERSE-BLIND]`
- **Statement attacked:** Infinite prime-log spectral rank was proposed not only as a category
  separator for hypertranscendence, but as a new producer capable of feeding horizontal
  zero-location into an RH route.

## Terminal bifurcation

There are two mathematically precise meanings of "prime-log spectral rank." Neither produces the
proposed RH conclusion.

### 1. Source spectrum

On a right half-plane the logarithmic Euler source is an ordinary Dirichlet series

```text
-zeta'(s)/zeta(s)=sum_(n>=2) Lambda(n)n^(-s).                (1)
```

Its vertical frequencies are `log n`, and its support contains every prime. Ostrowski's theorem,
in the Reich class-`D` form used by Nagoshi, already says that an ordinary Dirichlet series whose
nonzero support involves infinitely many distinct prime divisors is hypertranscendental.

Thus the source interpretation is valid but known:

```text
infinite prime support of the Dirichlet source
  => hypertranscendence.                                    (2)
```

It does not imply any zero-location statement. Multiplication by a nonzero DA meromorphic gauge
changes the divisor while changing the logarithmic derivative only by a DA term. Hence the source
class modulo DA is deliberately insensitive to those divisor changes.

### 2. Projected divisor spectrum

For a meromorphic function `F`, let

```text
nu_F=(Im)_* Div(F)                                          (3)
```

be the complete zero-ordinate counting measure, including multiplicity. The proved transverse
relocation pair in
`../2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/positive-density-transverse-divisor-relocation-law.md`
has all of the following simultaneously:

```text
nu_(F_0)=nu_(F_a),
[Dlog F_0]=[Dlog F_a] modulo DA,
same exact order and FE/Schwarz symmetries,
same finite differential-translation rank function,          (4)
```

while every zero of `F_0` lies on the critical line and `F_a` has two off-line vertical lattices
of combined density `4/pi` per unit height. Therefore the complete projected divisor spectrum—not
merely its leading counting asymptotic—does not determine transverse zero location.

The Fourier frequency module of `(3)` is consequently RH-blind. Giving it the prime-log source
frequencies by definition conflates two different objects: the Euler source `(1)` and the
height-projected divisor `(3)`.

## Why the natural repair is not this route

The remaining option is to retain the full complex zero locations, or equivalently test the divisor
by kernels evaluated at the complex points rather than only at their ordinates. That repair is
divisor-sensitive and can distinguish the relocation pair. It is exactly the kind of information
already retained by Weil positivity, Li coefficients, a canonical de Branges inner function, an
exact characteristic determinant, or Connes resonance widths.

It is no longer a finite spectral-rank theorem derived from HT. It is the transverse divisor input
whose sign or positivity is the RH problem.

## Route verdict

The proposed selector cannot be an independent producer for the named RH routes:

- read on the Euler source, it is the classical Ostrowski/Nagoshi HT obstruction and supplies no
  horizontal zero information;
- read on spectral heights, it is falsified by exact positive-density transverse relocation;
- repaired by complex transverse weights, it becomes divisor-sensitive input of the complete
  Weil/Li/de Branges/spectral criteria rather than a prior HT law generating that input.

This does not show that the complete named criteria cannot prove RH. It retires the proposed
finite-spectral-rank mechanism as a new path from hypertranscendence to their missing positivity or
self-adjointness.

## Surviving landscape result

The infinite prime-log module remains a rigorous characteristic of the Euler source and a known
certificate that no finite algebraic differential flow generates that source. The separate
finite-rank conjecture for pure-point divisor spectra remains live in
`../0-backlog/finite-spectral-rank-da-barrier.md` as a general HT landscape problem.

## Parent sources

1. A. Ostrowski, *Uber Dirichletsche Reihen und algebraische Differentialgleichungen*, Math. Z. 8
   (1920), 241--298; English translation `https://arxiv.org/abs/2211.02088`.
2. H. Nagoshi, *Hypertranscendence of L-functions for GL_m(A_Q)*, Bull. Aust. Math. Soc. 93
   (2016), 388--399, DOI `10.1017/S000497271500129X`.
3. `completed-logderiv-augmentation-filter-exposure.md` and
   `completed-logderiv-full-translation-orbit-freeness.md` for the completed-source application.

## Lean status

The exact completed source-stripping identity is formalized, but the analytic Ostrowski theorem and
the complete transverse-relocation HT pair are not. No stage-3 claim is made.
