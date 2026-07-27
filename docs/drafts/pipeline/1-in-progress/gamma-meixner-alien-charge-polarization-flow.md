# Gamma--Meixner alien-charge polarization flow

- **ID:** `gamma-meixner-alien-charge-polarization-flow`
- **Stage:** 1-in-progress
- **Type:** `[GENERAL HT POLARIZATION LAW] [SOURCE-SPECIFIC EULER ENDPOINT]`
- **Scientific status:** `[PROVED ON PAPER] [LEAN ALGEBRA CORE IN PROGRESS]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `../2-fully-proven/not_new_scientific_knowledge/archimedean-meixner-root-seam-scale.md`;
  - `complex-slope-gamma-alien-charge-classification.md`;
  - `../3-formalized/gamma-reflection-charge-conjugation-doubling.md`;
  - `../4-publication-ready/multiple-elliptic-gamma-rational-rank-dichotomy/main.tex`.

## 1. Problem

The finite Euler identity supplies nonreal Gamma slopes

```text
lambda_p = i log(p)/(2 pi),
```

but its two reciprocal-Gamma halves have zero total alien charge. Selecting one half after reading
a divisor would be target-fed and inadmissible. The missing question is whether an existing
positive source selects the two orientations before any Xi divisor is inserted.

The Gamma--Meixner convolution semigroup does. Its time-`theta` density is

```text
rho_theta(x)
 = c_theta Gamma(theta/4+i x/2) Gamma(theta/4-i x/2),    theta>0.       (1)
```

The two factors in `(1)` are distinguished by their upper/lower half-plane pole sets. Within the
source's zero-free minimal order-one Gamma class, Hadamard factorization makes this spectral
factorization unique up to `exp(alpha s+beta)`. The order-one condition is essential: without it,
`exp(h)A_+` and `exp(-h)A_-` for an arbitrary entire `h` preserve the density and destroy
uniqueness. This is more data than the real characteristic `cosh(t)^(-theta/2)` alone; the
characteristic or the odd Jacobi Gram by itself remains phase-blind.

## 2. Exact complex-charge flow

Fix `lambda in C*`, a real parameter `a`, and a nonzero integer lattice label `k`. Define

```text
M_(a,lambda)(s)
 = Gamma(a+lambda s) Gamma(a-lambda s),                 (2)

P_(a,lambda)(s)
 = Gamma(a+lambda s) / Gamma(a-lambda s).               (3)
```

For the complex scaled Gamma charge at `t=k lambda`, direct evaluation gives

```text
R_M(k lambda)
 = lambda[exp(-2 pi i k a)-exp(2 pi i k a)]
 = -2 i lambda sin(2 pi k a),                           (4)

R_P(k lambda)
 = lambda[exp(-2 pi i k a)+exp(2 pi i k a)]
 =  2 lambda cos(2 pi k a).                             (5)
```

For real `a`, equations `(4)--(5)` give the conserved polarization norm

```text
|R_M(k lambda)|^2+|R_P(k lambda)|^2=4|lambda|^2.         (6)
```

The coordinate-free charge divides by the unavoidable affine scale:

```text
Rhat_M=R_M/(2 lambda)=-i sin(2 pi k a),
Rhat_P=R_P/(2 lambda)=   cos(2 pi k a),                  (6a)

|Rhat_M|^2+|Rhat_P|^2=1.                                (6b)
```

Consequently every finite source amplitude packet `w_j` has an exact isometric split

```text
sum_j |w_j Rhat_M,j|^2+|w_j Rhat_P,j|^2
 =sum_j |w_j|^2.                                        (6c)
```

This normalization is load-bearing for the all-prime problem. Raw alien charge has size
`|lambda_p|` and would insert a spurious extra `(log p)^2` into the source norm. The normalized
charge is the unit orientation label carried by the corpus's source half-form; the source
amplitude, not the affine coordinate choice, supplies the Hilbert weight.

At Gamma--Meixner time `theta`, put `a=theta/4`. Then

```text
R_M(k lambda)=-2 i lambda sin(pi k theta/2),
R_P(k lambda)= 2 lambda cos(pi k theta/2).               (7)
```

Thus convolution time rotates a fixed alien-charge magnitude between the symmetric density and
the chiral spectral factor. This is an exact charge law; no asymptotic Gamma expansion or
numerical experiment enters it.

## 3. Singular Euler endpoint

At `theta=0`, equivalently `a=0`,

```text
M_(0,lambda)(s)=Gamma(lambda s)Gamma(-lambda s)
                       =-pi/[lambda s sin(pi lambda s)], (8)
R_M=0,                                                   (9)

P_(0,lambda)(s)=Gamma(lambda s)/Gamma(-lambda s),
R_P(k lambda)=2 lambda !=0.                              (10)
```

In normalized form the endpoint is exactly `(Rhat_M,Rhat_P)=(0,1)`: the complete finite source
norm is transferred into the chiral sector.

Equation `(8)` makes the symmetric endpoint differentially algebraic. Equation `(10)` and the
complex-slope classifier make its pole-oriented phase hypertranscendental. For every
`0<theta<2`, the first symmetric charge in `(7)` is nonzero, so the interior density is
hypertranscendental; hypertranscendence collapses only at the singular convolution endpoint while
the chiral charge survives.

For a prime `p`, scale the Meixner spectral coordinate by

```text
x=(log p/pi)s,
lambda=lambda_p=i log(p)/(2 pi).
```

Then the two pole-oriented factors in `(1)` become

```text
Gamma(theta/4+lambda_p s),
Gamma(theta/4-lambda_p s),                              (11)
```

and converge meromorphically away from poles to `Gamma(lambda_p s)` and
`Gamma(-lambda_p s)`. Recurrence gives

```text
Gamma(1-lambda_p s)=(-lambda_p s)Gamma(-lambda_p s).     (12)
```

Combining `(8)`, `(12)`, and Euler reflection recovers `1-p^(-s)` from the inverse symmetric
endpoint by a nonzero rational/exponential gauge. The chiral quotient is therefore selected
before any Xi divisor is read: approach the positive Gamma--Meixner semigroup endpoint and retain
the upper/lower pole orientation.

## 4. Hypertranscendence consequence

The source transition is

```text
theta>0:
  symmetric Meixner density HT, chiral factor HT;

theta=0:
  symmetric Euler intensity DA, chiral Euler phase HT.   (13)
```

This explains the finite Euler charge cancellation without discarding the positive survivor.
Charge is not destroyed; at the singular endpoint it is completely transferred to the
pole-oriented phase.

The result is stronger than the generic statement that modulus loses phase. The source supplies:

1. an explicit positive convolution semigroup;
2. a canonical meromorphic pole polarization;
3. an exact complex alien-charge transport law;
4. the local Euler factor as its singular endpoint.

## 5. Hostile controls

1. **Characteristic-only control.** The real characteristic
   `cosh(t)^(-theta/2)` and every Jacobi Gram built only from it are invariant under arbitrary
   unimodular changes of spectral factor. They do not select `(3)`. Pole orientation of the
   meromorphically continued density is load-bearing.
2. **Spectral-factor uniqueness control.** Pole orientation alone is insufficient because
   opposite entire exponential gauges preserve the product. Minimal order-one Gamma growth and one
   source normalization are load-bearing; then the remaining gauge is `exp(alpha s+beta)`, which
   is DA and has zero alien charge.
3. **Endpoint regularity.** The density normalization `c_theta` is singular as `theta->0`.
   Claims concern meromorphic Gamma factors and charge, not weak convergence of probability
   measures to a time-zero density.
4. **DA-limit control.** Differential algebraicity is not closed under arbitrary locally uniform
   limits. The content is the exact source family and its explicit endpoint, not a general
   closure theorem.
5. **Finite Euler control.** The unpolarized endpoint remains charge-zero. The theorem does not
   manufacture a defect from a finite Euler product; it canonically identifies the phase sector
   discarded by that product.
6. **RH control.** No zero location enters `(1)--(13)`. A remaining theorem must couple this
   source-selected chiral sector to the FE/Schwarz relative seam of an actual Xi fibre.

## 6. RH frontier changed

The prior source-weld alternative was

```text
chiral polarization or genuinely cofinal limit.
```

Equations `(1)--(12)` show these are not separate guesses. The canonical chiral polarization is
created by a genuinely cofinal Gamma--Meixner boundary:

```text
positive convolution roots
 -> pole-oriented spectral factors
 -> singular time-zero Euler endpoint
 -> DA intensity plus persistent HT phase charge.        (14)
```

The remaining open core is now narrower:

`[RH OPEN CORE: MEIXNER-POLARIZED FE/SCHWARZ SOURCE WELD]`

Construct, before evaluating any Xi zero, the source map from the pole-oriented time-zero factor
in `(14)` to the FE/Schwarz relative fibre channel, and prove that an off-critical fibre forces a
nonzero relative chiral charge inside a source-constrained DA carrier. The existing
Gamma--Meixner root-domain criterion reads the correct seam charge but does not yet provide this
phase-sensitive source map.

## 7. Novelty boundary

Known separately:

- Ramanujan's Gamma Fourier transform and the Gamma--Meixner convolution semigroup;
- Euler reflection and recurrence;
- Gamma intensity/phase differential-algebraic separation;
- real-slope reflected alien charge and the corpus's abstract charge doubling;
- the finite Euler reciprocal-Gamma identity.

Internal search found no prior statement of the charge-flow equations `(4)--(7)` or the
Meixner-to-Euler pole-polarized endpoint `(11)--(14)`. This composition is short, so search absence
does not establish priority or significance. External full-text audit remains required.

## 8. Lean status

`[LEAN-PROVED ALGEBRAIC CORE]`

```text
formal/GaloisForLFunctions/HTGeometry/GammaMeixnerAlienChargePolarization.lean
```

proves unconditionally:

1. exact exponential and sine/cosine formulas `(4)--(5)`;
2. raw norm conservation `(6)`;
3. normalized unit-charge conservation `(6a)--(6b)`;
4. the finite weighted isometry `(6c)`;
5. the pure chiral time-zero endpoint `(0,1)`;
6. nonzero symmetric charge throughout `0<theta<2`.

The module contains no analytic Gamma function or hidden hypertranscendence premise. Meromorphic
Gamma identities, the Gamma--Meixner density formula, and the analytic DA/HT classifier remain
paper-level parents of the source interpretation.

## Gates

- [x] exact source family identified
- [x] pole polarization defined before divisor insertion
- [x] intensity and phase charges computed on paper
- [x] singular Euler endpoint derived
- [x] phase-blind characteristic control stated
- [x] RH overclaim excluded
- [x] unconditional Lean algebraic charge-flow theorem
- [x] unconditional Lean normalized finite-source isometry
- [ ] exact Lean prime scaling and Euler endpoint gauge
- [ ] independent hostile proof audit
- [ ] full primary-literature priority audit
- [ ] FE/Schwarz relative source weld
