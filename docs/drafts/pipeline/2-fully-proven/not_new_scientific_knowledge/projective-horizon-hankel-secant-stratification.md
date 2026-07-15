# Projective-horizon caustics have a Hankel secant stratification

- **ID:** `projective-horizon-hankel-secant-stratification`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / HIGHER-CAUSTIC CLASSIFICATION
- **Scientific status:** `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Formal status:** exact Hankel/rank/recurrence core formalized
- **Parents:** `projective-horizon-rectangular-schur-caustic`,
  `projective-horizon-irreducible-simple-ramification`
- **Lane:** general hypertranscendence; static singularity topology

## Theorem

Let `K` be an algebraically closed field of characteristic zero, let `m>=2`, `s>=0`, and let
`h_s,...,h_(s+2m-2)` be independent coordinates.  Put

```text
T_(s,m)(r,i)=h_(s+m-1+r-i),       0<=r,i<m,                 (1)
H_(s,m)(r,j)=h_(s+r+j),           0<=r,j<m.                 (2)
```

The matrix `(1)` is the critical reciprocal-horizon Jacobian, up to a nonzero scalar, for depths

```text
(m,n)=(m,s+m-1).                                             (3)
```

Column reversal gives the exact identity

```text
T_(s,m)(r,m-1-j)=H_(s,m)(r,j).                               (4)
```

For `1<=k<=m-1`, let

```text
C_k={h : corank H_(s,m)>=k}.                                 (5)
```

After projectivizing the `2m-1` consecutive coefficient coordinates, `C_k` is the closure of the
spans of `m-k` points of the degree-`2m-2` rational normal curve.  Equivalently it is the Hankel
determinantal variety cut out by the `(m-k+1)`-minors.  It satisfies

```text
codim C_k=2k-1,                                              (6)
Sing(C_k)=C_(k+1)                  for k<m-1.                (7)
```

The final rank-one stratum `C_(m-1)` is the rational normal curve and is smooth projectively.  In
characteristic zero every `C_k` is normal, Cohen--Macaulay, and has rational singularities.

Thus a `k`-dimensional invisible-mode space has forced odd codimension `2k-1`; every higher
caustic is exactly the singular locus of the preceding caustic.

## Proof

### Horizon-to-Hankel conversion

For `j in {0,...,m-1}`, its reversed index is `m-1-j`.  Since `n=s+m-1`, direct substitution gives

```text
n+r-(m-1-j)=s+r+j.                                          (8)
```

This proves `(4)`.  Column reversal is multiplication by a permutation matrix, so it preserves
rank, corank, and every determinantal rank locus.  Hence the complete higher-caustic filtration of
the horizon Jacobian is the rank filtration of the square Hankel matrix `(2)`.

### Hankel determinantal geometry

Write `a_q=h_(s+q)` for `0<=q<=2m-2`.  The rank condition in `(5)` is the vanishing of all minors
of size

```text
t=m-k+1.                                                     (9)
```

The classical catalecticant theorem identifies this minor ideal with the homogeneous ideal of the
closure of spans of `t-1=m-k` points of the rational normal curve

```text
[u:v] |-> [u^(2m-2):u^(2m-3)v:...:v^(2m-2)].                (10)
```

The corresponding affine Hankel determinantal ring has dimension

```text
2t-2=2(m-k).                                                (11)
```

Its ambient affine coefficient space has dimension `2m-1`, so `(11)` gives `(6)`.  The standard
singular-locus theorem for Hankel determinantal rings says that the singular locus of the
`t`-minor ring is defined by the image of the `(t-1)`-minor ideal.  This is precisely `C_(k+1)`,
proving `(7)`.  When `t=2`, the projective variety is the rational normal curve and the next locus
is only the vertex of the affine cone, absent after projectivization or on a normalized affine
chart.

Conca--Mostafazadehfard--Singh--Varbaro prove that these characteristic-zero Hankel determinantal
rings have rational singularities; their generalities also supply normality and the
Cohen--Macaulay property.

### Transfer to the reciprocal source chart

For a normalized reciprocal series `Z=1+sum_(q>0) z_q t^q`, the coefficients of `Z^2` obey

```text
h_q=2z_q+polynomial(z_1,...,z_(q-1)).                       (12)
```

This is a triangular coordinate automorphism in characteristic zero.  Reciprocal inversion is
birational on the unit-jet chart.  Hence the secant filtration, codimensions, singular loci, and
rational-singularity type transfer unchanged to the critical horizon source chart.  When `s=0`,
the normalization `h_0=1` is the standard affine chart of the projective secant filtration.
`QED`

## Physical meaning

The caustic is not an arbitrary catastrophe.  Its complete singularity hierarchy is a finite
moment/secant hierarchy:

```text
rank one                = one coherent point on a rational normal curve,
rank at most r          = a border sum of r such points,
corank k                = k invisible horizon directions,
next higher corank      = the singular locus of the current stratum.
```

This is an algebraic, static statement.  It does not assert a particle ontology, quantization,
Hamiltonian, time variable, or black-hole model.

## Novelty gate

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

The exact transfer identifies the full higher-caustic topology of the reciprocal horizon and was
not previously recorded in the project.  However, after the column reversal `(4)`, all remaining
geometry is the classical theory of generic Hankel determinantal rings and secant varieties of a
rational normal curve.  The result is useful structure and a complete physical interpretation,
but it fails the novelty half of the dual gate.

Primary sources:

- A. Conca, M. Mostafazadehfard, A. K. Singh, M. Varbaro, *Hankel determinantal rings have
  rational singularities*, arXiv:1709.05685.
- W. Buczynska, J. Buczynski, *Secant varieties to high degree Veronese reembeddings,
  catalecticant matrices and smoothable Gorenstein schemes*, arXiv:1012.3563.

## RH impact

For an HT source such as zeta, algebraic independence keeps the source off every finite higher
caustic as an identity.  The stratification remains target-translation blind and supplies no sign,
zero location, or critical-line selector.  Its RH value is a precise no-go boundary: an arithmetic
caustic mechanism must add Euler or functional-equation data that cuts this universal secant
geometry non-generically.

## Lean verification

`ProjectiveHorizonHankelSecant.lean` formalizes:

1. the exact column-reversal identity `(4)`;
2. preservation of matrix rank and every corank threshold;
3. the exact equivalence between the determinant caustic and a nonzero finite recurrence
   annihilating the visible coefficient window.

The catalecticant/secant identification, codimension formula, and singularity theorems are invoked
from the cited paper-level parent theory.  The targeted Lean check passes; no full build is used.

## Gates

- [x] 0 -> 1: source-pure statement, exact matrix route, parent collision, and RH boundary stated
- [x] 1 -> 2: complete transfer and parent-theory proof of the higher-caustic classification
- [ ] 2 -> 3: exact rank/recurrence core formalized; full algebraic-geometric secant interface absent
- [ ] 3 -> 4: closed by failed novelty gate

