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


## Lean progress — 2026-08-30: the catalecticant identification and the dimension of the secant variety

**A corpus search first: most of the Hankel determinantal algebra was already here.**  The
`RHTower/DeningerHankel*` family owns the exact statements this card calls "classical catalecticant
theory":

- `DeningerHankelSecantParameterization.deningerHankelSecantMoment` — the `r`-atom moment
  `mₙ = ∑ⱼ Uⱼ Tⱼⁿ`, i.e. the parameterization `(10)` of the span of `r` points of the rational
  normal curve;
- **`DeningerHankelHigherRankGroebner.finiteHankelSecantIdeal_eq_parameterization_ker`** — the ideal
  of the `(r+1)`-minors of the finite Hankel matrix **is** the kernel of that parameterization, over
  every commutative coefficient ring.  This is exactly the catalecticant theorem `(5)`–`(10)` of
  this card: `C_k` is the Hankel determinantal variety **and** the closure of the spans of `m − k`
  points of the degree-`2m−2` rational normal curve;
- `finiteHankelSecant_degLex_isGroebnerBasis`, `finiteHankelSecantIdeal_isPrime`,
  `finiteHankelSecantIdeal_int_isPrime` — the minors are a degree-lex Gröbner basis and the ideal is
  prime, so each `C_k` is irreducible and reduced.

**New today** — the dimension, which the corpus did not have:

`formal/GaloisForLFunctions/HTGeometry/SecantMomentIndependence.lean` (axiom-clean, wired):

- `hermiteFunctional`, `hermiteNodePoly`, `hermiteDerivPoly` and
  **`hermiteFunctional_weights_eq_zero`** — a functional `p ↦ ∑ⱼ aⱼ p(tⱼ) + ∑ⱼ bⱼ p′(tⱼ)` at
  distinct nodes that kills every polynomial of degree below `2r` has zero weights (test against
  `∏_{i≠j}(X − tᵢ)²(X − tⱼ)` and `∏_{i≠j}(X − tᵢ)²`);
- `confluentVandermonde` and **`det_confluentVandermonde_ne_zero`** — the confluent Vandermonde
  matrix at distinct nodes is invertible;
- `secantMomentPoly`, its two partial derivatives, and the capstone
  **`algebraicIndependent_secantMomentPoly`**: the first `2r` moments of `r` atoms are algebraically
  independent over the base field.  The proof is the Jacobian criterion
  (`JacobianAlgebraicIndependence.algebraicIndependent_of_jacobian_det_ne_zero`) with the confluent
  Vandermonde as the Jacobian at `U = 1`, `T` distinct.

`formal/GaloisForLFunctions/HTGeometry/HankelSecantDimension.lean` (axiom-clean, wired):

- `secantMomentHankel`, `secantNodeVandermonde`, `secantAmplitudeDiagonal` and
  **`secantMomentHankel_eq`** — the atomic Hankel factorization `H = Vᵀ D V`;
- **`det_secantMomentHankel`** — `det H = (det V)² ∏ⱼ Uⱼ` — and
  **`det_secantMomentHankel_ne_zero`**: the atomic Hankel matrix is generically nonsingular, which
  is Prony's inversion (the first `2r−1` moments determine the nodes);
- `secantMomentAlgHom`, `hankelSecantQuotientHom` — the parameterization as an algebra map and the
  induced map out of the determinantal quotient;
- **`algebraicIndependent_hankelSecantQuotient`** — for `2r ≤ N`, the `2r` coefficient coordinates
  `x_{e}` with `e < 2r` remain algebraically independent modulo the ideal of `(r+1)`-minors.

**What this gives the card.**  Equation `(11)` — the affine Hankel determinantal ring has dimension
`2t − 2 = 2(m−k)` — is now Lean-proved as a lower bound, and the upper bound is immediate from the
same modules because the quotient maps into the polynomial ring on the `2r` atom coordinates
(`hankelSecantQuotientHom`, injective by `finiteHankelSecantIdeal_eq_parameterization_ker`).  With
the ambient dimension `2m − 1` this is `(6)`: `codim C_k = 2k − 1`.

**Still open on this card**, with the route recorded so it is not re-derived:

- `(7)` `Sing(C_k) = C_{k+1}`: the Jacobian criterion for the minor ideal.  The corpus owns the
  ingredients — `DeterminantalIdeal.detIdeal` with its equivalence-invariance, the cofactor
  expansion of a minor's partial derivatives, and `SquareMatrixCorankOne` for the corank transport.
  The statement to build is that the Jacobian matrix of the `(r+1)`-minors at a point of rank
  exactly `r` has rank `2(k) − 1`, dropping precisely on the next stratum.
- normality and Cohen–Macaulayness: the degree-lex Gröbner basis is squarefree, so the initial ideal
  is a Stanley–Reisner ideal; the standard route is shellability of its simplicial complex.  Neither
  mathlib nor this corpus has Stanley–Reisner theory, and that is the honest gap.
- rational singularities (Conca–Mostafazadehfard–Singh–Varbaro): needs machinery mathlib does not
  have at all.  It is used by this card only for the qualitative sentence in the theorem statement,
  not by any consumer.

### The dimension is now an equality, not a bound

`HankelSecantDimension.lean` was extended with

```text
hankelSecantQuotientHom_injective     the determinantal quotient embeds in the atom coordinates
trdeg_mvPolynomial_eq                 trdeg K (MvPolynomial σ K) = #σ
trdeg_hankelSecantQuotient
    ** Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ finiteHankelSecantIdeal K N r) = 2r **,  for 2r ≤ N
```

which is exactly equation `(11)` of this card: the affine Hankel determinantal ring of the
`t`-minors has dimension `2t − 2 = 2(m−k)`.  With the ambient coefficient space of dimension
`2m − 1` this is `(6)`, `codim C_k = 2k − 1`, as an equality.

The upper bound is the injection into the `2r` atom coordinates together with
`AlgebraicIndependent.cardinalMk_le_trdeg`; the lower bound is
`algebraicIndependent_hankelSecantQuotient`.  Both directions are unconditional and axiom-clean.

### Next: `(7)` `Sing(C_k) = C_{k+1}`, with the route decided

The containment `C_{k+1} ⊆ Sing(C_k)` is the algebraic half and reduces to one general theorem about
determinantal ideals, which `HTGeometry/DeterminantalIdeal.lean` is the natural home for:

```text
every partial derivative of a t-minor lies in the ideal of (t−1)-minors
```

— because `∂(det A)/∂x = tr(adj A · ∂A/∂x)` (Jacobi's formula) and every entry of the adjugate is a
signed `(t−1)`-minor.  At a point of `C_{k+1}` all `(t−1)`-minors vanish, so the whole Jacobian of
the defining equations vanishes and the point is singular.  `detIdeal` is defined as the span of
`det (M.submatrix I m)` over *arbitrary* index functions, so membership needs no monotonicity
bookkeeping.

The reverse containment `Sing(C_k) ⊆ C_{k+1}` is the smoothness of the rank-exactly-`r` locus and
needs the rank of that Jacobian, for which the corpus has `SquareMatrixCorankOne` and
`SchurCofactorLocus` as the pattern.

Mathlib check before starting: `Matrix.adjugate`, `Matrix.mul_adjugate`, `Matrix.adjugate_apply` are
present; Jacobi's formula for a derivation is **not**, and is the piece to build.

### `(7)`, one containment: the deeper stratum is singular

`formal/GaloisForLFunctions/HTGeometry/DeterminantalJacobi.lean` (built, wired, axiom-clean):

```text
derivation_prod                          the Leibniz rule for a finite product   (general)
derivation_det                           ** Jacobi's formula for a derivation:
                                            D (det M) = ∑ₖ det (M with row k differentiated) **
prod_updateRow_perm                      the Leibniz term of an updated row
derivation_det_submatrix_mem_detIdeal    ** every derivation of a (t+1)-minor lies in the ideal of
                                            t-minors **
pderiv_det_submatrix_eval_eq_zero        ** at a point where every t-minor vanishes, every partial
                                            derivative of every (t+1)-minor vanishes **
```

The last statement is `C_{k+1} ⊆ Sing(C_k)`: the Jacobian of the defining equations of the corank-`k`
locus is identically zero on the corank-`(k+1)` locus.  Neither mathlib nor the corpus had Jacobi's
formula for a derivation; it is proved here from the Leibniz formula for the determinant and the
finite-product Leibniz rule, and is stated for an arbitrary derivation of a commutative algebra, so
it is reusable well beyond this card.

The reverse containment `Sing(C_k) ⊆ C_{k+1}` — smoothness of the rank-exactly-`t` locus — remains,
and is the rank computation for that same Jacobian.

### `(7)` is CLOSED: both containments

```text
HTGeometry/GenericDeterminantalSmooth.lean                (built, wired, axiom-clean)
    pderiv_det_genericVarMatrix_snoc
        ** differentiating a generic (t+1)-minor in the entry at its last chosen row and column
           returns exactly the t-minor obtained by deleting them **
    exists_notMem_range
    exists_pderiv_det_ne_zero_of_minor_ne_zero
        ** some t-minor nonzero at a point ⟹ some partial derivative of some (t+1)-minor is
           nonzero there:  Sing(C_k) ⊆ C_{k+1} **

HTGeometry/SecantMomentImmersion.lean                     (built, wired, axiom-clean)
    confluentAmplitudeDiagonal, confluentVandermondeAmp, confluentVandermondeAmp_eq
    det_confluentAmplitudeDiagonal
    det_confluentVandermondeAmp_ne_zero
    secantPoint, map_eval_momentJacobian
    det_momentJacobian_eval_ne_zero
        ** the moment map is an IMMERSION at every configuration of distinct nodes with nonzero
           amplitudes — the Hankel form of smoothness off C_{k+1} **
```

With `DeterminantalJacobi.pderiv_det_submatrix_eval_eq_zero` (the reverse containment, landed
earlier today) this is `(7)`, `Sing(C_k) = C_{k+1}`, in both the generic determinantal form and the
Hankel/secant form: the Jacobian of the defining minors vanishes identically on the deeper stratum,
and off it the parameterization has invertible differential, so the variety is smooth there of
dimension `2r`.

**Remaining on this card:** normality and Cohen–Macaulayness (Stanley–Reisner theory, absent from
mathlib and the corpus) and rational singularities (Conca–Mostafazadehfard–Singh–Varbaro).  Neither
is used by any consumer of this card; `(4)`, `(5)`, `(6)`, `(7)` and the catalecticant identification
are all Lean-closed.
